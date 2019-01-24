/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <fstream>
#include <signal.h>
#include <cctype>
#include <cstdlib>
#include <string>
#include <utility>
#include <vector>
#include <set>
#include "runtime/stackinfo.h"
#include "runtime/interrupt.h"
#include "runtime/memory.h"
#include "runtime/thread.h"
#include "runtime/debug.h"
#include "runtime/sstream.h"
#include "util/timer.h"
#include "util/macros.h"
#include "util/lean_path.h"
#include "util/file_lock.h"
#include "util/sexpr/options.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "library/formatter.h"
#include "library/eval_helper.h"
#include "library/module_mgr.h"
#include "library/module.h"
#include "library/type_context.h"
#include "library/io_state_stream.h"
#include "library/message_builder.h"
#include "library/time_task.h"
#include "library/compiler/emit_cpp.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/json.h"
#include "frontends/lean/util.h"
#include "library/trace.h"
#include "init/init.h"
#include "shell/simple_pos_info_provider.h"
#ifdef _MSC_VER
#include <io.h>
#define STDOUT_FILENO 1
#else
#include <getopt.h>
#include <unistd.h>
#endif
#if defined(LEAN_EMSCRIPTEN)
#include <emscripten.h>
#endif
#include "githash.h" // NOLINT

#ifdef _MSC_VER
// extremely simple implementation of getopt.h
enum arg_opt { no_argument, required_argument, optional_argument };

struct option {
    const char name[12];
    arg_opt has_arg;
    int *flag;
    char val;
};

static char *optarg;
static int optind = 1;

int getopt_long(int argc, char *in_argv[], const char *optstring, const option *opts, int *index) {
    optarg = nullptr;
    if (optind >= argc)
        return -1;

    char *argv = in_argv[optind];
    if (argv[0] != '-') {
        // find first -opt if any
        int i = optind;
        bool found = false;
        for (; i < argc; ++i) {
            if (in_argv[i][0] == '-') {
                found = true;
                break;
            }
        }
        if (!found)
            return -1;
        auto next = in_argv[i];
        // FIXME: this doesn't account for long options with arguments like --foo arg
        memmove(&in_argv[optind + 1], &in_argv[optind], (i - optind) * sizeof(argv));
        argv = in_argv[optind] = next;
    }
    ++optind;

    // long option
    if (argv[1] == '-') {
        auto eq = strchr(argv, '=');
        size_t sz = (eq ? (eq - argv) : strlen(argv)) - 2;
        for (auto I = opts; *I->name; ++I) {
            if (!strncmp(I->name, argv + 2, sz) && I->name[sz] == '\0') {
                assert(!I->flag);
                switch (I->has_arg) {
                case no_argument:
                    if (eq) {
                        std::cerr << in_argv[0] << ": option doesn't take an argument -- " << I->name << std::endl;
                        return '?';
                    }
                    break;
                case required_argument:
                    if (eq) {
                        optarg = eq + 1;
                    } else {
                        if (optind >= argc) {
                            std::cerr << in_argv[0] << ": option requires an argument -- " << I->name << std::endl;
                            return '?';
                        }
                        optarg = in_argv[optind++];
                    }
                    break;
                case optional_argument:
                    if (eq) {
                        optarg = eq + 1;
                    }
                    break;
                }
                if (index)
                  *index = I - opts;
                return I->val;
            }
        }
        return '?';
    } else {
        auto opt = strchr(optstring, argv[1]);
        if (!opt)
            return '?';

        if (opt[1] == ':') {
            if (argv[2] == '\0') {
                if (optind < argc) {
                    optarg = in_argv[optind++];
                } else {
                    std::cerr << in_argv[0] << ": option requires an argument -- " << *opt << std::endl;
                    return '?';
                }
            } else {
                optarg = argv + 2;
            }
        }
        return *opt;
    }
}
#endif

using namespace lean; // NOLINT

#ifndef LEAN_SERVER_DEFAULT_MAX_MEMORY
#define LEAN_SERVER_DEFAULT_MAX_MEMORY 1024
#endif
#ifndef LEAN_DEFAULT_MAX_MEMORY
#define LEAN_DEFAULT_MAX_MEMORY 0
#endif
#ifndef LEAN_DEFAULT_MAX_HEARTBEAT
#define LEAN_DEFAULT_MAX_HEARTBEAT 0
#endif
#ifndef LEAN_SERVER_DEFAULT_MAX_HEARTBEAT
#define LEAN_SERVER_DEFAULT_MAX_HEARTBEAT 100000
#endif

static void display_header(std::ostream & out) {
    out << "Lean (version " << get_version_string() << ", " << LEAN_STR(LEAN_BUILD_TYPE) << ")\n";
}

static void display_help(std::ostream & out) {
    display_header(out);
    std::cout << "Miscellaneous:\n";
    std::cout << "  --help -h          display this message\n";
    std::cout << "  --version -v       display version number\n";
    std::cout << "  --githash          display the git commit hash number used to build this binary\n";
    std::cout << "  --run              executes the 'main' definition\n";
    std::cout << "  --make             create olean files\n";
    std::cout << "  --cpp=fname -c     name of the C++ output file\n";
    std::cout << "  --stdin            interpret stdin as content of single .lean file\n";
    std::cout << "  --recursive        recursively find *.lean files in directory arguments\n";
    std::cout << "  --trust=num -t     trust level (default: max) 0 means do not trust any macro,\n"
              << "                     and type check all imported modules\n";
    std::cout << "  --quiet -q         do not print verbose messages\n";
    std::cout << "  --memory=num -M    maximum amount of memory that should be used by Lean\n";
    std::cout << "                     (in megabytes)\n";
    std::cout << "  --timeout=num -T   maximum number of memory allocations per task\n";
    std::cout << "                     this is a deterministic way of interrupting long running tasks\n";
#if defined(LEAN_MULTI_THREAD)
    std::cout << "  --threads=num -j   number of threads used to process lean files\n";
    std::cout << "  --tstack=num -s    thread stack size in Kb\n";
#endif
    std::cout << "  --deps             just print dependencies of a Lean input\n";
#if defined(LEAN_JSON)
    std::cout << "  --path             display the path used for finding Lean libraries and extensions\n";
    std::cout << "  --json             print JSON-formatted structured error messages\n";
    std::cout << "  --server           start lean in server mode\n";
    std::cout << "  --server=file      start lean in server mode, redirecting standard input from the specified file (for debugging)\n";
#endif
    std::cout << "  --profile          display elaboration/type checking time for each definition/theorem\n";
    DEBUG_CODE(
    std::cout << "  --debug=tag        enable assertions with the given tag\n";
        )
    std::cout << "  -D name=value      set a configuration option (see set_option command)\n";
    std::cout << "  --test-suite       capture output and status code from each input file $f in $f.produced and $f.status, respectively\n";
}

static struct option g_long_options[] = {
    {"version",      no_argument,       0, 'v'},
    {"help",         no_argument,       0, 'h'},
    {"githash",      no_argument,       0, 'g'},
    {"make",         no_argument,       0, 'm'},
    {"stdin",        no_argument,       0, 'i'},
    {"recursive",    no_argument,       0, 'R'},
    {"memory",       required_argument, 0, 'M'},
    {"trust",        required_argument, 0, 't'},
    {"profile",      no_argument,       0, 'P'},
    {"threads",      required_argument, 0, 'j'},
    {"quiet",        no_argument,       0, 'q'},
    {"deps",         no_argument,       0, 'd'},
    {"test-suite",   no_argument,       0, 'e'},
    {"timeout",      optional_argument, 0, 'T'},
    {"cpp",          optional_argument, 0, 'c'},
#if defined(LEAN_JSON)
    {"json",         no_argument,       0, 'J'},
    {"path",         no_argument,       0, 'p'},
    {"server",       optional_argument, 0, 'S'},
#endif
#if defined(LEAN_MULTI_THREAD)
    {"tstack",       required_argument, 0, 's'},
#endif
#ifdef LEAN_DEBUG
    {"debug",        required_argument, 0, 'B'},
#endif
    {0, 0, 0, 0}
};

static char const * g_opt_str =
    "PdD:c:qpgvhet:012E:A:B:j:012rM:012T:012"
#if defined(LEAN_MULTI_THREAD)
    "s:012"
#endif
; // NOLINT

options set_config_option(options const & opts, char const * in) {
    if (!in) return opts;
    while (*in && std::isspace(*in))
        ++in;
    std::string in_str(in);
    auto pos = in_str.find('=');
    if (pos == std::string::npos)
        throw lean::exception("invalid -D parameter, argument must contain '='");
    lean::name opt = lean::string_to_name(in_str.substr(0, pos));
    std::string val = in_str.substr(pos+1);
    auto decls = lean::get_option_declarations();
    auto it = decls.find(opt);
    if (it) {
        switch (it->kind()) {
        case lean::BoolOption:
            if (val == "true")
                return opts.update(opt, true);
            else if (val == "false")
                return opts.update(opt, false);
            else
                throw lean::exception(lean::sstream() << "invalid -D parameter, invalid configuration option '" << opt
                                      << "' value, it must be true/false");
        case DoubleOption:
            return opts.update(opt, atof(val.c_str()));
        case lean::IntOption:
        case lean::UnsignedOption:
            return opts.update(opt, atoi(val.c_str()));
        case lean::StringOption:
            return opts.update(opt, val);
        default:
            throw lean::exception(lean::sstream() << "invalid -D parameter, configuration option '" << opt
                                  << "' cannot be set in the command line, use set_option command");
        }
    } else {
        throw lean::exception(lean::sstream() << "invalid -D parameter, unknown configuration option '" << opt << "'");
    }
}

class initializer {
private:
    lean::initializer m_init;
public:
    initializer() {
    }
    ~initializer() {
    }
};

int main(int argc, char ** argv) {
#if defined(LEAN_EMSCRIPTEN)
    EM_ASM(
        var lean_path = process.env['LEAN_PATH'];
        if (lean_path) {
            ENV['LEAN_PATH'] = lean_path;
        }

        try {
            // emscripten cannot mount all of / in the vfs,
            // we can only mount subdirectories...
            FS.mount(NODEFS, { root: '/home' }, '/home');
            FS.mkdir('/root');
            FS.mount(NODEFS, { root: '/root' }, '/root');

            FS.chdir(process.cwd());
        } catch (e) {
            console.log(e);
        });
#endif
    ::initializer init;
    bool make_mode          = false;
    bool use_stdin          = false;
    bool recursive          = false;
    unsigned trust_lvl      = LEAN_BELIEVER_TRUST_LEVEL+1;
    bool only_deps          = false;
    bool test_suite         = false;
    // unsigned num_threads    = 0;
#if defined(LEAN_MULTI_THREAD)
    // num_threads = hardware_concurrency();
#endif
#if defined(LEAN_JSON)
    bool json_output        = false;
#endif

    standard_search_path path;

    options opts;
    optional<std::string> server_in;
    std::string native_output;
    optional<std::string> cpp_output;
    while (true) {
        int c = getopt_long(argc, argv, g_opt_str, g_long_options, NULL);
        if (c == -1)
            break; // end of command line
        switch (c) {
        case 'j':
            // num_threads = static_cast<unsigned>(atoi(optarg));
            break;
        case 'v':
            display_header(std::cout);
            return 0;
        case 'g':
            std::cout << LEAN_GITHASH << "\n";
            return 0;
        case 'h':
            display_help(std::cout);
            return 0;
        case 'c':
            cpp_output = optarg;
            break;
        case 's':
            lean::lthread::set_thread_stack_size(static_cast<size_t>((atoi(optarg)/4)*4)*static_cast<size_t>(1024));
            break;
        case 'i':
            use_stdin = true;
            break;
        case 'm':
            make_mode = true;
            recursive = true;
            break;
        case 'R':
            recursive = true;
            break;
        case 'n':
            native_output         = optarg;
            break;
        case 'M':
            opts = opts.update(get_max_memory_opt_name(), atoi(optarg));
            break;
        case 'T':
            opts = opts.update(get_timeout_opt_name(), atoi(optarg));
            break;
        case 't':
            trust_lvl = atoi(optarg);
            break;
        case 'q':
            opts = opts.update(lean::get_verbose_opt_name(), false);
            break;
        case 'd':
            only_deps = true;
            break;
        case 'D':
            try {
                opts = set_config_option(opts, optarg);
            } catch (lean::exception & ex) {
                std::cerr << ex.what() << std::endl;
                return 1;
            }
            break;
#if defined(LEAN_JSON)
        case 'J':
            opts = opts.update(lean::name{"trace", "as_messages"}, true);
            json_output = true;
            break;
        case 'p': {
            json out;

            auto & out_path = out["path"] = json::array();
            for (auto & p : path.get_path()) out_path.push_back(p);

            out["leanpkg_path_file"] = path.m_leanpkg_path_fn ? *path.m_leanpkg_path_fn : path.m_user_leanpkg_path_fn;
            out["is_user_leanpkg_path"] = !path.m_leanpkg_path_fn;

            std::cout << std::setw(2) << out << std::endl;
            return 0;
        }
#endif
        case 'P':
            opts = opts.update("profiler", true);
            break;
        case 'e':
            test_suite = true;
            opts = opts.update(lean::name{"trace", "as_messages"}, true);
            break;
#if defined(LEAN_DEBUG)
        case 'B':
            lean::enable_debug(optarg);
            break;
#endif
        default:
            std::cerr << "Unknown command line option\n";
            display_help(std::cerr);
            return 1;
        }
    }

    if (use_stdin)
        recursive = false;

    if (auto max_memory = opts.get_unsigned(get_max_memory_opt_name(),
                                            opts.get_bool("server") ? LEAN_SERVER_DEFAULT_MAX_MEMORY : LEAN_DEFAULT_MAX_MEMORY)) {
        set_max_memory_megabyte(max_memory);
    }

    if (auto timeout = opts.get_unsigned(get_timeout_opt_name(),
                                         opts.get_bool("server") ? LEAN_SERVER_DEFAULT_MAX_HEARTBEAT : LEAN_DEFAULT_MAX_HEARTBEAT)) {
        set_max_heartbeat_thousands(timeout);
    }

    environment env(trust_lvl);

    io_state ios(opts, lean::mk_pretty_formatter_factory());

    if (json_output) ios.set_regular_channel(ios.get_diagnostic_channel_ptr());

    scope_global_ios scope_ios(ios);
    type_context_old trace_ctx(env, opts);
    scope_trace_env scope_trace(env, opts, trace_ctx);

    try {
        module_mgr mod_mgr(path.get_path(), env, ios);
        mod_mgr.set_save_olean(make_mode);

        std::vector<std::string> args(argv + optind, argv + argc);
        if (recursive) {
            if (args.empty()) args.push_back(".");
            std::vector<std::string> files;
            for (auto & f : args) {
                if (auto i_d = is_dir(f)) {
                    if (*i_d) {
                        find_files(f, ".lean", files);
                    } else {
                        files.push_back(f);
                    }
                }
            }
            args.clear();
            for (auto & f : files) {
                if (is_lean_file(f))
                    args.push_back(f);
            }
        }
        std::vector<std::string> module_args;
        for (auto & f : args) module_args.push_back(lrealpath(f));

        if (only_deps) {
            for (auto const & mod_fn : module_args) {
                auto contents = read_file(mod_fn);
                for (auto const & import : mod_mgr.get_direct_imports(mod_fn, contents)) {
                    std::string m_name = find_file(path.get_path(), import, {".lean"});
                    auto last_idx = m_name.find_last_of(".");
                    std::string rawname = m_name.substr(0, last_idx);
                    std::string ext = m_name.substr(last_idx);
                    m_name = rawname + ".olean";
                    std::cout << m_name << "\n";
                }
            }
            return 0;
        }

        struct input_mod {
            std::string m_file_name;
            std::shared_ptr<module_info const> m_mod_info;
        };
        std::vector<input_mod> mods;
        for (auto & mod : module_args) {
            auto mod_info = mod_mgr.get_module(module_name_of_file(path.get_path(), mod));
            mods.push_back({mod, mod_info});
        }

        bool ok = true;

        if (use_stdin) {
            std::stringstream buf;
            buf << std::cin.rdbuf();

            // This is where we will later spin off the server
            scope_global_ios scope_ios(ios);
            scope_traces_as_messages scope_trace_msgs("<stdin>", {1, 0});
            message_log l;
            scope_message_log scope_log(l);
            auto imports = mod_mgr.get_direct_imports("<stdin>", buf.str());
            std::set<module_name> failed_imports;
            for (auto & d : imports) {
                auto d_mod = mod_mgr.get_module(d);
                if (d_mod->m_log.has_errors())
                    // error in this import
                    failed_imports.insert(d_mod->m_name);
                else
                    // errors (maybe 0) in a transitive import
                    failed_imports.insert(d_mod->m_failed_deps.begin(), d_mod->m_failed_deps.end());
            }
            for (auto const & d : failed_imports) {
                message_builder msg(env, ios, "<stdin>", {1, 0}, ERROR);
                msg << "import " << d << " has errors, aborting";
                msg.report();
                ok = false;
            }

            if (ok) {
                try {
                    auto mod_env = import_modules(env, imports, mod_mgr.mk_loader());
                    parser p(mod_env, ios, buf, "<stdin>");
                    // The server will obviously do something more complicated from here
                    p.parse_commands();
                } catch (exception const & ex) {
                    message_builder msg(env, ios, "<stdin>", {1, 0}, ERROR);
                    msg.set_exception(ex);
                    report_message(msg.build());
                }
            }

            for (auto const & msg : l.to_buffer()) {
                if (json_output) {
#if defined(LEAN_JSON)
                    print_json(std::cout, msg);
#endif
                } else {
                    std::cout << msg;
                }
            }
            if (l.has_errors())
                ok = false;
        }

        for (auto & mod : mods) {
            if (test_suite) {
                std::ofstream out(mod.m_file_name + ".test_suite.out");
                for (auto const & msg : mod.m_mod_info->m_log.to_buffer()) {
                    out << msg;
                }
            }
            if (test_suite) {
                std::ofstream status(mod.m_file_name + ".status");
                status << (!mod.m_mod_info->has_errors() ? 0 : 1);
            }
        }

        if (!json_output)
            display_cumulative_profiling_times(std::cerr);

        if (cpp_output) {
            if (mods.size() != 1) {
                std::cerr << "Error, option `--cpp=<file>` expects one and only one input module\n";
                return 1;
            }
            module_name mod_name = mods[0].m_mod_info->m_name;
            buffer<name> dep_names;
            for (auto d : mods[0].m_mod_info->m_deps) {
                dep_names.push_back(d.m_mod_info->m_name);
            }
            std::ofstream out(*cpp_output);
            print_cpp_code(out, env, mod_name, to_list(dep_names));
        }

        if (!test_suite) {
            for (auto & mod : mods) {
                for (auto const & msg : mod.m_mod_info->m_log.to_buffer()) {
                    if (json_output) {
#if defined(LEAN_JSON)
                        print_json(std::cout, msg);
#endif
                    } else {
                        std::cout << msg;
                    }
                }
                if (mod.m_mod_info->has_errors())
                    ok = false;
            }
        }
        return ok ? 0 : 1;
    } catch (lean::throwable & ex) {
        std::cerr << lean::message_builder(env, ios, "<unknown>", lean::pos_info(1, 1), lean::ERROR).set_exception(ex).build();
    } catch (std::bad_alloc & ex) {
        std::cerr << "out of memory" << std::endl;
    }
    return 1;
}
