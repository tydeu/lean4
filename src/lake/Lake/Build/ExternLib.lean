/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.FacetConfig
public import Lake.Build.Job.Monad
import Lake.Build.Job.Register
import Lake.Build.Common
import Lake.Build.Infos

/-! # External Library Build
Build function definitions for external libraries.
-/

open System

namespace Lake

def ExternLib.recBuildStatic (lib : ExternLib) : FetchM (Job Artifact) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:static" do
  lib.config.getArtifact <$> fetch (lib.pkg.target lib.staticTargetName)

/-- The facet configuration for the builtin `ExternLib.staticFacet`. -/
public def ExternLib.staticFacetConfig : ExternLibFacetConfig staticFacet :=
  mkFacetJobConfig recBuildStatic

/--
Build a shared library from a static library using `leanc`
using the Lean toolchain's linker.
-/
public def buildLeanSharedLibOfStatic
  (staticLibJob : Job Artifact)
  (weakArgs traceArgs : Array String := #[])
: SpawnM (Job Artifact) :=
  staticLibJob.mapM fun staticLib => do
    addLeanTrace
    addPureTrace traceArgs
    addPlatformTrace -- shared libraries are platform-dependent artifacts
    let staticLibPath := staticLib.path
    let dynlib := staticLibPath.withExtension sharedLibExt
    buildFileUnlessUpToDate' dynlib do
      let lean ← getLeanInstall
      let baseArgs :=
        if System.Platform.isOSX then
          #[s!"-Wl,-force_load,{staticLibPath}"]
        else
          #["-Wl,--whole-archive", staticLibPath.toString, "-Wl,--no-whole-archive"]
      let args := baseArgs ++ weakArgs ++ traceArgs ++
        #["-L", lean.leanLibDir.toString] ++ lean.ccLinkSharedFlags
      compileSharedLib dynlib args lean.cc
    -- `buildFileUnlessUpToDate'` set the trace to the built file's hash and mtime
    return .ofTrace dynlib (← getTrace) sharedLibExt

def ExternLib.recBuildShared (lib : ExternLib) : FetchM (Job Artifact) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:shared" do
  buildLeanSharedLibOfStatic (← lib.static.fetch) lib.linkArgs

/-- The facet configuration for the builtin `ExternLib.sharedFacet`. -/
public def ExternLib.sharedFacetConfig : ExternLibFacetConfig sharedFacet :=
  mkFacetJobConfig recBuildShared

/-- Construct a `Dynlib` object for a shared library target. -/
def computeDynlibOfShared (sharedLibTarget : Job Artifact) : SpawnM (Job Dynlib) :=
  sharedLibTarget.mapM fun sharedLib => do
    let sharedLibPath := sharedLib.path
    if let some stem := sharedLibPath.fileStem then
      if Platform.isWindows then
        return {path := sharedLibPath, name := stem}
      else if stem.startsWith "lib" then
        return {path := sharedLibPath, name := stem.drop 3 |>.copy}
      else
        error s!"shared library `{sharedLibPath}` does not start with `lib`; this is not supported on Unix"
    else
      error s!"shared library `{sharedLibPath}` has no file name"

def ExternLib.recComputeDynlib (lib : ExternLib) : FetchM (Job Dynlib) := do
  withRegisterJob s!"{lib.staticTargetName.toString}:dynlib" do
  computeDynlibOfShared (← lib.shared.fetch)

/-- The facet configuration for the builtin `ExternLib.dynlibFacet`. -/
public def ExternLib.dynlibFacetConfig : ExternLibFacetConfig dynlibFacet :=
  mkFacetJobConfig recComputeDynlib

def ExternLib.recBuildDefault (lib : ExternLib) : FetchM (Job Artifact) :=
  lib.static.fetch

/-- The facet configuration for the builtin `ExternLib.dynlibFacet`. -/
public def ExternLib.defaultFacetConfig : ExternLibFacetConfig defaultFacet :=
  mkFacetJobConfig recBuildDefault (memoize := false)

/--
A name-configuration map for the initial set of
external library facets (e.g., `static`, `shared`).
-/
public def ExternLib.initFacetConfigs : DNameMap ExternLibFacetConfig :=
  DNameMap.empty
  |>.insert defaultFacet defaultFacetConfig
  |>.insert staticFacet staticFacetConfig
  |>.insert sharedFacet sharedFacetConfig
  |>.insert dynlibFacet dynlibFacetConfig
