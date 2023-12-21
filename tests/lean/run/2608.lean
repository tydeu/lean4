import Lean.Parser.Extra

/-
Tests that token kinds do not clash with user identifiers
(which they previously did).
-/

declare_syntax_cat bug (behavior := symbol)
syntax ident : bug

#check `(bug|ident)

section
#check `(bug|num)
local syntax num : bug
#check `(bug|num) -- previously errored; should now work
end

section
#check `(bug|scientific)
local syntax scientific : bug
#check `(bug|scientific) -- previously errored; should now work
end

section
#check `(bug|str)
local syntax str : bug
#check `(bug|str) -- previously errored; should now work
end

section
#check `(bug|char)
local syntax char : bug
#check `(bug|char) -- previously errored; should now work
end

section
#check `(bug|name)
local syntax name : bug
#check `(bug|name) -- previously errored; should now work
end

section
#check `(bug|interpolatedStr)
local syntax interpolatedStr(bug) : bug
#check `(bug|interpolatedStr) -- previously errored; should now work
end

open Lean.Parser
attribute [run_parser_attribute_hooks] fieldIdx

section
#check `(bug|fieldIdx)
local syntax fieldIdx : bug
#check `(bug|fieldIdx) -- previously errored; should now work
end
