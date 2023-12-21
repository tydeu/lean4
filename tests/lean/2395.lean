import Lean

declare_syntax_cat cat
syntax char : cat
syntax "char" : cat

elab "test" c:cat : command =>
  IO.println c

-- (choice (catChar "char") (cat_ "char"))
test char
