/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lake.Toml.Decode
import Lake.Toml.Encode

open Lean Parser Meta Elab Deriving Command

namespace Lake.Toml

partial def mkDefaultValueAux : Term → Expr → TermElabM Term
  | x, .lam n _ b c =>
    if c.isExplicit then
      mkDefaultValueAux (Syntax.mkApp x #[mkIdent n]) b
    else
      mkDefaultValueAux x b
  | x, e =>
    let_expr id _ _ := e | return x
    return x

def mkDefaultValue (default : Name) : TermElabM Term := do
  mkDefaultValueAux (mkIdent default) (← getConstInfo default).value!

def mkDecodeTomlBodyForStruct (indName : Name) (arg : Ident) : TermElabM Term := do
  let fields := getStructureFields (← getEnv) indName
  let getters ← fields.mapM fun field => do
    if isSubobjectField? (← getEnv) indName field |>.isSome then
      `(doElem|tryDecode (decodeToml $arg))
    else if let some default := getDefaultFnForField? (← getEnv) indName field then
      `(doElem|Table.tryDecodeD $(quote field) $(← mkDefaultValue default) $arg)
    else
      `(doElem|Table.tryDecode $arg $(quote field))
  let fields := fields.map Lean.mkIdent
  `(do
    let $arg ← Value.decodeTable $arg
    ensureDecode do
    $[let $fields:ident ← $getters]*
    return { $[$fields:ident],* })

/-
def mkDecodeTomlBodyForInduct (ctx : Deriving.Context) (indName : Name) (arg : Ident) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
  let alts ← mkAlts indVal
  let auxTerm ← alts.foldrM (fun xs x => `(Except.orElseLazy $xs (fun _ => $x))) (← `(Except.error "no inductive constructor matched"))
  `(match $arg with
    ${alts}*
    | _ => throw (.mk v.ref "expected one of 'c', 'llvm', or 'default'"))
where
  mkAlts (indVal : InductiveVal) : TermElabM (Array Term) := do
  let mut alts := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let alt ← do forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut binders   := #[]
        let mut userNames := #[]
        for i in [:ctorInfo.numFields] do
          let x := xs[indVal.numParams + i]!
          let localDecl ← x.fvarId!.getDecl
          if !localDecl.userName.hasMacroScopes then
            userNames := userNames.push localDecl.userName
          let a := mkIdent (← mkFreshUserName `a)
          binders := binders.push (a, localDecl.type)
        let fromJsonFuncId := mkIdent ctx.auxFunNames[0]!
        -- Return syntax to parse `id`, either via `FromJson` or recursively
        -- if `id`'s type is the type we're deriving for.
        let mkFromJson (idx : Nat) (type : Expr) : TermElabM (TSyntax ``doExpr) :=
          if type.isAppOf indVal.name then `(Lean.Parser.Term.doExpr| $fromJsonFuncId:ident jsons[$(quote idx)]!)
          else `(Lean.Parser.Term.doExpr| fromJson? jsons[$(quote idx)]!)
        let identNames := binders.map Prod.fst
        let fromJsons ← binders.mapIdxM fun idx (_, type) => mkFromJson idx type
        let userNamesOpt ← if binders.size == userNames.size then
          ``(some #[$[$(userNames.map quote)],*])
        else
          ``(none)
        let stx ←
          `((Json.parseTagged json $(quote ctorName.eraseMacroScopes.getString!) $(quote ctorInfo.numFields) $(quote userNamesOpt)).bind
            (fun jsons => do
              $[let $identNames:ident ← $fromJsons:doExpr]*
              return $(mkIdent ctorName):ident $identNames*))
        pure (stx, ctorInfo.numFields)
      alts := alts.push alt
  -- the smaller cases, especially the ones without fields are likely faster
  let alts' := alts.qsort (fun (_, x) (_, y) => x < y)
  return alts'.map Prod.fst
-/

def mkDecodeTomlBody (ctx : Deriving.Context) (indName : Name) (arg : Ident) : TermElabM Term := do
  if isStructure (← getEnv) indName then
    mkDecodeTomlBodyForStruct indName arg
  else
    throwError "deriving DecodeToml does not support inductives"
    --mkDecodeTomlBodyForInduct ctx indName

def mkDecodeTomlAuxFun
  (ctx : Deriving.Context) (auxFunName : Name) (typeInfo : InductiveVal)
: TermElabM Command := do
  let header ← mkHeader ``DecodeToml 0 typeInfo
  let argId : Ident ← `(val)
  let arg ← `(Term.bracketedBinderF|($argId : Toml.Value))
  let header := {header with binders := header.binders.push arg}
  Term.elabBinders header.binders fun _ => do
  let type := header.targetType
  let auxFunId := mkIdent auxFunName
  let bs := TSyntaxArray.mk (ks := [``Term.bracketedBinder]) header.binders
  let body ← mkDecodeTomlBody ctx typeInfo.name argId
  if ctx.usePartial || typeInfo.isRec then
    let body ← mkLet (← mkLocalInstanceLetDecls ctx ``DecodeToml header.argNames) body
    `(private partial def $auxFunId $bs* : Except (Array DecodeError) $type := $body)
  else
    `(private def $auxFunId $bs* : Except (Array DecodeError) $type := $body)

def mkDecodeTomlMutualBlock (ctx : Deriving.Context) : TermElabM Command := do
  let mut auxDefs := #[]
  for h : i in [:ctx.typeInfos.size] do
    let auxFunName := ctx.auxFunNames[i]!
    let typeInfo   := ctx.typeInfos[i]'h.upper
    auxDefs := auxDefs.push (← mkDecodeTomlAuxFun ctx auxFunName typeInfo)
  `(mutual $auxDefs:command* end)

def mkDecodeTomlInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "decodeToml" declName
  let cmds := #[← mkDecodeTomlMutualBlock ctx] ++
    (← mkInstanceCmds ctx ``DecodeToml #[declName])
  trace[Elab.Deriving.decodeToml] "\n{cmds}"
  return cmds

/-
def mkToTomlInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkToTomlInstance declName
      cmds.forM elabCommand
    return true
  else
    return false
-/

def mkDecodeTomlInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkDecodeTomlInstance declName
      cmds.forM elabCommand
    return true
  else
    return false

initialize
  --registerDerivingHandler ``ToToml mkToTomlInstanceHandler
  registerDerivingHandler ``DecodeToml mkDecodeTomlInstanceHandler

  -- registerTraceClass `Elab.Deriving.toToml
  registerTraceClass `Elab.Deriving.decodeToml
