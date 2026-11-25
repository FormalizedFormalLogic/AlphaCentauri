module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public meta import Lean.Elab.InfoTree.Util

/-! # A linter for arguments repeated in a section -/

public meta section

open Lean Elab Command Linter

namespace AlphaCentauri.Linter

/--
The "repeatedBinder" linter warns when two declarations of the same `section` or `namespace` take an
argument with the same signature, that is, the same name, the same kind of binder and the same type:
```
section

lemma lem1 {a : Nat} : True := trivial

lemma lem2 {a : Nat} : True := trivial -- warning

end
```
Such an argument is to be declared once, by `variable {a : Nat}`.

Types are compared as syntax, up to whitespace and comments. If a type mentions other arguments, or
section variables, these are to have the same signature as well. Arguments without a type or with a
default value, `_`, hypotheses, and arguments depending on any of them, are ignored. A hypothesis is
an argument whose type is a proposition; instance arguments are compared even if their class is a
proposition.

Two declarations are in the same section if the innermost `section` or `namespace` they are in is
the same; the file outside of any `section` and `namespace` counts as one.
-/
register_option linter.style.repeatedBinder : Bool := {
  defValue := true
  descr := "enable the repeatedBinder linter"
}

namespace RepeatedBinder

/-- A bracketed binder split into its parts. -/
structure BinderParts where
  /-- The opening bracket. -/
  opening : String
  /-- The closing bracket. -/
  closing : String
  /-- The syntax of the bound names, empty for an anonymous instance. -/
  names : Array Syntax
  /-- The type, unless it is omitted or the binder has a default value. -/
  type? : Option Syntax

/-- Splits a binder of any of the four kinds. -/
def BinderParts.ofSyntax? (stx : Syntax) : Option BinderParts :=
  let type? := if stx[2].getNumArgs == 2 then some stx[2][1] else none
  if stx.isOfKind ``Parser.Term.explicitBinder then
    some ⟨"(", ")", stx[1].getArgs, if stx[3].isNone then type? else none⟩
  else if stx.isOfKind ``Parser.Term.implicitBinder then
    some ⟨"{", "}", stx[1].getArgs, type?⟩
  else if stx.isOfKind ``Parser.Term.strictImplicitBinder then
    some ⟨"⦃", "⦄", stx[1].getArgs, type?⟩
  else if stx.isOfKind ``Parser.Term.instBinder then
    some ⟨"[", "]", if stx[1].isNone then #[] else #[stx[1][0]], some stx[2]⟩
  else
    none

/-- The tokens of `stx`, without whitespace and comments. -/
partial def tokens : Syntax → Array String
  | .atom _ val => #[val]
  | .ident _ raw _ _ => #[raw.toString]
  | .node _ _ args => args.flatMap tokens
  | .missing => #[]

/-- The first components of the identifiers of `stx`. -/
partial def rootIdents : Syntax → Array Name
  | .ident _ _ val _ => #[val.eraseMacroScopes.getRoot]
  | .node _ _ args => args.flatMap rootIdents
  | _ => #[]

/-- The source of `stx` on one line. -/
def sourceLine (stx : Syntax) : String :=
  match stx.getSubstring? (withLeading := false) (withTrailing := false) with
  | some s => " ".intercalate <| s.toString.split Char.isWhitespace |>.toList.map (·.toString)
      |>.filter (· != "")
  | none => " ".intercalate (tokens stx).toList

/-- An argument as the linter compares it. -/
structure Argument where
  /-- The signature, including that of the arguments the type mentions. -/
  signature : String
  /-- The argument as a binder of its own, for the message. -/
  display : String
  /-- The binder declaring the argument. -/
  ref : Syntax

/-- The signatures of the names in scope; `none` for an argument which is not compared. -/
abbrev Context := NameMap (Option String)

/-- Reads one binder after `ctx`, and returns the arguments it declares. Names that do not satisfy
`isData` are not compared. -/
def readBinder (ctx : Context) (stx : Syntax) (isData : Syntax → Bool := fun _ ↦ true) :
    Context × Array Argument := Id.run do
  let some parts := BinderParts.ofSyntax? stx
    | return (rootIdents stx |>.foldl (·.insert · none) ctx, #[])
  let name (s : Syntax) : Name := s.getId.eraseMacroScopes
  let some type := parts.type?
    | return (parts.names.foldl (fun c n ↦ c.insert (name n) none) ctx, #[])
  let dependencies := (rootIdents type).filterMap ctx.find?
  let comparable := dependencies.all Option.isSome
  let typeSignature := " ".intercalate (tokens type).toList ++
    String.join (dependencies.toList.map fun d ↦ s!" {hash d}")
  let mkArgument (pre : String) : Argument :=
    { signature := s!"{parts.opening}{pre}{typeSignature}{parts.closing}"
      display := s!"{parts.opening}{pre}{sourceLine type}{parts.closing}"
      ref := stx }
  if parts.names.isEmpty then
    return (ctx, if comparable then #[mkArgument ""] else #[])
  let mut ctx := ctx
  let mut arguments := #[]
  for n in parts.names do
    let argument := mkArgument s!"{name n} : "
    if comparable && n.isIdent && (parts.opening == "[" || isData n) then
      ctx := ctx.insert (name n) (some argument.signature)
      arguments := arguments.push argument
    else
      ctx := ctx.insert (name n) none
  return (ctx, arguments)

/-- Reads the binders of a `variable` command after `ctx`. A binder without a type only changes the
kind of a variable, and is skipped when there is such a variable. -/
def readVariables (ctx : Context) (binders : Array Syntax) : Context :=
  binders.foldl (init := ctx) fun ctx stx ↦
    match BinderParts.ofSyntax? stx with
    | some { names, type? := none, .. } =>
      if names.all (ctx.contains ·.getId.eraseMacroScopes) then ctx else (readBinder ctx stx).1
    | _ => (readBinder ctx stx).1

/-- A declaration together with the binders of its signature. -/
structure Declaration where
  /-- The name, unless the declaration is anonymous. -/
  name? : Option Name
  /-- The syntax of the declaration. -/
  ref : Syntax
  /-- The variables declared by `variable … in` in front of the declaration. -/
  localVariables : Array Syntax
  /-- The binders of the signature. -/
  binders : Array Syntax

/-- The signature of a declaration, which comes before any value, constructor or field. -/
partial def findSignature? (stx : Syntax) : Option Syntax :=
  if stx.isOfKind ``Parser.Command.declSig || stx.isOfKind ``Parser.Command.optDeclSig then
    some stx
  else
    stx.getArgs.findSome? findSignature?

/-- The binders of a declaration, also if its command takes binders without a `declSig`. -/
def signatureBinders (stx : Syntax) : Array Syntax :=
  match findSignature? stx with
  | some signature => signature[0].getArgs
  | none =>
    match stx.find? fun s ↦ s.getArgs.any (·.isOfKind ``Parser.Command.declId) with
    | some s => s.getArgs.flatMap fun arg ↦
        arg.getArgs.filter fun b ↦ (BinderParts.ofSyntax? b).isSome
    | none => #[]

/-- The declarations of a command. -/
partial def declarations (stx : Syntax) (localVariables : Array Syntax := #[]) :
    Array Declaration :=
  if stx.isOfKind ``Parser.Command.in then
    let here := if stx[0].isOfKind ``Parser.Command.variable then stx[0][2].getArgs else #[]
    let disabled := stx[0].isOfKind ``Parser.Command.set_option &&
      stx[0][1].getId == `linter.style.repeatedBinder && stx[0][3].isToken "false"
    if disabled then #[] else declarations stx[2] (localVariables ++ here)
  else if stx.isOfKind ``Parser.Command.mutual then
    stx[1].getArgs.flatMap (declarations · localVariables)
  else if stx[0].isOfKind ``Parser.Command.declModifiers then
    let name? := stx.find? (·.isOfKind ``Parser.Command.declId) |>.map (·[0].getId)
    #[{ name?, ref := stx, localVariables, binders := signatureBinders stx }]
  else
    #[]

/-- The first declaration of a section taking an argument. -/
structure Occurrence where
  /-- The name of the declaration, unless it is anonymous. -/
  name? : Option Name
  /-- The line of the argument. -/
  line : Nat

/-- The arguments seen so far in each open section, innermost first. -/
abbrev State := List (Std.HashMap String Occurrence)

/-- Adjusts the state to `depth` open scopes, dropping the closed sections. -/
def resize (state : State) (depth : Nat) : State :=
  List.replicate (depth - state.length) {} ++ state.drop (state.length - depth)

/-- The positions of the names bound in `binders` that elaborated to something else than a proof. -/
def dataPositions (binders : Array Syntax) : CommandElabM (Std.HashSet String.Pos.Raw) := do
  let mut positions : Std.HashSet String.Pos.Raw := {}
  for binder in binders do
    if let some parts := BinderParts.ofSyntax? binder then
      for n in parts.names do
        if let some pos := n.getPos? then positions := positions.insert pos
  if positions.isEmpty then return {}
  let mut infos : Std.HashMap String.Pos.Raw (ContextInfo × TermInfo) := {}
  for tree in (← getInfoTrees) do
    infos := tree.foldInfo (init := infos) fun ctx info infos ↦ Id.run do
      let .ofTermInfo info := info | return infos
      unless info.isBinder && info.expr.isFVar do return infos
      let some pos := info.stx.getPos? | return infos
      if positions.contains pos then infos.insertIfNew pos (ctx, info) else infos
  let mut result := {}
  for (pos, ctx, info) in infos do
    let isProof ← try info.runMetaM ctx (Meta.isProof info.expr) catch _ => pure true
    unless isProof do result := result.insert pos
  return result

/-- Compares `declaration` with the arguments `seen` in its section, and adds its own. -/
def check (declaration : Declaration) (seen : Std.HashMap String Occurrence) :
    CommandElabM (Std.HashMap String Occurrence) := do
  let mut ctx := readVariables {} ((← getScope).varDecls.map (·.raw))
  ctx := readVariables ctx declaration.localVariables
  let mut seen := seen
  let mut own : Std.HashSet String := {}
  let fileMap ← getFileMap
  let positions ← dataPositions declaration.binders
  for binder in declaration.binders do
    let (ctx', arguments) := readBinder ctx binder fun n ↦ n.getPos?.any positions.contains
    ctx := ctx'
    for argument in arguments do
      if own.contains argument.signature then continue
      own := own.insert argument.signature
      match seen[argument.signature]? with
      | none =>
        let line := (fileMap.toPosition (argument.ref.getPos?.getD 0)).line
        seen := seen.insert argument.signature { name? := declaration.name?, line }
      | some first =>
        let other := match first.name? with
          | some n => m!"`{n}`"
          | none => m!"an anonymous declaration"
        logLint linter.style.repeatedBinder argument.ref
          m!"The argument `{argument.display}` is repeated: {other} (line {first.line}) in the \
            same section takes it as well. Declare it once by `variable {argument.display}`."
  return seen

@[inherit_doc linter.style.repeatedBinder]
initialize repeatedBinderLinter : StatefulLinter State Unit ←
  registerStatefulLinter ([] : State) (post := fun stx state _ _ _ ↦ do
    let state := resize state (← get).scopes.length
    if stx.hasMissing then return state
    let seen := state.headD {}
    let seen ← withSetOptionIn (fun stx ↦ do
      unless getLinterValue linter.style.repeatedBinder (← getLinterOptions) do return seen
      (declarations stx).foldlM (fun seen d ↦ check d seen) seen) stx
    return seen :: state.tail)

end RepeatedBinder

end AlphaCentauri.Linter
