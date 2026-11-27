module

public meta import Lean.Elab.Command
public import AlphaCentauri.Init
public meta import AlphaCentauri.OpenProblem.Attribute

/-!
# Open problems

The command `open_problem`, which declares a proposition of unknown truth and records it.
-/

public meta section

open Lean Elab Command

namespace AlphaCentauri

/--
`open_problem Name binders := p` declares the proposition `p` as an open problem: it is
`def Name binders : Prop := p`, recorded as an open problem of the library. The docstring is
mandatory; it asks the problem as a question and cites its source.
-/
syntax (name := openProblem) declModifiers
  group("open_problem " declId (ppSpace bracketedBinder)* " := " term) : command

/-- Elaborates `open_problem` as a definition of a proposition, and records it. -/
@[command_elab openProblem]
def elabOpenProblem : CommandElab := fun stx => do
  let mods : TSyntax ``Parser.Command.declModifiers := ⟨stx[0]⟩
  let declId : TSyntax ``Parser.Command.declId := ⟨stx[1][1]⟩
  let binders : TSyntaxArray ``Parser.Term.bracketedBinder := stx[1][2].getArgs.map (⟨·⟩)
  let body : Term := ⟨stx[1][4]⟩
  if mods.raw[0].isNone then
    throwErrorAt declId "an open problem needs a docstring stating it and citing its source"
  elabCommand <| ← `($mods:declModifiers def $declId $binders* : Prop := $body)
  let name ← liftTermElabM <| realizeGlobalConstNoOverload declId.raw[0]
  openProblemAttr.setTag name

end AlphaCentauri
