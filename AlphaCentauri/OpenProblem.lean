module

public meta import Lean.Elab.Command
public meta import AlphaCentauri.OpenProblem.Attribute

/-!
# Open problems

`open_problem Name binders := p` declares an open problem: a proposition `p` whose truth is
unknown. It elaborates as `def Name binders : Prop := p` and records `Name` in `openProblemAttr`,
from which the executable `open_problems` collects the open problems of the library, with their
docstrings, into the list published on the project's pages.

An open problem is stated, never assumed: it is not an `axiom`, since a statement of unknown truth
may be false, or contradict a known theorem once combined with another open problem. A result
depending on it takes it as a hypothesis `(h : Name)`.
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
@[command_elab openProblem] def elabOpenProblem : CommandElab := fun stx => do
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
