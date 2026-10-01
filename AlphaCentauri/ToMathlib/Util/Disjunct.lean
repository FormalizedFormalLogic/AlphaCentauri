module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.Apply

/-!
# The `disj` tactic

`disj n` selects the `n`-th disjunct of a goal that is an iterated disjunction, replacing the
chain of `left` and `right` (or of `Or.inl` and `Or.inr`) that would otherwise name it.
-/

public meta section

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/-- The number of disjuncts of `e`, read as a right-nested chain `p₁ ∨ p₂ ∨ ⋯ ∨ pₙ`. -/
private partial def numDisjuncts (e : Expr) : MetaM Nat := do
  let e ← whnfR e
  if e.isAppOfArity ``Or 2 then
    return (← numDisjuncts e.appArg!) + 1
  else
    return 1

/-- Apply `Or.inl` or `Or.inr` to `goal`, whose target is a disjunction. -/
private def applyOrSide (goal : MVarId) (side : Name) : MetaM MVarId := do
  match ← goal.applyConst side with
  | [goal] => return goal
  | goals => throwError "`{side}` left {goals.length} goals"

/-- Replace the target of `goal`, a right-nested disjunction `p₁ ∨ p₂ ∨ ⋯ ∨ pₙ`, by its `i`-th
disjunct `pᵢ`, counting from `1`. -/
def selectDisjunct (goal : MVarId) (i : Nat) : MetaM MVarId := goal.withContext do
  let target ← goal.getType'
  let n ← numDisjuncts target
  if i = 0 then
    throwError "disjuncts are numbered from 1; `disj 1` selects the leftmost one"
  if n < i then
    throwError "the goal has {n} disjunct(s), but `disj {i}` was asked for{indentExpr target}"
  let mut goal := goal
  for _ in [0:i - 1] do
    goal ← applyOrSide goal ``Or.inr
  if i < n then
    goal ← applyOrSide goal ``Or.inl
  return goal

/--
`disj n` replaces a goal `p₁ ∨ p₂ ∨ ⋯ ∨ pₙ ∨ ⋯` by its `n`-th disjunct, counting from `1`; it
is `right` applied `n - 1` times followed by `left`. The disjuncts are those of the right-nested
chain the goal displays, so `disj 2` on `p ∨ (q ∨ r) ∨ s` leaves `q ∨ r`.
-/
elab (name := disj) "disj " i:num : tactic =>
  liftMetaTactic1 fun goal => selectDisjunct goal i.getNat

end Mathlib.Tactic
