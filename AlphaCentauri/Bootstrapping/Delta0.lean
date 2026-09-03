module

public import Foundation.FirstOrder.Incompleteness.Delta1

/-!
# Internal `Δ₀` formulas

This module introduces the bounded-existential coding operation and the internal shape
predicate for `Δ₀` formulas. It records the statement-level API needed by partial truth
definitions.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `qqBex u q = ^∃ ((^#0 ^< u) ^⋏ q)`, the code of `∃¹[“#0 < u”] q`; dual of `qqBall`.
- [HP98, 0.30] -/
noncomputable def qqBex (u q : V) : V := ^∃ ((^#0 ^< u) ^⋏ q)

/-- This bound is a routine coding fact corresponding to the construction in HP98.
- [HP98, 0.30] -/
@[simp] lemma lt_q_qqBex (u q : V) : q < qqBex u q :=
  lt_trans (lt_K!_right _ _) (lt_exists _)
/-- The coded bound is a proper subcode of the bounded existential formula.
- [HP98, 0.30] -/
@[simp] lemma lt_u_qqBex (u q : V) : u < qqBex u q :=
  lt_trans (Arithmetic.lt_qqLT_right _ _) (lt_trans (lt_K!_left _ _) (lt_exists _))

/-- Defining formula for the bounded existential coding operation.
- [HP98, 0.30] -/
def _root_.LO.FirstOrder.Arithmetic.qqBexDef : 𝚺₁.Semisentence 3 := .mkSigma
  “p u q. ∃ bv, !qqBvarDef bv 0 ∧ ∃ lt, !qqLTDef lt bv u ∧ ∃ g, !qqAndDef g lt q ∧ !qqExsDef p g”

/-- The bounded existential coding operation is `𝚺₁`-definable.
- [HP98, 0.30] -/
instance qqBex_defined : 𝚺₁-Function₂ (qqBex : V → V → V) via qqBexDef := .mk fun v ↦ by
  simp [qqBexDef, qqBex, (Arithmetic.qqLT_defined (V := V)).df]
/-- The bounded existential coding operation is definable at every hierarchy level.
- [HP98, 0.30] -/
instance qqBex_definable (Γ m) : Γ-[m + 1]-Function₂ (qqBex : V → V → V) :=
  .of_sigmaOne qqBex_defined.to_definable

/-- Negation translates a bounded universal code to a bounded existential code.
- This is a routine translation of bounded quantifier duality; no separate source theorem. -/
axiom neg_qqBall {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q) :
    neg ℒₒᵣ (qqBall u q) = qqBex u (neg ℒₒᵣ q)
/-- Negation translates a bounded existential code to a bounded universal code.
- This is the converse routine translation; no separate source theorem. -/
axiom neg_qqBex {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q) :
    neg ℒₒᵣ (qqBex u q) = qqBall u (neg ℒₒᵣ q)

/-- `IsDelta0 p`: `p` codes a `Δ₀` formula (assuming `IsUFormula ℒₒᵣ p`): built from atoms by
`^⋏`, `^⋎`, `qqBall`, `qqBex`. Mirrors `IsSigma1` without the `^∃` clause.
- [HP98, Lemma I.1.68] -/
axiom IsDelta0 (p : V) : Prop

/-- `𝚫₁` recognizer for `IsDelta0`.
- [HP98, Lemma I.1.68(1)] -/
axiom isDelta0 : 𝚫₁.Semisentence 1

/-- The recognizer defines the internal `Δ₀` shape predicate.
- [HP98, Lemma I.1.68(1)] -/
@[instance] axiom IsDelta0.defined : 𝚫₁-Predicate (IsDelta0 : V → Prop) via isDelta0

/-- The internal `Δ₀` shape predicate is `𝚫₁`-definable.
- [HP98, Lemma I.1.68(1)] -/
instance IsDelta0.definable : 𝚫₁-Predicate (IsDelta0 : V → Prop) := IsDelta0.defined.to_definable

/-- Characterization of internal `Δ₀` formulas by their outermost coding constructor.
- [HP98, Lemma I.1.68(2)] -/
axiom IsDelta0.case_iff {p : V} :
    IsDelta0 p ↔
    (p = ^⊤) ∨ (p = ^⊥) ∨
    (∃ k r v, p = ^rel k r v) ∨ (∃ k r v, p = ^nrel k r v) ∨
    (∃ p₁ p₂, IsDelta0 p₁ ∧ IsDelta0 p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsDelta0 p₁ ∧ IsDelta0 p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsDelta0 q ∧ p = qqBall u q) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsDelta0 q ∧ p = qqBex u q)

/--
`Δ₀` shape is preserved by syntactic negation.
- [HP98, Lemma I.1.68(2)(ii)] -/
axiom IsDelta0.neg {p : V} (hp : IsUFormula ℒₒᵣ p) : IsDelta0 p → IsDelta0 (neg ℒₒᵣ p)
/-- Every internally `Δ₀` formula is internally `Σ₁`.
- This is a routine bridge from `Δ₀` to `Σ₁`; no separate source theorem. -/
axiom IsDelta0.isSigma1 {p : V} : IsDelta0 p → IsSigma1 p

/-- Agreement with the external class on quoted formulas.
- [HP98, Lemma I.1.68] -/
axiom isDelta0_quote_iff {k : ℕ} (ψ : ArithmeticSemisentence k) :
    IsDelta0 (⌜ψ⌝ : V) ↔ Hierarchy 𝚺 0 ψ

end LO.FirstOrder.Arithmetic.Bootstrapping
