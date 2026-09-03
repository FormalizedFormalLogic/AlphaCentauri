module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Finite axiomatizability of `𝗜𝚺 n`

For `n ≥ 1`, `𝗜𝚺 n` is finitely axiomatizable: although the induction scheme `InductionScheme ℒₒᵣ
(Hierarchy 𝚺 n)` has infinitely many instances, a partial satisfaction predicate for `Σₙ` formulas
lets `n`-many of them be replaced by a single sentence expressing induction for that predicate. The
same argument in fact produces a single `Πₙ₊₂` sentence axiomatizing `𝗜𝚺 n`.

Both statements are recorded here with `sorry` bodies; the proof needs the partial truth
predicates `Sat_{Σ,n}` (#1, not yet formalized) and the API around `Entailment.FiniteAxiomatizable`
(#11, not yet grown), so it is deferred to a later revision of this file. `𝗕𝚺`, the collection
scheme of [HP98, §I.2(a)], does not exist in Foundation yet either (there is no `Collection`- or
`BSigma`-named declaration anywhere under `Foundation.FirstOrder.Arithmetic`), so the third
statement of [HP98, Theorem I.2.52] (`𝗕𝚺 (n + 1)` is finitely axiomatizable) is left out entirely
rather than stated against an invented notation.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

/-- For `n ≥ 1`, `𝗜𝚺 n` is finitely axiomatizable.
- [HP98, Theorem I.2.52] -/
theorem ISigma.finiteAxiomatizable (n : ℕ) (hn : 1 ≤ n) : Entailment.FiniteAxiomatizable (𝗜𝚺 n) := by
  sorry

/-- For `n ≥ 1`, `𝗜𝚺 n` is axiomatized by a single `𝚷 (n + 2)` sentence.
- [HP98, Remark I.4.35(1)] -/
theorem ISigma.exists_pi_sentence (n : ℕ) (hn : 1 ≤ n) :
    ∃ σ : ArithmeticSentence, Hierarchy 𝚷 (n + 2) σ ∧ ({σ} : ArithmeticTheory) ≊ 𝗜𝚺 n := by
  sorry

end LO.FirstOrder.Arithmetic
