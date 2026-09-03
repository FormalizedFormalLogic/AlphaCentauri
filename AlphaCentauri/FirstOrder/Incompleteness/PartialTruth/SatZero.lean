module

public import AlphaCentauri.FirstOrder.Bootstrapping.Delta0
public import AlphaCentauri.FirstOrder.Bootstrapping.TermVal

/-!
# Satisfaction for `Δ₀` formulas

This module states an internally coded partial satisfaction table for bounded formulas.
It exposes the resulting `Δ₀` satisfaction predicate and its Tarski conditions.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `PSatZero q z e` says that `q` is a partial satisfaction table for the `Δ₀` formula
`z` under assignment `e`. Its domain is the downward closure of `⟪z, e⟫` under immediate
subformulas, extending the assignment when entering bounded quantifiers.

- [HP98, Definition I.1.71(1)] -/
def PSatZero (q z e : V) : Prop := sorry

/-- The `𝚫₁` formula defining partial satisfaction tables.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def pSatZero : 𝚫₁.Semisentence 3 := sorry

/-- The formula `pSatZero` defines partial satisfaction tables.
- [HP98, Lemma I.1.72(1)] -/
instance PSatZero.defined : 𝚫₁-Relation₃ (PSatZero : V → V → V → Prop) via pSatZero := sorry

/-- Partial satisfaction tables form a `𝚫₁`-definable relation.
- [HP98, Lemma I.1.72(1)] -/
instance PSatZero.definable : 𝚫₁-Relation₃ (PSatZero : V → V → V → Prop) :=
  PSatZero.defined.to_definable

/-- A partial satisfaction table for a fixed formula and assignment is unique.
- [HP98, Lemma I.1.72(2)] -/
lemma PSatZero.uniq {q₁ q₂ z e : V} (h₁ : PSatZero q₁ z e) (h₂ : PSatZero q₂ z e) :
    q₁ = q₂ := sorry

/-- Every well-formed internally `Δ₀` formula has a partial satisfaction table.
- [HP98, Lemma I.1.72(3)] -/
lemma PSatZero.exists {z e : V} (hz : IsDelta0 z) (hz' : IsUFormula ℒₒᵣ z) :
    ∃ q, PSatZero q z e := sorry

/-- `SatZero z e` says that the internally coded `Δ₀` formula `z` is satisfied by `e`.
- [HP98, Definition I.1.71(2)] -/
def SatZero (z e : V) : Prop := ∃ q, PSatZero q z e ∧ ⟪⟪z, e⟫, 1⟫ ∈ q

/-- The `𝚫₁` formula defining satisfaction for internally coded `Δ₀` formulas.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
noncomputable def satZero : 𝚫₁.Semisentence 2 := sorry

/-- The formula `satZero` defines `SatZero`.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
instance SatZero.defined : 𝚫₁-Relation (SatZero : V → V → Prop) via satZero := sorry

/-- Satisfaction for internally coded `Δ₀` formulas is `𝚫₁`-definable.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
instance SatZero.definable : 𝚫₁-Relation (SatZero : V → V → Prop) :=
  SatZero.defined.to_definable

/-! ## Tarski conditions -/

/-- Satisfaction implies that its formula code belongs to the `Δ₀` domain.
- [HP98, Theorem I.1.70(i)] -/
lemma SatZero.dom {z e : V} : SatZero z e → IsDelta0 z ∧ IsUFormula ℒₒᵣ z := sorry

/-- The coded truth constant is satisfied.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma SatZero.verum (e : V) : SatZero ^⊤ e := sorry

/-- The coded falsehood constant is not satisfied.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma SatZero.falsum (e : V) : ¬SatZero ^⊥ e := sorry

/-- Satisfaction of coded equality agrees with equality of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma SatZero.eq_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^= u) e ↔ termVal e t = termVal e u := sorry

/-- Satisfaction of coded inequality agrees with inequality of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma SatZero.neq_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^≠ u) e ↔ termVal e t ≠ termVal e u := sorry

/-- Satisfaction of coded less-than agrees with comparison of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma SatZero.lt_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^< u) e ↔ termVal e t < termVal e u := sorry

/-- Satisfaction of coded negated less-than agrees with failure of comparison.
- [HP98, Theorem I.1.70(ii)] -/
lemma SatZero.nlt_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^≮ u) e ↔ ¬(termVal e t < termVal e u) := sorry

/-- Satisfaction commutes with coded conjunction.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma SatZero.and_iff {p q e : V} :
    SatZero (p ^⋏ q) e ↔ SatZero p e ∧ SatZero q e := sorry

/-- Satisfaction commutes with coded disjunction.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma SatZero.or_iff {p q e : V} :
    SatZero (p ^⋎ q) e ↔ SatZero p e ∨ SatZero q e := sorry

/-- Satisfaction commutes with coded negation on `Δ₀` formulas.
- [HP98, Theorem I.1.70(iii)] -/
lemma SatZero.neg_iff {p e : V} (hp : IsDelta0 p) (hp' : IsUFormula ℒₒᵣ p) :
    SatZero (neg ℒₒᵣ p) e ↔ ¬SatZero p e := sorry

/-- Satisfaction of a bounded universal is bounded universal satisfaction of its body.
- [HP98, Theorem I.1.70(iv)] -/
lemma SatZero.ball_iff {t q e : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsDelta0 q)
    (hq' : IsUFormula ℒₒᵣ q) :
    SatZero (qqBall (termBShift ℒₒᵣ t) q) e ↔ ∀ x < termVal e t, SatZero q (x ∷ e) := sorry

/-- Satisfaction of a bounded existential is bounded existential satisfaction of its body.
- [HP98, Theorem I.1.70(iv)] -/
lemma SatZero.bex_iff {t q e : V} (ht : IsUTerm ℒₒᵣ t) :
    SatZero (qqBex (termBShift ℒₒᵣ t) q) e ↔ ∃ x < termVal e t, SatZero q (x ∷ e) := sorry

/-- Satisfaction commutes with substitution of a coded vector of terms.
- [HP98, 1.64(4)]
- [HP98, Theorem I.1.70] -/
lemma SatZero.subst {n m w p e : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (hp' : IsDelta0 p) :
    SatZero (subst ℒₒᵣ w p) e ↔ SatZero p (termValVec e n w) := sorry

end LO.FirstOrder.Arithmetic.Bootstrapping
