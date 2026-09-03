module

public import AlphaCentauri.Bootstrapping.Delta0
public import AlphaCentauri.Bootstrapping.TermVal

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
axiom PSatZero (q z e : V) : Prop

/-- The `𝚫₁` formula defining partial satisfaction tables.
- [HP98, Lemma I.1.72(1)] -/
axiom pSatZero : 𝚫₁.Semisentence 3

/-- The formula `pSatZero` defines partial satisfaction tables.
- [HP98, Lemma I.1.72(1)] -/
@[instance] axiom PSatZero.defined : 𝚫₁-Relation₃ (PSatZero : V → V → V → Prop) via pSatZero

/-- Partial satisfaction tables form a `𝚫₁`-definable relation.
- [HP98, Lemma I.1.72(1)] -/
instance PSatZero.definable : 𝚫₁-Relation₃ (PSatZero : V → V → V → Prop) :=
  PSatZero.defined.to_definable

/-- A partial satisfaction table for a fixed formula and assignment is unique.
- [HP98, Lemma I.1.72(2)] -/
axiom PSatZero.uniq {q₁ q₂ z e : V} (h₁ : PSatZero q₁ z e) (h₂ : PSatZero q₂ z e) :
    q₁ = q₂

/-- Every well-formed internally `Δ₀` formula has a partial satisfaction table.
- [HP98, Lemma I.1.72(3)] -/
axiom PSatZero.exists {z e : V} (hz : IsDelta0 z) (hz' : IsUFormula ℒₒᵣ z) :
    ∃ q, PSatZero q z e

/-- `SatZero z e` says that the internally coded `Δ₀` formula `z` is satisfied by `e`.
- [HP98, Definition I.1.71(2)] -/
def SatZero (z e : V) : Prop := ∃ q, PSatZero q z e ∧ ⟪⟪z, e⟫, 1⟫ ∈ q

/-- The `𝚫₁` formula defining satisfaction for internally coded `Δ₀` formulas.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
axiom satZero : 𝚫₁.Semisentence 2

/-- The formula `satZero` defines `SatZero`.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
@[instance] axiom SatZero.defined : 𝚫₁-Relation (SatZero : V → V → Prop) via satZero

/-- Satisfaction for internally coded `Δ₀` formulas is `𝚫₁`-definable.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
instance SatZero.definable : 𝚫₁-Relation (SatZero : V → V → Prop) :=
  SatZero.defined.to_definable

/-! ## Tarski conditions -/

/-- Satisfaction implies that its formula code belongs to the `Δ₀` domain.
- [HP98, Theorem I.1.70(i)] -/
axiom SatZero.dom {z e : V} : SatZero z e → IsDelta0 z ∧ IsUFormula ℒₒᵣ z

/-- The coded truth constant is satisfied.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] axiom SatZero.verum (e : V) : SatZero ^⊤ e

/-- The coded falsehood constant is not satisfied.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] axiom SatZero.falsum (e : V) : ¬SatZero ^⊥ e

/-- Satisfaction of coded equality agrees with equality of term values.
- [HP98, Theorem I.1.70(ii)] -/
axiom SatZero.eq_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^= u) e ↔ termVal e t = termVal e u

/-- Satisfaction of coded inequality agrees with inequality of term values.
- [HP98, Theorem I.1.70(ii)] -/
axiom SatZero.neq_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^≠ u) e ↔ termVal e t ≠ termVal e u

/-- Satisfaction of coded less-than agrees with comparison of term values.
- [HP98, Theorem I.1.70(ii)] -/
axiom SatZero.lt_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^< u) e ↔ termVal e t < termVal e u

/-- Satisfaction of coded negated less-than agrees with failure of comparison.
- [HP98, Theorem I.1.70(ii)] -/
axiom SatZero.nlt_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^≮ u) e ↔ ¬(termVal e t < termVal e u)

/-- Satisfaction commutes with coded conjunction.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] axiom SatZero.and_iff {p q e : V} :
    SatZero (p ^⋏ q) e ↔ SatZero p e ∧ SatZero q e

/-- Satisfaction commutes with coded disjunction.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] axiom SatZero.or_iff {p q e : V} :
    SatZero (p ^⋎ q) e ↔ SatZero p e ∨ SatZero q e

/-- Satisfaction commutes with coded negation on `Δ₀` formulas.
- [HP98, Theorem I.1.70(iii)] -/
axiom SatZero.neg_iff {p e : V} (hp : IsDelta0 p) (hp' : IsUFormula ℒₒᵣ p) :
    SatZero (neg ℒₒᵣ p) e ↔ ¬SatZero p e

/-- Satisfaction of a bounded universal is bounded universal satisfaction of its body.
- [HP98, Theorem I.1.70(iv)] -/
axiom SatZero.ball_iff {t q e : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsDelta0 q)
    (hq' : IsUFormula ℒₒᵣ q) :
    SatZero (qqBall (termBShift ℒₒᵣ t) q) e ↔ ∀ x < termVal e t, SatZero q (x ∷ e)

/-- Satisfaction of a bounded existential is bounded existential satisfaction of its body.
- [HP98, Theorem I.1.70(iv)] -/
axiom SatZero.bex_iff {t q e : V} (ht : IsUTerm ℒₒᵣ t) :
    SatZero (qqBex (termBShift ℒₒᵣ t) q) e ↔ ∃ x < termVal e t, SatZero q (x ∷ e)

/-- Satisfaction commutes with substitution of a coded vector of terms.
- [HP98, 1.64(4)]
- [HP98, Theorem I.1.70] -/
axiom SatZero.subst {n m w p e : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (hp' : IsDelta0 p) :
    SatZero (subst ℒₒᵣ w p) e ↔ SatZero p (termValVec e n w)

end LO.FirstOrder.Arithmetic.Bootstrapping
