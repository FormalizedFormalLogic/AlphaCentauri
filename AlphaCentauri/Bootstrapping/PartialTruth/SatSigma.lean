module

public import AlphaCentauri.Bootstrapping.Prenex
public import AlphaCentauri.Bootstrapping.PartialTruth.SatZero

/-!
# Satisfaction for prenex `Σₙ` and `Πₙ` formulas

This module defines satisfaction predicates for the internally coded strict prenex hierarchy.
It states their definability, Tarski conditions, duality, monotonicity, and substitution laws.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

mutual
  /-- `SatSigma n z e` says that the strict prenex `Σₙ` formula `z` is satisfied by `e`.
  A positive level peels a block of existential quantifiers and prepends its witnesses to `e`.
  - [HP98, Definition I.1.74] -/
  def SatSigma : ℕ → V → V → Prop
    | 0 => SatZero
    | n + 1 => fun z e ↦
        ∃ k q, z = qqExss q k ∧ IsStrictPi n q ∧
          ∃ w, len w = k ∧ SatPi n q (vecAppend w e)

  /-- `SatPi n z e` says that the strict prenex `Πₙ` formula `z` is satisfied by `e`.
  At a positive level it is defined by duality through coded negation.
  - [HP98, Definition I.1.74] -/
  def SatPi : ℕ → V → V → Prop
    | 0 => SatZero
    | n + 1 => fun z e ↦
        IsStrictPi (n + 1) z ∧ IsUFormula ℒₒᵣ z ∧ ¬SatSigma (n + 1) (neg ℒₒᵣ z) e
end

/-- The `𝚺ₙ₊₁` formula defining `SatSigma (n + 1)`, with arguments `(z, e)`.
- [HP98, Definition I.1.74]
- [HP98, Theorem I.1.75(1)] -/
axiom satSigma (n : ℕ) : 𝚺-[n + 1].Semisentence 2

/-- The `𝚷ₙ₊₁` formula defining `SatPi (n + 1)`, with arguments `(z, e)`.
- [HP98, Definition I.1.74]
- [HP98, Theorem I.1.75(1)] -/
axiom satPi (n : ℕ) : 𝚷-[n + 1].Semisentence 2

/-- The formula `satSigma n` defines satisfaction for strict prenex `Σₙ₊₁` formulas.
- [HP98, Theorem I.1.75(1)] -/
@[instance] axiom SatSigma.defined (n : ℕ) :
    𝚺-[n + 1]-Relation (SatSigma (n + 1) : V → V → Prop) via satSigma n

/-- The formula `satPi n` defines satisfaction for strict prenex `Πₙ₊₁` formulas.
- [HP98, Theorem I.1.75(1)] -/
@[instance] axiom SatPi.defined (n : ℕ) :
    𝚷-[n + 1]-Relation (SatPi (n + 1) : V → V → Prop) via satPi n

/-- Satisfaction for strict prenex `Σₙ₊₁` formulas is definable at level `Σₙ₊₁`.
- [HP98, Theorem I.1.75(1)] -/
instance SatSigma.definable (n : ℕ) :
    𝚺-[n + 1]-Relation (SatSigma (n + 1) : V → V → Prop) :=
  (SatSigma.defined n).to_definable

/-- Satisfaction for strict prenex `Πₙ₊₁` formulas is definable at level `Πₙ₊₁`.
- [HP98, Theorem I.1.75(1)] -/
instance SatPi.definable (n : ℕ) :
    𝚷-[n + 1]-Relation (SatPi (n + 1) : V → V → Prop) :=
  (SatPi.defined n).to_definable

/-- At level zero, strict `Σ` satisfaction is `Δ₀` satisfaction.
- [HP98, Definition I.1.74] -/
@[simp] lemma SatSigma.zero : SatSigma 0 = (SatZero : V → V → Prop) := by simp [SatSigma]

/-- At level zero, strict `Π` satisfaction is `Δ₀` satisfaction.
- [HP98, Definition I.1.74] -/
@[simp] lemma SatPi.zero : SatPi 0 = (SatZero : V → V → Prop) := by simp [SatPi]

/-! ## Tarski conditions -/

/-- Strict `Σₙ` satisfaction implies membership in its syntactic domain.
- [HP98, Theorem I.1.75(2)] -/
axiom SatSigma.dom {n : ℕ} {z e : V} :
    SatSigma n z e → IsStrictSigma n z ∧ IsUFormula ℒₒᵣ z

/-- Strict `Πₙ` satisfaction implies membership in its syntactic domain.
- [HP98, Theorem I.1.75(2)] -/
axiom SatPi.dom {n : ℕ} {z e : V} :
    SatPi n z e → IsStrictPi n z ∧ IsUFormula ℒₒᵣ z

/-- An empty existential block reads a strict `Πₙ` formula as a `Σₙ₊₁` formula.
- [HP98, Theorem I.1.75(2)(v)] -/
axiom SatSigma.of_pi {n : ℕ} {z e : V} (hz : IsStrictPi n z)
    (hz' : IsUFormula ℒₒᵣ z) : SatSigma (n + 1) z e ↔ SatPi n z e

/-- An empty universal block reads a strict `Σₙ` formula as a `Πₙ₊₁` formula.
- [HP98, Theorem I.1.75(2)(v′)] -/
axiom SatPi.of_sigma {n : ℕ} {z e : V} (hz : IsStrictSigma n z)
    (hz' : IsUFormula ℒₒᵣ z) : SatPi (n + 1) z e ↔ SatSigma n z e

/-- Satisfaction of an existential formula is existential satisfaction of its body.
- [HP98, Theorem I.1.75(2)(v)] -/
axiom SatSigma.exs_iff {n : ℕ} {p e : V} :
    SatSigma (n + 1) (^∃ p) e ↔ ∃ x, SatSigma (n + 1) p (x ∷ e)

/-- Satisfaction of a universal formula is universal satisfaction of its body.
- [HP98, Theorem I.1.75(2)(v′)] -/
axiom SatPi.all_iff {n : ℕ} {p e : V} :
    SatPi (n + 1) (^∀ p) e ↔ ∀ x, SatPi (n + 1) p (x ∷ e)

/-- Satisfaction of a strict `Σₘ` formula is stable when viewed at a higher `Σ` level.
- [HP98, Theorem I.1.75(2)(v)] -/
axiom SatSigma.mono {m n : ℕ} (h : m ≤ n) {z e : V} (hz : IsStrictSigma m z)
    (hz' : IsUFormula ℒₒᵣ z) : SatSigma m z e ↔ SatSigma n z e

/-- Satisfaction of a strict `Πₘ` formula is stable when viewed at a higher `Π` level.
- [HP98, Theorem I.1.75(2)(v′)] -/
axiom SatPi.mono {m n : ℕ} (h : m ≤ n) {z e : V} (hz : IsStrictPi m z)
    (hz' : IsUFormula ℒₒᵣ z) : SatPi m z e ↔ SatPi n z e

/-- `Πₙ` satisfaction of a negated strict `Σₙ` formula is failure of `Σₙ` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
axiom SatPi.neg_iff {n : ℕ} {z e : V} (hz : IsStrictSigma n z)
    (hz' : IsUFormula ℒₒᵣ z) : SatPi n (neg ℒₒᵣ z) e ↔ ¬SatSigma n z e

/-- `Σₙ` satisfaction of a negated strict `Πₙ` formula is failure of `Πₙ` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
axiom SatSigma.neg_iff {n : ℕ} {z e : V} (hz : IsStrictPi n z)
    (hz' : IsUFormula ℒₒᵣ z) : SatSigma n (neg ℒₒᵣ z) e ↔ ¬SatPi n z e

/-- Strict `Σₙ` satisfaction commutes with substitution of a coded vector of terms.
- [HP98, Theorem I.1.75(2)] -/
axiom SatSigma.subst {n : ℕ} {m l w p e : V} (hw : IsSemitermVec ℒₒᵣ m l w)
    (hp : IsSemiformula ℒₒᵣ m p) (hp' : IsStrictSigma n p) :
    SatSigma n (subst ℒₒᵣ w p) e ↔ SatSigma n p (termValVec e m w)

/-! ## Satisfaction under an externally supplied vector -/

/-- `satSigmaVec n k` defines `SatSigma (n + 1)` under the vector formed by its `k`
free variables. This is the formula used by the corresponding induction scheme.

- [HP98, Remark I.1.77]
- [HP98, Definition I.1.78(2)] -/
noncomputable def satSigmaVec (n k : ℕ) : 𝚺-[n + 1].Semisentence (k + 1) := .mkSigma
  “p. ∃ e, !lenDef ↑k e ∧
    (⋀ i, ∃ z, !nthDef z e ↑(i : Fin k).val ∧ z = #i.succ.succ.succ) ∧
    !(satSigma n).val p e”
  (by simp [lenDef.sigma_prop.mono (Nat.le_add_left 1 n),
    nthDef.sigma_prop.mono (Nat.le_add_left 1 n)])

/-- The formula `satSigmaVec n k` defines strict `Σₙ₊₁` satisfaction under its variables.
- [HP98, Remark I.1.77]
- [HP98, Definition I.1.78(2)] -/
axiom satSigmaVec.defined (n k : ℕ) :
    𝚺-[n + 1].Defined
      (fun v : Fin (k + 1) → V ↦ SatSigma (n + 1) (v 0) (matrixToVec (v ·.succ)))
      (satSigmaVec n k)

end LO.FirstOrder.Arithmetic.Bootstrapping
