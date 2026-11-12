module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# The theory $\mathsf{PA}^-_{\mathrm{smu}}$

$\mathsf{PA}^-_{\mathrm{smu}}$ is $\mathsf{PA}^-$ together with two principles on powers of two,
where `x` is a power of two when each of its divisors is `1` or even: the Powers Existence
Principle, that each `x` has a power of two `u` with `u ≤ x + 1 < 2 * u`, and the Powers Division
Principle, that of two powers of two the smaller divides the larger.

- [Vis26, §3.1]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- `x` is a power of two: each divisor of `x` is `1` or even.
- [Vis26, §3.1] -/
def isPowerOfTwo : ArithmeticSemisentence 1 :=
  “x. ∀ y, (∃ z, z * y = x) → y = 1 ∨ ∃ w, w * 2 = y”

/-- The Powers Existence Principle.
- [Vis26, §3.1] -/
def powersExistence : ArithmeticSentence :=
  “∀ x, ∃ u, !isPowerOfTwo u ∧ u ≤ x + 1 ∧ x + 1 < 2 * u”

/-- The Powers Division Principle.
- [Vis26, §3.1] -/
def powersDivision : ArithmeticSentence :=
  “∀ x y, !isPowerOfTwo x ∧ !isPowerOfTwo y ∧ x ≤ y → ∃ z, z * x = y”

/-- $\mathsf{PA}^-_{\mathrm{smu}}$: $\mathsf{PA}^-$ together with the Powers Existence Principle and
the Powers Division Principle.
- [Vis26, §3.1] -/
def PeanoMinusSmu : ArithmeticTheory := 𝗣𝗔⁻ ∪ {powersExistence, powersDivision}

instance : 𝗣𝗔⁻ ⪯ PeanoMinusSmu := Entailment.WeakerThan.ofSubset Set.subset_union_left

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

@[simp] lemma eval_isPowerOfTwo {e : Fin 1 → M} {f : Empty → M} :
    Semiformula.Eval e f isPowerOfTwo ↔ ∀ y : M, (∃ z, z * y = e 0) → y = 1 ∨ ∃ w, w * 2 = y := by
  simp [isPowerOfTwo]

lemma models_powersExistence_iff :
    M↓[ℒₒᵣ] ⊧ powersExistence ↔ ∀ x : M, ∃ u : M,
      (∀ y : M, (∃ z, z * y = u) → y = 1 ∨ ∃ w, w * 2 = y) ∧ u ≤ x + 1 ∧ x + 1 < 2 * u := by
  simp [models_iff, powersExistence, Semiformula.eval_substs]

lemma models_powersDivision_iff :
    M↓[ℒₒᵣ] ⊧ powersDivision ↔ ∀ x y : M,
      (∀ v : M, (∃ z, z * v = x) → v = 1 ∨ ∃ w, w * 2 = v) →
      (∀ v : M, (∃ z, z * v = y) → v = 1 ∨ ∃ w, w * 2 = v) → x ≤ y → ∃ z, z * x = y := by
  simp [models_iff, powersDivision, Semiformula.eval_substs]

lemma models_PeanoMinusSmu_iff :
    M↓[ℒₒᵣ] ⊧* PeanoMinusSmu ↔
      M↓[ℒₒᵣ] ⊧ powersExistence ∧ M↓[ℒₒᵣ] ⊧ powersDivision := by
  simp [PeanoMinusSmu, (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻)]

end FFL.FirstOrder.Arithmetic
