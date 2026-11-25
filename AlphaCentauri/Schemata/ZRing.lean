module

public import AlphaCentauri.Init
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-! # The theory $\mathsf{ZR}$ of discretely ordered $\mathbb{Z}$-rings

The theory of non-negative parts of discretely ordered $\mathbb{Z}$-rings.

- [Wil78]
- [BO96, §1]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable (n : ℕ)

/-- Division with remainder by the numeral `n`. -/
def standardEuclideanDivisionBy : ArithmeticSentence :=
  “∀ b, ∃ q r, r < ↑n ∧ b = ↑n * q + r”

/-- $\mathsf{ZR}$: $\mathsf{PA}^-$ together with division with remainder by every standard
positive integer.
- [Wil78, §2]
- [BO96, §1] -/
def ZRing : ArithmeticTheory := 𝗣𝗔⁻ ∪ Set.range fun n : ℕ ↦ standardEuclideanDivisionBy (n + 1)

instance : 𝗣𝗔⁻ ⪯ ZRing := Entailment.WeakerThan.ofSubset Set.subset_union_left

instance : 𝗘𝗤 ℒₒᵣ ⪯ ZRing :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

variable {M : Type*} [ORingStructure M]

lemma models_standardEuclideanDivisionBy_iff [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] :
    M↓[ℒₒᵣ] ⊧ standardEuclideanDivisionBy n ↔ ∀ b : M, ∃ q r : M, r < n ∧ b = n * q + r := by
  simp [models_iff, standardEuclideanDivisionBy, numeral_eq_natCast]

namespace ZRing

variable [M↓[ℒₒᵣ] ⊧* ZRing]

instance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := ZRing) inferInstance

end ZRing

/-- $\mathsf{IOpen}$ proves $\mathsf{ZR}$.
- [Smi92b, Lemma 3.6, Corollary 3.7] -/
instance ZRing_weakerThan_IOpen : ZRing ⪯ 𝗜𝗢𝗽𝗲𝗻 :=
  weakerThan_of_models.{0} _ _ fun V _ _ ↦ models_theory_iff.mpr <| by
    rintro σ (hσ | ⟨n, rfl⟩)
    · exact models_of_mem hσ
    apply (models_standardEuclideanDivisionBy_iff (n + 1)).mpr
    intro b
    obtain ⟨r, hr, e⟩ := eq_mul_div_add_of_pos b (b := ((n + 1 : ℕ) : V)) (by simp)
    use b / ((n + 1 : ℕ) : V), r


end FFL.FirstOrder.Arithmetic
