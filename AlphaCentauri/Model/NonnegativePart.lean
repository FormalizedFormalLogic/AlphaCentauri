module

public import AlphaCentauri.ToMathlib.OpenPredicate
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Mathlib.Algebra.Order.Nonneg.Ring

/-!
# The non-negative part of a discretely ordered ring

The non-negative elements `Nonneg R` of an ordered commutative ring `R` form an
`ℒₒᵣ`-structure, which is a model of $\mathsf{PA}^-$ when `R` is discretely ordered.
-/

@[expose] public section

open FFL FirstOrder OpenPredicate

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The non-negative part of a discretely ordered ring is a model of $\mathsf{PA}^-$.
- [Kay91, §2.1] -/
instance [DiscretelyOrdered R] : (Nonneg R)↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_theory_iff.mpr fun {σ} h ↦ by
  rcases h
  case equal h => exact models_theory_iff.mp inferInstance _ h
  case addEqOfLt =>
    suffices ∀ x y : Nonneg R, x < y → ∃ z < y + 1, x + z = y by
      simpa [models_iff, Semiformula.eval_bexsLTSucc] using this
    intro x y h
    obtain ⟨z, rfl⟩ := exists_add_of_le h.le
    use z
    exact ⟨le_add_self.trans_lt (lt_add_one _), rfl⟩
  case oneLeOfZeroLt =>
    suffices ∀ x : Nonneg R, 0 < x → 1 ≤ x by simpa [models_iff] using this
    intro x h
    exact DiscretelyOrdered.one_le_of_pos (x : R) h
  case addAssoc => simpa [models_iff] using fun x y z : Nonneg R ↦ add_assoc x y z
  case addComm => simpa [models_iff] using fun x y : Nonneg R ↦ add_comm x y
  case mulAssoc => simpa [models_iff] using fun x y z : Nonneg R ↦ mul_assoc x y z
  case mulComm => simpa [models_iff] using fun x y : Nonneg R ↦ mul_comm x y
  case mulLtMul =>
    simpa [models_iff] using fun (x y z : Nonneg R) (h : x < y) (hz : 0 < z) ↦
      mul_lt_mul_of_pos_right h hz
  case distr => simpa [models_iff] using fun x y z : Nonneg R ↦ mul_add x y z
  case ltTrans =>
    simpa [models_iff] using fun (x y z : Nonneg R) (h : x < y) ↦ h.trans (c := z)
  case ltTri => simpa [models_iff] using fun x y : Nonneg R ↦ lt_trichotomy x y
  all_goals simp [models_iff]
