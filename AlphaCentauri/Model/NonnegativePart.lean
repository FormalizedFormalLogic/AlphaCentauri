module

public import AlphaCentauri.Schemata.ZRing
public import AlphaCentauri.ToFoundation.OpenPredicate
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Algebra.Order.Nonneg.Ring

/-!
# The non-negative part of a discretely ordered ring

The non-negative elements `Nonneg R` of an ordered commutative ring `R` form an
`ℒₒᵣ`-structure, which is a model of $\mathsf{PA}^-$ when `R` is discretely ordered, and a model of
$\mathsf{IOpen}$ exactly when `R` satisfies open induction.
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

namespace Nonneg

/-- The inclusion of the non-negative part, as an embedding of `ℒₒᵣ`-structures. -/
def oRingEmbedding : Nonneg R ↪ₛ[ℒₒᵣ] R where
  toFun := Subtype.val
  func' f v := by cases f <;> rfl
  rel' r _ := by cases r; exacts [congrArg Subtype.val, id]
  toFun_inj := Subtype.val_injective
  rel_inv' r _ := by cases r; exacts [Subtype.ext, id]

@[simp] lemma coe_oRingEmbedding : ⇑(oRingEmbedding : Nonneg R ↪ₛ[ℒₒᵣ] R) = Subtype.val := rfl

/-- The non-negative part of a discretely ordered ring is a model of $\mathsf{IOpen}$ if and only
if the ring satisfies open induction.
- [BO96, §1]
- [GG17, §2.3] -/
theorem models_IOpen_iff [DiscretelyOrdered R] :
    (Nonneg R)↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 ↔ OpenInduction R := by
  constructor
  · intro _ P hP h0 hs x hx
    obtain ⟨θ, hθ, h⟩ := exists_open_eval_iff (M := Nonneg R) (ι := Subtype.val)
      (fun x ↦ ⟨toNonneg x, toNonneg (-x), by simp⟩) hP
    have hθP (y : Nonneg R) : P ![(y : R)] ↔ θ.Eval ![y] id := by
      simpa [← h, Matrix.constant_eq_singleton] using
        (Semiformula.eval_hom_iff_of_open oRingEmbedding hθ (e₁ := ![y]) (ε₁ := id)).symm
    exact Arithmetic.succ_induction (P := fun y : Nonneg R ↦ P ![(y : R)]) ⟨θ, hθ, hθP⟩ h0
      (fun y ↦ hs y y.2) ⟨x, hx⟩
  · intro h
    apply Semantics.ModelsSet.union_iff.mpr
    and_intros
    · infer_instance
    apply Semantics.modelsSet_iff.mpr
    rintro _ ⟨φ, hφ, rfl⟩
    suffices ∀ f : ℕ → Nonneg R, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
        ∀ x, φ.Eval ![x] f by
      simpa [models_iff, Semiformula.eval_univCl, Arithmetic.succInd, Semiformula.eval_substs,
        Matrix.constant_eq_singleton] using this
    intro f h0 hs x
    have hφP (y : Nonneg R) : φ.Eval ![y] f ↔ φ.Eval ![(y : R)] fun i ↦ (f i : R) := by
      simpa [Matrix.constant_eq_singleton, Function.comp_def] using
        Semiformula.eval_hom_iff_of_open oRingEmbedding hφ (e₁ := ![y]) (ε₁ := f)
    simp only [hφP] at h0 hs ⊢
    exact h _ (isOpen_eval _ hφ) h0 (fun r hr ↦ hs ⟨r, hr⟩) x x.2

/-- The natural number cast of the semiring structure that the $\mathsf{PA}^-$ model structure on
`Nonneg R` induces agrees with the cast of `Nonneg R` itself. -/
lemma natCast_foundation [DiscretelyOrdered R] (m : ℕ) :
    @Nat.cast (Nonneg R) Arithmetic.instCommSemiring_foundation.toNatCast m = (m : Nonneg R) := by
  induction m with
  | zero => rw [@Nat.cast_zero _ Arithmetic.instCommSemiring_foundation.toAddMonoidWithOne,
      Nat.cast_zero]
  | succ m ih => rw [@Nat.cast_succ _ Arithmetic.instCommSemiring_foundation.toAddMonoidWithOne,
      Nat.cast_succ, ih]

/-- The numerals of the $\mathsf{PA}^-$ model structure on `Nonneg R` are those of `Nonneg R`. -/
lemma ofNat_foundation [DiscretelyOrdered R] (n : ℕ) [n.AtLeastTwo] :
    (@OfNat.ofNat (Nonneg R) n (@instOfNatAtLeastTwo _ n
      Arithmetic.instCommSemiring_foundation.toNatCast _) : Nonneg R) = OfNat.ofNat n :=
  (natCast_foundation n).trans Nat.cast_ofNat

/-- The numerals of the $\mathsf{PA}^-$ model structure on `Nonneg R` are those of `R`. -/
lemma coe_ofNat_foundation [DiscretelyOrdered R] (n : ℕ) [n.AtLeastTwo] :
    ((@OfNat.ofNat (Nonneg R) n (@instOfNatAtLeastTwo _ n
      Arithmetic.instCommSemiring_foundation.toNatCast _) : Nonneg R) : R) = OfNat.ofNat n :=
  congrArg Subtype.val (ofNat_foundation n)

/-- The non-negative part of a discretely ordered ring in which every element can be divided with
remainder by every positive natural number is a model of $\mathsf{ZR}$.
- [Wil78, §2]
- [BO96, §1] -/
theorem models_ZRing [DiscretelyOrdered R]
    (h : ∀ (a : R) {n : ℕ}, 0 < n → ∃ q r : R, 0 ≤ r ∧ r < n ∧ a = n * q + r) :
    (Nonneg R)↓[ℒₒᵣ] ⊧* Arithmetic.ZRing := by
  apply models_theory_iff.mpr
  rintro σ (hσ | ⟨n, rfl⟩)
  · exact models_of_mem hσ
  · apply (Arithmetic.models_standardEuclideanDivisionBy_iff (n + 1)).mpr
    intro b
    obtain ⟨q, r, hr₀, hr, e⟩ := h (b : R) n.succ_pos
    have hq : 0 ≤ q := by
      by_contra hq
      have := DiscretelyOrdered.one_le_of_pos (-q) (neg_pos.mpr (not_le.mp hq))
      nlinarith [b.2]
    have h₁ : (⟨r, hr₀⟩ : Nonneg R) < ((n + 1 : ℕ) : Nonneg R) := by exact_mod_cast hr
    have h₂ : b = ((n + 1 : ℕ) : Nonneg R) * ⟨q, hq⟩ + ⟨r, hr₀⟩ := by
      apply Subtype.ext
      simpa using e
    use ⟨q, hq⟩, ⟨r, hr₀⟩
    rw [natCast_foundation]
    exact ⟨h₁, h₂⟩

end Nonneg
