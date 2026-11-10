module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Trace.Basic
import Mathlib.GroupTheory.Sylow

/-!
# Finite field extensions

Quadratic extensions and intermediate fields of Galois extensions of prime-power degree.
-/

@[expose] public section

open Module

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

lemma Algebra.IsQuadraticExtension.mem_range_of_sq_eq [Algebra.IsQuadraticExtension K M] {β : M}
    {r : K} (hr : r ^ 2 = -Algebra.norm K β + Algebra.trace K M β * r) :
    β ∈ Set.range (algebraMap K M) := by
  have h₁ := IsQuadraticExtension.sq_eq_trace_smul_sub_norm K β
  have h₂ := congrArg (algebraMap K M) hr
  rw [Algebra.smul_def] at h₁
  simp only [map_pow, map_add, map_neg, map_mul] at h₂
  have : (β - algebraMap K M r) * (β - algebraMap K M (Algebra.trace K M β - r)) = 0 := by
    rw [map_sub]
    linear_combination h₁ - h₂
  rcases mul_eq_zero.mp this with h | h
  · exact ⟨r, (sub_eq_zero.mp h).symm⟩
  · exact ⟨_, (sub_eq_zero.mp h).symm⟩

lemma Module.exists_notMem_range_of_finrank_ne_one (h : finrank K M ≠ 1) :
    ∃ β : M, β ∉ Set.range (algebraMap K M) := by
  by_contra! hall
  refine h (Subalgebra.bot_eq_top_iff_finrank_eq_one.mp ?_)
  ext y
  simpa [Algebra.mem_bot] using hall y

/-- A field of characteristic other than two in which every element is a square has no quadratic
extension. -/
lemma Module.finrank_ne_two_of_forall_isSquare [NeZero (2 : K)] (h : ∀ x : K, IsSquare x) :
    finrank K M ≠ 2 := by
  intro h₂
  have : Algebra.IsQuadraticExtension K M := ⟨h₂⟩
  have : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨β, hβ⟩ := exists_notMem_range_of_finrank_ne_one (K := K) (M := M) (by omega)
  obtain ⟨r, hr⟩ := QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr.mpr (h _)
  exact hβ <| Algebra.IsQuadraticExtension.mem_range_of_sq_eq hr

lemma IsGalois.exists_intermediateField_finrank_eq_prime [FiniteDimensional K M] [IsGalois K M]
    {p k : ℕ} [Fact p.Prime] (h : finrank K M = p ^ (k + 1)) :
    ∃ E : IntermediateField K M, finrank K E = p ∧ finrank E M = p ^ k := by
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := Gal(M/K)) p (n := k)
    (by rw [IsGalois.card_aut_eq_finrank, h]; exact pow_dvd_pow p k.le_succ)
  have h₁ : finrank (IntermediateField.fixedField H) M = p ^ k := by
    rw [IntermediateField.finrank_fixedField_eq_card, hH]
  have h₂ := Module.finrank_mul_finrank K (IntermediateField.fixedField H) M
  rw [h₁, h, pow_succ, mul_comm] at h₂
  exact ⟨_, Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos k) h₂, h₁⟩
