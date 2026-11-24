module

public import AlphaCentauri.Model.Basic

/-! # Initial segments of models of arithmetic

A nonstandard model of `𝗜𝚺₁` has the same standard system as any end extension of it which again
models `𝗜𝚺₁`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {M N : Type*} [ORingStructure M] [ORingStructure N] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A nonstandard model of `𝗜𝚺₁` and an end extension of it which again models `𝗜𝚺₁` have the same
standard system.
- [Kay91, Chapter 12, p. 159] -/
theorem standardSystem_eq_of_endExtension (e : M ⊆ₑ N) (hM : ∃ c : M, ∀ m : ℕ, (m : M) < c) :
    standardSystem M = standardSystem N := by
  apply (standardSystem_subset_of_endExtension e).antisymm
  rintro _ ⟨a, rfl⟩
  obtain ⟨c, hc⟩ := hM
  have h₁ : ∀ m : ℕ, (m : N) < e c := by
    intro m
    simpa using e.emb_lt_emb.mpr (hc m)
  have h₂ : 0 < e c := by simpa using h₁ 0
  obtain ⟨s, hs, h₃⟩ := finset_comprehension₁ (Γ := 𝚺) (P := (· ∈ a)) (by definability) (log (e c))
  obtain ⟨x, rfl⟩ := e.mem_range_of_lt (hs.trans_le (exp_log_le_self h₂))
  use x
  ext n
  rw [← e.codedSet_emb]
  apply h₃
  have h₄ : ((n + 1 : ℕ) : N) ≤ log (e c) :=
    (exp_le_iff_le_log h₂).mp (nat_cast_exp (V := N) (n + 1) ▸ (h₁ _).le)
  exact (Nat.cast_lt.mpr n.lt_succ_self).trans_le h₄

end FFL.FirstOrder.Arithmetic
