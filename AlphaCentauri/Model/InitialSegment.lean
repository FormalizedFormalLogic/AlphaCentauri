module

public import AlphaCentauri.Model.Basic

/-! # Initial segments of models of arithmetic

A nonstandard model of `𝗜𝚺₁` has the same standard system as any end extension of it which again
models `𝗜𝚺₁`. If moreover `M` embeds onto a $\Sigma_n$-elementary initial segment of `N`, a
$\Pi_n$ formula satisfiable in `M` with a parameter `c` is satisfiable in `N`, with the image of `c`
as parameter, below any element outside the initial segment.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {M N : Type*} [ORingStructure M] [ORingStructure N]

section

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

/-- A nonstandard model of `𝗜𝚺₁` embedded onto an initial segment of a model of `𝗜𝚺₁` has the same
standard system as that model.
- [Kay91, Theorem 12.3] -/
theorem standardSystem_eq_of_initialSegmentEmbedding (hM : ∃ d : M, ∀ m : ℕ, (m : M) < d)
    {ι : M ↪ₛ[ℒₒᵣ] N} (hι : ∀ x y, y < ι x → y ∈ Set.range ι) :
    standardSystem M = standardSystem N :=
  standardSystem_eq_of_endExtension (.ofInitial ι hι) hM

end

/-- If `M` embeds onto a $\Sigma_n$-elementary initial segment of a model `N` of `𝗣𝗔⁻`, a
$\Pi_n$ formula satisfiable in `M` with the parameter `c` is satisfiable in `N`, with the image of
`c` as parameter, below any element outside the image.
- [Kay91, Theorem 12.3] -/
theorem exists_lt_of_initialSegmentEmbedding [N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {n : ℕ} {ι : M ↪ₛ[ℒₒᵣ] N}
    (hι : ∀ x y, y < ι x → y ∈ Set.range ι)
    (hel : IsElementary (fun {_} φ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n φ) ι) {b : N}
    (hb : b ∉ Set.range ι) {c : M} {θ : ArithmeticSemisentence 2}
    (hθ : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 n θ) (h : ∃ x : M, M ⊧/![x, c] θ) : ∃ x < b, N ⊧/![x, ι c] θ := by
  obtain ⟨x, hx⟩ := h
  use ι x
  and_intros
  · rcases lt_trichotomy (ι x) b with h | rfl | h
    · exact h
    · exact (hb (Set.mem_range_self x)).elim
    · exact (hb (hι x b h)).elim
  · have h₁ := hel (φ := Rewriting.emb (∼θ)) (hθ.neg.rew Rew.emb) ![x, c] (fun _ ↦ c)
    simpa [Matrix.comp_vecCons''] using h₁.not.mpr (by simpa using hx)

end FFL.FirstOrder.Arithmetic
