module

public import AlphaCentauri.Model.EndExtension
public import AlphaCentauri.ToFoundation.FirstOrder.Bounded
public import Foundation.FirstOrder.Arithmetic.Schemata

/-! # Absolute formulas along end extensions -/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula Tarski.Structure

universe u v

variable {ξ : Type*}

section Absolute

/-- `φ` is absolute for `T` when it takes the same truth value in every model of `T` as in every
end extension of that model which again models `T`. -/
def Absolute (T : ArithmeticTheory) {n : ℕ} (φ : ArithmeticSemiformula ξ n) : Prop :=
  ∀ (M : Type u) (N : Type v) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [hMN : M ⊆ₑ N] [N↓[ℒₒᵣ] ⊧* T]
    (e : Fin n → M) (f : ξ → M), φ.Eval e f ↔ φ.Eval (hMN.emb ∘ e) (hMN.emb ∘ f)

lemma absolute_of_open (T : ArithmeticTheory) {n} {φ : ArithmeticSemiformula ξ n} (hφ : φ.Open) :
    Absolute T φ := by
  intro M N _ _ hMN _ e f
  exact eval_hom_iff_of_open hMN.emb hφ

-- The universes of the models are parameters of `Absolute`, so the closure lemmas below pin
-- them explicitly: without the annotation each occurrence is generalized on its own.

variable {T : ArithmeticTheory} {n : ℕ}
  {φ ψ : ArithmeticSemiformula ξ n}
  {θ : ArithmeticSemiformula ξ (n + 1)} {t : ArithmeticSemiterm ξ n}

lemma and_absolute (hφ : Absolute.{u, v, _} T φ) (hψ : Absolute.{u, v, _} T ψ) :
    Absolute.{u, v, _} T (φ ⋏ ψ) := by
  intro M N _ _ hMN _ e f;
  simp [hφ M N e f, hψ M N e f]

lemma or_absolute (hφ : Absolute.{u, v, _} T φ) (hψ : Absolute.{u, v, _} T ψ) :
    Absolute.{u, v, _} T (φ ⋎ ψ) := by
  intro M N _ _ hMN _ e f;
  simp [hφ M N e f, hψ M N e f]

lemma ballLT_absolute (hθ : Absolute.{u, v, _} T θ) : Absolute.{u, v, _} T (θ.ballLT t) := by
  intro M N _ _ hMN _ e f
  simp only [eval_ballLT, ← HomClass.val_term hMN.emb e f t]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt hy
    rw [← Matrix.comp_vecCons'']
    exact (hθ M N (x :> e) f).mp (h x (by simpa using hy))
  · intro h x hx
    have h₁ := h (hMN.emb x) (by simpa using hx)
    rw [← Matrix.comp_vecCons''] at h₁
    exact (hθ M N (x :> e) f).mpr h₁

lemma bexsLT_absolute (hθ : Absolute.{u, v, _} T θ) : Absolute.{u, v, _} T (θ.bexsLT t) := by
  intro M N _ _ hMN _ e f
  simp only [eval_bexsLT, ← HomClass.val_term hMN.emb e f t]
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨hMN.emb x, by simpa using hx, ?_⟩
    rw [← Matrix.comp_vecCons'']
    exact (hθ M N (x :> e) f).mp h
  · rintro ⟨y, hy, h⟩
    obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt hy
    rw [← Matrix.comp_vecCons''] at h
    exact ⟨x, by simpa using hy, (hθ M N (x :> e) f).mpr h⟩

/-- Bounded formulas take the same truth value along an end extension.
- [HP98, Fact IV.1.3(4), Remark IV.1.18]
- [vO99, Exercise 37] -/
@[simp, grind .]
theorem absolute_of_bounded (hφ : ℬ[<, ℒₒᵣ].Closure φ) : Absolute T φ :=
  bounded_induction_open (P := fun _ φ ↦ Absolute T φ)
    (fun _ _ hφ ↦ absolute_of_open T hφ)
    (fun _ _ _ _ _ ihφ ihψ ↦ and_absolute ihφ ihψ)
    (fun _ _ _ _ _ ihφ ihψ ↦ or_absolute ihφ ihψ)
    (fun _ _ _ _ ih ↦ ballLT_absolute ih)
    (fun _ _ _ _ ih ↦ bexsLT_absolute ih)
    n φ hφ

end Absolute

variable {M : Type u} [ORingStructure M]

namespace EndExtension

variable {N : Type v} [hMN : M ⊆ₑ N]

private lemma eval_of_endExtension [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {φ : ArithmeticSemiformula ℕ 1}
    (hφ : ℬ[<, ℒₒᵣ].Closure φ)
    (v : ℕ → M) (h0 : φ.Eval ![0] v) (hs : ∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) (a : M) :
    φ.Eval ![a] v := by
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := hMN.models_peanoMinus
  have h₁ : ∀ x : M, φ.Eval ![x] v ↔ φ.Eval ![hMN.emb x] (hMN.emb ∘ v) := by
    intro x;
    simpa [Matrix.comp_vecCons'', Matrix.empty_eq] using
      absolute_of_bounded (T := 𝗣𝗔⁻) hφ M N ![x] v
  have h₂ : ∀ y : N, y < hMN.emb a + 1 → φ.Eval ![y] (hMN.emb ∘ v) := by
    refine InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0)
      ⟨(hMN.emb a + 1) :>ₙ fun j ↦ hMN.emb (v j),
        “#0 < &0” 🡒 (Rew.rewriteMap Nat.succ ▹ φ), by simp [hφ.hierarchy],
        by intro x; simp [Semiformula.eval_rewriteMap, Function.comp_def]⟩
      (by intro _; simpa using (h₁ 0).mp h0) ?_
    intro y ih hy
    have h₃ : y < hMN.emb a := lt_of_lt_of_le (lt_add_one y) (lt_succ_iff_le.mp hy)
    obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt h₃
    simpa using (h₁ (x + 1)).mp (hs x ((h₁ x).mpr (ih (lt_trans h₃ (lt_add_one _)))))
  exact (h₁ a).mpr (h₂ (hMN.emb a) (by simp))

/-- A structure with an end extension modelling `𝗜𝚺₀` is itself a model of `𝗜𝚺₀`.
- [HP98, Remark IV.1.21(2)] -/
theorem models_ISigma0 [hN : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
  simp only [Semantics.ModelsSet.union_iff, InductionScheme];
  and_intros;
  · exact hMN.models_peanoMinus
  · apply Semantics.ModelsSet.setOf_iff.mpr;
    rintro _ ⟨φ, hφ, rfl⟩
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs]
      using hMN.eval_of_endExtension
        (Bounding.PrenexHierarchy.zero_iff_bounded.mp hφ)

end EndExtension

end FFL.FirstOrder.Arithmetic
