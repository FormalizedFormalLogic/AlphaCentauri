module

public import AlphaCentauri.Model.Cut
public import AlphaCentauri.Model.Overspill
public import AlphaCentauri.ToFoundation.Hierarchy
public import Foundation.FirstOrder.Arithmetic.Collection.Basic

/-!
# Elementary substructures

An embedding of `ℒₒᵣ`-structures is $\Sigma_s$-elementary when prenex $\Sigma_m$ and $\Pi_m$
formulas, for `m ≤ s`, take the same truth value at elements of the substructure as at their images.
The Tarski–Vaught test reduces this to the absoluteness of bounded formulas and to finding witnesses
in the substructure. A proper cut $\Sigma_j$-elementary in a model of $\mathsf{I}\Sigma_j$ satisfies
$\mathsf{B}\Sigma_{j+1}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula

universe u v

variable {S : Type u} {M : Type v} [ORingStructure S] [ORingStructure M]

/-- `ι` is $\Sigma_s$-elementary: for `m ≤ s`, prenex $\Sigma_m$ and $\Pi_m$ formulas take the same
truth value at elements of `S` as at their images.
- [HP98, Definition IV.1.17] -/
def SigmaElementary (ι : S ↪ₛ[ℒₒᵣ] M) (s : ℕ) : Prop :=
  ∀ {Γ : Polarity} {m n : ℕ} {φ : ArithmeticSemiformula ℕ n}, m ≤ s →
    ℬ[<, ℒₒᵣ].PrenexHierarchy Γ m φ → ∀ (e : Fin n → S) (f : ℕ → S),
      φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f

variable (ι : S ↪ₛ[ℒₒᵣ] M)

/-- The Tarski–Vaught test: bounded formulas are absolute along `ι`, and every prenex $\Pi_m$
formula, `m < s`, with parameters from `S` and a witness in `M` has a witness in `S`.
- [HP98, Lemma IV.1.19] -/
theorem sigmaElementary_of_tarskiVaught (s : ℕ)
    (bounded : ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ n}, ℬ[<, ℒₒᵣ].Closure φ →
      ∀ (e : Fin n → S) (f : ℕ → S), φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f)
    (witness : ∀ m < s, ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ (n + 1)},
      ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 m φ → ∀ (e : Fin n → S) (f : ℕ → S),
        (∃ x : M, φ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : S, φ.Eval (ι x :> ι ∘ e) (ι ∘ f)) :
    SigmaElementary ι s := by
  intro Γ m n φ hm hφ
  induction m generalizing Γ n φ with
  | zero => exact bounded (Bounding.PrenexHierarchy.zero_iff_bounded.mp hφ)
  | succ m ih =>
    intro e f
    rcases Γ
    · obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hφ
      simp only [eval_ex]
      constructor
      · intro h
        obtain ⟨x, hx⟩ := witness m (by omega) hψ e f h
        use x
        rw [← Matrix.comp_vecCons''] at hx
        exact (ih (by omega) hψ (x :> e) f).mp hx
      · rintro ⟨x, hx⟩
        use ι x
        rw [← Matrix.comp_vecCons'']
        exact (ih (by omega) hψ (x :> e) f).mpr hx
    · obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.pi_succ_iff.mp hφ
      simp only [eval_all]
      constructor
      · intro h x
        have h₁ := h (ι x)
        rw [← Matrix.comp_vecCons''] at h₁
        exact (ih (by omega) hψ (x :> e) f).mp h₁
      · intro h
        by_contra! h₁
        obtain ⟨x, hx⟩ := witness m (by omega) hψ.neg e f (by simpa using h₁)
        rw [← Matrix.comp_vecCons''] at hx
        exact absurd (h x) (by simpa using (ih (by omega) hψ.neg (x :> e) f).mp hx)

/-- Bounded formulas are absolute along `ι` as soon as every bounded formula with parameters from
`S` and a witness in `M` has a witness in `S`. -/
axiom eval_iff_of_bounded_of_witness
    (witness : ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ (n + 1)}, ℬ[<, ℒₒᵣ].Closure φ →
      ∀ (e : Fin n → S) (f : ℕ → S),
        (∃ x : M, φ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : S, φ.Eval (ι x :> ι ∘ e) (ι ∘ f))
    {n : ℕ} {φ : ArithmeticSemiformula ℕ n} (hφ : ℬ[<, ℒₒᵣ].Closure φ)
    (e : Fin n → S) (f : ℕ → S) : φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f

/-- A $\Sigma_0$-elementary substructure of a model of `𝗣𝗔⁻` is a model of `𝗣𝗔⁻`.
- [HP98, Remark IV.1.21(2)] -/
axiom SigmaElementary.models_peanoMinus {ι : S ↪ₛ[ℒₒᵣ] M} (hι : SigmaElementary ι 0)
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] : S↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻

/-- A proper cut of a model of $\mathsf{I}\Sigma_j$ which is closed under the operations and
$\Sigma_j$-elementary satisfies $\mathsf{B}\Sigma_{j+1}$.
- [HP98, Lemma IV.1.22] -/
axiom Cut.models_BSigma_succ {j : ℕ} [M↓[ℒₒᵣ] ⊧* 𝗜𝚺j] (I : Cut M) [I.Closed]
    (hI : ∃ c, c ∉ I.carrier) (hj : SigmaElementary I.endExtension.emb j) :
    I.carrier↓[ℒₒᵣ] ⊧* 𝗕𝚺 (j + 1)

end FFL.FirstOrder.Arithmetic
