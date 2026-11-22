module

public import AlphaCentauri.Model.Basic
public import Foundation.FirstOrder.Arithmetic.Collection.Basic
import AlphaCentauri.OpenProblem

/-! # Models of $\mathsf{B}\Sigma_n$

A proper cut of a model of $\mathsf{I}\Sigma_j$ which is closed under the operations and
$\Sigma_j$-elementary satisfies $\mathsf{B}\Sigma_{j+1}$.

A model of $\mathsf{I}\Delta_0$ with a proper end extension to a model of $\mathsf{I}\Delta_0$
satisfies $\mathsf{B}\Sigma_1$, and a countable model of $\mathsf{B}\Sigma_1 + \mathrm{Exp}$ has
such an extension. Whether the hypothesis $\mathrm{Exp}$ can be dropped is open.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula

section

variable {M : Type*} [ORingStructure M]

namespace ClosedCut

variable {j : ℕ} [M↓[ℒₒᵣ] ⊧* 𝗜𝚺j] (I : ClosedCut M)

private lemma exists_bound_of_isElementary (hI : ∃ c, c ∉ I.carrier)
    (hj : IsElementary (ℬ[<, ℒₒᵣ].PrenexHierarchyLE j)
      I.endExtension.emb) {ψ : ArithmeticSemiformula ℕ 3}
    (hψ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 j ψ) (e : ℕ → I.carrier) (a : I.carrier)
    (h : ∀ x < a, ∃ y z, ψ.Eval ![z, x, y] e) :
    ∃ b, ∀ x < a, ∃ y < b, ∃ z, ψ.Eval ![z, x, y] e := by
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺j)
  obtain ⟨c₀, hc₀⟩ := hI
  let ι : I.carrier ⊂ₑ M := { I.endExtension with
    not_surjective h := hc₀ <| by obtain ⟨x, rfl⟩ := h c₀; exact x.2 }
  have hψ' (x y z : I.carrier) :
      ψ.Eval ![z.1, x.1, y.1] (I.endExtension.emb ∘ e) ↔ ψ.Eval ![z, x, y] e := by
    simpa [Matrix.comp_vecCons''] using hj ⟨j, le_rfl, 𝚷, hψ⟩ ![z, x, y] e
  have hlt {y c : M} (hy : y ∈ I.carrier) (hc : c ∉ I.carrier) : y < c := by
    by_contra! h₁
    exact hc <| h₁.lt_or_eq.elim (I.mem_of_lt · hy) (· ▸ hy)
  let Θ : ArithmeticSemiformula ℕ 1 :=
    ((((Rew.rewriteMap Nat.succ ▹ ψ) ⇜ ![#0, #2, #1]).bexsLT #2).bexsLT #1).ballLT &0
  let g : ℕ → M := a.1 :>ₙ (Subtype.val ∘ e)
  have hΘ (c : M) : Θ.Eval ![c] g ↔
      ∀ x < a.1, ∃ y < c, ∃ z < c, ψ.Eval ![z, x, y] fun i ↦ (e i).1 := by
    simp [Θ, g, eval_rewriteMap, Matrix.comp_vecCons'']
  have h₁ {c : M} (hc : c ∉ I.carrier) : Θ.Eval ![c] g := by
    apply (hΘ c).mpr
    intro x hx
    obtain ⟨y, z, h₂⟩ := h ⟨x, I.mem_of_lt hx a.2⟩ hx
    use y
    and_intros
    · exact hlt y.2 hc
    · use z
      and_intros
      · exact hlt z.2 hc
      · exact (hψ' _ y z).mpr h₂
  obtain ⟨b, hb, h₂⟩ : ∃ b ∈ I.carrier, Θ.Eval ![b] g := by
    by_contra! h₂
    obtain ⟨c, hc, h₃⟩ := overspill ι 𝚺 j (φ := ∼Θ)
      (by simp [Θ, hψ.hierarchy]) g fun b ↦ by simpa [ι] using h₂ b.1 b.2
    have hc' : c ∉ I.carrier := fun h ↦ hc ⟨⟨c, h⟩, rfl⟩
    obtain ⟨d, rfl⟩ := eq_succ_of_pos (hlt I.zero_mem hc')
    exact absurd (h₁ fun h ↦ hc' (I.succ_mem h)) (by simpa using h₃ d (lt_add_one d))
  use ⟨b, hb⟩
  intro x hx
  obtain ⟨y, hy, z, hz, h₃⟩ := (hΘ b).mp h₂ x.1 hx
  use ⟨y, I.mem_of_lt hy hb⟩
  and_intros
  · exact hy
  · use ⟨z, I.mem_of_lt hz hb⟩
    exact (hψ' x ⟨y, _⟩ ⟨z, _⟩).mp h₃

/-- A proper cut of a model of $\mathsf{I}\Sigma_j$ which is closed under the operations and
$\Sigma_j$-elementary satisfies $\mathsf{B}\Sigma_{j+1}$.
- [HP98, Lemma IV.1.22] -/
theorem models_BSigma_succ (hI : ∃ c, c ∉ I.carrier)
    (hj : IsElementary (ℬ[<, ℒₒᵣ].PrenexHierarchyLE j)
      I.endExtension.emb) :
    I.carrier↓[ℒₒᵣ] ⊧* 𝗕𝚺 (j + 1) := by
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := mod_ISigma_of_le (Nat.zero_le j)
  apply Semantics.ModelsSet.union_iff.mpr
  and_intros
  · exact I.endExtension.models_ISigma0
  · apply Semantics.ModelsSet.setOf_iff.mpr
    rintro _ ⟨φ, hφ, rfl⟩
    suffices ∀ (e : ℕ → I.carrier) (a : I.carrier), (∀ x < a, ∃ y, φ.Eval ![x, y] e) →
        ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] e by
      simpa [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
        Semiformula.eval_bexsLT, Semiformula.eval_substs] using this
    obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hφ
    simpa using I.exists_bound_of_isElementary hI hj hψ

end ClosedCut

end

/-! ## End extensions of models of $\mathsf{B}\Sigma_1$ -/

/-- Does every countable model of $\mathsf{B}\Sigma_1$ have a proper end extension to a model of
$\mathsf{I}\Delta_0$?
- [Kay91, Chapter 16, p. 269]
- [WP89] -/
open_problem exists_proper_endExtension_ISigma0_of_BSigma1 :=
  ∀ (M : Type) [Countable M] [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗕𝚺1],
    ∃ (N : Type) (_ : ORingStructure N) (_ : M ⊂ₑ N), N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀

end FFL.FirstOrder.Arithmetic
