module

public import AlphaCentauri.Schemata.Induction
public import Foundation.FirstOrder.Arithmetic.Collection.Equiv

/-!
# The `Δ` induction schemes from the collection scheme `𝗕𝚺(n + 1)`

A $\Delta_{n + 1}$ predicate of a model of `𝗕𝚺(n + 1)` is at once the existential quantification
of a $\Pi_n$ relation and the complement of another such, and it obeys successor induction.

- [Sla04, §2.1]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

variable {V : Type*} [ORingStructure V] {n : ℕ}

section models

variable {P : V → Prop} {Q R : V → V → Prop}

/-- Lying beyond `a` or having a witness below `b` is `𝚷-[n]`-definable. -/
private lemma definablePred_lt_or_witness_below [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (hQ : 𝚷-[n].DefinableRel Q)
    (a b : V) : 𝚷-[n].DefinablePred fun x ↦ a < x ∨ ∃ y < b, Q x y := by
  have h₁ : 𝚷-[n].Definable fun v : Fin 1 → V ↦ a < v 0 :=
    .of_iff
      (HierarchySymbol.Definable.retractiont 1
        (inferInstance : 𝚷-[n].DefinableRel (LT.lt : V → V → Prop)) ![&a, #0])
      (by intro v; simp)
  have h₂ : 𝚷-[n].Definable
      fun v : Fin 1 → V ↦ ∃ y < (&b : ArithmeticSemiterm V 1).val v id, Q (v 0) y := by
    apply HierarchySymbol.Definable.bexs
    exact .of_iff (hQ.retraction ![1, 0]) (by intro w; simp)
  exact (h₁.or h₂).of_iff (by intro v; simp)

/-- Successor induction holds for a predicate that is at once the existential quantification of a
`𝚷-[n]`-definable relation and the complement of another, in a model of `𝗕𝚺(n + 1)`.
- [Sla04, §2.1] -/
lemma succ_induction_of_complementary_exists_pi [V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1)]
    (hQ : 𝚷-[n].DefinableRel Q) (hR : 𝚷-[n].DefinableRel R) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
    (hPR : ∀ x, ¬P x ↔ ∃ w, R x w) (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n := models_ISigma_of_models_BSigma_succ
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n :=
    models_of_ss inferInstance (CollectionOnHierarchy_subset_BSigma_succ 𝚷 n)
  intro a
  by_contra ha
  have hQR : 𝚷-[n].DefinableRel fun x y ↦ Q x y ∨ R x y := .of_iff (hQ.or hR) (by intro v; simp)
  obtain ⟨b, hb⟩ := CollectionOnHierarchy.collection_of_definable (Γ := 𝚷) hQR (a + 1) <| by
    intro x _
    by_cases hx : P x
    · exact ((hPQ x).mp hx).imp fun w hw ↦ Or.inl hw
    · exact ((hPR x).mp hx).imp fun w hw ↦ Or.inr hw
  have h : ∀ x < a + 1, P x → ∃ y < b, Q x y := by
    intro x hx hPx
    obtain ⟨y, hy, hQy | hRy⟩ := hb x hx
    · exact ⟨y, hy, hQy⟩
    · exact absurd hPx ((hPR x).mpr ⟨y, hRy⟩)
  have key : ∀ x, a < x ∨ ∃ y < b, Q x y := by
    apply InductionOnHierarchy.succ_induction 𝚷 n (definablePred_lt_or_witness_below hQ a b)
    · exact Or.inr (h 0 (lt_of_le_of_lt (by simp) (lt_add_one a)) zero)
    · rintro x (hx | ⟨y, -, hy⟩)
      · exact Or.inl (lt_trans hx (lt_add_one x))
      · rcases lt_or_ge a (x + 1) with hax | hax
        · exact Or.inl hax
        · exact Or.inr <|
            h (x + 1) (lt_of_le_of_lt hax (lt_add_one a)) (succ x ((hPQ x).mpr ⟨y, hy⟩))
  obtain hy | ⟨y, -, hy⟩ := key a
  · exact absurd hy (lt_irrefl a)
  · exact ha ((hPQ a).mpr ⟨y, hy⟩)

end models

section theorems

/-- Every model of `𝗕𝚺(n + 1)` satisfies the `Δ` induction scheme for a class of formulas whose
evaluations are `𝚺-[n + 1]`-definable.
- [Sla04, §2.1] -/
private lemma models_DeltaInductionScheme_of_definablePred
    {C : ArithmeticSemiformula ℕ 1 → Prop} [V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1)]
    (hC : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → ∀ f : ℕ → V,
      𝚺-[n + 1].DefinablePred fun x : V ↦ φ.Eval ![x] f) :
    V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ DeltaInductionScheme C := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  have h₀ : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n :=
    models_of_ss inferInstance (CollectionOnHierarchy_subset_BSigma_succ 𝚷 n)
  refine Semantics.ModelsSet.union_iff.mpr ⟨h₀, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, ψ, hφ, hψ, rfl⟩
  apply (models_deltaInd_iff φ ψ).mpr
  intro f heq zero succ
  obtain ⟨Q, hQ, hQiff⟩ := exists_pi_definableRel_iff (hC hφ f)
  obtain ⟨R, hR, hRiff⟩ := exists_pi_definableRel_iff (hC hψ f)
  exact succ_induction_of_complementary_exists_pi hQ hR hQiff
    (fun x ↦ by rw [heq x, not_not]; exact hRiff x) zero succ

/-- Every model of `𝗕𝚺(n + 1)` satisfies `𝗜𝚫(n + 1)`.
- [Sla04, §2.1] -/
lemma models_IDelta_of_models_BSigma_succ (n : ℕ) (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜𝚫(n + 1) :=
  models_DeltaInductionScheme_of_definablePred fun hφ f ↦
    definablePred_of_hierarchy hφ.hierarchy f

/-- `𝗜𝚫(n + 1)` is at most as strong as `𝗕𝚺(n + 1)`.
- [Sla04, §2.1] -/
theorem IDelta_weakerThan_BSigma (n : ℕ) : 𝗜𝚫(n + 1) ⪯ 𝗕𝚺(n + 1) :=
  weakerThan_of_models.{0} _ _ fun V _ _ ↦ models_IDelta_of_models_BSigma_succ n V

/-- Every model of `𝗕𝚺(n + 1)` satisfies `𝗜𝚫⁺(n + 1)`.
- [Sla04, §2.1] -/
lemma models_IDeltaOnBroadHierarchy_of_models_BSigma_succ (n : ℕ) (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜𝚫⁺(n + 1) :=
  models_DeltaInductionScheme_of_definablePred fun hφ f ↦ definablePred_of_hierarchy hφ f

/-- `𝗜𝚫⁺(n + 1)` is at most as strong as `𝗕𝚺(n + 1)`.
- [Sla04, §2.1] -/
theorem IDeltaOnBroadHierarchy_weakerThan_BSigma (n : ℕ) : 𝗜𝚫⁺(n + 1) ⪯ 𝗕𝚺(n + 1) :=
  weakerThan_of_models.{0} _ _ fun V _ _ ↦
    models_IDeltaOnBroadHierarchy_of_models_BSigma_succ n V

end theorems

end FFL.FirstOrder.Arithmetic
