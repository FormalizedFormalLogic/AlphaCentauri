module

public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import AlphaCentauri.Schemata.Induction

/-!
# Parameter-free induction `𝗜ᶠ` over the prenex hierarchy

`𝗜ᶠ Γ s` is `𝗘𝗔` together with successor induction for the
`ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s` formulas `φ(x)`
that carry no free variable besides the induction variable `x`.

- [Bek99, §1]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

section axioms

variable {L : Language} [L.ORing] {C C' : Semisentence L 1 → Prop}

variable (L) in
/-- The parameter-free induction instance for a formula `φ` of one free variable:
`φ(0) → (∀ x, φ(x) → φ(x + 1)) → ∀ x, φ(x)`.
- [Bek99, §1] -/
def parameterFreeSuccInd (φ : Semisentence L 1) : Sentence L := .univCl (succInd (Rew.emb ▹ φ))

variable (L) in
/-- The parameter-free induction schema restricted to the formulas satisfying `C`:
`{ φ(0) → (∀ x, φ(x) → φ(x + 1)) → ∀ x, φ(x) | C φ }`.
- [Bek99, §1] -/
def parameterFreeInductionOn (C : Semisentence L 1 → Prop) : Set (Sentence L) :=
  parameterFreeSuccInd L '' {φ | C φ}

/-- `𝗜ᶠ Γ s` is `𝗘𝗔` together with the parameter-free induction schema for
`ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s`.
- [Bek99, §1] -/
abbrev IParameterFree (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝗘𝗔 ∪ parameterFreeInductionOn ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s)

prefix:max "𝗜ᶠ " => IParameterFree

lemma parameterFreeInductionOn_subset (h : ∀ {φ : Semisentence L 1}, C φ → C' φ) :
    parameterFreeInductionOn L C ⊆ parameterFreeInductionOn L C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma parameterFreeInductionOn_subset_InductionScheme (Γ : Polarity) (s : ℕ) :
    parameterFreeInductionOn ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s) ⊆
      InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s) := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact ⟨Rew.emb ▹ φ, Bounding.PrenexHierarchy.rew_iff.mpr hφ, rfl⟩

instance IParameterFree_weakerThan_EA_union_InductionScheme (Γ : Polarity) (s : ℕ) :
    𝗜ᶠ Γ s ⪯ 𝗘𝗔 ∪ InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s) :=
  WeakerThan.ofSubset
    (Set.union_subset_union_right _ (parameterFreeInductionOn_subset_InductionScheme Γ s))

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗔 ⪯ 𝗜ᶠ Γ s := WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (s : ℕ) : 𝗣𝗔⁻ ⪯ 𝗜ᶠ Γ s :=
  WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ 𝗘𝗔) inferInstance

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜ᶠ Γ s :=
  WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗘𝗔) inferInstance

section monotonicity

variable {V : Type*} [ORingStructure V]

lemma parameterFreeInductionOn.models_of_exists_eval_iff {C C' : ArithmeticSemisentence 1 → Prop}
    [V↓[ℒₒᵣ] ⊧* parameterFreeInductionOn ℒₒᵣ C']
    (h : ∀ φ, C φ → ∃ ψ, C' ψ ∧
      ∀ (e : Fin 1 → V) (f : Empty → V), Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ) :
    V↓[ℒₒᵣ] ⊧* parameterFreeInductionOn ℒₒᵣ C := by
  apply Semantics.modelsSet_iff.mpr
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨ψ, hψ, H⟩ := h φ hφ
  have := Theory.models (T := parameterFreeInductionOn ℒₒᵣ C') V ⟨ψ, hψ, rfl⟩
  simpa [parameterFreeSuccInd, models_iff, Semiformula.eval_univCl, succInd,
    Semiformula.eval_substs, Semiformula.eval_emb, H] using this

lemma IParameterFree_weakerThan_of_le {Γ : Polarity} {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) :
    𝗜ᶠ Γ s₁ ⪯ 𝗜ᶠ Γ s₂ :=
  weakerThan_of_models.{0} _ _ fun V _ hV ↦ by
    have h₀ : V↓[ℒₒᵣ] ⊧* 𝗘𝗔 := models_of_ss hV Set.subset_union_left
    have : V↓[ℒₒᵣ] ⊧* parameterFreeInductionOn ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s₂) :=
      models_of_ss hV Set.subset_union_right
    exact Semantics.ModelsSet.union_iff.mpr ⟨h₀,
      parameterFreeInductionOn.models_of_exists_eval_iff fun _ hφ ↦
        (hφ.exists_eval_iff_of_le h).imp fun _ H ↦ ⟨H.1, H.2 V⟩⟩

end monotonicity

end axioms

section standardModel

instance models_IParameterFree (Γ : Polarity) (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗜ᶠ Γ s := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, -, rfl⟩
  exact models_succInd _

instance (Γ : Polarity) (s : ℕ) : Consistent (𝗜ᶠ Γ s) := (𝗜ᶠ Γ s).consistent_of_sound (Eq ⊥) rfl

end standardModel

end FFL.FirstOrder.Arithmetic
