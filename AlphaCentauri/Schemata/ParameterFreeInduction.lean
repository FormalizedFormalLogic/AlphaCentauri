module

public import AlphaCentauri.Init
public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata
public import AlphaCentauri.Schemata.DeltaInduction

/-! # Parameter-free induction `𝗜ᶠ` over the prenex hierarchy

Parameter-free induction over the prenex hierarchy.

- [Bek99, §1]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.FFL.Entailment


section axioms

variable {L : Language} [L.ORing] {C C' : Semisentence L 1 → Prop} (Γ : Polarity) (s : ℕ)

variable (L)

/-- The parameter-free induction instance for a formula `φ` of one free variable:
`φ(0) → (∀ x, φ(x) → φ(x + 1)) → ∀ x, φ(x)`.
- [Bek99, §1] -/
def parameterFreeSuccInd (φ : Semisentence L 1) : Sentence L := .univCl (succInd (Rew.emb ▹ φ))

/-- The parameter-free induction schema restricted to the formulas satisfying `C`:
`{ φ(0) → (∀ x, φ(x) → φ(x + 1)) → ∀ x, φ(x) | C φ }`.
- [Bek99, §1] -/
def parameterFreeInductionOn (C : Semisentence L 1 → Prop) : Set (Sentence L) :=
  parameterFreeSuccInd L '' {φ | C φ}

variable {L}

/-- `𝗜ᶠ Γ s` is `𝗘𝗔` together with the parameter-free induction schema for
`ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s`.
- [Bek99, §1] -/
abbrev IParameterFree : ArithmeticTheory :=
  𝗘𝗔 ∪ parameterFreeInductionOn ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s)

prefix:max "𝗜ᶠ " => IParameterFree

lemma parameterFreeInductionOn_subset_InductionScheme :
    parameterFreeInductionOn ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s) ⊆
      InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s) := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact ⟨Rew.emb ▹ φ, Bounding.PrenexHierarchy.rew_iff.mpr hφ, rfl⟩

instance IParameterFree_weakerThan_EA_union_InductionScheme :
    𝗜ᶠ Γ s ⪯ 𝗘𝗔 ∪ InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s) :=
  WeakerThan.ofSubset
    (Set.union_subset_union_right _ (parameterFreeInductionOn_subset_InductionScheme Γ s))

instance : 𝗘𝗔 ⪯ 𝗜ᶠ Γ s := WeakerThan.ofSubset Set.subset_union_left

instance : 𝗣𝗔⁻ ⪯ 𝗜ᶠ Γ s :=
  WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ 𝗘𝗔) inferInstance

instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜ᶠ Γ s :=
  WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗘𝗔) inferInstance

end axioms

variable (Γ : Polarity) (s : ℕ)

instance models_IParameterFree : ℕ↓[ℒₒᵣ] ⊧* 𝗜ᶠ Γ s := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, -, rfl⟩
  exact models_succInd _

instance : Consistent (𝗜ᶠ Γ s) := (𝗜ᶠ Γ s).consistent_of_sound (Eq ⊥) rfl



end FFL.FirstOrder.Arithmetic
