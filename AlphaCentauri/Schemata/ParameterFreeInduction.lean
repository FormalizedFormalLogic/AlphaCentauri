module

public import AlphaCentauri.Schemata.EA
public import AlphaCentauri.Schemata.Induction

/-!
# Parameter-free induction schemata `𝗜⁻` over the strict hierarchy

`𝗜⁻ Γ s` is `𝗘𝗔` together with the induction scheme restricted to `StrictHierarchy Γ s` formulas
`φ(x)` that carry no free variable besides the induction variable `x`.

- [Bek99, §1]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

section axioms

/-- The induction scheme for the class `Γ` of `Semisentence L 1`, restricted to formulas with no
free variable besides the induction variable.
- [Bek99, §1] -/
def ParameterFreeInductionScheme (L : Language) [L.ORing] (Γ : Semisentence L 1 → Prop) :
    Theory L :=
  { σ | ∃ φ : Semisentence L 1, Γ φ ∧ σ = .univCl (succInd (Rew.emb ▹ φ)) }

/-- `𝗜⁻ Γ s` is `𝗘𝗔` together with the parameter-free induction scheme for `StrictHierarchy Γ s`.
- [Bek99, §1] -/
abbrev ParameterFreeInductionOnStrictHierarchy (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝗘𝗔 ∪ ParameterFreeInductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s)

prefix:max "𝗜⁻ " => ParameterFreeInductionOnStrictHierarchy

variable {L : Language} [L.ORing] {C C' : Semisentence L 1 → Prop}

lemma ParameterFreeInductionScheme_subset (h : ∀ {φ : Semisentence L 1}, C φ → C' φ) :
    ParameterFreeInductionScheme L C ⊆ ParameterFreeInductionScheme L C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma ParameterFreeInductionOnStrictHierarchy_subset_mono {Γ : Polarity} {s₁ s₂ : ℕ}
    (h : s₁ ≤ s₂) : 𝗜⁻ Γ s₁ ⊆ 𝗜⁻ Γ s₂ :=
  Set.union_subset_union_right _
    (ParameterFreeInductionScheme_subset (fun H ↦ H.mono h))

lemma ParameterFreeInductionOnStrictHierarchy_weakerThan_of_le {Γ : Polarity} {s₁ s₂ : ℕ}
    (h : s₁ ≤ s₂) : 𝗜⁻ Γ s₁ ⪯ 𝗜⁻ Γ s₂ :=
  WeakerThan.ofSubset (ParameterFreeInductionOnStrictHierarchy_subset_mono h)

lemma ParameterFreeInductionScheme_subset_InductionScheme (Γ : Polarity) (s : ℕ) :
    ParameterFreeInductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s) ⊆
      InductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s) := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨Rew.emb ▹ φ, StrictHierarchy.rew_iff.mpr hφ, rfl⟩

instance ParameterFreeInductionOnStrictHierarchy_weakerThan_EA_union_InductionOnStrictHierarchy
    (Γ : Polarity) (s : ℕ) :
    𝗜⁻ Γ s ⪯ 𝗘𝗔 ∪ InductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s) :=
  WeakerThan.ofSubset
    (Set.union_subset_union_right _ (ParameterFreeInductionScheme_subset_InductionScheme Γ s))

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗔 ⪯ 𝗜⁻ Γ s := WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (s : ℕ) : 𝗣𝗔⁻ ⪯ 𝗜⁻ Γ s :=
  WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ 𝗘𝗔) inferInstance

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜⁻ Γ s :=
  WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗘𝗔) inferInstance

end axioms

section standardModel

instance models_ParameterFreeInductionOnStrictHierarchy (Γ : Polarity) (s : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧* 𝗜⁻ Γ s := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, -, rfl⟩
  exact models_succInd _

instance (Γ : Polarity) (s : ℕ) : Consistent (𝗜⁻ Γ s) :=
  (𝗜⁻ Γ s).consistent_of_sound (Eq ⊥) rfl

end standardModel

end FFL.FirstOrder.Arithmetic
