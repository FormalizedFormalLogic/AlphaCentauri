module

public import AlphaCentauri.Schemata.EA
public import AlphaCentauri.Schemata.Induction

/-!
# Parameter-free induction schemata `𝗜ᶠ` over the strict hierarchy

`𝗜ᶠ Γ s` is `𝗘𝗔` together with the induction scheme restricted to `StrictHierarchy Γ s` formulas
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

/-- `𝗜ᶠ Γ s` is `𝗘𝗔` together with the parameter-free induction scheme for `StrictHierarchy Γ s`.
- [Bek99, §1] -/
abbrev IParameterFree (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝗘𝗔 ∪ ParameterFreeInductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s)

prefix:max "𝗜ᶠ " => IParameterFree

variable {L : Language} [L.ORing] {C C' : Semisentence L 1 → Prop}

lemma ParameterFreeInductionScheme_subset (h : ∀ {φ : Semisentence L 1}, C φ → C' φ) :
    ParameterFreeInductionScheme L C ⊆ ParameterFreeInductionScheme L C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma IParameterFree_subset_mono {Γ : Polarity} {s₁ s₂ : ℕ}
    (h : s₁ ≤ s₂) : 𝗜ᶠ Γ s₁ ⊆ 𝗜ᶠ Γ s₂ :=
  Set.union_subset_union_right _
    (ParameterFreeInductionScheme_subset (fun H ↦ H.mono h))

lemma IParameterFree_weakerThan_of_le {Γ : Polarity} {s₁ s₂ : ℕ}
    (h : s₁ ≤ s₂) : 𝗜ᶠ Γ s₁ ⪯ 𝗜ᶠ Γ s₂ :=
  WeakerThan.ofSubset (IParameterFree_subset_mono h)

lemma ParameterFreeInductionScheme_subset_InductionScheme (Γ : Polarity) (s : ℕ) :
    ParameterFreeInductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s) ⊆
      InductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s) := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨Rew.emb ▹ φ, StrictHierarchy.rew_iff.mpr hφ, rfl⟩

instance IParameterFree_weakerThan_EA_union_InductionScheme
    (Γ : Polarity) (s : ℕ) :
    𝗜ᶠ Γ s ⪯ 𝗘𝗔 ∪ InductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s) :=
  WeakerThan.ofSubset
    (Set.union_subset_union_right _ (ParameterFreeInductionScheme_subset_InductionScheme Γ s))

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗔 ⪯ 𝗜ᶠ Γ s := WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (s : ℕ) : 𝗣𝗔⁻ ⪯ 𝗜ᶠ Γ s :=
  WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ 𝗘𝗔) inferInstance

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜ᶠ Γ s :=
  WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗘𝗔) inferInstance

end axioms

section standardModel

instance models_IParameterFree (Γ : Polarity) (s : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧* 𝗜ᶠ Γ s := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, -, rfl⟩
  exact models_succInd _

instance (Γ : Polarity) (s : ℕ) : Consistent (𝗜ᶠ Γ s) :=
  (𝗜ᶠ Γ s).consistent_of_sound (Eq ⊥) rfl

end standardModel

end FFL.FirstOrder.Arithmetic
