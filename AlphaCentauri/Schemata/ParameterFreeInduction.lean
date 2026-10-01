module

public import AlphaCentauri.Schemata.EA
public import AlphaCentauri.Schemata.Induction

/-!
# Parameter-free induction `𝗜ᶠ` over the strict hierarchy

`𝗜ᶠ Γ s` is `𝗘𝗔` together with successor induction for the `StrictHierarchy Γ s` formulas `φ(x)`
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

/-- `𝗜ᶠ Γ s` is `𝗘𝗔` together with the parameter-free induction schema for `StrictHierarchy Γ s`.
- [Bek99, §1] -/
abbrev IParameterFree (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝗘𝗔 ∪ parameterFreeInductionOn ℒₒᵣ (Arithmetic.StrictHierarchy Γ s)

prefix:max "𝗜ᶠ " => IParameterFree

lemma parameterFreeInductionOn_subset (h : ∀ {φ : Semisentence L 1}, C φ → C' φ) :
    parameterFreeInductionOn L C ⊆ parameterFreeInductionOn L C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma IParameterFree_subset_mono {Γ : Polarity} {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : 𝗜ᶠ Γ s₁ ⊆ 𝗜ᶠ Γ s₂ :=
  Set.union_subset_union_right _ (parameterFreeInductionOn_subset (fun H ↦ H.mono h))

lemma IParameterFree_weakerThan_of_le {Γ : Polarity} {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) :
    𝗜ᶠ Γ s₁ ⪯ 𝗜ᶠ Γ s₂ :=
  WeakerThan.ofSubset (IParameterFree_subset_mono h)

lemma parameterFreeInductionOn_subset_InductionScheme (Γ : Polarity) (s : ℕ) :
    parameterFreeInductionOn ℒₒᵣ (Arithmetic.StrictHierarchy Γ s) ⊆
      InductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s) := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact ⟨Rew.emb ▹ φ, StrictHierarchy.rew_iff.mpr hφ, rfl⟩

instance IParameterFree_weakerThan_EA_union_InductionScheme (Γ : Polarity) (s : ℕ) :
    𝗜ᶠ Γ s ⪯ 𝗘𝗔 ∪ InductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s) :=
  WeakerThan.ofSubset
    (Set.union_subset_union_right _ (parameterFreeInductionOn_subset_InductionScheme Γ s))

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗔 ⪯ 𝗜ᶠ Γ s := WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (s : ℕ) : 𝗣𝗔⁻ ⪯ 𝗜ᶠ Γ s :=
  WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ 𝗘𝗔) inferInstance

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜ᶠ Γ s :=
  WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗘𝗔) inferInstance

end axioms

section standardModel

instance models_IParameterFree (Γ : Polarity) (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗜ᶠ Γ s := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, -, rfl⟩
  exact models_succInd _

instance (Γ : Polarity) (s : ℕ) : Consistent (𝗜ᶠ Γ s) := (𝗜ᶠ Γ s).consistent_of_sound (Eq ⊥) rfl

end standardModel

end FFL.FirstOrder.Arithmetic
