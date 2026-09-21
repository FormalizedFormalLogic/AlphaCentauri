module

public import AlphaCentauri.Schemata.Collection.Basic
public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy

/-!
# The induction schemes `𝗜` and `𝗜𝚫` over the strict hierarchy

The $\Sigma_n$ and $\Pi_n$ of the literature are the strict hierarchy, so `𝗜 Γ s` is the induction
scheme over `StrictHierarchy Γ s`; `𝗜𝗡𝗗 Γ s` is its broad counterpart, as `𝗕⁺ Γ s` is of `𝗕 Γ s`.

A $\Delta_s$ formula is not a syntactic class, so the induction scheme for it carries its own
equivalence hypothesis: the axiom for a pair `φ`, `ψ` of $\Sigma_s$ formulas assumes that `φ` and
`¬ψ` define the same set and concludes successor induction for `φ`.

- [HP98, §I.2(a)]
- [Sla04, §1.2]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

section axioms

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

/-- `𝗜 Γ s` is `𝗣𝗔⁻` together with the induction scheme for `StrictHierarchy Γ s`.
- [HP98, §I.2(a)] -/
abbrev InductionOnStrictHierarchy (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s)

prefix:max "𝗜 " => InductionOnStrictHierarchy

lemma InductionOnStrictHierarchy_subset_InductionOnHierarchy (Γ : Polarity) (s : ℕ) :
    𝗜 Γ s ⊆ 𝗜𝗡𝗗 Γ s :=
  Set.union_subset_union_right _ (InductionScheme_subset (·.hierarchy))

instance InductionOnStrictHierarchy_weakerThan_InductionOnHierarchy (Γ : Polarity) (s : ℕ) :
    𝗜 Γ s ⪯ 𝗜𝗡𝗗 Γ s :=
  WeakerThan.ofSubset (InductionOnStrictHierarchy_subset_InductionOnHierarchy Γ s)

lemma InductionOnStrictHierarchy_zero (Γ : Polarity) : 𝗜 Γ 0 = 𝗜𝚺₀ := by
  refine congrArg _ (Set.ext fun σ ↦ ⟨?_, ?_⟩)
  · rintro ⟨φ, hφ, rfl⟩; exact ⟨φ, Arithmetic.Hierarchy.zero_iff.mp hφ.hierarchy, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩; exact ⟨φ, .zero hφ, rfl⟩

lemma InductionOnStrictHierarchy_subset_mono {Γ : Polarity} {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) :
    𝗜 Γ s₁ ⊆ 𝗜 Γ s₂ :=
  Set.union_subset_union_right _ (InductionScheme_subset (fun H ↦ H.mono h))

lemma InductionOnStrictHierarchy_subset_of_lt {Γ Γ' : Polarity} {s₁ s₂ : ℕ} (h : s₁ < s₂) :
    𝗜 Γ s₁ ⊆ 𝗜 Γ' s₂ :=
  Set.union_subset_union_right _ (InductionScheme_subset (fun H ↦ H.strict_mono _ h))

lemma InductionOnStrictHierarchy_weakerThan_of_le {Γ : Polarity} {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) :
    𝗜 Γ s₁ ⪯ 𝗜 Γ s₂ :=
  WeakerThan.ofSubset (InductionOnStrictHierarchy_subset_mono h)

instance (Γ : Polarity) (s : ℕ) : 𝗣𝗔⁻ ⪯ 𝗜 Γ s := WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜 Γ s :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  WeakerThan.trans this inferInstance

/-- The `Δ` induction axiom for the pair `φ`, `ψ`: successor induction for `φ`, under the
hypothesis that `φ` and `¬ψ` define the same set.
- [Sla04, §1.2] -/
def deltaInd {ξ} (φ ψ : Semiformula L ξ 1) : Formula L ξ :=
  “(∀ x, !φ x ↔ ¬!ψ x) → !φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”

/-- The `Δ` induction scheme for the class `Γ` of `ArithmeticSemiformula ℕ 1`.
- [Sla04, §1.2] -/
def DeltaInductionScheme (Γ : ArithmeticSemiformula ℕ 1 → Prop) : ArithmeticTheory :=
  { σ | ∃ φ ψ : ArithmeticSemiformula ℕ 1, Γ φ ∧ Γ ψ ∧ σ = .univCl (deltaInd φ ψ) }

/-- `𝗜𝚫 s` is `𝗜𝚺₀` together with the `Δ` induction scheme for `StrictHierarchy 𝚺 s`.
- [Sla04, §1.2] -/
abbrev IDelta (s : ℕ) : ArithmeticTheory :=
  𝗜𝚺₀ ∪ DeltaInductionScheme (Arithmetic.StrictHierarchy 𝚺 s)

prefix:max "𝗜𝚫 " => IDelta

/-- The `Δ` induction scheme for the broad hierarchy `Hierarchy 𝚺 s`. -/
abbrev IDeltaOnBroadHierarchy (s : ℕ) : ArithmeticTheory :=
  𝗜𝚺₀ ∪ DeltaInductionScheme (Arithmetic.Hierarchy 𝚺 s)

prefix:max "𝗜𝚫⁺ " => IDeltaOnBroadHierarchy

variable {C C' : ArithmeticSemiformula ℕ 1 → Prop}

lemma DeltaInductionScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → C' φ) :
    DeltaInductionScheme C ⊆ DeltaInductionScheme C' := by
  rintro _ ⟨φ, ψ, hφ, hψ, rfl⟩; exact ⟨φ, ψ, h hφ, h hψ, rfl⟩

lemma mem_DeltaInductionScheme_of_mem {φ ψ : ArithmeticSemiformula ℕ 1} (hφ : C φ) (hψ : C ψ) :
    .univCl (deltaInd φ ψ) ∈ DeltaInductionScheme C := ⟨φ, ψ, hφ, hψ, rfl⟩

lemma IDelta_subset_mono {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : 𝗜𝚫 s₁ ⊆ 𝗜𝚫 s₂ :=
  Set.union_subset_union_right _ (DeltaInductionScheme_subset (fun H ↦ H.mono h))

lemma IDelta_weakerThan_of_le {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : 𝗜𝚫 s₁ ⪯ 𝗜𝚫 s₂ :=
  WeakerThan.ofSubset (IDelta_subset_mono h)

lemma IDelta_subset_IDeltaOnBroadHierarchy (s : ℕ) : 𝗜𝚫 s ⊆ 𝗜𝚫⁺ s :=
  Set.union_subset_union_right _ (DeltaInductionScheme_subset (·.hierarchy))

instance IDelta_weakerThan_IDeltaOnBroadHierarchy (s : ℕ) : 𝗜𝚫 s ⪯ 𝗜𝚫⁺ s :=
  WeakerThan.ofSubset (IDelta_subset_IDeltaOnBroadHierarchy s)

instance (s : ℕ) : 𝗜𝚺₀ ⪯ 𝗜𝚫 s := WeakerThan.ofSubset Set.subset_union_left

instance (s : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚫 s :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀ := inferInstance
  WeakerThan.trans this inferInstance

end axioms

section models

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- The reading of the `Δ` induction axiom in a model of `𝗣𝗔⁻`.
- [Sla04, §1.2] -/
lemma models_deltaInd_iff (φ ψ : ArithmeticSemiformula ℕ 1) :
    V↓[ℒₒᵣ] ⊧ .univCl (deltaInd φ ψ) ↔
      ∀ f : ℕ → V, (∀ x : V, φ.Eval ![x] f ↔ ¬ψ.Eval ![x] f) →
        φ.Eval ![0] f → (∀ x : V, φ.Eval ![x] f → φ.Eval ![x + 1] f) → ∀ x : V, φ.Eval ![x] f := by
  simp [models_iff, Semiformula.eval_univCl, deltaInd, Semiformula.eval_substs]

end models

section standardModel

instance models_InductionOnStrictHierarchy (Γ : Polarity) (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗜 Γ s :=
  models_of_ss inferInstance (InductionOnStrictHierarchy_subset_InductionOnHierarchy Γ s)

instance models_IDeltaOnBroadHierarchy (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚫⁺ s := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, ψ, -, -, rfl⟩
  apply models_deltaInd_iff _ _ |>.mpr
  intro f _ hzero hsucc x
  induction x with
  | zero => exact hzero
  | succ x ih => exact hsucc x ih

instance models_IDelta (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚫 s :=
  Semantics.ModelsSet.of_subset (models_IDeltaOnBroadHierarchy s)
    (IDelta_subset_IDeltaOnBroadHierarchy s)

instance (s : ℕ) : Consistent (𝗜𝚫 s) := (𝗜𝚫 s).consistent_of_sound (Eq ⊥) rfl

end standardModel

end FFL.FirstOrder.Arithmetic
