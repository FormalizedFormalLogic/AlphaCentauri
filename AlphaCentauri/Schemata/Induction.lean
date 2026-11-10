module

public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import Foundation.FirstOrder.Arithmetic.IDelta.Basic
public import Foundation.FirstOrder.Arithmetic.Schema.DeltaInduction
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Variants of the induction schemata

The $\Delta$ induction scheme over the broad hierarchy, parameter-free induction over the prenex
hierarchy, and induction for bounded existential formulas.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.FFL.Entailment

section DeltaOnBroadHierarchy

/-! ## The `Δ` induction scheme over the broad hierarchy

`𝗜𝚫⁺ s` is the variant of Foundation's `𝗜𝚫 s` whose `Δ` induction scheme ranges over the broad
hierarchy `ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s` instead of the prenex one.

- [Sla04, §1.2]
-/

/-- The `Δ` induction scheme for the broad hierarchy `ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s`. -/
abbrev IDeltaOnBroadHierarchy (s : ℕ) : ArithmeticTheory :=
  𝗜𝚺₀ ∪ DeltaInductionScheme (ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s)

prefix:max "𝗜𝚫⁺ " => IDeltaOnBroadHierarchy

lemma IDelta_subset_IDeltaOnBroadHierarchy (s : ℕ) : 𝗜𝚫 s ⊆ 𝗜𝚫⁺ s :=
  Set.union_subset_union_right _ (DeltaInductionScheme_subset (·.hierarchy))

instance IDelta_weakerThan_IDeltaOnBroadHierarchy (s : ℕ) : 𝗜𝚫 s ⪯ 𝗜𝚫⁺ s :=
  WeakerThan.ofSubset (IDelta_subset_IDeltaOnBroadHierarchy s)

instance models_IDeltaOnBroadHierarchy (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚫⁺ s := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, ψ, -, -, rfl⟩
  apply models_deltaInd_iff _ _ |>.mpr
  intro f _ hzero hsucc x
  induction x with
  | zero => exact hzero
  | succ x ih => exact hsucc x ih

end DeltaOnBroadHierarchy

section DeltaInduction

/-! ## The `Δ` induction schemes between `𝗜𝚺 n` and `𝗕𝚺(n + 1)`

A $\Delta_{n + 1}$ predicate of a model of `𝗕𝚺(n + 1)` obeys successor induction, also when it is
defined by formulas of the broad hierarchy; whether `𝗜𝚫(n + 1)` proves `𝗕𝚺(n + 1)` is open.

- [Sla04, §2.1]
-/

/-- Every model of `𝗕𝚺(n + 1)` satisfies `𝗜𝚫⁺(n + 1)`.
- [Sla04, §2.1] -/
lemma models_IDeltaOnBroadHierarchy_of_models_BSigma_succ (n : ℕ) (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜𝚫⁺(n + 1) := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  have h₀ : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n :=
    have : 𝗕𝚷 n ⪯ 𝗕𝚺 (n + 1) := CollectionOnPrenexHierarchy_weakerThan_BSigma_succ 𝚷 n
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  refine Semantics.ModelsSet.union_iff.mpr ⟨h₀, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, ψ, hφ, hψ, rfl⟩
  apply (models_deltaInd_iff φ ψ).mpr
  intro f heq zero succ
  obtain ⟨Q, hQ, hQiff⟩ := exists_pi_definableRel_iff (Bounding.definablePred_of_hierarchy hφ f)
  obtain ⟨R, hR, hRiff⟩ := exists_pi_definableRel_iff (Bounding.definablePred_of_hierarchy hψ f)
  exact succ_induction_of_complementary_exists_pi hQ hR hQiff
    (fun x ↦ by rw [heq x, not_not]; exact hRiff x) zero succ

/-- `𝗜𝚫⁺(n + 1)` is at most as strong as `𝗕𝚺(n + 1)`.
- [Sla04, §2.1] -/
theorem IDeltaOnBroadHierarchy_weakerThan_BSigma (n : ℕ) : 𝗜𝚫⁺(n + 1) ⪯ 𝗕𝚺(n + 1) :=
  weakerThan_of_models.{0} _ _ fun V _ _ ↦
    models_IDeltaOnBroadHierarchy_of_models_BSigma_succ n V

/-- $\mathsf{I}\Delta_{n + 1}$ proves $\mathsf{B}\Sigma_{n + 1}$ for every $n$. An open problem;
it holds once exponentiation is adjoined to $\mathsf{I}\Delta_0$.
- [HP98, Remark after Theorem I.2.5]
- [Sla04] -/
def BSigmaWeakerThanIDelta : Prop := ∀ n : ℕ, 𝗕𝚺(n + 1) ⪯ 𝗜𝚫(n + 1)

end DeltaInduction

section ParameterFreeInduction

/-! ## Parameter-free induction `𝗜ᶠ` over the prenex hierarchy

`𝗜ᶠ Γ s` is `𝗘𝗔` together with successor induction for the
`ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s` formulas `φ(x)`
that carry no free variable besides the induction variable `x`.

- [Bek99, §1]
-/

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

end axioms

section standardModel

instance models_IParameterFree (Γ : Polarity) (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗜ᶠ Γ s := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, -, rfl⟩
  exact models_succInd _

instance (Γ : Polarity) (s : ℕ) : Consistent (𝗜ᶠ Γ s) := (𝗜ᶠ Γ s).consistent_of_sound (Eq ⊥) rfl

end standardModel

end ParameterFreeInduction

section BoundedInduction

/-! ## Induction for bounded existential formulas

$\mathsf{I}\mathsf{E}_k$ is induction for $E_k$ formulas over $\mathsf{PA}^-$, where $E_k$ and
$U_k$ count the alternations of blocks of bounded quantifiers over an open matrix.

- [Wil85]
- [Smi93, Definition 2.1, Definition 2.2]
- [DAq05, §8]
- [Car16]
-/

variable {ξ : Type*}

mutual

/-- `Eₖ` formulas: a block `∃ x₁ < t₁, ⋯, ∃ xₘ < tₘ` over a `Uₖ₋₁` formula, or an open formula
for `k = 0`, where the bound `tᵢ` of `xᵢ` mentions only the earlier variables.
- [Wil85]
- [Smi93, Definition 2.1] -/
inductive Semiformula.BoundedExistential : ℕ → {n : ℕ} → ArithmeticSemiformula ξ n → Prop
  | of_open {k n : ℕ} {φ : ArithmeticSemiformula ξ n} : φ.Open → BoundedExistential k φ
  | of_boundedUniversal {k n : ℕ} {φ : ArithmeticSemiformula ξ n} :
      BoundedUniversal k φ → BoundedExistential (k + 1) φ
  | bexsLT {k n : ℕ} (t : ArithmeticSemiterm ξ n) {φ : ArithmeticSemiformula ξ (n + 1)} :
      BoundedExistential (k + 1) φ → BoundedExistential (k + 1) (Semiformula.bexsLT t φ)

/-- `Uₖ` formulas: a block `∀ x₁ < t₁, ⋯, ∀ xₘ < tₘ` over an `Eₖ₋₁` formula, or an open formula
for `k = 0`, where the bound `tᵢ` of `xᵢ` mentions only the earlier variables.
- [Wil85]
- [Smi93, Definition 2.1] -/
inductive Semiformula.BoundedUniversal : ℕ → {n : ℕ} → ArithmeticSemiformula ξ n → Prop
  | of_open {k n : ℕ} {φ : ArithmeticSemiformula ξ n} : φ.Open → BoundedUniversal k φ
  | of_boundedExistential {k n : ℕ} {φ : ArithmeticSemiformula ξ n} :
      BoundedExistential k φ → BoundedUniversal (k + 1) φ
  | ballLT {k n : ℕ} (t : ArithmeticSemiterm ξ n) {φ : ArithmeticSemiformula ξ (n + 1)} :
      BoundedUniversal (k + 1) φ → BoundedUniversal (k + 1) (Semiformula.ballLT t φ)

end

/-- Induction for `Eₖ` formulas over $\mathsf{PA}^-$.
- [Wil85]
- [Smi93, Definition 2.2] -/
abbrev IE (k : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ (Semiformula.BoundedExistential k)

@[inherit_doc] notation "𝗜𝗘₁" => IE 1

@[inherit_doc] notation "𝗜𝗘₂" => IE 2

instance (k : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ IE k :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻)
    (Entailment.WeakerThan.ofSubset Set.subset_union_left)

section

variable {V : Type*} [ORingStructure V]

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝗘₁] : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  Semantics.ModelsSet.of_subset (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗜𝗘₁) Set.subset_union_left

instance {k : ℕ} [V↓[ℒₒᵣ] ⊧* IE k] :
    V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Semiformula.BoundedExistential k) :=
  Semantics.ModelsSet.of_subset (inferInstance : V↓[ℒₒᵣ] ⊧* IE k) Set.subset_union_right

end

/-- $\mathsf{I}\mathsf{E}_1$ is strictly weaker than $\mathsf{I}\Delta_0$. An open problem.
- [DAq05, §8] -/
def IE1StrictlyWeakerThanISigma0 : Prop := 𝗜𝗘₁ ⪱ 𝗜𝚺₀

/-- $\mathsf{I}\mathsf{E}_k$ is strictly weaker than $\mathsf{I}\mathsf{E}_{k + 1}$ for each
$k \ge 1$. An open problem.
- [Wil85, §4.13, Problem (1)]
- [Car16] -/
def IEStrictlyWeakerThanIESucc : Prop := ∀ k : ℕ, 1 ≤ k → IE k ⪱ IE (k + 1)

/-- $\mathsf{I}\mathsf{E}_1$ proves the least number principle for $U_1$ formulas. An open problem.
- [Wil85, §4.13, Problem (2)] -/
def LeastNumberBoundedUniversalWeakerThanIE1 : Prop :=
  𝗣𝗔⁻ ∪ LeastNumberScheme (Semiformula.BoundedUniversal 1) ⪯ 𝗜𝗘₁

end BoundedInduction

end FFL.FirstOrder.Arithmetic
