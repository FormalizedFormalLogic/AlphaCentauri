module

public import Foundation.FirstOrder.Arithmetic.Schemata
public import AlphaCentauri.Vorspiel.Definable

/-!
# The least number schemes `𝗟𝚺` and `𝗟𝚷`

- [HP98, §I.2(a)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

section axioms

/-- The least number scheme for the class `Γ` of `Semiformula ℒₒᵣ ℕ 1`.
- [HP98, §I.2(a)] -/
def LeastNumberScheme (Γ : ArithmeticSemiformula ℕ 1 → Prop) : ArithmeticTheory :=
  { ψ | ∃ φ : ArithmeticSemiformula ℕ 1, Γ φ ∧ ψ = .univCl (leastNumber φ) }

/-- `𝗟 Γ n` is `𝗣𝗔⁻` together with the least number scheme for `Hierarchy Γ n`.
- [HP98, I.2.3] -/
abbrev LeastNumberOnHierarchy (Γ : Polarity) (n : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ LeastNumberScheme (Arithmetic.Hierarchy Γ n)

prefix:max "𝗟 " => LeastNumberOnHierarchy

/-- `𝗟𝚺 n` is `𝗣𝗔⁻` together with the least number scheme for `𝚺-[n]` formulas.
- [HP98, I.2.3] -/
abbrev LSigma (n : ℕ) : ArithmeticTheory := 𝗟 𝚺 n

prefix:max "𝗟𝚺" => LSigma

/-- `𝗟𝚷 n` is `𝗣𝗔⁻` together with the least number scheme for `𝚷-[n]` formulas.
- [HP98, I.2.3] -/
abbrev LPi (n : ℕ) : ArithmeticTheory := 𝗟 𝚷 n

prefix:max "𝗟𝚷" => LPi

variable {C C' : ArithmeticSemiformula ℕ 1 → Prop} {Γ : Polarity}

lemma LeastNumberScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → C' φ) :
    LeastNumberScheme C ⊆ LeastNumberScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma mem_LeastNumberScheme_of_mem {φ : ArithmeticSemiformula ℕ 1} (hφ : C φ) :
    .univCl (leastNumber φ) ∈ LeastNumberScheme C := ⟨φ, hφ, rfl⟩

lemma LeastNumberOnHierarchy_subset_mono {n₁ n₂} (h : n₁ ≤ n₂) : 𝗟 Γ n₁ ⊆ 𝗟 Γ n₂ :=
  Set.union_subset_union_right _ (LeastNumberScheme_subset (fun H ↦ H.mono h))

lemma LeastNumberOnHierarchy_weakerThan_of_le {n₁ n₂} (h : n₁ ≤ n₂) : 𝗟 Γ n₁ ⪯ 𝗟 Γ n₂ :=
  WeakerThan.ofSubset (LeastNumberOnHierarchy_subset_mono h)

instance (Γ : Polarity) (n : ℕ) : 𝗣𝗔⁻ ⪯ 𝗟 Γ n := WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (n : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗟 Γ n :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  WeakerThan.trans this inferInstance

end axioms

section models

variable {V : Type*} [ORingStructure V]

namespace LeastNumberScheme

variable {C : ArithmeticSemiformula ℕ 1 → Prop} [V↓[ℒₒᵣ] ⊧* LeastNumberScheme C]

private lemma leastNumber_eval {φ : ArithmeticSemiformula ℕ 1} (hφ : C φ) (v : ℕ → V) :
    (∃ x, φ.Eval ![x] v) → ∃ z, φ.Eval ![z] v ∧ ∀ x < z, ¬φ.Eval ![x] v := by
  have : V↓[ℒₒᵣ] ⊧ .univCl (leastNumber φ) :=
    Theory.models (T := LeastNumberScheme C) V (by simpa using mem_LeastNumberScheme_of_mem hφ)
  revert v
  simpa [models_iff, Semiformula.eval_univCl, leastNumber, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using this

lemma least_number {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : ArithmeticSemiformula ℕ 1, C φ ∧ ∀ x, P x ↔ φ.Eval ![x] e)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  rcases hP with ⟨e, φ, Cφ, hφ⟩
  simpa [← hφ] using leastNumber_eval (V := V) Cφ e ⟨x, (hφ x).mp h⟩

end LeastNumberScheme

namespace LeastNumberOnHierarchy

variable (Γ : Polarity) (m : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗟 Γ m]

instance : V↓[ℒₒᵣ] ⊧* LeastNumberScheme (Hierarchy Γ m) :=
  have : V↓[ℒₒᵣ] ⊧* 𝗟 Γ m := inferInstance
  models_of_subtheory this

lemma least_number {P : V → Prop} (hP : Γ-[m].DefinablePred P) {x} (h : P x) :
    ∃ y, P y ∧ ∀ z < y, ¬P z :=
  LeastNumberScheme.least_number (P := P) (C := Hierarchy Γ m) (by
    classical
    rcases hP with ⟨φ, hp⟩
    have : Inhabited V := Classical.inhabited_of_nonempty'
    exact ⟨φ.val.enumerateFVar, (Rew.rewriteMap φ.val.idxOfFVar) ▹ φ.val, by simp,
      by intro x; simp [Semiformula.eval_rewriteMap, hp.df.iff]⟩) h

/-- The least number scheme for `Γ` proves successor induction for `Γ.alt`-definable
predicates. -/
lemma succ_induction {P : V → Prop} (hP : Γ.alt-[m].DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗟 Γ m›
  have : V↓[ℒₒᵣ] ⊧* 𝗤 := models_of_subtheory this
  have hP' : (SigmaPiDelta.alt (Γ : SigmaPiDelta))-[m].DefinablePred P := by
    rw [SigmaPiDelta.alt_coe]; exact hP
  by_contra hcon
  obtain ⟨a, ha⟩ : ∃ x, ¬P x := by simpa using hcon
  obtain ⟨y, hy, hmin⟩ := least_number Γ m (P := fun x ↦ ¬P x) hP'.not ha
  have hy0 : y ≠ 0 := by rintro rfl; exact hy zero
  obtain ⟨z, rfl⟩ := Arithmetic.exists_succ_of_ne_zero hy0
  exact hy (succ z (not_not.mp (hmin z (lt_succ_iff_le.mpr le_rfl))))

end LeastNumberOnHierarchy

variable (n : ℕ)

instance models_LSigma_of_ISigma [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n] : V↓[ℒₒᵣ] ⊧* 𝗟𝚺 n := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n›
  suffices V↓[ℒₒᵣ] ⊧* LeastNumberScheme (Hierarchy 𝚺 n) by
    simpa [LSigma, LeastNumberOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩
  simp only [LeastNumberScheme]
  refine Semantics.ModelsSet.setOf_iff.mpr ?_
  rintro _ ⟨φ, hφ, rfl⟩
  suffices ∀ v : ℕ → V, (∃ x, φ.Eval ![x] v) → ∃ z, φ.Eval ![z] v ∧ ∀ x < z, ¬φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, leastNumber, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this
  intro v ⟨x, hx⟩
  exact InductionOnHierarchy.least_number 𝚺 n (definablePred_of_hierarchy hφ v) hx

instance models_LPi_of_ISigma [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n] : V↓[ℒₒᵣ] ⊧* 𝗟𝚷 n := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n›
  suffices V↓[ℒₒᵣ] ⊧* LeastNumberScheme (Hierarchy 𝚷 n) by
    simpa [LPi, LeastNumberOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩
  simp only [LeastNumberScheme]
  refine Semantics.ModelsSet.setOf_iff.mpr ?_
  rintro _ ⟨φ, hφ, rfl⟩
  suffices ∀ v : ℕ → V, (∃ x, φ.Eval ![x] v) → ∃ z, φ.Eval ![z] v ∧ ∀ x < z, ¬φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, leastNumber, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this
  intro v ⟨x, hx⟩
  exact InductionOnHierarchy.least_number 𝚷 n (definablePred_of_hierarchy hφ v) hx

instance models_IPi_of_LSigma [V↓[ℒₒᵣ] ⊧* 𝗟𝚺 n] : V↓[ℒₒᵣ] ⊧* 𝗜𝚷 n := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗟𝚺 n›
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy 𝚷 n) by
    simpa [IPi, InductionOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩
  simp only [InductionScheme]
  refine Semantics.ModelsSet.setOf_iff.mpr ?_
  rintro _ ⟨φ, hφ, rfl⟩
  suffices ∀ v : ℕ → V, φ.Eval ![0] v → (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) →
      ∀ x, φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this
  intro v
  exact LeastNumberOnHierarchy.succ_induction 𝚺 n (definablePred_of_hierarchy hφ v)

instance models_ISigma_of_LPi [V↓[ℒₒᵣ] ⊧* 𝗟𝚷 n] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗟𝚷 n›
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy 𝚺 n) by
    simpa [ISigma, InductionOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩
  simp only [InductionScheme]
  refine Semantics.ModelsSet.setOf_iff.mpr ?_
  rintro _ ⟨φ, hφ, rfl⟩
  suffices ∀ v : ℕ → V, φ.Eval ![0] v → (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) →
      ∀ x, φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this
  intro v
  exact LeastNumberOnHierarchy.succ_induction 𝚷 n (definablePred_of_hierarchy hφ v)

end models

section theorems

/-- The induction schemes for `𝚺-[n]` and `𝚷-[n]` formulas give the same theory.
- [HP98, Theorem I.2.4] -/
theorem ISigma_equiv_IPi (n : ℕ) : 𝗜𝚺 n ≊ 𝗜𝚷 n :=
  Equiv.antisymm_iff.mpr
    ⟨weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance,
     weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance⟩

/-- The least number scheme for `𝚺-[n]` formulas gives the same theory as the induction
scheme for `𝚺-[n]` formulas.
- [HP98, Lemma I.2.8]
- [HP98, Lemma I.2.12] -/
theorem LSigma_equiv_ISigma (n : ℕ) : 𝗟𝚺 n ≊ 𝗜𝚺 n :=
  Equiv.antisymm_iff.mpr
    ⟨weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance,
     weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance⟩

/-- The least number scheme for `𝚷-[n]` formulas gives the same theory as the induction
scheme for `𝚺-[n]` formulas.
- [HP98, Lemma I.2.8]
- [HP98, Lemma I.2.12] -/
theorem LPi_equiv_ISigma (n : ℕ) : 𝗟𝚷 n ≊ 𝗜𝚺 n :=
  Equiv.antisymm_iff.mpr
    ⟨weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance,
     weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance⟩

end theorems

end FFL.FirstOrder.Arithmetic
