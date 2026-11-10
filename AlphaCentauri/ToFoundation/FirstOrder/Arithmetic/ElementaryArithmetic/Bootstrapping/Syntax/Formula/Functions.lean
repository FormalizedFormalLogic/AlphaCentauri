module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping.Syntax.Formula.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping.Syntax.Term.Functions
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions

/-!
# Functions on codes of formulas in models of $\mathsf{EA}$

The part of `Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Formula/Functions.lean` on
operations on codes of formulas, ported to models of $\mathsf{EA}$: negation `neg`, implication
`imp`, equivalence `iff`, the shift `shift` of free variables, substitution `subst` for the bound
variables, the instantiation `free` of a bound variable by a free one and the complexity
`formulaComplexity`. The blueprints and formulas are Foundation's; the recursions on formulas
carry a bound on their values, and inductions are on locally $\Delta_0$ predicates.

- [HP98, §V.3]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

section structuralBound

variable {c : V}

lemma seven_le_exp_exp {n : V} (hn : 2 ≤ n) : (7 : V) ≤ Exp.exp (Exp.exp n) := by
  have h2 : Exp.exp (2 : V) = 4 := by
    rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, exp_succ, exp_one]; norm_num
  have h4 : Exp.exp (4 : V) = 16 := by
    rw [show (4 : V) = 2 * 2 by norm_num, exp_even, h2, sq]; norm_num
  refine le_trans ?_ (exp_exp_le_of_le hn)
  rw [h2, h4]
  exact_mod_cast (by norm_num : (7 : ℕ) ≤ 16)

/-- The code `a' ∷ y` with a tag `a' ≤ 7` is bounded by `Exp.exp (Exp.exp (8 * (a ∷ p) + c))`
when `y` is bounded by `Exp.exp (Exp.exp (8 * p + c))`. -/
lemma adjoin_le_exp_exp_of_le (hc : 1 ≤ c) {a a' p y : V} (ha' : a' ≤ 7)
    (hy : y ≤ Exp.exp (Exp.exp (8 * p + c))) :
    a' ∷ y ≤ Exp.exp (Exp.exp (8 * (a ∷ p) + c)) := by
  have hn : (2 : V) ≤ 8 * p + c + 1 := by
    rw [← one_add_one_eq_two]; exact add_le_add_left (le_trans hc le_add_self) 1
  apply le_trans (adjoin_le_exp_exp (le_trans one_le_two hn) (le_trans ha' (seven_le_exp_exp hn))
    (le_trans hy (exp_exp_le_of_le le_self_add))) (exp_exp_le_of_le _)
  have : p + 1 ≤ a ∷ p := succ_le_iff_lt.mpr (lt_adjoin' a p)
  calc 8 * p + c + 1 + 2 ≤ 8 * p + c + 8 := by
        rw [add_assoc]
        exact add_le_add_right (by
          rw [show (1 : V) + 2 = 3 by norm_num]; exact_mod_cast (by norm_num : (3 : ℕ) ≤ 8)) _
    _ = 8 * (p + 1) + c := by grind
    _ ≤ 8 * (a ∷ p) + c := by gcongr

/-- The code `a' ∷ ⟪y₁, y₂⟫` with a tag `a' ≤ 7` is bounded by
`Exp.exp (Exp.exp (8 * (a ∷ ⟪p₁, p₂⟫) + c))` when each `yᵢ` is bounded by
`Exp.exp (Exp.exp (8 * pᵢ + c))`. -/
lemma adjoin_pair_le_exp_exp_of_le (hc : 1 ≤ c) {a a' p₁ p₂ y₁ y₂ : V} (ha' : a' ≤ 7)
    (hy₁ : y₁ ≤ Exp.exp (Exp.exp (8 * p₁ + c))) (hy₂ : y₂ ≤ Exp.exp (Exp.exp (8 * p₂ + c))) :
    a' ∷ ⟪y₁, y₂⟫ ≤ Exp.exp (Exp.exp (8 * (a ∷ ⟪p₁, p₂⟫) + c)) := by
  set m := max p₁ p₂
  have hpa (a b : V) : ⟪a, b⟫ ≤ a ∷ b := by rw [adjoin_def]; exact le_self_add
  have hn : (1 : V) ≤ 8 * m + c := le_trans hc le_add_self
  have h₁ : ⟪y₁, y₂⟫ ≤ Exp.exp (Exp.exp (8 * m + c + 2)) :=
    le_trans (hpa _ _) <| adjoin_le_exp_exp hn
      (le_trans hy₁ (exp_exp_le_of_le (by gcongr; exact le_max_left _ _)))
      (le_trans hy₂ (exp_exp_le_of_le (by gcongr; exact le_max_right _ _)))
  have hn2 : (2 : V) ≤ 8 * m + c + 2 := le_add_self
  have h₂ : a' ∷ ⟪y₁, y₂⟫ ≤ Exp.exp (Exp.exp (8 * m + c + 2 + 2)) :=
    adjoin_le_exp_exp (le_trans one_le_two hn2) (le_trans ha' (seven_le_exp_exp hn2)) h₁
  apply le_trans h₂ (exp_exp_le_of_le _)
  have : m + 1 ≤ a ∷ ⟪p₁, p₂⟫ :=
    succ_le_iff_lt.mpr (lt_of_le_of_lt (max_le (le_pair_left _ _) (le_pair_right _ _))
      (lt_adjoin' a _))
  calc 8 * m + c + 2 + 2 ≤ 8 * m + c + 8 := by
        have h48 : (2 : V) + 2 ≤ 8 := by
          rw [show (2 : V) + 2 = 4 by norm_num]; exact_mod_cast (by norm_num : (4 : ℕ) ≤ 8)
        rw [add_assoc]
        exact add_le_add_right h48 _
    _ = 8 * (m + 1) + c := by grind
    _ ≤ 8 * (a ∷ ⟪p₁, p₂⟫) + c := by gcongr

/-- The code `a' ∷ ⟪k, R, w⟫` with a tag `a' ≤ 7` is bounded by
`Exp.exp (Exp.exp (8 * (a ∷ ⟪k, R, v⟫) + c))` when `w` is bounded by
`Exp.exp (Exp.exp (8 * v + c))`. -/
lemma adjoin_pair_pair_le_exp_exp_of_le (hc : 1 ≤ c) {a a' k R v w : V} (ha' : a' ≤ 7)
    (hw : w ≤ Exp.exp (Exp.exp (8 * v + c))) :
    a' ∷ ⟪k, R, w⟫ ≤ Exp.exp (Exp.exp (8 * (a ∷ ⟪k, R, v⟫) + c)) := by
  set m := max k (max R v)
  set E := Exp.exp (Exp.exp (8 * m + c))
  have hpa (a b : V) : ⟪a, b⟫ ≤ a ∷ b := by rw [adjoin_def]; exact le_self_add
  have hn : (1 : V) ≤ 8 * m + c := le_trans hc le_add_self
  have hmle : m ≤ 8 * m + c :=
    le_trans (le_mul_of_one_le_left (by simp) (by exact_mod_cast (by norm_num))) le_self_add
  have hk : k ≤ E := le_exp_exp (le_trans (le_max_left _ _) hmle)
  have hR : R ≤ E := le_exp_exp (le_trans (le_trans (le_max_left R v) (le_max_right _ _)) hmle)
  have hw' : w ≤ E :=
    le_trans hw (exp_exp_le_of_le (by gcongr; exact le_trans (le_max_right R v) (le_max_right _ _)))
  have h₁ : ⟪R, w⟫ ≤ Exp.exp (Exp.exp (8 * m + c + 2)) :=
    le_trans (hpa R w) (adjoin_le_exp_exp hn hR hw')
  have h₂ : ⟪k, R, w⟫ ≤ Exp.exp (Exp.exp (8 * m + c + 2 + 2)) :=
    le_trans (hpa _ _) (adjoin_le_exp_exp (le_trans hn le_self_add)
      (le_trans hk (exp_exp_le_of_le le_self_add)) h₁)
  have hn2 : (2 : V) ≤ 8 * m + c + 2 + 2 := le_add_self
  have h₃ : a' ∷ ⟪k, R, w⟫ ≤ Exp.exp (Exp.exp (8 * m + c + 2 + 2 + 2)) :=
    adjoin_le_exp_exp (le_trans one_le_two hn2) (le_trans ha' (seven_le_exp_exp hn2)) h₂
  apply le_trans h₃ (exp_exp_le_of_le _)
  have : m + 1 ≤ a ∷ ⟪k, R, v⟫ := by
    refine succ_le_iff_lt.mpr (lt_of_le_of_lt (max_le (le_pair_left _ _) (max_le ?_ ?_))
      (lt_adjoin' a _))
    · exact le_trans (le_pair_left R v) (le_pair_right _ _)
    · exact le_trans (le_pair_right R v) (le_pair_right _ _)
  have h68 : (2 : V) + 2 + 2 ≤ 8 := by
    rw [show (2 : V) + 2 + 2 = 6 by norm_num]
    exact_mod_cast (by norm_num : (6 : ℕ) ≤ 8)
  calc 8 * m + c + 2 + 2 + 2 = (8 * m + c) + (2 + 2 + 2) := by simp only [add_assoc]
    _ ≤ (8 * m + c) + 8 := add_le_add_right h68 _
    _ = 8 * (m + 1) + c := by grind
    _ ≤ 8 * (a ∷ ⟪k, R, v⟫) + c := by gcongr

end structuralBound

variable {L : Language} [L.Encodable] [L.LORDefinable]

section negation

namespace Negation

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Negation (blueprint) in
/-- The recursion on formulas computing the code of the negation. -/
noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel _ k R v := ^nrel k R v
  nrel _ k R v := ^rel k R v
  verum _ := ^⊥
  falsum _ := ^⊤
  and _ _ _ y₁ y₂ := y₁ ^⋎ y₂
  or _ _ _ y₁ y₂ := y₁ ^⋏ y₂
  all _ _ ys := ^∃ ys.[0]
  exs _ _ ys := ^∀ ys.[0]
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  rel_locallyDelta0 := qqNRel_locallyDelta0.comp₃ (LocallyDelta0Function.var 1)
    (LocallyDelta0Function.var 2) (LocallyDelta0Function.var 3)
  nrel_locallyDelta0 := qqRel_locallyDelta0.comp₃ (LocallyDelta0Function.var 1)
    (LocallyDelta0Function.var 2) (LocallyDelta0Function.var 3)
  verum_locallyDelta0 := LocallyDelta0Function.const _
  falsum_locallyDelta0 := LocallyDelta0Function.const _
  and_locallyDelta0 := qqOr_locallyDelta0.comp₂ (LocallyDelta0Function.var 3)
    (LocallyDelta0Function.var 4)
  or_locallyDelta0 := qqAnd_locallyDelta0.comp₂ (LocallyDelta0Function.var 3)
    (LocallyDelta0Function.var 4)
  all_locallyDelta0 := qqExs_locallyDelta0.comp₁ <| nth_locallyDelta0.comp₂
    (LocallyDelta0Function.var 2) (LocallyDelta0Function.const 0)
  exs_locallyDelta0 := qqAll_locallyDelta0.comp₁ <| nth_locallyDelta0.comp₂
    (LocallyDelta0Function.var 2) (LocallyDelta0Function.const 0)
  bound _ p := Exp.exp (Exp.exp (8 * p + 1))
  rel_le_bound _ _ _ v := adjoin_pair_pair_le_exp_exp_of_le le_rfl
    (by exact_mod_cast (by norm_num)) (le_exp_exp_eight_mul_add v 1)
  nrel_le_bound _ _ _ v := adjoin_pair_pair_le_exp_exp_of_le le_rfl zero_le
    (le_exp_exp_eight_mul_add v 1)
  verum_le_bound _ := adjoin_le_exp_exp_of_le le_rfl
    (by exact_mod_cast (by norm_num)) zero_le
  falsum_le_bound _ := adjoin_le_exp_exp_of_le le_rfl
    (by exact_mod_cast (by norm_num)) zero_le
  and_le_bound _ _ _ _ _ h₁ h₂ := adjoin_pair_le_exp_exp_of_le le_rfl
    (by exact_mod_cast (by norm_num)) h₁ h₂
  or_le_bound _ _ _ _ _ h₁ h₂ := adjoin_pair_le_exp_exp_of_le le_rfl
    (by exact_mod_cast (by norm_num)) h₁ h₂
  all_le_bound _ _ _ h := by
    simp only [nth_adjoin_zero]
    exact adjoin_le_exp_exp_of_le le_rfl (by exact_mod_cast (by norm_num)) h
  exs_le_bound _ _ _ h := by
    simp only [nth_adjoin_zero]
    exact adjoin_le_exp_exp_of_le le_rfl (by exact_mod_cast (by norm_num)) h
  bound_monotone _ _ _ h := exp_monotone_le.mpr (exp_monotone_le.mpr (by gcongr))
  bound_locallyDelta0 := LocallyDelta0Function.exp_exp_mul_add 8 (LocallyDelta0Function.var 1)
    (LocallyDelta0Function.const 1)

end Negation

open Negation

variable (L)

/-- The code of the negation of the code `p` of a formula. -/
noncomputable def neg (p : V) : V := construction.result L 0 p

variable {L}

section

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (negGraph)

instance neg.defined : 𝚺ᴬ₁-Function₁ neg (V := V) L via negGraph L := .mk fun v ↦ by
  simpa [negGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
      using! construction.result_defined.defined ![v 0, 0, v 1]

instance neg.definable : 𝚺ᴬ₁-Function₁ neg (V := V) L := neg.defined.to_definable

instance neg.definable' (Γ m) : Γᴬ_[m + 1]-Function₁ neg (V := V) L := .of_sigmaOne neg.definable

end

lemma neg_locallyDelta0 : LocallyDelta0Function₁ (neg (V := V) L) :=
  (construction.result_locallyDelta0 L).comp₂ (LocallyDelta0Function.const 0)
    (LocallyDelta0Function.var 0)

@[simp] lemma neg_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    neg L (^rel k R v) = ^nrel k R v := by simp [neg, hR, hv, construction]

@[simp] lemma neg_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    neg L (^nrel k R v) = ^rel k R v := by simp [neg, hR, hv, construction]

@[simp] lemma neg_verum :
    neg L (^⊤ : V) = ^⊥ := by simp [neg, construction]

@[simp] lemma neg_falsum :
    neg L (^⊥ : V) = ^⊤ := by simp [neg, construction]

@[simp] lemma neg_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    neg L (p ^⋏ q) = neg L p ^⋎ neg L q := by simp [neg, hp, hq, construction]

@[simp] lemma neg_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    neg L (p ^⋎ q) = neg L p ^⋏ neg L q := by simp [neg, hp, hq, construction]

@[simp] lemma neg_all {p : V} (hp : IsUFormula L p) :
    neg L (^∀ p) = ^∃ (neg L p) := by simp [neg, hp, construction]

@[simp] lemma neg_ex {p : V} (hp : IsUFormula L p) :
    neg L (^∃ p) = ^∀ (neg L p) := by simp [neg, hp, construction]

lemma neg_not_uformula {x : V} (h : ¬IsUFormula L x) :
    neg L x = 0 := construction.result_prop_not _ h

lemma IsUFormula.neg {p : V} : IsUFormula L p → IsUFormula L (Bootstrapping.neg L p) := by
  intro hp
  refine IsUFormula.induction (P := fun p ↦ IsUFormula L (Bootstrapping.neg L p)) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ p hp
  · exact isUFormula_locallyDelta0.pred_comp
      (neg_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

@[simp] lemma IsUFormula.bv_neg {p : V} :
    IsUFormula L p → bv L (Bootstrapping.neg L p) = bv L p := by
  intro hp
  refine IsUFormula.induction (P := fun p ↦ bv L (Bootstrapping.neg L p) = bv L p) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ p hp
  · exact LocallyDelta0.eq
      (bv_locallyDelta0.comp₁ (neg_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))))
      (bv_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · intro k R v hR hv; simp [*]
  · intro k R v hR hv; simp [*]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]

@[simp] lemma IsUFormula.neg_neg {p : V} :
    IsUFormula L p → Bootstrapping.neg L (Bootstrapping.neg L p) = p := by
  intro hp
  refine IsUFormula.induction
    (P := fun p ↦ Bootstrapping.neg L (Bootstrapping.neg L p) = p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · exact LocallyDelta0.eq
      (neg_locallyDelta0.comp₁ (neg_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))))
      (LocallyDelta0Function.var (0 : Fin 1))
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]

@[simp] lemma IsUFormula.neg_iff {p : V} :
    IsUFormula L (Bootstrapping.neg L p) ↔ IsUFormula L p := by
  constructor
  · intro h; by_contra hp
    have Hp : IsUFormula L p := by by_contra hp; simp [neg_not_uformula hp] at h
    contradiction
  · exact IsUFormula.neg

@[simp] lemma IsSemiformula.neg_iff {n p : V} :
    IsSemiformula L n (neg L p) ↔ IsSemiformula L n p := by
  constructor
  · intro h; by_contra hp
    have Hp : IsUFormula L p := by by_contra hp; simp [neg_not_uformula hp] at h
    have : IsSemiformula L n p := ⟨Hp, by simpa [Hp.bv_neg] using h.bv_le⟩
    contradiction
  · intro h; exact ⟨by simp [h.isUFormula], by simpa [h.isUFormula] using h.bv_le⟩

alias ⟨IsSemiformula.elim_neg, IsSemiformula.neg⟩ := IsSemiformula.neg_iff

@[simp] lemma neg_inj_iff {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    neg L p = neg L q ↔ p = q := by
  constructor
  · intro h; simpa [hp.neg_neg, hq.neg_neg] using congrArg (neg L) h
  · rintro rfl; rfl

end negation

variable (L)

noncomputable def imp (p q : V) : V := neg L p ^⋎ q

noncomputable def iff (p q : V) : V := (imp L p q) ^⋏ (imp L q p)

variable {L}

section imp

@[simp] lemma IsUFormula.imp {p q : V} :
    IsUFormula L (imp L p q) ↔ IsUFormula L p ∧ IsUFormula L q := by
  simp [Bootstrapping.imp]

@[simp] lemma IsSemiformula.imp {n p q : V} :
    IsSemiformula L n (imp L p q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  simp [Bootstrapping.imp]

section

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (impGraph)

instance imp.defined : 𝚺ᴬ₁-Function₂ imp (V := V) L via impGraph L :=
  .mk fun v ↦ by simp [impGraph]; rfl

instance imp.definable : 𝚺ᴬ₁-Function₂ imp (V := V) L := imp.defined.to_definable

instance imp.definable' (Γ m) : Γᴬ_[m + 1]-Function₂ imp (V := V) L := imp.definable.of_sigmaOne

end

lemma imp_locallyDelta0 : LocallyDelta0Function₂ (imp (V := V) L) :=
  qqOr_locallyDelta0.comp₂ (neg_locallyDelta0.comp₁ (LocallyDelta0Function.var 0))
    (LocallyDelta0Function.var 1)

end imp

section iff

@[simp] lemma IsUFormula.iff {p q : V} :
    IsUFormula L (iff L p q) ↔ IsUFormula L p ∧ IsUFormula L q := by
  simp only [Bootstrapping.iff, and, imp, and_iff_left_iff_imp, and_imp]
  intros; simp_all

@[simp] lemma IsSemiformula.iff {n p q : V} :
    IsSemiformula L n (iff L p q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  simp only [Bootstrapping.iff, and, imp, and_iff_left_iff_imp, and_imp]
  intros; simp_all

@[simp] lemma lt_iff_left (p q : V) : p < iff L p q := lt_trans (lt_or_right _ _) (lt_K!_right _ _)

@[simp] lemma lt_iff_right (p q : V) : q < iff L p q := lt_trans (lt_or_right _ _) (lt_K!_left _ _)

section

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (iffGraph)

instance iff.defined : 𝚺ᴬ₁-Function₂ iff (V := V) L via iffGraph L :=
  .mk fun v ↦ by simp [iffGraph]; rfl

instance iff.definable : 𝚺ᴬ₁-Function₂ iff (V := V) L := iff.defined.to_definable

instance iff_definable' (Γ m) : Γᴬ_[m + 1]-Function₂ iff (V := V) L := iff.definable.of_sigmaOne

end

end iff

section shift

namespace Shift

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Shift (blueprint) in
variable (L) in
/-- The recursion on formulas raising the indices of the free variables by one. -/
noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel _ k R v := ^rel k R (termShiftVec L k v)
  nrel _ k R v := ^nrel k R (termShiftVec L k v)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ y₁ y₂ := y₁ ^⋏ y₂
  or _ _ _ y₁ y₂ := y₁ ^⋎ y₂
  all _ _ ys := ^∀ ys.[0]
  exs _ _ ys := ^∃ ys.[0]
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  rel_locallyDelta0 := qqRel_locallyDelta0.comp₃ (LocallyDelta0Function.var 1)
    (LocallyDelta0Function.var 2) (termShiftVec_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
      (LocallyDelta0Function.var 3))
  nrel_locallyDelta0 := qqNRel_locallyDelta0.comp₃ (LocallyDelta0Function.var 1)
    (LocallyDelta0Function.var 2) (termShiftVec_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
      (LocallyDelta0Function.var 3))
  verum_locallyDelta0 := LocallyDelta0Function.const _
  falsum_locallyDelta0 := LocallyDelta0Function.const _
  and_locallyDelta0 := qqAnd_locallyDelta0.comp₂ (LocallyDelta0Function.var 3)
    (LocallyDelta0Function.var 4)
  or_locallyDelta0 := qqOr_locallyDelta0.comp₂ (LocallyDelta0Function.var 3)
    (LocallyDelta0Function.var 4)
  all_locallyDelta0 := qqAll_locallyDelta0.comp₁ <| nth_locallyDelta0.comp₂
    (LocallyDelta0Function.var 2) (LocallyDelta0Function.const 0)
  exs_locallyDelta0 := qqExs_locallyDelta0.comp₁ <| nth_locallyDelta0.comp₂
    (LocallyDelta0Function.var 2) (LocallyDelta0Function.const 0)
  bound _ p := Exp.exp (Exp.exp (8 * p + 2))
  rel_le_bound _ k _ v := adjoin_pair_pair_le_exp_exp_of_le one_le_two zero_le
    (termShiftVec_le_exp_exp k v)
  nrel_le_bound _ k _ v := adjoin_pair_pair_le_exp_exp_of_le one_le_two
    (by exact_mod_cast (by norm_num)) (termShiftVec_le_exp_exp k v)
  verum_le_bound _ := adjoin_le_exp_exp_of_le one_le_two
    (by exact_mod_cast (by norm_num)) zero_le
  falsum_le_bound _ := adjoin_le_exp_exp_of_le one_le_two
    (by exact_mod_cast (by norm_num)) zero_le
  and_le_bound _ _ _ _ _ h₁ h₂ := adjoin_pair_le_exp_exp_of_le one_le_two
    (by exact_mod_cast (by norm_num)) h₁ h₂
  or_le_bound _ _ _ _ _ h₁ h₂ := adjoin_pair_le_exp_exp_of_le one_le_two
    (by exact_mod_cast (by norm_num)) h₁ h₂
  all_le_bound _ _ _ h := by
    simp only [nth_adjoin_zero]
    exact adjoin_le_exp_exp_of_le one_le_two (by exact_mod_cast (by norm_num)) h
  exs_le_bound _ _ _ h := by
    simp only [nth_adjoin_zero]
    exact adjoin_le_exp_exp_of_le one_le_two (by exact_mod_cast (by norm_num)) h
  bound_monotone _ _ _ h := exp_monotone_le.mpr (exp_monotone_le.mpr (by gcongr))
  bound_locallyDelta0 := LocallyDelta0Function.exp_exp_mul_add 8 (LocallyDelta0Function.var 1)
    (LocallyDelta0Function.const 2)

end Shift

open Shift

variable (L)

/-- The code of the formula obtained by raising the indices of the free variables by one. -/
noncomputable def shift (p : V) : V := (construction L).result L 0 p

variable {L}

section

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (shiftGraph)

instance shift.defined : 𝚺ᴬ₁-Function₁[V] shift L via shiftGraph L := .mk fun v ↦ by
  simpa [shiftGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
      using! (construction L).result_defined.defined ![v 0, 0, v 1]

instance shift.definable : 𝚺ᴬ₁-Function₁[V] shift L := shift.defined.to_definable

instance shift.definable' (Γ m) : Γᴬ_[m + 1]-Function₁[V] shift L := shift.definable.of_sigmaOne

end

lemma shift_locallyDelta0 : LocallyDelta0Function₁ (shift (V := V) L) :=
  ((construction L).result_locallyDelta0 L).comp₂ (LocallyDelta0Function.const 0)
    (LocallyDelta0Function.var 0)

@[simp] lemma shift_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    shift L (^rel k R v) = ^rel k R (termShiftVec L k v) := by simp [shift, hR, hv, construction]

@[simp] lemma shift_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    shift L (^nrel k R v) = ^nrel k R (termShiftVec L k v) := by
  simp [shift, hR, hv, construction]

@[simp] lemma shift_verum : shift L (^⊤ : V) = ^⊤ := by simp [shift, construction]

@[simp] lemma shift_falsum : shift L (^⊥ : V) = ^⊥ := by simp [shift, construction]

@[simp] lemma shift_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    shift L (p ^⋏ q) = shift L p ^⋏ shift L q := by simp [shift, hp, hq, construction]

@[simp] lemma shift_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    shift L (p ^⋎ q) = shift L p ^⋎ shift L q := by simp [shift, hp, hq, construction]

@[simp] lemma shift_all {p : V} (hp : IsUFormula L p) :
    shift L (^∀ p) = ^∀ (shift L p) := by simp [shift, hp, construction]

@[simp] lemma shift_exs {p : V} (hp : IsUFormula L p) :
    shift L (^∃ p) = ^∃ (shift L p) := by simp [shift, hp, construction]

lemma shift_not_uformula {x : V} (h : ¬IsUFormula L x) :
    shift L x = 0 := (construction L).result_prop_not _ h

lemma IsUFormula.shift {p : V} : IsUFormula L p → IsUFormula L (Bootstrapping.shift L p) := by
  intro hp
  refine IsUFormula.induction (P := fun p ↦ IsUFormula L (Bootstrapping.shift L p)) ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ p hp
  · exact isUFormula_locallyDelta0.pred_comp
      (shift_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

lemma IsUFormula.bv_shift {p : V} :
    IsUFormula L p → bv L (Bootstrapping.shift L p) = bv L p := by
  intro hp
  refine IsUFormula.induction (P := fun p ↦ bv L (Bootstrapping.shift L p) = bv L p) ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ p hp
  · exact LocallyDelta0.eq
      (bv_locallyDelta0.comp₁ (shift_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))))
      (bv_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq, hp.shift, hq.shift]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq, hp.shift, hq.shift]
  · intro p hp ihp; simp [hp, ihp, hp.shift]
  · intro p hp ihp; simp [hp, ihp, hp.shift]

lemma IsSemiformula.shift {n p : V} :
    IsSemiformula L n p → IsSemiformula L n (Bootstrapping.shift L p) := by
  intro hp
  refine IsSemiformula.induction
    (P := fun n p ↦ IsSemiformula L n (Bootstrapping.shift L p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · exact isSemiformula_locallyDelta0.rel_comp₂ (LocallyDelta0Function.var (0 : Fin 2))
      (shift_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2)))
  · intro n k r v hr hv; simp [hr, hv.isUTerm]
  · intro n k r v hr hv; simp [hr, hv.isUTerm]
  · simp
  · simp
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p hp ihp; simp [hp.isUFormula, ihp]
  · intro n p hp ihp; simp [hp.isUFormula, ihp]

@[simp] lemma IsUFormula.shift_iff {p : V} :
    IsUFormula L (Bootstrapping.shift L p) ↔ IsUFormula L p := by
  constructor
  · intro h; by_contra hp
    have Hp : IsUFormula L p := by by_contra hp; simp [shift_not_uformula hp] at h
    contradiction
  · exact IsUFormula.shift

@[simp] lemma IsSemiformula.shift_iff {n p : V} :
    IsSemiformula L n (Bootstrapping.shift L p) ↔ IsSemiformula L n p :=
  ⟨fun h ↦ by
    have : IsUFormula L p := by by_contra hp; simp [shift_not_uformula hp] at h
    exact ⟨this, by simpa [this.bv_shift] using h.bv_le⟩,
    IsSemiformula.shift⟩

lemma shift_neg {n p : V} (hp : IsSemiformula L n p) :
    shift L (neg L p) = neg L (shift L p) := by
  refine IsSemiformula.induction
    (P := fun _ p ↦ shift L (neg L p) = neg L (shift L p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · exact LocallyDelta0.eq
      (shift_locallyDelta0.comp₁ (neg_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2))))
      (neg_locallyDelta0.comp₁ (shift_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2))))
  · intro n k R v hR hv; simp [hR, hv.isUTerm, hv.termShiftVec.isUTerm]
  · intro n k R v hR hv; simp [hR, hv.isUTerm, hv.termShiftVec.isUTerm]
  · simp
  · simp
  · intro n p q hp hq ihp ihq
    simp [hp.isUFormula, hq.isUFormula, hp.shift.isUFormula, hq.shift.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq
    simp [hp.isUFormula, hq.isUFormula, hp.shift.isUFormula, hq.shift.isUFormula, ihp, ihq]
  · intro n p hp ih; simp [hp.isUFormula, hp.shift.isUFormula, ih]
  · intro n p hp ih; simp [hp.isUFormula, hp.shift.isUFormula, ih]

end shift

section subst


private lemma bvarAt_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 2 → V ↦
      (fun (r : Fin 1 → V) i ↦ ^#(r 0 + i)) (w ·.succ) (w 0) := by
  have : LocallyDelta0Function fun w : Fin 2 → V ↦ ^#(w 1 + w 0) :=
    qqBvar_locallyDelta0.comp₁ (LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.var 1)
      (LocallyDelta0Function.var 0))
  simpa using this

/-- The list `^#a, ^#(a + 1), …, ^#(a + n - 1)`. -/
noncomputable def bvarRange (a n : V) : V := listMap (fun r i ↦ ^#(r 0 + i)) ![a] (rangeList n)

@[simp] lemma len_bvarRange (a n : V) : len (bvarRange a n) = n := by
  rw [bvarRange, len_listMap bvarAt_locallyDelta0, len_rangeList]

@[simp] lemma nth_bvarRange {a n i : V} (hi : i < n) : (bvarRange a n).[i] = ^#(a + i) := by
  rw [bvarRange, nth_listMap bvarAt_locallyDelta0 _ _ (by simpa using hi), nth_rangeList hi]
  simp

lemma bvarRange_locallyDelta0 : LocallyDelta0Function₂ (bvarRange : V → V → V) := by
  have := (listMap_locallyDelta0 (g := fun (r : Fin 1 → V) i ↦ ^#(r 0 + i))
    bvarAt_locallyDelta0).comp_cons (rangeList_locallyDelta0.comp₁ (LocallyDelta0Function.var 1))
    (u := ![fun w : Fin 2 → V ↦ w 0]) <| Fin.forall_fin_succ.mpr
      ⟨LocallyDelta0Function.var 0, finZeroElim⟩
  convert this using 2 with w
  simp only [bvarRange]
  congr 1
  funext j
  rw [Fin.fin_one_eq_zero j]
  rfl

lemma IsSemitermVec.bvarRange (a n : V) : IsSemitermVec L n (a + n) (bvarRange a n) :=
  IsSemitermVec.iff.mpr ⟨by simp, fun i hi ↦ by
    rw [nth_bvarRange hi]
    exact ⟨by simp, by simpa [add_assoc] using add_le_add_right (succ_le_iff_lt.mpr hi) a⟩⟩

lemma termBShiftVec_bvarRange (a n : V) :
    termBShiftVec L n (bvarRange a n) = bvarRange (a + 1) n := by
  have h := (IsSemitermVec.bvarRange (L := L) a n).isUTerm
  apply nth_ext (by simp [h])
  intro i hi
  rw [len_termBShiftVec h] at hi
  rw [nth_termBShiftVec h hi, nth_bvarRange hi, nth_bvarRange hi]
  simp [add_right_comm]

variable (L)

/-- The code of the term `t` with the indices of its bound variables raised by `d`. -/
noncomputable def termBShiftIter (d t : V) : V := termSubst L (bvarRange d (termBV L t)) t

variable {L}

lemma termBShiftIter_locallyDelta0 : LocallyDelta0Function₂ (termBShiftIter L : V → V → V) :=
  termSubst_locallyDelta0.comp₂ (bvarRange_locallyDelta0.comp₂ (LocallyDelta0Function.var 0)
    (termBV_locallyDelta0.comp₁ (LocallyDelta0Function.var 1))) (LocallyDelta0Function.var 1)

lemma termBShiftIter_zero {t : V} (ht : IsUTerm L t) : termBShiftIter L 0 t = t :=
  termSubst_eq_self ht.isSemiterm fun i hi ↦ by simp [hi]

lemma IsUTerm.termBShiftIter {t : V} (ht : IsUTerm L t) (d : V) :
    IsUTerm L (termBShiftIter L d t) :=
  ((IsSemitermVec.bvarRange d (termBV L t)).termSubst ht.isSemiterm).isUTerm

lemma termBShift_termBShiftIter {t : V} (ht : IsUTerm L t) (d : V) :
    termBShift L (termBShiftIter L d t) = termBShiftIter L (d + 1) t := by
  rw [termBShiftIter, bShift_substs ht.isSemiterm (IsSemitermVec.bvarRange d (termBV L t)),
    termBShiftVec_bvarRange]
  rfl

open Classical in
private lemma qVecIterAt_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 3 → V ↦
      (fun (r : Fin 2 → V) i ↦ if i < r 1 then ^#i else termBShiftIter L (r 1) (r 0).[i - r 1])
        (w ·.succ) (w 0) := by
  have v3 := fun i : Fin 3 ↦ LocallyDelta0Function.var (V := V) i
  have := LocallyDelta0Function.ite (LocallyDelta0.lt (v3 0) (v3 2))
    (qqBvar_locallyDelta0.comp₁ (v3 0))
    ((termBShiftIter_locallyDelta0 (L := L)).comp₂ (v3 2) (nth_locallyDelta0.comp₂ (v3 1)
      (LocallyDelta0Function.sub.comp₂ (v3 0) (v3 2))))
  simpa using this

variable (L)

open Classical in
/-- The list obtained from `w` by `d` applications of `qVec`, given in closed form: the codes
`^#0, …, ^#(d - 1)` followed by the terms of `w` with their bound variables raised by `d`. -/
noncomputable def qVecIter (w d : V) : V :=
  if d = 0 then w else
    listMap (fun r i ↦ if i < r 1 then ^#i else termBShiftIter L (r 1) (r 0).[i - r 1]) ![w, d]
      (rangeList (d + if IsUTermVec L (len w) w then len w else 0))

variable {L}

@[simp] lemma qVecIter_zero (w : V) : qVecIter L w 0 = w := by simp [qVecIter]

open Classical in
lemma len_qVecIter {w d : V} (hd : d ≠ 0) :
    len (qVecIter L w d) = d + if IsUTermVec L (len w) w then len w else 0 := by
  simp only [qVecIter, hd, ↓reduceIte]
  rw [len_listMap qVecIterAt_locallyDelta0, len_rangeList]

open Classical in
lemma nth_qVecIter {w d i : V} (hd : d ≠ 0)
    (hi : i < d + if IsUTermVec L (len w) w then len w else 0) :
    (qVecIter L w d).[i] = if i < d then ^#i else termBShiftIter L d w.[i - d] := by
  simp only [qVecIter, hd, ↓reduceIte]
  rw [nth_listMap qVecIterAt_locallyDelta0 _ _ (by simpa using hi), nth_rangeList hi]
  simp

open Classical in
lemma isUTermVec_qVecIter {w d : V} (hd : d ≠ 0) :
    IsUTermVec L (d + if IsUTermVec L (len w) w then len w else 0) (qVecIter L w d) := by
  refine ⟨(len_qVecIter hd).symm, fun i hi ↦ ?_⟩
  rw [nth_qVecIter hd hi]
  split_ifs with h
  · simp
  · by_cases hw : IsUTermVec L (len w) w
    · have hi' : i - d < len w := by
        simp only [hw, ↓reduceIte] at hi
        exact (tsub_lt_iff_left (not_lt.mp h)).mpr hi
      exact (hw.2 _ hi').termBShiftIter d
    · simp only [hw, ↓reduceIte, add_zero] at hi
      exact absurd hi h

open Classical in
lemma qVec_qVecIter (w d : V) : qVec L (qVecIter L w d) = qVecIter L w (d + 1) := by
  have hlenR := len_qVecIter (L := L) (w := w) (d := d + 1) (by simp)
  by_cases hd : d = 0
  · subst hd
    simp only [qVecIter_zero, zero_add] at hlenR ⊢
    by_cases hw : IsUTermVec L (len w) w
    · simp only [hw, ↓reduceIte] at hlenR
      apply nth_ext (by rw [len_qVec hw, hlenR, add_comm])
      intro i hi
      rw [len_qVec hw] at hi
      rw [nth_qVecIter one_ne_zero (by simpa [hw, add_comm] using hi)]
      rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
      · simp [qVec]
      · have hj : j < len w := by simpa using hi
        have hj' : IsUTerm L w.[j] := hw.2 j hj
        have e : termBShiftIter L 1 w.[j] = termBShift L w.[j] := by
          rw [← zero_add (1 : V), ← termBShift_termBShiftIter hj', termBShiftIter_zero hj']
        simp [qVec, nth_termBShiftVec hw hj, e]
    · simp only [hw, ↓reduceIte, add_zero] at hlenR
      have hq : qVec L w = ?[^#0] := by simp [qVec, termBShiftVec, hw]
      rw [hq]
      apply nth_ext (by simp [hlenR])
      intro i hi
      have hi0 : i = 0 := lt_one_iff_eq_zero.mp (by simpa using hi)
      subst hi0
      rw [nth_qVecIter one_ne_zero (by simp [hw])]
      simp
  · set ℓ : V := if IsUTermVec L (len w) w then len w else 0 with hℓ
    have hx : IsUTermVec L (d + ℓ) (qVecIter L w d) := isUTermVec_qVecIter hd
    have hlx : len (qVecIter L w d) = d + ℓ := len_qVecIter hd
    have hlq : len (qVec L (qVecIter L w d)) = d + ℓ + 1 := len_qVec hx
    apply nth_ext (by rw [hlq, hlenR]; grind)
    intro i hi
    rw [hlq] at hi
    rw [nth_qVecIter (by simp) (by rw [← hℓ]; grind)]
    rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
    · simp [qVec]
    · have hj : j < d + ℓ := by simpa using hi
      have e : (qVec L (qVecIter L w d)).[j + 1] = termBShift L (qVecIter L w d).[j] := by
        rw [qVec, hlx]; simp [nth_termBShiftVec hx hj]
      rw [e, nth_qVecIter hd hj]
      by_cases hjd : j < d
      · simp [hjd]
      · have hw : IsUTermVec L (len w) w := by
          by_contra hw
          simp only [hℓ, hw, ↓reduceIte, add_zero] at hj
          exact hjd hj
        have hjw : j - d < len w := by
          simp only [hℓ, hw, ↓reduceIte] at hj
          exact (tsub_lt_iff_left (not_lt.mp hjd)).mpr hj
        simp only [hjd, ↓reduceIte, add_lt_add_iff_right, add_tsub_add_eq_tsub_right]
        exact termBShift_termBShiftIter (hw.2 _ hjw) d

open Classical in
lemma qVecIter_locallyDelta0 :
    LocallyDelta0Function fun v : Fin 2 → V ↦ qVecIter L (v 0) (v 1) := by
  have v2 := fun i : Fin 2 ↦ LocallyDelta0Function.var (V := V) i
  have hℓ : LocallyDelta0Function fun v : Fin 2 → V ↦
      if IsUTermVec L (len (v 0)) (v 0) then len (v 0) else 0 :=
    LocallyDelta0Function.ite (isUTermVec_locallyDelta0.rel_comp₂
      (len_locallyDelta0.comp₁ (v2 0)) (v2 0)) (len_locallyDelta0.comp₁ (v2 0))
      (LocallyDelta0Function.const 0)
  have hmap := (listMap_locallyDelta0 (g := fun (r : Fin 2 → V) i ↦
      if i < r 1 then ^#i else termBShiftIter L (r 1) (r 0).[i - r 1])
    qVecIterAt_locallyDelta0).comp_cons
    (rangeList_locallyDelta0.comp₁ (LocallyDelta0Function.add.comp₂ (v2 1) hℓ))
    (u := ![fun w : Fin 2 → V ↦ w 0, fun w ↦ w 1]) <| Fin.forall_fin_succ.mpr
      ⟨v2 0, Fin.forall_fin_succ.mpr ⟨v2 1, finZeroElim⟩⟩
  have := LocallyDelta0Function.ite (LocallyDelta0.eq (v2 1) (LocallyDelta0Function.const 0))
    (v2 0) hmap
  convert this using 2 with v
  simp only [qVecIter]
  by_cases h : v 1 = 0
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    congr 1
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact j.elim0


private lemma qVecIter_var_locallyDelta0 {n : ℕ} (w : V) (i : Fin n) :
    LocallyDelta0Function fun u : Fin n → V ↦ qVecIter L w (u i) :=
  qVecIter_locallyDelta0.comp₂ (LocallyDelta0Function.const w) (LocallyDelta0Function.var i)

private lemma add_var_locallyDelta0 {n : ℕ} (m : V) (i : Fin n) :
    LocallyDelta0Function fun u : Fin n → V ↦ m + u i :=
  LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.const m) (LocallyDelta0Function.var i)

private lemma qVecIterAt'_locallyDelta0 :
    LocallyDelta0Function fun u : Fin 2 → V ↦
      (fun (r : Fin 1 → V) d ↦ qVecIter L (r 0) d) (u ·.succ) (u 0) := by
  simpa using (qVecIter_locallyDelta0 (L := L)).retraction ![1, 0]

variable (L)

/-- The largest of the lists `qVecIter L w d` over the depths `d ≤ p`. -/
noncomputable def qVecIterMax (w p : V) : V :=
  listMax (listMap (fun r d ↦ qVecIter L (r 0) d) ![w] (rangeList (p + 1)))

variable {L}

lemma le_qVecIterMax {w p d : V} (hd : d ≤ p) : qVecIter L w d ≤ qVecIterMax L w p := by
  have hd' : d < len (rangeList (p + 1)) := by simpa [lt_succ_iff_le] using hd
  have := nth_le_listMax (v := listMap (fun r d ↦ qVecIter L (r 0) d) ![w] (rangeList (p + 1)))
    (i := d) (by rwa [len_listMap qVecIterAt'_locallyDelta0])
  rw [nth_listMap qVecIterAt'_locallyDelta0 _ _ hd', nth_rangeList (by simpa using hd')] at this
  exact this

lemma le_qVecIterMax_self (w p : V) : w ≤ qVecIterMax L w p := by
  simpa using le_qVecIterMax (L := L) (w := w) (zero_le (a := p))

lemma qVecIterMax_le {w p B : V} (h : ∀ d ≤ p, qVecIter L w d ≤ B) : qVecIterMax L w p ≤ B := by
  apply listMaxss_le
  intro i hi
  rw [len_listMap qVecIterAt'_locallyDelta0] at hi
  rw [nth_listMap qVecIterAt'_locallyDelta0 _ _ hi, nth_rangeList (by simpa using hi)]
  exact h i (lt_succ_iff_le.mp (by simpa using hi))

lemma qVecIterMax_monotone {w p q : V} (h : p ≤ q) : qVecIterMax L w p ≤ qVecIterMax L w q :=
  qVecIterMax_le fun _ hd ↦ le_qVecIterMax (le_trans hd h)

lemma qVecIter_qVec (w d : V) : qVecIter L (qVec L w) d = qVecIter L w (d + 1) := by
  have hP : LocallyDelta0Pred fun d ↦ qVecIter L (qVec L w) d = qVecIter L w (d + 1) :=
    LocallyDelta0.eq (qVecIter_locallyDelta0.comp₂ (LocallyDelta0Function.const _)
        (LocallyDelta0Function.var 0))
      (qVecIter_locallyDelta0.comp₂ (LocallyDelta0Function.const w)
        (LocallyDelta0Function.add_one (LocallyDelta0Function.var 0)))
  revert d
  apply LocallyDelta0Pred.succ_induction hP
  · rw [qVecIter_zero, zero_add, ← zero_add (1 : V), ← qVec_qVecIter, qVecIter_zero]
  · intro d ih
    rw [← qVec_qVecIter, ih, qVec_qVecIter]

lemma qVecIterMax_qVec_le (w p : V) : qVecIterMax L (qVec L w) p ≤ qVecIterMax L w (p + 1) :=
  qVecIterMax_le fun d hd ↦ by
    rw [qVecIter_qVec]; exact le_qVecIterMax (by gcongr)

lemma qVecIterMax_locallyDelta0 :
    LocallyDelta0Function fun u : Fin 2 → V ↦ qVecIterMax L (u 0) (u 1) := by
  have := (listMap_locallyDelta0 (g := fun (r : Fin 1 → V) d ↦ qVecIter L (r 0) d)
    qVecIterAt'_locallyDelta0).comp_cons
    (rangeList_locallyDelta0.comp₁ (LocallyDelta0Function.add_one (LocallyDelta0Function.var 1)))
    (u := ![fun w : Fin 2 → V ↦ w 0]) <| Fin.forall_fin_succ.mpr
      ⟨LocallyDelta0Function.var 0, finZeroElim⟩
  convert listMax_locallyDelta0.comp₁ this using 2 with u
  simp only [qVecIterMax]
  congr 2
  funext j
  rw [Fin.fin_one_eq_zero j]
  rfl

lemma one_le_add_four (x : V) : 1 ≤ x + 4 :=
  le_trans (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 4)) le_add_self

namespace Substs

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (qVecGraph)
open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Substs (blueprint) in
variable (L) in
/-- The recursion on formulas substituting the list `w` for the bound variables; below a
quantifier the list becomes `qVec L w`. -/
noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel w k R v := ^rel k R (termSubstVec L k w v)
  nrel w k R v := ^nrel k R (termSubstVec L k w v)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ y₁ y₂ := y₁ ^⋏ y₂
  or _ _ _ y₁ y₂ := y₁ ^⋎ y₂
  all _ _ ys := ^∀ ys.[0]
  exs _ _ ys := ^∃ ys.[0]
  allChanges w _ := qVec L w
  exsChanges w _ := qVec L w
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [qVec.defined.df]
  exChanges_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [qVec.defined.df]
  change w := qVec L w
  iter w d := qVecIter L w d
  iter_zero := qVecIter_zero
  iter_succ w d := (qVec_qVecIter w d).symm
  iter_locallyDelta0 := qVecIter_locallyDelta0
  rel_locallyDelta0 := qqRel_locallyDelta0.comp₃ (LocallyDelta0Function.var 1)
    (LocallyDelta0Function.var 2) (termSubstVec_locallyDelta0.comp₃
      (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 3))
  nrel_locallyDelta0 := qqNRel_locallyDelta0.comp₃ (LocallyDelta0Function.var 1)
    (LocallyDelta0Function.var 2) (termSubstVec_locallyDelta0.comp₃
      (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 3))
  verum_locallyDelta0 := LocallyDelta0Function.const _
  falsum_locallyDelta0 := LocallyDelta0Function.const _
  and_locallyDelta0 := qqAnd_locallyDelta0.comp₂ (LocallyDelta0Function.var 3)
    (LocallyDelta0Function.var 4)
  or_locallyDelta0 := qqOr_locallyDelta0.comp₂ (LocallyDelta0Function.var 3)
    (LocallyDelta0Function.var 4)
  all_locallyDelta0 := qqAll_locallyDelta0.comp₁ <| nth_locallyDelta0.comp₂
    (LocallyDelta0Function.var 2) (LocallyDelta0Function.const 0)
  exs_locallyDelta0 := qqExs_locallyDelta0.comp₁ <| nth_locallyDelta0.comp₂
    (LocallyDelta0Function.var 2) (LocallyDelta0Function.const 0)
  bound w p := Exp.exp (Exp.exp (8 * p + (qVecIterMax L w p + 4)))
  rel_le_bound w k _ v := adjoin_pair_pair_le_exp_exp_of_le (one_le_add_four _) zero_le <|
    le_trans (termSubstVec_le_exp_exp k w v)
      (exp_exp_le_of_le (by gcongr; exact le_qVecIterMax_self w _))
  nrel_le_bound w k _ v := adjoin_pair_pair_le_exp_exp_of_le (one_le_add_four _)
    (by exact_mod_cast (by norm_num)) <|
    le_trans (termSubstVec_le_exp_exp k w v)
      (exp_exp_le_of_le (by gcongr; exact le_qVecIterMax_self w _))
  verum_le_bound _ := adjoin_le_exp_exp_of_le (one_le_add_four _)
    (by exact_mod_cast (by norm_num)) zero_le
  falsum_le_bound _ := adjoin_le_exp_exp_of_le (one_le_add_four _)
    (by exact_mod_cast (by norm_num)) zero_le
  and_le_bound w p₁ p₂ _ _ h₁ h₂ := adjoin_pair_le_exp_exp_of_le (one_le_add_four _)
    (by exact_mod_cast (by norm_num))
    (le_trans h₁ <| exp_exp_le_of_le <| by
      gcongr; exact qVecIterMax_monotone (lt_K!_left _ _).le)
    (le_trans h₂ <| exp_exp_le_of_le <| by
      gcongr; exact qVecIterMax_monotone (lt_K!_right _ _).le)
  or_le_bound w p₁ p₂ _ _ h₁ h₂ := adjoin_pair_le_exp_exp_of_le (one_le_add_four _)
    (by exact_mod_cast (by norm_num))
    (le_trans h₁ <| exp_exp_le_of_le <| by
      gcongr; exact qVecIterMax_monotone (lt_or_left _ _).le)
    (le_trans h₂ <| exp_exp_le_of_le <| by
      gcongr; exact qVecIterMax_monotone (lt_or_right _ _).le)
  all_le_bound w p₁ _ h := by
    simp only [nth_adjoin_zero]
    refine adjoin_le_exp_exp_of_le (one_le_add_four _)
      (by exact_mod_cast (by norm_num)) (le_trans h (exp_exp_le_of_le ?_))
    gcongr
    exact le_trans (qVecIterMax_qVec_le w p₁)
      (qVecIterMax_monotone (succ_le_iff_lt.mpr (lt_forall p₁)))
  exs_le_bound w p₁ _ h := by
    simp only [nth_adjoin_zero]
    refine adjoin_le_exp_exp_of_le (one_le_add_four _)
      (by exact_mod_cast (by norm_num)) (le_trans h (exp_exp_le_of_le ?_))
    gcongr
    exact le_trans (qVecIterMax_qVec_le w p₁)
      (qVecIterMax_monotone (succ_le_iff_lt.mpr (lt_exists p₁)))
  bound_monotone w _ _ h :=
    exp_exp_le_of_le (by gcongr; exact qVecIterMax_monotone h)
  bound_locallyDelta0 := LocallyDelta0Function.exp_exp_mul_add 8 (LocallyDelta0Function.var 1)
    (LocallyDelta0Function.add.comp₂ qVecIterMax_locallyDelta0 (LocallyDelta0Function.const 4))

end Substs

open Substs

variable (L)

/-- The substitution of the list `w` for the bound variables in the code `p` of a formula. -/
noncomputable def subst (w p : V) : V := (construction L).result L w p

variable {L}

section

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (substsGraph)

instance subst.defined : 𝚺ᴬ₁-Function₂[V] subst L via substsGraph L := by
  unfold substsGraph
  exact (construction L).result_defined

instance subst.definable : 𝚺ᴬ₁-Function₂[V] subst L := subst.defined.to_definable

instance subst.definable' (Γ m) : Γᴬ_[m + 1]-Function₂[V] subst L := subst.definable.of_sigmaOne

end

lemma subst_locallyDelta0 : LocallyDelta0Function₂ (subst (V := V) L) :=
  (construction L).result_locallyDelta0 L

variable {m w : V}

@[simp] lemma substs_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    subst L w (^rel k R v) = ^rel k R (termSubstVec L k w v) := by
  simp [subst, hR, hv, construction]

@[simp] lemma substs_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    subst L w (^nrel k R v) = ^nrel k R (termSubstVec L k w v) := by
  simp [subst, hR, hv, construction]

@[simp] lemma substs_verum (w : V) : subst L w ^⊤ = ^⊤ := by simp [subst, construction]

@[simp] lemma substs_falsum (w : V) : subst L w ^⊥ = ^⊥ := by simp [subst, construction]

@[simp] lemma substs_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    subst L w (p ^⋏ q) = subst L w p ^⋏ subst L w q := by simp [subst, hp, hq, construction]

@[simp] lemma substs_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    subst L w (p ^⋎ q) = subst L w p ^⋎ subst L w q := by simp [subst, hp, hq, construction]

@[simp] lemma substs_all {p} (hp : IsUFormula L p) :
    subst L w (^∀ p) = ^∀ (subst L (qVec L w) p) := by simp [subst, hp, construction]

@[simp] lemma substs_ex {p} (hp : IsUFormula L p) :
    subst L w (^∃ p) = ^∃ (subst L (qVec L w) p) := by simp [subst, hp, construction]

lemma IsSemitermVec.qVecIter {k m w d : V} (h : IsSemitermVec L k (m + d) (qVecIter L w d)) :
    IsSemitermVec L (k + 1) (m + (d + 1)) (qVecIter L w (d + 1)) := by
  rw [← qVec_qVecIter, ← add_assoc]; exact h.qVec

/-- Structural induction on semiformulas with a counter `d ≤ n` of the quantifiers passed. -/
lemma IsSemiformula.depth_induction {Q : V → V → V → Prop}
    (hQ : LocallyDelta0 fun w : Fin 3 → V ↦ Q (w 0) (w 1) (w 2))
    (hrel : ∀ d n k r v, L.IsRel k r → IsSemitermVec L k n v → Q d n (^rel k r v))
    (hnrel : ∀ d n k r v, L.IsRel k r → IsSemitermVec L k n v → Q d n (^nrel k r v))
    (hverum : ∀ d n, Q d n ^⊤)
    (hfalsum : ∀ d n, Q d n ^⊥)
    (hand : ∀ d n p q, IsSemiformula L n p → IsSemiformula L n q →
      Q d n p → Q d n q → Q d n (p ^⋏ q))
    (hor : ∀ d n p q, IsSemiformula L n p → IsSemiformula L n q →
      Q d n p → Q d n q → Q d n (p ^⋎ q))
    (hall : ∀ d n p, IsSemiformula L (n + 1) p → Q (d + 1) (n + 1) p → Q d n (^∀ p))
    (hexs : ∀ d n p, IsSemiformula L (n + 1) p → Q (d + 1) (n + 1) p → Q d n (^∃ p)) {n p} :
    IsSemiformula L n p → ∀ d ≤ n, Q d n p := by
  intro hp
  refine IsSemiformula.induction (P := fun n p ↦ ∀ d ≤ n, Q d n p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hp
  · exact (LocallyDelta0.ball_le_function (LocallyDelta0Function.var (0 : Fin 2)) hQ).of_iff
      fun w ↦ by simp
  · intro n k r v hr hv d _; exact hrel d n k r v hr hv
  · intro n k r v hr hv d _; exact hnrel d n k r v hr hv
  · intro n d _; exact hverum d n
  · intro n d _; exact hfalsum d n
  · intro n p q hp hq ihp ihq d hd; exact hand d n p q hp hq (ihp d hd) (ihq d hd)
  · intro n p q hp hq ihp ihq d hd; exact hor d n p q hp hq (ihp d hd) (ihq d hd)
  · intro n p hp ih d hd; exact hall d n p hp (ih (d + 1) (by simpa using hd))
  · intro n p hp ih d hd; exact hexs d n p hp (ih (d + 1) (by simpa using hd))

@[simp] lemma IsSemiformula.subst {n p m w : V} :
    IsSemiformula L n p → IsSemitermVec L n m w → IsSemiformula L m (subst L w p) := by
  intro hp hw
  suffices H : ∀ d ≤ n, IsSemitermVec L n (m + d) (qVecIter L w d) →
      IsSemiformula L (m + d) (Bootstrapping.subst L (qVecIter L w d) p) by
    simpa using H 0 zero_le (by simpa using hw)
  have v3 := fun i : Fin 3 ↦ LocallyDelta0Function.var (V := V) i
  have hwd := qVecIter_var_locallyDelta0 (L := L) w (0 : Fin 3)
  have hmd := add_var_locallyDelta0 m (0 : Fin 3)
  refine IsSemiformula.depth_induction
    (Q := fun d n p ↦ IsSemitermVec L n (m + d) (qVecIter L w d) →
      IsSemiformula L (m + d) (Bootstrapping.subst L (qVecIter L w d) p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hp
  · exact (isSemitermVec_locallyDelta0.comp₃ (v3 1) hmd hwd).imp
      (isSemiformula_locallyDelta0.rel_comp₂ hmd (subst_locallyDelta0.comp₂ hwd (v3 2)))
  · intro d n k R v hR hv hw'; simp [hR, hv.isUTerm, hw'.termSubstVec hv]
  · intro d n k R v hR hv hw'; simp [hR, hv.isUTerm, hw'.termSubstVec hv]
  · intro d n _; simp
  · intro d n _; simp
  · intro d n p q hp hq ihp ihq hw'
    simp [hp.isUFormula, hq.isUFormula, ihp hw', ihq hw']
  · intro d n p q hp hq ihp ihq hw'
    simp [hp.isUFormula, hq.isUFormula, ihp hw', ihq hw']
  · intro d n p hp ih hw'
    simpa [hp.isUFormula, qVec_qVecIter, add_assoc] using ih hw'.qVecIter
  · intro d n p hp ih hw'
    simpa [hp.isUFormula, qVec_qVecIter, add_assoc] using ih hw'.qVecIter

lemma substs_neg {n m w p : V} (hp : IsSemiformula L n p) :
    IsSemitermVec L n m w → subst L w (neg L p) = neg L (subst L w p) := by
  intro hw
  suffices H : ∀ d ≤ n, IsSemitermVec L n (m + d) (qVecIter L w d) →
      subst L (qVecIter L w d) (neg L p) = neg L (subst L (qVecIter L w d) p) by
    simpa using H 0 zero_le (by simpa using hw)
  have v3 := fun i : Fin 3 ↦ LocallyDelta0Function.var (V := V) i
  have hwd := qVecIter_var_locallyDelta0 (L := L) w (0 : Fin 3)
  have hmd := add_var_locallyDelta0 m (0 : Fin 3)
  refine IsSemiformula.depth_induction
    (Q := fun d n p ↦ IsSemitermVec L n (m + d) (qVecIter L w d) →
      subst L (qVecIter L w d) (neg L p) = neg L (subst L (qVecIter L w d) p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ hp
  · exact (isSemitermVec_locallyDelta0.comp₃ (v3 1) hmd hwd).imp <| LocallyDelta0.eq
      (subst_locallyDelta0.comp₂ hwd (neg_locallyDelta0.comp₁ (v3 2)))
      (neg_locallyDelta0.comp₁ (subst_locallyDelta0.comp₂ hwd (v3 2)))
  · intro d n k R v hR hv hw'
    rw [neg_rel hR hv.isUTerm, substs_nrel hR hv.isUTerm, substs_rel hR hv.isUTerm,
      neg_rel hR (hw'.termSubstVec hv).isUTerm]
  · intro d n k R v hR hv hw'
    rw [neg_nrel hR hv.isUTerm, substs_rel hR hv.isUTerm, substs_nrel hR hv.isUTerm,
      neg_nrel hR (hw'.termSubstVec hv).isUTerm]
  · intros; simp [*]
  · intros; simp [*]
  · intro d n p q hp hq ihp ihq hw'
    rw [neg_and hp.isUFormula hq.isUFormula,
      substs_or hp.neg.isUFormula hq.neg.isUFormula,
      substs_and hp.isUFormula hq.isUFormula,
      neg_and (hp.subst hw').isUFormula (hq.subst hw').isUFormula,
      ihp hw', ihq hw']
  · intro d n p q hp hq ihp ihq hw'
    rw [neg_or hp.isUFormula hq.isUFormula,
      substs_and hp.neg.isUFormula hq.neg.isUFormula,
      substs_or hp.isUFormula hq.isUFormula,
      neg_or (hp.subst hw').isUFormula (hq.subst hw').isUFormula,
      ihp hw', ihq hw']
  · intro d n p hp ih hw'
    have ih := ih hw'.qVecIter
    rw [← qVec_qVecIter] at ih
    rw [neg_all hp.isUFormula, substs_ex hp.neg.isUFormula,
      substs_all hp.isUFormula, neg_all (hp.subst hw'.qVec).isUFormula, ih]
  · intro d n p hp ih hw'
    have ih := ih hw'.qVecIter
    rw [← qVec_qVecIter] at ih
    rw [neg_ex hp.isUFormula, substs_all hp.neg.isUFormula,
      substs_ex hp.isUFormula, neg_ex (hp.subst hw'.qVec).isUFormula, ih]

lemma shift_substs {n m w p : V} (hp : IsSemiformula L n p) :
    IsSemitermVec L n m w → shift L (subst L w p) = subst L (termShiftVec L n w) (shift L p) := by
  intro hw
  suffices H : ∀ d ≤ n, IsSemitermVec L n (m + d) (qVecIter L w d) →
      shift L (subst L (qVecIter L w d) p) =
        subst L (termShiftVec L n (qVecIter L w d)) (shift L p) by
    simpa using H 0 zero_le (by simpa using hw)
  have v3 := fun i : Fin 3 ↦ LocallyDelta0Function.var (V := V) i
  have hwd := qVecIter_var_locallyDelta0 (L := L) w (0 : Fin 3)
  have hmd := add_var_locallyDelta0 m (0 : Fin 3)
  refine IsSemiformula.depth_induction
    (Q := fun d n p ↦ IsSemitermVec L n (m + d) (qVecIter L w d) →
      shift L (subst L (qVecIter L w d) p) =
        subst L (termShiftVec L n (qVecIter L w d)) (shift L p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · exact (isSemitermVec_locallyDelta0.comp₃ (v3 1) hmd hwd).imp <| LocallyDelta0.eq
      (shift_locallyDelta0.comp₁ (subst_locallyDelta0.comp₂ hwd (v3 2)))
      (subst_locallyDelta0.comp₂ (termShiftVec_locallyDelta0.comp₂ (v3 1) hwd)
        (shift_locallyDelta0.comp₁ (v3 2)))
  · intro d n k R v hR hv hw'
    rw [substs_rel hR hv.isUTerm,
      shift_rel hR (hw'.termSubstVec hv).isUTerm,
      shift_rel hR hv.isUTerm,
      substs_rel hR hv.termShiftVec.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw'.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw'.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi,
      termShift_termSubsts (hv.nth hi) hw']
  · intro d n k R v hR hv hw'
    rw [substs_nrel hR hv.isUTerm,
      shift_nrel hR (hw'.termSubstVec hv).isUTerm,
      shift_nrel hR hv.isUTerm,
      substs_nrel hR hv.termShiftVec.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw'.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw'.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi,
      termShift_termSubsts (hv.nth hi) hw']
  · intro d n hw'; simp
  · intro d n hw'; simp
  · intro d n p q hp hq ihp ihq hw'
    rw [substs_and hp.isUFormula hq.isUFormula,
      shift_and (hp.subst hw').isUFormula (hq.subst hw').isUFormula,
      shift_and hp.isUFormula hq.isUFormula,
      substs_and hp.shift.isUFormula hq.shift.isUFormula,
      ihp hw', ihq hw']
  · intro d n p q hp hq ihp ihq hw'
    rw [substs_or hp.isUFormula hq.isUFormula,
      shift_or (hp.subst hw').isUFormula (hq.subst hw').isUFormula,
      shift_or hp.isUFormula hq.isUFormula,
      substs_or hp.shift.isUFormula hq.shift.isUFormula,
      ihp hw', ihq hw']
  · intro d n p hp ih hw'
    have ih := ih hw'.qVecIter
    rw [← qVec_qVecIter] at ih
    rw [substs_all hp.isUFormula,
      shift_all (hp.subst hw'.qVec).isUFormula,
      shift_all hp.isUFormula,
      substs_all hp.shift.isUFormula,
      ih,
      termShift_qVec hw']
  · intro d n p hp ih hw'
    have ih := ih hw'.qVecIter
    rw [← qVec_qVecIter] at ih
    rw [substs_ex hp.isUFormula,
      shift_exs (hp.subst hw'.qVec).isUFormula,
      shift_exs hp.isUFormula,
      substs_ex hp.shift.isUFormula,
      ih,
      termShift_qVec hw']

lemma substs_substs {l n m w v p : V} (hp : IsSemiformula L l p) :
    IsSemitermVec L n m w → IsSemitermVec L l n v →
      subst L w (subst L v p) = subst L (termSubstVec L l w v) p := by
  intro hw hv
  suffices H : ∀ d ≤ l, IsSemitermVec L (n + d) (m + d) (qVecIter L w d) →
      IsSemitermVec L l (n + d) (qVecIter L v d) →
      subst L (qVecIter L w d) (subst L (qVecIter L v d) p) =
        subst L (termSubstVec L l (qVecIter L w d) (qVecIter L v d)) p by
    simpa using H 0 zero_le (by simpa using hw) (by simpa using hv)
  have v3 := fun i : Fin 3 ↦ LocallyDelta0Function.var (V := V) i
  have hwd := qVecIter_var_locallyDelta0 (L := L) w (0 : Fin 3)
  have hvd := qVecIter_var_locallyDelta0 (L := L) v (0 : Fin 3)
  have hnd := add_var_locallyDelta0 n (0 : Fin 3)
  have hmd := add_var_locallyDelta0 m (0 : Fin 3)
  refine IsSemiformula.depth_induction
    (Q := fun d l p ↦ IsSemitermVec L (n + d) (m + d) (qVecIter L w d) →
      IsSemitermVec L l (n + d) (qVecIter L v d) →
      subst L (qVecIter L w d) (subst L (qVecIter L v d) p) =
        subst L (termSubstVec L l (qVecIter L w d) (qVecIter L v d)) p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · exact (isSemitermVec_locallyDelta0.comp₃ hnd hmd hwd).imp <|
      (isSemitermVec_locallyDelta0.comp₃ (v3 1) hnd hvd).imp <| LocallyDelta0.eq
        (subst_locallyDelta0.comp₂ hwd (subst_locallyDelta0.comp₂ hvd (v3 2)))
        (subst_locallyDelta0.comp₂ (termSubstVec_locallyDelta0.comp₃ (v3 1) hwd hvd) (v3 2))
  · intro d l k R ts hR hts _ hv'
    rw [substs_rel hR hts.isUTerm,
      substs_rel hR (hv'.termSubstVec hts).isUTerm,
      substs_rel hR hts.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv'.termSubstVec hts).isUTerm])
        (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv'.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      termSubst_termSubst hv' (hts.nth hi)]
  · intro d l k R ts hR hts _ hv'
    rw [substs_nrel hR hts.isUTerm,
      substs_nrel hR (hv'.termSubstVec hts).isUTerm,
      substs_nrel hR hts.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv'.termSubstVec hts).isUTerm])
        (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv'.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      termSubst_termSubst hv' (hts.nth hi)]
  · intros; simp
  · intros; simp
  · intro d l p q hp hq ihp ihq hw' hv'
    rw [substs_and hp.isUFormula hq.isUFormula,
      substs_and (hp.subst hv').isUFormula (hq.subst hv').isUFormula,
      substs_and hp.isUFormula hq.isUFormula,
      ihp hw' hv', ihq hw' hv']
  · intro d l p q hp hq ihp ihq hw' hv'
    rw [substs_or hp.isUFormula hq.isUFormula,
      substs_or (hp.subst hv').isUFormula (hq.subst hv').isUFormula,
      substs_or hp.isUFormula hq.isUFormula,
      ihp hw' hv', ihq hw' hv']
  · intro d l p hp ih hw' hv'
    have ih := ih (by simpa only [add_assoc] using hw'.qVecIter) hv'.qVecIter
    simp only [← qVec_qVecIter] at ih
    rw [substs_all hp.isUFormula,
      substs_all (hp.subst hv'.qVec).isUFormula,
      substs_all hp.isUFormula,
      ih,
      termSubstVec_qVec_qVec hv' hw']
  · intro d l p hp ih hw' hv'
    have ih := ih (by simpa only [add_assoc] using hw'.qVecIter) hv'.qVecIter
    simp only [← qVec_qVecIter] at ih
    rw [substs_ex hp.isUFormula,
      substs_ex (hp.subst hv'.qVec).isUFormula,
      substs_ex hp.isUFormula,
      ih,
      termSubstVec_qVec_qVec hv' hw']

lemma nth_qVec_eq_bvar {n w : V} (hw : IsSemitermVec L n n w) (H : ∀ i < n, w.[i] = ^#i) :
    ∀ i < n + 1, (qVec L w).[i] = ^#i := by
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp [qVec]
  · have hi : i < n := by simpa using hi
    simp only [qVec, nth_adjoin_succ]
    rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by simp [hw.lh, hi])]
    simp [H i hi]

lemma subst_eq_self {n w p : V} (hp : IsSemiformula L n p) (hw : IsSemitermVec L n n w)
    (H : ∀ i < n, w.[i] = ^#i) :
    subst L w p = p := by
  suffices H' : ∀ d ≤ n, IsSemitermVec L n n (qVecIter L w d) →
      (∀ i < n, (qVecIter L w d).[i] = ^#i) → subst L (qVecIter L w d) p = p by
    simpa using H' 0 zero_le (by simpa using hw) (by simpa using H)
  have v3 := fun i : Fin 3 ↦ LocallyDelta0Function.var (V := V) i
  have v4 := fun i : Fin 4 ↦ LocallyDelta0Function.var (V := V) i
  have hwd := qVecIter_var_locallyDelta0 (L := L) w (0 : Fin 3)
  have hwd' : LocallyDelta0Function fun u : Fin 4 → V ↦ qVecIter L w (u 1) :=
    qVecIter_locallyDelta0.comp₂ (LocallyDelta0Function.const w) (v4 1)
  refine IsSemiformula.depth_induction
    (Q := fun d n p ↦ IsSemitermVec L n n (qVecIter L w d) →
      (∀ i < n, (qVecIter L w d).[i] = ^#i) → subst L (qVecIter L w d) p = p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · exact (isSemitermVec_locallyDelta0.comp₃ (v3 1) (v3 1) hwd).imp <|
      (LocallyDelta0.ball_lt_function (v3 1) (LocallyDelta0.eq
        (nth_locallyDelta0.comp₂ hwd' (v4 0))
        (qqBvar_locallyDelta0.comp₁ (v4 0)))).imp <| LocallyDelta0.eq
          (subst_locallyDelta0.comp₂ hwd (v3 2)) (v3 2)
  · intro d n k R v hR hv _ H'
    simp only [substs_rel, qqRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H']
  · intro d n k R v hR hv _ H'
    simp only [substs_nrel, qqNRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H']
  · intros; simp
  · intros; simp
  · intro d n p q hp hq ihp ihq hw' H'
    simp [hp.isUFormula, hq.isUFormula, ihp hw' H', ihq hw' H']
  · intro d n p q hp hq ihp ihq hw' H'
    simp [hp.isUFormula, hq.isUFormula, ihp hw' H', ihq hw' H']
  · intro d n p hp ih hw' H'
    have ih := ih (by rw [← qVec_qVecIter]; exact hw'.qVec)
      (by rw [← qVec_qVecIter]; exact nth_qVec_eq_bvar hw' H')
    rw [← qVec_qVecIter] at ih
    simp [hp.isUFormula, ih]
  · intro d n p hp ih hw' H'
    have ih := ih (by rw [← qVec_qVecIter]; exact hw'.qVec)
      (by rw [← qVec_qVecIter]; exact nth_qVec_eq_bvar hw' H')
    rw [← qVec_qVecIter] at ih
    simp [hp.isUFormula, ih]

end subst

variable (L)

noncomputable def substs1 (t u : V) : V := subst L ?[t] u

variable {L}

section substs1

section

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (substs1Graph)

instance substs1.defined : 𝚺ᴬ₁-Function₂[V] substs1 L via substs1Graph L :=
  .mk fun v ↦ by simp [substs1Graph]; rfl

instance substs1.definable : 𝚺ᴬ₁-Function₂[V] substs1 L := substs1.defined.to_definable

instance substs1.definable' (Γ m) : Γᴬ_[m + 1]-Function₂[V] substs1 L :=
  substs1.definable.of_sigmaOne

end

lemma substs1_locallyDelta0 : LocallyDelta0Function₂ (substs1 (V := V) L) :=
  subst_locallyDelta0.comp₂
    (LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 0)
      (LocallyDelta0Function.const 0))
    (LocallyDelta0Function.var 1)

lemma IsSemiformula.substs1 {n t p : V} (ht : IsSemiterm L n t) (hp : IsSemiformula L 1 p) :
    IsSemiformula L n (substs1 L t p) :=
  IsSemiformula.subst hp (by simp [ht])

lemma subst_imp {n m w p q : V} (hp : IsSemiformula L n p) (hq : IsSemiformula L n q)
    (hw : IsSemitermVec L n m w) : subst L w (imp L p q) = imp L (subst L w p) (subst L w q) := by
  simp [imp, hp.isUFormula, hq.isUFormula, substs_neg hp hw]

lemma substs1_subst_qVec {j w q t : V} (hw : IsSemitermVec L j 0 w)
    (hq : IsSemiformula L (j + 1) q) (ht : IsSemiterm L 0 t) :
    substs1 L t (subst L (qVec L w) q) = subst L (t ∷ w) q := by
  have h₁ : IsSemitermVec L 1 0 (?[t] : V) := by simp [ht]
  have h₂ : IsSemitermVec L (j + 1) 1 (qVec L w) := by simpa using hw.qVec
  rw [substs1, substs_substs hq h₁ h₂]
  congr 1
  apply nth_ext' (j + 1) (by simp [(h₁.termSubstVec h₂).lh]) (by simp [hw.lh])
  intro i hi
  rw [nth_termSubstVec h₂.isUTerm hi]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp [qVec]
  · have hi : i < j := by simpa using hi
    rw [qVec, nth_adjoin_succ, hw.lh, nth_termBShiftVec hw.isUTerm hi,
      substs_cons_bShift (hw.nth hi), substs_nil (hw.nth hi)]
    simp

end substs1

variable (L)

noncomputable def free (p : V) : V := substs1 L ^&0 (shift L p)

variable {L}

/-! ### free function -/

section free

section

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (freeGraph)

instance free.defined : 𝚺ᴬ₁-Function₁[V] free L via freeGraph L :=
  .mk fun v ↦ by simp [freeGraph, free]

instance free.definable : 𝚺ᴬ₁-Function₁[V] free L := free.defined.to_definable

instance free.definable' (Γ m) : Γᴬ_[m + 1]-Function₁[V] free L := free.definable.of_sigmaOne

end

lemma free_locallyDelta0 : LocallyDelta0Function₁ (free (V := V) L) :=
  substs1_locallyDelta0.comp₂ (LocallyDelta0Function.const _)
    (shift_locallyDelta0.comp₁ (LocallyDelta0Function.var 0))

@[simp] lemma IsSemiformula.free {p : V} (hp : IsSemiformula L 1 p) : IsFormula L (free L p) :=
  IsSemiformula.substs1 (by simp) hp.shift

end free

section free1

variable (L)

noncomputable def free1 (p : V) : V := subst L ?[^&0, ^#0] (shift L p)

variable {L}

@[simp] lemma IsSemiformula.free1 {p : V} (hp : IsSemiformula L 2 p) :
    IsSemiformula L 1 (free1 L p) :=
  IsSemiformula.subst (m := 1) hp.shift
      (SemitermVec.adjoin (SemitermVec.adjoin (IsSemitermVec.empty _) (by simp)) (by simp))

end free1

section complexity

namespace FormulaComplexity

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.FormulaComplexity (blueprint) in
/-- The recursion on formulas computing the depth of the nesting of connectives. -/
noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel _ _ _ _ := 0
  nrel _ _ _ _ := 0
  verum _ := 0
  falsum _ := 0
  and _ _ _ y₁ y₂ := max y₁ y₂ + 1
  or _ _ _ y₁ y₂ := max y₁ y₂ + 1
  all _ _ ys := ys.[0] + 1
  exs _ _ ys := ys.[0] + 1
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint, max_add_add_right]
  or_defined := .mk fun v ↦ by simp [blueprint, max_add_add_right]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  rel_locallyDelta0 := LocallyDelta0Function.const 0
  nrel_locallyDelta0 := LocallyDelta0Function.const 0
  verum_locallyDelta0 := LocallyDelta0Function.const 0
  falsum_locallyDelta0 := LocallyDelta0Function.const 0
  and_locallyDelta0 := LocallyDelta0Function.add_one <| LocallyDelta0Function.max.comp₂
    (LocallyDelta0Function.var 3) (LocallyDelta0Function.var 4)
  or_locallyDelta0 := LocallyDelta0Function.add_one <| LocallyDelta0Function.max.comp₂
    (LocallyDelta0Function.var 3) (LocallyDelta0Function.var 4)
  all_locallyDelta0 := LocallyDelta0Function.add_one <| nth_locallyDelta0.comp₂
    (LocallyDelta0Function.var 2) (LocallyDelta0Function.const 0)
  exs_locallyDelta0 := LocallyDelta0Function.add_one <| nth_locallyDelta0.comp₂
    (LocallyDelta0Function.var 2) (LocallyDelta0Function.const 0)
  bound _ p := p
  rel_le_bound _ _ _ _ := zero_le
  nrel_le_bound _ _ _ _ := zero_le
  verum_le_bound _ := zero_le
  falsum_le_bound _ := zero_le
  and_le_bound _ p₁ p₂ _ _ h₁ h₂ := succ_le_iff_lt.mpr <|
    max_lt (lt_of_le_of_lt h₁ (lt_K!_left p₁ p₂)) (lt_of_le_of_lt h₂ (lt_K!_right p₁ p₂))
  or_le_bound _ p₁ p₂ _ _ h₁ h₂ := succ_le_iff_lt.mpr <|
    max_lt (lt_of_le_of_lt h₁ (lt_or_left p₁ p₂)) (lt_of_le_of_lt h₂ (lt_or_right p₁ p₂))
  all_le_bound _ p₁ _ h := by
    simpa using succ_le_iff_lt.mpr (lt_of_le_of_lt h (lt_forall p₁))
  exs_le_bound _ p₁ _ h := by
    simpa using succ_le_iff_lt.mpr (lt_of_le_of_lt h (lt_exists p₁))
  bound_monotone _ _ _ h := h
  bound_locallyDelta0 := LocallyDelta0Function.var 1

end FormulaComplexity

open FormulaComplexity

variable (L)

/-- The depth of the nesting of connectives in the code `p` of a formula. -/
noncomputable def formulaComplexity (p : V) : V := construction.result L 0 p

variable {L}

section

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (formulaComplexityGraph)

instance formulaComplexity.defined :
    𝚺ᴬ₁-Function₁[V] formulaComplexity L via formulaComplexityGraph L := .mk fun v ↦ by
  simpa [formulaComplexityGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
      using! construction.result_defined.defined ![v 0, 0, v 1]

instance formulaComplexity.definable : 𝚺ᴬ₁-Function₁[V] formulaComplexity L :=
  formulaComplexity.defined.to_definable

instance formulaComplexity.definable' (Γ m) : Γᴬ_[m + 1]-Function₁[V] formulaComplexity L :=
  .of_sigmaOne formulaComplexity.definable

end

lemma formulaComplexity_locallyDelta0 : LocallyDelta0Function₁ (formulaComplexity (V := V) L) :=
  (construction.result_locallyDelta0 L).comp₂ (LocallyDelta0Function.const 0)
    (LocallyDelta0Function.var 0)

@[simp] lemma formulaComplexity_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    formulaComplexity L (^rel k R v) = 0 := by simp [formulaComplexity, hR, hv, construction]

@[simp] lemma formulaComplexity_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    formulaComplexity L (^nrel k R v) = 0 := by simp [formulaComplexity, hR, hv, construction]

@[simp] lemma formulaComplexity_verum :
    formulaComplexity L (^⊤ : V) = 0 := by simp [formulaComplexity, construction]

@[simp] lemma formulaComplexity_falsum :
    formulaComplexity L (^⊥ : V) = 0 := by simp [formulaComplexity, construction]

@[simp] lemma formulaComplexity_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    formulaComplexity L (p ^⋏ q) = max (formulaComplexity L p) (formulaComplexity L q) + 1 := by
  simp [formulaComplexity, hp, hq, construction]

@[simp] lemma formulaComplexity_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    formulaComplexity L (p ^⋎ q) = max (formulaComplexity L p) (formulaComplexity L q) + 1 := by
  simp [formulaComplexity, hp, hq, construction]

@[simp] lemma formulaComplexity_all {p : V} (hp : IsUFormula L p) :
    formulaComplexity L (^∀ p) = formulaComplexity L p + 1 := by
  simp [formulaComplexity, hp, construction]

@[simp] lemma formulaComplexity_ex {p : V} (hp : IsUFormula L p) :
    formulaComplexity L (^∃ p) = formulaComplexity L p + 1 := by
  simp [formulaComplexity, hp, construction]

@[simp] lemma formulaComplexity_neg {p : V} :
    IsUFormula L p → formulaComplexity L (neg L p) = formulaComplexity L p := by
  intro hp
  refine IsUFormula.induction
    (P := fun p ↦ formulaComplexity L (neg L p) = formulaComplexity L p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    p hp
  · exact LocallyDelta0.eq
      (formulaComplexity_locallyDelta0.comp₁
        (neg_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))))
      (formulaComplexity_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

@[simp] lemma formulaComplexity_shift {p : V} :
    IsUFormula L p → formulaComplexity L (shift L p) = formulaComplexity L p := by
  intro hp
  refine IsUFormula.induction
    (P := fun p ↦ formulaComplexity L (shift L p) = formulaComplexity L p) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ p hp
  · exact LocallyDelta0.eq
      (formulaComplexity_locallyDelta0.comp₁
        (shift_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))))
      (formulaComplexity_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

lemma fomulaComplexity_substs {n p : V} (hp : IsSemiformula L n p) {m w : V} :
    IsSemitermVec L n m w → formulaComplexity L (subst L w p) = formulaComplexity L p := by
  intro hw
  suffices H : ∀ d ≤ n, IsSemitermVec L n (m + d) (qVecIter L w d) →
      formulaComplexity L (subst L (qVecIter L w d) p) = formulaComplexity L p by
    simpa using H 0 zero_le (by simpa using hw)
  have v3 := fun i : Fin 3 ↦ LocallyDelta0Function.var (V := V) i
  have hwd := qVecIter_var_locallyDelta0 (L := L) w (0 : Fin 3)
  have hmd := add_var_locallyDelta0 m (0 : Fin 3)
  refine IsSemiformula.depth_induction
    (Q := fun d n p ↦ IsSemitermVec L n (m + d) (qVecIter L w d) →
      formulaComplexity L (subst L (qVecIter L w d) p) = formulaComplexity L p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · exact (isSemitermVec_locallyDelta0.comp₃ (v3 1) hmd hwd).imp <| LocallyDelta0.eq
      (formulaComplexity_locallyDelta0.comp₁ (subst_locallyDelta0.comp₂ hwd (v3 2)))
      (formulaComplexity_locallyDelta0.comp₁ (v3 2))
  · intro d n k R v hR hv hw'
    rw [formulaComplexity_rel hR hv.isUTerm, substs_rel hR hv.isUTerm,
        formulaComplexity_rel hR (hw'.termSubstVec hv).isUTerm]
  · intro d n k R v hR hv hw'
    rw [formulaComplexity_nrel hR hv.isUTerm, substs_nrel hR hv.isUTerm,
        formulaComplexity_nrel hR (hw'.termSubstVec hv).isUTerm]
  · intro d n hw'
    rw [substs_verum]
  · intro d n hw'
    rw [substs_falsum]
  · intro d n p q hp hq ihp ihq hw'
    rw [substs_and hp.isUFormula hq.isUFormula,
      formulaComplexity_and (hp.subst hw').isUFormula (hq.subst hw').isUFormula,
      ihp hw', ihq hw',
      formulaComplexity_and hp.isUFormula hq.isUFormula]
  · intro d n p q hp hq ihp ihq hw'
    rw [substs_or hp.isUFormula hq.isUFormula,
      formulaComplexity_or (hp.subst hw').isUFormula (hq.subst hw').isUFormula,
      ihp hw', ihq hw',
      formulaComplexity_or hp.isUFormula hq.isUFormula]
  · intro d n p hp ih hw'
    have ih := ih hw'.qVecIter
    rw [← qVec_qVecIter] at ih
    rw [substs_all hp.isUFormula,
     formulaComplexity_all (hp.subst hw'.qVec).isUFormula,
     ih,
     formulaComplexity_all hp.isUFormula]
  · intro d n p hp ih hw'
    have ih := ih hw'.qVecIter
    rw [← qVec_qVecIter] at ih
    rw [substs_ex hp.isUFormula,
     formulaComplexity_ex (hp.subst hw'.qVec).isUFormula,
     ih,
     formulaComplexity_ex hp.isUFormula]

lemma fomulaComplexity_substs1 {p : V} (hp : IsSemiformula L 1 p) {m t : V}
    (ht : IsSemiterm L m t) :
    formulaComplexity L (substs1 L t p) = formulaComplexity L p := by
  unfold substs1
  rw [fomulaComplexity_substs hp (IsSemitermVec.singleton.mpr ht)]

lemma fomulaComplexity_free {p : V} (hp : IsSemiformula L 1 p) :
    formulaComplexity L (free L p) = formulaComplexity L p := by
  unfold free
  have : IsSemiterm (V := V) L 0 ^&0 := by simp
  rw [fomulaComplexity_substs1 hp.shift this,
    formulaComplexity_shift hp.isUFormula]

end complexity

@[simp] lemma lt_max_succ_left (a b : V) : a < max a b + 1 := lt_succ_iff_le.mpr <| by simp

@[simp] lemma lt_max_succ_right (a b : V) : b < max a b + 1 := lt_succ_iff_le.mpr <| by simp

namespace Arithmetic

-- `Arithmetic` is intentionally re-opened here even though the ambient namespace
-- already contains it, keeping the names of Foundation's `Bootstrapping.Arithmetic.*`.
set_option linter.dupNamespace false

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic (eqIndex ltIndex)

noncomputable def qqEQ (x y : V) : V := ^rel 2 (eqIndex : V) ?[x, y]

noncomputable def qqNEQ (x y : V) : V := ^nrel 2 (eqIndex : V) ?[x, y]

noncomputable def qqLT (x y : V) : V := ^rel 2 (ltIndex : V) ?[x, y]

noncomputable def qqNLT (x y : V) : V := ^nrel 2 (ltIndex : V) ?[x, y]

notation:75 x:75 " ^= " y:76 => qqEQ x y

notation:75 x:75 " ^≠ " y:76 => qqNEQ x y

notation:78 x:78 " ^< " y:79 => qqLT x y

notation:78 x:78 " ^≮ " y:79 => qqNLT x y

@[simp] lemma lt_qqEQ_left (x y : V) : x < x ^= y := by
  simpa using! nth_lt_qqRel_of_lt (i := 0) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqEQ_right (x y : V) : y < x ^= y := by
  simpa using! nth_lt_qqRel_of_lt (i := 1) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqLT_left (x y : V) : x < x ^< y := by
  simpa using! nth_lt_qqRel_of_lt (i := 0) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqLT_right (x y : V) : y < x ^< y := by
  simpa using! nth_lt_qqRel_of_lt (i := 1) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNEQ_left (x y : V) : x < x ^≠ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 0) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNEQ_right (x y : V) : y < x ^≠ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 1) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNLT_left (x y : V) : x < x ^≮ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 0) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNLT_right (x y : V) : y < x ^≮ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 1) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

instance qqEQ_defined : 𝚺ᴬ₁-Function₂ (qqEQ : V → V → V) via qqEQDef :=
  .mk fun v ↦ by simp [qqEQDef, numeral_eq_natCast, qqEQ]

instance qqNEQ_defined : 𝚺ᴬ₁-Function₂ (qqNEQ : V → V → V) via qqNEQDef :=
  .mk fun v ↦ by simp [qqNEQDef, numeral_eq_natCast, qqNEQ]

instance qqLT_defined : 𝚺ᴬ₁-Function₂ (qqLT : V → V → V) via qqLTDef :=
  .mk fun v ↦ by simp [qqLTDef, numeral_eq_natCast, qqLT]

instance qqNLT_defined : 𝚺ᴬ₁-Function₂ (qqNLT : V → V → V) via qqNLTDef :=
  .mk fun v ↦ by simp [qqNLTDef, numeral_eq_natCast, qqNLT]

instance (Γ m) : Γᴬ_[m + 1]-Function₂ (qqEQ : V → V → V) := .of_sigmaOne qqEQ_defined.to_definable

instance (Γ m) : Γᴬ_[m + 1]-Function₂ (qqNEQ : V → V → V) := .of_sigmaOne qqNEQ_defined.to_definable

instance (Γ m) : Γᴬ_[m + 1]-Function₂ (qqLT : V → V → V) := .of_sigmaOne qqLT_defined.to_definable

instance (Γ m) : Γᴬ_[m + 1]-Function₂ (qqNLT : V → V → V) := .of_sigmaOne qqNLT_defined.to_definable

lemma neg_eq {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^= u) = t ^≠ u := by
  simp only [qqEQ, qqNEQ]
  rw [neg_rel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_neq {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^≠ u) = t ^= u := by
  simp only [qqNEQ, qqEQ]
  rw [neg_nrel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_lt {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^< u) = t ^≮ u := by
  simp only [qqLT, qqNLT]
  rw [neg_rel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_nlt {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^≮ u) = t ^< u := by
  simp only [qqNLT, qqLT]
  rw [neg_nrel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

end Arithmetic

/-! ### Bounded universal quantifier -/

section qqBall

/-- `qqBall u q = ^∀ ((^#0 ^≮ u) ^⋎ q)`, the code of `∀¹[“#0 < u”] q`. -/
noncomputable def qqBall (u q : V) : V := qqAll (qqOr (Arithmetic.qqNLT (qqBvar 0) u) q)

@[simp] lemma lt_q_qqBall (u q : V) : q < qqBall u q :=
  lt_trans (lt_or_right _ _) (lt_forall _)

@[simp] lemma lt_u_qqBall (u q : V) : u < qqBall u q :=
  lt_trans (Arithmetic.lt_qqNLT_right _ _) (lt_trans (lt_or_left _ _) (lt_forall _))

instance qqBall_defined :
    𝚺ᴬ₁-Function₂ (qqBall : V → V → V) via qqBallDef := .mk fun v ↦ by
  simp [qqBallDef, qqBall, (Arithmetic.qqNLT_defined (V := V)).df]

instance qqBall_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (qqBall : V → V → V) :=
  .of_sigmaOne qqBall_defined.to_definable

end qqBall

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
