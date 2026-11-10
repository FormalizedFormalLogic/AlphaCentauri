module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.Bootstrapping.Syntax.Formula.Functions
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Iteration

/-!
# Iterated connectives and quantifiers in models of $\mathsf{EA}$

The part of `Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Formula/Iteration.lean` on the
iterated universal quantifier `qqAlls`, ported to models of $\mathsf{EA}$. The blueprint and the
formula `qqAllsDef` are Foundation's; the recursion carries a bound on its values, and inductions
are on locally $\Delta_0$ predicates.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ### Iterated universal quantifier -/

section qqAlls

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.qqAlls (blueprint)

lemma qqAlls.bound_locallyDelta0 : LocallyDelta0Function fun v : Fin (1 + 1) → V ↦
    Exp.exp (Exp.exp (v 1 + v 0 + v 0 + 2)) + 1 :=
  LocallyDelta0Function.add_one <|
    LocallyDelta0Function.exp.comp₁ <| LocallyDelta0Function.exp.comp₁ <|
      LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.add.comp₂
        (LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.var 1)
          (LocallyDelta0Function.var 0)) (LocallyDelta0Function.var 0))
        (LocallyDelta0Function.const 2)

noncomputable def qqAlls.construction : PR.Construction V blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ ^∀ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, qqAll]
  zero_locallyDelta0 := LocallyDelta0Function.var 0
  succ_locallyDelta0 := qqAll_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)
  bound p k := Exp.exp (Exp.exp (p 0 + k + k + 2)) + 1
  bound_monotone _ _ _ h :=
    add_le_add (exp_monotone_le.mpr (exp_monotone_le.mpr
      (add_le_add (add_le_add (add_le_add le_rfl h) h) le_rfl))) le_rfl
  bound_locallyDelta0 := qqAlls.bound_locallyDelta0
  inv_locallyDelta0 := PR.lt_bound_locallyDelta0
    (bound := fun (p : Fin 1 → V) k ↦ Exp.exp (Exp.exp (p 0 + k + k + 2)) + 1)
    qqAlls.bound_locallyDelta0
  zero_lt_bound p := lt_succ_iff_le.mpr (le_exp_exp (by simp))
  succ_lt_bound p i z h := by
    beta_reduce at h ⊢
    have hn : (2 : V) ≤ p 0 + i + i + 2 := le_add_self
    have h6 : (6 : V) ≤ Exp.exp (Exp.exp (p 0 + i + i + 2)) :=
      le_trans (by exact_mod_cast (by norm_num : (6 : ℕ) ≤ 7)) (seven_le_exp_exp hn)
    have := adjoin_le_exp_exp (le_trans one_le_two hn) h6 (lt_succ_iff_le.mp h)
    rw [show p 0 + (i + 1) + (i + 1) + 2 = p 0 + i + i + 2 + 2 by grind]
    exact lt_succ_iff_le.mpr this

/-- `qqAlls p k = ^∀ ^∀ ... ^∀ p` (`k` universal quantifiers). -/
noncomputable def qqAlls (p k : V) : V := qqAlls.construction.result ![p] k

@[simp] lemma qqAlls_zero (p : V) : qqAlls p 0 = p := by simp [qqAlls, qqAlls.construction]

@[simp] lemma qqAlls_succ (p k : V) : qqAlls p (k + 1) = ^∀ (qqAlls p k) := by
  simp [qqAlls, qqAlls.construction]

set_option linter.flexible false in
instance qqAlls_defined : 𝚺ᴬ₁-Function₂ (qqAlls : V → V → V) via qqAllsDef := .mk
  fun v ↦ by
    simp [qqAlls.construction.result_defined_iff, qqAllsDef, qqAlls]
    rw [show (![v 1] : Fin 1 → V) = fun _ ↦ v 1 from funext fun j ↦ by
      rw [Fin.fin_one_eq_zero j]; rfl]

instance qqAlls_definable : 𝚺ᴬ₁-Function₂ (qqAlls : V → V → V) :=
  qqAlls_defined.to_definable

instance qqAlls_definable' {Γ : Polarity} {m : ℕ} :
    Γᴬ_[m + 1]-Function₂ (qqAlls : V → V → V) := qqAlls_definable.of_sigmaOne

lemma qqAlls_locallyDelta0 : LocallyDelta0Function₂ (qqAlls : V → V → V) := by
  have := (qqAlls.construction (V := V)).result_locallyDelta0.retraction (![1, 0] : Fin 2 → Fin 2)
  convert this using 3
  simp only [qqAlls]
  congr 1
  exact funext fun j ↦ by rw [Fin.fin_one_eq_zero j]; rfl

lemma le_qqAll (p : V) : p ≤ ^∀ p := by
  simp only [qqAll]; exact le_trans (le_pair_right _ _) le_self_add

lemma qqAlls_all (p k : V) : qqAlls (^∀ p) k = ^∀ (qqAlls p k) := by
  have hP : LocallyDelta0Pred fun k : V ↦ qqAlls (^∀ p) k = ^∀ (qqAlls p k) :=
    LocallyDelta0.eq (qqAlls_locallyDelta0.comp₂
      (qqAll_locallyDelta0.comp₁ (LocallyDelta0Function.const p)) (LocallyDelta0Function.var 0))
      (qqAll_locallyDelta0.comp₁ (qqAlls_locallyDelta0.comp₂ (LocallyDelta0Function.const p)
        (LocallyDelta0Function.var 0)))
  apply LocallyDelta0Pred.succ_induction hP
  · simp
  · intro k ih
    rw [qqAlls_succ, ih, qqAlls_succ]

lemma qqAlls_succ' (p k : V) : qqAlls p (k + 1) = qqAlls (^∀ p) k := by
  rw [qqAlls_succ, qqAlls_all]

@[simp]
lemma le_qqAlls (p k : V) : p ≤ qqAlls p k := by
  have hP : LocallyDelta0Pred fun k : V ↦ p ≤ qqAlls p k :=
    LocallyDelta0.le (LocallyDelta0Function.const p) (qqAlls_locallyDelta0.comp₂
      (LocallyDelta0Function.const p) (LocallyDelta0Function.var 0))
  apply LocallyDelta0Pred.succ_induction hP
  · simp
  · intro k ih
    rw [qqAlls_succ]
    exact ih.trans (le_qqAll _)

lemma succ_le_qqAll (p : V) : p + 1 ≤ ^∀ p := by
  simp only [qqAll]; exact add_le_add (le_pair_right _ _) (le_refl 1)

@[simp] lemma index_le_qqAlls (p k : V) : k ≤ qqAlls p k := by
  have hP : LocallyDelta0Pred fun k : V ↦ k ≤ qqAlls p k :=
    LocallyDelta0.le (LocallyDelta0Function.var 0) (qqAlls_locallyDelta0.comp₂
      (LocallyDelta0Function.const p) (LocallyDelta0Function.var 0))
  apply LocallyDelta0Pred.succ_induction hP
  · simp
  · intro k ih
    rw [qqAlls_succ]
    exact le_trans (add_le_add ih (le_refl 1)) (succ_le_qqAll _)

@[simp] lemma isUFormula_qqAlls {p k : V} : IsUFormula L (qqAlls p k) ↔ IsUFormula L p := by
  have hP : LocallyDelta0Pred fun k : V ↦ IsUFormula L (qqAlls p k) ↔ IsUFormula L p :=
    ((isUFormula_locallyDelta0 (L := L)).pred_comp (qqAlls_locallyDelta0.comp₂
      (LocallyDelta0Function.const p) (LocallyDelta0Function.var 0))).iff
      ((isUFormula_locallyDelta0 (L := L)).pred_comp (LocallyDelta0Function.const p))
  revert k
  apply LocallyDelta0Pred.succ_induction hP
  · simp
  · intro k ih
    rw [qqAlls_succ, IsUFormula.all, ih]

lemma bv_qqAlls {p k : V} (hp : IsUFormula L p) : bv L (qqAlls p k) = bv L p - k := by
  have hsub : LocallyDelta0 fun y : Fin 3 → V ↦ y 0 = y 1 - y 2 :=
    LocallyDelta0.of_definable (by definability)
  have hP : LocallyDelta0Pred fun k : V ↦ bv L (qqAlls p k) = bv L p - k :=
    (hsub.comp₃ ((bv_locallyDelta0 (L := L)).comp₁ (qqAlls_locallyDelta0.comp₂
      (LocallyDelta0Function.const p) (LocallyDelta0Function.var 0)))
      ((bv_locallyDelta0 (L := L)).comp₁ (LocallyDelta0Function.const p))
      (LocallyDelta0Function.var 0)).of_iff fun w ↦ by simp
  revert k
  apply LocallyDelta0Pred.succ_induction hP
  · simp
  · intro k ih
    rw [qqAlls_succ, bv_all (isUFormula_qqAlls.mpr hp), ih, Arithmetic.sub_sub]

lemma IsSemiformula.qqAlls {n k p : V} (h : IsSemiformula L (n + k) p) :
    IsSemiformula L n (qqAlls p k) := by
  rw [isSemiformula_iff] at h ⊢
  obtain ⟨hu, hbv⟩ := h
  exact ⟨isUFormula_qqAlls.mpr hu, by rwa [bv_qqAlls hu, tsub_le_iff_right]⟩

end qqAlls

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
