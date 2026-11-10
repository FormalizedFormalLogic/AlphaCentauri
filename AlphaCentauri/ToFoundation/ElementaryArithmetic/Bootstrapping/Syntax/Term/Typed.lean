module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping.Syntax.Formula.Basic
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Typed

/-!
# Typed terms in models of $\mathsf{EA}$

The part of `Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Typed.lean` on the
internal free-variable vector `fvarVec`, ported to models of $\mathsf{EA}$. The blueprint and the
formula `fvarVecDef` are Foundation's; the values of the recursion are not bounded below a
fixed bound, so the recursion carries the invariant that the value is the list of the first free
variables.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

/-! ## Internal free-variable vector `fvarVec` -/

section fvarVec

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.fvarVec (blueprint)

/-- `^&` is monotone. -/
lemma qqFvar_le_qqFvar {i j : V} (h : i ≤ j) : ^&i ≤ ^&j := by
  simpa [qqFvar] using pair_le_pair_right 1 h

/-- The list `⟨^&0, …, ^&(k-1)⟩` as a mapping over `[0, …, k - 1]`. -/
noncomputable def fvarVecClosed (k : V) : V := listMap (fun _ i ↦ ^&i) ![] (rangeList k)

lemma fvarVecFun_locallyDelta0 : LocallyDelta0Function fun w : Fin (0 + 1) → V ↦
    (fun (_ : Fin 0 → V) i ↦ ^&i) (w ·.succ) (w 0) :=
  qqFvar_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)

lemma len_fvarVecClosed (k : V) : len (fvarVecClosed k) = k := by
  rw [fvarVecClosed, len_listMap fvarVecFun_locallyDelta0, len_rangeList]

lemma nth_fvarVecClosed {k i : V} (hi : i < k) : (fvarVecClosed k).[i] = ^&i := by
  rw [fvarVecClosed, nth_listMap fvarVecFun_locallyDelta0 _ _ (by simpa using hi),
    nth_rangeList hi]

lemma fvarVecClosed_locallyDelta0 : LocallyDelta0Function₁ (fvarVecClosed : V → V) := by
  have := (listMap_locallyDelta0 (g := fun _ i ↦ ^&i) fvarVecFun_locallyDelta0).comp_cons
    (rangeList_locallyDelta0.comp₁ (LocallyDelta0Function.var 0))
    (u := (![] : Fin 0 → (Fin 1 → V) → V)) finZeroElim
  convert this using 2 with w
  simp only [fvarVecClosed]
  congr 1
  exact funext finZeroElim

lemma fvarVecClosed_zero : fvarVecClosed (0 : V) = 0 := by
  apply nth_ext (by simp [len_fvarVecClosed])
  intro i hi
  simp [len_fvarVecClosed] at hi

lemma concat_fvarVecClosed (k : V) :
    concat (fvarVecClosed k) (^&k) = fvarVecClosed (k + 1) := by
  apply nth_ext (by simp [len_fvarVecClosed])
  intro i hi
  rw [len_concat, len_fvarVecClosed] at hi
  rcases (lt_succ_iff_le.mp hi).lt_or_eq with hlt | rfl
  · rw [concat_nth_lt _ _ (by rwa [len_fvarVecClosed]), nth_fvarVecClosed hlt,
      nth_fvarVecClosed hi]
  · rw [concat_nth_len' _ _ (len_fvarVecClosed _), nth_fvarVecClosed hi]

lemma fvarVecClosed_le (k : V) :
    fvarVecClosed k ≤ Exp.exp (Exp.exp (k + k + ^&k + 3)) := by
  have := le_exp_exp_of_nth_le (B := ^&k) (fvarVecClosed k) fun i hi ↦ by
    rw [len_fvarVecClosed] at hi
    rw [nth_fvarVecClosed hi]
    exact qqFvar_le_qqFvar hi.le
  simpa [len_fvarVecClosed] using this

lemma fvarVecBound_locallyDelta0 :
    LocallyDelta0Function fun v : Fin (0 + 1) → V ↦
      Exp.exp (Exp.exp (v 0 + v 0 + ^&(v 0) + 3)) + 1 :=
  LocallyDelta0Function.add_one <|
    LocallyDelta0Function.exp.comp₁ <| LocallyDelta0Function.exp.comp₁ <|
      LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.add.comp₂
        (LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.var 0)
          (LocallyDelta0Function.var 0))
        (qqFvar_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)))
        (LocallyDelta0Function.const 3)

noncomputable def fvarVec.construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun _ n ih ↦ concat ih (^&n)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]
  zero_locallyDelta0 := LocallyDelta0Function.const 0
  succ_locallyDelta0 := concat_locallyDelta0.comp₂ (LocallyDelta0Function.var 0)
    (qqFvar_locallyDelta0.comp₁ (LocallyDelta0Function.var 1))
  bound _ i := Exp.exp (Exp.exp (i + i + ^&i + 3)) + 1
  bound_monotone _ _ _ h :=
    add_le_add (exp_monotone_le.mpr (exp_monotone_le.mpr
      (add_le_add (add_le_add (add_le_add h h) (qqFvar_le_qqFvar h)) le_rfl))) le_rfl
  bound_locallyDelta0 := fvarVecBound_locallyDelta0
  inv _ i z := z = fvarVecClosed i
  inv_locallyDelta0 := LocallyDelta0.eq (LocallyDelta0Function.var (V := V) 0)
    (fvarVecClosed_locallyDelta0.comp₁ (LocallyDelta0Function.var 1))
  lt_bound_of_inv _ i z h := lt_succ_iff_le.mpr (h ▸ fvarVecClosed_le i)
  zero_lt_bound _ := fvarVecClosed_zero.symm
  succ_lt_bound _ i z h := by
    rw [h, concat_fvarVecClosed]

/-- `fvarVec k = ⟨^&0, …, ^&(k-1)⟩`. -/
noncomputable def fvarVec (k : V) : V := fvarVec.construction.result ![] k

@[simp] lemma fvarVec_zero : fvarVec (0 : V) = 0 := by simp [fvarVec, fvarVec.construction]

@[simp] lemma fvarVec_succ (k : V) : fvarVec (k + 1) = concat (fvarVec k) (^&k) := by
  simp [fvarVec, fvarVec.construction]

instance fvarVec_defined : 𝚺ᴬ₁-Function₁ (fvarVec : V → V) via fvarVecDef := .mk
  fun v ↦ by simp [fvarVec.construction.result_defined_iff, fvarVecDef]; rfl

instance fvarVec_definable : 𝚺ᴬ₁-Function₁ (fvarVec : V → V) :=
  fvarVec_defined.to_definable

instance fvarVec_definable' {Γ : Polarity} {m : ℕ} :
    Γᴬ_[m + 1]-Function₁ (fvarVec : V → V) := fvarVec_definable.of_sigmaOne

lemma fvarVec_locallyDelta0 : LocallyDelta0Function₁ (fvarVec : V → V) := by
  convert fvarVec.construction.result_locallyDelta0 (V := V) using 3
  simp [fvarVec, Matrix.empty_eq]

@[simp] lemma len_fvarVec (k : V) : len (fvarVec k) = k := by
  have hP : LocallyDelta0Pred fun k : V ↦ len (fvarVec k) = k :=
    LocallyDelta0.eq (len_locallyDelta0.comp₁ (fvarVec_locallyDelta0.comp₁
      (LocallyDelta0Function.var (0 : Fin 1)))) (LocallyDelta0Function.var 0)
  apply LocallyDelta0Pred.succ_induction hP
  · simp
  · intro k ih
    simp [ih]

lemma nth_fvarVec (k : V) : ∀ i < k, (fvarVec k).[i] = ^&i := by
  have hR : LocallyDelta0 fun w : Fin 2 → V ↦ w 0 < w 1 → (fvarVec (w 1)).[w 0] = ^&(w 0) :=
    (LocallyDelta0.lt (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 1)).imp
      (LocallyDelta0.eq (nth_locallyDelta0.comp₂ (fvarVec_locallyDelta0.comp₁
        (LocallyDelta0Function.var 1)) (LocallyDelta0Function.var 0))
        (qqFvar_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)))
  have hP : LocallyDelta0Pred fun k : V ↦ ∀ i < k, (fvarVec k).[i] = ^&i :=
    (LocallyDelta0.ball_lt_function (LocallyDelta0Function.var (0 : Fin 1))
      hR).of_iff fun w ↦ by simp
  apply LocallyDelta0Pred.succ_induction hP
  · simp
  · intro k ih i hi
    rcases (lt_succ_iff_le.mp hi).lt_or_eq with hlt | rfl
    · rw [fvarVec_succ, concat_nth_lt _ _ (by simpa using hlt)]; exact ih i hlt
    · rw [fvarVec_succ, concat_nth_len' _ _ (by simp)]

end fvarVec

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
