module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.HFS.PRF

/-!
# Course-of-values recursion in models of $\mathsf{EA}$

A function `r` on a model of $\mathsf{EA}$ given by `r n = F n T`, where `T` is the sequence
`⟪0, r 0⟫, …, ⟪n - 1, r (n - 1)⟫` of the earlier values, for a locally $\Delta_0$ function `F`.
The construction carries a monotone locally $\Delta_0$ bound, and `r n` is the value clipped by the
bound at `n`; when `F n T` stays below the bound, `r n = F n T`. The table is built by bounded
primitive recursion, and `r` is locally $\Delta_0$.

- [HP98, §V.3]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

section functions

lemma LocallyDelta0Function.min : LocallyDelta0Function₂ (min : V → V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, by definability⟩

lemma LocallyDelta0Function.pairing : LocallyDelta0Function₂ (fun x y : V ↦ ⟪x, y⟫) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, by definability⟩

lemma LocallyDelta0Function.insert : LocallyDelta0Function₂ (insert : V → V → V) where
  graph := LocallyDelta0.of_definable insert_definable
  bounded X := by
    use X + Exp.exp X
    intro w hw
    exact insert_le_of_le_of_le (hw 0) (hw 1)

lemma znth_le (s i : V) : znth s i ≤ s := by
  by_cases h : Seq s ∧ i < lh s
  · obtain ⟨y, hy⟩ := h.1.exists h.2
    rw [h.1.znth_eq_of_mem hy]
    exact (lt_of_mem_rng hy).le
  · rw [znth_prop_not ((not_and_or.mp h).imp_right not_lt.mp)]
    simp

lemma LocallyDelta0Function.znth : LocallyDelta0Function₂ (znth : V → V → V) where
  graph := LocallyDelta0.of_definable znth_definable
  bounded X := by
    use X
    intro w hw
    exact le_trans (znth_le _ _) (hw 0)

lemma Seq.znth_of_lt {s i : V} (h : Seq s) (hi : i < lh s) : ⟪i, znth s i⟫ ∈ s := by
  obtain ⟨y, hy⟩ := h.exists hi
  rwa [h.znth_eq_of_mem hy]

lemma Seq.znth_seqCons_of_lt {s x i : V} (h : Seq s) (hi : i < lh s) :
    znth (s ⁀' x) i = znth s i :=
  (h.seqCons x).znth_eq_of_mem <| (Seq.mem_seqCons_iff_of_lt hi).mpr (h.znth_of_lt hi)

lemma Seq.znth_seqCons_lh {s x : V} (h : Seq s) : znth (s ⁀' x) (lh s) = x :=
  (h.seqCons x).znth_eq_of_mem (Seq.mem_seqCons s x)

end functions

namespace CourseOfValues

variable (V)

/-- A course-of-values recursion `r n = val v n T` with a monotone bound on its values, where `T`
is the sequence of the values below `n`. -/
structure Construction (k : ℕ) where
  /-- `c.val v n T` is the value at `n`, where `T` is the sequence of the values below `n`. -/
  val : (Fin k → V) → V → V → V
  val_locallyDelta0 :
    LocallyDelta0Function fun w : Fin (k + 2) → V ↦ val (w ·.succ.succ) (w 1) (w 0)
  /-- `c.bound v n` bounds the value at `n`. -/
  bound : (Fin k → V) → V → V
  bound_monotone : ∀ v {m n}, m ≤ n → bound v m ≤ bound v n
  bound_locallyDelta0 : LocallyDelta0Function fun w : Fin (k + 1) → V ↦ bound (w ·.succ) (w 0)

variable {V}

namespace Construction

variable {k : ℕ} (c : Construction V k) (v : Fin k → V)

/-- The value at `n` clipped by the bound. -/
noncomputable def clippedVal (n T : V) : V := min (c.val v n T) (c.bound v n)

lemma bound_succ_locallyDelta0 :
    LocallyDelta0Function fun w : Fin (k + 1) → V ↦
      Exp.exp ⟪w 0, c.bound (w ·.succ) (w 0) + 1⟫ :=
  LocallyDelta0Function.exp.comp₁ <| LocallyDelta0Function.pairing.comp₂
    (LocallyDelta0Function.var 0) (LocallyDelta0Function.add_one c.bound_locallyDelta0)

/-- The recursion building the table of values. -/
noncomputable def recursion : PR.Recursion V k where
  zero _ := ∅
  succ v n T := insert ⟪n, c.clippedVal v n T⟫ T
  zero_locallyDelta0 := LocallyDelta0Function.const ∅
  succ_locallyDelta0 := by
    have hval : LocallyDelta0Function fun w : Fin (k + 2) → V ↦
        c.clippedVal (w ·.succ.succ) (w 1) (w 0) := by
      simpa [clippedVal] using LocallyDelta0Function.min.comp₂ c.val_locallyDelta0
        (by simpa using c.bound_locallyDelta0.retraction Fin.succ)
    exact LocallyDelta0Function.insert.comp₂
      (LocallyDelta0Function.pairing.comp₂ (LocallyDelta0Function.var 1) hval)
      (LocallyDelta0Function.var 0)
  bound v n := Exp.exp ⟪n, c.bound v n + 1⟫
  zero_lt_bound _ := by simp [emptyset_def]
  succ_lt_bound v n T hT := by
    apply lt_exp_iff.mpr
    intro j hj
    have hK : ⟪n, c.bound v n + 1⟫ ≤ ⟪n + 1, c.bound v (n + 1) + 1⟫ :=
      pair_le_pair (by simp) (by simpa using c.bound_monotone v (show n ≤ n + 1 by simp))
    rcases mem_bitInsert_iff.mp hj with (rfl | hj)
    · apply lt_of_lt_of_le _ hK
      exact pair_lt_pair_right _ (lt_succ_iff_le.mpr (min_le_right _ _))
    · exact lt_of_lt_of_le (lt_exp_iff.mp hT j hj) hK
  bound_monotone v {m n} h :=
    exp_monotone_le.mpr <| pair_le_pair h (by simpa using c.bound_monotone v h)
  bound_locallyDelta0 := c.bound_succ_locallyDelta0

/-- The table `⟪0, r 0⟫, …, ⟪n - 1, r (n - 1)⟫` of the values below `n`. -/
noncomputable def table (n : V) : V := c.recursion.result v n

/-- The value of the recursion at `n`. -/
noncomputable def result (n : V) : V := znth (c.table v (n + 1)) n

variable {v}

@[simp] lemma table_zero : c.table v 0 = ∅ := c.recursion.result_zero v

lemma table_succ (n : V) :
    c.table v (n + 1) = insert ⟪n, c.clippedVal v n (c.table v n)⟫ (c.table v n) :=
  c.recursion.result_succ v n

lemma table_locallyDelta0 :
    LocallyDelta0Function fun w : Fin (k + 1) → V ↦ c.table (w ·.succ) (w 0) :=
  c.recursion.result_locallyDelta0

private lemma table_comp {n : ℕ} {f : (Fin n → V) → V} (hf : LocallyDelta0Function f) :
    LocallyDelta0Function fun w : Fin n → V ↦ c.table v (f w) := by
  simpa using c.table_locallyDelta0.comp_cons hf fun j ↦ LocallyDelta0Function.const (v j)

lemma table_seq (n : V) : Seq (c.table v n) ∧ lh (c.table v n) = n := by
  have hP : LocallyDelta0Pred fun n ↦ Seq (c.table v n) ∧ lh (c.table v n) = n := by
    have := (LocallyDelta0.of_definable (R := fun y : Fin 2 → V ↦ Seq (y 0) ∧ lh (y 0) = y 1)
      (by definability)).comp₂
        (c.table_comp (v := v) (LocallyDelta0Function.var (V := V) (0 : Fin 1)))
        (LocallyDelta0Function.var (V := V) (0 : Fin 1))
    simpa using this
  revert n
  apply LocallyDelta0Pred.succ_induction hP
  · simp
  · rintro n ⟨hs, hl⟩
    have : c.table v (n + 1) = c.table v n ⁀' c.clippedVal v n (c.table v n) := by
      simp [table_succ, seqCons, hl]
    rw [this]
    exact ⟨hs.seqCons _, by simp [hs, hl]⟩

lemma table_succ_eq_seqCons (n : V) :
    c.table v (n + 1) = c.table v n ⁀' c.clippedVal v n (c.table v n) := by
  simp [table_succ, seqCons, (c.table_seq (v := v) n).2]

lemma result_eq (n : V) : c.result v n = c.clippedVal v n (c.table v n) := by
  have := (c.table_seq (v := v) n).1.znth_seqCons_lh (x := c.clippedVal v n (c.table v n))
  rw [(c.table_seq (v := v) n).2] at this
  simpa [result, c.table_succ_eq_seqCons] using this

lemma result_le_bound (n : V) : c.result v n ≤ c.bound v n := by
  simp [c.result_eq, clippedVal]

lemma result_eq_val {n : V} (h : c.val v n (c.table v n) ≤ c.bound v n) :
    c.result v n = c.val v n (c.table v n) := by
  simpa [c.result_eq, clippedVal] using h

lemma znth_table {m n : V} (hm : m < n) : znth (c.table v n) m = c.result v m := by
  have hP : LocallyDelta0Pred fun n ↦ ∀ m < n, znth (c.table v n) m = c.result v m := by
    have hR : LocallyDelta0 fun y : Fin 2 → V ↦ znth (c.table v (y 1)) (y 0) =
        znth (c.table v (y 0 + 1)) (y 0) := by
      simpa using LocallyDelta0.eq
        (LocallyDelta0Function.znth.comp₂
          (c.table_comp (v := v) (LocallyDelta0Function.var (V := V) (1 : Fin 2)))
          (LocallyDelta0Function.var (V := V) (0 : Fin 2)))
        (LocallyDelta0Function.znth.comp₂
          (c.table_comp (v := v) <| LocallyDelta0Function.add_one <|
            LocallyDelta0Function.var (V := V) (0 : Fin 2))
          (LocallyDelta0Function.var (V := V) (0 : Fin 2)))
    exact (LocallyDelta0.ball_lt_function (LocallyDelta0Function.var (V := V) (0 : Fin 1))
      hR).of_iff fun w ↦ by simp [result]
  have : ∀ n, ∀ m < n, znth (c.table v n) m = c.result v m := by
    apply LocallyDelta0Pred.succ_induction hP
    · simp
    · intro n ih m hm
      rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hm) with (hm | rfl)
      · rw [c.table_succ_eq_seqCons,
          (c.table_seq (v := v) n).1.znth_seqCons_of_lt
            (by simpa [(c.table_seq (v := v) n).2] using hm)]
        exact ih m hm
      · rfl
  exact this n m hm

lemma result_locallyDelta0 :
    LocallyDelta0Function fun w : Fin (k + 1) → V ↦ c.result (w ·.succ) (w 0) := by
  have := LocallyDelta0Function.znth.comp₂
    (c.table_locallyDelta0.comp_cons
      (LocallyDelta0Function.add_one (LocallyDelta0Function.var 0))
      fun j ↦ LocallyDelta0Function.var j.succ)
    (LocallyDelta0Function.var 0)
  simpa [result] using this

end Construction

end CourseOfValues

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
