module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.HFS.Seq
public import AlphaCentauri.ToFoundation.ElementaryArithmetic.LocallyDelta0
public import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
# Primitive recursion in models of $\mathsf{EA}$

The file `Foundation/FirstOrder/Arithmetic/HFS/PRF.lean` on functions defined by primitive
recursion in models of $\mathsf{I}\Sigma_1$, ported to models of $\mathsf{EA}$. A construction
supplies, besides the functions and their defining formulas, a monotone bound on the values of
the recursion, so that every computation sequence is bounded and the recursion is carried out by
induction on a locally $\Delta_0$ predicate. The formulas of Foundation's `PR.Blueprint` define
the result.

- [HP98, §V.3]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

namespace PR

variable (V)

/-- A primitive recursion in a model of $\mathsf{EA}$, with a monotone bound on its values. -/
structure Construction {k : ℕ} (p : Arithmetic.PR.Blueprint k) where
  /-- `c.zero v` is the value at `0`. -/
  zero : (Fin k → V) → V
  /-- `c.succ v i z` is the value at `i + 1`, where `z` is the value at `i`. -/
  succ : (Fin k → V) → V → V → V
  zero_defined : 𝚺ᴬ₁.DefinedFunction zero p.zero
  succ_defined : 𝚺ᴬ₁.DefinedFunction (fun v ↦ succ (v ·.succ.succ) (v 1) (v 0)) p.succ
  zero_locallyDelta0 : LocallyDelta0Function zero
  succ_locallyDelta0 :
    LocallyDelta0Function fun v : Fin (k + 2) → V ↦ succ (v ·.succ.succ) (v 1) (v 0)
  /-- `c.bound v i` bounds the value at `i`. -/
  bound : (Fin k → V) → V → V
  zero_lt_bound : ∀ v, zero v < bound v 0
  succ_lt_bound : ∀ v i z, z < bound v i → succ v i z < bound v (i + 1)
  bound_monotone : ∀ v {i j}, i ≤ j → bound v i ≤ bound v j
  bound_locallyDelta0 : LocallyDelta0Function fun v : Fin (k + 1) → V ↦ bound (v ·.succ) (v 0)

variable {V}

namespace Construction

variable {k : ℕ} {p : Arithmetic.PR.Blueprint k} (c : Construction V p) (v : Fin k → V)

/-- `s` is a computation sequence of the recursion. -/
def CSeq (s : V) : Prop :=
  Seq s ∧ ⟪0, c.zero v⟫ ∈ s ∧ ∀ i < lh s - 1, ∀ z, ⟪i, z⟫ ∈ s → ⟪i + 1, c.succ v i z⟫ ∈ s

private lemma cseq_iff (s : V) : c.CSeq v s ↔
    Seq s
    ∧ (∃ z < s, z = c.zero v ∧ ⟪0, z⟫ ∈ s)
    ∧ (∀ i < 2 * s,
      (∃ l ≤ 2 * s, l = lh s ∧ i + 1 < l) → ∀ z < s, ⟪i, z⟫ ∈ s →
        ∃ u < s, u = c.succ v i z ∧ ⟪i + 1, u⟫ ∈ s) :=
  ⟨by rintro ⟨Hs, hz, hs⟩
      exact ⟨Hs, ⟨c.zero v, lt_of_mem_rng hz, rfl, hz⟩, fun i _ hi z _ hiz ↦
      ⟨c.succ v i z, by
        have := hs i (by rcases hi with ⟨l, _, rfl, hl⟩; simp [lt_tsub_iff_right, hl]) z hiz
        exact ⟨lt_of_mem_rng this, rfl, this⟩⟩⟩,
   by rintro ⟨Hs, ⟨z, _, rfl, hz⟩, h⟩
      exact ⟨Hs, hz, fun i hi z hiz ↦ by
        rcases h i
          (lt_of_lt_of_le hi (by simpa using le_trans (lh_bound _) (by simp)))
          ⟨lh s, by simp, rfl, by simpa [lt_tsub_iff_right] using hi⟩ z
          (lt_of_mem_rng hiz) hiz with ⟨_, _, rfl, h⟩
        exact h⟩⟩

lemma cseq_defined : 𝚺ᴬ₁.Defined (fun v ↦ c.CSeq (v ·.succ) (v 0) : (Fin (k + 1) → V) → Prop)
    p.cseqDef := .mk fun v ↦ by
  simp [Arithmetic.PR.Blueprint.cseqDef, cseq_iff, c.zero_defined.iff, c.succ_defined.iff]

@[simp] lemma cseq_defined_iff (v : Fin (k + 1) → V) :
    p.cseqDef.val.Evalb v ↔ c.CSeq (v ·.succ) (v 0) := c.cseq_defined.iff

private lemma cseq_iff_bounded (s : V) : c.CSeq v s ↔
    Seq s ∧ ⟪0, c.zero v⟫ ∈ s ∧
      ∀ i < s, i + 1 < lh s → ∀ z < s, ⟪i, z⟫ ∈ s → ⟪i + 1, c.succ v i z⟫ ∈ s := by
  constructor
  · rintro ⟨Hs, hz, hs⟩
    exact ⟨Hs, hz, fun i _ hi z _ hiz ↦ hs i (by simpa [lt_tsub_iff_right] using hi) z hiz⟩
  · rintro ⟨Hs, hz, hs⟩
    refine ⟨Hs, hz, fun i hi z hiz ↦ hs i (lt_of_mem_dom hiz)
      (by simpa [lt_tsub_iff_right] using hi) z (lt_of_mem_rng hiz) hiz⟩

lemma cseq_locallyDelta0 :
    LocallyDelta0 (k := k + 1) fun w ↦ c.CSeq (w ·.succ) (w 0) := by
  have hsucc : LocallyDelta0Function fun x : Fin (k + 3) → V ↦
      c.succ (fun j ↦ x j.succ.succ.succ) (x 1) (x 0) :=
    by simpa using c.succ_locallyDelta0.retraction (0 :> 1 :> fun j ↦ j.succ.succ.succ)
  have hstep : LocallyDelta0 fun x : Fin (k + 3) → V ↦
      ⟪x 1, x 0⟫ ∈ x 2 → ⟪x 1 + 1, c.succ (fun j ↦ x j.succ.succ.succ) (x 1) (x 0)⟫ ∈ x 2 := by
    apply LocallyDelta0.imp
    · apply LocallyDelta0.of_definable
      definability
    · have := (LocallyDelta0.of_definable (R := fun y : Fin 3 → V ↦ ⟪y 1 + 1, y 0⟫ ∈ y 2)
        (by definability)).comp (f := ![fun x ↦ c.succ (fun j ↦ x j.succ.succ.succ) (x 1) (x 0),
          fun x ↦ x 1, fun x ↦ x 2]) <| Fin.forall_fin_succ.mpr ⟨hsucc, Fin.forall_fin_succ.mpr
            ⟨LocallyDelta0Function.var 1, Fin.forall_fin_succ.mpr
              ⟨LocallyDelta0Function.var 2, finZeroElim⟩⟩⟩
      exact this.of_iff fun x ↦ by simp
  have hz : LocallyDelta0 fun y : Fin (k + 2) → V ↦
      ∀ z < y 1, ⟪y 0, z⟫ ∈ y 1 →
        ⟪y 0 + 1, c.succ (fun j ↦ y j.succ.succ) (y 0) z⟫ ∈ y 1 :=
    (LocallyDelta0.ball_lt_function (LocallyDelta0Function.var 1) hstep).of_iff fun y ↦ by simp
  have hlh : LocallyDelta0 fun y : Fin (k + 2) → V ↦ y 0 + 1 < lh (y 1) :=
    LocallyDelta0.of_definable (by definability)
  have hi : LocallyDelta0 fun w : Fin (k + 1) → V ↦
      ∀ i < w 0, i + 1 < lh (w 0) → ∀ z < w 0, ⟪i, z⟫ ∈ w 0 →
        ⟪i + 1, c.succ (fun j ↦ w j.succ) i z⟫ ∈ w 0 :=
    (LocallyDelta0.ball_lt_function (LocallyDelta0Function.var 0) (hlh.imp hz)).of_iff
      fun w ↦ by simp
  have hzero : LocallyDelta0 fun w : Fin (k + 1) → V ↦ ⟪0, c.zero (fun j ↦ w j.succ)⟫ ∈ w 0 := by
    have := (LocallyDelta0.of_definable (R := fun y : Fin 2 → V ↦ ⟪0, y 0⟫ ∈ y 1)
      (by definability)).comp (f := ![fun w ↦ c.zero (fun j ↦ w j.succ), fun w ↦ w 0]) <|
        Fin.forall_fin_succ.mpr ⟨c.zero_locallyDelta0.retraction Fin.succ,
          Fin.forall_fin_succ.mpr ⟨LocallyDelta0Function.var 0, finZeroElim⟩⟩
    exact this.of_iff fun w ↦ by simp
  have hseq : LocallyDelta0 fun w : Fin (k + 1) → V ↦ Seq (w 0) :=
    LocallyDelta0.of_definable (by definability)
  exact (hseq.and (hzero.and hi)).of_iff fun w ↦ by simpa using c.cseq_iff_bounded _ (w 0)

variable {c v}

namespace CSeq

variable {s : V}

lemma seq (h : c.CSeq v s) : Seq s := h.1

lemma zero (h : c.CSeq v s) : ⟪0, c.zero v⟫ ∈ s := h.2.1

lemma succ (h : c.CSeq v s) : ∀ i < lh s - 1, ∀ z, ⟪i, z⟫ ∈ s → ⟪i + 1, c.succ v i z⟫ ∈ s := h.2.2

lemma unique {s₁ s₂ : V} (H₁ : c.CSeq v s₁) (H₂ : c.CSeq v s₂) (h₁₂ : lh s₁ ≤ lh s₂) {i}
    (hi : i < lh s₁) {z₁ z₂} :
    ⟪i, z₁⟫ ∈ s₁ → ⟪i, z₂⟫ ∈ s₂ → z₁ = z₂ := by
  revert z₁ z₂
  suffices ∀ z₁ < s₁, ∀ z₂ < s₂, ⟪i, z₁⟫ ∈ s₁ → ⟪i, z₂⟫ ∈ s₂ → z₁ = z₂
  by intro z₁ z₂ hz₁ hz₂; exact this z₁ (lt_of_mem_rng hz₁) z₂ (lt_of_mem_rng hz₂) hz₁ hz₂
  intro z₁ hz₁ z₂ hz₂ h₁ h₂
  induction i using ISigma0.succ_induction generalizing z₁ z₂
  · definability
  case zero =>
    have : z₁ = c.zero v := H₁.seq.isMapping.uniq h₁ H₁.zero
    have : z₂ = c.zero v := H₂.seq.isMapping.uniq h₂ H₂.zero
    simp_all
  case succ i ih =>
    have hi' : i < lh s₁ := lt_of_le_of_lt (by simp) hi
    let z' := H₁.seq.nth hi'
    have ih₁ : ⟪i, z'⟫ ∈ s₁ := H₁.seq.nth_mem hi'
    have ih₂ : ⟪i, z'⟫ ∈ s₂ := by
      have : z' = H₂.seq.nth (lt_of_lt_of_le hi' h₁₂) :=
        ih hi' z' (by simp [z']) (H₂.seq.nth (lt_of_lt_of_le hi' h₁₂))
          (by simp) (by simp [z']) (by simp)
      simp [this]
    have h₁' : ⟪i + 1, c.succ v i z'⟫ ∈ s₁ := H₁.succ i (by simp [lt_tsub_iff_right, hi]) z' ih₁
    have h₂' : ⟪i + 1, c.succ v i z'⟫ ∈ s₂ :=
      H₂.succ i (by simpa [lt_tsub_iff_right] using lt_of_lt_of_le hi h₁₂) z' ih₂
    have e₁ : z₁ = c.succ v i z' := H₁.seq.isMapping.uniq h₁ h₁'
    have e₂ : z₂ = c.succ v i z' := H₂.seq.isMapping.uniq h₂ h₂'
    simp [e₁, e₂]

lemma initial : c.CSeq v !⟦c.zero v⟧ :=
  ⟨by simp, by simp [seqCons], by simp⟩

lemma successor {s l z : V} (Hs : c.CSeq v s) (hl : l + 1 = lh s) (hz : ⟪l, z⟫ ∈ s) :
    c.CSeq v (s ⁀' c.succ v l z) :=
  ⟨ Hs.seq.seqCons _, by simp [seqCons, Hs.zero], by
    simp only [Hs.seq.lh_seqCons, add_tsub_cancel_right]
    intro i hi w hiw
    have hiws : ⟪i, w⟫ ∈ s := by
      rcases show i = lh s ∧ w = c.succ v l z ∨ ⟪i, w⟫ ∈ s by
        simpa [mem_seqCons_iff] using hiw with (⟨rfl, rfl⟩ | h)
      · simp at hi
      · assumption
    have : i ≤ l := by simpa [← hl, lt_succ_iff_le] using hi
    rcases this with (rfl | hil)
    · have : w = z := Hs.seq.isMapping.uniq hiws hz
      simp [this, hl]
    · simp only [mem_seqCons_iff]; right
      exact Hs.succ i (by simp [← hl, hil]) w hiws ⟩

/-- Every value of a computation sequence lies below the bound. -/
lemma lt_bound (H : c.CSeq v s) {i z : V} (h : ⟪i, z⟫ ∈ s) : z < c.bound v i := by
  have hb : LocallyDelta0Function fun x : Fin 2 → V ↦ c.bound v (x 1) := by
    have := c.bound_locallyDelta0.comp (f := (fun x : Fin 2 → V ↦ x 1) :> fun j _ ↦ v j)
      fun j ↦ by
        cases j using Fin.cases with
        | zero => simpa using LocallyDelta0Function.var 1
        | succ j => simpa using LocallyDelta0Function.const (v j)
    simpa using this
  have hQ : LocallyDelta0 fun x : Fin 2 → V ↦ ⟪x 1, x 0⟫ ∈ s → x 0 < c.bound v (x 1) := by
    have := (LocallyDelta0.of_definable (R := fun y : Fin 3 → V ↦ ⟪y 0, y 1⟫ ∈ s → y 1 < y 2)
      (by definability)).comp (f := ![fun x ↦ x 1, fun x ↦ x 0, fun x ↦ c.bound v (x 1)]) <|
        Fin.forall_fin_succ.mpr ⟨LocallyDelta0Function.var 1, Fin.forall_fin_succ.mpr
          ⟨LocallyDelta0Function.var 0, Fin.forall_fin_succ.mpr ⟨hb, finZeroElim⟩⟩⟩
    exact this.of_iff fun x ↦ by simp
  have hP : LocallyDelta0Pred fun i ↦ ∀ z < s, ⟪i, z⟫ ∈ s → z < c.bound v i :=
    (LocallyDelta0.ball_lt_function (LocallyDelta0Function.const s) hQ).of_iff fun x ↦ by simp
  have : ∀ i, ∀ z < s, ⟪i, z⟫ ∈ s → z < c.bound v i := by
    apply LocallyDelta0Pred.succ_induction hP
    · intro z _ hz
      rw [H.seq.isMapping.uniq hz H.zero]
      exact c.zero_lt_bound v
    · intro i ih z _ hz
      have hi : i + 1 < lh s := H.seq.lt_lh_of_mem hz
      have hi' : i < lh s := lt_trans (by simp) hi
      have hmem := H.seq.nth_mem hi'
      have hsucc := H.succ i (by simpa [lt_tsub_iff_right] using hi) _ hmem
      rw [H.seq.isMapping.uniq hz hsucc]
      exact c.succ_lt_bound v i _ (ih _ (lt_of_mem_rng hmem) hmem)
  exact this i z (lt_of_mem_rng h) h

/-- A computation sequence of length at most `l + 1` lies below `Exp.exp ⟪l + 1, c.bound v l⟫`. -/
lemma lt_exp_of_lh_le (H : c.CSeq v s) {l : V} (hl : lh s ≤ l + 1) :
    s < Exp.exp ⟪l + 1, c.bound v l⟫ := by
  apply lt_exp_iff.mpr
  intro q hq
  have hq' : ⟪π₁ q, π₂ q⟫ ∈ s := by simpa using hq
  have hi : π₁ q < l + 1 := lt_of_lt_of_le (H.seq.lt_lh_of_mem hq') hl
  have hz : π₂ q < c.bound v l :=
    lt_of_lt_of_le (H.lt_bound hq') (c.bound_monotone v (lt_succ_iff_le.mp hi))
  simpa using pair_lt_pair hi hz

end CSeq

/-! ## Result of primitive recursion -/

variable (c v)

private lemma cseq_lh_locallyDelta0 :
    LocallyDelta0 fun x : Fin 2 → V ↦ c.CSeq v (x 0) ∧ x 1 + 1 = lh (x 0) := by
  have hcseq : LocallyDelta0 fun x : Fin 2 → V ↦ c.CSeq v (x 0) := by
    have := c.cseq_locallyDelta0.comp (f := (fun x : Fin 2 → V ↦ x 0) :> fun j _ ↦ v j)
      fun j ↦ by
        cases j using Fin.cases with
        | zero => simpa using LocallyDelta0Function.var 0
        | succ j => simpa using LocallyDelta0Function.const (v j)
    simpa using this
  exact hcseq.and <| LocallyDelta0.of_definable (by definability)

lemma CSeq.exists (l : V) : ∃ s, c.CSeq v s ∧ l + 1 = lh s := by
  set E := Exp.exp ⟪l + 1, c.bound v l⟫
  have hP : LocallyDelta0Pred fun m ↦ m ≤ l → ∃ s < E, c.CSeq v s ∧ m + 1 = lh s := by
    have := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.const (k := 1) E)
      (c.cseq_lh_locallyDelta0 v)
    exact (LocallyDelta0.of_definable (R := fun x : Fin 1 → V ↦ x 0 ≤ l) (by definability)).imp
      this |>.of_iff fun x ↦ by simp
  have : ∀ m, m ≤ l → ∃ s < E, c.CSeq v s ∧ m + 1 = lh s := by
    apply LocallyDelta0Pred.succ_induction hP
    · intro _
      use !⟦c.zero v⟧
      exact ⟨CSeq.initial.lt_exp_of_lh_le (by simp), CSeq.initial, by simp⟩
    · intro m ih hm
      obtain ⟨s, _, Hs, hls⟩ := ih (le_trans le_self_add hm)
      obtain ⟨z, hz⟩ := Hs.seq.exists (show m < lh s by simp [← hls])
      have H' := Hs.successor hls hz
      have hlh : lh (s ⁀' c.succ v m z) = m + 1 + 1 := by simp [Hs.seq, hls]
      use s ⁀' c.succ v m z
      exact ⟨H'.lt_exp_of_lh_le (by simpa [hlh] using hm), H', hlh.symm⟩
  obtain ⟨s, -, H⟩ := this l le_rfl
  exact ⟨s, H⟩

lemma cSeq_result_existsUnique (l : V) : ∃! z, ∃ s, c.CSeq v s ∧ l + 1 = lh s ∧ ⟪l, z⟫ ∈ s := by
  obtain ⟨s, Hs, h⟩ := CSeq.exists c v l
  obtain ⟨z, hz⟩ := Hs.seq.exists (show l < lh s by simp [← h])
  apply ExistsUnique.intro z ⟨s, Hs, h, hz⟩
  rintro z' ⟨s', Hs', h', hz'⟩
  exact Eq.symm <| Hs.unique Hs' (by simp [← h, ← h']) (show l < lh s by simp [← h]) hz hz'

/-- The value of the recursion at `u`. -/
noncomputable def result (u : V) : V := Classical.choose! (c.cSeq_result_existsUnique v u)

lemma result_spec (u : V) : ∃ s, c.CSeq v s ∧ u + 1 = lh s ∧ ⟪u, c.result v u⟫ ∈ s :=
  Classical.choose!_spec (c.cSeq_result_existsUnique v u)

@[simp] theorem result_zero : c.result v 0 = c.zero v := by
  obtain ⟨s, Hs, _, h0⟩ := c.result_spec v 0
  exact Hs.seq.isMapping.uniq h0 Hs.zero

@[simp] theorem result_succ (u : V) : c.result v (u + 1) = c.succ v u (c.result v u) := by
  obtain ⟨s, Hs, hk, h⟩ := c.result_spec v u
  have : CSeq c v (s ⁀' c.succ v u (result c v u)) := Hs.successor hk h
  exact Eq.symm <| Classical.choose_uniq (c.cSeq_result_existsUnique v (u + 1))
    ⟨_, this, by simp [Hs.seq, hk], by simp [hk]⟩

lemma result_graph (z u : V) : z = c.result v u ↔ ∃ s, c.CSeq v s ∧ ⟪u, z⟫ ∈ s :=
  ⟨by rintro rfl
      obtain ⟨s, Hs, _, h⟩ := c.result_spec v u
      exact ⟨s, Hs, h⟩,
   by rintro ⟨s, Hs, h⟩
      obtain ⟨s', Hs', hu, h'⟩ := c.result_spec v u
      exact Eq.symm <| Hs'.unique Hs
        (by simpa [← hu, succ_le_iff_lt] using Hs.seq.lt_lh_iff.mpr (mem_domain_of_pair_mem h))
        (by simp [← hu]) h' h⟩

lemma result_lt_bound (u : V) : c.result v u < c.bound v u := by
  obtain ⟨s, Hs, _, h⟩ := c.result_spec v u
  exact Hs.lt_bound h

private lemma result_graph_bounded (z u : V) : z = c.result v u ↔
    ∃ s < Exp.exp ⟪u + 1, c.bound v u⟫, c.CSeq v s ∧ u + 1 = lh s ∧ ⟪u, z⟫ ∈ s := by
  constructor
  · rintro rfl
    obtain ⟨s, Hs, hu, h⟩ := c.result_spec v u
    exact ⟨s, Hs.lt_exp_of_lh_le hu.symm.le, Hs, hu, h⟩
  · rintro ⟨s, _, Hs, _, h⟩
    exact (c.result_graph v z u).mpr ⟨s, Hs, h⟩

set_option linter.flexible false in
lemma result_defined : 𝚺ᴬ₁.DefinedFunction
    (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) p.resultDef := .mk fun v ↦ by
  simp [Arithmetic.PR.Blueprint.resultDef, result_graph, c.cseq_defined_iff]

lemma result_defined_delta : 𝚫ᴬ₁.DefinedFunction
    (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) p.resultDeltaDef :=
  c.result_defined.graph_delta

@[simp] lemma result_defined_iff (v : Fin (k + 2) → V) :
    p.resultDef.val.Evalb v ↔ v 0 = c.result (v ·.succ.succ) (v 1) :=
  c.result_defined.iff

lemma result_definable : 𝚺ᴬ₁.DefinableFunction
    (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) :=
  c.result_defined.to_definable

lemma result_definable_delta₁ : 𝚫ᴬ₁.DefinableFunction
    (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) :=
  c.result_defined_delta.to_definable

lemma result_locallyDelta0 :
    LocallyDelta0Function fun w : Fin (k + 1) → V ↦ c.result (w ·.succ) (w 0) where
  graph := by
    have hpair : LocallyDelta0Function fun x : Fin 2 → V ↦ ⟪x 0, x 1⟫ :=
      LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, by definability⟩
    have hadd : LocallyDelta0Function fun x : Fin 2 → V ↦ x 0 + x 1 :=
      LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, by definability⟩
    have hsucc : LocallyDelta0Function fun w : Fin (k + 2) → V ↦ w 1 + 1 :=
      hadd.comp (f := ![fun w ↦ w 1, fun _ ↦ 1]) <| Fin.forall_fin_succ.mpr
        ⟨LocallyDelta0Function.var 1, Fin.forall_fin_succ.mpr
          ⟨LocallyDelta0Function.const 1, finZeroElim⟩⟩
    have hbound : LocallyDelta0Function fun w : Fin (k + 2) → V ↦
        c.bound (fun j ↦ w j.succ.succ) (w 1) := by
      simpa using c.bound_locallyDelta0.retraction Fin.succ
    have hE : LocallyDelta0Function fun w : Fin (k + 2) → V ↦
        Exp.exp ⟪w 1 + 1, c.bound (fun j ↦ w j.succ.succ) (w 1)⟫ := by
      have := hpair.comp (f := ![fun w ↦ w 1 + 1, fun w ↦ c.bound (fun j ↦ w j.succ.succ) (w 1)])
        <| Fin.forall_fin_succ.mpr ⟨hsucc, Fin.forall_fin_succ.mpr ⟨hbound, finZeroElim⟩⟩
      have := LocallyDelta0Function.exp.comp (f := ![fun w ↦
        ⟪w 1 + 1, c.bound (fun j ↦ w j.succ.succ) (w 1)⟫]) <|
          Fin.forall_fin_succ.mpr ⟨by simpa using this, finZeroElim⟩
      simpa using this
    have hcseq : LocallyDelta0 fun x : Fin (k + 3) → V ↦
        c.CSeq (fun j ↦ x j.succ.succ.succ) (x 0) := by
      have := c.cseq_locallyDelta0.comp
        (f := (fun x : Fin (k + 3) → V ↦ x 0) :> fun j x ↦ x j.succ.succ.succ) fun j ↦ by
          cases j using Fin.cases with
          | zero => simpa using LocallyDelta0Function.var 0
          | succ j => simpa using LocallyDelta0Function.var j.succ.succ.succ
      simpa using this
    have hbody : LocallyDelta0 fun x : Fin (k + 3) → V ↦
        c.CSeq (fun j ↦ x j.succ.succ.succ) (x 0) ∧ x 2 + 1 = lh (x 0) ∧ ⟪x 2, x 1⟫ ∈ x 0 :=
      hcseq.and <| LocallyDelta0.of_definable (by definability)
    exact (LocallyDelta0.bexs_lt_function hE hbody).of_iff fun w ↦ by
      simpa using c.result_graph_bounded (fun j ↦ w j.succ.succ) (w 0) (w 1)
  bounded X := by
    obtain ⟨Y, hY⟩ := c.bound_locallyDelta0.bounded X
    use Y
    intro w hw
    exact le_trans (c.result_lt_bound _ _).le (hY w hw)

end Construction

end PR

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
