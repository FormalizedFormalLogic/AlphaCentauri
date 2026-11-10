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

end CSeq

end Construction

end PR

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
