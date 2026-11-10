module

public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic

/-!
# Internal proof measures

`cutRank` is the primitive-recursive cut rank of an internal proof code; it is total on all
codes and is zero on codes that are not proof-rule constructors.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

section Measures

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace InternalMeasures

/-- The rule tag stored in a proof-rule constructor code, i.e. the first component of `sndIdx d`. -/
noncomputable def tag (d : V) : V := π₁ (sndIdx d)

/-- The tail of a proof-rule constructor code after its rule tag, with the outermost pairing layer
stripped off: the sole stored child of a unary rule (`wkRule`, `shiftRule`). -/
noncomputable def last₁ (d : V) : V := π₂ (sndIdx d)

/-- As `last₁`, with a further pairing layer stripped off: the stored child of `allIntro`. -/
noncomputable def last₂ (d : V) : V := π₂ (π₂ (sndIdx d))

/-- As `last₂`, with a further pairing layer stripped off: the stored child of `orIntro` and
`exsIntro`, and the second child `d₂` of `cutRule`. -/
noncomputable def last₃ (d : V) : V := π₂ (π₂ (π₂ (sndIdx d)))

/-- As `last₃`, with a further pairing layer stripped off: the second child `dq` of `andIntro`. -/
noncomputable def last₄ (d : V) : V := π₂ (π₂ (π₂ (π₂ (sndIdx d))))

/-- The first component of the middle pair stored by `cutRule`, i.e. its cut formula `p`. -/
noncomputable def pre₂ (d : V) : V := π₁ (π₂ (sndIdx d))

/-- The first component of the last pair stored by `cutRule`, i.e. its first child `d₁`. -/
noncomputable def pre₃ (d : V) : V := π₁ (π₂ (π₂ (sndIdx d)))

/-- The first component of the last pair stored by `andIntro`, i.e. its first child `dp`. -/
noncomputable def pre₄ (d : V) : V := π₁ (π₂ (π₂ (π₂ (sndIdx d))))

/-- The $\Sigma_1$ graph of `tag`. -/
def tagGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “t d. ∃ r, !sndIdxDef r d ∧ !pi₁Def t r”

/-- The $\Sigma_1$ graph of `last₁`. -/
def last₁Graph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ !pi₂Def a r”

/-- The $\Sigma_1$ graph of `last₂`. -/
def last₂Graph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧ !pi₂Def a q”

/-- The $\Sigma_1$ graph of `last₃`. -/
def last₃Graph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ !pi₂Def a q'”

/-- The $\Sigma_1$ graph of `last₄`. -/
def last₄Graph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ ∃ q'', !pi₂Def q'' q' ∧ !pi₂Def a q''”

/-- The $\Sigma_1$ graph of `pre₂`. -/
def pre₂Graph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧ !pi₁Def a q”

/-- The $\Sigma_1$ graph of `pre₃`. -/
def pre₃Graph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ !pi₁Def a q'”

/-- The $\Sigma_1$ graph of `pre₄`. -/
def pre₄Graph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ ∃ q'', !pi₂Def q'' q' ∧ !pi₁Def a q''”

instance tag_def : 𝚺ᴬ₁-Function₁[V] tag via tagGraph := .mk fun v ↦ by
  simp [tagGraph, tag]

instance last₁_def : 𝚺ᴬ₁-Function₁[V] last₁ via last₁Graph := .mk fun v ↦ by
  simp [last₁Graph, last₁]

instance last₂_def : 𝚺ᴬ₁-Function₁[V] last₂ via last₂Graph := .mk fun v ↦ by
  simp [last₂Graph, last₂]

instance last₃_def : 𝚺ᴬ₁-Function₁[V] last₃ via last₃Graph := .mk fun v ↦ by
  simp [last₃Graph, last₃]

instance last₄_def : 𝚺ᴬ₁-Function₁[V] last₄ via last₄Graph := .mk fun v ↦ by
  simp [last₄Graph, last₄]

instance pre₂_def : 𝚺ᴬ₁-Function₁[V] pre₂ via pre₂Graph := .mk fun v ↦ by
  simp [pre₂Graph, pre₂]

instance pre₃_def : 𝚺ᴬ₁-Function₁[V] pre₃ via pre₃Graph := .mk fun v ↦ by
  simp [pre₃Graph, pre₃]

instance pre₄_def : 𝚺ᴬ₁-Function₁[V] pre₄ via pre₄Graph := .mk fun v ↦ by
  simp [pre₄Graph, pre₄]

@[simp] lemma tag_andIntro (s p q dp dq : V) : tag (andIntro s p q dp dq) = 2 := by
  simp [andIntro, tag, sndIdx]

@[simp] lemma pre₄_andIntro (s p q dp dq : V) : pre₄ (andIntro s p q dp dq) = dp := by
  simp [andIntro, pre₄, sndIdx]

@[simp] lemma last₄_andIntro (s p q dp dq : V) : last₄ (andIntro s p q dp dq) = dq := by
  simp [andIntro, last₄, sndIdx]

@[simp] lemma tag_orIntro (s p q d : V) : tag (orIntro s p q d) = 3 := by
  simp [orIntro, tag, sndIdx]

@[simp] lemma last₃_orIntro (s p q d : V) : last₃ (orIntro s p q d) = d := by
  simp [orIntro, last₃, sndIdx]

@[simp] lemma tag_allIntro (s p d : V) : tag (allIntro s p d) = 4 := by
  simp [allIntro, tag, sndIdx]

@[simp] lemma last₂_allIntro (s p d : V) : last₂ (allIntro s p d) = d := by
  simp [allIntro, last₂, sndIdx]

@[simp] lemma tag_exsIntro (s p t d : V) : tag (exsIntro s p t d) = 5 := by
  simp [exsIntro, tag, sndIdx]

@[simp] lemma last₃_exsIntro (s p t d : V) : last₃ (exsIntro s p t d) = d := by
  simp [exsIntro, last₃, sndIdx]

@[simp] lemma tag_wkRule (s d : V) : tag (wkRule s d) = 6 := by
  simp [wkRule, tag, sndIdx]

@[simp] lemma last₁_wkRule (s d : V) : last₁ (wkRule s d) = d := by
  simp [wkRule, last₁, sndIdx]

@[simp] lemma tag_shiftRule (s d : V) : tag (shiftRule s d) = 7 := by
  simp [shiftRule, tag, sndIdx]

@[simp] lemma last₁_shiftRule (s d : V) : last₁ (shiftRule s d) = d := by
  simp [shiftRule, last₁, sndIdx]

@[simp] lemma tag_cutRule (s p d₁ d₂ : V) : tag (cutRule s p d₁ d₂) = 8 := by
  simp [cutRule, tag, sndIdx]

@[simp] lemma pre₂_cutRule (s p d₁ d₂ : V) : pre₂ (cutRule s p d₁ d₂) = p := by
  simp [cutRule, pre₂, sndIdx]

@[simp] lemma pre₃_cutRule (s p d₁ d₂ : V) : pre₃ (cutRule s p d₁ d₂) = d₁ := by
  simp [cutRule, pre₃, sndIdx]

@[simp] lemma last₃_cutRule (s p d₁ d₂ : V) : last₃ (cutRule s p d₁ d₂) = d₂ := by
  simp [cutRule, last₃, sndIdx]

variable (L : Language) [L.Encodable] [L.LORDefinable]

/-- The next cut rank in the primitive-recursive history of an internal proof code, computed from
the history `ih` of the cut ranks of all smaller codes: a cut node contributes one more than the
complexity of its cut formula, every other node only passes on the ranks of its children.

- [Bus98, Ch. I §2.4] -/
noncomputable def nodeCutRank (d ih : V) : V :=
  if tag d = 2 then max (znth ih (pre₄ d)) (znth ih (last₄ d))
  else if tag d = 3 then znth ih (last₃ d)
  else if tag d = 4 then znth ih (last₂ d)
  else if tag d = 5 then znth ih (last₃ d)
  else if tag d = 6 then znth ih (last₁ d)
  else if tag d = 7 then znth ih (last₁ d)
  else if tag d = 8 then
    max (max (znth ih (pre₃ d)) (znth ih (last₃ d))) (formulaComplexity L (pre₂ d) + 1)
  else 0

/-- The $\Sigma_1$ graph of `nodeCutRank`. -/
noncomputable def nodeCutRankGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “r d ih. (∃ t, !tagGraph t d ∧ t = 2 ∧ ∃ p, !pre₄Graph p d ∧ ∃ q, !last₄Graph q d ∧
      ∃ rp, !znthDef rp ih p ∧ ∃ rq, !znthDef rq ih q ∧ !max.dfn r rp rq) ∨
    (∃ t, !tagGraph t d ∧ t = 3 ∧ ∃ p, !last₃Graph p d ∧ !znthDef r ih p) ∨
    (∃ t, !tagGraph t d ∧ t = 4 ∧ ∃ p, !last₂Graph p d ∧ !znthDef r ih p) ∨
    (∃ t, !tagGraph t d ∧ t = 5 ∧ ∃ p, !last₃Graph p d ∧ !znthDef r ih p) ∨
    (∃ t, !tagGraph t d ∧ t = 6 ∧ ∃ p, !last₁Graph p d ∧ !znthDef r ih p) ∨
    (∃ t, !tagGraph t d ∧ t = 7 ∧ ∃ p, !last₁Graph p d ∧ !znthDef r ih p) ∨
    (∃ t, !tagGraph t d ∧ t = 8 ∧ ∃ p, !pre₃Graph p d ∧ ∃ q, !last₃Graph q d ∧
      ∃ rp, !znthDef rp ih p ∧ ∃ rq, !znthDef rq ih q ∧ ∃ m, !max.dfn m rp rq ∧
      ∃ c, !pre₂Graph c d ∧ ∃ k, !(formulaComplexityGraph L) k c ∧ !max.dfn r m (k + 1)) ∨
    (∃ t, !tagGraph t d ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ t ≠ 5 ∧ t ≠ 6 ∧ t ≠ 7 ∧ t ≠ 8 ∧ r = 0)”

instance nodeCutRank_def :
    𝚺ᴬ₁-Function₂[V] nodeCutRank L via nodeCutRankGraph L := .mk fun v ↦ by
  simp [nodeCutRankGraph, nodeCutRank, (formulaComplexity.defined (L := L) (V := V)).iff]
  split_ifs <;> simp_all [numeral_eq_natCast]

/-- The primitive-recursion blueprint for `cutRankSeq`: it grows a sequence of cut ranks, one entry
per code, by appending `nodeCutRank` computed from the entries seen so far. -/
noncomputable def cutRankBlueprint : PR.Blueprint 0 where
  zero := .mkSigma “s. !seqConsDef s 0 0”
  succ := .mkSigma “y ih k. ∃ r, !(nodeCutRankGraph L) r (k + 1) ih ∧ !seqConsDef y ih r”

/-- The primitive-recursive construction underlying `cutRankSeq`. -/
noncomputable def cutRankConstruction : PR.Construction V (cutRankBlueprint L) where
  zero _ := 0 ⁀' 0
  succ _ k ih := ih ⁀' nodeCutRank L (k + 1) ih
  zero_defined := .mk fun v ↦ by simp [cutRankBlueprint]
  succ_defined := .mk fun v ↦ by simp [cutRankBlueprint, (nodeCutRank_def (L := L) (V := V)).iff]

/-- The primitive-recursive history of cut ranks through the internal code `d`. -/
noncomputable def cutRankSeq (d : V) : V := (cutRankConstruction L).result ![] d

/-- The $\Sigma_1$ graph of `cutRankSeq`. -/
noncomputable def cutRankSeqGraph : 𝚺ᴬ₁.Semisentence 2 := (cutRankBlueprint L).resultDef

/-- The primitive-recursive cut rank assigned to an internal proof code: one more than the greatest
complexity of a formula cut on in `d`, and `0` when `d` cuts on nothing.

- [Bus98, Ch. I §2.4] -/
noncomputable def cutRank (d : V) : V := znth (cutRankSeq L d) d

/-- The $\Sigma_1$ graph of `cutRank`. -/
noncomputable def cutRankGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “r d. ∃ s, !(cutRankBlueprint L).resultDef s d ∧ !znthDef r s d”

variable {L}

@[simp] lemma cutRankSeq_zero : cutRankSeq L (0 : V) = 0 ⁀' 0 := by
  simp [cutRankSeq, cutRankConstruction]

@[simp] lemma cutRankSeq_succ (d : V) :
    cutRankSeq L (d + 1) = cutRankSeq L d ⁀' nodeCutRank L (d + 1) (cutRankSeq L d) := by
  rw [cutRankSeq, (cutRankConstruction L).result_succ]
  rfl

instance cutRankSeq_def : 𝚺ᴬ₁-Function₁[V] cutRankSeq L via cutRankSeqGraph L := .mk fun v ↦ by
  have h := (cutRankConstruction L).result_defined_iff (V := V) v
  simpa [cutRankSeqGraph, cutRankSeq, cutRankBlueprint,
    Subsingleton.elim (fun x : Fin 0 ↦ v x.succ.succ) ![],
    Subsingleton.elim (fun _ : Fin 0 ↦ v 1) ![]] using h

instance cutRankSeq_definable : 𝚺ᴬ₁-Function₁[V] cutRankSeq L := cutRankSeq_def.to_definable

instance cutRank_def : 𝚺ᴬ₁-Function₁[V] cutRank L via cutRankGraph L := .mk fun v ↦ by
  have h (s d : V) : (cutRankBlueprint L).resultDef.val.Evalb ![s, d] ↔ s = cutRankSeq L d := by
    simpa [cutRankSeq, cutRankBlueprint, Subsingleton.elim (fun _ : Fin 0 ↦ d) ![]] using
      ((cutRankConstruction L).result_defined_iff (![s, d] : Fin 2 → V) :
        (cutRankBlueprint L).resultDef.val.Evalb ![s, d] ↔
          s = (cutRankConstruction L).result (fun _ : Fin 0 ↦ d) d)
  simp [cutRankGraph, cutRank, h]

instance cutRank_definable : 𝚺ᴬ₁-Function₁[V] cutRank L := cutRank_def.to_definable

private lemma seq_zero : Seq (0 : V) := by simpa [emptyset_def] using (seq_empty : Seq (∅ : V))

private lemma lh_zero : lh (0 : V) = 0 := by
  simpa [emptyset_def] using (lh_empty : lh (∅ : V) = 0)

private lemma cutRankSeq_seq (d : V) : Seq (cutRankSeq L d) := by
  induction d using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using seq_zero.seqCons 0
  case succ d ih => simpa using ih.seqCons _

private lemma lh_cutRankSeq (d : V) : lh (cutRankSeq L d) = d + 1 := by
  induction d using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [cutRankSeq_zero, seq_zero.lh_seqCons 0, lh_zero]
  case succ d ih => rw [cutRankSeq_succ, (cutRankSeq_seq (L := L) d).lh_seqCons _, ih]

private lemma znth_seqCons_of_lt {s z x : V} (H : Seq s) (hx : x < lh s) :
    znth (s ⁀' z) x = znth s x :=
  (H.seqCons z).znth_eq_of_mem (Seq.subset_seqCons s z (H.znth hx))

/-- Every entry of `cutRankSeq d` at an index `x ≤ d` agrees with `cutRank x`: extending the
history further never changes the cut rank already recorded for a smaller code. -/
private lemma znth_cutRankSeq_of_le {x d : V} (h : x ≤ d) :
    znth (cutRankSeq L d) x = cutRank L x := by
  induction d using ISigma1.sigma1_succ_induction generalizing x
  · definability
  case zero =>
    rcases nonpos_iff_eq_zero.mp h with rfl
    rfl
  case succ d ih =>
    rcases le_iff_lt_or_eq.mp h with hlt | rfl
    · have hxd : x ≤ d := lt_succ_iff_le.mp hlt
      rw [cutRankSeq_succ, znth_seqCons_of_lt (cutRankSeq_seq (L := L) d)
        (by rw [lh_cutRankSeq]; exact lt_succ_iff_le.mpr hxd)]
      exact ih hxd
    · rfl

/-- The cut rank of a code built as the successor of `c` unfolds one primitive-recursion step: it
is `nodeCutRank` applied to the history of cut ranks up to `c`. -/
private lemma cutRank_succ (c : V) :
    cutRank L (c + 1) = nodeCutRank L (c + 1) (cutRankSeq L c) := by
  have hmem : ⟪c + 1, nodeCutRank L (c + 1) (cutRankSeq L c)⟫ ∈ cutRankSeq L (c + 1) := by
    rw [cutRankSeq_succ, ← lh_cutRankSeq (L := L) c]
    exact lh_mem_seqCons (cutRankSeq L c) _
  simpa [cutRank] using (cutRankSeq_seq (L := L) (c + 1)).znth_eq_of_mem hmem

private lemma cutRank_eq_of_succ {c d : V} (h : c + 1 = d) :
    cutRank L d = nodeCutRank L d (cutRankSeq L c) :=
  h ▸ cutRank_succ c

@[simp] lemma cutRank_axL (s p : V) : cutRank L (axL s p) = 0 := by
  simp [axL, cutRank_succ, nodeCutRank, tag, sndIdx]

@[simp] lemma cutRank_verumIntro (s : V) : cutRank L (verumIntro s) = 0 := by
  simp [verumIntro, cutRank_succ, nodeCutRank, tag, sndIdx]

@[simp] lemma cutRank_axm (s p : V) : cutRank L (axm s p) = 0 := by
  simp [axm, cutRank_succ, nodeCutRank, tag, sndIdx]

@[simp] lemma cutRank_andIntro (s p q dp dq : V) :
    cutRank L (andIntro s p q dp dq) = max (cutRank L dp) (cutRank L dq) := by
  have hp : dp ≤ ⟪s, 2, p, q, dp, dq⟫ := lt_succ_iff_le.mp (dp_lt_andIntro s p q dp dq)
  have hq : dq ≤ ⟪s, 2, p, q, dp, dq⟫ := lt_succ_iff_le.mp (dq_lt_andIntro s p q dp dq)
  rw [cutRank_eq_of_succ (c := ⟪s, 2, p, q, dp, dq⟫) (d := andIntro s p q dp dq) rfl]
  simp [nodeCutRank, znth_cutRankSeq_of_le hp, znth_cutRankSeq_of_le hq]

@[simp] lemma cutRank_orIntro (s p q d : V) : cutRank L (orIntro s p q d) = cutRank L d := by
  have hd : d ≤ ⟪s, 3, p, q, d⟫ := lt_succ_iff_le.mp (d_lt_orIntro s p q d)
  rw [cutRank_eq_of_succ (c := ⟪s, 3, p, q, d⟫) (d := orIntro s p q d) rfl]
  simp [nodeCutRank, znth_cutRankSeq_of_le hd]

@[simp] lemma cutRank_allIntro (s p d : V) : cutRank L (allIntro s p d) = cutRank L d := by
  have hd : d ≤ ⟪s, 4, p, d⟫ := lt_succ_iff_le.mp (s_lt_allIntro s p d)
  rw [cutRank_eq_of_succ (c := ⟪s, 4, p, d⟫) (d := allIntro s p d) rfl]
  simp [nodeCutRank, znth_cutRankSeq_of_le hd]

@[simp] lemma cutRank_exsIntro (s p t d : V) : cutRank L (exsIntro s p t d) = cutRank L d := by
  have hd : d ≤ ⟪s, 5, p, t, d⟫ := lt_succ_iff_le.mp (d_lt_exsIntro s p t d)
  rw [cutRank_eq_of_succ (c := ⟪s, 5, p, t, d⟫) (d := exsIntro s p t d) rfl]
  simp [nodeCutRank, znth_cutRankSeq_of_le hd]

@[simp] lemma cutRank_wkRule (s d : V) : cutRank L (wkRule s d) = cutRank L d := by
  have hd : d ≤ ⟪s, 6, d⟫ := lt_succ_iff_le.mp (d_lt_wkRule s d)
  rw [cutRank_eq_of_succ (c := ⟪s, 6, d⟫) (d := wkRule s d) rfl]
  simp [nodeCutRank, znth_cutRankSeq_of_le hd]

@[simp] lemma cutRank_shiftRule (s d : V) : cutRank L (shiftRule s d) = cutRank L d := by
  have hd : d ≤ ⟪s, 7, d⟫ := lt_succ_iff_le.mp (d_lt_shiftRule s d)
  rw [cutRank_eq_of_succ (c := ⟪s, 7, d⟫) (d := shiftRule s d) rfl]
  simp [nodeCutRank, znth_cutRankSeq_of_le hd]

@[simp] lemma cutRank_cutRule (s p d₁ d₂ : V) :
    cutRank L (cutRule s p d₁ d₂) =
      max (max (cutRank L d₁) (cutRank L d₂)) (formulaComplexity L p + 1) := by
  have h₁ : d₁ ≤ ⟪s, 8, p, d₁, d₂⟫ := lt_succ_iff_le.mp (d₁_lt_cutRule s p d₁ d₂)
  have h₂ : d₂ ≤ ⟪s, 8, p, d₁, d₂⟫ := lt_succ_iff_le.mp (d₂_lt_cutRule s p d₁ d₂)
  rw [cutRank_eq_of_succ (c := ⟪s, 8, p, d₁, d₂⟫) (d := cutRule s p d₁ d₂) rfl]
  simp [nodeCutRank, znth_cutRankSeq_of_le h₁, znth_cutRankSeq_of_le h₂]

end InternalMeasures

end Measures

end FFL.FirstOrder.Arithmetic.Bootstrapping
