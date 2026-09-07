module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic

/-!
# Internal proof measures

This module defines primitive-recursive height and cut-rank functions on internal proof codes.
Both are total on all codes; on codes that are not proof-rule constructors their value is zero.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace InternalMeasures

/-- The rule tag stored in a proof-rule constructor code, i.e. the first component of `sndIdx d`.

No source; a formalization device for reading off the constructor used to build `d`. -/
noncomputable def tag (d : V) : V := π₁ (sndIdx d)

/-- The tail of a proof-rule constructor code after its rule tag, with the outermost pairing layer
stripped off: the sole stored child of a unary rule (`wkRule`, `shiftRule`).

No source; a formalization device for reading off a constructor argument of `d`. -/
noncomputable def last₁ (d : V) : V := π₂ (sndIdx d)

/-- As `last₁`, with a further pairing layer stripped off: the stored child of `allIntro`.

No source; a formalization device. -/
noncomputable def last₂ (d : V) : V := π₂ (π₂ (sndIdx d))

/-- As `last₂`, with a further pairing layer stripped off: the stored child of `orIntro` and
`exsIntro`, and the second child `d₂` of `cutRule`.

No source; a formalization device. -/
noncomputable def last₃ (d : V) : V := π₂ (π₂ (π₂ (sndIdx d)))

/-- As `last₃`, with a further pairing layer stripped off: the second child `dq` of `andIntro`.

No source; a formalization device. -/
noncomputable def last₄ (d : V) : V := π₂ (π₂ (π₂ (π₂ (sndIdx d))))

/-- The first component of the last pair stored by `cutRule`, i.e. its first child `d₁`.

No source; a formalization device. -/
noncomputable def pre₃ (d : V) : V := π₁ (π₂ (π₂ (sndIdx d)))

/-- The first component of the last pair stored by `andIntro`, i.e. its first child `dp`.

No source; a formalization device. -/
noncomputable def pre₄ (d : V) : V := π₁ (π₂ (π₂ (π₂ (sndIdx d))))

/-- The `𝚺₁` graph of `tag`.

No source; a formalization device. -/
def tagGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “t d. ∃ r, !sndIdxDef r d ∧ !pi₁Def t r”

/-- The `𝚺₁` graph of `last₁`.

No source; a formalization device. -/
def last₁Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ !pi₂Def a r”

/-- The `𝚺₁` graph of `last₂`.

No source; a formalization device. -/
def last₂Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧ !pi₂Def a q”

/-- The `𝚺₁` graph of `last₃`.

No source; a formalization device. -/
def last₃Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ !pi₂Def a q'”

/-- The `𝚺₁` graph of `last₄`.

No source; a formalization device. -/
def last₄Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ ∃ q'', !pi₂Def q'' q' ∧ !pi₂Def a q''”

/-- The `𝚺₁` graph of `pre₃`.

No source; a formalization device. -/
def pre₃Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ !pi₁Def a q'”

/-- The `𝚺₁` graph of `pre₄`.

No source; a formalization device. -/
def pre₄Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ ∃ q'', !pi₂Def q'' q' ∧ !pi₁Def a q''”

/-- `tag` is `𝚺₁`-definable.

No source; a formalization device. -/
instance tag_def : 𝚺₁-Function₁[V] tag via tagGraph := .mk fun v ↦ by
  simp [tagGraph, tag]

/-- `last₁` is `𝚺₁`-definable.

No source; a formalization device. -/
instance last₁_def : 𝚺₁-Function₁[V] last₁ via last₁Graph := .mk fun v ↦ by
  simp [last₁Graph, last₁]

/-- `last₂` is `𝚺₁`-definable.

No source; a formalization device. -/
instance last₂_def : 𝚺₁-Function₁[V] last₂ via last₂Graph := .mk fun v ↦ by
  simp [last₂Graph, last₂]

/-- `last₃` is `𝚺₁`-definable.

No source; a formalization device. -/
instance last₃_def : 𝚺₁-Function₁[V] last₃ via last₃Graph := .mk fun v ↦ by
  simp [last₃Graph, last₃]

/-- `last₄` is `𝚺₁`-definable.

No source; a formalization device. -/
instance last₄_def : 𝚺₁-Function₁[V] last₄ via last₄Graph := .mk fun v ↦ by
  simp [last₄Graph, last₄]

/-- `pre₃` is `𝚺₁`-definable.

No source; a formalization device. -/
instance pre₃_def : 𝚺₁-Function₁[V] pre₃ via pre₃Graph := .mk fun v ↦ by
  simp [pre₃Graph, pre₃]

/-- `pre₄` is `𝚺₁`-definable.

No source; a formalization device. -/
instance pre₄_def : 𝚺₁-Function₁[V] pre₄ via pre₄Graph := .mk fun v ↦ by
  simp [pre₄Graph, pre₄]

/-- The rule tag of `axL s p` is `0`, the constructor's own tag.

No source; direct computation from the definition of `tag`. -/
@[simp] lemma tag_axL (s p : V) : tag (axL s p) = 0 := by
  rw [show axL s p = ⟪s, 0, p⟫ + 1 from rfl]
  simp [tag, sndIdx]

/-- The rule tag of `verumIntro s` is `1`, the constructor's own tag.

No source; direct computation from the definition of `tag`. -/
@[simp] lemma tag_verumIntro (s : V) : tag (verumIntro s) = 1 := by
  rw [show verumIntro s = ⟪s, 1, 0⟫ + 1 from rfl]
  simp [tag, sndIdx]

/-- The rule tag of `andIntro s p q dp dq` is `2`, the constructor's own tag.

No source; direct computation from the definition of `tag`. -/
@[simp] lemma tag_andIntro (s p q dp dq : V) : tag (andIntro s p q dp dq) = 2 := by
  rw [show andIntro s p q dp dq = ⟪s, 2, p, q, dp, dq⟫ + 1 from rfl]
  simp [tag, sndIdx]

/-- `pre₄` recovers the first child `dp` stored by `andIntro s p q dp dq`.

No source; direct computation from the definition of `pre₄`. -/
@[simp] lemma pre₄_andIntro (s p q dp dq : V) : pre₄ (andIntro s p q dp dq) = dp := by
  rw [show andIntro s p q dp dq = ⟪s, 2, p, q, dp, dq⟫ + 1 from rfl]
  simp [pre₄, sndIdx]

/-- `last₄` recovers the second child `dq` stored by `andIntro s p q dp dq`.

No source; direct computation from the definition of `last₄`. -/
@[simp] lemma last₄_andIntro (s p q dp dq : V) : last₄ (andIntro s p q dp dq) = dq := by
  rw [show andIntro s p q dp dq = ⟪s, 2, p, q, dp, dq⟫ + 1 from rfl]
  simp [last₄, sndIdx]

/-- The rule tag of `orIntro s p q d` is `3`, the constructor's own tag.

No source; direct computation from the definition of `tag`. -/
@[simp] lemma tag_orIntro (s p q d : V) : tag (orIntro s p q d) = 3 := by
  rw [show orIntro s p q d = ⟪s, 3, p, q, d⟫ + 1 from rfl]
  simp [tag, sndIdx]

/-- `last₃` recovers the child `d` stored by `orIntro s p q d`.

No source; direct computation from the definition of `last₃`. -/
@[simp] lemma last₃_orIntro (s p q d : V) : last₃ (orIntro s p q d) = d := by
  rw [show orIntro s p q d = ⟪s, 3, p, q, d⟫ + 1 from rfl]
  simp [last₃, sndIdx]

/-- The rule tag of `allIntro s p d` is `4`, the constructor's own tag.

No source; direct computation from the definition of `tag`. -/
@[simp] lemma tag_allIntro (s p d : V) : tag (allIntro s p d) = 4 := by
  rw [show allIntro s p d = ⟪s, 4, p, d⟫ + 1 from rfl]
  simp [tag, sndIdx]

/-- `last₂` recovers the child `d` stored by `allIntro s p d`.

No source; direct computation from the definition of `last₂`. -/
@[simp] lemma last₂_allIntro (s p d : V) : last₂ (allIntro s p d) = d := by
  rw [show allIntro s p d = ⟪s, 4, p, d⟫ + 1 from rfl]
  simp [last₂, sndIdx]

/-- The rule tag of `exsIntro s p t d` is `5`, the constructor's own tag.

No source; direct computation from the definition of `tag`. -/
@[simp] lemma tag_exsIntro (s p t d : V) : tag (exsIntro s p t d) = 5 := by
  rw [show exsIntro s p t d = ⟪s, 5, p, t, d⟫ + 1 from rfl]
  simp [tag, sndIdx]

/-- `last₃` recovers the child `d` stored by `exsIntro s p t d`.

No source; direct computation from the definition of `last₃`. -/
@[simp] lemma last₃_exsIntro (s p t d : V) : last₃ (exsIntro s p t d) = d := by
  rw [show exsIntro s p t d = ⟪s, 5, p, t, d⟫ + 1 from rfl]
  simp [last₃, sndIdx]

/-- The rule tag of `wkRule s d` is `6`, the constructor's own tag.

No source; direct computation from the definition of `tag`. -/
@[simp] lemma tag_wkRule (s d : V) : tag (wkRule s d) = 6 := by
  rw [show wkRule s d = ⟪s, 6, d⟫ + 1 from rfl]
  simp [tag, sndIdx]

/-- `last₁` recovers the child `d` stored by `wkRule s d`.

No source; direct computation from the definition of `last₁`. -/
@[simp] lemma last₁_wkRule (s d : V) : last₁ (wkRule s d) = d := by
  rw [show wkRule s d = ⟪s, 6, d⟫ + 1 from rfl]
  simp [last₁, sndIdx]

/-- The rule tag of `shiftRule s d` is `7`, the constructor's own tag.

No source; direct computation from the definition of `tag`. -/
@[simp] lemma tag_shiftRule (s d : V) : tag (shiftRule s d) = 7 := by
  rw [show shiftRule s d = ⟪s, 7, d⟫ + 1 from rfl]
  simp [tag, sndIdx]

/-- `last₁` recovers the child `d` stored by `shiftRule s d`.

No source; direct computation from the definition of `last₁`. -/
@[simp] lemma last₁_shiftRule (s d : V) : last₁ (shiftRule s d) = d := by
  rw [show shiftRule s d = ⟪s, 7, d⟫ + 1 from rfl]
  simp [last₁, sndIdx]

/-- The rule tag of `cutRule s p d₁ d₂` is `8`, the constructor's own tag.

No source; direct computation from the definition of `tag`. -/
@[simp] lemma tag_cutRule (s p d₁ d₂ : V) : tag (cutRule s p d₁ d₂) = 8 := by
  rw [show cutRule s p d₁ d₂ = ⟪s, 8, p, d₁, d₂⟫ + 1 from rfl]
  simp [tag, sndIdx]

/-- `pre₃` recovers the first child `d₁` stored by `cutRule s p d₁ d₂`.

No source; direct computation from the definition of `pre₃`. -/
@[simp] lemma pre₃_cutRule (s p d₁ d₂ : V) : pre₃ (cutRule s p d₁ d₂) = d₁ := by
  rw [show cutRule s p d₁ d₂ = ⟪s, 8, p, d₁, d₂⟫ + 1 from rfl]
  simp [pre₃, sndIdx]

/-- `last₃` recovers the second child `d₂` stored by `cutRule s p d₁ d₂`.

No source; direct computation from the definition of `last₃`. -/
@[simp] lemma last₃_cutRule (s p d₁ d₂ : V) : last₃ (cutRule s p d₁ d₂) = d₂ := by
  rw [show cutRule s p d₁ d₂ = ⟪s, 8, p, d₁, d₂⟫ + 1 from rfl]
  simp [last₃, sndIdx]

/-- The rule tag of `axm s p` is `9`, the constructor's own tag.

No source; direct computation from the definition of `tag`. -/
@[simp] lemma tag_axm (s p : V) : tag (axm s p) = 9 := by
  rw [show axm s p = ⟪s, 9, p⟫ + 1 from rfl]
  simp [tag, sndIdx]

/-- The next height in the primitive-recursive history of an internal proof code, computed from
the history `ih` of the heights of all smaller codes.

- [Bus98, Ch. I §2.4] -/
noncomputable def nodeHeight (d ih : V) : V :=
  if tag d = 2 then max (znth ih (pre₄ d)) (znth ih (last₄ d)) + 1
  else if tag d = 3 then znth ih (last₃ d) + 1
  else if tag d = 4 then znth ih (last₂ d) + 1
  else if tag d = 5 then znth ih (last₃ d) + 1
  else if tag d = 6 then znth ih (last₁ d) + 1
  else if tag d = 7 then znth ih (last₁ d) + 1
  else if tag d = 8 then max (znth ih (pre₃ d)) (znth ih (last₃ d)) + 1
  else 0

/-- The `𝚺₁` graph of `nodeHeight`.

No source; a formalization device. -/
def nodeHeightGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “h d ih. (∃ t, !tagGraph t d ∧ t = 2 ∧ ∃ p, !pre₄Graph p d ∧ ∃ q, !last₄Graph q d ∧
      ∃ hp, !znthDef hp ih p ∧ ∃ hq, !znthDef hq ih q ∧ ∃ m, !max.dfn m hp hq ∧ h = m + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 3 ∧ ∃ p, !last₃Graph p d ∧ ∃ hp, !znthDef hp ih p ∧ h = hp + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 4 ∧ ∃ p, !last₂Graph p d ∧ ∃ hp, !znthDef hp ih p ∧ h = hp + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 5 ∧ ∃ p, !last₃Graph p d ∧ ∃ hp, !znthDef hp ih p ∧ h = hp + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 6 ∧ ∃ p, !last₁Graph p d ∧ ∃ hp, !znthDef hp ih p ∧ h = hp + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 7 ∧ ∃ p, !last₁Graph p d ∧ ∃ hp, !znthDef hp ih p ∧ h = hp + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 8 ∧ ∃ p, !pre₃Graph p d ∧ ∃ q, !last₃Graph q d ∧
      ∃ hp, !znthDef hp ih p ∧ ∃ hq, !znthDef hq ih q ∧ ∃ m, !max.dfn m hp hq ∧ h = m + 1) ∨
    (∃ t, !tagGraph t d ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ t ≠ 5 ∧ t ≠ 6 ∧ t ≠ 7 ∧ t ≠ 8 ∧ h = 0)”

/-- `nodeHeight` is `𝚺₁`-definable.

No source; a formalization device. -/
instance nodeHeight_def : 𝚺₁-Function₂[V] nodeHeight via nodeHeightGraph := .mk fun v ↦ by
  simp [nodeHeightGraph, nodeHeight]
  split_ifs <;> simp_all [numeral_eq_natCast]

/-- The primitive-recursion blueprint for `heightSeq`: it grows a sequence of heights, one entry
per code, by appending `nodeHeight` computed from the entries seen so far.

No source; a formalization device. -/
noncomputable def heightBlueprint : PR.Blueprint 0 where
  zero := .mkSigma “s. !seqConsDef s 0 0”
  succ := .mkSigma “y ih k. ∃ h, !nodeHeightGraph h (k + 1) ih ∧ !seqConsDef y ih h”

/-- The primitive-recursive construction underlying `heightSeq`.

No source; a formalization device. -/
noncomputable def heightConstruction : PR.Construction V heightBlueprint where
  zero _ := 0 ⁀' 0
  succ _ k ih := ih ⁀' nodeHeight (k + 1) ih
  zero_defined := .mk fun v ↦ by simp [heightBlueprint]
  succ_defined := .mk fun v ↦ by simp [heightBlueprint, nodeHeight_def.iff]

/-- The primitive-recursive history of heights through the internal code `d`. -/
noncomputable def heightSeq (d : V) : V := heightConstruction.result ![] d

/-- `heightSeq` at `0` is the length-one sequence holding a single height entry `0`.

No source; a formalization device. -/
@[simp] lemma heightSeq_zero : heightSeq (0 : V) = 0 ⁀' 0 := by
  simp [heightSeq, heightConstruction]

/-- `heightSeq` grows by appending the next node's height to the history seen so far.

No source; a formalization device. -/
@[simp] lemma heightSeq_succ (d : V) :
    heightSeq (d + 1) = heightSeq d ⁀' nodeHeight (d + 1) (heightSeq d) := by
  rw [heightSeq, heightConstruction.result_succ]
  rfl

/-- The `𝚺₁` graph of `heightSeq`.

No source; a formalization device. -/
noncomputable def heightSeqGraph : 𝚺₁.Semisentence 2 := heightBlueprint.resultDef

/-- `heightSeq` is `𝚺₁`-definable.

No source; a formalization device. -/
instance heightSeq_def : 𝚺₁-Function₁[V] heightSeq via heightSeqGraph := .mk fun v ↦ by
  have h := heightConstruction.result_defined_iff v
  have hv : (fun x : Fin 0 ↦ v x.succ.succ) = (![] : Fin 0 → V) := by
    ext x
    exact Fin.elim0 x
  have hv' : (fun _ : Fin 0 ↦ v 1) = (![] : Fin 0 → V) := by
    ext x
    exact Fin.elim0 x
  simpa [heightSeqGraph, heightSeq, heightBlueprint, hv, hv'] using h

/-- `heightSeq` is `𝚺₁`-definable.

No source; a formalization device. -/
instance heightSeq_definable : 𝚺₁-Function₁[V] heightSeq := heightSeq_def.to_definable

/-- The primitive-recursive height assigned to an internal proof code: the length of the longest
branch of the derivation `d` denotes, or `0` if `d` is not a proof-rule constructor.

- [Bus98, Ch. I §2.4] -/
noncomputable def height (d : V) : V := znth (heightSeq d) d

/-- The `𝚺₁` graph of `height`.

No source; a formalization device. -/
noncomputable def heightGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “h d. ∃ s, !heightBlueprint.resultDef s d ∧ !znthDef h s d”

/-- `height` is `𝚺₁`-definable.

No source; a formalization device. -/
instance height_def : 𝚺₁-Function₁[V] height via heightGraph := .mk fun v ↦ by
  have h (s d : V) : heightBlueprint.resultDef.val.Evalb ![s, d] ↔ s = heightSeq d := by
    have hparam : (fun _ : Fin 0 ↦ d) = (![] : Fin 0 → V) := by
      ext x
      exact Fin.elim0 x
    simpa [heightSeq, heightBlueprint, hparam] using
      (heightConstruction.result_defined_iff (![s, d] : Fin 2 → V) :
        heightBlueprint.resultDef.val.Evalb ![s, d] ↔
          s = heightConstruction.result (fun _ : Fin 0 ↦ d) d)
  simp [heightGraph, height, h]

/-- `height` is `𝚺₁`-definable.

No source; a formalization device. -/
instance height_definable : 𝚺₁-Function₁[V] height := height_def.to_definable

/-- `0` is not a proof-rule constructor, so its height is `0`.

No source; a formalization device. -/
@[simp] lemma height_zero : height (0 : V) = 0 := by
  have hzero : Seq (0 : V) := by simpa [emptyset_def] using (seq_empty : Seq (∅ : V))
  have hs : Seq (0 ⁀' 0 : V) := hzero.seqCons _
  have hm : ⟪0, 0⟫ ∈ (0 ⁀' 0 : V) := by
    have h : (0 : V) = ∅ := by simp [emptyset_def]
    have hl : lh (0 : V) = 0 := by
      calc
        lh (0 : V) = lh (∅ : V) := congrArg lh h
        _ = 0 := lh_empty
    have hp : (⟪0, 0⟫ : V) = ⟪lh (0 : V), 0⟫ := by
      congr 1
      exact hl.symm
    rw [hp]
    exact lh_mem_seqCons (0 : V) (0 : V)
  simpa [height, heightSeq, heightConstruction] using hs.znth_eq_of_mem hm

/-- `0` is a sequence, being the empty sequence in disguise.

No source; a formalization device. -/
private lemma seq_zero : Seq (0 : V) := by simpa [emptyset_def] using (seq_empty : Seq (∅ : V))

/-- `0` has length `0`, being the empty sequence in disguise.

No source; a formalization device. -/
private lemma lh_zero : lh (0 : V) = 0 := by
  simpa [emptyset_def] using (lh_empty : lh (∅ : V) = 0)

/-- `heightSeq d` is always a sequence.

No source; a formalization device. -/
private lemma heightSeq_seq (d : V) : Seq (heightSeq d) := by
  induction d using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using seq_zero.seqCons 0
  case succ d ih => simpa using ih.seqCons _

/-- `heightSeq d` has length `d + 1`: it records one height entry per code up to and including `d`.

No source; a formalization device. -/
private lemma lh_heightSeq (d : V) : lh (heightSeq d) = d + 1 := by
  induction d using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [heightSeq_zero, seq_zero.lh_seqCons 0, lh_zero]
  case succ d ih => rw [heightSeq_succ, (heightSeq_seq d).lh_seqCons _, ih]

/-- Consing onto a sequence does not change the values already recorded at indices below its
length.

No source; a formalization device. -/
private lemma znth_seqCons_of_lt {s z x : V} (H : Seq s) (hx : x < lh s) :
    znth (s ⁀' z) x = znth s x :=
  (H.seqCons z).znth_eq_of_mem (Seq.subset_seqCons s z (H.znth hx))

/-- Consing `z` onto a sequence `s` records `z` at the fresh index `lh s`.

No source; a formalization device. -/
private lemma znth_seqCons_lh {s z : V} (H : Seq s) : znth (s ⁀' z) (lh s) = z :=
  (H.seqCons z).znth_eq_of_mem (Seq.mem_seqCons s z)

/-- Every entry of `heightSeq d` at an index `x ≤ d` agrees with `height x`: extending the history
further never changes the height already recorded for a smaller code.

No source; a formalization device. -/
lemma znth_heightSeq_of_le {x d : V} (h : x ≤ d) : znth (heightSeq d) x = height x := by
  induction d using ISigma1.sigma1_succ_induction generalizing x
  · definability
  case zero =>
    rcases nonpos_iff_eq_zero.mp h with rfl
    rfl
  case succ d ih =>
    rcases le_iff_lt_or_eq.mp h with hlt | rfl
    · have hxd : x ≤ d := lt_succ_iff_le.mp hlt
      rw [heightSeq_succ, znth_seqCons_of_lt (heightSeq_seq d) (by rw [lh_heightSeq]; exact lt_succ_iff_le.mpr hxd)]
      exact ih hxd
    · rfl

/-- The height of a code built as the successor of `c` unfolds one primitive-recursion step: it is
`nodeHeight` applied to the history of heights up to `c`.

No source; a formalization device. -/
lemma height_succ (c : V) : height (c + 1) = nodeHeight (c + 1) (heightSeq c) := by
  have hmem : ⟪c + 1, nodeHeight (c + 1) (heightSeq c)⟫ ∈ heightSeq (c + 1) := by
    rw [heightSeq_succ, ← lh_heightSeq c]
    exact lh_mem_seqCons (heightSeq c) _
  simpa [height] using (heightSeq_seq (c + 1)).znth_eq_of_mem hmem

/-- As `height_succ`, stated for a code `d` known to be some `c + 1`, so that `rw` can unfold
`height d` while keeping `d` itself in constructor form for the rule-specific `tag`/`lastᵢ` simp
lemmas to fire.

No source; a formalization device. -/
private lemma height_eq_of_succ {c d : V} (h : c + 1 = d) : height d = nodeHeight d (heightSeq c) :=
  h ▸ height_succ c

/-- An axiom leaf has height `0`.

No source; direct computation from the definition of `height`. -/
@[simp] lemma height_axL (s p : V) : height (axL s p) = 0 := by
  rw [show axL s p = ⟪s, 0, p⟫ + 1 from rfl, height_succ]
  simp [nodeHeight, tag, sndIdx]

/-- A `⊤`-introduction leaf has height `0`.

No source; direct computation from the definition of `height`. -/
@[simp] lemma height_verumIntro (s : V) : height (verumIntro s) = 0 := by
  rw [show verumIntro s = ⟪s, 1, 0⟫ + 1 from rfl, height_succ]
  simp [nodeHeight, tag, sndIdx]

/-- A theory-axiom leaf has height `0`.

No source; direct computation from the definition of `height`. -/
@[simp] lemma height_axm (s p : V) : height (axm s p) = 0 := by
  rw [show axm s p = ⟪s, 9, p⟫ + 1 from rfl, height_succ]
  simp [nodeHeight, tag, sndIdx]

/-- An `∧`-introduction node's height is one more than the greater of its two children's heights.

No source; direct computation from the definition of `height`. -/
@[simp] lemma height_andIntro (s p q dp dq : V) :
    height (andIntro s p q dp dq) = max (height dp) (height dq) + 1 := by
  have hp : dp ≤ ⟪s, 2, p, q, dp, dq⟫ := lt_succ_iff_le.mp (dp_lt_andIntro s p q dp dq)
  have hq : dq ≤ ⟪s, 2, p, q, dp, dq⟫ := lt_succ_iff_le.mp (dq_lt_andIntro s p q dp dq)
  rw [height_eq_of_succ (c := ⟪s, 2, p, q, dp, dq⟫) (d := andIntro s p q dp dq) rfl]
  simp [nodeHeight, znth_heightSeq_of_le hp, znth_heightSeq_of_le hq]

/-- An `∨`-introduction node's height is one more than its child's height.

No source; direct computation from the definition of `height`. -/
@[simp] lemma height_orIntro (s p q d : V) : height (orIntro s p q d) = height d + 1 := by
  have hd : d ≤ ⟪s, 3, p, q, d⟫ := lt_succ_iff_le.mp (d_lt_orIntro s p q d)
  rw [height_eq_of_succ (c := ⟪s, 3, p, q, d⟫) (d := orIntro s p q d) rfl]
  simp [nodeHeight, znth_heightSeq_of_le hd]

/-- A `∀`-introduction node's height is one more than its child's height.

No source; direct computation from the definition of `height`. -/
@[simp] lemma height_allIntro (s p d : V) : height (allIntro s p d) = height d + 1 := by
  have hd : d ≤ ⟪s, 4, p, d⟫ := lt_succ_iff_le.mp (s_lt_allIntro s p d)
  rw [height_eq_of_succ (c := ⟪s, 4, p, d⟫) (d := allIntro s p d) rfl]
  simp [nodeHeight, znth_heightSeq_of_le hd]

/-- An `∃`-introduction node's height is one more than its child's height.

No source; direct computation from the definition of `height`. -/
@[simp] lemma height_exsIntro (s p t d : V) : height (exsIntro s p t d) = height d + 1 := by
  have hd : d ≤ ⟪s, 5, p, t, d⟫ := lt_succ_iff_le.mp (d_lt_exsIntro s p t d)
  rw [height_eq_of_succ (c := ⟪s, 5, p, t, d⟫) (d := exsIntro s p t d) rfl]
  simp [nodeHeight, znth_heightSeq_of_le hd]

/-- A weakening node's height is one more than its child's height.

No source; direct computation from the definition of `height`. -/
@[simp] lemma height_wkRule (s d : V) : height (wkRule s d) = height d + 1 := by
  have hd : d ≤ ⟪s, 6, d⟫ := lt_succ_iff_le.mp (d_lt_wkRule s d)
  rw [height_eq_of_succ (c := ⟪s, 6, d⟫) (d := wkRule s d) rfl]
  simp [nodeHeight, znth_heightSeq_of_le hd]

/-- A shift node's height is one more than its child's height.

No source; direct computation from the definition of `height`. -/
@[simp] lemma height_shiftRule (s d : V) : height (shiftRule s d) = height d + 1 := by
  have hd : d ≤ ⟪s, 7, d⟫ := lt_succ_iff_le.mp (d_lt_shiftRule s d)
  rw [height_eq_of_succ (c := ⟪s, 7, d⟫) (d := shiftRule s d) rfl]
  simp [nodeHeight, znth_heightSeq_of_le hd]

/-- A cut node's height is one more than the greater of its two children's heights.

No source; direct computation from the definition of `height`. -/
@[simp] lemma height_cutRule (s p d₁ d₂ : V) :
    height (cutRule s p d₁ d₂) = max (height d₁) (height d₂) + 1 := by
  have h₁ : d₁ ≤ ⟪s, 8, p, d₁, d₂⟫ := lt_succ_iff_le.mp (d₁_lt_cutRule s p d₁ d₂)
  have h₂ : d₂ ≤ ⟪s, 8, p, d₁, d₂⟫ := lt_succ_iff_le.mp (d₂_lt_cutRule s p d₁ d₂)
  rw [height_eq_of_succ (c := ⟪s, 8, p, d₁, d₂⟫) (d := cutRule s p d₁ d₂) rfl]
  simp [nodeHeight, znth_heightSeq_of_le h₁, znth_heightSeq_of_le h₂]

/-- The first component of the middle pair stored by `cutRule`, i.e. its cut formula `p`. -/
noncomputable def pre₂ (d : V) : V := π₁ (π₂ (sndIdx d))

/-- The `𝚺₁` graph of `pre₂`. -/
def pre₂Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧ !pi₁Def a q”

/-- `pre₂` is `𝚺₁`-definable. -/
instance pre₂_def : 𝚺₁-Function₁[V] pre₂ via pre₂Graph := .mk fun v ↦ by
  simp [pre₂Graph, pre₂]

/-- `pre₂` recovers the cut formula `p` stored by `cutRule s p d₁ d₂`. -/
@[simp] lemma pre₂_cutRule (s p d₁ d₂ : V) : pre₂ (cutRule s p d₁ d₂) = p := by
  rw [show cutRule s p d₁ d₂ = ⟪s, 8, p, d₁, d₂⟫ + 1 from rfl]
  simp [pre₂, sndIdx]

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

/-- The `𝚺₁` graph of `nodeCutRank`. -/
noncomputable def nodeCutRankGraph : 𝚺₁.Semisentence 3 := .mkSigma
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

/-- `nodeCutRank` is `𝚺₁`-definable. -/
instance nodeCutRank_def :
    𝚺₁-Function₂[V] nodeCutRank L via nodeCutRankGraph L := .mk fun v ↦ by
  simp [nodeCutRankGraph, nodeCutRank, (formulaComplexity.defined (L := L) (V := V)).iff]
  have h₂₅ : (2 : V) ≠ ORingStructure.numeral 5 := by simp [numeral_eq_natCast]
  have h₂₆ : (2 : V) ≠ ORingStructure.numeral 6 := by simp [numeral_eq_natCast]
  have h₂₇ : (2 : V) ≠ ORingStructure.numeral 7 := by simp [numeral_eq_natCast]
  have h₂₈ : (2 : V) ≠ ORingStructure.numeral 8 := by simp [numeral_eq_natCast]
  have h₃₅ : (3 : V) ≠ ORingStructure.numeral 5 := by simp [numeral_eq_natCast]
  have h₃₆ : (3 : V) ≠ ORingStructure.numeral 6 := by simp [numeral_eq_natCast]
  have h₃₇ : (3 : V) ≠ ORingStructure.numeral 7 := by simp [numeral_eq_natCast]
  have h₃₈ : (3 : V) ≠ ORingStructure.numeral 8 := by simp [numeral_eq_natCast]
  have h₄₅ : (4 : V) ≠ ORingStructure.numeral 5 := by simp [numeral_eq_natCast]
  have h₄₆ : (4 : V) ≠ ORingStructure.numeral 6 := by simp [numeral_eq_natCast]
  have h₄₇ : (4 : V) ≠ ORingStructure.numeral 7 := by simp [numeral_eq_natCast]
  have h₄₈ : (4 : V) ≠ ORingStructure.numeral 8 := by simp [numeral_eq_natCast]
  have h₅₆ : (5 : V) ≠ ORingStructure.numeral 6 := by simp [numeral_eq_natCast]
  have h₅₇ : (5 : V) ≠ ORingStructure.numeral 7 := by simp [numeral_eq_natCast]
  have h₅₈ : (5 : V) ≠ ORingStructure.numeral 8 := by simp [numeral_eq_natCast]
  have h₆₇ : (6 : V) ≠ ORingStructure.numeral 7 := by simp [numeral_eq_natCast]
  have h₆₈ : (6 : V) ≠ ORingStructure.numeral 8 := by simp [numeral_eq_natCast]
  have h₇₈ : (7 : V) ≠ ORingStructure.numeral 8 := by simp [numeral_eq_natCast]
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

variable {L}

/-- `cutRankSeq` at `0` is the length-one sequence holding a single cut rank entry `0`. -/
@[simp] lemma cutRankSeq_zero : cutRankSeq L (0 : V) = 0 ⁀' 0 := by
  simp [cutRankSeq, cutRankConstruction]

/-- `cutRankSeq` grows by appending the next node's cut rank to the history seen so far. -/
@[simp] lemma cutRankSeq_succ (d : V) :
    cutRankSeq L (d + 1) = cutRankSeq L d ⁀' nodeCutRank L (d + 1) (cutRankSeq L d) := by
  rw [cutRankSeq, (cutRankConstruction L).result_succ]
  rfl

variable (L)

/-- The `𝚺₁` graph of `cutRankSeq`. -/
noncomputable def cutRankSeqGraph : 𝚺₁.Semisentence 2 := (cutRankBlueprint L).resultDef

variable {L}

/-- `cutRankSeq` is `𝚺₁`-definable. -/
instance cutRankSeq_def : 𝚺₁-Function₁[V] cutRankSeq L via cutRankSeqGraph L := .mk fun v ↦ by
  have h := (cutRankConstruction L).result_defined_iff (V := V) v
  have hv : (fun x : Fin 0 ↦ v x.succ.succ) = (![] : Fin 0 → V) := by
    ext x
    exact Fin.elim0 x
  have hv' : (fun _ : Fin 0 ↦ v 1) = (![] : Fin 0 → V) := by
    ext x
    exact Fin.elim0 x
  simpa [cutRankSeqGraph, cutRankSeq, cutRankBlueprint, hv, hv'] using h

/-- `cutRankSeq` is `𝚺₁`-definable. -/
instance cutRankSeq_definable : 𝚺₁-Function₁[V] cutRankSeq L := cutRankSeq_def.to_definable

variable (L)

/-- The primitive-recursive cut rank assigned to an internal proof code: one more than the greatest
complexity of a formula cut on in `d`, and `0` when `d` cuts on nothing.

- [Bus98, Ch. I §2.4] -/
noncomputable def cutRank (d : V) : V := znth (cutRankSeq L d) d

/-- The `𝚺₁` graph of `cutRank`. -/
noncomputable def cutRankGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “r d. ∃ s, !(cutRankBlueprint L).resultDef s d ∧ !znthDef r s d”

variable {L}

/-- `cutRank` is `𝚺₁`-definable. -/
instance cutRank_def : 𝚺₁-Function₁[V] cutRank L via cutRankGraph L := .mk fun v ↦ by
  have h (s d : V) : (cutRankBlueprint L).resultDef.val.Evalb ![s, d] ↔ s = cutRankSeq L d := by
    have hparam : (fun _ : Fin 0 ↦ d) = (![] : Fin 0 → V) := by
      ext x
      exact Fin.elim0 x
    simpa [cutRankSeq, cutRankBlueprint, hparam] using
      ((cutRankConstruction L).result_defined_iff (![s, d] : Fin 2 → V) :
        (cutRankBlueprint L).resultDef.val.Evalb ![s, d] ↔
          s = (cutRankConstruction L).result (fun _ : Fin 0 ↦ d) d)
  simp [cutRankGraph, cutRank, h]

/-- `cutRank` is `𝚺₁`-definable. -/
instance cutRank_definable : 𝚺₁-Function₁[V] cutRank L := cutRank_def.to_definable

/-- `cutRankSeq d` is always a sequence. -/
private lemma cutRankSeq_seq (d : V) : Seq (cutRankSeq L d) := by
  induction d using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using seq_zero.seqCons 0
  case succ d ih => simpa using ih.seqCons _

/-- `cutRankSeq d` has length `d + 1`: it records one cut rank entry per code up to and including
`d`. -/
private lemma lh_cutRankSeq (d : V) : lh (cutRankSeq L d) = d + 1 := by
  induction d using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [cutRankSeq_zero, seq_zero.lh_seqCons 0, lh_zero]
  case succ d ih => rw [cutRankSeq_succ, (cutRankSeq_seq (L := L) d).lh_seqCons _, ih]

/-- Every entry of `cutRankSeq d` at an index `x ≤ d` agrees with `cutRank x`: extending the
history further never changes the cut rank already recorded for a smaller code. -/
lemma znth_cutRankSeq_of_le {x d : V} (h : x ≤ d) : znth (cutRankSeq L d) x = cutRank L x := by
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
lemma cutRank_succ (c : V) : cutRank L (c + 1) = nodeCutRank L (c + 1) (cutRankSeq L c) := by
  have hmem : ⟪c + 1, nodeCutRank L (c + 1) (cutRankSeq L c)⟫ ∈ cutRankSeq L (c + 1) := by
    rw [cutRankSeq_succ, ← lh_cutRankSeq (L := L) c]
    exact lh_mem_seqCons (cutRankSeq L c) _
  simpa [cutRank] using (cutRankSeq_seq (L := L) (c + 1)).znth_eq_of_mem hmem

/-- An axiom leaf cuts on nothing, so its cut rank is `0`. -/
@[simp] lemma cutRank_axL (s p : V) : cutRank L (axL s p) = 0 := by
  rw [show axL s p = ⟪s, 0, p⟫ + 1 from rfl, cutRank_succ]
  simp [nodeCutRank, tag, sndIdx]

/-- A `⊤`-introduction leaf cuts on nothing, so its cut rank is `0`. -/
@[simp] lemma cutRank_verumIntro (s : V) : cutRank L (verumIntro s) = 0 := by
  rw [show verumIntro s = ⟪s, 1, 0⟫ + 1 from rfl, cutRank_succ]
  simp [nodeCutRank, tag, sndIdx]

/-- A theory-axiom leaf cuts on nothing, so its cut rank is `0`. -/
@[simp] lemma cutRank_axm (s p : V) : cutRank L (axm s p) = 0 := by
  rw [show axm s p = ⟪s, 9, p⟫ + 1 from rfl, cutRank_succ]
  simp [nodeCutRank, tag, sndIdx]

/-- An `∧`-introduction node's cut rank is the greater of its two children's cut ranks. -/
@[simp] lemma cutRank_andIntro (s p q dp dq : V) :
    cutRank L (andIntro s p q dp dq) = max (cutRank L dp) (cutRank L dq) := by
  have hp : dp ≤ ⟪s, 2, p, q, dp, dq⟫ := lt_succ_iff_le.mp (dp_lt_andIntro s p q dp dq)
  have hq : dq ≤ ⟪s, 2, p, q, dp, dq⟫ := lt_succ_iff_le.mp (dq_lt_andIntro s p q dp dq)
  have h := cutRank_succ (L := L) (⟪s, 2, p, q, dp, dq⟫ : V)
  rw [show (⟪s, 2, p, q, dp, dq⟫ : V) + 1 = andIntro s p q dp dq from rfl] at h
  rw [h]
  simp [nodeCutRank, znth_cutRankSeq_of_le hp, znth_cutRankSeq_of_le hq]

/-- An `∨`-introduction node's cut rank is its child's cut rank. -/
@[simp] lemma cutRank_orIntro (s p q d : V) : cutRank L (orIntro s p q d) = cutRank L d := by
  have hd : d ≤ ⟪s, 3, p, q, d⟫ := lt_succ_iff_le.mp (d_lt_orIntro s p q d)
  have h := cutRank_succ (L := L) (⟪s, 3, p, q, d⟫ : V)
  rw [show (⟪s, 3, p, q, d⟫ : V) + 1 = orIntro s p q d from rfl] at h
  rw [h]
  simp [nodeCutRank, znth_cutRankSeq_of_le hd]

/-- A `∀`-introduction node's cut rank is its child's cut rank. -/
@[simp] lemma cutRank_allIntro (s p d : V) : cutRank L (allIntro s p d) = cutRank L d := by
  have hd : d ≤ ⟪s, 4, p, d⟫ := lt_succ_iff_le.mp (s_lt_allIntro s p d)
  have h := cutRank_succ (L := L) (⟪s, 4, p, d⟫ : V)
  rw [show (⟪s, 4, p, d⟫ : V) + 1 = allIntro s p d from rfl] at h
  rw [h]
  simp [nodeCutRank, znth_cutRankSeq_of_le hd]

/-- An `∃`-introduction node's cut rank is its child's cut rank. -/
@[simp] lemma cutRank_exsIntro (s p t d : V) : cutRank L (exsIntro s p t d) = cutRank L d := by
  have hd : d ≤ ⟪s, 5, p, t, d⟫ := lt_succ_iff_le.mp (d_lt_exsIntro s p t d)
  have h := cutRank_succ (L := L) (⟪s, 5, p, t, d⟫ : V)
  rw [show (⟪s, 5, p, t, d⟫ : V) + 1 = exsIntro s p t d from rfl] at h
  rw [h]
  simp [nodeCutRank, znth_cutRankSeq_of_le hd]

/-- A weakening node's cut rank is its child's cut rank. -/
@[simp] lemma cutRank_wkRule (s d : V) : cutRank L (wkRule s d) = cutRank L d := by
  have hd : d ≤ ⟪s, 6, d⟫ := lt_succ_iff_le.mp (d_lt_wkRule s d)
  have h := cutRank_succ (L := L) (⟪s, 6, d⟫ : V)
  rw [show (⟪s, 6, d⟫ : V) + 1 = wkRule s d from rfl] at h
  rw [h]
  simp [nodeCutRank, znth_cutRankSeq_of_le hd]

/-- A shift node's cut rank is its child's cut rank. -/
@[simp] lemma cutRank_shiftRule (s d : V) : cutRank L (shiftRule s d) = cutRank L d := by
  have hd : d ≤ ⟪s, 7, d⟫ := lt_succ_iff_le.mp (d_lt_shiftRule s d)
  have h := cutRank_succ (L := L) (⟪s, 7, d⟫ : V)
  rw [show (⟪s, 7, d⟫ : V) + 1 = shiftRule s d from rfl] at h
  rw [h]
  simp [nodeCutRank, znth_cutRankSeq_of_le hd]

/-- A cut node's cut rank is the greater of its two children's cut ranks and one more than the
complexity of its cut formula. -/
@[simp] lemma cutRank_cutRule (s p d₁ d₂ : V) :
    cutRank L (cutRule s p d₁ d₂) =
      max (max (cutRank L d₁) (cutRank L d₂)) (formulaComplexity L p + 1) := by
  have h₁ : d₁ ≤ ⟪s, 8, p, d₁, d₂⟫ := lt_succ_iff_le.mp (d₁_lt_cutRule s p d₁ d₂)
  have h₂ : d₂ ≤ ⟪s, 8, p, d₁, d₂⟫ := lt_succ_iff_le.mp (d₂_lt_cutRule s p d₁ d₂)
  have h := cutRank_succ (L := L) (⟪s, 8, p, d₁, d₂⟫ : V)
  rw [show (⟪s, 8, p, d₁, d₂⟫ : V) + 1 = cutRule s p d₁ d₂ from rfl] at h
  rw [h]
  simp [nodeCutRank, znth_cutRankSeq_of_le h₁, znth_cutRankSeq_of_le h₂]

end InternalMeasures

end LO.FirstOrder.Arithmetic.Bootstrapping
