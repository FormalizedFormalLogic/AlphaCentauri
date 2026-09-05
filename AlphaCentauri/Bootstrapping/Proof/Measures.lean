module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic

/-!
# Internal proof measures

This module defines a primitive-recursive height function on internal proof codes.  It is total
on all codes; on codes that are not proof-rule constructors its value is zero.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace InternalMeasures

/-- The rule tag stored in a proof-rule constructor code, i.e. the first component of `sndIdx d`.

No source; a formalization device for reading off the constructor used to build `d`. -/
noncomputable def tag (d : V) : V := π₁ (sndIdx d)

/-- The first stored argument of a proof-rule constructor code, after its rule tag.

No source; a formalization device. -/
noncomputable def arg₁ (d : V) : V := π₁ (π₂ (sndIdx d))

/-- The second stored argument of a proof-rule constructor code, after its rule tag.

No source; a formalization device. -/
noncomputable def arg₂ (d : V) : V := π₁ (π₂ (π₂ (sndIdx d)))

/-- The third stored argument of a proof-rule constructor code, after its rule tag.

No source; a formalization device. -/
noncomputable def arg₃ (d : V) : V := π₁ (π₂ (π₂ (π₂ (sndIdx d))))

/-- The fourth stored argument of a proof-rule constructor code, after its rule tag.

No source; a formalization device. -/
noncomputable def arg₄ (d : V) : V := π₁ (π₂ (π₂ (π₂ (π₂ (sndIdx d)))))

/-- The `𝚺₁` graph of `tag`.

No source; a formalization device. -/
def tagGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “t d. ∃ r, !sndIdxDef r d ∧ !pi₁Def t r”

/-- The `𝚺₁` graph of `arg₁`.

No source; a formalization device. -/
def arg₁Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧ !pi₁Def a q”

/-- The `𝚺₁` graph of `arg₂`.

No source; a formalization device. -/
def arg₂Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ !pi₁Def a q'”

/-- The `𝚺₁` graph of `arg₃`.

No source; a formalization device. -/
def arg₃Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ ∃ q'', !pi₂Def q'' q' ∧ !pi₁Def a q''”

/-- The `𝚺₁` graph of `arg₄`.

No source; a formalization device. -/
def arg₄Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ ∃ q'', !pi₂Def q'' q' ∧
    ∃ q''', !pi₂Def q''' q'' ∧ !pi₁Def a q'''”

/-- `tag` is `𝚺₁`-definable.

No source; a formalization device. -/
instance tag_def : 𝚺₁-Function₁[V] tag via tagGraph := .mk fun v ↦ by
  simp [tagGraph, tag]

/-- `arg₁` is `𝚺₁`-definable.

No source; a formalization device. -/
instance arg₁_def : 𝚺₁-Function₁[V] arg₁ via arg₁Graph := .mk fun v ↦ by
  simp [arg₁Graph, arg₁]

/-- `arg₂` is `𝚺₁`-definable.

No source; a formalization device. -/
instance arg₂_def : 𝚺₁-Function₁[V] arg₂ via arg₂Graph := .mk fun v ↦ by
  simp [arg₂Graph, arg₂]

/-- `arg₃` is `𝚺₁`-definable.

No source; a formalization device. -/
instance arg₃_def : 𝚺₁-Function₁[V] arg₃ via arg₃Graph := .mk fun v ↦ by
  simp [arg₃Graph, arg₃]

/-- `arg₄` is `𝚺₁`-definable.

No source; a formalization device. -/
instance arg₄_def : 𝚺₁-Function₁[V] arg₄ via arg₄Graph := .mk fun v ↦ by
  simp [arg₄Graph, arg₄]

/-- The next height in the primitive-recursive history of an internal proof code, computed from
the history `ih` of the heights of all smaller codes.

This is the standard structural height of a one-sided sequent-calculus derivation; no citation is
given because the reference this repository would cite (Buss, *An Introduction to Proof Theory*,
key `Bus98`) is not yet registered in `references.yml`. -/
noncomputable def nodeHeight (d ih : V) : V :=
  if tag d = 2 then max (znth ih (arg₃ d)) (znth ih (arg₄ d)) + 1
  else if tag d = 3 then znth ih (arg₃ d) + 1
  else if tag d = 4 then znth ih (arg₂ d) + 1
  else if tag d = 5 then znth ih (arg₃ d) + 1
  else if tag d = 6 then znth ih (arg₂ d) + 1
  else if tag d = 7 then znth ih (arg₂ d) + 1
  else if tag d = 8 then max (znth ih (arg₃ d)) (znth ih (arg₄ d)) + 1
  else 0

/-- The `𝚺₁` graph of `nodeHeight`.

No source; a formalization device. -/
def nodeHeightGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “h d ih. (∃ t, !tagGraph t d ∧ t = 2 ∧ ∃ p, !arg₃Graph p d ∧ ∃ q, !arg₄Graph q d ∧
      ∃ hp, !znthDef hp ih p ∧ ∃ hq, !znthDef hq ih q ∧ ∃ m, !max.dfn m hp hq ∧ h = m + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 3 ∧ ∃ p, !arg₃Graph p d ∧ ∃ hp, !znthDef hp ih p ∧ h = hp + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 4 ∧ ∃ p, !arg₂Graph p d ∧ ∃ hp, !znthDef hp ih p ∧ h = hp + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 5 ∧ ∃ p, !arg₃Graph p d ∧ ∃ hp, !znthDef hp ih p ∧ h = hp + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 6 ∧ ∃ p, !arg₂Graph p d ∧ ∃ hp, !znthDef hp ih p ∧ h = hp + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 7 ∧ ∃ p, !arg₂Graph p d ∧ ∃ hp, !znthDef hp ih p ∧ h = hp + 1) ∨
    (∃ t, !tagGraph t d ∧ t = 8 ∧ ∃ p, !arg₃Graph p d ∧ ∃ q, !arg₄Graph q d ∧
      ∃ hp, !znthDef hp ih p ∧ ∃ hq, !znthDef hq ih q ∧ ∃ m, !max.dfn m hp hq ∧ h = m + 1) ∨
    (∃ t, !tagGraph t d ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ t ≠ 5 ∧ t ≠ 6 ∧ t ≠ 7 ∧ t ≠ 8 ∧ h = 0)”

/-- `nodeHeight` is `𝚺₁`-definable.

No source; a formalization device. -/
instance nodeHeight_def : 𝚺₁-Function₂[V] nodeHeight via nodeHeightGraph := .mk fun v ↦ by
  simp [nodeHeightGraph, nodeHeight]
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

This is the standard structural height of a one-sided sequent-calculus derivation; no citation is
given because the reference this repository would cite (Buss, *An Introduction to Proof Theory*,
key `Bus98`) is not yet registered in `references.yml`. -/
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

end InternalMeasures

end LO.FirstOrder.Arithmetic.Bootstrapping
