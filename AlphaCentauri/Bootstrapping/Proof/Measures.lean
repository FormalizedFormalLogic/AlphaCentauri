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

noncomputable def tag (d : V) : V := π₁ (sndIdx d)

noncomputable def arg₁ (d : V) : V := π₁ (π₂ (sndIdx d))

noncomputable def arg₂ (d : V) : V := π₁ (π₂ (π₂ (sndIdx d)))

noncomputable def arg₃ (d : V) : V := π₁ (π₂ (π₂ (π₂ (sndIdx d))))

noncomputable def arg₄ (d : V) : V := π₁ (π₂ (π₂ (π₂ (π₂ (sndIdx d)))))

def tagGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “t d. ∃ r, !sndIdxDef r d ∧ !pi₁Def t r”

def arg₁Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧ !pi₁Def a q”

def arg₂Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ !pi₁Def a q'”

def arg₃Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ ∃ q'', !pi₂Def q'' q' ∧ !pi₁Def a q''”

def arg₄Graph : 𝚺₁.Semisentence 2 := .mkSigma
  “a d. ∃ r, !sndIdxDef r d ∧ ∃ q, !pi₂Def q r ∧
    ∃ q', !pi₂Def q' q ∧ ∃ q'', !pi₂Def q'' q' ∧
    ∃ q''', !pi₂Def q''' q'' ∧ !pi₁Def a q'''”

instance tag_def : 𝚺₁-Function₁[V] tag via tagGraph := .mk fun v ↦ by
  simp [tagGraph, tag]

instance arg₁_def : 𝚺₁-Function₁[V] arg₁ via arg₁Graph := .mk fun v ↦ by
  simp [arg₁Graph, arg₁]

instance arg₂_def : 𝚺₁-Function₁[V] arg₂ via arg₂Graph := .mk fun v ↦ by
  simp [arg₂Graph, arg₂]

instance arg₃_def : 𝚺₁-Function₁[V] arg₃ via arg₃Graph := .mk fun v ↦ by
  simp [arg₃Graph, arg₃]

instance arg₄_def : 𝚺₁-Function₁[V] arg₄ via arg₄Graph := .mk fun v ↦ by
  simp [arg₄Graph, arg₄]

/-- The next height in the primitive-recursive history of an internal proof code. -/
noncomputable def nodeHeight (d ih : V) : V :=
  if tag d = 2 then max (znth ih (arg₃ d)) (znth ih (arg₄ d)) + 1
  else if tag d = 3 then znth ih (arg₃ d) + 1
  else if tag d = 4 then znth ih (arg₂ d) + 1
  else if tag d = 5 then znth ih (arg₃ d) + 1
  else if tag d = 6 then znth ih (arg₂ d) + 1
  else if tag d = 7 then znth ih (arg₂ d) + 1
  else if tag d = 8 then max (znth ih (arg₃ d)) (znth ih (arg₄ d)) + 1
  else 0

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

noncomputable def heightBlueprint : PR.Blueprint 0 where
  zero := .mkSigma “s. !seqConsDef s 0 0”
  succ := .mkSigma “y ih k. ∃ h, !nodeHeightGraph h (k + 1) ih ∧ !seqConsDef y ih h”

noncomputable def heightConstruction : PR.Construction V heightBlueprint where
  zero _ := 0 ⁀' 0
  succ _ k ih := ih ⁀' nodeHeight (k + 1) ih
  zero_defined := .mk fun v ↦ by simp [heightBlueprint]
  succ_defined := .mk fun v ↦ by simp [heightBlueprint, nodeHeight_def.iff]

/-- The primitive-recursive history of heights through the internal code `d`. -/
noncomputable def heightSeq (d : V) : V := heightConstruction.result ![] d

@[simp] lemma heightSeq_zero : heightSeq (0 : V) = 0 ⁀' 0 := by
  simp [heightSeq, heightConstruction]

@[simp] lemma heightSeq_succ (d : V) :
    heightSeq (d + 1) = heightSeq d ⁀' nodeHeight (d + 1) (heightSeq d) := by
  rw [heightSeq, heightConstruction.result_succ]
  rfl

noncomputable def heightSeqGraph : 𝚺₁.Semisentence 2 := heightBlueprint.resultDef

instance heightSeq_def : 𝚺₁-Function₁[V] heightSeq via heightSeqGraph := .mk fun v ↦ by
  have h := heightConstruction.result_defined_iff v
  have hv : (fun x : Fin 0 ↦ v x.succ.succ) = (![] : Fin 0 → V) := by
    ext x
    exact Fin.elim0 x
  have hv' : (fun _ : Fin 0 ↦ v 1) = (![] : Fin 0 → V) := by
    ext x
    exact Fin.elim0 x
  simpa [heightSeqGraph, heightSeq, heightBlueprint, hv, hv'] using h

/-- The primitive-recursive height assigned to an internal proof code. -/
noncomputable def height (d : V) : V := znth (heightSeq d) d

noncomputable def heightGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “h d. ∃ s, !heightBlueprint.resultDef s d ∧ !znthDef h s d”

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

end InternalMeasures

end LO.FirstOrder.Arithmetic.Bootstrapping
