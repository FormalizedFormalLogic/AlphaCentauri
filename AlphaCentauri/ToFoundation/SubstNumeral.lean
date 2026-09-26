module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.FixedPoint

/-!
# Numeral substitution

The internal function that substitutes the numeral of a code into a formula with one free
variable, iterated a given number of times, and a $\Delta_1$ presentation of the set of numeral
instances of a formula with one free variable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma substNumeral_app_natCast (σ : ArithmeticSemisentence 1) (n : ℕ) :
    substNumeral ⌜σ⌝ (n : V) = ⌜(σ/[↑n] : ArithmeticSentence)⌝ := by
  simp [substNumeral, Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_subst_eq_subst_coe₁]

section substNumeralItr

namespace SubstNumeralItr

noncomputable def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y p a. y = a”
  succ := .mkSigma
    “y ih n p a. ∃ m, !numeralGraph m ih ∧ ∃ v, !adjoinDef v m 0 ∧ !(substsGraph ℒₒᵣ) y v p”

noncomputable def construction : PR.Construction V blueprint where
  zero v := v 1
  succ v _ ih := substNumeral (v 0) ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, substNumeral]

end SubstNumeralItr

open SubstNumeralItr

/-- `substNumeralItr p a k` starts from `a` and, `k` times, substitutes the numeral of the current
value into `p`. -/
noncomputable def substNumeralItr (p a k : V) : V := construction.result ![p, a] k

@[simp] lemma substNumeralItr_zero (p a : V) : substNumeralItr p a 0 = a := by
  simp [substNumeralItr, construction]

@[simp] lemma substNumeralItr_succ (p a k : V) :
    substNumeralItr p a (k + 1) = substNumeral p (substNumeralItr p a k) := by
  simp [substNumeralItr, construction]

noncomputable def _root_.FFL.FirstOrder.Arithmetic.substNumeralItrDef : 𝚺₁.Semisentence 4 :=
  blueprint.resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

instance substNumeralItr.defined :
    𝚺₁-Function₃[V] substNumeralItr via substNumeralItrDef := .mk fun v ↦ by
  simp [construction.result_defined_iff, substNumeralItrDef, substNumeralItr]

instance substNumeralItr.definable : 𝚺₁-Function₃ (substNumeralItr : V → V → V → V) :=
  substNumeralItr.defined.to_definable

lemma substNumeralItr_quote (σ : ArithmeticSemisentence 1) (π : ArithmeticSentence) (k : ℕ) :
    substNumeralItr (⌜σ⌝ : V) ⌜π⌝ (k : V) =
      ⌜(fun π : ArithmeticSentence ↦ (σ/[⌜π⌝] : ArithmeticSentence))^[k] π⌝ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, substNumeralItr_succ, ih, Function.iterate_succ_apply']
    simpa [Sentence.coe_quote_eq_quote] using substNumeral_app_natCast (V := V) σ
      ⌜(fun π : ArithmeticSentence ↦ (σ/[⌜π⌝] : ArithmeticSentence))^[k] π⌝

end substNumeralItr

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Theory.Δ₁

open Arithmetic Arithmetic.HierarchySymbol.Semiformula Arithmetic.Bootstrapping
  Arithmetic.Bootstrapping.Arithmetic

variable (φ : ArithmeticSemisentence 1)

/-- The recognizer of the codes of the numeral instances `φ/[↑n]`. -/
noncomputable def numeralInstancesCh : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “x. ∃ n <⁺ x, !ssnum x ↑(⌜φ⌝ : ℕ) n”)
  (.mkPi “x. ∃ n <⁺ x, ∀ y, !ssnum y ↑(⌜φ⌝ : ℕ) n → x = y”)

/-- The numeral instances of `φ` form a $\Delta_1$-presented theory, provided the code of each
instance `φ/[↑n]` is at least `n`. -/
noncomputable abbrev numeralInstances
    (hφ : ∀ n : ℕ, n ≤ (⌜(φ/[↑n] : ArithmeticSentence)⌝ : ℕ)) :
    Theory.Δ₁ (Set.range fun n : ℕ ↦ (φ/[↑n] : ArithmeticSentence)) where
  ch := numeralInstancesCh φ
  mem_iff ψ := by
    have h (n : ℕ) : substNumeral (⌜φ⌝ : ℕ) n = ⌜(φ/[↑n] : ArithmeticSentence)⌝ := by
      simpa using substNumeral_app_natCast (V := ℕ) φ n
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, numeralInstancesCh, Fin.Fin1.eq_one,
      Fin.isValue, Sentence.coe_quote, val_mkDelta, val_mkSigma, eval_bexsLTSucc',
      Semiterm.val_bvar, Matrix.cons_val_fin_one, Semiformula.eval_substs, Matrix.comp₃,
      Matrix.cons_val_one, Sentence.val_quote, Matrix.cons_val_zero, HierarchySymbol.Defined.iff,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_app_two, h, Set.mem_range,
      exists_exists_eq_and]
    constructor
    · rintro ⟨n, -, hn⟩
      exact ⟨n, (Semiformula.quote_inj_iff (V := ℕ)).mp hn⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, Nat.eq_or_lt_of_le (hφ n), rfl⟩
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by
    intro v
    simp [numeralInstancesCh]

end FFL.FirstOrder.Theory.Δ₁
