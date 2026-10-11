module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Codes of formulas built by derived connectives

A vector is `matrixToVec u` exactly when it has the length of `u` and the entries of `u`. The code
of a negation, an implication, a block of universal quantifiers, a finite conjunction or a
substitution instance of a formula is obtained from the code of the formula by the corresponding
function on codes.
-/

@[expose] public section

namespace FFL.FirstOrder

open Arithmetic Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma Arithmetic.Bootstrapping.eq_matrixToVec_iff {k : ℕ} {w : V} {u : Fin k → V} :
    w = matrixToVec u ↔ (k : V) = len w ∧ ∀ i : Fin k, w.[((i : ℕ) : V)] = u i := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h₁, h₂⟩
    apply nth_ext' (k : V) h₁.symm (by simp)
    intro i hi
    obtain ⟨i, rfl⟩ := eq_fin_of_lt_nat hi
    simp [h₂]

namespace Semiformula

variable {L : Language} [L.Encodable] [L.LORDefinable]

@[simp] lemma quote_neg {n : ℕ} (φ : Semiproposition L n) :
    (⌜∼φ⌝ : V) = Bootstrapping.neg L ⌜φ⌝ := by
  simp [quote_def]

@[simp] lemma quote_imp {n : ℕ} (φ ψ : Semiproposition L n) :
    (⌜φ 🡒 ψ⌝ : V) = Bootstrapping.imp L ⌜φ⌝ ⌜ψ⌝ := by
  simp [quote_def, Bootstrapping.imp]

lemma quote_allItr {n k : ℕ} (φ : Semiproposition L (n + k)) :
    (⌜∀¹^[k] φ⌝ : V) = qqAlls (⌜φ⌝ : V) (k : V) := by
  induction k with
  | zero => simp
  | succ k ih => simpa [allItr_succ, qqAlls_all] using ih (∀¹ φ)

lemma quote_conj {n k : ℕ} (φ : Fin k → Semiproposition L n) :
    (⌜Matrix.conj φ⌝ : V) = ^⋀ matrixToVec fun i ↦ (⌜φ i⌝ : V) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simpa [Matrix.conj, Matrix.vecHead, Matrix.vecTail, Function.comp_def] using
      ih (Matrix.vecTail φ)

lemma quote_substs {n m : ℕ} (w : Fin n → SyntacticSemiterm L m) (φ : Semiproposition L n) :
    (⌜φ ⇜ w⌝ : V) = Bootstrapping.subst L (matrixToVec fun i ↦ (⌜w i⌝ : V)) ⌜φ⌝ := by
  simp [quote_def, Semiterm.quote_def]
  rfl

end Semiformula

end FFL.FirstOrder
