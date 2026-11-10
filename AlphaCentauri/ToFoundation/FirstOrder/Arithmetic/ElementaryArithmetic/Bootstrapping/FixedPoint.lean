module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping.Syntax.Formula.Functions
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.FixedPoint

/-!
# Substitution of numerals in models of $\mathsf{EA}$

The part of `Foundation/FirstOrder/Arithmetic/Bootstrapping/FixedPoint.lean` on substituting
numerals for the bound variables of a code of a formula, ported to models of $\mathsf{EA}$: the list
`matrixToVec v` of the entries of a tuple, `substNumeral` and `substNumerals`, defined by
Foundation's `ssnum` and `ssnums`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic
namespace ElementaryArithmetic

open _root_.FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔] {k : ℕ}

/-- The list of the entries of the tuple `v`. -/
noncomputable def matrixToVec {k : ℕ} (v : Fin k → V) : V := Matrix.foldr (fun t w ↦ t ∷ w) 0 v

@[simp] lemma matrixToVec_nil (v : Fin 0 → V) : matrixToVec v = 0 := rfl

@[simp] lemma matrixToVec_succ {k : ℕ} (v : Fin (k + 1) → V) :
    matrixToVec v = Matrix.vecHead v ∷ matrixToVec (Matrix.vecTail v) := rfl

@[simp] lemma matrixToVec_len {k : ℕ} (v : Fin k → V) : len (matrixToVec v) = k := by
  induction k <;> simp [*]

@[simp] lemma matrixToVec_nth {k : ℕ} (v : Fin k → V) (i : Fin k) :
    (matrixToVec v).[↑i] = v i := by
  induction k
  · exact i.elim0
  · cases i using Fin.cases
    · simp; rfl
    · simp [*]; rfl

section matrixToVec

variable {L : Language} [L.Encodable] [L.LORDefinable] {v : Fin k → V}

lemma isSemitermVec_matrixToVec {n : V} :
    IsSemitermVec L (k : V) n (matrixToVec v) ↔ ∀ i, IsSemiterm L n (v i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [matrixToVec_succ, Nat.cast_succ, IsSemitermVec.cons_iff, ih, Fin.forall_fin_succ]
    rfl

lemma isUTermVec_matrixToVec (hv : ∀ i, IsUTerm L (v i)) : IsUTermVec L (k : V) (matrixToVec v) :=
  ⟨by simp, fun i hi ↦ by obtain ⟨i, rfl⟩ := eq_fin_of_lt_nat hi; simpa using hv i⟩

lemma termSubstVec_matrixToVec {w : V} (hv : ∀ i, IsUTerm L (v i)) :
    termSubstVec L (k : V) w (matrixToVec v) = matrixToVec fun i ↦ termSubst L w (v i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [matrixToVec_succ, matrixToVec_succ, Nat.cast_succ,
      termSubstVec_cons (t := Matrix.vecHead v) (hv 0)
        (isUTermVec_matrixToVec (v := Matrix.vecTail v) fun i ↦ hv i.succ),
      ih (v := Matrix.vecTail v) fun i ↦ hv i.succ]
    rfl

end matrixToVec

namespace Bootstrapping.Arithmetic

set_option linter.dupNamespace false

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic (ssnum ssnums)

/-- The code of the formula obtained from the code `φ` by substituting the numeral of `x` for its
bound variable. -/
noncomputable def substNumeral (φ x : V) : V := subst ℒₒᵣ ?[numeral x] φ

/-- The code of the formula obtained from the code `φ` by substituting the numerals of the entries
of `v` for its bound variables. -/
noncomputable def substNumerals (φ : V) (v : Fin k → V) : V :=
  subst ℒₒᵣ (matrixToVec (fun i ↦ numeral (v i))) φ

instance substNumeral.defined : 𝚺ᴬ₁-Function₂ (substNumeral : V → V → V) via ssnum :=
  .mk fun v ↦ by simp [ssnum, substNumeral]

instance substNumerals.defined :
    HierarchySymbol.DefinedFunction
      (fun v ↦ substNumerals (v 0) (v ·.succ) : (Fin (k + 1) → V) → V) ssnums := .mk fun v ↦ by
  unfold ssnums
  symm
  suffices
      v 0 = subst ℒₒᵣ (matrixToVec fun i ↦ numeral (v i.succ.succ)) (v 1) ↔
      ∃ x, ↑k = len x ∧ (∀ i : Fin k, nth x ((i : ℕ) : V) = numeral (v i.succ.succ)) ∧
        v 0 = subst ℒₒᵣ x (v 1) by
    simpa [ssnums, substNumerals, numeral_eq_natCast]
  constructor
  · intro h
    refine ⟨matrixToVec fun i ↦ numeral (v i.succ.succ), ?_⟩
    simpa
  · rintro ⟨x, hx, h, e⟩
    suffices (matrixToVec fun i ↦ numeral (v i.succ.succ)) = x by simpa [this]
    apply nth_ext' (k : V)
    · simp
    · simp [hx]
    · intro i hi
      rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
      simp [h]

end Bootstrapping.Arithmetic

end ElementaryArithmetic
end FFL.FirstOrder.Arithmetic
