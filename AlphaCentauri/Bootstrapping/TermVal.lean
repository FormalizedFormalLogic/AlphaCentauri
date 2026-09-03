module

public import Foundation.FirstOrder.Bootstrapping.Syntax

/-!
# Internal evaluation of terms

This module introduces internal evaluation functions for coded arithmetic terms and vectors.
It also records their definability interfaces and the basic computation and substitution laws.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `termVal e t`: the value of the coded `ℒₒᵣ`-term `t` under the assignment `e`
(a vector; `^#i ↦ e.[i]`, `^&x ↦ 0`).
- [HP98, 1.64(5)] -/
noncomputable def termVal (e t : V) : V := sorry

/-- `termValVec e k v`: `termVal e` applied to each entry of the `k`-vector `v`.
- [HP98, 1.64(5)] -/
noncomputable def termValVec (e k v : V) : V := sorry

/-- The `𝚺₁` graph of `termVal`; argument order `(y, e, t)`, `y = termVal e t`.
- [HP98, 1.63] -/
noncomputable def termValGraph : 𝚺₁.Semisentence 3 := sorry

/-- Graph of `termValVec`; argument order `(y, e, k, v)`.
- [HP98, 1.63] -/
noncomputable def termValVecGraph : 𝚺₁.Semisentence 4 := sorry

/-- The `𝚺₁` definability witness for `termVal`.
- [HP98, 1.63] -/
instance termVal.defined : 𝚺₁-Function₂ (termVal : V → V → V) via termValGraph := sorry

/-- The `𝚫₁` definability instance for `termVal`, using uniqueness of its graph.
- [HP98, 1.63] -/
instance termVal.definable : 𝚫₁-Function₂ (termVal : V → V → V) := sorry

/-- The `𝚺₁` definability witness for evaluation of term vectors.
- [HP98, 1.63] -/
instance termValVec.defined : 𝚺₁-Function₃ (termValVec : V → V → V → V) via termValVecGraph := sorry

/-- Evaluation of a coded bound variable reads the corresponding assignment entry.
- [HP98, 1.64(5)] -/
@[simp] lemma termVal_bvar (e z : V) : termVal e ^#z = e.[z] := sorry
/-- Evaluation of a coded free variable is zero under the total-assignment convention.
- No source; this is the convention for free variables in internal evaluation. -/
@[simp] lemma termVal_fvar (e x : V) : termVal e ^&x = 0 := sorry
/-- Evaluation of the coded zero term is zero.
- [HP98, 1.64(5)] -/
@[simp] lemma termVal_zero (e : V) : termVal e (𝟎 : V) = 0 := sorry
/-- Evaluation of the coded one term is one.
- [HP98, 1.64(5)] -/
@[simp] lemma termVal_one (e : V) : termVal e (𝟏 : V) = 1 := sorry
/-- Evaluation commutes with coded addition on coded terms.
- [HP98, 1.64(5)] -/
@[simp] lemma termVal_add {e t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    termVal e (t ^+ u) = termVal e t + termVal e u := sorry
/-- Evaluation commutes with coded multiplication on coded terms.
- [HP98, 1.64(5)] -/
@[simp] lemma termVal_mul {e t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    termVal e (t ^* u) = termVal e t * termVal e u := sorry
/-- Non-term codes evaluate to zero under the total internal evaluation.
- No source; this is the convention for malformed term codes. -/
lemma termVal_not_uterm {e t : V} (h : ¬IsUTerm ℒₒᵣ t) : termVal e t = 0 := sorry

/-- Evaluation of a coded term vector preserves its coded length.
- [HP98, 1.64(5)] -/
@[simp] lemma len_termValVec {e k v : V} (hv : IsUTermVec ℒₒᵣ k v) :
    len (termValVec e k v) = k := sorry
/-- The `i`-th entry of an evaluated term vector is the evaluation of its `i`-th term.
- [HP98, 1.64(5)] -/
@[simp] lemma nth_termValVec {e k v i : V} (hv : IsUTermVec ℒₒᵣ k v) (hi : i < k) :
    (termValVec e k v).[i] = termVal e v.[i] := sorry

/-- Evaluation after coded term substitution agrees with evaluation under substituted values.
- [HP98, 1.64(3), 1.67] -/
lemma termVal_termSubst {e n m w t : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t) :
    termVal e (termSubst ℒₒᵣ w t) = termVal (termValVec e n w) t := sorry
/-- Evaluation is invariant under a bound shift when entering a quantifier.
- No source; routine bridge between coded syntax and evaluation. -/
lemma termVal_termBShift {t : V} (ht : IsUTerm ℒₒᵣ t) (x e : V) :
    termVal (x ∷ e) (termBShift ℒₒᵣ t) = termVal e t := sorry
/-- Evaluation is invariant under the external-variable shift on closed terms.
- No source; routine bridge between coded syntax and evaluation. -/
lemma termVal_termShift {t : V} (ht : IsUTerm ℒₒᵣ t) (e : V) :
    termVal e (termShift ℒₒᵣ t) = termVal e t := sorry

/-- Agreement with external evaluation on quoted closed terms.
- [HP98, 1.66] -/
lemma termVal_quote {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) (v : Fin k → V) :
    termVal (matrixToVec v) ⌜t⌝ = t.valb v := sorry

end LO.FirstOrder.Arithmetic.Bootstrapping
