module

public import AlphaCentauri.ToFoundation.FirstOrder.ConstantExtension
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-! # The language of ordered rings with finitely many extra constants

Extension of Foundation's `ℒₒᵣ` (`Arithmetic/Basic.lean`). `Language.oringConst k` is `ℒₒᵣ`
together with `k` new constant symbols. Closed terms of `ℒₒᵣ` in `k` variables are dominated by a
single one below any code, and a model of a theory of that language is a model of `ℒₒᵣ` with a
`k`-tuple named by the constants.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- `ℒₒᵣ` extended by `k` new constant symbols. -/
abbrev Language.oringConst (k : ℕ) : Language := Language.add ℒₒᵣ (Language.constant (Fin k))

namespace Arithmetic

open Semiformula

universe u

variable {k : ℕ}

section

/-- A closed term of `ℒₒᵣ` in `k` variables dominating every such term with code below `n`. -/
def dominatingTerm (k : ℕ) : ℕ → ClosedSemiterm ℒₒᵣ k
  | 0 => ‘0’
  | n + 1 => ‘!!(dominatingTerm k n) + !!((Encodable.decode n).getD ‘0’)’

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

lemma valb_le_valb_dominatingTerm {n : ℕ} {t : ClosedSemiterm ℒₒᵣ k}
  (ht : Encodable.encode t < n) (e : Fin k → M)
  : t.valb e ≤ (dominatingTerm k n).valb e := by
  induction n with
  | zero => simp at ht
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
    · exact le_trans (ih h) (by simp [dominatingTerm])
    · have : (Encodable.decode n : Option (ClosedSemiterm ℒₒᵣ k)) = some t :=
        h ▸ Encodable.encodek t
      simp [dominatingTerm, this]

end

variable {T : Theory (Language.oringConst k)} [𝗘𝗤 (Language.oringConst k) ⪯ T]
  (sat : Semantics.Satisfiable (Tarski.Struc (Language.oringConst k)) T)

/-- The tuple of elements of `ModelOfSatEq sat` named by the adjoined constants. -/
noncomputable def cstVal (i : Fin k) : ModelOfSatEq sat := Semiterm.valb ![] (cst (L := ℒₒᵣ) i)

lemma reduct_eq :
    (ModelOfSatEq.struc sat).lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) =
      standardModel (ModelOfSatEq sat) :=
  letI s : Tarski.Structure ℒₒᵣ (ModelOfSatEq sat) :=
    (ModelOfSatEq.struc sat).lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k)))
  have : Tarski.Structure.Zero ℒₒᵣ (ModelOfSatEq sat) := ⟨rfl⟩
  have : Tarski.Structure.One ℒₒᵣ (ModelOfSatEq sat) := ⟨rfl⟩
  have : Tarski.Structure.Add ℒₒᵣ (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩
  have : Tarski.Structure.Mul ℒₒᵣ (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩
  have : Tarski.Structure.Eq ℒₒᵣ (ModelOfSatEq sat) := ⟨by
    intro _ _;
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Matrix.fun_eq_vec_two]⟩
  have : Tarski.Structure.LT ℒₒᵣ (ModelOfSatEq sat) := ⟨fun _ _ ↦ iff_of_eq rfl⟩
  standardModel_unique _ _

lemma models_lift_iff (φ : ArithmeticSemisentence k) :
    (ModelOfSatEq sat)↓[Language.oringConst k] ⊧ lift φ ↔ φ.Evalb (cstVal sat) := by
  simp only [lift, models_iff, Semiformula.Realize, eval_substs, Semiformula.eval_lMap]
  rw [reduct_eq]
  exact Iff.rfl

lemma models_of_lMap_image_subset {U : ArithmeticTheory}
    (h : Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) '' U ⊆ T) :
    (ModelOfSatEq sat)↓[ℒₒᵣ] ⊧* U := ⟨fun _ hσ ↦
  reduct_eq sat ▸ Semiformula.models_lMap.mp
    ((ModelOfSatEq.models sat).models _ (h (Set.mem_image_of_mem _ hσ)))⟩

end Arithmetic

end FFL.FirstOrder
