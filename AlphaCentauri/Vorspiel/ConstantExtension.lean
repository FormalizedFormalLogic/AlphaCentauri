module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.Basic.Eq

/-! # The language of ordered rings with finitely many extra constants

`Language.oRingConst k` is `ℒₒᵣ` together with `k` new constant symbols. An `ℒₒᵣ`-formula in `k`
free variables becomes a sentence of that language by filling its variables with the constants,
and a model of `ℒₒᵣ` becomes a model of it by choosing a `k`-tuple.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Language

/-- `ℒₒᵣ` extended by `k` new constant symbols. -/
abbrev oRingConst (k : ℕ) : Language := Language.add ℒₒᵣ (Language.constant (Fin k))

end Language

namespace Arithmetic

open Semiformula

variable {k : ℕ}

/-- The `i`-th of the `k` constants adjoined to `ℒₒᵣ`. -/
def cst {ξ n} (i : Fin k) : Semiterm (Language.oRingConst k) ξ n :=
  Semiterm.func (arity := 0) (Sum.inr (Language.Constant.Func.const i)) ![]

/-- An `ℒₒᵣ`-formula in `k` free variables, read as a sentence of `Language.oRingConst k` with the
variables filled by the adjoined constants. -/
def lift (φ : ArithmeticSemisentence k) : Sentence (Language.oRingConst k) :=
  Rew.subst (fun i ↦ cst i) ▹ Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) φ

section

variable (M : Type u) [ORingStructure M] (a : Fin k → M)

/-- `M` as a structure for `Language.oRingConst k`, reading the `i`-th adjoined constant as
`a i`. -/
def strucOfTuple : Struc (Language.oRingConst k) where
  Dom := M
  nonempty := ⟨0⟩
  struc :=
    letI : Structure (Language.constant (Fin k)) M :=
      { func := fun _ c _ ↦ match c with | .const i => a i
        rel := fun _ r _ ↦ r.elim }
    Structure.add ℒₒᵣ (Language.constant (Fin k)) M

@[simp] lemma strucOfTuple_models_lift_iff (φ : ArithmeticSemisentence k) :
    strucOfTuple M a ⊧ lift φ ↔ φ.Evalb a := by
  simp only [lift, strucOfTuple, models_iff, Semiformula.Realize, eval_substs,
    Structure.eval_lMap_add₁]
  exact Iff.rfl

lemma strucOfTuple_models_eq : strucOfTuple M a ⊧* 𝗘𝗤 (Language.oRingConst k) := by
  let s : Structure (Language.oRingConst k) M := (strucOfTuple M a).struc
  have : Nonempty M := ⟨0⟩
  have : Structure.Eq (Language.oRingConst k) M := ⟨fun _ _ ↦ iff_of_eq rfl⟩
  show M↓[Language.oRingConst k] ⊧* 𝗘𝗤 (Language.oRingConst k)
  infer_instance

lemma strucOfTuple_models_lMap_image {U : ArithmeticTheory} (h : M↓[ℒₒᵣ] ⊧* U) :
    strucOfTuple M a ⊧*
      Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) '' U := by
  refine Semantics.modelsSet_iff.mpr ?_
  rintro _ ⟨σ, hσ, rfl⟩
  simpa [strucOfTuple, models_iff, Semiformula.Realize] using Semantics.modelsSet_iff.mp h hσ

end

section

/-- A closed term of `ℒₒᵣ` in `k` variables dominating every such term with code below `n`. -/
def dominatingTerm (k : ℕ) : ℕ → ClosedSemiterm ℒₒᵣ k
  | 0 => ‘0’
  | n + 1 => ‘!!(dominatingTerm k n) + !!((Encodable.decode n).getD ‘0’)’

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

lemma valb_le_valb_dominatingTerm {n : ℕ} {t : ClosedSemiterm ℒₒᵣ k}
    (ht : Encodable.encode t < n) (e : Fin k → M) :
    t.valb e ≤ (dominatingTerm k n).valb e := by
  induction n with
  | zero => simp at ht
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
    · exact le_trans (ih h) (by simp [dominatingTerm])
    · have : (Encodable.decode n : Option (ClosedSemiterm ℒₒᵣ k)) = some t :=
        h ▸ Encodable.encodek t
      simp [dominatingTerm, this]

end

section

variable {T : Theory (Language.oRingConst k)} [𝗘𝗤 (Language.oRingConst k) ⪯ T]
  (sat : Semantics.Satisfiable (Struc (Language.oRingConst k)) T)

/-- The tuple of elements of `ModelOfSatEq sat` named by the adjoined constants. -/
noncomputable def cstVal (i : Fin k) : ModelOfSatEq sat := Semiterm.valb ![] (cst i)

lemma reduct_eq :
    (ModelOfSatEq.struc sat).lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) =
      standardModel (ModelOfSatEq sat) :=
  letI s : Structure ℒₒᵣ (ModelOfSatEq sat) :=
    (ModelOfSatEq.struc sat).lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k)))
  have : Structure.Zero ℒₒᵣ (ModelOfSatEq sat) := ⟨rfl⟩
  have : Structure.One ℒₒᵣ (ModelOfSatEq sat) := ⟨rfl⟩
  have : Structure.Add ℒₒᵣ (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩
  have : Structure.Mul ℒₒᵣ (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩
  have : Structure.Eq ℒₒᵣ (ModelOfSatEq sat) := ⟨fun _ _ ↦ by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Matrix.fun_eq_vec_two]⟩
  have : Structure.LT ℒₒᵣ (ModelOfSatEq sat) := ⟨fun _ _ ↦ iff_of_eq rfl⟩
  standardModel_unique _ _

lemma models_lift_iff (φ : ArithmeticSemisentence k) :
    (ModelOfSatEq sat)↓[Language.oRingConst k] ⊧ lift φ ↔ φ.Evalb (cstVal sat) := by
  simp only [lift, models_iff, Semiformula.Realize, eval_substs, Semiformula.eval_lMap]
  rw [reduct_eq]
  exact Iff.rfl

lemma models_of_lMap_image_subset {U : ArithmeticTheory}
    (h : Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) '' U ⊆ T) :
    (ModelOfSatEq sat)↓[ℒₒᵣ] ⊧* U := ⟨fun _ hσ ↦
  have h₁ := Semiformula.models_lMap.mp
    ((ModelOfSatEq.models sat).models _ (h (Set.mem_image_of_mem _ hσ)))
  reduct_eq sat ▸ h₁⟩

end

end Arithmetic

end FFL.FirstOrder
