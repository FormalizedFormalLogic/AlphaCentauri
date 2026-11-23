module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# Extending a language by constants

`L.add (Language.constant ι)` is `L` together with a new constant symbol for each `i : ι`. A
formula becomes a formula of the extended language by replacing its bound or its free variables by
the new constants, and an `L`-structure becomes a structure of the extended language by choosing an
element for each constant.

`Language.oringConst k` is `ℒₒᵣ` together with `k` new constant symbols. Closed terms of `ℒₒᵣ` in
`k` variables are dominated by a single one below any code, and a model of a theory of that language
is a model of `ℒₒᵣ` with a `k`-tuple named by the constants.
-/

@[expose] public section

namespace FFL.FirstOrder

open Semiformula

universe u

section

variable {L : Language} {ι : Type*} {k : ℕ}

/-- The new constant symbol `i` of `L.add (Language.constant ι)`. -/
def cst {ξ n} (i : ι) : Semiterm (L.add (Language.constant ι)) ξ n :=
  Semiterm.func (arity := 0) (Sum.inr (Language.Constant.Func.const i)) ![]

/-- `φ` as a sentence of `L` extended by `k` constants, with its bound variables filled by the
constants. -/
def lift (φ : Semisentence L k) : Sentence (L.add (Language.constant (Fin k))) :=
  Rew.subst (fun i ↦ cst i) ▹ Semiformula.lMap (Language.Hom.add₁ L (Language.constant (Fin k))) φ

/-- `φ` as a formula of `L` extended by constants indexed by `ι`, with its free variables replaced
by the constants. -/
def liftParameters (φ : Semiformula L ι k) : Semisentence (L.add (Language.constant ι)) k :=
  Rew.rewrite (fun i ↦ cst i) ▹ Semiformula.lMap (Language.Hom.add₁ L (Language.constant ι)) φ

section

variable (M : Type u) [Tarski.Structure L M] (a : ι → M)

/-- The structure for `L.add (Language.constant ι)` on `M` reading the constant `i` as `a i`. -/
abbrev structureOfTuple : Tarski.Structure (L.add (Language.constant ι)) M :=
  letI : Tarski.Structure (Language.constant ι) M :=
    { func := fun _ c _ ↦ match c with | .const i => a i
      rel := fun _ r _ ↦ r.elim }
  Tarski.Structure.add L (Language.constant ι) M

@[simp]
lemma eval_strucOfTuple_liftParameters (φ : Semiformula L ι k) (e : Fin k → M) :
    (liftParameters φ).Eval (s := structureOfTuple M a) e Empty.elim ↔ φ.Eval e a := by
  rw [liftParameters, eval_rew]
  simp only [Function.comp_def, Rew.rewrite_bvar, Rew.rewrite_fvar,
    Tarski.Structure.eval_lMap_add₁]
  exact Iff.rfl

variable [Nonempty M]

/-- `M` as a structure for `L.add (Language.constant ι)`, reading the constant `i` as `a i`. -/
abbrev strucOfTuple : Tarski.Struc (L.add (Language.constant ι)) := (structureOfTuple M a).toStruc

@[simp]
lemma strucOfTuple_models_lift_iff (a : Fin k → M) (φ : Semisentence L k) :
    strucOfTuple M a ⊧ lift φ ↔ φ.Evalb a := by
  simp only [lift, strucOfTuple, models_iff, Semiformula.Realize, eval_substs,
    Tarski.Structure.eval_lMap_add₁]
  exact Iff.rfl

lemma strucOfTuple_models_eq [L.Eq] [Tarski.Structure.Eq L M] :
    strucOfTuple M a ⊧* 𝗘𝗤 (L.add (Language.constant ι)) := by
  let s : Tarski.Structure (L.add (Language.constant ι)) M := structureOfTuple M a
  have : Tarski.Structure.Eq (L.add (Language.constant ι)) M :=
    ⟨fun x y ↦ Tarski.Structure.Eq.eq (L := L) x y⟩
  change M↓[L.add (Language.constant ι)] ⊧* 𝗘𝗤 (L.add (Language.constant ι))
  infer_instance

lemma strucOfTuple_models_lMap_image {T : Theory L} (h : M↓[L] ⊧* T) :
    strucOfTuple M a ⊧* Semiformula.lMap (Language.Hom.add₁ L (Language.constant ι)) '' T := by
  apply Semantics.modelsSet_iff.mpr
  rintro _ ⟨σ, hσ, rfl⟩
  simpa [strucOfTuple, models_iff, Semiformula.Realize] using Semantics.modelsSet_iff.mp h hσ

end

section

variable (N : Tarski.Struc (L.add (Language.constant ι)))

/-- The reduct of `N` to `L`. -/
abbrev Tarski.Struc.reduct : Tarski.Struc L :=
  (N.struc.lMap (Language.Hom.add₁ L (Language.constant ι))).toStruc

/-- The element of `N` named by the constant `i`. -/
noncomputable def Tarski.Struc.cstVal (i : ι) : N :=
  Semiterm.valb ![] (cst (L := L) i : Semiterm (L.add (Language.constant ι)) Empty 0)

lemma Tarski.Struc.models_lMap_iff (σ : Sentence L) :
    N ⊧ Semiformula.lMap (Language.Hom.add₁ L (Language.constant ι)) σ ↔ N.reduct ⊧ σ :=
  Semiformula.models_lMap

lemma Tarski.Struc.models_lift_iff (N : Tarski.Struc (L.add (Language.constant (Fin k))))
    (φ : Semisentence L k) : N ⊧ lift φ ↔ φ.Evalb (s := N.reduct.struc) N.cstVal := by
  change (lift φ).Eval ![] Empty.elim ↔ _
  simp only [lift, eval_substs, Semiformula.eval_lMap]
  exact Iff.rfl

lemma Tarski.Struc.eval_liftParameters_iff (φ : Semiformula L ι k) (e : Fin k → N) :
    (liftParameters φ).Eval e Empty.elim ↔ φ.Eval (s := N.reduct.struc) e N.cstVal := by
  have hc : (fun i ↦ Semiterm.val e Empty.elim
      (cst i : Semiterm (L.add (Language.constant ι)) Empty k)) = N.cstVal := by
    funext i
    exact congrArg (Tarski.Structure.func _) (funext fun j ↦ j.elim0)
  rw [liftParameters, eval_rew]
  simp only [Function.comp_def, Rew.rewrite_bvar, Rew.rewrite_fvar, Semiformula.eval_lMap,
    Semiterm.val_bvar, hc]

end

end

/-! ## The language of ordered rings with finitely many extra constants -/

/-- `ℒₒᵣ` extended by `k` new constant symbols. -/
abbrev Language.oringConst (k : ℕ) : Language := Language.add ℒₒᵣ (Language.constant (Fin k))

namespace Arithmetic

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
