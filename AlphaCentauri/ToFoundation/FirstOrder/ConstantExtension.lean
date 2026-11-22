module

public import Foundation.FirstOrder.Tarski.Eq
public import Foundation.FirstOrder.Tarski.Model

/-! # Extending a language by constants

`L.add (Language.constant ι)` is `L` together with a new constant symbol for each `i : ι`. A
formula becomes a formula of the extended language by replacing its bound or its free variables by
the new constants, and an `L`-structure becomes a structure of the extended language by choosing an
element for each constant.
-/

@[expose] public section

namespace FFL.FirstOrder

open Semiformula

universe u

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

end FFL.FirstOrder
