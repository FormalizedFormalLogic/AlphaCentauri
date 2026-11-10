module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.HFS.PRF
public import Foundation.FirstOrder.Arithmetic.HFS.Fixpoint

/-!
# Fixpoint construction in models of $\mathsf{EA}$

The file `Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean` on inductively defined sets in
models of $\mathsf{I}\Sigma_1$, ported to models of $\mathsf{EA}$. The operator is required to be
locally $\Delta_0$; the stages `limSeq` are then given by bounded primitive recursion, and the
formulas of Foundation's `Fixpoint.Blueprint` define them. For strongly finite operators the
fixpoint is locally $\Delta_0$, is a fixed point of the operator, and satisfies induction on
locally $\Delta_0$ predicates. For operators that are only finite, a premise is reached at a
stage that has to be given explicitly.

- [HP98, §V.3]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

namespace Fixpoint

variable (V)

/-- A monotone, locally $\Delta_0$ operator defined by the core of a blueprint. -/
structure Construction {k : ℕ} (φ : Arithmetic.Fixpoint.Blueprint k) where
  /-- `c.Φ v Y x` states that `x ∈ Φ(Y)`. -/
  Φ : (Fin k → V) → Set V → V → Prop
  defined : 𝚫ᴬ₁.Defined (fun v ↦ Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0)) φ.core
  monotone {C C' : Set V} (h : C ⊆ C') {v x} : Φ v C x → Φ v C' x
  Φ_locallyDelta0 :
    LocallyDelta0 fun v : Fin (k + 2) → V ↦ Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0)

class Construction.Finite {k : ℕ} {φ : Arithmetic.Fixpoint.Blueprint k} (c : Construction V φ) where
  finite {C : Set V} {v x} : c.Φ v C x → ∃ m, c.Φ v {y ∈ C | y < m} x

class Construction.StrongFinite {k : ℕ} {φ : Arithmetic.Fixpoint.Blueprint k}
    (c : Construction V φ) where
  strong_finite {C : Set V} {v x} : c.Φ v C x → c.Φ v {y ∈ C | y < x} x

instance {k : ℕ} {φ : Arithmetic.Fixpoint.Blueprint k} (c : Construction V φ) [c.StrongFinite] :
    c.Finite where
  finite {_ _ x} := fun h ↦ ⟨x, Construction.StrongFinite.strong_finite h⟩

variable {V}

namespace Construction

variable {k : ℕ} {φ : Arithmetic.Fixpoint.Blueprint k} (c : Construction V φ) (v : Fin k → V)

lemma eval_formula (v : Fin k.succ.succ → V) :
    φ.core.val.Evalb v ↔ c.Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0) := c.defined.iff

private lemma phi_comp {n : ℕ} {f g : (Fin n → V) → V} (hf : LocallyDelta0Function f)
    (hg : LocallyDelta0Function g) :
    LocallyDelta0 fun w : Fin n → V ↦ c.Φ v {z | z ∈ g w} (f w) := by
  have := c.Φ_locallyDelta0.comp (f := f :> g :> fun j _ ↦ v j) fun j ↦ by
    cases j using Fin.cases with
    | zero => simpa using hf
    | succ j =>
      cases j using Fin.cases with
      | zero => simpa using hg
      | succ j => simpa using LocallyDelta0Function.const (v j)
  simpa using this

private lemma add_one_locallyDelta0 {n : ℕ} {f : (Fin n → V) → V}
    (hf : LocallyDelta0Function f) :
    LocallyDelta0Function fun w : Fin n → V ↦ f w + 1 := by
  have hadd : LocallyDelta0Function fun x : Fin 2 → V ↦ x 0 + x 1 :=
    LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, by definability⟩
  exact hadd.comp (f := ![f, fun _ ↦ 1]) <| Fin.forall_fin_succ.mpr
    ⟨hf, Fin.forall_fin_succ.mpr ⟨LocallyDelta0Function.const 1, finZeroElim⟩⟩

private lemma add_locallyDelta0 {n : ℕ} {f g : (Fin n → V) → V} (hf : LocallyDelta0Function f)
    (hg : LocallyDelta0Function g) : LocallyDelta0Function fun w : Fin n → V ↦ f w + g w := by
  have hadd : LocallyDelta0Function fun x : Fin 2 → V ↦ x 0 + x 1 :=
    LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, by definability⟩
  exact hadd.comp (f := ![f, g]) <| Fin.forall_fin_succ.mpr
    ⟨hf, Fin.forall_fin_succ.mpr ⟨hg, finZeroElim⟩⟩

lemma succ_existsUnique (s ih : V) :
    ∃! u : V, ∀ x, (x ∈ u ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x) := by
  have : LocallyDelta0Pred fun x ↦ x ≤ s ∧ c.Φ v {z | z ∈ ih} x :=
    (LocallyDelta0.of_definable (R := fun w : Fin 1 → V ↦ w 0 ≤ s) (by definability)).and
      (c.phi_comp v (LocallyDelta0Function.var 0) (LocallyDelta0Function.const ih))
  exact this.finite_comprehension! ⟨s + 1, fun i ⟨hi, _⟩ ↦ lt_succ_iff_le.mpr hi⟩

/-- The next stage `{x ≤ s | x ∈ Φ(ih)}`. -/
noncomputable def succ (s ih : V) : V := Classical.choose! (c.succ_existsUnique v s ih)

variable {v}

lemma mem_succ_iff {s ih x : V} : x ∈ c.succ v s ih ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x :=
  Classical.choose!_spec (c.succ_existsUnique v s ih) x

lemma succ_lt_exp (s ih : V) : c.succ v s ih < Exp.exp (s + 1) :=
  lt_exp_iff.mpr fun _ hj ↦ lt_succ_iff_le.mpr (c.mem_succ_iff.mp hj).1

private lemma succ_graph {u s ih : V} :
    u = c.succ v s ih ↔ ∀ x < u + (s + 1), x ∈ u ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x :=
  ⟨by rintro rfl x _; simp [mem_succ_iff], by
    intro h; apply mem_ext
    intro x; constructor
    · intro hx
      exact c.mem_succ_iff.mpr <| h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · intro hx
      exact h x (lt_of_lt_of_le (lt_succ_iff_le.mpr (c.mem_succ_iff.mp hx).1)
        (by simp)) |>.mpr (c.mem_succ_iff.mp hx)⟩

set_option linter.flexible false in
lemma succ_defined : 𝚺ᴬ₁.DefinedFunction
    (fun v : Fin (k + 2) → V ↦ c.succ (v ·.succ.succ) (v 1) (v 0)) φ.succDef :=
  .mk fun v ↦ by
  simp [Arithmetic.Fixpoint.Blueprint.succDef, succ_graph,
    Bounding.HierarchySymbol.Semiformula.val_sigma, c.eval_formula,
    c.defined.proper.iff', -and_imp, BinderNotation.finSuccItr]
  grind

lemma eval_succDef (v : Fin (k + 3) → V) :
    φ.succDef.val.Evalb v ↔ v 0 = c.succ (v ·.succ.succ.succ) (v 2) (v 1) := c.succ_defined.iff

lemma succ_locallyDelta0 :
    LocallyDelta0Function fun w : Fin (k + 2) → V ↦ c.succ (w ·.succ.succ) (w 1) (w 0) where
  graph := by
    have hbound : LocallyDelta0Function fun y : Fin (k + 3) → V ↦ y 0 + (y 2 + 1) :=
      add_locallyDelta0 (LocallyDelta0Function.var 0)
        (add_one_locallyDelta0 (LocallyDelta0Function.var 2))
    have hbody : LocallyDelta0 fun x : Fin (k + 4) → V ↦
        x 0 ∈ x 1 ↔ x 0 ≤ x 3 ∧ c.Φ (fun j ↦ x j.succ.succ.succ.succ) {z | z ∈ x 2} (x 0) := by
      have hphi := c.Φ_locallyDelta0.comp
        (f := (fun x : Fin (k + 4) → V ↦ x 0) :> (fun x ↦ x 2) :>
          fun j x ↦ x j.succ.succ.succ.succ)
        fun j ↦ by
          cases j using Fin.cases with
          | zero => simpa using LocallyDelta0Function.var 0
          | succ j =>
            cases j using Fin.cases with
            | zero => simpa using LocallyDelta0Function.var 2
            | succ j => simpa using LocallyDelta0Function.var j.succ.succ.succ.succ
      exact (LocallyDelta0.of_definable (R := fun x : Fin (k + 4) → V ↦ x 0 ∈ x 1)
        (by definability)).iff ((LocallyDelta0.of_definable
          (R := fun x : Fin (k + 4) → V ↦ x 0 ≤ x 3) (by definability)).and (by simpa using hphi))
    exact (LocallyDelta0.ball_lt_function hbound hbody).of_iff fun y ↦ by
      simpa using c.succ_graph (v := fun j ↦ y j.succ.succ.succ) (u := y 0) (s := y 2) (ih := y 1)
  bounded X := by
    use Exp.exp (X + 1)
    intro w hw
    exact le_trans (c.succ_lt_exp _ _).le (exp_monotone_le.mpr (by simpa using hw 1))

end Construction

end Fixpoint

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
