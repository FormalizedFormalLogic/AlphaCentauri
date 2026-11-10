module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.HFS.CourseOfValues
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.HFS.PRF
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
  simpa using c.Φ_locallyDelta0.comp_cons₂ hf hg fun j ↦ LocallyDelta0Function.const (v j)

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
      LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.var 0)
        (LocallyDelta0Function.var 2).add_one
    have hbody : LocallyDelta0 fun x : Fin (k + 4) → V ↦
        x 0 ∈ x 1 ↔ x 0 ≤ x 3 ∧ c.Φ (fun j ↦ x j.succ.succ.succ.succ) {z | z ∈ x 2} (x 0) := by
      have hphi := c.Φ_locallyDelta0.comp_cons₂ (LocallyDelta0Function.var (0 : Fin (k + 4)))
        (LocallyDelta0Function.var 2) fun j ↦ LocallyDelta0Function.var j.succ.succ.succ.succ
      exact (LocallyDelta0.of_definable (R := fun x : Fin (k + 4) → V ↦ x 0 ∈ x 1)
        (by definability)).iff ((LocallyDelta0.of_definable
          (R := fun x : Fin (k + 4) → V ↦ x 0 ≤ x 3) (by definability)).and (by simpa using hphi))
    exact (LocallyDelta0.ball_lt_function hbound hbody).of_iff fun y ↦ by
      simpa using c.succ_graph (v := fun j ↦ y j.succ.succ.succ) (u := y 0) (s := y 2) (ih := y 1)
  bounded X := by
    use Exp.exp (X + 1)
    intro w hw
    exact le_trans (c.succ_lt_exp _ _).le (exp_monotone_le.mpr (by simpa using hw 1))

lemma stageBound_locallyDelta0 :
    LocallyDelta0Function fun w : Fin (k + 1) → V ↦ Exp.exp (w 0) := by
  simpa using LocallyDelta0Function.exp.retraction (fun _ : Fin 1 ↦ (0 : Fin (k + 1)))

/-- The stages of the construction, as a bounded primitive recursion. -/
noncomputable def prConstruction : PR.Construction V φ.prBlueprint where
  zero := fun _ ↦ ∅
  succ := c.succ
  zero_defined := .mk fun v ↦ by simp [Arithmetic.Fixpoint.Blueprint.prBlueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by simp [Arithmetic.Fixpoint.Blueprint.prBlueprint, c.eval_succDef]
  zero_locallyDelta0 := LocallyDelta0Function.const ∅
  succ_locallyDelta0 := c.succ_locallyDelta0
  bound := fun _ i ↦ Exp.exp i
  zero_lt_bound := by simp [emptyset_def]
  succ_lt_bound := fun _ i z _ ↦ c.succ_lt_exp i z
  bound_monotone := fun _ _ _ h ↦ exp_monotone_le.mpr h
  bound_locallyDelta0 := stageBound_locallyDelta0
  inv_locallyDelta0 :=
    PR.lt_bound_locallyDelta0 (bound := fun _ i ↦ Exp.exp i) stageBound_locallyDelta0

variable (v)

/-- The `s`-th stage of the construction. -/
noncomputable def limSeq (s : V) : V := c.prConstruction.result v s

variable {v}

@[simp] lemma limSeq_zero : c.limSeq v 0 = ∅ := by simp [limSeq, prConstruction]

lemma limSeq_succ (s : V) : c.limSeq v (s + 1) = c.succ v s (c.limSeq v s) := by
  simp [limSeq, prConstruction]

lemma termSet_defined :
    𝚺ᴬ₁.DefinedFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) φ.limSeqDef := .mk fun v ↦ by
  simp [c.prConstruction.result_defined_iff, Arithmetic.Fixpoint.Blueprint.limSeqDef]; rfl

@[simp] lemma eval_limSeqDef (v : Fin (k + 2) → V) :
    φ.limSeqDef.val.Evalb v ↔ v 0 = c.limSeq (v ·.succ.succ) (v 1) := c.termSet_defined.iff

lemma limSeq_locallyDelta0 :
    LocallyDelta0Function fun w : Fin (k + 1) → V ↦ c.limSeq (w ·.succ) (w 0) :=
  c.prConstruction.result_locallyDelta0

private lemma limSeq_comp {n : ℕ} {f : (Fin n → V) → V} (hf : LocallyDelta0Function f) :
    LocallyDelta0Function fun w : Fin n → V ↦ c.limSeq v (f w) := by
  simpa using c.limSeq_locallyDelta0.comp_cons hf fun j ↦ LocallyDelta0Function.const (v j)

lemma mem_limSeq_succ_iff {x s : V} :
    x ∈ c.limSeq v (s + 1) ↔ x ≤ s ∧ c.Φ v {z | z ∈ c.limSeq v s} x := by
  simp [limSeq_succ, mem_succ_iff]

lemma limSeq_cumulative {s s' : V} : s ≤ s' → c.limSeq v s ⊆ c.limSeq v s' := by
  have hR : LocallyDelta0 fun y : Fin 2 → V ↦ c.limSeq v (y 0) ⊆ c.limSeq v (y 1) := by
    exact ((LocallyDelta0.of_definable (R := fun y : Fin 2 → V ↦ y 0 ⊆ y 1)
      (by definability)).comp₂ (c.limSeq_comp (v := v) (LocallyDelta0Function.var 0))
        (c.limSeq_comp (v := v) (LocallyDelta0Function.var 1))).of_iff fun y ↦ by simp
  have hP : LocallyDelta0Pred fun s' ↦ ∀ s ≤ s', c.limSeq v s ⊆ c.limSeq v s' :=
    (LocallyDelta0.ball_le_function (LocallyDelta0Function.var 0) hR).of_iff fun _ ↦ by simp
  have : ∀ s', ∀ s ≤ s', c.limSeq v s ⊆ c.limSeq v s' := by
    apply LocallyDelta0Pred.succ_induction hP
    · intro s hs
      simp [nonpos_iff_eq_zero.mp hs]
    · intro s' ih s hs u hu
      rcases zero_or_succ s with (rfl | ⟨s, rfl⟩)
      · simp at hu
      have hs : s ≤ s' := by simpa using hs
      obtain ⟨hu, Hu⟩ := c.mem_limSeq_succ_iff.mp hu
      exact c.mem_limSeq_succ_iff.mpr ⟨le_trans hu hs, c.monotone (fun z hz ↦ ih s hs hz) Hu⟩
  exact this s' s

lemma mem_limSeq_self [c.StrongFinite] {u s : V} :
    u ∈ c.limSeq v s → u ∈ c.limSeq v (u + 1) := by
  have hR : LocallyDelta0 fun y : Fin 2 → V ↦
      y 1 ∈ c.limSeq v (y 0) → y 1 ∈ c.limSeq v (y 1 + 1) := by
    exact ((LocallyDelta0.of_definable (R := fun y : Fin 3 → V ↦ y 0 ∈ y 1 → y 0 ∈ y 2)
      (by definability)).comp₃ (LocallyDelta0Function.var 1)
        (c.limSeq_comp (v := v) (LocallyDelta0Function.var 0))
        (c.limSeq_comp (v := v) (LocallyDelta0Function.var (1 : Fin 2)).add_one)).of_iff
      fun y ↦ by simp
  have hP : LocallyDelta0Pred fun u ↦
      ∀ t ≤ s, u ∈ c.limSeq v t → u ∈ c.limSeq v (u + 1) :=
    (LocallyDelta0.ball_le_function (LocallyDelta0Function.const s) hR).of_iff fun _ ↦ by simp
  have : ∀ u, ∀ t ≤ s, u ∈ c.limSeq v t → u ∈ c.limSeq v (u + 1) := by
    apply LocallyDelta0Pred.order_induction hP
    intro u ih t ht hu
    rcases zero_or_succ t with (rfl | ⟨t, rfl⟩)
    · simp at hu
    obtain ⟨_, Hu⟩ := c.mem_limSeq_succ_iff.mp hu
    have : c.Φ v {z | z ∈ c.limSeq v t ∧ z < u} u := StrongFinite.strong_finite Hu
    have : c.Φ v {z | z ∈ c.limSeq v u} u :=
      c.monotone (by
        simp only [Set.ofPred_subset_ofPred, and_imp]
        intro z hz hzu
        exact c.limSeq_cumulative (succ_le_iff_lt.mpr hzu)
          (ih z hzu t (le_trans (by simp) ht) hz))
        this
    exact c.mem_limSeq_succ_iff.mpr ⟨by rfl, this⟩
  exact this u s le_rfl

variable (v)

set_option linter.dupNamespace false in
/-- `c.Fixpoint v x` states that `x` belongs to the least fixed point of the operator. -/
def Fixpoint (x : V) : Prop := ∃ s, x ∈ c.limSeq v s

variable {v}

lemma fixpoint_iff [c.StrongFinite] {x : V} : c.Fixpoint v x ↔ x ∈ c.limSeq v (x + 1) :=
  ⟨by rintro ⟨s, hs⟩; exact c.mem_limSeq_self hs, fun h ↦ ⟨x + 1, h⟩⟩

lemma fixpoint_iff_succ {x : V} : c.Fixpoint v x ↔ ∃ u, x ∈ c.limSeq v (u + 1) :=
  ⟨by
    rintro ⟨u, h⟩
    rcases zero_or_succ u with (rfl | ⟨u, rfl⟩)
    · simp at h
    · exact ⟨u, h⟩, by rintro ⟨u, h⟩; exact ⟨u + 1, h⟩⟩

lemma case_mp {x : V} : c.Fixpoint v x → c.Φ v {z | c.Fixpoint v z} x := by
  intro h
  obtain ⟨u, hu⟩ := c.fixpoint_iff_succ.mp h
  have : c.Φ v {z | z ∈ c.limSeq v u} x := (c.mem_limSeq_succ_iff.mp hu).2
  exact c.monotone (C' := {z | c.Fixpoint v z}) (fun _ hx ↦ ⟨u, hx⟩) this

/-- A point whose premises below `m` all appear by the stage `S` belongs to the fixpoint. -/
lemma case_mpr_of_stage {x m S : V} (hΦ : c.Φ v {z | c.Fixpoint v z ∧ z < m} x)
    (hS : ∀ z < m, c.Fixpoint v z → z ∈ c.limSeq v S) : c.Fixpoint v x := by
  have : c.Φ v {z | z ∈ c.limSeq v S} x :=
    c.monotone (C' := {z | z ∈ c.limSeq v S}) (fun z hz ↦ hS z hz.2 hz.1) hΦ
  use max S x + 1
  exact c.mem_limSeq_succ_iff.mpr
    ⟨by simp, c.monotone (C' := {z | z ∈ c.limSeq v (max S x)})
      (fun _ hz ↦ c.limSeq_cumulative (by simp) hz) this⟩

theorem case [c.StrongFinite] {x : V} : c.Fixpoint v x ↔ c.Φ v {z | c.Fixpoint v z} x := by
  constructor
  · exact c.case_mp
  · intro hx
    apply c.case_mpr_of_stage (m := x) (S := x) (StrongFinite.strong_finite hx)
    intro z hz hfix
    exact c.limSeq_cumulative (succ_le_iff_lt.mpr hz) (c.fixpoint_iff.mp hfix)

lemma fixpoint_defined : 𝚺ᴬ₁.Defined (fun v ↦ c.Fixpoint (v ·.succ) (v 0)) φ.fixpointDef :=
  .mk fun v ↦ by
  simp [Arithmetic.Fixpoint.Blueprint.fixpointDef, c.eval_limSeqDef]; rfl

@[simp] lemma eval_fixpointDef (v : Fin (k + 1) → V) :
    φ.fixpointDef.val.Evalb v ↔ c.Fixpoint (v ·.succ) (v 0) := c.fixpoint_defined.iff

lemma fixpoint_definedΔ₁ [c.StrongFinite] :
    𝚫ᴬ₁.Defined (fun v ↦ c.Fixpoint (v ·.succ) (v 0)) φ.fixpointDefΔ₁ :=
  ⟨by intro v; simp [Arithmetic.Fixpoint.Blueprint.fixpointDefΔ₁, c.eval_limSeqDef],
   by intro v; simp [Arithmetic.Fixpoint.Blueprint.fixpointDefΔ₁, c.eval_limSeqDef, fixpoint_iff]⟩

@[simp] lemma eval_fixpointDefΔ₁ [c.StrongFinite] (v : Fin (k + 1) → V) :
    φ.fixpointDefΔ₁.val.Evalb v ↔ c.Fixpoint (v ·.succ) (v 0) := c.fixpoint_definedΔ₁.iff

lemma fixpoint_locallyDelta0 [c.StrongFinite] :
    LocallyDelta0 fun w : Fin (k + 1) → V ↦ c.Fixpoint (w ·.succ) (w 0) := by
  have hlim : LocallyDelta0Function fun w : Fin (k + 1) → V ↦ c.limSeq (w ·.succ) (w 0 + 1) := by
    simpa using c.limSeq_locallyDelta0.comp_cons
      (LocallyDelta0Function.var (0 : Fin (k + 1))).add_one fun j ↦ LocallyDelta0Function.var j.succ
  exact ((LocallyDelta0.of_definable (R := fun y : Fin 2 → V ↦ y 0 ∈ y 1)
    (by definability)).comp₂ (LocallyDelta0Function.var 0) hlim).of_iff
      fun w ↦ by simpa using c.fixpoint_iff

theorem induction [c.StrongFinite] {P : V → Prop} (hP : LocallyDelta0Pred P)
    (H : ∀ C : Set V, (∀ x ∈ C, c.Fixpoint v x ∧ P x) → ∀ x, c.Φ v C x → P x) :
    ∀ x, c.Fixpoint v x → P x := by
  have hfix : LocallyDelta0Pred fun x ↦ c.Fixpoint v x := by
    simpa using c.fixpoint_locallyDelta0.comp_cons (LocallyDelta0Function.var (0 : Fin 1))
      fun j ↦ LocallyDelta0Function.const (v j)
  apply LocallyDelta0Pred.order_induction (P := fun x ↦ c.Fixpoint v x → P x) (hfix.imp hP)
  intro x ih hx
  have : c.Φ v {y | c.Fixpoint v y ∧ y < x} x := StrongFinite.strong_finite (c.case.mp hx)
  exact H {y | c.Fixpoint v y ∧ y < x} (by intro y ⟨hy, hyx⟩; exact ⟨hy, ih y hyx hy⟩) x this

end Construction

end Fixpoint

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
