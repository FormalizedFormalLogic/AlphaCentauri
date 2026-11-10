module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.HFS.CourseOfValues
public import AlphaCentauri.ToFoundation.ElementaryArithmetic.HFS.Fixpoint
public import Foundation.FirstOrder.Arithmetic.HFS.Vec

/-!
# Lists in models of $\mathsf{EA}$

The file `Foundation/FirstOrder/Arithmetic/HFS/Vec.lean` on lists coded by iterated pairing in
models of $\mathsf{I}\Sigma_1$, ported to models of $\mathsf{EA}$: `x ∷ v`, the `i`-th element
`v.[i]`, induction on lists for locally $\Delta_0$ predicates, recursion on lists with a monotone
bound on its values, and the length, maximum, last elements, concatenation, membership,
repetition and set of elements of a list. The formulas `adjoinDef`, `mkVec₁Def`, `mkVec₂Def`,
`nthDef`, `lenDef`, `listMaxDef`, `takeLastDef`, `concatDef`, `memVecDef`, `subsetVecDef`,
`repeatVecDef` and `vecToSetDef` define the $\mathsf{EA}$ versions. A Skolem function for a
locally $\Delta_0$ relation with bounded witnesses is `sigmaZero_skolem_vec`.

- [HP98, §V.3]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

lemma LocallyDelta0.mem {k : ℕ} {f f' : (Fin k → V) → V} (hf : LocallyDelta0Function f)
    (hf' : LocallyDelta0Function f') : LocallyDelta0 fun v ↦ f v ∈ f' v :=
  (LocallyDelta0.of_definable (R := fun w : Fin 2 → V ↦ w 0 ∈ w 1)
    (by definability)).comp₂ hf hf'

section adjoin

noncomputable scoped instance : Adjoin V V := ⟨(⟪·, ·⟫ + 1)⟩

lemma adjoin_def (x v : V) : x ∷ v = ⟪x, v⟫ + 1 := rfl

@[simp] lemma fstIdx_adjoin (x v : V) : fstIdx (x ∷ v) = x := by simp [adjoin_def, fstIdx]

@[simp] lemma sndIdx_adjoin (x v : V) : sndIdx (x ∷ v) = v := by simp [adjoin_def, sndIdx]

lemma succ_eq_adjoin (x : V) : x + 1 = π₁ x ∷ π₂ x := by simp [adjoin_def]

@[simp] lemma lt_adjoin (x v : V) : x < x ∷ v := by simp [adjoin_def, lt_succ_iff_le]

@[simp] lemma lt_adjoin' (x v : V) : v < x ∷ v := by simp [adjoin_def, lt_succ_iff_le]

@[simp] lemma zero_lt_adjoin (x v : V) : 0 < x ∷ v := by simp [adjoin_def]

@[simp] lemma adjoin_ne_zero (x v : V) : x ∷ v ≠ 0 := by simp [adjoin_def]

@[simp] lemma zero_ne_adjoin (x v : V) : 0 ≠ x ∷ v := by symm; simp [adjoin_def]

lemma nil_or_adjoin (z : V) : z = 0 ∨ ∃ x v, z = x ∷ v := by
  rcases zero_or_succ z with (rfl | ⟨z, rfl⟩)
  · left; rfl
  · right; exact ⟨π₁ z, π₂ z, by simp [succ_eq_adjoin]⟩

@[simp] lemma adjoin_inj (x₁ x₂ v₁ v₂ : V) :
    x₁ ∷ v₁ = x₂ ∷ v₂ ↔ x₁ = x₂ ∧ v₁ = v₂ := by simp [adjoin_def]

lemma LocallyDelta0Function.pi₁ : LocallyDelta0Function₁ (pi₁ : V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, by definability⟩

lemma LocallyDelta0Function.pi₂ : LocallyDelta0Function₁ (pi₂ : V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, by definability⟩

lemma LocallyDelta0Function.sub : LocallyDelta0Function₂ ((· - ·) : V → V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, by definability⟩

lemma adjoin_le_adjoin {x₁ x₂ v₁ v₂ : V} (hx : x₁ ≤ x₂) (hv : v₁ ≤ v₂) :
    x₁ ∷ v₁ ≤ x₂ ∷ v₂ := by simpa [adjoin_def] using pair_le_pair hx hv

instance adjoin_defined : 𝚺ᴬ₀-Function₂ (adjoin : V → V → V) via adjoinDef := .mk fun v ↦ by
  simp_all [adjoinDef, adjoin_def]

instance adjoin_definable : 𝚺ᴬ₀-Function₂ (adjoin : V → V → V) := adjoin_defined.to_definable

instance adjoin_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₂ (adjoin : V → V → V) := adjoin_definable.of_zero

instance mkVec₁_defined : 𝚺ᴬ₀-Function₁ (fun x : V ↦ ?[x]) via mkVec₁Def := .mk fun v ↦ by
  simp [mkVec₁Def]

instance mkVec₁_definable : 𝚺ᴬ₀-Function₁ (fun x : V ↦ ?[x]) := mkVec₁_defined.to_definable

instance mkVec₁_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₁ (fun x : V ↦ ?[x]) := mkVec₁_definable.of_zero

instance mkVec₂_defined : 𝚺ᴬ₁-Function₂ (fun x y : V ↦ ?[x, y]) via mkVec₂Def := .mk fun v ↦ by
  simp [mkVec₂Def]

instance mkVec₂_definable : 𝚺ᴬ₁-Function₂ (fun x y : V ↦ ?[x, y]) := mkVec₂_defined.to_definable

instance mkVec₂_definable' (Γ m) : Γᴬ_[m + 1]-Function₂ (fun x y : V ↦ ?[x, y]) :=
  mkVec₂_definable.of_sigmaOne

instance adjoin_bounded : Bounded₂ (adjoin : V → V → V) :=
  ⟨‘x y. (x + y + 1) * (x + y + 1) + 1’, fun v ↦ by
    simpa [adjoin_def, sq] using pair_polybound (v 0) (v 1)⟩

lemma LocallyDelta0Function.adjoin : LocallyDelta0Function₂ (adjoin : V → V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, adjoin_definable⟩

instance fstIdx_bounded : Bounded₁ (fstIdx : V → V) := ⟨‘x. x’, fun _ ↦ by simp⟩

instance sndIdx_bounded : Bounded₁ (sndIdx : V → V) := ⟨‘x. x’, fun _ ↦ by simp⟩

lemma exp_exp_add_two (n : V) :
    Exp.exp (Exp.exp (n + 2)) = (Exp.exp (Exp.exp n) * Exp.exp (Exp.exp n)) ^ 2 := by
  have : Exp.exp (n + 2) = 2 * (2 * Exp.exp n) := by
    rw [← one_add_one_eq_two, ← add_assoc, exp_succ, exp_succ, one_add_one_eq_two]
  rw [this, exp_even, exp_even, sq, mul_pow]

/-- A pair of elements below `Exp.exp (Exp.exp n)` lies below `Exp.exp (Exp.exp (n + 2))`. -/
lemma adjoin_le_exp_exp {a b n : V} (hn : 1 ≤ n) (ha : a ≤ Exp.exp (Exp.exp n))
    (hb : b ≤ Exp.exp (Exp.exp n)) : a ∷ b ≤ Exp.exp (Exp.exp (n + 2)) := by
  set E := Exp.exp (Exp.exp n)
  have hE : 2 * 2 ≤ E := by
    have h2 : 2 ≤ Exp.exp n := by simpa using exp_monotone_le.mpr hn
    have : Exp.exp (1 + 1 : V) = 2 * 2 := by rw [exp_succ, exp_one]
    rw [← this, one_add_one_eq_two]
    exact exp_monotone_le.mpr h2
  have hE₁ : 1 ≤ E := one_le_exp _
  have hlt : a + b + 1 < E * E := calc
    a + b + 1 ≤ E + E + E := add_le_add (add_le_add ha hb) hE₁
    _ < E + E + E + E := lt_add_of_pos_right _ (lt_of_lt_of_le (by simp) hE₁)
    _ = (2 * 2) * E := by rw [two_mul, add_mul, two_mul]; simp [add_assoc]
    _ ≤ E * E := mul_le_mul_of_nonneg_right hE (by simp)
  have : ⟪a, b⟫ < (E * E) ^ 2 :=
    lt_of_le_of_lt (pair_polybound a b) (pow_lt_pow_left₀ hlt (by simp) (by simp))
  rw [exp_exp_add_two, adjoin_def]
  exact lt_iff_succ_le.mp this

lemma le_exp_exp {a n : V} (h : a ≤ n) : a ≤ Exp.exp (Exp.exp n) :=
  le_trans h (lt_trans (lt_exp n) (exp_monotone.mpr (lt_exp n))).le

end adjoin

/-! ### The `i`-th element of a list -/

namespace Nth

/-- The rules generating the graph `⟪v, i, x⟫` of `v.[i] = x`. -/
def Phi (C : Set V) (pr : V) : Prop :=
  (∃ v, pr = ⟪v, 0, fstIdx v⟫) ∨ (∃ v i x, pr = ⟪v, i + 1, x⟫ ∧ ⟪sndIdx v, i, x⟫ ∈ C)

private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
    (∃ v ≤ pr, ∃ fst ≤ v, fst = fstIdx v ∧ pr = ⟪v, 0, fst⟫) ∨
    (∃ v ≤ pr, ∃ i ≤ pr, ∃ x ≤ pr, pr = ⟪v, i + 1, x⟫ ∧
      ∃ snd ≤ v, snd = sndIdx v ∧ ∃ six < C, six = ⟪snd, i, x⟫ ∧ six ∈ C) := by
  constructor
  · rintro (⟨v, rfl⟩ | ⟨v, i, x, rfl, hC⟩)
    · left; exact ⟨v, by simp, _, by simp, rfl, rfl⟩
    · right; exact ⟨v, by simp,
        i, le_trans (le_trans (by simp) (le_pair_left _ _)) (le_pair_right _ _),
        x, le_trans (by simp) (le_pair_right _ _), rfl, _, by simp, rfl, _, lt_of_mem hC, rfl, hC⟩
  · rintro (⟨v, _, _, _, rfl, rfl⟩ | ⟨v, _, i, _, x, _, rfl, _, _, rfl, _, _, rfl, hC⟩)
    · left; exact ⟨v, rfl⟩
    · right; exact ⟨v, i, x, rfl, hC⟩

lemma phi_definable : 𝚺ᴬ₀.Definable fun w : Fin 2 → V ↦ Phi {x | x ∈ w 1} (w 0) :=
  HierarchySymbol.Definable.of_iff (by definability) fun w ↦ phi_iff (w 1) (w 0)

/-- The construction of the graph of `nth`. -/
def adjointruction : Fixpoint.Construction V Arithmetic.Nth.blueprint where
  Φ := fun _ ↦ Phi
  defined := .of_zero <| .mk fun v ↦ by simp [phi_iff]
  monotone := by
    rintro C C' hC _ x (h | ⟨v, i, x, rfl, h⟩)
    · left; exact h
    · right; exact ⟨v, i, x, rfl, hC h⟩
  Φ_locallyDelta0 := LocallyDelta0.of_definable phi_definable

instance : adjointruction.StrongFinite V where
  strong_finite := by
    rintro C v x (h | ⟨v, i, x, rfl, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v, i, x, rfl, h, lt_of_le_of_lt (pair_le_pair_left (by simp) _)
        (pair_lt_pair_right _ (pair_lt_pair_left (by simp) _))⟩

/-- `Graph ⟪v, i, x⟫` states that `v.[i] = x`. -/
def Graph : V → Prop := adjointruction.Fixpoint ![]

instance graph_defined : 𝚺ᴬ₁-Predicate (Graph : V → Prop) via Arithmetic.Nth.graphDef :=
  adjointruction.fixpoint_defined

lemma graph_case {pr : V} :
    Graph pr ↔
    (∃ v, pr = ⟪v, 0, fstIdx v⟫) ∨ (∃ v i x, pr = ⟪v, i + 1, x⟫ ∧ Graph ⟪sndIdx v, i, x⟫) :=
  adjointruction.case

lemma graph_locallyDelta0 : LocallyDelta0 fun w : Fin 3 → V ↦ Graph ⟪w 0, w 1, w 2⟫ := by
  have := adjointruction.fixpoint_locallyDelta0.comp_cons (u := Fin.elim0)
    (LocallyDelta0Function.pairing.comp₂ (LocallyDelta0Function.var (V := V) (0 : Fin 3))
      (LocallyDelta0Function.pairing.comp₂ (LocallyDelta0Function.var (V := V) (1 : Fin 3))
        (LocallyDelta0Function.var (V := V) (2 : Fin 3)))) (fun j ↦ j.elim0)
  exact this.of_iff fun w ↦ by simp [Graph, Matrix.empty_eq]

lemma graph_zero {v x : V} : Graph ⟪v, 0, x⟫ ↔ x = fstIdx v := by
  constructor
  · intro h
    rcases graph_case.mp h with (⟨w, h⟩ | ⟨w, i, x, h, _⟩)
    · rcases show v = w ∧ x = fstIdx w by simpa using h with ⟨rfl, rfl, rfl⟩; rfl
    · simp at h
  · rintro rfl; exact graph_case.mpr <| Or.inl ⟨v, rfl⟩

lemma graph_succ {v i x : V} : Graph ⟪v, i + 1, x⟫ ↔ Graph ⟪sndIdx v, i, x⟫ := by
  constructor
  · intro h
    rcases graph_case.mp h with (⟨w, h⟩ | ⟨w, j, y, h, hw⟩)
    · simp at h
    · rcases show v = w ∧ i = j ∧ x = y by simpa using h with ⟨rfl, rfl, rfl⟩; exact hw
  · intro h; exact graph_case.mpr <| Or.inr ⟨v, i, x, rfl, h⟩

lemma exists_le_graph (v i : V) : ∃ x ≤ v, Graph ⟪v, i, x⟫ := by
  have hP : LocallyDelta0Pred fun i' ↦ ∀ v' ≤ v, ∃ x ≤ v', Graph ⟪v', i', x⟫ := by
    have hR : LocallyDelta0 fun y : Fin 3 → V ↦ Graph ⟪y 1, y 2, y 0⟫ := by
      simpa using graph_locallyDelta0.comp₃ (LocallyDelta0Function.var 1)
        (LocallyDelta0Function.var 2) (LocallyDelta0Function.var 0)
    have := LocallyDelta0.ball_le_function (LocallyDelta0Function.const v) <|
      LocallyDelta0.bexs_le_function (LocallyDelta0Function.var 0) hR
    exact this.of_iff fun w ↦ by simp
  have : ∀ i', ∀ v' ≤ v, ∃ x ≤ v', Graph ⟪v', i', x⟫ := by
    apply LocallyDelta0Pred.succ_induction hP
    · intro v' _
      exact ⟨fstIdx v', by simp, graph_case.mpr <| Or.inl ⟨v', rfl⟩⟩
    · intro i' ih v' hv'
      obtain ⟨x, hx, hg⟩ := ih (sndIdx v') (le_trans (by simp) hv')
      exact ⟨x, le_trans hx (by simp), graph_succ.mpr hg⟩
  exact this i v le_rfl

lemma graph_unique {v i x₁ x₂ : V} : Graph ⟪v, i, x₁⟫ → Graph ⟪v, i, x₂⟫ → x₁ = x₂ := by
  set A := v + x₁ + x₂
  have hP : LocallyDelta0Pred fun i ↦
      ∀ v ≤ A, ∀ x₁ ≤ A, ∀ x₂ ≤ A, Graph ⟪v, i, x₁⟫ → Graph ⟪v, i, x₂⟫ → x₁ = x₂ := by
    have hR : LocallyDelta0 fun y : Fin 4 → V ↦
        Graph ⟪y 2, y 3, y 1⟫ → Graph ⟪y 2, y 3, y 0⟫ → y 1 = y 0 := by
      apply LocallyDelta0.imp
      · simpa using graph_locallyDelta0.comp₃ (LocallyDelta0Function.var 2)
          (LocallyDelta0Function.var 3) (LocallyDelta0Function.var 1)
      apply LocallyDelta0.imp
      · simpa using graph_locallyDelta0.comp₃ (LocallyDelta0Function.var 2)
          (LocallyDelta0Function.var 3) (LocallyDelta0Function.var 0)
      exact LocallyDelta0.of_definable (by definability)
    have := LocallyDelta0.ball_le_function (LocallyDelta0Function.const A) <|
      LocallyDelta0.ball_le_function (LocallyDelta0Function.const A) <|
        LocallyDelta0.ball_le_function (LocallyDelta0Function.const A) hR
    exact this.of_iff fun w ↦ by simp
  have : ∀ i, ∀ v ≤ A, ∀ x₁ ≤ A, ∀ x₂ ≤ A, Graph ⟪v, i, x₁⟫ → Graph ⟪v, i, x₂⟫ → x₁ = x₂ := by
    apply LocallyDelta0Pred.succ_induction hP
    · intro v _ x₁ _ x₂ _
      simp only [graph_zero]
      rintro rfl rfl; rfl
    · intro i ih v hv x₁ hx₁ x₂ hx₂
      simp only [graph_succ]
      exact ih (sndIdx v) (le_trans (by simp) hv) x₁ hx₁ x₂ hx₂
  exact this i v (by simp [A, add_assoc]) x₁ (by simp [A]) x₂ (by simp [A])

lemma graph_existsUnique (v i : V) : ∃! x, Graph ⟪v, i, x⟫ := by
  obtain ⟨x, -, hx⟩ := exists_le_graph v i
  exact ExistsUnique.intro x hx fun y hy ↦ graph_unique hy hx

end Nth

section nth

/-- The `i`-th element of the list `v`. -/
noncomputable def nth (v i : V) : V := Classical.choose! (Nth.graph_existsUnique v i)

scoped notation:max v:max ".[" i "]" => nth v i

lemma nth_graph (v i : V) : Nth.Graph ⟪v, i, v.[i]⟫ :=
  Classical.choose!_spec (Nth.graph_existsUnique v i)

lemma nth_eq_of_graph {v i x : V} (h : Nth.Graph ⟪v, i, x⟫) : nth v i = x :=
  Nth.graph_unique (nth_graph v i) h

lemma nth_zero (v : V) : v.[0] = fstIdx v := nth_eq_of_graph (Nth.graph_zero.mpr rfl)

lemma nth_succ (v i : V) : v.[i + 1] = (sndIdx v).[i] :=
  nth_eq_of_graph (Nth.graph_succ.mpr <| nth_graph _ _)

@[simp] lemma nth_adjoin_zero (x v : V) : (x ∷ v).[0] = x := by
  simp [nth_zero]

@[simp] lemma nth_adjoin_succ (x v i : V) : (x ∷ v).[i + 1] = v.[i] := by
  simp [nth_succ]

@[simp] lemma nth_adjoin_one (x v : V) : (x ∷ v).[1] = v.[0] := by
  simpa using nth_adjoin_succ x v 0

@[simp] lemma nth_adjoin_two (x v : V) : (x ∷ v).[2] = v.[1] := by
  simpa [-nth_adjoin_succ, one_add_one_eq_two] using nth_adjoin_succ x v 1

@[simp] lemma nth_le (v i : V) : v.[i] ≤ v := by
  obtain ⟨x, hx, h⟩ := Nth.exists_le_graph v i
  simpa [nth_eq_of_graph h] using hx

lemma nth_locallyDelta0 : LocallyDelta0Function₂ (nth : V → V → V) where
  graph := by
    have := Nth.graph_locallyDelta0.comp₃ (LocallyDelta0Function.var (V := V) (1 : Fin 3))
      (LocallyDelta0Function.var (V := V) (2 : Fin 3))
      (LocallyDelta0Function.var (V := V) (0 : Fin 3))
    exact this.of_iff fun w ↦ ⟨by rintro h; simp [h, nth_graph], by
      intro h; exact (nth_eq_of_graph (by simpa using h)).symm⟩
  bounded X := by
    use X
    intro w hw
    exact le_trans (nth_le _ _) (hw 0)

lemma adjoin_cases (x : V) : x = 0 ∨ ∃ y v, x = y ∷ v := nil_or_adjoin x

lemma adjoin_induction {P : V → Prop} (hP : LocallyDelta0Pred P)
    (nil : P 0) (adjoin : ∀ x v, P v → P (x ∷ v)) : ∀ v, P v :=
  hP.order_induction <| by
    intro v ih
    rcases nil_or_adjoin v with (rfl | ⟨x, v, rfl⟩)
    · exact nil
    · exact adjoin _ _ (ih v (by simp))

set_option linter.flexible false in
instance nth_defined : 𝚺ᴬ₁-Function₂ (nth : V → V → V) via nthDef := .mk fun v ↦ by
  simp [nthDef]
  constructor
  · intro h; simp [nth_eq_of_graph h]
  · intro h; rw [h]; exact nth_graph _ _

instance nth_definable : 𝚺ᴬ₁-Function₂ (nth : V → V → V) := nth_defined.to_definable

instance nth_definable' (Γ m) : Γᴬ_[m + 1]-Function₂ (nth : V → V → V) :=
  nth_definable.of_sigmaOne

lemma adjoin_absolute (a v : ℕ) : ((a ∷ v : ℕ) : V) = (a : V) ∷ (v : V) := by
  simpa using DefinedFunction.sigmaZero_absolute_func V adjoin_defined adjoin_defined ![a, v]

lemma pi₁_zero : π₁ (0 : V) = 0 := nonpos_iff_eq_zero.mp (pi₁_le_self 0)

lemma pi₂_zero : π₂ (0 : V) = 0 := nonpos_iff_eq_zero.mp (pi₂_le_self 0)

@[simp] lemma nth_zero_idx (i : V) : (0 : V).[i] = 0 :=
  nonpos_iff_eq_zero.mp (nth_le 0 i)

lemma nth_lt_of_pos {v} (hv : 0 < v) (i : V) : v.[i] < v := by
  rcases zero_or_succ v with (rfl | ⟨v, rfl⟩)
  · simp at hv
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp [succ_eq_adjoin v]
  · simp only [succ_eq_adjoin v, nth_adjoin_succ]
    exact lt_of_le_of_lt (nth_le _ _) (by simp)

end nth

/-! ### Recursion on lists -/

namespace VecRec

variable (V)

/-- A recursion on lists in a model of $\mathsf{EA}$, with a monotone bound on its values. -/
structure Construction {arity : ℕ} (β : Arithmetic.VecRec.Blueprint arity) where
  nil (param : Fin arity → V) : V
  adjoin (param : Fin arity → V) (x xs ih : V) : V
  nil_defined : 𝚺ᴬ₁.DefinedFunction nil β.nil
  adjoin_defined :
    𝚺ᴬ₁.DefinedFunction (fun v ↦ adjoin (v ·.succ.succ.succ) (v 0) (v 1) (v 2)) β.adjoin
  nil_locallyDelta0 : LocallyDelta0Function nil
  adjoin_locallyDelta0 : LocallyDelta0Function fun v : Fin (arity + 3) → V ↦
    adjoin (v ·.succ.succ.succ) (v 0) (v 1) (v 2)
  /-- `c.bound param xs` bounds the value at `xs`. -/
  bound (param : Fin arity → V) (xs : V) : V
  nil_le_bound : ∀ param, nil param ≤ bound param 0
  adjoin_le_bound : ∀ param x xs ih, ih ≤ bound param xs →
    adjoin param x xs ih ≤ bound param (x ∷ xs)
  bound_monotone : ∀ param {xs ys}, xs ≤ ys → bound param xs ≤ bound param ys
  bound_locallyDelta0 :
    LocallyDelta0Function fun v : Fin (arity + 1) → V ↦ bound (v ·.succ) (v 0)

variable {V}

namespace Construction

variable {arity : ℕ} {β : Arithmetic.VecRec.Blueprint arity} (c : Construction V β)

/-- The rules generating the graph `⟪xs, y⟫` of the recursion. -/
def Phi (param : Fin arity → V) (C : Set V) (pr : V) : Prop :=
  pr = ⟪0, c.nil param⟫ ∨ (∃ x xs ih, pr = ⟪x ∷ xs, c.adjoin param x xs ih⟫ ∧ ⟪xs, ih⟫ ∈ C)

private lemma phi_iff (param : Fin arity → V) (C pr : V) :
    c.Phi param {x | x ∈ C} pr ↔
    pr = ⟪0, c.nil param⟫ ∨
    (∃ x < pr, ∃ xs < pr, ∃ ih < C, pr = ⟪x ∷ xs, c.adjoin param x xs ih⟫ ∧ ⟪xs, ih⟫ ∈ C) := by
  constructor
  · rintro (h | ⟨x, xs, ih, rfl, hC⟩)
    · left; exact h
    · right
      exact ⟨x, lt_of_lt_of_le (by simp) (le_pair_left _ _),
        xs, lt_of_lt_of_le (by simp) (le_pair_left _ _), ih, lt_of_mem_rng hC, rfl, hC⟩
  · rintro (h | ⟨x, _, xs, _, ih, _, rfl, hC⟩)
    · left; exact h
    · right; exact ⟨x, xs, ih, rfl, hC⟩

lemma phi_locallyDelta0 :
    LocallyDelta0 fun w : Fin (arity + 2) → V ↦ c.Phi (w ·.succ.succ) {x | x ∈ w 1} (w 0) := by
  have hnil : LocallyDelta0 fun w : Fin (arity + 2) → V ↦ w 0 = ⟪0, c.nil (w ·.succ.succ)⟫ :=
    LocallyDelta0.eq (LocallyDelta0Function.var 0) <| LocallyDelta0Function.pairing.comp₂
      (LocallyDelta0Function.const 0) (c.nil_locallyDelta0.retraction fun j ↦ j.succ.succ)
  have hadjoin : LocallyDelta0Function fun y : Fin (arity + 5) → V ↦
      c.adjoin (fun j ↦ y j.succ.succ.succ.succ.succ) (y 2) (y 1) (y 0) := by
    simpa using c.adjoin_locallyDelta0.retraction
      (2 :> 1 :> 0 :> fun j ↦ j.succ.succ.succ.succ.succ)
  have hbody : LocallyDelta0 fun y : Fin (arity + 5) → V ↦
      y 3 = ⟪y 2 ∷ y 1, c.adjoin (fun j ↦ y j.succ.succ.succ.succ.succ) (y 2) (y 1) (y 0)⟫ ∧
        ⟪y 1, y 0⟫ ∈ y 4 := by
    exact (LocallyDelta0.eq (LocallyDelta0Function.var 3) <| LocallyDelta0Function.pairing.comp₂
      (LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 2)
        (LocallyDelta0Function.var 1)) hadjoin).and <|
      LocallyDelta0.mem (LocallyDelta0Function.pairing.comp₂ (LocallyDelta0Function.var 1)
        (LocallyDelta0Function.var 0)) (LocallyDelta0Function.var 4)
  have hex := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 0) <|
    LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1) <|
      LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 3) hbody
  exact (hnil.or hex).of_iff fun w ↦ by simpa using c.phi_iff (w ·.succ.succ) (w 1) (w 0)

/-- The construction of the graph of the recursion. -/
def adjointruction : Fixpoint.Construction V β.blueprint where
  Φ := c.Phi
  defined := .mk ⟨by
    intro v; simp [Arithmetic.VecRec.Blueprint.blueprint, c.nil_defined.iff,
      c.adjoin_defined.iff], by
    intro v
    symm
    simpa [Arithmetic.VecRec.Blueprint.blueprint, c.nil_defined.iff, c.adjoin_defined.iff]
      using c.phi_iff _ _ _⟩
  monotone := by
    rintro C C' hC _ x (h | ⟨v, i, hv, rfl, h⟩)
    · left; exact h
    · right; exact ⟨v, i, hv, rfl, hC h⟩
  Φ_locallyDelta0 := c.phi_locallyDelta0

variable (param : Fin arity → V)

/-- `c.Graph param ⟪xs, y⟫` states that the recursion takes the value `y` at `xs`. -/
def Graph : V → Prop := c.adjointruction.Fixpoint param

lemma graph_defined : 𝚺ᴬ₁.Defined (fun v ↦ c.Graph (v ·.succ) (v 0)) β.graphDef :=
  c.adjointruction.fixpoint_defined

variable {param}

open Classical in
/-- The course-of-values recursion computing the values. -/
noncomputable def courseOfValues : CourseOfValues.Construction V arity where
  val param n T :=
    if n = 0 then c.nil param else c.adjoin param (π₁ (n - 1)) (π₂ (n - 1)) (znth T (π₂ (n - 1)))
  val_locallyDelta0 := by
    have hpred : LocallyDelta0Function fun w : Fin (arity + 2) → V ↦ w 1 - 1 :=
      LocallyDelta0Function.sub.comp₂ (LocallyDelta0Function.var 1) (LocallyDelta0Function.const 1)
    have hpi₁ : LocallyDelta0Function fun w : Fin (arity + 2) → V ↦ π₁ (w 1 - 1) :=
      LocallyDelta0Function.pi₁.comp₁ hpred
    have hpi₂ : LocallyDelta0Function fun w : Fin (arity + 2) → V ↦ π₂ (w 1 - 1) :=
      LocallyDelta0Function.pi₂.comp₁ hpred
    have hznth : LocallyDelta0Function fun w : Fin (arity + 2) → V ↦ znth (w 0) (π₂ (w 1 - 1)) :=
      LocallyDelta0Function.znth.comp₂ (LocallyDelta0Function.var 0) hpi₂
    have hadjoin := c.adjoin_locallyDelta0.comp_cons hpi₁
      (u := (fun w : Fin (arity + 2) → V ↦ π₂ (w 1 - 1)) :>
        (fun w ↦ znth (w 0) (π₂ (w 1 - 1))) :> fun j w ↦ w j.succ.succ) <|
        Fin.forall_fin_succ.mpr ⟨hpi₂, Fin.forall_fin_succ.mpr ⟨hznth, fun j ↦ by
          simpa using LocallyDelta0Function.var j.succ.succ⟩⟩
    exact LocallyDelta0Function.ite (LocallyDelta0.of_definable (by definability))
      (c.nil_locallyDelta0.retraction fun j ↦ j.succ.succ) (by simpa using hadjoin)
  bound := c.bound
  bound_monotone := c.bound_monotone
  bound_locallyDelta0 := c.bound_locallyDelta0

variable (param)

/-- The value of the recursion at `xs`. -/
noncomputable def result (xs : V) : V := c.courseOfValues.result param xs

lemma result_le_bound (xs : V) : c.result param xs ≤ c.bound param xs :=
  c.courseOfValues.result_le_bound (v := param) xs

@[simp] lemma result_nil : c.result param (0 : V) = c.nil param := by
  have : c.courseOfValues.val param 0 (c.courseOfValues.table param 0) = c.nil param := by
    simp [courseOfValues]
  rw [result, c.courseOfValues.result_eq_val (by rw [this]; exact c.nil_le_bound param), this]

@[simp] lemma result_adjoin (x xs : V) :
    c.result param (x ∷ xs) = c.adjoin param x xs (c.result param xs) := by
  have hz : znth (c.courseOfValues.table param (x ∷ xs)) xs = c.result param xs :=
    c.courseOfValues.znth_table (show xs < x ∷ xs by simp)
  have e : x ∷ xs - 1 = ⟪x, xs⟫ := by simp [adjoin_def]
  have hval : c.courseOfValues.val param (x ∷ xs) (c.courseOfValues.table param (x ∷ xs)) =
      c.adjoin param x xs (c.result param xs) := by
    change (if x ∷ xs = 0 then c.nil param else c.adjoin param (π₁ (x ∷ xs - 1)) (π₂ (x ∷ xs - 1))
      (znth (c.courseOfValues.table param (x ∷ xs)) (π₂ (x ∷ xs - 1)))) = _
    simp [e, hz]
  have hle := c.adjoin_le_bound param x xs _ (c.result_le_bound param xs)
  rw [← hval] at hle
  rw [result, c.courseOfValues.result_eq_val hle, hval]

lemma result_locallyDelta0 :
    LocallyDelta0Function fun w : Fin (arity + 1) → V ↦ c.result (w ·.succ) (w 0) :=
  c.courseOfValues.result_locallyDelta0

private lemma limSeq_comp {n : ℕ} {f : (Fin n → V) → V} (hf : LocallyDelta0Function f) :
    LocallyDelta0Function fun w : Fin n → V ↦ c.adjointruction.limSeq param (f w) := by
  simpa using c.adjointruction.limSeq_locallyDelta0.comp_cons hf fun j ↦
    LocallyDelta0Function.const (param j)

private lemma result_comp {n : ℕ} {f : (Fin n → V) → V} (hf : LocallyDelta0Function f) :
    LocallyDelta0Function fun w : Fin n → V ↦ c.result param (f w) := by
  simpa using c.result_locallyDelta0.comp_cons hf fun j ↦ LocallyDelta0Function.const (param j)

lemma eq_of_mem_limSeq {s z : V} (h : z ∈ c.adjointruction.limSeq param s) :
    z = ⟪π₁ z, c.result param (π₁ z)⟫ := by
  have hR : LocallyDelta0 fun y : Fin 2 → V ↦
      y 0 ∈ c.adjointruction.limSeq param (y 1) →
        y 0 = ⟪π₁ (y 0), c.result param (π₁ (y 0))⟫ := by
    exact (LocallyDelta0.mem (LocallyDelta0Function.var (0 : Fin 2))
      (c.limSeq_comp param (LocallyDelta0Function.var 1))).imp <|
      LocallyDelta0.eq (LocallyDelta0Function.var 0) <| LocallyDelta0Function.pairing.comp₂
        (LocallyDelta0Function.pi₁.comp₁ (LocallyDelta0Function.var 0))
        (c.result_comp param <| LocallyDelta0Function.pi₁.comp₁ (LocallyDelta0Function.var 0))
  have hP : LocallyDelta0Pred fun s ↦ ∀ z < c.adjointruction.limSeq param s,
      z ∈ c.adjointruction.limSeq param s → z = ⟪π₁ z, c.result param (π₁ z)⟫ :=
    (LocallyDelta0.ball_lt_function
      (c.limSeq_comp param (LocallyDelta0Function.var (V := V) (0 : Fin 1))) hR).of_iff
        fun w ↦ by simp
  have : ∀ s, ∀ z < c.adjointruction.limSeq param s,
      z ∈ c.adjointruction.limSeq param s → z = ⟪π₁ z, c.result param (π₁ z)⟫ := by
    apply LocallyDelta0Pred.succ_induction hP
    · intro z _ hz
      simp at hz
    · intro s ih z _ hz
      have hΦ : c.Phi param {z | z ∈ c.adjointruction.limSeq param s} z :=
        (c.adjointruction.mem_limSeq_succ_iff.mp hz).2
      rcases hΦ with (rfl | ⟨x, xs, y, rfl, hC⟩)
      · simp
      · have hC : ⟪xs, y⟫ ∈ c.adjointruction.limSeq param s := hC
        have := ih _ (lt_of_mem hC) hC
        have hy : y = c.result param xs := by simpa using congrArg (fun p ↦ π₂ p) this
        simp [hy]
  exact this s z (lt_of_mem h) h

lemma mem_limSeq_result (xs : V) :
    ⟪xs, c.result param xs⟫ ∈
      c.adjointruction.limSeq param (⟪xs, c.bound param xs⟫ + xs + 1) := by
  set K := ⟪xs, c.bound param xs⟫
  have hP : LocallyDelta0Pred fun ys ↦
      ys ≤ xs → ⟪ys, c.result param ys⟫ ∈ c.adjointruction.limSeq param (K + ys + 1) := by
    exact (LocallyDelta0.le (LocallyDelta0Function.var (0 : Fin 1))
      (LocallyDelta0Function.const xs)).imp <|
      LocallyDelta0.mem (LocallyDelta0Function.pairing.comp₂ (LocallyDelta0Function.var 0)
        (c.result_comp param (LocallyDelta0Function.var 0)))
        (c.limSeq_comp param <| LocallyDelta0Function.add_one <|
          LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.const K)
            (LocallyDelta0Function.var 0))
  have : ∀ ys, ys ≤ xs →
      ⟪ys, c.result param ys⟫ ∈ c.adjointruction.limSeq param (K + ys + 1) := by
    apply LocallyDelta0Pred.order_induction hP
    intro ys ih hys
    have hle : ⟪ys, c.result param ys⟫ ≤ K :=
      pair_le_pair hys (le_trans (c.result_le_bound param ys) (c.bound_monotone param hys))
    apply c.adjointruction.mem_limSeq_succ_iff.mpr
    apply And.intro (le_trans hle le_self_add)
    change c.Phi param _ _
    rcases nil_or_adjoin ys with (rfl | ⟨x, ys', rfl⟩)
    · left; simp
    · right
      use x, ys', c.result param ys'
      constructor
      · simp
      · have hys' : ys' < x ∷ ys' := by simp
        exact c.adjointruction.limSeq_cumulative
          (by rw [add_assoc]; exact add_le_add_right (succ_le_iff_lt.mpr hys') K)
          (ih ys' hys' (le_trans hys'.le hys))
  exact this xs le_rfl

variable {param}

lemma graph_iff {xs y : V} : c.Graph param ⟪xs, y⟫ ↔ y = c.result param xs := by
  constructor
  · rintro ⟨s, h⟩
    simpa using c.eq_of_mem_limSeq param h
  · rintro rfl
    exact ⟨_, c.mem_limSeq_result param xs⟩

lemma graph_nil {l : V} : c.Graph param ⟪0, l⟫ ↔ l = c.nil param := by
  simp [graph_iff]

lemma graph_adjoin {x xs y : V} :
    c.Graph param ⟪x ∷ xs, y⟫ ↔ ∃ y', y = c.adjoin param x xs y' ∧ c.Graph param ⟪xs, y'⟫ := by
  simp [graph_iff]

variable (param)

lemma result_graph (xs : V) : c.Graph param ⟪xs, c.result param xs⟫ := c.graph_iff.mpr rfl

lemma graph_exists (xs : V) : ∃ y, c.Graph param ⟪xs, y⟫ := ⟨_, c.result_graph param xs⟩

variable {param}

lemma graph_unique {xs y₁ y₂ : V} :
    c.Graph param ⟪xs, y₁⟫ → c.Graph param ⟪xs, y₂⟫ → y₁ = y₂ := by
  simp only [graph_iff]
  rintro rfl rfl; rfl

variable (param)

lemma graph_existsUnique (xs : V) : ∃! y, c.Graph param ⟪xs, y⟫ :=
  ExistsUnique.intro _ (c.result_graph param xs) fun _ h ↦
    c.graph_unique h (c.result_graph param xs)

lemma result_eq_of_graph {xs y : V} (h : c.Graph param ⟪xs, y⟫) : c.result param xs = y :=
  (c.graph_iff.mp h).symm

set_option linter.flexible false in
lemma result_defined :
    𝚺ᴬ₁.DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0)) β.resultDef := .mk fun v ↦ by
  simp [Arithmetic.VecRec.Blueprint.resultDef, c.graph_defined.iff]
  constructor
  · intro h; symm; simpa using c.result_eq_of_graph _ h
  · intro h; rw [h]; exact c.result_graph _ _

@[simp] lemma eval_resultDef (v : Fin (arity + 2) → V) :
    β.resultDef.val.Evalb v ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.iff

lemma result_definable : 𝚺ᴬ₁.DefinableFunction (fun v ↦ c.result (v ·.succ) (v 0)) :=
  c.result_defined.to_definable

end Construction

end VecRec

/-! ### Length of a list -/

namespace Len

noncomputable def adjointruction : VecRec.Construction V Arithmetic.Len.blueprint where
  nil _ := 0
  adjoin _ _ _ ih := ih + 1
  nil_defined := .mk fun v ↦ by simp [Arithmetic.Len.blueprint]
  adjoin_defined := .mk fun v ↦ by simp [Arithmetic.Len.blueprint]
  nil_locallyDelta0 := LocallyDelta0Function.const 0
  adjoin_locallyDelta0 := LocallyDelta0Function.add_one (LocallyDelta0Function.var 2)
  bound _ xs := xs
  nil_le_bound _ := le_rfl
  adjoin_le_bound _ x xs _ h := succ_le_iff_lt.mpr (lt_of_le_of_lt h (lt_adjoin' x xs))
  bound_monotone _ _ _ h := h
  bound_locallyDelta0 := LocallyDelta0Function.var 0

end Len

section len

/-- The length of the list `v`. -/
noncomputable def len (v : V) : V := Len.adjointruction.result ![] v

@[simp] lemma len_nil : len (0 : V) = 0 := by simp [len, Len.adjointruction]

@[simp] lemma len_adjoin (x v : V) : len (x ∷ v) = len v + 1 := by simp [len, Len.adjointruction]

instance len_defined : 𝚺ᴬ₁-Function₁ (len : V → V) via lenDef :=
  Len.adjointruction.result_defined

instance len_definable : 𝚺ᴬ₁-Function₁ (len : V → V) := len_defined.to_definable

instance len_definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (len : V → V) := len_definable.of_sigmaOne

lemma len_locallyDelta0 : LocallyDelta0Function₁ (len : V → V) := by
  convert Len.adjointruction.result_locallyDelta0 (V := V) using 3
  simp [len, Matrix.empty_eq]

@[simp] lemma len_zero_iff_eq_nil {v : V} : len v = 0 ↔ v = 0 := by
  rcases nil_or_adjoin v with (rfl | ⟨x, v, rfl⟩) <;> simp

@[simp] lemma len_le (v : V) : len v ≤ v := by
  have hP : LocallyDelta0Pred fun v : V ↦ len v ≤ v :=
    LocallyDelta0.le (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
      (LocallyDelta0Function.var (0 : Fin 1))
  apply adjoin_induction hP
  · simp
  · intro x v ih
    rw [len_adjoin]
    exact succ_le_iff_lt.mpr (lt_of_le_of_lt ih (lt_adjoin' x v))

end len

lemma nth_lt_len {v i : V} (hl : len v ≤ i) : v.[i] = 0 := by
  have hR : LocallyDelta0 fun w : Fin 2 → V ↦ len (w 1) ≤ w 0 → (w 1).[w 0] = 0 :=
    (LocallyDelta0.le (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2)))
      (LocallyDelta0Function.var 0)).imp
      (LocallyDelta0.eq (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
        (LocallyDelta0Function.var 0)) (LocallyDelta0Function.const 0))
  have hP : LocallyDelta0Pred fun u ↦ ∀ j ≤ i, len u ≤ j → u.[j] = 0 :=
    (LocallyDelta0.ball_le_function (LocallyDelta0Function.const i) hR).of_iff fun w ↦ by simp
  have : ∀ j ≤ i, len v ≤ j → v.[j] = 0 := by
    apply adjoin_induction hP
    · intro j _ _
      simp
    · intro x v ih j hj hl'
      rcases zero_or_succ j with (rfl | ⟨j, rfl⟩)
      · simp at hl'
      · simpa using ih j (le_trans le_self_add hj) (by simpa using hl')
  exact this i le_rfl hl

lemma nth_ext {v₁ v₂ : V} (hl : len v₁ = len v₂) (H : ∀ i < len v₁, v₁.[i] = v₂.[i]) :
    v₁ = v₂ := by
  have hR : LocallyDelta0 fun w : Fin 2 → V ↦
      len (w 1) = len (w 0) → (∀ i < len (w 1), (w 1).[i] = (w 0).[i]) → w 1 = w 0 := by
    apply LocallyDelta0.imp
    · exact LocallyDelta0.eq (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2)))
        (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 2)))
    apply LocallyDelta0.imp
    · have hnth : LocallyDelta0 fun t : Fin 3 → V ↦ (t 2).[t 0] = (t 1).[t 0] :=
        LocallyDelta0.eq (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 2)
          (LocallyDelta0Function.var 0)) (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
            (LocallyDelta0Function.var 0))
      exact (LocallyDelta0.ball_lt_function
        (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2))) hnth).of_iff
          fun w ↦ by simp
    · exact LocallyDelta0.eq (LocallyDelta0Function.var (1 : Fin 2)) (LocallyDelta0Function.var 0)
  have hP : LocallyDelta0Pred fun u ↦ ∀ u' ≤ v₂, len u = len u' →
      (∀ i < len u, u.[i] = u'.[i]) → u = u' :=
    (LocallyDelta0.ball_le_function (LocallyDelta0Function.const v₂) hR).of_iff fun w ↦ by simp
  have : ∀ u' ≤ v₂, len v₁ = len u' → (∀ i < len v₁, v₁.[i] = u'.[i]) → v₁ = u' := by
    apply adjoin_induction hP
    · intro u' _ h _
      exact Eq.symm <| len_zero_iff_eq_nil.mp (by simp [← h])
    · intro x v ih u' hu' hl H
      rcases nil_or_adjoin u' with (rfl | ⟨y, w, rfl⟩)
      · simp at hl
      have hx : x = y := by simpa using H 0 (by simp)
      have hv : v = w :=
        ih w (le_trans (lt_adjoin' y w).le hu') (by simpa using hl)
          (by intro i hi; simpa using H (i + 1) (by simpa using hi))
      simp [hx, hv]
  exact this v₂ le_rfl hl H

lemma nth_ext' (l : V) {v₁ v₂ : V} (hl₁ : len v₁ = l) (hl₂ : len v₂ = l)
    (H : ∀ i < l, v₁.[i] = v₂.[i]) : v₁ = v₂ := by
  rcases hl₂; exact nth_ext hl₁ (by simpa [hl₁] using H)

lemma le_of_nth_le_nth {v₁ v₂ : V} (hl : len v₁ = len v₂)
    (H : ∀ i < len v₁, v₁.[i] ≤ v₂.[i]) : v₁ ≤ v₂ := by
  have hR : LocallyDelta0 fun w : Fin 2 → V ↦
      len (w 1) = len (w 0) → (∀ i < len (w 1), (w 1).[i] ≤ (w 0).[i]) → w 1 ≤ w 0 := by
    apply LocallyDelta0.imp
    · exact LocallyDelta0.eq (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2)))
        (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 2)))
    apply LocallyDelta0.imp
    · have hnth : LocallyDelta0 fun t : Fin 3 → V ↦ (t 2).[t 0] ≤ (t 1).[t 0] :=
        LocallyDelta0.le (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 2)
          (LocallyDelta0Function.var 0)) (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
            (LocallyDelta0Function.var 0))
      exact (LocallyDelta0.ball_lt_function
        (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2))) hnth).of_iff
          fun w ↦ by simp
    · exact LocallyDelta0.le (LocallyDelta0Function.var (1 : Fin 2)) (LocallyDelta0Function.var 0)
  have hP : LocallyDelta0Pred fun u ↦ ∀ u' ≤ v₂, len u = len u' →
      (∀ i < len u, u.[i] ≤ u'.[i]) → u ≤ u' :=
    (LocallyDelta0.ball_le_function (LocallyDelta0Function.const v₂) hR).of_iff fun w ↦ by simp
  have : ∀ u' ≤ v₂, len v₁ = len u' → (∀ i < len v₁, v₁.[i] ≤ u'.[i]) → v₁ ≤ u' := by
    apply adjoin_induction hP
    · intro u' _ _ _
      simp
    · intro x v ih u' hu' hl H
      rcases nil_or_adjoin u' with (rfl | ⟨y, w, rfl⟩)
      · simp at hl
      have hx : x ≤ y := by simpa using H 0 (by simp)
      have hv : v ≤ w :=
        ih w (le_trans (lt_adjoin' y w).le hu') (by simpa using hl)
          (by intro i hi; simpa using H (i + 1) (by simpa using hi))
      exact adjoin_le_adjoin hx hv
  exact this v₂ le_rfl hl H

lemma nth_lt_self {v i : V} (hi : i < len v) : v.[i] < v := by
  have hR : LocallyDelta0 fun w : Fin 2 → V ↦ w 0 < len (w 1) → (w 1).[w 0] < w 1 :=
    (LocallyDelta0.lt (LocallyDelta0Function.var (0 : Fin 2))
      (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2)))).imp
      (LocallyDelta0.lt (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
        (LocallyDelta0Function.var 0)) (LocallyDelta0Function.var 1))
  have hP : LocallyDelta0Pred fun u ↦ ∀ j ≤ i, j < len u → u.[j] < u :=
    (LocallyDelta0.ball_le_function (LocallyDelta0Function.const i) hR).of_iff fun w ↦ by simp
  have : ∀ j ≤ i, j < len v → v.[j] < v := by
    apply adjoin_induction hP
    · intro j _ h
      simp at h
    · intro x v ih j hj hl
      rcases zero_or_succ j with (rfl | ⟨j, rfl⟩)
      · simp
      · simpa using lt_trans (ih j (le_trans le_self_add hj) (by simpa using hl)) (by simp)
  exact this i le_rfl hi

theorem sigmaZero_skolem_vec {R : V → V → Prop} (hR : LocallyDelta0Rel R) {l B : V}
    (H : ∀ x < l, ∃ y < B, R x y) : ∃ v, len v = l ∧ ∀ i < l, R i v.[i] := by
  have hE : LocallyDelta0Function fun w : Fin 1 → V ↦ Exp.exp (Exp.exp (w 0 + w 0 + B + 3)) :=
    LocallyDelta0Function.exp.comp₁ <| LocallyDelta0Function.exp.comp₁ <|
      LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.add.comp₂
        (LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.var 0)
          (LocallyDelta0Function.var 0)) (LocallyDelta0Function.const B))
        (LocallyDelta0Function.const 3)
  have hRi : LocallyDelta0 fun t : Fin 3 → V ↦ R (l - t 2 + t 0) (t 1).[t 0] :=
    (hR.comp₂ (LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.sub.comp₂
      (LocallyDelta0Function.const l) (LocallyDelta0Function.var 2)) (LocallyDelta0Function.var 0))
      (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0))).of_iff
        fun t ↦ by simp
  have hbody : LocallyDelta0 fun u : Fin 2 → V ↦
      len (u 0) = u 1 ∧ ∀ i < u 1, R (l - u 1 + i) (u 0).[i] :=
    (LocallyDelta0.eq (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 2)))
      (LocallyDelta0Function.var 1)).and
      ((LocallyDelta0.ball_lt_function (LocallyDelta0Function.var (1 : Fin 2)) hRi).of_iff
        fun w ↦ by simp)
  have hP : LocallyDelta0Pred fun k ↦ k ≤ l →
      ∃ v ≤ Exp.exp (Exp.exp (k + k + B + 3)), len v = k ∧ ∀ i < k, R (l - k + i) v.[i] :=
    ((LocallyDelta0.le (LocallyDelta0Function.var (0 : Fin 1))
      (LocallyDelta0Function.const l)).imp (LocallyDelta0.bexs_le_function hE hbody)).of_iff
        fun w ↦ by simp
  have key : ∀ k ≤ l, ∃ v ≤ Exp.exp (Exp.exp (k + k + B + 3)),
      len v = k ∧ ∀ i < k, R (l - k + i) v.[i] := by
    apply LocallyDelta0Pred.succ_induction hP
    · intro _
      use 0
      and_intros <;> simp
    · intro k ih hk
      obtain ⟨v, hv, hvk, hvR⟩ := ih (le_trans le_self_add hk)
      obtain ⟨y, hyB, hy⟩ := H (l - (k + 1)) (by simp [tsub_lt_iff_left hk])
      use y ∷ v
      and_intros
      · have e : k + 1 + (k + 1) + B + 3 = (k + k + B + 3) + 2 := by grind
        rw [e]
        have hn : (1 : V) ≤ k + k + B + 3 := le_trans (by norm_num) le_add_self
        exact adjoin_le_exp_exp hn
          (le_exp_exp (le_trans hyB.le (le_trans le_add_self le_self_add))) hv
      · simp [hvk]
      · intro i hi
        rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
        · simpa using hy
        · simpa [sub_succ_add_succ (succ_le_iff_lt.mp hk) i] using hvR i (by simpa [hvk] using hi)
  obtain ⟨v, -, hv⟩ := key l le_rfl
  use v
  simpa using hv

lemma eq_singleton_iff_len_eq_one {v : V} : len v = 1 ↔ ∃ x, v = ?[x] := by
  constructor
  · intro h; exact ⟨v.[0], nth_ext (by simp [h]) (by simp [h])⟩
  · rintro ⟨x, rfl⟩; simp

lemma eq_doubleton_of_len_eq_two {v : V} : len v = 2 ↔ ∃ x y, v = ?[x, y] := by
  constructor
  · intro h; exact ⟨v.[0], v.[1],
      nth_ext (by simp [h, one_add_one_eq_two])
        (by simp [lt_two_iff_le_one, le_one_iff_eq_zero_or_one, h])⟩
  · rintro ⟨x, y, rfl⟩; simp [one_add_one_eq_two]

/-! ### Maximum of a list -/

lemma LocallyDelta0Function.max : LocallyDelta0Function₂ (Max.max : V → V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, by definability⟩

namespace ListMax

noncomputable def adjointruction : VecRec.Construction V Arithmetic.ListMax.blueprint where
  nil _ := 0
  adjoin _ x _ ih := max x ih
  nil_defined := .mk fun v ↦ by simp [Arithmetic.ListMax.blueprint]
  adjoin_defined := .mk fun v ↦ by simp [Arithmetic.ListMax.blueprint]
  nil_locallyDelta0 := LocallyDelta0Function.const 0
  adjoin_locallyDelta0 :=
    LocallyDelta0Function.max.comp₂ (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 2)
  bound _ xs := xs
  nil_le_bound _ := le_rfl
  adjoin_le_bound _ x xs _ h := max_le (lt_adjoin x xs).le (le_trans h (lt_adjoin' x xs).le)
  bound_monotone _ _ _ h := h
  bound_locallyDelta0 := LocallyDelta0Function.var 0

end ListMax

section listMax

/-- The maximum of the elements of the list `v`. -/
noncomputable def listMax (v : V) : V := ListMax.adjointruction.result ![] v

@[simp] lemma listMax_nil : listMax (0 : V) = 0 := by simp [listMax, ListMax.adjointruction]

@[simp] lemma listMax_adjoin (x v : V) : listMax (x ∷ v) = max x (listMax v) := by
  simp [listMax, ListMax.adjointruction]

instance listMax_defined : 𝚺ᴬ₁-Function₁ (listMax : V → V) via listMaxDef :=
  ListMax.adjointruction.result_defined

instance listMax_definable : 𝚺ᴬ₁-Function₁ (listMax : V → V) := listMax_defined.to_definable

instance listMax_definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (listMax : V → V) :=
  listMax_definable.of_sigmaOne

lemma listMax_locallyDelta0 : LocallyDelta0Function₁ (listMax : V → V) := by
  convert ListMax.adjointruction.result_locallyDelta0 (V := V) using 3
  simp [listMax, Matrix.empty_eq]

lemma nth_le_listMax {i v : V} (h : i < len v) : v.[i] ≤ listMax v := by
  have hR : LocallyDelta0 fun w : Fin 2 → V ↦ w 0 < len (w 1) → (w 1).[w 0] ≤ listMax (w 1) :=
    (LocallyDelta0.lt (LocallyDelta0Function.var (0 : Fin 2))
      (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2)))).imp
      (LocallyDelta0.le (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
        (LocallyDelta0Function.var 0)) (listMax_locallyDelta0.comp₁ (LocallyDelta0Function.var 1)))
  have hP : LocallyDelta0Pred fun u ↦ ∀ j ≤ i, j < len u → u.[j] ≤ listMax u :=
    (LocallyDelta0.ball_le_function (LocallyDelta0Function.const i) hR).of_iff fun w ↦ by simp
  have : ∀ j ≤ i, j < len v → v.[j] ≤ listMax v := by
    apply adjoin_induction hP
    · intro j _ h
      simp at h
    · intro x v ih j hj hl
      rcases zero_or_succ j with (rfl | ⟨j, rfl⟩)
      · simp
      · simp [ih j (le_trans le_self_add hj) (by simpa using hl)]
  exact this i le_rfl h

lemma listMaxss_le {v z : V} (h : ∀ i < len v, v.[i] ≤ z) : listMax v ≤ z := by
  have hnth : LocallyDelta0 fun t : Fin 2 → V ↦ (t 1).[t 0] ≤ z :=
    LocallyDelta0.le (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
      (LocallyDelta0Function.var 0)) (LocallyDelta0Function.const z)
  have hP : LocallyDelta0Pred fun u : V ↦ (∀ i < len u, u.[i] ≤ z) → listMax u ≤ z :=
    ((LocallyDelta0.ball_lt_function
      (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))) hnth).imp
        (LocallyDelta0.le (listMax_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
          (LocallyDelta0Function.const z))).of_iff fun w ↦ by simp
  have : (∀ i < len v, v.[i] ≤ z) → listMax v ≤ z := by
    apply adjoin_induction hP
    · intro _
      simp
    · intro x v ih h
      simp only [listMax_adjoin, max_le_iff]
      constructor
      · simpa using h 0 (by simp)
      · exact ih (fun i hi ↦ by simpa using h (i + 1) (by simp [hi]))
  exact this h

lemma listMaxss_le_iff {v z : V} : listMax v ≤ z ↔ ∀ i < len v, v.[i] ≤ z := by
  constructor
  · intro h i hi; exact le_trans (nth_le_listMax hi) h
  · exact listMaxss_le

end listMax

/-! ### The last `k` elements of a list -/

namespace TakeLast

open Classical in
noncomputable def adjointruction : VecRec.Construction V Arithmetic.TakeLast.blueprint where
  nil _ := 0
  adjoin param x xs ih := if len xs < param 0 then x ∷ xs else ih
  nil_defined := .mk fun v ↦ by simp [Arithmetic.TakeLast.blueprint]
  adjoin_defined := .mk fun v ↦ by
    suffices
      (len (v 2) < v 4 → v 0 = v 1 ∷ v 2) ∧ (v 4 ≤ len (v 2) → v 0 = v 3) ↔
      (v 0 = if len (v 2) < v 4 then v 1 ∷ v 2 else v 3) by
      simpa [Arithmetic.TakeLast.blueprint, Fin.isValue]
    rcases lt_or_ge (len (v 2)) (v 4) with (hv | hv)
    · simp [hv]
    · simp [hv, not_lt_of_ge hv]
  nil_locallyDelta0 := LocallyDelta0Function.const 0
  adjoin_locallyDelta0 := LocallyDelta0Function.ite
    (LocallyDelta0.lt (len_locallyDelta0.comp₁ (LocallyDelta0Function.var 1))
      (LocallyDelta0Function.var 3))
    (LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 0)
      (LocallyDelta0Function.var 1)) (LocallyDelta0Function.var 2)
  bound _ xs := xs
  nil_le_bound _ := le_rfl
  adjoin_le_bound _ x xs _ h := by
    split_ifs
    · exact le_rfl
    · exact le_trans h (lt_adjoin' x xs).le
  bound_monotone _ _ _ h := h
  bound_locallyDelta0 := LocallyDelta0Function.var 0

end TakeLast

section takeLast

/-- The last `k` elements of the list `v`. -/
noncomputable def takeLast (v k : V) : V := TakeLast.adjointruction.result ![k] v

@[simp] lemma takeLast_nil (k : V) : takeLast (0 : V) k = 0 := by
  simp [takeLast, TakeLast.adjointruction]

open Classical in
lemma takeLast_adjoin (x v k : V) :
    takeLast (x ∷ v) k = if len v < k then x ∷ v else takeLast v k := by
  simp [takeLast, TakeLast.adjointruction]

instance takeLast_defined : 𝚺ᴬ₁-Function₂ (takeLast : V → V → V) via takeLastDef :=
  TakeLast.adjointruction.result_defined

instance takeLast_definable : 𝚺ᴬ₁-Function₂ (takeLast : V → V → V) := takeLast_defined.to_definable

instance takeLast_definable' (Γ m) : Γᴬ_[m + 1]-Function₂ (takeLast : V → V → V) :=
  takeLast_definable.of_sigmaOne

lemma takeLast_locallyDelta0 : LocallyDelta0Function₂ (takeLast : V → V → V) := by
  convert TakeLast.adjointruction.result_locallyDelta0 (V := V) using 3
  simp [takeLast]
  rfl

lemma len_takeLast {v k : V} (h : k ≤ len v) : len (takeLast v k) = k := by
  have hP : LocallyDelta0Pred fun u ↦ k ≤ len u → len (takeLast u k) = k :=
    ((LocallyDelta0.le (LocallyDelta0Function.const k)
      (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))).imp
      (LocallyDelta0.eq (len_locallyDelta0.comp₁ (takeLast_locallyDelta0.comp₂
        (LocallyDelta0Function.var (0 : Fin 1)) (LocallyDelta0Function.const k)))
        (LocallyDelta0Function.const k))).of_iff fun w ↦ by simp
  have : k ≤ len v → len (takeLast v k) = k := by
    apply adjoin_induction hP
    · intro h
      simp_all
    · intro x v ih h
      have : k = len v + 1 ∨ k ≤ len v := by
        rcases eq_or_lt_of_le h with (h | h)
        · left; simpa using h
        · right; simpa [lt_succ_iff_le] using h
      rcases this with (rfl | hkv)
      · simp [takeLast_adjoin]
      · simp [takeLast_adjoin, not_lt_of_ge hkv, ih hkv]
  exact this h

@[simp] lemma takeLast_len_self (v : V) : takeLast v (len v) = v := by
  rcases nil_or_adjoin v with (rfl | ⟨x, v, rfl⟩) <;> simp [takeLast_adjoin]

@[simp] lemma takeLast_zero (v : V) : takeLast v 0 = 0 := by
  have hP : LocallyDelta0Pred fun u : V ↦ takeLast u 0 = 0 :=
    LocallyDelta0.eq (takeLast_locallyDelta0.comp₂ (LocallyDelta0Function.var (0 : Fin 1))
      (LocallyDelta0Function.const 0)) (LocallyDelta0Function.const 0)
  apply adjoin_induction hP
  · simp
  · intro x v ih
    simp [takeLast_adjoin, ih]

lemma takeLast_succ_of_lt {i v : V} (h : i < len v) :
    takeLast v (i + 1) = v.[len v - (i + 1)] ∷ takeLast v i := by
  have hR : LocallyDelta0 fun w : Fin 2 → V ↦ w 0 < len (w 1) →
      takeLast (w 1) (w 0 + 1) = (w 1).[len (w 1) - (w 0 + 1)] ∷ takeLast (w 1) (w 0) :=
    (LocallyDelta0.lt (LocallyDelta0Function.var (0 : Fin 2))
      (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2)))).imp <|
      LocallyDelta0.eq (takeLast_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
        (LocallyDelta0Function.add_one (LocallyDelta0Function.var 0)))
        (LocallyDelta0Function.adjoin.comp₂
          (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
            (LocallyDelta0Function.sub.comp₂ (len_locallyDelta0.comp₁ (LocallyDelta0Function.var 1))
              (LocallyDelta0Function.add_one (LocallyDelta0Function.var 0))))
          (takeLast_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
            (LocallyDelta0Function.var 0)))
  have hP : LocallyDelta0Pred fun u ↦ ∀ j ≤ i, j < len u →
      takeLast u (j + 1) = u.[len u - (j + 1)] ∷ takeLast u j :=
    (LocallyDelta0.ball_le_function (LocallyDelta0Function.const i) hR).of_iff fun w ↦ by simp
  have : ∀ j ≤ i, j < len v → takeLast v (j + 1) = v.[len v - (j + 1)] ∷ takeLast v j := by
    apply adjoin_induction hP
    · intro j _ h
      simp at h
    · intro x v ih j hj hl
      rcases show j = len v ∨ j < len v from
        eq_or_lt_of_le (by simpa [lt_succ_iff_le] using hl) with (rfl | hi)
      · simp [takeLast_adjoin]
      · have : len v - j = len v - (j + 1) + 1 := by
          rw [← Arithmetic.sub_sub, sub_add_self_of_le
            (le_tsub_of_add_le_left (lt_iff_succ_le.mp hi))]
        simpa [takeLast_adjoin, lt_succ_iff_le, not_le_of_gt hi, this, not_lt_of_gt hi,
          add_tsub_add_eq_tsub_right] using ih j hj hi
  exact this i le_rfl h

end takeLast

/-! ### Concatenation -/

namespace Concat

noncomputable def adjointruction : VecRec.Construction V Arithmetic.Concat.blueprint where
  nil param := ?[param 0]
  adjoin _ x _ ih := x ∷ ih
  nil_defined := .mk fun v ↦ by simp [Arithmetic.Concat.blueprint]
  adjoin_defined := .mk fun v ↦ by simp [Arithmetic.Concat.blueprint, Fin.isValue]
  nil_locallyDelta0 := LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 0)
    (LocallyDelta0Function.const 0)
  adjoin_locallyDelta0 :=
    LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 2)
  bound param xs := Exp.exp (Exp.exp (xs + xs + param 0 + 3))
  nil_le_bound param := by
    have e : (0 : V) + 0 + param 0 + 3 = param 0 + 1 + 2 := by grind
    rw [e]
    exact adjoin_le_exp_exp (le_add_self.trans' (by norm_num))
      (le_exp_exp le_self_add) (le_exp_exp zero_le)
  adjoin_le_bound param x xs ih h := by
    have hm : xs + 1 ≤ x ∷ xs := succ_le_iff_lt.mpr (lt_adjoin' x xs)
    have hn : xs + xs + param 0 + 3 ≤ (x ∷ xs) + (x ∷ xs) + param 0 + 1 := by
      calc xs + xs + param 0 + 3 = (xs + 1) + (xs + 1) + param 0 + 1 := by grind
        _ ≤ (x ∷ xs) + (x ∷ xs) + param 0 + 1 :=
          add_le_add (add_le_add (add_le_add hm hm) le_rfl) le_rfl
    have hx : x ≤ (x ∷ xs) + (x ∷ xs) + param 0 + 1 :=
      le_trans (lt_adjoin x xs).le (le_trans le_self_add (le_trans le_self_add le_self_add))
    have e : (x ∷ xs) + (x ∷ xs) + param 0 + 3 = (x ∷ xs) + (x ∷ xs) + param 0 + 1 + 2 := by
      grind
    rw [e]
    exact adjoin_le_exp_exp (le_add_self.trans' (by norm_num)) (le_exp_exp hx)
      (le_trans h (exp_monotone_le.mpr (exp_monotone_le.mpr hn)))
  bound_monotone _ _ _ h :=
    exp_monotone_le.mpr (exp_monotone_le.mpr
      (add_le_add (add_le_add (add_le_add h h) le_rfl) le_rfl))
  bound_locallyDelta0 := LocallyDelta0Function.exp.comp₁ <| LocallyDelta0Function.exp.comp₁ <|
    LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.add.comp₂
      (LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.var 0)
        (LocallyDelta0Function.var 0)) (LocallyDelta0Function.var 1))
      (LocallyDelta0Function.const 3)

end Concat

section concat

/-- The list `v` followed by `z`. -/
noncomputable def concat (v z : V) : V := Concat.adjointruction.result ![z] v

@[simp] lemma concat_nil (z : V) : concat 0 z = ?[z] := by
  simp [concat, Concat.adjointruction]

@[simp] lemma concat_adjoin (x v z : V) : concat (x ∷ v) z = x ∷ concat v z := by
  simp [concat, Concat.adjointruction]

instance concat_defined : 𝚺ᴬ₁-Function₂ (concat : V → V → V) via concatDef :=
  Concat.adjointruction.result_defined

instance concat_definable : 𝚺ᴬ₁-Function₂ (concat : V → V → V) := concat_defined.to_definable

instance concat_definable' (Γ m) : Γᴬ_[m + 1]-Function₂ (concat : V → V → V) :=
  concat_definable.of_sigmaOne

lemma concat_locallyDelta0 : LocallyDelta0Function₂ (concat : V → V → V) := by
  convert Concat.adjointruction.result_locallyDelta0 (V := V) using 3
  simp [concat]
  rfl

@[simp] lemma len_concat (v z : V) : len (concat v z) = len v + 1 := by
  have hP : LocallyDelta0Pred fun u : V ↦ len (concat u z) = len u + 1 :=
    LocallyDelta0.eq (len_locallyDelta0.comp₁ (concat_locallyDelta0.comp₂
      (LocallyDelta0Function.var (0 : Fin 1)) (LocallyDelta0Function.const z)))
      (LocallyDelta0Function.add_one (len_locallyDelta0.comp₁
        (LocallyDelta0Function.var (0 : Fin 1))))
  apply adjoin_induction hP
  · simp
  · intro x v ih
    simp [ih]

lemma concat_nth_lt (v z : V) {i} (hi : i < len v) : (concat v z).[i] = v.[i] := by
  have hR : LocallyDelta0 fun w : Fin 2 → V ↦
      w 0 < len (w 1) → (concat (w 1) z).[w 0] = (w 1).[w 0] :=
    (LocallyDelta0.lt (LocallyDelta0Function.var (0 : Fin 2))
      (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2)))).imp
      (LocallyDelta0.eq (nth_locallyDelta0.comp₂ (concat_locallyDelta0.comp₂
        (LocallyDelta0Function.var 1) (LocallyDelta0Function.const z))
          (LocallyDelta0Function.var 0))
        (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0)))
  have hP : LocallyDelta0Pred fun u ↦ ∀ j ≤ i, j < len u → (concat u z).[j] = u.[j] :=
    (LocallyDelta0.ball_le_function (LocallyDelta0Function.const i) hR).of_iff fun w ↦ by simp
  have : ∀ j ≤ i, j < len v → (concat v z).[j] = v.[j] := by
    apply adjoin_induction hP
    · intro j _ h
      simp at h
    · intro x v ih j hj hl
      rcases zero_or_succ j with (rfl | ⟨j, rfl⟩)
      · simp
      · simp [ih j (le_trans le_self_add hj) (by simpa using hl)]
  exact this i le_rfl hi

@[simp] lemma concat_nth_len (v z : V) : (concat v z).[len v] = z := by
  have hP : LocallyDelta0Pred fun u : V ↦ (concat u z).[len u] = z :=
    LocallyDelta0.eq (nth_locallyDelta0.comp₂ (concat_locallyDelta0.comp₂
      (LocallyDelta0Function.var (0 : Fin 1)) (LocallyDelta0Function.const z))
      (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1))))
      (LocallyDelta0Function.const z)
  apply adjoin_induction hP
  · simp
  · intro x v ih
    simp [ih]

lemma concat_nth_len' (v z : V) {i} (hi : len v = i) : (concat v z).[i] = z := by
  rcases hi; simp

end concat

/-! ### Membership -/

section vecMembership

/-- `x ∈ᵥ v` states that `x` is an element of the list `v`. -/
def MemVec (x v : V) : Prop := ∃ i < len v, x = v.[i]

scoped infix:40 " ∈ᵥ " => MemVec

@[simp] lemma not_memVec_empty (x : V) : ¬x ∈ᵥ 0 := by rintro ⟨i, h, _⟩; simp at h

lemma nth_mem_memVec {i v : V} (h : i < len v) : v.[i] ∈ᵥ v := ⟨i, by simp [h]⟩

@[simp] lemma memVec_insert_fst {x v : V} : x ∈ᵥ x ∷ v := ⟨0, by simp⟩

@[simp] lemma memVec_adjoin_iff {x y v : V} : x ∈ᵥ y ∷ v ↔ x = y ∨ x ∈ᵥ v := by
  constructor
  · rintro ⟨i, h, rfl⟩
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · right; simpa using nth_mem_memVec (by simpa using h)
  · rintro (rfl | hx)
    · simp
    · rcases hx with ⟨i, hi, rfl⟩
      exact ⟨i + 1, by simp [hi]⟩

lemma le_of_memVec {x v : V} (h : x ∈ᵥ v) : x ≤ v := by
  rcases h with ⟨i, _, rfl⟩; simp

instance memVec_defined : 𝚫ᴬ₁-Relation (MemVec : V → V → Prop) via memVecDef :=
  ⟨by intro v; simp [memVecDef], by intro v; simp [memVecDef, MemVec]⟩

instance memVec_definable : 𝚫ᴬ₁-Relation (MemVec : V → V → Prop) := memVec_defined.to_definable

instance memVec_definable' (Γ m) : Γᴬ_[m + 1]-Relation (MemVec : V → V → Prop) :=
  memVec_definable.of_deltaOne

end vecMembership

/-! ### Subset -/

section vecSubset

/-- `v ⊆ᵥ w` states that every element of the list `v` is an element of the list `w`. -/
def SubsetVec (v w : V) : Prop := ∀ x, x ∈ᵥ v → x ∈ᵥ w

scoped infix:30 " ⊆ᵥ " => SubsetVec

@[simp, refl] lemma SubsetVec.refl (v : V) : v ⊆ᵥ v := fun _ hx ↦ hx

@[simp] lemma subsetVec_insert_tail (x v : V) : v ⊆ᵥ x ∷ v := by intro y hy; simp [hy]

set_option linter.flexible false in
instance subsetVec_defined : 𝚫ᴬ₁-Relation (SubsetVec : V → V → Prop) via subsetVecDef :=
  ⟨by intro v; simp [subsetVecDef, Bounding.HierarchySymbol.Semiformula.val_sigma,
    memVec_defined.proper.iff'],
   by intro v
      simp [subsetVecDef, Bounding.HierarchySymbol.Semiformula.val_sigma,
        memVec_defined.proper.iff']
      constructor
      · intro h x hx; exact h x (le_of_memVec hx) hx
      · intro h x _; exact h x⟩

instance subsetVec_definable : 𝚫ᴬ₁-Relation (SubsetVec : V → V → Prop) :=
  subsetVec_defined.to_definable

instance subsetVec_definable' (Γ m) : Γᴬ_[m + 1]-Relation (SubsetVec : V → V → Prop) :=
  subsetVec_definable.of_deltaOne

end vecSubset

/-! ### Repetition -/

section repeatVec

noncomputable def repeatVec.adjointruction :
    PR.Construction V Arithmetic.repeatVec.blueprint where
  zero := fun _ ↦ 0
  succ := fun p _ ih ↦ p 0 ∷ ih
  zero_defined := .mk fun v ↦ by simp [Arithmetic.repeatVec.blueprint]
  succ_defined := .mk fun v ↦ by simp [Arithmetic.repeatVec.blueprint]
  zero_locallyDelta0 := LocallyDelta0Function.const 0
  succ_locallyDelta0 :=
    LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 2) (LocallyDelta0Function.var 0)
  bound p i := Exp.exp (Exp.exp (i + i + p 0 + 3)) + 1
  zero_lt_bound _ := by simp
  succ_lt_bound p i z h := by
    have hn : (1 : V) ≤ i + i + p 0 + 3 := le_trans (by norm_num) le_add_self
    have e : i + 1 + (i + 1) + p 0 + 3 = i + i + p 0 + 3 + 2 := by grind
    have := adjoin_le_exp_exp hn (le_exp_exp (le_trans le_add_self le_self_add))
      (lt_succ_iff_le.mp h)
    rw [← e] at this
    exact lt_succ_iff_le.mpr this
  bound_monotone _ _ _ h :=
    add_le_add (exp_monotone_le.mpr (exp_monotone_le.mpr
      (add_le_add (add_le_add (add_le_add h h) le_rfl) le_rfl))) le_rfl
  bound_locallyDelta0 := LocallyDelta0Function.add_one <|
    LocallyDelta0Function.exp.comp₁ <| LocallyDelta0Function.exp.comp₁ <|
      LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.add.comp₂
        (LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.var 0)
          (LocallyDelta0Function.var 0)) (LocallyDelta0Function.var 1))
        (LocallyDelta0Function.const 3)

/-- `repeatVec x k = x ∷ x ∷ x ∷ ... k times ... ∷ 0` -/
noncomputable def repeatVec (x k : V) : V := repeatVec.adjointruction.result ![x] k

@[simp] lemma repeatVec_zero (x : V) : repeatVec x 0 = 0 := by
  simp [repeatVec, repeatVec.adjointruction]

@[simp] lemma repeatVec_succ (x k : V) : repeatVec x (k + 1) = x ∷ repeatVec x k := by
  simp [repeatVec, repeatVec.adjointruction]

instance repeatVec_defined : 𝚺ᴬ₁-Function₂ (repeatVec : V → V → V) via repeatVecDef := .mk
  fun v ↦ by simp [repeatVec.adjointruction.result_defined_iff, repeatVecDef]; rfl

instance repeatVec_definable : 𝚺ᴬ₁-Function₂ (repeatVec : V → V → V) :=
  repeatVec_defined.to_definable

instance repeatVec_definable' (Γ m) : Γᴬ_[m + 1]-Function₂ (repeatVec : V → V → V) :=
  repeatVec_definable.of_sigmaOne

lemma repeatVec_locallyDelta0 : LocallyDelta0Function₂ (repeatVec : V → V → V) := by
  have := (repeatVec.adjointruction (V := V)).result_locallyDelta0.retraction
    (![1, 0] : Fin 2 → Fin 2)
  convert this using 3
  simp [repeatVec]
  rfl

@[simp] lemma len_repeatVec (x k : V) : len (repeatVec x k) = k := by
  have hP : LocallyDelta0Pred fun k : V ↦ len (repeatVec x k) = k :=
    LocallyDelta0.eq (len_locallyDelta0.comp₁ (repeatVec_locallyDelta0.comp₂
      (LocallyDelta0Function.const x) (LocallyDelta0Function.var (0 : Fin 1))))
      (LocallyDelta0Function.var 0)
  apply LocallyDelta0Pred.succ_induction hP
  · simp
  · intro k ih
    simp [ih]

@[simp] lemma le_repaetVec (x k : V) : k ≤ repeatVec x k := by
  simpa using len_le (repeatVec x k)

lemma nth_repeatVec (x k : V) {i} (h : i < k) : (repeatVec x k).[i] = x := by
  have hR : LocallyDelta0 fun w : Fin 2 → V ↦ w 0 < w 1 → (repeatVec x (w 1)).[w 0] = x :=
    (LocallyDelta0.lt (LocallyDelta0Function.var (0 : Fin 2)) (LocallyDelta0Function.var 1)).imp
      (LocallyDelta0.eq (nth_locallyDelta0.comp₂ (repeatVec_locallyDelta0.comp₂
        (LocallyDelta0Function.const x) (LocallyDelta0Function.var 1))
          (LocallyDelta0Function.var 0)) (LocallyDelta0Function.const x))
  have hP : LocallyDelta0Pred fun k ↦ ∀ j ≤ i, j < k → (repeatVec x k).[j] = x :=
    (LocallyDelta0.ball_le_function (LocallyDelta0Function.const i) hR).of_iff fun w ↦ by simp
  have : ∀ j ≤ i, j < k → (repeatVec x k).[j] = x := by
    apply LocallyDelta0Pred.succ_induction hP
    · intro j _ h
      simp at h
    · intro k ih j hj hl
      rcases zero_or_succ j with (rfl | ⟨j, rfl⟩)
      · simp
      · simpa using ih j (le_trans le_self_add hj) (by simpa using hl)
  exact this i le_rfl h

lemma len_repeatVec_of_nth_le {v m : V} (H : ∀ i < len v, v.[i] ≤ m) :
    v ≤ repeatVec m (len v) :=
  le_of_nth_le_nth (by simp) (fun i hi ↦ by simp [nth_repeatVec m (len v) hi, H i hi])

end repeatVec

/-! ### Conversion to a set -/

namespace VecToSet

noncomputable def adjointruction : VecRec.Construction V Arithmetic.VecToSet.blueprint where
  nil _ := ∅
  adjoin _ x _ ih := insert x ih
  nil_defined := .mk fun v ↦ by simp [Arithmetic.VecToSet.blueprint, emptyset_def]
  adjoin_defined := .mk fun v ↦ by simp [Arithmetic.VecToSet.blueprint]
  nil_locallyDelta0 := LocallyDelta0Function.const ∅
  adjoin_locallyDelta0 :=
    LocallyDelta0Function.insert.comp₂ (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 2)
  bound _ xs := Exp.exp (xs + 1)
  nil_le_bound _ := zero_le
  adjoin_le_bound _ x xs ih h := by
    have h₁ : Exp.exp (xs + 1) ≤ Exp.exp (x ∷ xs) :=
      exp_monotone_le.mpr (succ_le_iff_lt.mpr (lt_adjoin' x xs))
    have h₂ : Exp.exp x ≤ Exp.exp (x ∷ xs) := exp_monotone_le.mpr (lt_adjoin x xs).le
    calc insert x ih ≤ Exp.exp (xs + 1) + Exp.exp x := insert_le_of_le_of_le le_rfl h
      _ ≤ Exp.exp (x ∷ xs) + Exp.exp (x ∷ xs) := add_le_add h₁ h₂
      _ = Exp.exp (x ∷ xs + 1) := by rw [exp_succ, two_mul]
  bound_monotone _ _ _ h := exp_monotone_le.mpr (add_le_add h le_rfl)
  bound_locallyDelta0 := LocallyDelta0Function.exp.comp₁ (LocallyDelta0Function.add_one
    (LocallyDelta0Function.var 0))

end VecToSet

section vecToSet

/-- The set of the elements of the list `v`. -/
noncomputable def vecToSet (v : V) : V := VecToSet.adjointruction.result ![] v

@[simp] lemma vecToSet_nil : vecToSet (0 : V) = ∅ := by simp [vecToSet, VecToSet.adjointruction]

@[simp] lemma vecToSet_adjoin (x v : V) :
    vecToSet (x ∷ v) = insert x (vecToSet v) := by simp [vecToSet, VecToSet.adjointruction]

instance vecToSet_defined : 𝚺ᴬ₁-Function₁ (vecToSet : V → V) via vecToSetDef :=
  VecToSet.adjointruction.result_defined

instance vecToSet_definable : 𝚺ᴬ₁-Function₁ (vecToSet : V → V) := vecToSet_defined.to_definable

instance vecToSet_definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (vecToSet : V → V) :=
  vecToSet_definable.of_sigmaOne

lemma vecToSet_locallyDelta0 : LocallyDelta0Function₁ (vecToSet : V → V) := by
  convert VecToSet.adjointruction.result_locallyDelta0 (V := V) using 3
  simp [vecToSet, Matrix.empty_eq]

lemma mem_vecToSet_iff {v x : V} : x ∈ vecToSet v ↔ ∃ i < len v, x = v.[i] := by
  have hex : LocallyDelta0 fun w : Fin 1 → V ↦ ∃ i < len (w 0), x = (w 0).[i] :=
    (LocallyDelta0.bexs_lt_function (len_locallyDelta0.comp₁
      (LocallyDelta0Function.var (0 : Fin 1)))
      (LocallyDelta0.eq (LocallyDelta0Function.const x) (nth_locallyDelta0.comp₂
        (LocallyDelta0Function.var (1 : Fin 2)) (LocallyDelta0Function.var 0)))).of_iff
          fun w ↦ by simp
  have hP : LocallyDelta0Pred fun u : V ↦ x ∈ vecToSet u ↔ ∃ i < len u, x = u.[i] :=
    ((LocallyDelta0.mem (LocallyDelta0Function.const x) (vecToSet_locallyDelta0.comp₁
      (LocallyDelta0Function.var (0 : Fin 1)))).iff hex).of_iff fun w ↦ by simp
  apply adjoin_induction hP
  · simp
  · intro y v ih
    simp only [vecToSet_adjoin, mem_bitInsert_iff, ih, len_adjoin]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by simp⟩
      · exact ⟨i + 1, by simp [hi]⟩
    · rintro ⟨i, hi, rfl⟩
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp
      · right; exact ⟨i, by simpa using hi, by simp⟩

@[simp] lemma nth_mem_vecToSet {v i : V} (h : i < len v) : v.[i] ∈ vecToSet v :=
  mem_vecToSet_iff.mpr ⟨i, h, rfl⟩

end vecToSet

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
