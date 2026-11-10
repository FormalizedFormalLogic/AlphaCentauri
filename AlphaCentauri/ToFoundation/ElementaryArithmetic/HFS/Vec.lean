module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.HFS.CourseOfValues
public import AlphaCentauri.ToFoundation.ElementaryArithmetic.HFS.Fixpoint
public import Foundation.FirstOrder.Arithmetic.HFS.Vec

/-!
# Lists in models of $\mathsf{EA}$

The file `Foundation/FirstOrder/Arithmetic/HFS/Vec.lean` on lists coded by iterated pairing in
models of $\mathsf{I}\Sigma_1$, ported to models of $\mathsf{EA}$: `x ∷ v`, the `i`-th element
`v.[i]`, and induction on lists for locally $\Delta_0$ predicates. The formulas `adjoinDef`,
`mkVec₁Def`, `mkVec₂Def` and `nthDef` define the $\mathsf{EA}$ versions.

- [HP98, §V.3]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

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
      (LocallyDelta0Function.var (V := V) (2 : Fin 3)) (LocallyDelta0Function.var (V := V) (0 : Fin 3))
    exact this.of_iff fun w ↦ ⟨by rintro h; simp [h, nth_graph], by
      intro h; exact (nth_eq_of_graph (by simpa using h)).symm⟩
  bounded X := by
    use X
    intro w hw
    exact le_trans (nth_le _ _) (hw 0)

lemma adjoin_cases (x : V) : x = 0 ∨ ∃ y v, x = y ∷ v := by
  rcases zero_or_succ x with (rfl | ⟨z, rfl⟩)
  · simp
  · right; exact ⟨π₁ z, π₂ z, by simp [adjoin]⟩

@[elab_as_elim]
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

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
