module

public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Arithmetic.Definability.Definable

/-!
# An injective enumeration from a failure of collection
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Bounding FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {m : ℕ}

lemma definable_exists_lt_theta {θ : ArithmeticSemisentence (m + 2)}
    (hθ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 θ) (e : Fin m → V) :
    𝚺ᴬ₀.DefinableRel fun s x : V ↦ ∃ u < s, V ⊧/(u :> x :> e) θ := by
  let w : Fin (m + 2) → ArithmeticSemiterm V 3 := #0 :> #2 :> fun i ↦ &(e i)
  have h₁ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 (Semiformula.emb θ ⇜ w) :=
    (hθ.rew Rew.emb).rew (Rew.subst w)
  have h₂ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0
      ((Semiformula.emb θ ⇜ w).bexsLT (#0 : ArithmeticSemiterm V 2)) := by
    simpa using h₁
  refine (FFL.FirstOrder.Bounding.definableRel_of_hierarchy h₂ id).of_iff fun v ↦ ?_
  have h : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
  have hw : ∀ x : V, Semiterm.val (x :> v) id ∘ w = x :> v 1 :> e := by
    intro x
    funext j
    induction j using Fin.cases with
    | zero => simp [w]
    | succ j =>
      induction j using Fin.cases with
      | zero => simp [w]
      | succ i => simp [w]
  simp [h, Semiformula.Evalb, hw]

lemma definablePred_exists_lt_theta {θ : ArithmeticSemisentence (m + 2)}
    (hθ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 θ) (e : Fin m → V) (x : V) :
    𝚺ᴬ₀.DefinablePred fun s : V ↦ ∃ u < s, V ⊧/(u :> x :> e) θ := by
  have := FFL.FirstOrder.Bounding.HierarchySymbol.Definable.retractiont
    (definable_exists_lt_theta hθ e) (![#0, &x] : Fin 2 → ArithmeticSemiterm V 1)
  exact this.of_iff fun v ↦ by simp

lemma definableRel_graph [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {θ : ArithmeticSemisentence (m + 2)}
    (hθ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 θ) (e : Fin m → V) (a : V) :
    𝚺ᴬ₀.DefinableRel fun x y : V ↦ x < a ∧
      ∃ z, z < y + 1 ∧ y = ⟪x, z⟫ ∧ (∃ u < z, V ⊧/(u :> x :> e) θ) ∧
        ∀ z' < z, ¬∃ u < z', V ⊧/(u :> x :> e) θ := by
  have hσ := definable_exists_lt_theta hθ e
  have hpair : 𝚺ᴬ₀.DefinableRel₃ fun x z y : V ↦ y = ⟪x, z⟫ := by definability
  have hlt : 𝚺ᴬ₀.DefinableRel fun x _ : V ↦ x < a := by definability
  have hP₁ : 𝚺ᴬ₀.Definable (k := 3) fun w : Fin 3 → V ↦ w 2 = ⟪w 1, w 0⟫ :=
    (FFL.FirstOrder.Bounding.HierarchySymbol.Definable.retraction hpair ![1, 0, 2]).of_iff
      (by intro w; simp)
  have hP₂ : 𝚺ᴬ₀.Definable (k := 3) fun w : Fin 3 → V ↦
      ∃ u < w 0, V ⊧/(u :> w 1 :> e) θ :=
    (FFL.FirstOrder.Bounding.HierarchySymbol.Definable.retraction hσ ![0, 1]).of_iff
      (by intro w; simp)
  have hP₃ : 𝚺ᴬ₀.Definable (k := 3) fun w : Fin 3 → V ↦
      ∀ z' < w 0, ¬∃ u < z', V ⊧/(u :> w 1 :> e) θ :=
    FFL.FirstOrder.Bounding.HierarchySymbol.Definable.ball (R := Semiformula.Operator.LT.lt)
      (P := fun (v : Fin 3 → V) (z' : V) ↦ ¬∃ u < z', V ⊧/(u :> v 1 :> e) θ) (by rfl)
      ((FFL.FirstOrder.Bounding.HierarchySymbol.Definable.notSigma
        (FFL.FirstOrder.Bounding.HierarchySymbol.Definable.retraction hσ ![0, 2])).of_zero
          (ℌ := 𝚺ᴬ₀) |>.of_iff (by intro w; simp))
      (#0)
  have hB := FFL.FirstOrder.Bounding.HierarchySymbol.Definable.bexs
    (R := Semiformula.Operator.LT.lt) (by rfl)
    (P := fun (v : Fin 2 → V) (z : V) ↦ v 1 = ⟪v 0, z⟫ ∧ (∃ u < z, V ⊧/(u :> v 0 :> e) θ) ∧
      ∀ z' < z, ¬∃ u < z', V ⊧/(u :> v 0 :> e) θ)
    ((hP₁.and (hP₂.and hP₃)).of_iff (by intro w; simp))
    ‘#1 + 1’
  exact (hlt.and hB).of_iff (by intro v; simp)

end FFL.FirstOrder.Arithmetic
