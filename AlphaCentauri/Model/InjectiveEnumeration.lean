module

public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Arithmetic.Definability.Definable

/-!
# An injective enumeration from a failure of collection

A $\Delta_0$ formula with parameters which fails collection at a bound `a` yields an injective,
unbounded map on `a` whose graph is $\Delta_0$-definable.
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

/-- If a $\Delta_0$ formula `θ` with parameters `e` has a witness below every `x < a` but no
uniform bound on the witnesses below `a`, then there is an injective unbounded map `f` on `a`
whose graph restricted to `a` is $\Delta_0$-definable.
- [Sla04, Lemma 2.2] -/
theorem exists_injective_unbounded_of_not_collection [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    {θ : ArithmeticSemisentence (m + 2)} (hθ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 θ) (e : Fin m → V) (a : V)
    (hex : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ)
    (hnb : ∀ w, ∃ x < a, ∀ u ≤ w, ¬V ⊧/(u :> x :> e) θ) :
    ∃ f : V → V, (∀ x < a, ∀ y < a, f x = f y → x = y) ∧ (∀ s, ∃ x < a, s < f x) ∧
      𝚺ᴬ₀-Relation fun x y ↦ x < a ∧ f x = y := by
  have hleast : ∀ x < a, ∃ s, (∃ u < s, V ⊧/(u :> x :> e) θ) ∧
      ∀ z < s, ¬∃ u < z, V ⊧/(u :> x :> e) θ := by
    intro x hx
    obtain ⟨u, hu⟩ := hex x hx
    exact ISigma0.least_number (x := u + 1) (definablePred_exists_lt_theta hθ e x)
      ⟨u, by simp, hu⟩
  choose! s hs using hleast
  refine ⟨fun x ↦ ⟪x, s x⟫, ?_, ?_, ?_⟩
  · intro x _ y _ hxy
    exact (pair_ext_iff.mp hxy).1
  · intro t
    obtain ⟨x, hx, hnbx⟩ := hnb t
    obtain ⟨u, hu_lt, hu⟩ := (hs x hx).1
    refine ⟨x, hx, ?_⟩
    have htu : t < u := not_le.mp fun h ↦ hnbx u h hu
    exact lt_of_lt_of_le (lt_trans htu hu_lt) (le_pair_right x (s x))
  · refine (definableRel_graph hθ e a).of_iff fun v ↦ ?_
    change (v 0 < a ∧ ⟪v 0, s (v 0)⟫ = v 1) ↔ _
    constructor
    · rintro ⟨hx, hxy⟩
      refine ⟨hx, s (v 0), ?_, hxy.symm, (hs _ hx).1, (hs _ hx).2⟩
      rw [← hxy]
      exact lt_of_le_of_lt (le_pair_right _ _) (lt_add_one _)
    · rintro ⟨hx, z, -, hyz, hσz, hmin⟩
      refine ⟨hx, ?_⟩
      rcases lt_trichotomy z (s (v 0)) with h | h | h
      · exact absurd hσz ((hs _ hx).2 z h)
      · rw [hyz, h]
      · exact absurd (hs _ hx).1 (hmin _ h)

end FFL.FirstOrder.Arithmetic
