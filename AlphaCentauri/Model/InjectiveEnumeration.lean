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

variable {V : Type*} [ORingStructure V]

lemma definable_exists_lt {Q : V → V → Prop} (hQ : 𝚺ᴬ₀.DefinableRel Q) :
    𝚺ᴬ₀.DefinableRel fun s x : V ↦ ∃ u < s, Q u x := by
  have h : 𝚺ᴬ₀.Definable (k := 3) fun w : Fin 3 → V ↦ Q (w 0) (w 2) :=
    (FFL.FirstOrder.Bounding.HierarchySymbol.Definable.retraction hQ ![0, 2]).of_iff
      (by intro w; simp)
  have hB := FFL.FirstOrder.Bounding.HierarchySymbol.Definable.bexs
    (R := Semiformula.Operator.LT.lt) (by rfl)
    (P := fun (v : Fin 2 → V) (u : V) ↦ Q u (v 1))
    (h.of_iff (by intro w; simp)) (#0 : ArithmeticSemiterm V 2)
  exact hB.of_iff (by intro v; simp)

lemma definablePred_exists_lt {Q : V → V → Prop} (hQ : 𝚺ᴬ₀.DefinableRel Q) (x : V) :
    𝚺ᴬ₀.DefinablePred fun s : V ↦ ∃ u < s, Q u x := by
  have := FFL.FirstOrder.Bounding.HierarchySymbol.Definable.retractiont
    (definable_exists_lt hQ) (![#0, &x] : Fin 2 → ArithmeticSemiterm V 1)
  exact this.of_iff fun v ↦ by simp

lemma definableRel_graph [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {Q : V → V → Prop} (hQ : 𝚺ᴬ₀.DefinableRel Q)
    (a : V) :
    𝚺ᴬ₀.DefinableRel fun x y : V ↦ x < a ∧
      ∃ z, z < y + 1 ∧ y = ⟪x, z⟫ ∧ (∃ u < z, Q u x) ∧ ∀ z' < z, ¬∃ u < z', Q u x := by
  have hσ := definable_exists_lt hQ
  have hpair : 𝚺ᴬ₀.DefinableRel₃ fun x z y : V ↦ y = ⟪x, z⟫ := by definability
  have hlt : 𝚺ᴬ₀.DefinableRel fun x _ : V ↦ x < a := by definability
  have hP₁ : 𝚺ᴬ₀.Definable (k := 3) fun w : Fin 3 → V ↦ w 2 = ⟪w 1, w 0⟫ :=
    (FFL.FirstOrder.Bounding.HierarchySymbol.Definable.retraction hpair ![1, 0, 2]).of_iff
      (by intro w; simp)
  have hP₂ : 𝚺ᴬ₀.Definable (k := 3) fun w : Fin 3 → V ↦ ∃ u < w 0, Q u (w 1) :=
    (FFL.FirstOrder.Bounding.HierarchySymbol.Definable.retraction hσ ![0, 1]).of_iff
      (by intro w; simp)
  have hP₃ : 𝚺ᴬ₀.Definable (k := 3) fun w : Fin 3 → V ↦ ∀ z' < w 0, ¬∃ u < z', Q u (w 1) :=
    FFL.FirstOrder.Bounding.HierarchySymbol.Definable.ball (R := Semiformula.Operator.LT.lt)
      (P := fun (v : Fin 3 → V) (z' : V) ↦ ¬∃ u < z', Q u (v 1)) (by rfl)
      ((FFL.FirstOrder.Bounding.HierarchySymbol.Definable.notSigma
        (FFL.FirstOrder.Bounding.HierarchySymbol.Definable.retraction hσ ![0, 2])).of_zero
          (ℌ := 𝚺ᴬ₀) |>.of_iff (by intro w; simp))
      (#0)
  have hB := FFL.FirstOrder.Bounding.HierarchySymbol.Definable.bexs
    (R := Semiformula.Operator.LT.lt) (by rfl)
    (P := fun (v : Fin 2 → V) (z : V) ↦ v 1 = ⟪v 0, z⟫ ∧ (∃ u < z, Q u (v 0)) ∧
      ∀ z' < z, ¬∃ u < z', Q u (v 0))
    ((hP₁.and (hP₂.and hP₃)).of_iff (by intro w; simp))
    ‘#1 + 1’
  exact (hlt.and hB).of_iff (by intro v; simp)

/-- If a $\Delta_0$-definable relation `Q` has a witness `u` for every `x < a`, but no bound `w`
bounds the witnesses of all `x < a`, then there is an injective unbounded map `f` on `a` whose
graph restricted to `a` is $\Delta_0$-definable.
- [Sla04, Lemma 2.2] -/
theorem exists_injective_unbounded_of_not_collection [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    {Q : V → V → Prop} (hQ : 𝚺ᴬ₀.DefinableRel Q) (a : V)
    (hex : ∀ x < a, ∃ u, Q u x) (hnb : ∀ w, ∃ x < a, ∀ u ≤ w, ¬Q u x) :
    ∃ f : V → V, (∀ x < a, ∀ y < a, f x = f y → x = y) ∧ (∀ s, ∃ x < a, s < f x) ∧
      𝚺ᴬ₀-Relation fun x y ↦ x < a ∧ f x = y := by
  have hleast : ∀ x < a, ∃ s, (∃ u < s, Q u x) ∧ ∀ z < s, ¬∃ u < z, Q u x := by
    intro x hx
    obtain ⟨u, hu⟩ := hex x hx
    exact ISigma0.least_number (x := u + 1) (definablePred_exists_lt hQ x)
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
  · refine (definableRel_graph hQ a).of_iff fun v ↦ ?_
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
