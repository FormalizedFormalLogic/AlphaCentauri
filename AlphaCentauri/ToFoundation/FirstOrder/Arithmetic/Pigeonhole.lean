module

public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Arithmetic.Definability
public import Foundation.FirstOrder.Arithmetic.Exponential.Bit
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.BlockSequence
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Exponential
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Power
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Injection

/-!
# The pigeonhole principle in models of $\mathsf{I}\Sigma_m$

In a model of $\mathsf{I}\Sigma_m$, $m \ge 1$, no $\Sigma_m$-definable relation is an injection of
$a + 1$ into $a$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

section PigeonholeIOpen

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] {m : ℕ} [Fact (1 ≤ m)] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺m]

section

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma exists_set_of_definableRel {R : V → V → Prop} (hR : 𝚺ᴬ_[m].DefinableRel R) (a b : V) :
    ∃ w : V, ∀ x < a, ∀ y < b, ⟪x, y⟫ ∈ w ↔ R x y := by
  have hp : 𝚺ᴬ_[m].DefinableRel₃ fun z x y : V ↦ z = ⟪x, y⟫ :=
    (show 𝚺ᴬ₀.DefinableRel₃ fun z x y : V ↦ z = ⟪x, y⟫ by definability).of_zero
  have : 𝚺ᴬ_[m]-Predicate fun z : V ↦ ∃ x < a, ∃ y < b, z = ⟪x, y⟫ ∧ R x y := by
    apply Bounding.HierarchySymbol.Definable.arithmetic_bexs_blt (by definability)
    apply Bounding.HierarchySymbol.Definable.arithmetic_bexs_blt (by definability)
    apply Bounding.HierarchySymbol.Definable.and
    · simpa using Bounding.HierarchySymbol.Definable.arithmetic_bounded_comp₃
        (R := fun z x y : V ↦ z = ⟪x, y⟫)
        (by definability) (by definability) (by definability)
    · simpa using Bounding.HierarchySymbol.Definable.arithmetic_bounded_comp₂ (R := R)
        (by definability) (by definability)
  obtain ⟨w, hw, H⟩ := finset_comprehension this ⟪a, b⟫
  use w
  intro x hx y hy
  rw [H _ (pair_lt_pair hx hy)]
  simp [pair_ext_iff]
  grind

private def IsInjection (a w : V) : Prop :=
  (∀ x < a + 1, ∃ y < a, ⟪x, y⟫ ∈ w) ∧
  ∀ x < a + 1, ∀ x' < a + 1, ∀ y < a, ⟪x, y⟫ ∈ w → ⟪x', y⟫ ∈ w → x = x'

private lemma exists_isInjection_of_succ {a w : V} (h : IsInjection (a + 1) w) :
    ∃ w', IsInjection a w' := by
  have : Fact (1 ≤ 1) := ⟨le_rfl⟩
  obtain ⟨w', hw'⟩ := exists_set_of_definableRel (m := 1)
    (R := fun x y ↦ ⟪x, y⟫ ∈ w ∨ (⟪x, a⟫ ∈ w ∧ ⟪a + 1, y⟫ ∈ w)) (by definability) (a + 1) a
  obtain ⟨hT, hI⟩ := h
  use w'
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hT x (by simp [lt_succ_iff_le, hx.le])
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hy) with hy | hya
    · use y
      and_intros
      · exact hy
      · exact (hw' x hx y hy).2 (Or.inl hxy)
    · rw [hya] at hxy
      obtain ⟨y', hy', hxy'⟩ := hT (a + 1) (by simp)
      have hne : y' ≠ a := by
        intro hyy
        rw [hyy] at hxy'
        have := hI x (by simp [lt_succ_iff_le, hx.le]) (a + 1) (by simp) a (by simp) hxy hxy'
        exact this.not_lt hx
      have hy'' : y' < a := lt_of_le_of_ne (lt_succ_iff_le.mp hy') hne
      use y'
      and_intros
      · exact hy''
      · exact (hw' x hx y' hy'').2 (Or.inr ⟨hxy, hxy'⟩)
  · intro x hx x' hx' y hy h h'
    rw [hw' x hx y hy] at h
    rw [hw' x' hx' y hy] at h'
    have hx₁ : x < a + 1 + 1 := by simp [lt_succ_iff_le, hx.le]
    have hx₁' : x' < a + 1 + 1 := by simp [lt_succ_iff_le, hx'.le]
    have hy₁ : y < a + 1 := by simp [lt_succ_iff_le, hy.le]
    have ha₁ : a < a + 1 := by simp
    have ha₂ : a + 1 < a + 1 + 1 := by simp
    rcases h with h | ⟨h₁, h₂⟩ <;> rcases h' with h' | ⟨h₁', h₂'⟩
    · exact hI x hx₁ x' hx₁' y hy₁ h h'
    · exact absurd (hI x hx₁ (a + 1) ha₂ y hy₁ h h₂') hx.ne
    · exact absurd (hI x' hx₁' (a + 1) ha₂ y hy₁ h' h₂) hx'.ne
    · exact hI x hx₁ x' hx₁' a ha₁ h₁ h₁'

private lemma not_isInjection (a w : V) : ¬IsInjection a w := by
  suffices ∀ a : V, ∀ w, ¬IsInjection a w from this a w
  intro a
  induction a using ISigma1.pi1_succ_induction
  · unfold IsInjection
    definability
  case zero =>
    intro w h
    obtain ⟨y, hy, _⟩ := h.1 0 (by simp)
    simp at hy
  case succ a ih =>
    intro w h
    obtain ⟨w', h'⟩ := exists_isInjection_of_succ h
    exact ih w' h'

end

/-- A $\Sigma_m$-definable relation giving every `x < a + 1` some value below `a` gives two of
them a common value.
- [HP98, Theorem I.1.41] -/
theorem pigeonhole {R : V → V → Prop} (hR : 𝚺ᴬ_[m].DefinableRel R) (a : V)
    (total : ∀ x < a + 1, ∃ y < a, R x y) :
    ∃ x < a + 1, ∃ x' < a + 1, ∃ y < a, x ≠ x' ∧ R x y ∧ R x' y := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
  by_contra hne
  obtain ⟨w, hw⟩ := exists_set_of_definableRel hR (a + 1) a
  apply not_isInjection a w
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := total x hx
    use y
    and_intros
    · exact hy
    · exact (hw x hx y hy).2 hxy
  · intro x hx x' hx' y hy h h'
    by_contra hxx
    apply hne
    use x
    and_intros
    · exact hx
    · use x'
      and_intros
      · exact hx'
      · use y
        and_intros
        · exact hy
        · exact hxx
        · exact (hw x hx y hy).1 h
        · exact (hw x' hx' y hy).1 h'

end PigeonholeIOpen

end FFL.FirstOrder.Arithmetic
