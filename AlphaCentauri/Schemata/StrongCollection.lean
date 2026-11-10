module

public import Foundation.FirstOrder.Arithmetic.HFS.Seq
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv

/-! # Pieces and strong collection in `𝗜𝚺 (n + 1)`

In a model of $\mathsf{I}\Sigma_{n + 1}$ every $\Sigma_{n + 1}$ predicate is piecewise coded, and
the witnesses of a $\Sigma_{n + 1}$ relation are bounded on an interval even at the arguments
where it has none.

- [HP98, Definition I.2.6, Lemma I.2.13(a), Lemma I.2.27]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)
open _root_.FFL.Entailment

section StrongCollection

variable {V : Type*} [ORingStructure V] {n : ℕ} [V↓[ℒₒᵣ] ⊧* 𝗜𝚺(n + 1)]

/-- A $\Sigma_{n + 1}$ predicate has a piece of every length `z`: a sequence of length `z`
whose `i`-th entry is `1` exactly when the predicate holds at `i`.
- [HP98, Definition I.2.6, Lemma I.2.13(a)] -/
theorem exists_piece [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {P : V → Prop} (hP : 𝚺ᴬ_[n + 1].DefinablePred P) (z : V) :
    ∃ q, Seq q ∧ lh q = z ∧ ∀ i < z, (znth q i = 1 ↔ P i) := by
  have : Fact (1 ≤ n + 1) := ⟨by omega⟩
  obtain ⟨s, -, hs⟩ := finset_comprehension hP z
  obtain ⟨q, hq, hlh, hmem⟩ := sigmaOne_skolem_seq
    (R := fun i x ↦ (i ∈ s ∧ x = 1) ∨ (i ∉ s ∧ x = 0)) (by definability) (l := z)
    (by intro i _; by_cases h : i ∈ s <;> simp [h])
  have : ∀ i < z, (znth q i = 1 ↔ P i) := by
    intro i hi
    obtain ⟨x, hx⟩ := hq.exists (hlh ▸ hi)
    rw [hq.znth_eq_of_mem hx, ← hs i hi]
    rcases hmem i x hx with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp [h]
  use q

/-- Strong $\Sigma_{n + 1}$ collection: below every `u`, the witnesses of a $\Sigma_{n + 1}$
relation are bounded at all arguments that have one.
- [HP98, Lemma I.2.27] -/
theorem strong_collection {R : V → V → Prop} (hR : 𝚺ᴬ_[n + 1].DefinableRel R) (u : V) :
    ∃ v, ∀ x < u, (∃ y, R x y) → ∃ y < v, R x y := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ n + 1 by omega)
  obtain ⟨q, -, -, hq⟩ := exists_piece (n := n) (P := fun x ↦ ∃ y, R x y) (by definability) u
  obtain ⟨v, hv⟩ := IBroadSigma.collection (R := fun x y ↦ znth q x = 1 → R x y)
    (by definability) u (by intro x hx; by_cases h : znth q x = 1 <;> simp_all)
  use v
  intro x hx h
  obtain ⟨y, hy, hRy⟩ := hv x hx
  use y
  and_intros
  · exact hy
  · exact hRy <| (hq x hx).mpr h

end StrongCollection

end FFL.FirstOrder.Arithmetic
