module

public import Mathlib.Combinatorics.Pigeonhole

/-!
# Ramsey's theorem for finite sets

For all `k`, `c` and `q` there is `N` such that every colouring with `c` colours of the
`k`-element subsets of a finite set with at least `N` elements has a homogeneous set of size `q`:
a subset all of whose `k`-element subsets have the same colour.
-/

@[expose] public section

open Finset

universe u

namespace Finset

variable {k c : ℕ}

/-- If every `c`-colouring of `k`-element sets has arbitrarily large homogeneous sets, then every
`c`-colouring of `(k + 1)`-element sets has arbitrarily large sets on which the colour of a set
is the colour of one of its elements. -/
lemma exists_preHomogeneous
    (ih : ∀ q, ∃ N, ∀ {α : Type u} [DecidableEq α] (X : Finset α), N ≤ #X →
      ∀ f : Finset α → Fin c, ∃ H ⊆ X, q ≤ #H ∧ ∃ i, ∀ s ⊆ H, #s = k → f s = i)
    (m : ℕ) :
    ∃ N, ∀ {α : Type u} [DecidableEq α] (X : Finset α), N ≤ #X →
      ∀ f : Finset α → Fin c, ∃ P ⊆ X, m ≤ #P ∧
        ∃ g : α → Fin c, ∀ s ⊆ P, #s = k + 1 → ∃ a ∈ s, f s = g a := by
  induction m with
  | zero =>
    use 0
    intro α _ X _ f
    use ∅
    and_intros
    · exact empty_subset X
    · exact Nat.zero_le _
    use fun _ ↦ f ∅
    intro s hs hcard
    simp [subset_empty.mp hs] at hcard
  | succ m ihm =>
    obtain ⟨M, hM⟩ := ihm
    obtain ⟨R, hR⟩ := ih M
    use R + 1
    intro α _ X hX f
    obtain ⟨a, ha⟩ : X.Nonempty := card_pos.mp <| by omega
    obtain ⟨Y, hYX, hMY, i, hY⟩ :=
      hR (X.erase a) (by rw [card_erase_of_mem ha]; omega) fun t ↦ f (insert a t)
    obtain ⟨P, hPY, hmP, g, hP⟩ := hM Y hMY f
    have haP : a ∉ P := fun h ↦ by simpa using hYX <| hPY h
    use insert a P
    and_intros
    · exact insert_subset ha <| (hPY.trans hYX).trans <| erase_subset a X
    · rw [card_insert_of_notMem haP]
      omega
    use Function.update g a i
    intro s hs hcard
    by_cases has : a ∈ s
    · use a, has
      rw [Function.update_self, ← insert_erase has]
      apply hY
      · intro x hx
        obtain ⟨hxa, hxs⟩ := mem_erase.mp hx
        exact hPY <| (mem_insert.mp <| hs hxs).resolve_left hxa
      · rw [card_erase_of_mem has, hcard, Nat.add_sub_cancel]
    · obtain ⟨b, hbs, hb⟩ := hP s ((subset_insert_iff_of_notMem has).mp hs) hcard
      use b, hbs
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hbs has), hb]

/-- **Ramsey's theorem** for finite sets: for all `k`, `c` and `q` there is `N` such that every
colouring with `c` colours of the `k`-element subsets of a finite set with at least `N` elements
has a homogeneous set of size at least `q`.

- [HP98, Theorem II.1.10] -/
theorem exists_ramsey (k c q : ℕ) :
    ∃ N, ∀ {α : Type u} [DecidableEq α] (X : Finset α), N ≤ #X →
      ∀ f : Finset α → Fin c, ∃ H ⊆ X, q ≤ #H ∧ ∃ i, ∀ s ⊆ H, #s = k → f s = i := by
  induction k generalizing q with
  | zero =>
    use q
    intro α _ X hX f
    use X, Subset.rfl, hX, f ∅
    intro s _ hs
    rw [card_eq_zero.mp hs]
  | succ k ih =>
    obtain ⟨N, hN⟩ := exists_preHomogeneous ih (c * q)
    use N
    intro α _ X hX f
    obtain ⟨P, hPX, hcP, g, hP⟩ := hN X hX f
    have : Nonempty (Fin c) := ⟨f ∅⟩
    obtain ⟨i, -, hi⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
      (fun a _ ↦ mem_univ (g a)) univ_nonempty (by simpa using hcP)
    use {a ∈ P | g a = i}
    and_intros
    · exact (filter_subset _ P).trans hPX
    · exact hi
    use i
    intro s hs hcard
    obtain ⟨a, has, hfa⟩ := hP s (hs.trans <| filter_subset _ P) hcard
    rw [hfa]
    exact (mem_filter.mp <| hs has).2

end Finset

/-- **Ramsey's theorem** for `Fin N`: for all `k`, `c` and `q` there is `N` such that every
colouring with `c` colours of the `k`-element subsets of `Fin N` has a homogeneous set of size at
least `q`.

- [HP98, Theorem II.1.10] -/
theorem exists_ramsey (k c q : ℕ) :
    ∃ N, ∀ f : Finset (Fin N) → Fin c, ∃ H : Finset (Fin N), q ≤ H.card ∧
      ∃ i, ∀ s ⊆ H, s.card = k → f s = i := by
  obtain ⟨N, hN⟩ := Finset.exists_ramsey.{0} k c q
  use N
  intro f
  obtain ⟨H, -, hH⟩ := hN univ (by simp) f
  use H
