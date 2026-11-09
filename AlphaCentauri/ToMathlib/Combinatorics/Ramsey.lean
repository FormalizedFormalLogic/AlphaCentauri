module

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat

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
    · simp
    · simp
    use fun _ ↦ f ∅
    simp
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
    use X
    and_intros
    · exact Subset.rfl
    · exact hX
    use f ∅
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

variable {α : Type u} [DecidableEq α]

/-- For a finite set `L` and all `m` and `q` there is `N` such that for every colouring `G` with
`c` colours and every finite set `X` with at least `N` elements there is `B ⊆ X` with at least `q`
elements such that, for `W ⊆ B` with at most `m` elements and `S ⊆ L`, the colour of `W ∪ S`
depends only on `S` and the size of `W`. -/
lemma exists_forall_union_eq (L : Finset α) (m q : ℕ) :
    ∃ N, ∀ (G : Finset α → Fin c) (X : Finset α), N ≤ #X → ∃ B ⊆ X, q ≤ #B ∧
      ∀ W ⊆ B, ∀ W' ⊆ B, #W = #W' → #W ≤ m → ∀ S ⊆ L, G (W ∪ S) = G (W' ∪ S) := by
  induction m generalizing q with
  | zero =>
    use q
    intro G X hX
    use X
    and_intros
    · exact Subset.rfl
    · exact hX
    intro W _ W' _ h hW S _
    rw [card_eq_zero.mp (by omega : #W = 0), card_eq_zero.mp (by omega : #W' = 0)]
  | succ m ih =>
    obtain ⟨R, hR⟩ := exists_ramsey.{u} (m + 1) (Fintype.card (L.powerset → Fin c)) q
    obtain ⟨N, hN⟩ := ih R
    use N
    intro G X hX
    obtain ⟨B, hBX, hRB, hB⟩ := hN G X hX
    obtain ⟨B', hB'B, hqB', i, hB'⟩ :=
      hR B hRB fun W ↦ Fintype.equivFin _ fun S : L.powerset ↦ G (W ∪ S)
    use B'
    and_intros
    · exact hB'B.trans hBX
    · exact hqB'
    intro W hW W' hW' h hm S hS
    rcases (by omega : #W ≤ m ∨ #W = m + 1) with hm | hm
    · exact hB W (hW.trans hB'B) W' (hW'.trans hB'B) h hm S hS
    · have := (Fintype.equivFin _).injective <| (hB' W hW hm).trans (hB' W' hW' (h ▸ hm)).symm
      exact congrFun this ⟨S, mem_powerset.mpr hS⟩

/-- For every `e ≥ 1` there is `n` such that every colouring with two colours of the `e`-element
subsets of `{0, …, n - 1}` has a homogeneous set `Y ⊆ {0, …, n - 1}` with `e + 1` elements, one of
which is at most `e + 1`; in particular `#Y ≥ min Y`.

- [Qui80, p. 77]
- [Kay91, §14.3] -/
theorem exists_diagonal_paris_harrington {e : ℕ} (he : 1 ≤ e) :
    ∃ n, ∀ G : Finset ℕ → Fin 2, ∃ Y ⊆ range n, #Y = e + 1 ∧ (∃ x ∈ Y, x ≤ e + 1) ∧
      ∃ i, ∀ s ⊆ Y, #s = e → G s = i := by
  obtain ⟨N, hN⟩ := exists_forall_union_eq.{0} (c := 2) (range (e + 2)) e e
  use e + 2 + N
  intro G
  set L := range (e + 2)
  obtain ⟨B, hBX, heB, hB⟩ := hN G (Ico (e + 2) (e + 2 + N)) (by simp)
  have hBL : ∀ b ∈ B, b ∉ L := by
    intro b hb
    have := mem_Ico.mp <| hBX hb
    simp [L]
    omega
  have hLB : L ∪ B ⊆ range (e + 2 + N) := by
    apply union_subset (range_subset_range.mpr (by omega))
    intro b hb
    have := mem_Ico.mp <| hBX hb
    simp
    omega
  by_contra! hno
  have hcol : ∀ t ⊆ L ∪ B, ∀ t' ⊆ L ∪ B, #t = e → #t' = e → t ∩ L = t' ∩ L → G t = G t' := by
    intro t ht t' ht' hte ht'e h
    have := card_sdiff_add_card_inter t L
    have := card_sdiff_add_card_inter t' L
    rw [← sdiff_union_inter t L, ← sdiff_union_inter t' L, h]
    have hsub : ∀ u ⊆ L ∪ B, u \ L ⊆ B := by
      intro u hu x hx
      obtain ⟨hxu, hxL⟩ := mem_sdiff.mp hx
      exact (mem_union.mp (hu hxu)).resolve_left hxL
    apply hB _ (hsub t ht) _ (hsub t' ht')
    · rw [h] at *
      omega
    · omega
    · exact inter_subset_right
  have hFin : ∀ a b c : Fin 2, (a = c ↔ b = c) → a = b := by decide
  obtain ⟨t₀, ht₀B, ht₀⟩ := exists_subset_card_eq heB
  have hparity : ∀ j ≤ e, ∀ t ⊆ L ∪ B, #t = e → #(t ∩ L) = j → (G t = G t₀ ↔ Even j) := by
    intro j
    induction j with
    | zero =>
      intro _ t ht hte htL
      simp only [Even.zero, iff_true]
      apply hcol t ht t₀ (ht₀B.trans subset_union_right) hte ht₀
      rw [card_eq_zero.mp htL, eq_comm, ← disjoint_iff_inter_eq_empty]
      exact disjoint_left.mpr fun b hb ↦ hBL b (ht₀B hb)
    | succ j ih =>
      intro hj t ht hte htL
      have := card_sdiff_add_card_inter t L
      obtain ⟨b, hbB, hbt⟩ := exists_mem_notMem_of_card_lt_card (s := t \ L) (t := B) (by omega)
      have hbt : b ∉ t := fun h ↦ hbt <| mem_sdiff.mpr ⟨h, hBL b hbB⟩
      have hYL : insert b t ∩ L = t ∩ L := insert_inter_of_notMem (hBL b hbB)
      have hYB : insert b t ⊆ L ∪ B := insert_subset (mem_union_right _ hbB) ht
      have hYcard : #(insert b t) = e + 1 := by rw [card_insert_of_notMem hbt, hte]
      obtain ⟨x, hx⟩ : (t ∩ L).Nonempty := card_pos.mp (by omega)
      obtain ⟨hxt, hxL⟩ := mem_inter.mp hx
      by_contra hne
      have hGt : G t = G t₀ ↔ Even j := by
        rw [Nat.even_add_one] at hne
        tauto
      obtain ⟨s, hsY, hse, hs⟩ := hno (insert b t) (hYB.trans hLB) hYcard
        ⟨x, mem_insert_of_mem hxt, by simp [L] at hxL; omega⟩ (G t)
      apply hs
      obtain ⟨a, has, hins⟩ := exists_eq_insert_iff.mpr ⟨hsY, by rw [hse, hYcard]⟩
      by_cases haL : a ∈ L
      · have hsL : insert a (s ∩ L) = t ∩ L := by rw [← insert_inter_of_mem haL, hins, hYL]
        have : a ∉ s ∩ L := fun h ↦ has (mem_inter.mp h).1
        rw [← hsL, card_insert_of_notMem this] at htL
        exact hFin _ _ _ <| (ih (by omega) s (hsY.trans hYB) hse (by omega)).trans hGt.symm
      · apply hcol s (hsY.trans hYB) t ht hse hte
        rw [← insert_inter_of_notMem haL, hins, hYL]
  have hL : ∀ s ⊆ L, #s = e → (G s = G t₀ ↔ Even e) := by
    intro s hs hse
    apply hparity e le_rfl s (hs.trans subset_union_left) hse
    rw [inter_eq_left.mpr hs, hse]
  have hrange : range e ⊆ L := range_subset_range.mpr (by omega)
  obtain ⟨s, hs, hse, hne⟩ :=
    hno (L.erase 0) (((erase_subset 0 L).trans subset_union_left).trans hLB)
      (by rw [card_erase_of_mem (by simp [L])]; simp [L]) ⟨1, by simp [L], by omega⟩ (G (range e))
  have hsL : s ⊆ L := hs.trans (erase_subset 0 L)
  exact hne <| hFin _ _ _ <| (hL s hsL hse).trans (hL _ hrange (card_range e)).symm

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
