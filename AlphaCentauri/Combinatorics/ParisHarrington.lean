module

public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Arithmetic.HFS.Vec
public import AlphaCentauri.ToFoundation.NatCoding
public import AlphaCentauri.ToMathlib.List
public import AlphaCentauri.ToMathlib.Combinatorics.Ramsey

/-!
# The two-colour diagonal Paris–Harrington sentence

A finite set $Y$ is large if $|Y| \ge \min Y$, and $n \to_* (e + 1)^e_2$ says that every colouring
of the $e$-element subsets of $\{0, \dots, n - 1\}$ with two colours has a large homogeneous set
of size at least $e + 1$. The sentence $\forall e \ge 1\, \exists n\, (n \to_* (e + 1)^e_2)$ is
provable in $\mathsf{PA}$; with three colours instead of two, it is not.

- [Qui80, p. 77]
- [Kay91, §14.3]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Encodable Finset

/-- `v` codes a strictly increasing list of length `l`. -/
def isIncreasingList : ArithmeticSemisentence 2 :=
  “v l. !lenDef l v ∧ ∀ j < l, ∀ i < j, ∃ a, ∃ b, !nthDef a v i ∧ !nthDef b v j ∧ a < b”

/-- Each of the first `k` entries of the list `t` is one of the first `l` entries of the list `y`.
-/
def isListSubset : ArithmeticSemisentence 4 :=
  “t k y l. ∀ i < k, ∃ a, !nthDef a t i ∧ ∃ j < l, !nthDef a y j”

/-- $\forall e \ge 1\, \exists n\, (n \to_* (e + 1)^e_2)$: for every $e \ge 1$ there is an $n$
such that every colouring of the $e$-element subsets of $\{0, \dots, n - 1\}$ with two colours has
a homogeneous set $Y$ with $|Y| \ge e + 1$ and $|Y| \ge \min Y$. The domain starts at $0$ and
largeness is $|Y| \ge \min Y$, not $|Y| > \min Y$, as in all three sources. A subset is coded by
the list of its elements in increasing order, and a colouring by the set of the codes of the
subsets of colour $1$.
- [Qui80, p. 77]
- [Kay91, §14.3]
- [HP98, II.1.2] -/
def diagonalRamseyTwoColours : ArithmeticSentence :=
  “∀ e, 1 ≤ e → ∃ n, ∀ F, ∃ y, ∃ l, !isIncreasingList y l ∧ e + 1 ≤ l ∧
    (∃ m, !nthDef m y 0 ∧ m ≤ l) ∧ (∀ i < l, ∃ a, !nthDef a y i ∧ a < n) ∧
    ((∀ t, !isIncreasingList t e ∧ !isListSubset t e y l → t ∈ F) ∨
      (∀ t, !isIncreasingList t e ∧ !isListSubset t e y l → t ∉ F))”

axiom provable_diagonalRamseyTwoColours_PA : 𝗣𝗔 ⊢ diagonalRamseyTwoColours

lemma exists_finset_iff_increasingList {e : ℕ} {y : List ℕ} {t : ℕ} :
    (e = len t ∧ (∀ j < e, ∀ i < j, t.[i] < t.[j]) ∧
      ∀ i < e, ∃ j < y.length, t.[i] = y.getD j 0) ↔
    ∃ s ⊆ y.toFinset, s.card = e ∧ t = encode (s.sort (· ≤ ·)) := by
  obtain ⟨l, rfl⟩ : ∃ l : List ℕ, encode l = t := ⟨_, Denumerable.encode_ofNat t⟩
  simp only [len_encode_list, nth_encode_list]
  constructor
  · rintro ⟨rfl, hinc, hsub⟩
    rw [← List.sortedLT_iff_getD_lt_getD] at hinc
    rw [← List.subset_iff_getD] at hsub
    use l.toFinset
    and_intros
    · intro x hx
      simpa using hsub (by simpa using hx)
    · exact List.toFinset_card_of_nodup hinc.nodup
    rw [(List.toFinset_sort _ hinc.nodup).mpr]
    exact (List.sortedLT_iff_pairwise.mp hinc).imp le_of_lt
  · rintro ⟨s, hs, rfl, hl⟩
    obtain rfl := encode_injective hl
    have hinc := (List.sortedLT_iff_getD_lt_getD 0).mp (sortedLT_sort s)
    have hsub := (List.subset_iff_getD (t := s.sort (· ≤ ·)) (l := y) 0).mp fun x hx ↦ by
      simpa using hs (by simpa using hx)
    rw [length_sort] at hinc hsub
    exact ⟨by simp, hinc, hsub⟩

lemma forall_increasingList_iff {e : ℕ} {y : List ℕ} {P : ℕ → Prop} :
    (∀ t, e = len t → (∀ j < e, ∀ i < j, t.[i] < t.[j]) →
      (∀ i < e, ∃ j < y.length, t.[i] = y.getD j 0) → P t) ↔
    ∀ s ⊆ y.toFinset, s.card = e → P (encode (s.sort (· ≤ ·))) := by
  constructor
  · intro H s hs hse
    obtain ⟨h₁, h₂, h₃⟩ := exists_finset_iff_increasingList.mpr ⟨s, hs, hse, rfl⟩
    exact H _ h₁ h₂ h₃
  · intro H t h₁ h₂ h₃
    obtain ⟨s, hs, hse, rfl⟩ := exists_finset_iff_increasingList.mp ⟨h₁, h₂, h₃⟩
    exact H s hs hse

lemma nat_models_diagonalRamseyTwoColours_iff : ℕ↓[ℒₒᵣ] ⊧ diagonalRamseyTwoColours ↔
    ∀ e ≥ 1, ∃ n, ∀ F : (Finset.range n).powersetCard e → Fin 2,
      ∃ Y ⊆ Finset.range n, e + 1 ≤ Y.card ∧ (∃ x ∈ Y, x ≤ Y.card) ∧
        ∃ c, ∀ s : (Finset.range n).powersetCard e, (s : Finset ℕ) ⊆ Y → F s = c := by
  classical
  simp only [diagonalRamseyTwoColours, Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue,
    isIncreasingList, Nat.succ_eq_add_one, LogicalConnective.HomClass.map_and, isListSubset,
    models_iff, Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
    Semiformula.eval_operator, Matrix.comp₂, Semiterm.val_operator, Matrix.comp₀,
    Tarski.Structure.numeral_eq_numeral, ORingStructure.one_eq_one, Semiterm.val_bvar,
    Matrix.cons_val_fin_one, Tarski.Structure.LE.le, Semiformula.eval_ex, Semiformula.eval_substs,
    Matrix.cons_val_one, Matrix.cons_val_zero, Bounding.HierarchySymbol.Defined.iff,
    Fin.succ_zero_eq_one, Semiformula.eval_ballLT, Matrix.comp₃, Matrix.cons_app_four,
    Matrix.cons_app_three, Matrix.cons_app_two, Fin.succ_one_eq_two, Tarski.Structure.lt_iff_lt,
    LogicalConnective.Prop.and_eq, exists_and_left, ↓existsAndEq, true_and, exists_eq_left,
    Tarski.Structure.Add.add, Order.add_one_le_iff, ORingStructure.zero_eq_zero,
    Matrix.cons_app_five, LogicalConnective.HomClass.map_or, Matrix.comp₄,
    Semiformula.eval_bexsLT, Tarski.Structure.mem_iff_mem, LogicalConnective.Prop.arrow_eq, and_imp,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
    LogicalConnective.Prop.or_eq, ge_iff_le, Subtype.forall, mem_powersetCard, forall_and_index,
    Fin.exists_fin_two]
  refine forall₂_congr fun e he ↦ exists_congr fun n ↦ ⟨fun H F ↦ ?_, fun H F ↦ ?_⟩
  · let S : Finset ℕ := (((Finset.range n).powersetCard e).attach.filter (F · = 1)).image
      fun s ↦ encode (s.1.sort (· ≤ ·))
    have hS : ∀ s (hs : s ∈ (Finset.range n).powersetCard e),
        encode (s.sort (· ≤ ·)) ∈ (∑ i ∈ S, 2 ^ i : ℕ) ↔ F ⟨s, hs⟩ = 1 := by
      intro s hs
      rw [mem_sum_two_pow_iff]
      simp only [S, mem_image, mem_filter, mem_attach, true_and, Subtype.exists]
      constructor
      · rintro ⟨a, ha, hFa, h⟩
        obtain rfl : a = s := by simpa using congrArg List.toFinset (encode_injective h)
        exact hFa
      · intro h
        use s
        exact ⟨hs, h, rfl⟩
    obtain ⟨y, hinc, hlen, hmin, hlt, hhom⟩ := H (∑ i ∈ S, 2 ^ i)
    obtain ⟨y, rfl⟩ : ∃ l : List ℕ, encode l = y := ⟨_, Denumerable.encode_ofNat y⟩
    simp only [len_encode_list, nth_encode_list, ← List.sortedLT_iff_getD_lt_getD,
      forall_increasingList_iff] at hinc hlen hmin hlt hhom
    replace hlt := (List.forall_mem_iff_getD (P := (· < n)) 0).mpr hlt
    have hcard : y.toFinset.card = y.length := List.toFinset_card_of_nodup hinc.nodup
    use y.toFinset
    and_intros
    · intro x hx
      simpa using hlt x (by simpa using hx)
    · omega
    · use y.getD 0 0
      and_intros
      · rw [List.mem_toFinset, List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      · omega
    · rcases hhom with hhom | hhom
      · right
        intro a han hae haY
        exact (hS a (by simp [han, hae])).mp (hhom a haY hae)
      · left
        intro a han hae haY
        have := (hS a (by simp [han, hae])).not.mp (hhom a haY hae)
        omega
  · obtain ⟨Y, hYn, hcard, ⟨x, hxY, hx⟩, hhom⟩ :=
      H fun s ↦ if encode (s.1.sort (· ≤ ·)) ∈ F then 1 else 0
    use encode Y.sort
    simp only [len_encode_list, nth_encode_list, forall_increasingList_iff, sort_toFinset]
    and_intros
    · exact (List.sortedLT_iff_getD_lt_getD 0).mp (sortedLT_sort Y)
    · simpa using hcard
    · rw [length_sort, List.getD_eq_getElem _ _ (by rw [length_sort]; omega), sorted_zero_eq_min']
      exact (min'_le Y x hxY).trans hx
    · apply (List.forall_mem_iff_getD (P := (· < n)) 0).mp
      intro x hx
      simpa using hYn (by simpa using hx)
    · rcases hhom with hhom | hhom
      · right
        intro s hsY hse
        simpa using hhom s (hsY.trans hYn) hse hsY
      · left
        intro s hsY hse
        simpa using hhom s (hsY.trans hYn) hse hsY

/-- The two-colour diagonal Paris–Harrington sentence is true in $\mathbb{N}$.

- [Qui80, p. 77]
- [Kay91, §14.3] -/
theorem nat_models_diagonalRamseyTwoColours : ℕ↓[ℒₒᵣ] ⊧ diagonalRamseyTwoColours := by
  apply nat_models_diagonalRamseyTwoColours_iff.mpr
  intro e he
  obtain ⟨n, hn⟩ := exists_diagonal_paris_harrington he
  use n
  intro F
  obtain ⟨Y, hYn, hY, ⟨x, hxY, hx⟩, i, hi⟩ :=
    hn fun s ↦ if h : s ∈ (Finset.range n).powersetCard e then F ⟨s, h⟩ else 0
  use Y
  and_intros
  · exact hYn
  · omega
  · use x, hxY
    omega
  use i
  intro s hs
  simpa [s.2] using hi s hs (mem_powersetCard.mp s.2).2

end FFL.FirstOrder.Arithmetic
