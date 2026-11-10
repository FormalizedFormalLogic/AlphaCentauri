module

public import AlphaCentauri.ToMathlib.OpenPredicate
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Open induction of bounded degree

A predicate on a commutative ordered ring `R` is `DeterminedBySigns N` if its truth value at `x`
depends only on the signs of finitely many polynomials of degree at most `N` at `x`. If `R` is
discretely ordered and embeds into an ordered field `K` with the intermediate value property for
polynomials, in which every root of a nonzero polynomial over `R` of degree at most `N` has an
integer part in `R`, then induction holds for such predicates.
-/

@[expose] public section

open Polynomial

namespace OpenPredicate

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- The truth value of `P` at `x` depends only on the signs at `x` of finitely many polynomials of
degree at most `N`. -/
def DeterminedBySigns (N : ℕ) (P : R → Prop) : Prop :=
  ∃ s : Finset R[X], (∀ p ∈ s, p.natDegree ≤ N) ∧ ∀ x y : R,
    (∀ p ∈ s, (p.eval x = 0 ↔ p.eval y = 0) ∧ (0 < p.eval x ↔ 0 < p.eval y)) → (P x ↔ P y)

namespace DeterminedBySigns

variable {N : ℕ} {P Q : R → Prop}

lemma of_iff (hP : DeterminedBySigns N P) (h : ∀ x, P x ↔ Q x) : DeterminedBySigns N Q := by
  obtain ⟨s, hs, hd⟩ := hP
  exact ⟨s, hs, fun x y hxy ↦ (h x).symm.trans ((hd x y hxy).trans (h y))⟩

lemma eq_zero {p : R[X]} (hp : p.natDegree ≤ N) : DeterminedBySigns N fun x ↦ p.eval x = 0 :=
  ⟨{p}, by simpa using hp, fun x y h ↦ (h p (by simp)).1⟩

lemma pos {p : R[X]} (hp : p.natDegree ≤ N) : DeterminedBySigns N fun x ↦ 0 < p.eval x :=
  ⟨{p}, by simpa using hp, fun x y h ↦ (h p (by simp)).2⟩

lemma not (hP : DeterminedBySigns N P) : DeterminedBySigns N fun x ↦ ¬P x := by
  obtain ⟨s, hs, hd⟩ := hP
  exact ⟨s, hs, fun x y h ↦ not_congr (hd x y h)⟩

lemma and (hP : DeterminedBySigns N P) (hQ : DeterminedBySigns N Q) :
    DeterminedBySigns N fun x ↦ P x ∧ Q x := by
  classical
  obtain ⟨s, hs, hd⟩ := hP
  obtain ⟨t, ht, he⟩ := hQ
  use s ∪ t
  constructor
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    exacts [hs p hp, ht p hp]
  · intro x y h
    exact and_congr (hd x y fun p hp ↦ h p (by simp [hp])) (he x y fun p hp ↦ h p (by simp [hp]))

lemma or (hP : DeterminedBySigns N P) (hQ : DeterminedBySigns N Q) :
    DeterminedBySigns N fun x ↦ P x ∨ Q x :=
  (hP.not.and hQ.not).not.of_iff fun _ ↦ by tauto

variable [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
lemma eq {p q : R[X]} (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N) :
    DeterminedBySigns N fun x ↦ p.eval x = q.eval x :=
  (eq_zero ((natDegree_sub_le p q).trans (max_le hp hq))).of_iff fun _ ↦ by simp [sub_eq_zero]

lemma lt {p q : R[X]} (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N) :
    DeterminedBySigns N fun x ↦ p.eval x < q.eval x :=
  (pos ((natDegree_sub_le q p).trans (max_le hq hp))).of_iff fun _ ↦ by simp

variable [DiscretelyOrdered R] {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (ι : R →+* K) (hι : StrictMono ι)
  (hivt : ∀ f : K[X], ∀ a b : K, a < b → f.eval a < 0 → 0 < f.eval b →
    ∃ c, a < c ∧ c < b ∧ f.IsRoot c)
  (hint : ∀ f : R[X], f ≠ 0 → f.natDegree ≤ N → ∀ α : K, (f.map ι).IsRoot α →
    ∃ r : R, ι r ≤ α ∧ α < ι r + 1)
include hι hivt hint

/-- Induction for predicates determined by the signs of polynomials of degree at most `N`.
- [Kov24, Theorem 2.2] -/
theorem induction (hP : DeterminedBySigns N P) (h0 : P 0)
    (hs : ∀ x, 0 ≤ x → P x → P (x + 1)) : ∀ x, 0 ≤ x → P x := by
  classical
  obtain ⟨s, hdeg, hdet⟩ := hP
  set A : Finset K := (s.filter (· ≠ 0)).biUnion fun p ↦ (p.map ι).roots.toFinset
  have hA : ∀ α ∈ A, ∃ r : R, ι r ≤ α ∧ α < ι r + 1 := by
    intro α hα
    simp only [A, Finset.mem_biUnion, Finset.mem_filter, Multiset.mem_toFinset] at hα
    obtain ⟨p, ⟨hps, hp0⟩, hα⟩ := hα
    exact hint p hp0 (hdeg p hps) α (mem_roots'.mp hα).2
  choose! fl hfl using hA
  have hdisc {x y : R} (h : x < y + 1) : x ≤ y := by
    by_contra h'
    have := DiscretelyOrdered.one_le_of_pos (x - y) (sub_pos.mpr (not_le.mp h'))
    linarith
  have hevalι (p : R[X]) (x : R) : (p.map ι).eval (ι x) = ι (p.eval x) := by
    rw [eval_map, eval₂_at_apply]
  -- Between two points with no root of a polynomial of `s` in between, `P` is constant.
  have hconst (x y : R) (hxy : x ≤ y) (hroot : ∀ α ∈ A, ¬(ι x ≤ α ∧ α ≤ ι y)) : P x ↔ P y := by
    apply hdet
    intro p hps
    by_cases hp0 : p = 0
    · simp [hp0]
    have hmem (α : K) (h : (p.map ι).IsRoot α) : α ∈ A := by
      simp only [A, Finset.mem_biUnion, Finset.mem_filter, Multiset.mem_toFinset]
      exact ⟨p, ⟨hps, hp0⟩, (mem_roots ((Polynomial.map_ne_zero_iff hι.injective).mpr hp0)).mpr h⟩
    have hx : p.eval x ≠ 0 := fun h ↦ hroot _ (hmem _ (by simp [IsRoot, hevalι, h]))
      ⟨le_rfl, hι.monotone hxy⟩
    have hy : p.eval y ≠ 0 := fun h ↦ hroot _ (hmem _ (by simp [IsRoot, hevalι, h]))
      ⟨hι.monotone hxy, le_rfl⟩
    have hsign : (0 < p.eval x ↔ 0 < p.eval y) := by
      rcases hxy.eq_or_lt with rfl | hlt
      · rfl
      have key (f : K[X]) (hf : ∀ α, f.IsRoot α → α ∈ A) (ha : f.eval (ι x) < 0)
          (hb : 0 < f.eval (ι y)) : False := by
        obtain ⟨c, hc₁, hc₂, hc⟩ := hivt f _ _ (hι hlt) ha hb
        exact hroot c (hf c hc) ⟨hc₁.le, hc₂.le⟩
      have hι0 (u : R) : 0 < ι u ↔ 0 < u := by simpa using hι.lt_iff_lt (a := 0) (b := u)
      have hιneg (u : R) : ι u < 0 ↔ u < 0 := by simpa using hι.lt_iff_lt (a := u) (b := 0)
      constructor
      · intro h
        by_contra h'
        have hneg : p.eval y < 0 := lt_of_le_of_ne (not_lt.mp h') hy
        apply key (-(p.map ι)) (fun α h ↦ hmem α (by simpa using h)) <;>
          simp [hevalι, hι0, hιneg, h, hneg]
      · intro h
        by_contra h'
        have hneg : p.eval x < 0 := lt_of_le_of_ne (not_lt.mp h') hx
        apply key (p.map ι) hmem <;> simp [hevalι, hι0, hιneg, h, hneg]
    exact ⟨by simp [hx, hy], hsign⟩
  intro c hc
  by_contra hPc
  set C : Finset R := insert 0 (insert c (A.image fl ∪ A.image (fl · + 1)))
  set S := C.filter fun y ↦ 0 ≤ y ∧ ¬P y
  obtain ⟨m, hmS, hmin⟩ := S.exists_min_image id ⟨c, by simp [S, C, hc, hPc]⟩
  simp only [S, Finset.mem_filter] at hmS
  have hflC (α : K) (hα : α ∈ A) : fl α ∈ C ∧ fl α + 1 ∈ C :=
    ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image_of_mem fl hα))),
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image_of_mem (fl · + 1) hα)))⟩
  have hbelow : ∀ x, 0 ≤ x → x < m → P x := by
    intro x hx hxm
    by_contra hPx
    obtain ⟨y, hyC, hymax⟩ := (C.filter (· ≤ x)).exists_max_image id ⟨0, by simp [C, hx]⟩
    rw [Finset.mem_filter] at hyC
    have hmax' : ∀ z ∈ C, z ≤ x → z ≤ y := fun z hz hzx ↦ hymax z (by simp [hz, hzx])
    have hy0 : 0 ≤ y := hmax' 0 (by simp [C]) hx
    have hyx : y < x := by
      refine lt_of_le_of_ne hyC.2 fun h ↦ (not_le.mpr hxm) (hmin x ?_)
      exact Finset.mem_filter.mpr ⟨h ▸ hyC.1, hx, hPx⟩
    have hroot : ∀ α ∈ A, ¬(ι y ≤ α ∧ α ≤ ι x) := by
      rintro α hα ⟨h₁, h₂⟩
      obtain ⟨hr₁, hr₂⟩ := hfl α hα
      by_cases h : fl α + 1 ≤ x
      · have := hι.monotone (hmax' _ (hflC α hα).2 h)
        rw [map_add, map_one] at this
        linarith
      · have hrx : fl α ≤ x := hι.le_iff_le.mp (hr₁.trans h₂)
        have hxr : x ≤ fl α := hdisc (not_le.mp h)
        have := hmax' x (le_antisymm hrx hxr ▸ (hflC α hα).1) le_rfl
        exact (lt_irrefl _ (hyx.trans_le this))
    exact hPx ((hconst y x hyx.le hroot).mp (by
      by_contra hPy
      exact (not_le.mpr (hyx.trans hxm)) (hmin y (Finset.mem_filter.mpr ⟨hyC.1, hy0, hPy⟩))))
  rcases hmS.2.1.eq_or_lt with h | h
  · exact hmS.2.2 (h ▸ h0)
  · have hm1 := DiscretelyOrdered.one_le_of_pos m h
    have := hs (m - 1) (by linarith) (hbelow (m - 1) (by linarith) (by linarith))
    exact hmS.2.2 (by simpa using this)

end DeterminedBySigns

end OpenPredicate
