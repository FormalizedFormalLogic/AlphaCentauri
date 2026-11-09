module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Order.Int.LeastGreatest
public import Mathlib.RingTheory.HahnSeries.Lex
public import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Integer parts of Hahn series

`HahnSeries.supportedIn G` is the subring of the Hahn series `Lex ℝ⟦ℚ⟧`, ordered
lexicographically, whose support lies in the additive subgroup `G` of `ℚ`, and
`HahnSeries.integerPartSubring G` is the subring of those supported in the non-positive part of `G`
with an integer constant coefficient. If `G` is closed under division by `1, …, N`, then every root
of a nonzero polynomial of degree at most `N` with coefficients in `supportedIn G` lies in
`supportedIn G`, and so has an integer part in `integerPartSubring G`.
-/

@[expose] public section

open Polynomial

namespace HahnSeries

variable (G : AddSubgroup ℚ)

/-- The Hahn series whose support lies in `G`. -/
def supportedIn : Subring (Lex ℝ⟦ℚ⟧) where
  carrier := {x | ∀ g ∈ (ofLex x).support, g ∈ G}
  mul_mem' {x y} hx hy g hg := by
    obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hg
    exact G.add_mem (hx i hi) (hy j hj)
  one_mem' g hg := by
    simp only [ofLex_one, support_one, Set.mem_singleton_iff] at hg
    exact hg ▸ G.zero_mem
  add_mem' {x y} hx hy g hg := by
    rcases support_add_subset (ofLex x) (ofLex y) hg with h | h
    exacts [hx g h, hy g h]
  zero_mem' g hg := by simp at hg
  neg_mem' {x} hx g hg := hx g (by simpa using hg)

lemma coeff_mul_zero_of_support_nonpos {x y : ℝ⟦ℚ⟧} (hx : ∀ g ∈ x.support, g ≤ 0)
    (hy : ∀ g ∈ y.support, g ≤ 0) : (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  rw [coeff_mul, Finset.sum_eq_single ((0 : ℚ), (0 : ℚ))]
  · rintro ⟨i, j⟩ hij hne
    obtain ⟨hi, hj, hij⟩ := Finset.mem_antidiagonal.mp hij
    have := hx i hi
    have := hy j hj
    exact absurd (Prod.ext (by simp only; linarith) (by simp only; linarith)) hne
  · intro h
    simp only [Finset.mem_antidiagonal, mem_support, add_zero, and_true, not_and_or,
      not_not] at h
    rcases h with h | h <;> simp [h]

/-- The Hahn series supported in the non-positive part of `G` whose constant coefficient is an
integer. -/
def integerPartSubring : Subring (Lex ℝ⟦ℚ⟧) where
  carrier := {x | (∀ g ∈ (ofLex x).support, g ∈ G ∧ g ≤ 0) ∧ ∃ n : ℤ, (ofLex x).coeff 0 = n}
  mul_mem' {x y} hx hy := by
    obtain ⟨hx, m, hm⟩ := hx
    obtain ⟨hy, n, hn⟩ := hy
    constructor
    · intro g hg
      obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hg
      exact ⟨G.add_mem (hx i hi).1 (hy j hj).1, add_nonpos (hx i hi).2 (hy j hj).2⟩
    · use m * n
      rw [ofLex_mul, coeff_mul_zero_of_support_nonpos (fun g hg ↦ (hx g hg).2)
        (fun g hg ↦ (hy g hg).2), hm, hn]
      push_cast
      rfl
  one_mem' := by
    constructor
    · intro g hg
      simp only [ofLex_one, support_one, Set.mem_singleton_iff] at hg
      subst hg
      exact ⟨G.zero_mem, le_rfl⟩
    · use 1
      simp
  add_mem' {x y} hx hy := by
    obtain ⟨hx, m, hm⟩ := hx
    obtain ⟨hy, n, hn⟩ := hy
    constructor
    · intro g hg
      rcases support_add_subset (ofLex x) (ofLex y) hg with h | h
      exacts [hx g h, hy g h]
    · use m + n
      simp [hm, hn]
  zero_mem' := ⟨by simp, 0, by simp⟩
  neg_mem' {x} hx := by
    obtain ⟨hx, n, hn⟩ := hx
    exact ⟨fun g hg ↦ hx g (by simpa using hg), -n, by simp [hn]⟩

variable {G}

lemma coeff_order_ne_zero {x : ℝ⟦ℚ⟧} (h : x ≠ 0) : x.coeff x.order ≠ 0 :=
  mt coeff_order_eq_zero.mp h

lemma pos_of_coeff {x : Lex ℝ⟦ℚ⟧} {i : ℚ} (h : ∀ j < i, (ofLex x).coeff j = 0)
    (hi : 0 < (ofLex x).coeff i) : 0 < x :=
  (lt_iff 0 x).mpr ⟨i, fun j hj ↦ by simp [h j hj], by simpa using hi⟩

lemma lt_of_order_lt {x y : Lex ℝ⟦ℚ⟧} (hx : 0 < x) (hy : 0 < y)
    (h : (ofLex x).order < (ofLex y).order) : y < x := by
  have hx' : ofLex x ≠ 0 := hx.ne'
  have hy' : ofLex y ≠ 0 := hy.ne'
  have := abs_lt_abs_of_orderTop_ofLex (x := y) (y := x) (by
    rw [← order_eq_orderTop_of_ne_zero hx', ← order_eq_orderTop_of_ne_zero hy']
    exact WithTop.coe_lt_coe.mpr h)
  rwa [abs_of_pos hx, abs_of_pos hy] at this

lemma order_mem_of_mem_supportedIn {x : Lex ℝ⟦ℚ⟧} (hx : x ∈ supportedIn G) (h : x ≠ 0) :
    (ofLex x).order ∈ G :=
  hx _ (coeff_order_ne_zero (x := ofLex x) h)

lemma integerPartSubring_le_supportedIn : integerPartSubring G ≤ supportedIn G :=
  fun _ hx g hg ↦ (hx.1 g hg).1

/-- A Hahn series supported in the non-negative rationals lies between consecutive integers. -/
lemma exists_intCast_le_lt_of_support_nonneg {β : Lex ℝ⟦ℚ⟧}
    (hβ : ∀ g ∈ (ofLex β).support, 0 ≤ g) : ∃ n : ℤ, (n : Lex ℝ⟦ℚ⟧) ≤ β ∧ β < n + 1 := by
  have hbelow (j : ℚ) (hj : j < 0) : (ofLex β).coeff j = 0 := by
    by_contra h
    exact (hβ j ((mem_support _ _).mpr h)).not_gt hj
  have hcast (u : ℝ) : (ofLex (toLex (C u : ℝ⟦ℚ⟧))).coeff = fun j ↦ if j = 0 then u else 0 := by
    ext j
    simp [C_apply, coeff_single]
  have hlt (u : ℝ) (h : u < (ofLex β).coeff 0) : toLex (C u) < β := by
    rw [← sub_pos]
    apply pos_of_coeff (i := 0)
    · intro j hj
      simp [hj.ne, hbelow j hj]
    · simpa [hcast] using h
  have hgt (u : ℝ) (h : (ofLex β).coeff 0 < u) : β < toLex (C u) := by
    rw [← sub_pos]
    apply pos_of_coeff (i := 0)
    · intro j hj
      simp [hj.ne, hbelow j hj]
    · simpa [hcast] using h
  have hint (n : ℤ) : (n : Lex ℝ⟦ℚ⟧) = toLex (C (n : ℝ)) := by simp [map_intCast]
  set c := (ofLex β).coeff 0
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd (P := fun n : ℤ ↦ (n : Lex ℝ⟦ℚ⟧) ≤ β)
    ⟨⌈c⌉, fun z hz ↦ by
      by_contra h
      have : c < z := by linarith [Int.ceil_lt_iff.mp (lt_of_not_ge h)]
      exact (hgt z this).not_ge (hint z ▸ hz)⟩
    ⟨⌊c⌋ - 1, by
      rw [hint]
      apply (hlt _ _).le
      push_cast
      linarith [Int.floor_le c]⟩
  use n, hn
  by_contra h
  have := hmax (n + 1) (by push_cast; exact not_lt.mp h)
  omega

/-- Every Hahn series supported in `G` has an integer part in `integerPartSubring G`. -/
lemma exists_mem_integerPartSubring_le_lt {α : Lex ℝ⟦ℚ⟧} (hα : α ∈ supportedIn G) :
    ∃ r ∈ integerPartSubring G, r ≤ α ∧ α < r + 1 := by
  set τ : Lex ℝ⟦ℚ⟧ := toLex (truncLT 0 (ofLex α))
  obtain ⟨n, hn₁, hn₂⟩ := exists_intCast_le_lt_of_support_nonneg (β := α - τ) (by
    intro g hg
    by_contra h
    simp [τ, coeff_truncLT_of_lt (not_le.mp h)] at hg)
  have hτ : τ ∈ integerPartSubring G := by
    constructor
    · intro g hg
      simp only [τ, ofLex_toLex, support_truncLT, Set.mem_ofPred_eq] at hg
      exact ⟨hα g hg.1, hg.2.le⟩
    · use 0
      simp [τ, coeff_truncLT_of_le le_rfl]
  use τ + n, add_mem hτ (intCast_mem _ n)
  constructor
  · exact le_sub_iff_add_le'.mp hn₁
  · rw [add_assoc]
    exact sub_lt_iff_lt_add'.mp hn₂

/-- A polynomial over `supportedIn G` of degree at most `N` does not vanish at a nonzero series
whose order lies outside `G`, if `G` is closed under division by `1, …, N`. -/
lemma eval_ne_zero_of_order_notMem {N : ℕ}
    (hG : ∀ d : ℕ, 0 < d → d ≤ N → ∀ q : ℚ, (d : ℚ) * q ∈ G → q ∈ G)
    {f : (Lex ℝ⟦ℚ⟧)[X]} (hf : f ≠ 0) (hN : f.natDegree ≤ N) (hc : ∀ i, f.coeff i ∈ supportedIn G)
    {s : Lex ℝ⟦ℚ⟧} (hs : s ≠ 0) (hsG : (ofLex s).order ∉ G) : f.eval s ≠ 0 := by
  set γ := (ofLex s).order
  set T := (Finset.range (f.natDegree + 1)).filter fun i ↦ f.coeff i ≠ 0
  let o : ℕ → ℚ := fun i ↦ (ofLex (f.coeff i)).order + i * γ
  have ho (i : ℕ) (hi : f.coeff i ≠ 0) : (ofLex (f.coeff i * s ^ i)).order = o i := by
    rw [ofLex_mul, ofLex_pow, order_mul (by simpa using hi) (pow_ne_zero _ (by simpa using hs)),
      order_pow, nsmul_eq_mul]
  have hinj : ∀ i ∈ T, ∀ j ∈ T, o i = o j → i = j := by
    intro i hi j hj hij
    by_contra hne
    wlog hlt : i < j generalizing i j
    · exact this j hj i hi hij.symm (Ne.symm hne) (by omega)
    simp only [T, Finset.mem_filter, Finset.mem_range] at hi hj
    apply hsG
    apply hG (j - i) (by omega) (by omega)
    have : ((j - i : ℕ) : ℚ) * γ = (ofLex (f.coeff i)).order - (ofLex (f.coeff j)).order := by
      push_cast [Nat.cast_sub hlt.le]
      simp only [o] at hij
      linarith
    rw [this]
    exact G.sub_mem (order_mem_of_mem_supportedIn (hc i) hi.2)
      (order_mem_of_mem_supportedIn (hc j) hj.2)
  obtain ⟨j₀, hj₀, hmin⟩ := T.exists_min_image o ⟨f.natDegree, by simp [T, hf]⟩
  simp only [T, Finset.mem_filter, Finset.mem_range] at hj₀
  intro h0
  have h := congrArg (fun x : Lex ℝ⟦ℚ⟧ ↦ (ofLex x).coeff (o j₀)) h0
  simp only [eval_eq_sum_range] at h
  change (∑ i ∈ Finset.range (f.natDegree + 1), ofLex (f.coeff i * s ^ i)).coeff (o j₀) = 0 at h
  rw [coeff_sum, Finset.sum_eq_single_of_mem j₀ (Finset.mem_range.mpr hj₀.1)] at h
  · apply coeff_order_ne_zero (x := ofLex (f.coeff j₀ * s ^ j₀))
      (mul_ne_zero hj₀.2 (pow_ne_zero _ hs))
    rwa [ho j₀ hj₀.2]
  · intro i hi hne
    by_cases hci : f.coeff i = 0
    · simp [hci]
    apply coeff_eq_zero_of_lt_order
    rw [ho i hci]
    have hiT : i ∈ T := by simpa [T, hci] using hi
    exact lt_of_le_of_ne (hmin i hiT) fun h ↦ hne (hinj i hiT j₀ (by simpa [T] using hj₀) h.symm)

/-- A root of a nonzero polynomial over `supportedIn G` of degree at most `N` lies in
`supportedIn G`, if `G` is closed under division by `1, …, N`.
- [Kov24, Lemma 2.3] -/
lemma mem_supportedIn_of_isRoot {N : ℕ}
    (hG : ∀ d : ℕ, 0 < d → d ≤ N → ∀ q : ℚ, (d : ℚ) * q ∈ G → q ∈ G)
    {f : (Lex ℝ⟦ℚ⟧)[X]} (hf : f ≠ 0) (hN : f.natDegree ≤ N) (hc : ∀ i, f.coeff i ∈ supportedIn G)
    {α : Lex ℝ⟦ℚ⟧} (hα : f.IsRoot α) : α ∈ supportedIn G := by
  by_contra hαG
  set B := {g ∈ (ofLex α).support | g ∉ G}
  have hB : B.Nonempty := by
    simp only [supportedIn, Subring.mem_mk, Subsemiring.mem_mk, Submonoid.mem_mk,
      Subsemigroup.mem_mk, Set.mem_ofPred_eq, not_forall] at hαG
    obtain ⟨g, hg, hgG⟩ := hαG
    exact ⟨g, hg, hgG⟩
  have hwf : B.IsWF := (ofLex α).isWF_support.subset fun _ hg ↦ hg.1
  set γ := hwf.min hB
  have hγ : γ ∈ B := hwf.min_mem hB
  set r : Lex ℝ⟦ℚ⟧ := toLex (truncLT γ (ofLex α))
  have hr : r ∈ supportedIn G := by
    intro g hg
    simp only [r, ofLex_toLex, support_truncLT, Set.mem_ofPred_eq] at hg
    by_contra h
    exact hwf.not_lt_min hB ⟨hg.1, h⟩ hg.2
  have hcoeff (g : ℚ) : (ofLex (α - r)).coeff g = if g < γ then 0 else (ofLex α).coeff g := by
    simp only [r, ofLex_sub, ofLex_toLex, coeff_sub, HahnSeries.coeff_truncLT]
    split_ifs <;> simp
  have hγne : (ofLex (α - r)).coeff γ ≠ 0 := by
    simpa only [hcoeff, lt_irrefl, ↓reduceIte] using (mem_support _ _).mp hγ.1
  have hs : α - r ≠ 0 := fun h ↦ hγne (by simp [h])
  have hsγ : (ofLex (α - r)).order = γ := by
    apply le_antisymm (order_le_of_coeff_ne_zero hγne)
    by_contra h
    exact coeff_order_ne_zero (x := ofLex (α - r)) hs
      (by simp only [hcoeff, not_le.mp h, ↓reduceIte])
  obtain ⟨f₀, rfl⟩ := (mem_lifts f).mp <|
    (lifts_iff_coeff_lifts (f := (supportedIn G).subtype) f).mpr fun n ↦ ⟨⟨_, hc n⟩, rfl⟩
  set g := (f₀.comp (X + Polynomial.C ⟨r, hr⟩)).map (supportedIn G).subtype
  have hg : g ≠ 0 := by
    simp only [g, ne_eq, Polynomial.map_eq_zero_iff (supportedIn G).subtype_injective,
      comp_X_add_C_eq_zero_iff]
    rintro rfl
    simp at hf
  have hgN : g.natDegree ≤ N := by
    rw [natDegree_map_eq_of_injective (supportedIn G).subtype_injective] at hN ⊢
    simpa [g, natDegree_comp] using hN
  apply eval_ne_zero_of_order_notMem hG hg hgN (fun i ↦ by simp [g, coeff_map]) hs
    (hsγ ▸ hγ.2)
  simpa [g, map_comp, eval_comp] using hα

lemma one_le_of_mem_integerPartSubring {x : Lex ℝ⟦ℚ⟧} (hx : x ∈ integerPartSubring G)
    (hpos : 0 < x) : 1 ≤ x := by
  obtain ⟨hsupp, n, hn⟩ := hx
  have hx0 : ofLex x ≠ 0 := hpos.ne'
  have hord := hsupp _ (coeff_order_ne_zero hx0)
  rcases hord.2.lt_or_eq with h | h
  · exact (lt_of_order_lt hpos one_pos (by simpa using h)).le
  · have hxC : ofLex x = C (n : ℝ) := by
      ext g
      rw [C_apply, coeff_single]
      split_ifs with hg
      · exact hg ▸ hn
      · rcases lt_or_gt_of_ne hg with hg | hg
        · exact coeff_eq_zero_of_lt_order (h ▸ hg)
        · by_contra hm
          exact (hsupp g ((mem_support _ _).mpr hm)).2.not_gt hg
    have : (0 : ℤ) < n := by
      have := leadingCoeff_pos_iff.mpr hpos
      rw [leadingCoeff_eq, h, hn] at this
      exact_mod_cast this
    have hxn : x = n := by rw [← toLex_ofLex x, hxC, map_intCast, toLex_intCast]
    rw [hxn]
    exact_mod_cast this

/-- The infinite series `t⁻¹ = single (-1) 1` has no integer `p`-th root in `integerPartSubring G`
if `p * q = -1` has no solution `q` in `G`. -/
lemma not_pow_le_lt_add_one_pow {p : ℕ} (hpG : ∀ q ∈ G, (p : ℚ) * q ≠ -1)
    {y : Lex ℝ⟦ℚ⟧} (hy : y ∈ integerPartSubring G) (hy0 : 0 ≤ y) :
    ¬(y ^ p ≤ toLex (single (-1 : ℚ) (1 : ℝ)) ∧ toLex (single (-1 : ℚ) (1 : ℝ)) < (y + 1) ^ p) := by
  set a : Lex ℝ⟦ℚ⟧ := toLex (single (-1 : ℚ) (1 : ℝ))
  have ha : 0 < a := pos_of_coeff (i := -1) (fun j hj ↦ by simp [a, hj.ne])
    (by simp [a])
  have hoa : (ofLex a).order = -1 := by simp [a]
  have h1a : 1 < a := lt_of_order_lt ha one_pos (by simp [hoa])
  rintro ⟨h₁, h₂⟩
  rcases hy0.eq_or_lt with rfl | hpos
  · simp at h₂
    exact h₂.not_gt h1a
  have hy1 := one_le_of_mem_integerPartSubring hy hpos
  have h₃ : a < 2 ^ p * y ^ p := h₂.trans_le (by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) p)
  have hyp : ofLex (y ^ p) ≠ 0 := (pow_pos hpos p).ne'
  have ho : (ofLex (y ^ p)).order = p * (ofLex y).order := by
    rw [ofLex_pow, order_pow, nsmul_eq_mul]
  have ho₂ : (ofLex (2 ^ p * y ^ p)).order = (ofLex (y ^ p)).order := by
    have h2 : ofLex (2 ^ p : Lex ℝ⟦ℚ⟧) = C (2 ^ p : ℝ) := by
      change (2 : ℝ⟦ℚ⟧) ^ p = C (2 ^ p : ℝ)
      rw [map_pow, map_ofNat]
    rw [ofLex_mul, h2, order_mul (C_ne_zero (by positivity)) hyp, order_C, zero_add]
  rcases lt_trichotomy (ofLex (y ^ p)).order (-1) with h | h | h
  · exact h₁.not_gt (lt_of_order_lt (pow_pos hpos p) ha (by rwa [hoa]))
  · exact hpG _ (hy.1 _ (coeff_order_ne_zero (x := ofLex y) hpos.ne')).1 (ho ▸ h)
  · exact h₃.not_gt (lt_of_order_lt ha (by positivity) (by rwa [hoa, ho₂]))

end HahnSeries

namespace AddSubgroup

/-- The rationals `z / n ^ k` with `z : ℤ` and `k : ℕ`. -/
def powDenominators (n : ℕ) : AddSubgroup ℚ where
  carrier := {q | ∃ k : ℕ, ∃ z : ℤ, (n : ℚ) ^ k * q = z}
  add_mem' := by
    rintro q r ⟨k, z, hz⟩ ⟨l, w, hw⟩
    use k + l, z * n ^ l + w * n ^ k
    push_cast
    rw [← hz, ← hw]
    ring
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro q ⟨k, z, hz⟩
    use k, -z
    push_cast
    rw [← hz]
    ring

variable {n : ℕ}

lemma mem_powDenominators_of_mul_mem {d : ℕ} (hdn : d ∣ n) {q : ℚ}
    (hq : (d : ℚ) * q ∈ powDenominators n) : q ∈ powDenominators n := by
  obtain ⟨k, z, hz⟩ := hq
  obtain ⟨e, rfl⟩ := hdn
  use k + 1, z * e
  push_cast at hz ⊢
  rw [← hz]
  ring

lemma neg_one_mem_powDenominators : (-1 : ℚ) ∈ powDenominators n := ⟨0, -1, by simp⟩

lemma mul_ne_neg_one_of_mem_powDenominators {p : ℕ} (hp : p.Prime) (hpn : ¬p ∣ n) {q : ℚ}
    (hq : q ∈ powDenominators n) : (p : ℚ) * q ≠ -1 := by
  obtain ⟨k, z, hz⟩ := hq
  intro h
  have : ((n ^ k : ℕ) : ℤ) = p * -z := by
    have : ((n ^ k : ℕ) : ℚ) = ((p * -z : ℤ) : ℚ) := by
      push_cast
      rw [← hz]
      calc (n : ℚ) ^ k = -((n : ℚ) ^ k * -1) := by ring
        _ = -((n : ℚ) ^ k * (p * q)) := by rw [h]
        _ = p * -((n : ℚ) ^ k * q) := by ring
    exact_mod_cast this
  have : p ∣ n ^ k := Int.natCast_dvd_natCast.mp ⟨-z, this⟩
  exact hpn ((Nat.prime_iff.mp hp).dvd_of_dvd_pow this)

end AddSubgroup
