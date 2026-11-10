module

public import Mathlib.NumberTheory.Bertrand
public import AlphaCentauri.NumberTheory.Primes
public import AlphaCentauri.NumberTheory.Bertrand.Embedding
public import AlphaCentauri.NumberTheory.Bertrand.Sizes

/-!
# Bertrand's postulate over $\mathsf{I}\Delta_0 + \Omega_1$

If there is no prime in $(n, 2n]$, the positions of the prime-power decompositions of
$1, \dots, 2n$ and of the Chebyshev bands $\binom{2M_r}{M_r}$, $M_r \approx n / (3 \cdot 2^r)$,
assemble into a $\Delta_0$-definable injection of $z + a$ into $z + b$ numbers with
$a \approx 2ns$ and $b \approx \frac43 ns$: Erdős's estimates $\log_2 \binom{2n}{n} \approx 2n$
and $\log_2 \binom{2n}{n} \lesssim \frac43 n$ become maps of positions, and the common part `z`,
of size about $ns\|n\|^2$, is carried along. The weak pigeonhole principle with ratio
$(K + 1) / K$ for $K \approx 16\|n\|^2$ excludes it.

- [HP98, §V.5(f)]
- [PWW88, remark before Theorem 12]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁]

namespace Bertrand

variable {B s : V}

variable (n : V)

/-- The positions $(k, y)$ of a copy `c` of $\mathrm{Bits}(n)$ or of $\mathrm{Bits}(M_r)$, carried
along by the injection, are numbered in blocks of $n \Lambda$. -/
def CarryEncode (u v : V) : Prop :=
  (∃ c ≤ u, ∃ k ≤ u, ∃ y ≤ u, c ≤ 1 ∧ u = ⟪0, c, k, y⟫ ∧
      v = c * (n * blockWidth n) + (k - 1) * blockWidth n + y) ∨
    (∃ r ≤ u, ∃ c ≤ u, ∃ k ≤ u, ∃ y ≤ u, c ≤ 1 ∧ u = ⟪1, r, c, k, y⟫ ∧
      v = (2 + 2 * r + c) * (n * blockWidth n) + (k - 1) * blockWidth n + y)

/-- The encoding of the domain in $[0, z + a)$. -/
def DomainEncode (u v : V) : Prop :=
  CarryEncode n u v ∨ ∃ y ≤ u, u = ⟪0, 2, y⟫ ∧ v = lowerSize n + y

/-- The index of an element of the $r$-th band in $[0, 2 M_r w)$. -/
def BandIndex (r x q : V) : Prop :=
  (∃ y ≤ x, x = ⟪3, y⟫ ∧ q = y) ∨
    (∃ c ≤ x, ∃ k ≤ x, ∃ i ≤ x, 4 ≤ c ∧ c ≤ 5 ∧ x = ⟪c, k, i⟫ ∧
      q = 2 * bandBound n r * exponent n + (c - 4) * (bandBound n r * (‖n‖ + 1)) +
        (k - 1) * (‖n‖ + 1) + i)

/-- The position of the `q`-th element of the $r$-th band: the first $2 u_{r + 1} w$ elements
go to $[w(2x - 2u_r), w(2x - u_r))$, and the remaining $2w$ to the end. -/
def BandPosition (r q v : V) : Prop :=
  (q < 2 * bandSize n (r + 1) * bandUnit n ∧
      v = bandUnit n * (2 * cutoff n - 2 * bandSize n r) + q) ∨
    (2 * bandSize n (r + 1) * bandUnit n ≤ q ∧
      v = 2 * cutoff n * bandUnit n + 2 * r * bandUnit n +
        (q - 2 * bandSize n (r + 1) * bandUnit n))

/-- The offset of the Chebyshev bands. -/
def bandOffset : V :=
  lowerSize n + blockWidth n + 2 * n * (‖n‖ + 1) + ((√(2 * n) : V) + 1) * blockWidth n

/-- The encoding of the codomain in $[0, z + b)$. -/
def CodomainEncode (u v : V) : Prop :=
  CarryEncode n u v ∨
    (∃ y ≤ u, u = ⟪0, 4, y⟫ ∧ v = lowerSize n + y) ∨
    (∃ k ≤ u, ∃ i ≤ u, u = ⟪0, 3, k, i⟫ ∧
      v = lowerSize n + blockWidth n + (k - 1) * (‖n‖ + 1) + i) ∨
    (∃ p ≤ u, ∃ o ≤ u, u = ⟪0, 5, p, o⟫ ∧
      v = lowerSize n + blockWidth n + 2 * n * (‖n‖ + 1) + p * blockWidth n + o) ∨
    (∃ r ≤ u, ∃ x ≤ u, ∃ q ≤ v, ∃ w ≤ v, u = ⟪1, r, x⟫ ∧ BandIndex n r x q ∧
      BandPosition n r q w ∧ v = bandOffset n + w)

lemma definable_carryEncode : 𝚺ᴬ₀.DefinableRel (CarryEncode n) := by
  unfold CarryEncode
  definability

lemma definable_domainEncode : 𝚺ᴬ₀.DefinableRel (DomainEncode n) := by
  have := definable_carryEncode n
  unfold DomainEncode
  definability

lemma definable_bandIndex : 𝚺ᴬ₀.DefinableRel₃ (BandIndex n) := by
  unfold BandIndex bandBound bandSize
  definability

lemma definable_bandPosition : 𝚺ᴬ₀.DefinableRel₃ (BandPosition n) := by
  unfold BandPosition bandSize
  definability

lemma definable_codomainEncode : 𝚺ᴬ₀.DefinableRel (CodomainEncode n) := by
  have := definable_carryEncode n
  have := definable_bandIndex n
  have := definable_bandPosition n
  unfold CodomainEncode
  definability

variable {n}

lemma two_le_of_length_ge {n : V} (hℓ : (1024 : V) ≤ ‖n‖) : 2 ≤ n := by
  by_contra h
  have h₁ : n < 1 + 1 := by rwa [one_add_one_eq_two, ← not_le]
  have h₂ : ‖n‖ ≤ 1 := by simpa using length_monotone (lt_succ_iff_le.mp h₁)
  exact absurd (by exact_mod_cast hℓ.trans h₂ : (1024 : ℕ) ≤ 1) (by decide)

lemma eq_of_mul_add_eq {a a' x x' m : V} (hx : x < m) (hx' : x' < m)
    (h : a * m + x = a' * m + x') : a = a' ∧ x = x' := by
  have h₁ : a = a' := calc
    a = (a * m + x) / m := (div_mul_add a m hx).symm
    _ = (a' * m + x') / m := by rw [h]
    _ = a' := div_mul_add a' m hx'
  subst h₁
  exact ⟨rfl, add_left_cancel h⟩

lemma eq_of_sub_one_eq {k k' : V} (hk : 0 < k) (hk' : 0 < k') (h : k - 1 = k' - 1) : k = k' :=
  calc k = k - 1 + 1 := (tsub_add_cancel_of_le (pos_iff_one_le.mp hk)).symm
    _ = k' - 1 + 1 := by rw [h]
    _ = k' := tsub_add_cancel_of_le (pos_iff_one_le.mp hk')

lemma mul_add_lt_mul {j y m n : V} (hj : 0 < j) (hjn : j ≤ n) (hy : y < m) :
    (j - 1) * m + y < n * m :=
  calc (j - 1) * m + y < (j - 1) * m + m := (add_lt_add_iff_left _).mpr hy
    _ = (j - 1 + 1) * m := by rw [add_mul, one_mul]
    _ = j * m := by rw [tsub_add_cancel_of_le (pos_iff_one_le.mp hj)]
    _ ≤ n * m := mul_le_mul_right hjn

lemma scaledLength_lt_blockWidth {y : V} (hn : 0 < n) (hy : 0 < y) (hyn : y ≤ 2 * n) :
    scaledLength (powerBound n) (exponent n) y < blockWidth n := by
  have h₁ : exponent n * ‖y‖ < ‖powerBound n‖ :=
    lt_of_le_of_lt (mul_le_mul_left (length_monotone (hyn.trans (by simp))))
      exponent_mul_length_lt
  calc scaledLength (powerBound n) (exponent n) y ≤ exponent n * ‖y‖ :=
        scaledLength_le (smash_pos _ _) hy h₁
    _ ≤ exponent n * (‖n‖ + 1) :=
        mul_le_mul_left ((length_monotone hyn).trans (length_two_mul_of_pos hn).le)
    _ < blockWidth n := lt_add_one _

lemma carry_core_inj {j j' k k' y y' : V} (hk : 0 < k) (hk' : 0 < k') (hkn : k ≤ n)
    (hkn' : k' ≤ n) (hy : y < blockWidth n) (hy' : y' < blockWidth n)
    (h : j * (n * blockWidth n) + (k - 1) * blockWidth n + y =
      j' * (n * blockWidth n) + (k' - 1) * blockWidth n + y') :
    j = j' ∧ k = k' ∧ y = y' := by
  obtain ⟨rfl, h₁⟩ := eq_of_mul_add_eq (mul_add_lt_mul hk hkn hy) (mul_add_lt_mul hk' hkn' hy')
    (by simpa only [add_assoc] using h)
  obtain ⟨h₂, rfl⟩ := eq_of_mul_add_eq hy hy' h₁
  exact ⟨rfl, eq_of_sub_one_eq hk hk' h₂, rfl⟩

lemma domain_zero_iff {c w : V} :
    Domain B s n ⟪0, c, w⟫ ↔ (c = 0 ∧ Bits B s n w) ∨ (c = 1 ∧ Bits B s n w) ∨
      (c = 2 ∧ Below ((2 * n - 1) * s) w) := by
  simp [Domain, LowerDomain, tagged_pair_iff, family_pair_iff]

lemma domain_one_iff {r c w : V} :
    Domain B s n ⟪1, r, c, w⟫ ↔ r < bandCount n ∧
      ((c = 0 ∧ Bits B s (bandBound n r) w) ∨ (c = 1 ∧ Bits B s (bandBound n r) w)) := by
  simp [Domain, BandCarry, tagged_pair_iff, family_pair_iff]

lemma codomain_zero_iff {c w : V} :
    Codomain B s n ⟪0, c, w⟫ ↔ ((c = 0 ∧ Bits B s n w) ∨ (c = 1 ∧ Bits B s n w)) ∨
      (c = 3 ∧ Top (2 * n) w) ∨ (c = 4 ∧ Below (scaledLength B s n) w) ∨
        (c = 5 ∧ Small B s n w) := by
  simp [Codomain, LowerResidue, tagged_pair_iff, family_pair_iff]

lemma codomain_one_iff {r c w : V} :
    Codomain B s n ⟪1, r, c, w⟫ ↔ r < bandCount n ∧
      (((c = 0 ∧ Bits B s (bandBound n r) w) ∨ (c = 1 ∧ Bits B s (bandBound n r) w) ∨
        (c = 3 ∧ Below (2 * bandBound n r * s) w)) ∨
        ((c = 4 ∧ Top (bandBound n r) w) ∨ (c = 5 ∧ Top (bandBound n r) w))) := by
  simp [Codomain, BandCodomain, tagged_pair_iff, family_pair_iff]

lemma bandIndex_cases {r x q : V} (hx : BandCodomain B (exponent n) (bandBound n r) x)
    (hq : BandIndex n r x q) :
    (∃ y, x = ⟪3, y⟫ ∧ y < 2 * bandBound n r * exponent n ∧ q = y) ∨
      ∃ c k i, (c = 4 ∨ c = 5) ∧ x = ⟪c, k, i⟫ ∧ 0 < k ∧ k ≤ bandBound n r ∧ i < ‖k‖ ∧
        q = 2 * bandBound n r * exponent n + (c - 4) * (bandBound n r * (‖n‖ + 1)) +
          (k - 1) * (‖n‖ + 1) + i := by
  rcases hq with ⟨y, -, rfl, hqy⟩ | ⟨c, -, k, -, i, -, h4, h5, rfl, hqc⟩
  · left
    rcases hx with (h | h | h) | h | h
    · exact absurd (tagged_pair_iff.mp h).1 (by norm_num)
    · exact absurd (tagged_pair_iff.mp h).1 (by norm_num)
    · use y
      exact ⟨rfl, (tagged_pair_iff.mp h).2, hqy⟩
    · exact absurd (tagged_pair_iff.mp h).1 (by norm_num)
    · exact absurd (tagged_pair_iff.mp h).1 (by norm_num)
  · right
    rcases hx with (h | h | h) | h | h
    · exact absurd (h4.trans_eq (tagged_pair_iff.mp h).1) (by norm_num)
    · exact absurd (h4.trans_eq (tagged_pair_iff.mp h).1) (by norm_num)
    · exact absurd (h4.trans_eq (tagged_pair_iff.mp h).1) (by norm_num)
    · obtain ⟨hc, ht⟩ := tagged_pair_iff.mp h
      obtain ⟨hk0, hkM, hi⟩ := top_pair_iff.mp ht
      use c, k, i
      exact ⟨Or.inl hc, rfl, hk0, hkM, hi, hqc⟩
    · obtain ⟨hc, ht⟩ := tagged_pair_iff.mp h
      obtain ⟨hk0, hkM, hi⟩ := top_pair_iff.mp ht
      use c, k, i
      exact ⟨Or.inr hc, rfl, hk0, hkM, hi, hqc⟩

lemma four_le_of_cases {c : V} (h : c = 4 ∨ c = 5) : 4 ≤ c := by
  rcases h with rfl | rfl
  · exact le_rfl
  · norm_num

lemma sub_four_cases {c : V} (h : c = 4 ∨ c = 5) : c - 4 = 0 ∨ c - 4 = 1 := by
  rcases h with rfl | rfl
  · exact Or.inl (tsub_self _)
  · exact Or.inr (tsub_eq_of_eq_add (by norm_num))

lemma eq_of_sub_four_eq {c c' : V} (h : c = 4 ∨ c = 5) (h' : c' = 4 ∨ c' = 5)
    (e : c - 4 = c' - 4) : c = c' :=
  calc c = c - 4 + 4 := (tsub_add_cancel_of_le (four_le_of_cases h)).symm
    _ = c' - 4 + 4 := by rw [e]
    _ = c' := tsub_add_cancel_of_le (four_le_of_cases h')

lemma bandIndex_spec {r x q : V} (hr : bandBound n r ≤ n)
    (hx : BandCodomain B (exponent n) (bandBound n r) x) (hq : BandIndex n r x q) :
    q < 2 * bandBound n r * bandUnit n ∧
      ∀ x', BandCodomain B (exponent n) (bandBound n r) x' → BandIndex n r x' q → x' = x := by
  have hi_lt : ∀ {k i : V}, k ≤ bandBound n r → i < ‖k‖ → i < ‖n‖ + 1 := fun hk hi ↦
    hi.trans_le ((length_monotone (hk.trans hr)).trans le_self_add)
  have hrem : ∀ {k i : V}, 0 < k → k ≤ bandBound n r → i < ‖k‖ →
      (k - 1) * (‖n‖ + 1) + i < bandBound n r * (‖n‖ + 1) := fun hk0 hkM hi ↦
    mul_add_lt_mul hk0 hkM (hi_lt hkM hi)
  have hge : ∀ {A B' C i q' : V}, q' = A + B' + C + i → A ≤ q' := by
    intro A B' C i q' h
    rw [h]
    exact le_self_add.trans (le_self_add.trans le_self_add)
  refine ⟨?_, fun x' hx' hq' ↦ ?_⟩
  · rcases bandIndex_cases hx hq with ⟨y, rfl, hy, hqy⟩ | ⟨c, k, i, hc, rfl, hk0, hkM, hi, hqc⟩
    · rw [hqy]
      calc y < 2 * bandBound n r * exponent n := hy
        _ ≤ 2 * bandBound n r * bandUnit n := mul_le_mul_left (le_self_add.trans le_self_add)
    · have h₁ : (c - 4) * (bandBound n r * (‖n‖ + 1)) + ((k - 1) * (‖n‖ + 1) + i) <
          2 * (bandBound n r * (‖n‖ + 1)) := by
        rcases sub_four_cases hc with h | h <;> rw [h]
        · rw [zero_mul, zero_add]
          exact (hrem hk0 hkM hi).trans_le (le_mul_of_one_le_left (Arithmetic.zero_le _) one_le_two)
        · rw [one_mul, two_mul]
          exact (add_lt_add_iff_left _).mpr (hrem hk0 hkM hi)
      rw [hqc]
      calc _ = 2 * bandBound n r * exponent n +
            ((c - 4) * (bandBound n r * (‖n‖ + 1)) + ((k - 1) * (‖n‖ + 1) + i)) := by
            simp only [add_assoc]
        _ < 2 * bandBound n r * exponent n + 2 * (bandBound n r * (‖n‖ + 1)) :=
            (add_lt_add_iff_left _).mpr h₁
        _ = 2 * bandBound n r * bandUnit n := by unfold bandUnit; grind
  · rcases bandIndex_cases hx hq with ⟨y, rfl, hy, hqy⟩ | ⟨c, k, i, hc, rfl, hk0, hkM, hi, hqc⟩ <;>
      rcases bandIndex_cases hx' hq' with ⟨y', rfl, hy', hqy'⟩ |
        ⟨c', k', i', hc', rfl, hk0', hkM', hi', hqc'⟩
    · rw [← hqy', hqy]
    · exact absurd (hqy ▸ hy) (not_lt.mpr (hge hqc'))
    · exact absurd (hqy' ▸ hy') (not_lt.mpr (hge hqc))
    · have h₁ : (c - 4) * (bandBound n r * (‖n‖ + 1)) + ((k - 1) * (‖n‖ + 1) + i) =
          (c' - 4) * (bandBound n r * (‖n‖ + 1)) + ((k' - 1) * (‖n‖ + 1) + i') := by
        apply add_left_cancel (a := 2 * bandBound n r * exponent n)
        simpa only [add_assoc] using hqc.symm.trans hqc'
      obtain ⟨h₂, h₃⟩ := eq_of_mul_add_eq (hrem hk0 hkM hi) (hrem hk0' hkM' hi') h₁
      obtain ⟨h₄, rfl⟩ := eq_of_mul_add_eq (hi_lt hkM hi) (hi_lt hkM' hi') h₃
      rw [eq_of_sub_four_eq hc hc' h₂, eq_of_sub_one_eq hk0 hk0' h₄]

section band

variable {r r' q q' w : V}

lemma bandPosition_exists (r q : V) : ∃ w, BandPosition n r q w := by
  rcases lt_or_ge q (2 * bandSize n (r + 1) * bandUnit n) with h | h
  · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨_, Or.inr ⟨h, rfl⟩⟩

lemma bandSize_le_cutoff (hr : r ≤ bandCount n) : bandSize n r ≤ cutoff n :=
  bandSize_zero (n := n) ▸ bandSize_antitone (Arithmetic.zero_le r) hr

lemma bandStart_add (hr : r ≤ bandCount n) :
    bandUnit n * (2 * cutoff n - 2 * bandSize n r) + 2 * bandSize n r * bandUnit n =
      2 * cutoff n * bandUnit n := by
  have h : 2 * bandSize n r ≤ 2 * cutoff n := mul_le_mul_left (bandSize_le_cutoff hr)
  calc _ = bandUnit n * (2 * cutoff n - 2 * bandSize n r + 2 * bandSize n r) := by grind
    _ = _ := by rw [tsub_add_cancel_of_le h, mul_comm]

lemma le_of_add_eq_of_add_eq {A A' X X' Y T : V} (h : A + X = T) (h' : A' + Y = T)
    (hX : X' + Y ≤ X) : A + X' ≤ A' := by
  apply (add_le_add_iff_right Y).mp
  calc A + X' + Y = A + (X' + Y) := add_assoc _ _ _
    _ ≤ A + X := add_le_add le_rfl hX
    _ = A' + Y := h.trans h'.symm

lemma bandKind1_lt_end (hr : r < bandCount n) (hq : q < 2 * bandSize n (r + 1) * bandUnit n) :
    bandUnit n * (2 * cutoff n - 2 * bandSize n r) + q < 2 * cutoff n * bandUnit n := by
  rw [← bandStart_add hr.le]
  apply (add_lt_add_iff_left _).mpr
  exact hq.trans_le (mul_le_mul_right (mul_le_mul_left
    (bandSize_antitone le_self_add (succ_le_iff_lt.mpr hr))))

lemma bandKind1_lt (hrr : r < r') (hr' : r' ≤ bandCount n)
    (hq : q < 2 * bandSize n (r + 1) * bandUnit n) :
    bandUnit n * (2 * cutoff n - 2 * bandSize n r) + q <
      bandUnit n * (2 * cutoff n - 2 * bandSize n r') := by
  have hs := (bandSize_succ (hrr.trans_le hr')).1
  have hc : bandSize n r' ≤ bandSize n (r + 1) := bandSize_antitone (succ_le_iff_lt.mpr hrr) hr'
  have h₁ : 2 * bandSize n (r + 1) * bandUnit n + 2 * bandSize n r' * bandUnit n ≤
      2 * bandSize n r * bandUnit n := by
    calc _ = (2 * (bandSize n (r + 1) + bandSize n r')) * bandUnit n := by grind
      _ ≤ (2 * bandSize n r) * bandUnit n := by
        apply mul_le_mul_right
        calc 2 * (bandSize n (r + 1) + bandSize n r') ≤ 2 * (bandSize n (r + 1) +
            bandSize n (r + 1)) := mul_le_mul_left (add_le_add le_rfl hc)
          _ = 2 * (2 * bandSize n (r + 1)) := by grind
          _ ≤ _ := mul_le_mul_left hs
  calc _ < bandUnit n * (2 * cutoff n - 2 * bandSize n r) + 2 * bandSize n (r + 1) * bandUnit n :=
        (add_lt_add_iff_left _).mpr hq
    _ ≤ _ := le_of_add_eq_of_add_eq (bandStart_add (hrr.le.trans hr'))
        (bandStart_add hr') h₁

lemma bandKind2_sub_lt (hq : q < 2 * bandBound n r * bandUnit n)
    (h : 2 * bandSize n (r + 1) * bandUnit n ≤ q) :
    q - 2 * bandSize n (r + 1) * bandUnit n < 2 * bandUnit n := by
  apply (tsub_lt_iff_left h).mpr
  calc q < 2 * bandBound n r * bandUnit n := hq
    _ = 2 * bandSize n (r + 1) * bandUnit n + 2 * bandUnit n := by unfold bandBound; grind

lemma bandKind2_lt {d : V} (hrr : r < r') (hd : d < 2 * bandUnit n) :
    2 * cutoff n * bandUnit n + 2 * r * bandUnit n + d <
      2 * cutoff n * bandUnit n + 2 * r' * bandUnit n :=
  calc _ < 2 * cutoff n * bandUnit n + 2 * r * bandUnit n + 2 * bandUnit n :=
        (add_lt_add_iff_left _).mpr hd
    _ = 2 * cutoff n * bandUnit n + 2 * (r + 1) * bandUnit n := by grind
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_right (mul_le_mul_left (succ_le_iff_lt.mpr hrr)))

lemma bandPosition_spec (hr : r < bandCount n) (hq : q < 2 * bandBound n r * bandUnit n)
    (h : BandPosition n r q w) :
    q ≤ w ∧ w < 2 * cutoff n * bandUnit n + 2 * bandCount n * bandUnit n := by
  rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact ⟨le_add_self, (bandKind1_lt_end hr h).trans_le le_self_add⟩
  · have hu : bandSize n (r + 1) ≤ cutoff n := bandSize_le_cutoff (succ_le_iff_lt.mpr hr)
    constructor
    · calc q = 2 * bandSize n (r + 1) * bandUnit n + (q - 2 * bandSize n (r + 1) * bandUnit n) :=
            (add_tsub_cancel_of_le h).symm
        _ ≤ 2 * cutoff n * bandUnit n + (q - 2 * bandSize n (r + 1) * bandUnit n) :=
            add_le_add (mul_le_mul_right (mul_le_mul_left hu)) le_rfl
        _ ≤ _ := add_le_add le_self_add le_rfl
    · exact bandKind2_lt hr (bandKind2_sub_lt hq h)

lemma bandPosition_false_of_lt (hrr : r < r') (hr' : r' < bandCount n)
    (hq : q < 2 * bandBound n r * bandUnit n) (h : BandPosition n r q w)
    (h' : BandPosition n r' q' w) : False := by
  rcases h with ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩ <;> rcases h' with ⟨h₂, h₂'⟩ | ⟨h₂, h₂'⟩
  · exact absurd h₂' (ne_of_lt ((bandKind1_lt hrr hr'.le h₁).trans_le le_self_add))
  · exact absurd h₂' (ne_of_lt ((bandKind1_lt_end (hrr.trans hr') h₁).trans_le
      (le_self_add.trans le_self_add)))
  · exact absurd h₂'.symm (ne_of_lt ((bandKind1_lt_end hr' h₂).trans_le
      (le_self_add.trans le_self_add)))
  · exact absurd h₂' (ne_of_lt ((bandKind2_lt hrr (bandKind2_sub_lt hq h₁)).trans_le le_self_add))

lemma bandPosition_inj (hr : r < bandCount n) (hr' : r' < bandCount n)
    (hq : q < 2 * bandBound n r * bandUnit n) (hq' : q' < 2 * bandBound n r' * bandUnit n)
    (h : BandPosition n r q w) (h' : BandPosition n r' q' w) : r = r' ∧ q = q' := by
  rcases lt_trichotomy r r' with hrr | rfl | hrr
  · exact (bandPosition_false_of_lt hrr hr' hq h h').elim
  · refine ⟨rfl, ?_⟩
    rcases h with ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩ <;> rcases h' with ⟨h₂, h₂'⟩ | ⟨h₂, h₂'⟩
    · exact add_left_cancel h₂'
    · exact absurd h₂' (ne_of_lt ((bandKind1_lt_end hr h₁).trans_le
        (le_self_add.trans le_self_add)))
    · exact absurd h₂'.symm (ne_of_lt ((bandKind1_lt_end hr h₂).trans_le
        (le_self_add.trans le_self_add)))
    · have := add_left_cancel (a := 2 * cutoff n * bandUnit n + 2 * r * bandUnit n)
        (by simpa only [add_assoc] using h₂'.symm)
      calc q = 2 * bandSize n (r + 1) * bandUnit n + (q - 2 * bandSize n (r + 1) * bandUnit n) :=
            (add_tsub_cancel_of_le h₁).symm
        _ = 2 * bandSize n (r + 1) * bandUnit n + (q' - 2 * bandSize n (r + 1) * bandUnit n) := by
            rw [this]
        _ = q' := add_tsub_cancel_of_le h₂
  · exact (bandPosition_false_of_lt hrr hr hq' h' h).elim

end band

attribute [local simp] le_pair_of_le_right

lemma bits_of_codomain_zero {c k y : V} (h : Codomain B s n ⟪0, c, k, y⟫) (hc : c ≤ 1) :
    Bits B s n ⟪k, y⟫ := by
  rcases codomain_zero_iff.mp h with (⟨-, hb⟩ | ⟨-, hb⟩) | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    first | assumption | exact absurd hc (by norm_num)

lemma bits_of_codomain_one {r c k y : V} (h : Codomain B s n ⟪1, r, c, k, y⟫) (hc : c ≤ 1) :
    r < bandCount n ∧ Bits B s (bandBound n r) ⟪k, y⟫ := by
  obtain ⟨hr, h⟩ := codomain_one_iff.mp h
  refine ⟨hr, ?_⟩
  rcases h with (⟨-, hb⟩ | ⟨-, hb⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    first | assumption | exact absurd hc (by norm_num)

lemma domain_of_bits_zero {c k y : V} (hb : Bits B s n ⟪k, y⟫) (hc : c ≤ 1) :
    Domain B s n ⟪0, c, k, y⟫ := by
  rcases le_one_iff_eq_zero_or_one.mp hc with rfl | rfl
  · exact domain_zero_iff.mpr (Or.inl ⟨rfl, hb⟩)
  · exact domain_zero_iff.mpr (Or.inr (Or.inl ⟨rfl, hb⟩))

lemma domain_of_bits_one {r c k y : V} (hr : r < bandCount n)
    (hb : Bits B s (bandBound n r) ⟪k, y⟫) (hc : c ≤ 1) : Domain B s n ⟪1, r, c, k, y⟫ := by
  refine domain_one_iff.mpr ⟨hr, ?_⟩
  rcases le_one_iff_eq_zero_or_one.mp hc with rfl | rfl
  · exact Or.inl ⟨rfl, hb⟩
  · exact Or.inr ⟨rfl, hb⟩

lemma codomain_band_iff {r x : V} :
    Codomain B s n ⟪1, r, x⟫ ↔ r < bandCount n ∧ BandCodomain B s (bandBound n r) x := by
  simp [Codomain, tagged_pair_iff, family_pair_iff]

lemma below_of_codomain_four {y : V} (h : Codomain B s n ⟪0, 4, y⟫) :
    y < scaledLength B s n := by
  rcases codomain_zero_iff.mp h with (⟨h0, -⟩ | ⟨h0, -⟩) | ⟨h0, -⟩ | ⟨-, hb⟩ | ⟨h0, -⟩ <;>
    first | assumption | exact absurd h0 (by norm_num)

lemma top_of_codomain_three {w : V} (h : Codomain B s n ⟪0, 3, w⟫) : Top (2 * n) w := by
  rcases codomain_zero_iff.mp h with (⟨h0, -⟩ | ⟨h0, -⟩) | ⟨-, hb⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ <;>
    first | assumption | exact absurd h0 (by norm_num)

lemma small_of_codomain_five {w : V} (h : Codomain B s n ⟪0, 5, w⟫) : Small B s n w := by
  rcases codomain_zero_iff.mp h with (⟨h0, -⟩ | ⟨h0, -⟩) | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, hb⟩ <;>
    first | assumption | exact absurd h0 (by norm_num)

lemma lowerSize_eq : lowerSize n = (2 * bandCount n + 2) * (n * blockWidth n) := by
  unfold lowerSize
  rw [mul_assoc]

lemma code_lt_lowerSize {j rem : V} (hrem : rem < n * blockWidth n)
    (hj : j + 1 ≤ 2 * bandCount n + 2) : j * (n * blockWidth n) + rem < lowerSize n :=
  calc j * (n * blockWidth n) + rem < j * (n * blockWidth n) + n * blockWidth n :=
        (add_lt_add_iff_left _).mpr hrem
    _ = (j + 1) * (n * blockWidth n) := by rw [add_mul, one_mul]
    _ ≤ (2 * bandCount n + 2) * (n * blockWidth n) := mul_le_mul_right hj
    _ = lowerSize n := lowerSize_eq.symm

lemma small_pair_iff {p o : V} :
    Small B s n ⟪p, o⟫ ↔ IsPrime p ∧ p * p ≤ 2 * n ∧ o < scaledLength B s p := by
  constructor
  · rintro ⟨p', -, o', -, h, hh⟩
    obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h
    exact hh
  · intro h
    exact ⟨p, le_pair_left _ _, o, le_pair_right _ _, rfl, h⟩

lemma le_sqrt_of_mul_self_le {p a : V} (h : p * p ≤ a) : p ≤ √a := by
  by_contra hlt
  have h₁ : √a + 1 ≤ p := succ_le_iff_lt.mpr (not_le.mp hlt)
  exact lt_irrefl a <| calc
    a < (√a + 1) * (√a + 1) := sqrt_spec_lt a
    _ ≤ p * p := mul_self_le_mul_self (Arithmetic.zero_le _) h₁
    _ ≤ a := h

lemma targetExcess_eq : lowerSize n + targetExcess n =
    bandOffset n + 2 * cutoff n * bandUnit n + 2 * bandCount n * bandUnit n := by
  unfold targetExcess bandOffset
  grind

section encoding

variable (hn2 : 2 ≤ n)
include hn2

lemma carryEncode_cases {t v : V} (ht : Codomain (powerBound n) (exponent n) n t)
    (h : CarryEncode n t v) :
    (∃ c k y, c ≤ 1 ∧ 0 < k ∧ k ≤ n ∧ y < blockWidth n ∧ t = ⟪0, c, k, y⟫ ∧
      v = c * (n * blockWidth n) + (k - 1) * blockWidth n + y) ∨
    (∃ r c k y, c ≤ 1 ∧ r < bandCount n ∧ 0 < k ∧ k ≤ n ∧ y < blockWidth n ∧
      t = ⟪1, r, c, k, y⟫ ∧
      v = (2 + 2 * r + c) * (n * blockWidth n) + (k - 1) * blockWidth n + y) := by
  have hn0 : 0 < n := lt_of_lt_of_le two_pos hn2
  rcases h with ⟨c, -, k, -, y, -, hc, rfl, rfl⟩ | ⟨r, -, c, -, k, -, y, -, hc, rfl, rfl⟩
  · obtain ⟨hk0, hkn, hy⟩ := bits_pair_iff.mp (bits_of_codomain_zero ht hc)
    exact Or.inl ⟨c, k, y, hc, hk0, hkn,
      hy.trans (scaledLength_lt_blockWidth hn0 hk0 (hkn.trans (by simp))), rfl, rfl⟩
  · obtain ⟨hr, hb⟩ := bits_of_codomain_one ht hc
    obtain ⟨hk0, hkM, hy⟩ := bits_pair_iff.mp hb
    have hkn : k ≤ n := hkM.trans (bandBound_le hr hn2)
    exact Or.inr ⟨r, c, k, y, hc, hr, hk0, hkn,
      hy.trans (scaledLength_lt_blockWidth hn0 hk0 (hkn.trans (by simp))), rfl, rfl⟩

lemma carryEncode_lt {t v : V} (ht : Codomain (powerBound n) (exponent n) n t)
    (h : CarryEncode n t v) : v < lowerSize n := by
  have hc2 : ∀ {c : V}, c ≤ 1 → c + 1 ≤ 2 := fun hc ↦
    (add_le_add hc le_rfl).trans_eq one_add_one_eq_two
  rcases carryEncode_cases hn2 ht h with
    ⟨c, k, y, hc, hk0, hkn, hy, rfl, rfl⟩ | ⟨r, c, k, y, hc, hr, hk0, hkn, hy, rfl, rfl⟩
  · rw [add_assoc]
    exact code_lt_lowerSize (mul_add_lt_mul hk0 hkn hy) ((hc2 hc).trans le_add_self)
  · rw [add_assoc]
    apply code_lt_lowerSize (mul_add_lt_mul hk0 hkn hy)
    calc 2 + 2 * r + c + 1 = 2 + 2 * r + (c + 1) := add_assoc _ _ _
      _ ≤ 2 + 2 * r + 2 := add_le_add le_rfl (hc2 hc)
      _ = 2 * (r + 1) + 2 := by grind
      _ ≤ 2 * bandCount n + 2 := add_le_add (mul_le_mul_left (succ_le_iff_lt.mpr hr)) le_rfl

lemma carryEncode_inj {t t' v : V} (ht : Codomain (powerBound n) (exponent n) n t)
    (ht' : Codomain (powerBound n) (exponent n) n t') (h : CarryEncode n t v)
    (h' : CarryEncode n t' v) : t = t' := by
  rcases carryEncode_cases hn2 ht h with
      ⟨c, k, y, hc, hk0, hkn, hy, rfl, hv⟩ | ⟨r, c, k, y, hc, hr, hk0, hkn, hy, rfl, hv⟩ <;>
    rcases carryEncode_cases hn2 ht' h' with
      ⟨c', k', y', hc', hk0', hkn', hy', rfl, hv'⟩ |
        ⟨r', c', k', y', hc', hr', hk0', hkn', hy', rfl, hv'⟩
  · obtain ⟨rfl, rfl, rfl⟩ := carry_core_inj hk0 hk0' hkn hkn' hy hy' (hv.symm.trans hv')
    rfl
  · obtain ⟨hj, -, -⟩ := carry_core_inj hk0 hk0' hkn hkn' hy hy' (hv.symm.trans hv')
    exact absurd (((le_self_add.trans le_self_add).trans_eq hj.symm).trans hc) (by norm_num)
  · obtain ⟨hj, -, -⟩ := carry_core_inj hk0 hk0' hkn hkn' hy hy' (hv.symm.trans hv')
    exact absurd (((le_self_add.trans le_self_add).trans_eq hj).trans hc') (by norm_num)
  · obtain ⟨hj, rfl, rfl⟩ := carry_core_inj hk0 hk0' hkn hkn' hy hy' (hv.symm.trans hv')
    have h₂ : r * 2 + c = r' * 2 + c' := by
      rw [mul_comm r 2, mul_comm r' 2]
      apply add_left_cancel (a := 2)
      simpa only [add_assoc] using hj
    obtain ⟨rfl, rfl⟩ := eq_of_mul_add_eq (lt_two_iff_le_one.mpr hc) (lt_two_iff_le_one.mpr hc') h₂
    rfl

lemma codomainEncode_cases {t v : V} (ht : Codomain (powerBound n) (exponent n) n t)
    (h : CodomainEncode n t v) :
    (CarryEncode n t v ∧ v < lowerSize n) ∨
    (∃ y, t = ⟪0, 4, y⟫ ∧ y < blockWidth n ∧ v = lowerSize n + y ∧
      lowerSize n ≤ v ∧ v < lowerSize n + blockWidth n) ∨
    (∃ k i, t = ⟪0, 3, k, i⟫ ∧ 0 < k ∧ i < ‖n‖ + 1 ∧
      v = lowerSize n + blockWidth n + (k - 1) * (‖n‖ + 1) + i ∧
      lowerSize n + blockWidth n ≤ v ∧
      v < lowerSize n + blockWidth n + 2 * n * (‖n‖ + 1)) ∨
    (∃ p o, t = ⟪0, 5, p, o⟫ ∧ o < blockWidth n ∧
      v = lowerSize n + blockWidth n + 2 * n * (‖n‖ + 1) + p * blockWidth n + o ∧
      lowerSize n + blockWidth n + 2 * n * (‖n‖ + 1) ≤ v ∧ v < bandOffset n) ∨
    (∃ r x q w, t = ⟪1, r, x⟫ ∧ r < bandCount n ∧
      BandCodomain (powerBound n) (exponent n) (bandBound n r) x ∧ BandIndex n r x q ∧
      BandPosition n r q w ∧ q < 2 * bandBound n r * bandUnit n ∧ v = bandOffset n + w ∧
      bandOffset n ≤ v ∧ v < lowerSize n + targetExcess n) := by
  have hn0 : 0 < n := lt_of_lt_of_le two_pos hn2
  have hn2n : n ≤ 2 * n := by simp
  rcases h with hc | ⟨y, -, rfl, rfl⟩ | ⟨k, -, i, -, rfl, rfl⟩ | ⟨p, -, o, -, rfl, rfl⟩ |
    ⟨r, -, x, -, q, -, w, -, rfl, hq, hw, rfl⟩
  · exact Or.inl ⟨hc, carryEncode_lt hn2 ht hc⟩
  · have hy := (below_of_codomain_four ht).trans (scaledLength_lt_blockWidth hn0 hn0 hn2n)
    exact Or.inr (Or.inl ⟨y, rfl, hy, rfl, le_self_add, (add_lt_add_iff_left _).mpr hy⟩)
  · obtain ⟨hk0, hk2, hi⟩ := top_pair_iff.mp (top_of_codomain_three ht)
    have hi' : i < ‖n‖ + 1 :=
      hi.trans_le ((length_monotone hk2).trans (length_two_mul_of_pos hn0).le)
    refine Or.inr (Or.inr (Or.inl ⟨k, i, rfl, hk0, hi', rfl, le_self_add.trans le_self_add, ?_⟩))
    rw [add_assoc]
    exact (add_lt_add_iff_left _).mpr (mul_add_lt_mul hk0 hk2 hi')
  · obtain ⟨hp, hpp, ho⟩ := small_pair_iff.mp (small_of_codomain_five ht)
    have hp2 : p ≤ 2 * n := (le_mul_of_one_le_right (Arithmetic.zero_le p) hp.1.le).trans hpp
    have ho' := ho.trans (scaledLength_lt_blockWidth hn0 (pos_of_gt hp.1) hp2)
    refine Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, o, rfl, ho', rfl, le_self_add.trans le_self_add, ?_⟩)))
    unfold bandOffset
    calc _ = lowerSize n + blockWidth n + 2 * n * (‖n‖ + 1) + (p * blockWidth n + o) :=
          add_assoc _ _ _
      _ < _ := (add_lt_add_iff_left _).mpr <| calc
          p * blockWidth n + o < p * blockWidth n + blockWidth n := (add_lt_add_iff_left _).mpr ho'
          _ = (p + 1) * blockWidth n := by rw [add_mul, one_mul]
          _ ≤ ((√(2 * n) : V) + 1) * blockWidth n :=
            mul_le_mul_right (add_le_add (le_sqrt_of_mul_self_le hpp) le_rfl)
  · obtain ⟨hr, hx⟩ := codomain_band_iff.mp ht
    obtain ⟨hq2, -⟩ := bandIndex_spec (bandBound_le hr hn2) hx hq
    obtain ⟨-, hw2⟩ := bandPosition_spec hr hq2 hw
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨r, x, q, w, rfl, hr, hx, hq, hw, hq2, rfl,
      le_self_add, ?_⟩)))
    rw [targetExcess_eq, add_assoc]
    exact (add_lt_add_iff_left _).mpr hw2


lemma codomainEncode_band_total {r x q : V} (hr : r < bandCount n)
    (hx : BandCodomain (powerBound n) (exponent n) (bandBound n r) x) (hq : BandIndex n r x q) :
    ∃ v, CodomainEncode n ⟪1, r, x⟫ v := by
  obtain ⟨hq₂, -⟩ := bandIndex_spec (bandBound_le hr hn2) hx hq
  obtain ⟨w, hw⟩ := bandPosition_exists (n := n) r q
  obtain ⟨hqw, -⟩ := bandPosition_spec hr hq₂ hw
  use bandOffset n + w
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨r, by simp, x, by simp, q,
    hqw.trans le_add_self, w, le_add_self, rfl, hq, hw, rfl⟩)))

lemma codomainEncode_total {t : V} (ht : Codomain (powerBound n) (exponent n) n t) :
    ∃ v, CodomainEncode n t v := by
  obtain ⟨a, b, rfl⟩ := exists_pair₂ t
  have ha : a = 0 ∨ a = 1 := by
    rcases ht with h | h
    · exact Or.inl (by simpa using h.1)
    · exact Or.inr (by simpa using h.1)
  rcases ha with rfl | rfl
  · obtain ⟨c, w, rfl⟩ := exists_pair₂ b
    rcases codomain_zero_iff.mp ht with (⟨rfl, hb⟩ | ⟨rfl, hb⟩) | ⟨rfl, ht₃⟩ | ⟨rfl, hy⟩ | ⟨rfl, hs⟩
    · obtain ⟨k, -, y, -, rfl, -⟩ := hb
      exact ⟨_, Or.inl (Or.inl ⟨0, by simp, k, by simp, y, by simp, zero_le_one, rfl, rfl⟩)⟩
    · obtain ⟨k, -, y, -, rfl, -⟩ := hb
      exact ⟨_, Or.inl (Or.inl ⟨1, by simp, k, by simp, y, by simp, le_rfl, rfl, rfl⟩)⟩
    · obtain ⟨k, -, i, -, rfl, -⟩ := ht₃
      exact ⟨_, Or.inr (Or.inr (Or.inl ⟨k, by simp, i, by simp, rfl, rfl⟩))⟩
    · exact ⟨_, Or.inr (Or.inl ⟨w, by simp, rfl, rfl⟩)⟩
    · obtain ⟨p, -, o, -, rfl, -⟩ := hs
      exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, o, by simp, rfl, rfl⟩)))⟩
  · obtain ⟨r, b', rfl⟩ := exists_pair₂ b
    obtain ⟨c, w, rfl⟩ := exists_pair₂ b'
    obtain ⟨hr, hx⟩ := codomain_band_iff.mp ht
    rcases codomain_one_iff.mp ht with
      ⟨-, (⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hy⟩) | ⟨rfl, ht₄⟩ | ⟨rfl, ht₅⟩⟩
    · obtain ⟨k, -, y, -, rfl, -⟩ := hb
      exact ⟨_, Or.inl (Or.inr ⟨r, by simp, 0, by simp, k, by simp (maxDischargeDepth := 8), y,
        by simp (maxDischargeDepth := 8), zero_le_one, rfl, rfl⟩)⟩
    · obtain ⟨k, -, y, -, rfl, -⟩ := hb
      exact ⟨_, Or.inl (Or.inr ⟨r, by simp, 1, by simp, k, by simp (maxDischargeDepth := 8), y,
        by simp (maxDischargeDepth := 8), le_rfl, rfl, rfl⟩)⟩
    · exact codomainEncode_band_total hn2 hr hx (Or.inl ⟨w, by simp, rfl, rfl⟩)
    · obtain ⟨k, -, i, -, rfl, -⟩ := ht₄
      exact codomainEncode_band_total hn2 hr hx
        (Or.inr ⟨4, by simp, k, by simp, i, by simp, le_rfl, by norm_num, rfl, rfl⟩)
    · obtain ⟨k, -, i, -, rfl, -⟩ := ht₅
      exact codomainEncode_band_total hn2 hr hx
        (Or.inr ⟨5, by simp, k, by simp, i, by simp, by norm_num, le_rfl, rfl, rfl⟩)

end encoding

section encode

variable (hℓ : (1024 : V) ≤ ‖n‖)
include hℓ

lemma isInj_codomainEncode :
    IsInj (CodomainEncode n) (Codomain (powerBound n) (exponent n) n)
      (· < lowerSize n + targetExcess n) := by
  have hn2 := two_le_of_length_ge hℓ
  have h₁ : lowerSize n ≤ lowerSize n + blockWidth n := le_self_add
  have h₂ : lowerSize n + blockWidth n ≤ lowerSize n + blockWidth n + 2 * n * (‖n‖ + 1) :=
    le_self_add
  have h₃ : lowerSize n + blockWidth n + 2 * n * (‖n‖ + 1) ≤ bandOffset n := by
    unfold bandOffset
    exact le_self_add
  have h₄ : bandOffset n ≤ lowerSize n + targetExcess n := by
    rw [targetExcess_eq]
    exact le_self_add.trans le_self_add
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact codomainEncode_total hn2 ht
  · intro t v ht h
    rcases codomainEncode_cases hn2 ht h with ⟨-, hv⟩ | ⟨y, -, -, -, -, hv⟩ |
      ⟨k, i, -, -, -, -, -, hv⟩ | ⟨p, o, -, -, -, -, hv⟩ | ⟨r, x, q, w, -, -, -, -, -, -, -, -, hv⟩
    · exact hv.trans_le (h₁.trans (h₂.trans (h₃.trans h₄)))
    · exact hv.trans_le (h₂.trans (h₃.trans h₄))
    · exact hv.trans_le (h₃.trans h₄)
    · exact hv.trans_le h₄
    · exact hv
  · intro t t' v ht ht' h h'
    rcases codomainEncode_cases hn2 ht h with ⟨hc, hv⟩ | ⟨y, rfl, hy, hvy, hlo, hhi⟩ |
      ⟨k, i, rfl, hk, hi, hvk, hlo, hhi⟩ | ⟨p, o, rfl, ho, hvp, hlo, hhi⟩ |
      ⟨r, x, q, w, rfl, hr, hx, hq, hw, hqb, hvb, hlo, hhi⟩
    · rcases codomainEncode_cases hn2 ht' h' with ⟨hc', hv'⟩ | ⟨y', rfl, hy', hvy', hlo', hhi'⟩ |
        ⟨k', i', rfl, hk', hi', hvk', hlo', hhi'⟩ | ⟨p', o', rfl, ho', hvp', hlo', hhi'⟩ |
        ⟨r', x', q', w', rfl, hr', hx', hq', hw', hqb', hvb', hlo', hhi'⟩
      · exact carryEncode_inj hn2 ht ht' hc hc'
      all_goals grind
    · rcases codomainEncode_cases hn2 ht' h' with ⟨hc', hv'⟩ | ⟨y', rfl, hy', hvy', hlo', hhi'⟩ |
        ⟨k', i', rfl, hk', hi', hvk', hlo', hhi'⟩ | ⟨p', o', rfl, ho', hvp', hlo', hhi'⟩ |
        ⟨r', x', q', w', rfl, hr', hx', hq', hw', hqb', hvb', hlo', hhi'⟩
      · grind
      · rw [add_left_cancel (hvy.symm.trans hvy')]
      all_goals grind
    · rcases codomainEncode_cases hn2 ht' h' with ⟨hc', hv'⟩ | ⟨y', rfl, hy', hvy', hlo', hhi'⟩ |
        ⟨k', i', rfl, hk', hi', hvk', hlo', hhi'⟩ | ⟨p', o', rfl, ho', hvp', hlo', hhi'⟩ |
        ⟨r', x', q', w', rfl, hr', hx', hq', hw', hqb', hvb', hlo', hhi'⟩
      · grind
      · grind
      · have e : (k - 1) * (‖n‖ + 1) + i = (k' - 1) * (‖n‖ + 1) + i' := by
          apply add_left_cancel (a := lowerSize n + blockWidth n)
          simpa only [add_assoc] using hvk.symm.trans hvk'
        obtain ⟨e₁, rfl⟩ := eq_of_mul_add_eq hi hi' e
        rw [eq_of_sub_one_eq hk hk' e₁]
      all_goals grind
    · rcases codomainEncode_cases hn2 ht' h' with ⟨hc', hv'⟩ | ⟨y', rfl, hy', hvy', hlo', hhi'⟩ |
        ⟨k', i', rfl, hk', hi', hvk', hlo', hhi'⟩ | ⟨p', o', rfl, ho', hvp', hlo', hhi'⟩ |
        ⟨r', x', q', w', rfl, hr', hx', hq', hw', hqb', hvb', hlo', hhi'⟩
      · grind
      · grind
      · grind
      · have e : p * blockWidth n + o = p' * blockWidth n + o' := by
          apply add_left_cancel (a := lowerSize n + blockWidth n + 2 * n * (‖n‖ + 1))
          simpa only [add_assoc] using hvp.symm.trans hvp'
        obtain ⟨rfl, rfl⟩ := eq_of_mul_add_eq ho ho' e
        rfl
      all_goals grind
    · rcases codomainEncode_cases hn2 ht' h' with ⟨hc', hv'⟩ | ⟨y', rfl, hy', hvy', hlo', hhi'⟩ |
        ⟨k', i', rfl, hk', hi', hvk', hlo', hhi'⟩ | ⟨p', o', rfl, ho', hvp', hlo', hhi'⟩ |
        ⟨r', x', q', w', rfl, hr', hx', hq', hw', hqb', hvb', hlo', hhi'⟩
      · grind
      · grind
      · grind
      · grind
      · obtain rfl : w = w' := add_left_cancel (hvb.symm.trans hvb')
        obtain ⟨rfl, rfl⟩ := bandPosition_inj hr hr' hqb hqb' hw hw'
        rw [(bandIndex_spec (bandBound_le hr hn2) hx hq).2 x' hx' hq']

lemma domainEncode_cover :
    ∀ v < lowerSize n + upperExcess n,
      (∀ u, Domain (powerBound n) (exponent n) n u → ¬DomainEncode n u v) →
      v < lowerSize n + targetExcess n ∧
        ∀ t, Codomain (powerBound n) (exponent n) n t → ¬CodomainEncode n t v := by
  have hn2 := two_le_of_length_ge hℓ
  intro v hv hno
  have hvz : v < lowerSize n := by
    by_contra hge
    obtain ⟨y, rfl⟩ := le_iff_exists_add.mp (not_lt.mp hge)
    exact hno ⟪0, 2, y⟫ (domain_zero_iff.mpr (Or.inr (Or.inr
      ⟨rfl, (add_lt_add_iff_left _).mp hv⟩))) (Or.inr ⟨y, by simp, rfl, rfl⟩)
  refine ⟨hvz.trans_le le_self_add, ?_⟩
  intro t ht h
  rcases codomainEncode_cases hn2 ht h with ⟨hc, -⟩ | ⟨y, -, -, -, hlo, -⟩ |
    ⟨k, i, -, -, -, -, hlo, -⟩ | ⟨p, o, -, -, -, hlo, -⟩ | ⟨r, x, q, w, -, -, -, -, -, -, -, hlo, -⟩
  · rcases carryEncode_cases hn2 ht hc with ⟨c, k, y, hc₁, -, -, -, rfl, -⟩ |
      ⟨r, c, k, y, hc₁, hr, -, -, -, rfl, -⟩
    · exact hno _ (domain_of_bits_zero (bits_of_codomain_zero ht hc₁) hc₁) (Or.inl hc)
    · exact hno _ (domain_of_bits_one hr (bits_of_codomain_one ht hc₁).2 hc₁) (Or.inl hc)
  · exact lt_irrefl _ (hvz.trans_le hlo)
  · exact lt_irrefl _ (hvz.trans_le (le_self_add.trans hlo))
  · exact lt_irrefl _ (hvz.trans_le ((le_self_add.trans le_self_add).trans hlo))
  · have : lowerSize n ≤ bandOffset n := by
      unfold bandOffset
      exact le_self_add.trans (le_self_add.trans le_self_add)
    exact lt_irrefl _ (hvz.trans_le (this.trans hlo))

omit hℓ in
lemma domainEncode_functional :
    ∀ u v v', Domain (powerBound n) (exponent n) n u → DomainEncode n u v →
      DomainEncode n u v' → v = v' := by
  intro u v v' _ h h'
  rcases h with (⟨c, -, k, -, y, -, hc, rfl, rfl⟩ | ⟨r, -, c, -, k, -, y, -, hc, rfl, rfl⟩) |
    ⟨y, -, rfl, rfl⟩ <;>
  rcases h' with (⟨c', -, k', -, y', -, hc', h₂, rfl⟩ |
    ⟨r', -, c', -, k', -, y', -, hc', h₂, rfl⟩) | ⟨y', -, h₂, rfl⟩
  · obtain ⟨-, rfl, rfl, rfl⟩ : 0 = 0 ∧ c = c' ∧ k = k' ∧ y = y' := by
      simpa only [pair_ext_iff] using h₂
    rfl
  · exact absurd (pair_ext_iff.mp h₂).1 zero_ne_one
  · obtain rfl := (pair_ext_iff.mp (pair_ext_iff.mp h₂).2).1
    exact absurd hc (by norm_num)
  · exact absurd (pair_ext_iff.mp h₂).1 one_ne_zero
  · obtain ⟨-, rfl, rfl, rfl, rfl⟩ : 1 = 1 ∧ r = r' ∧ c = c' ∧ k = k' ∧ y = y' := by
      simpa only [pair_ext_iff] using h₂
    rfl
  · exact absurd (pair_ext_iff.mp h₂).1 one_ne_zero
  · obtain rfl := (pair_ext_iff.mp (pair_ext_iff.mp h₂).2).1
    exact absurd hc' (by norm_num)
  · exact absurd (pair_ext_iff.mp h₂).1 zero_ne_one
  · obtain ⟨-, -, rfl⟩ : 0 = 0 ∧ 2 = 2 ∧ y = y' := by simpa only [pair_ext_iff] using h₂
    rfl

end encode

lemma definable_domain (B s : V) : 𝚺ᴬ₀.DefinablePred (Domain B s n) := by
  have := definable_bits B s
  unfold Domain LowerDomain BandCarry Family Tagged Below bandBound bandSize bandCount cutoff
  definability

lemma Domain.lt {B s u : V} (hn2 : 2 ≤ n) (h : Domain B s n u) :
    u < ⟪1, n, 10, payloadBound B s n⟫ + 1 := by
  rcases h with h | h
  · exact Tagged.lt_of_tagged_zero h fun _ ↦ LowerDomain.le_bound
  · exact Tagged.lt_of_family h bandCount_le fun r hr x hx ↦
      BandCarry.le_bound (bandBound_le hr hn2) hx

lemma Codomain.lt {B s u : V} (hn2 : 2 ≤ n) (h : Codomain B s n u) :
    u < ⟪1, n, 10, payloadBound B s n⟫ + 1 := by
  rcases h with h | h
  · exact Tagged.lt_of_tagged_zero h fun _ ↦ LowerResidue.le_bound
  · exact Tagged.lt_of_family h bandCount_le fun r hr x hx ↦
      BandCodomain.le_bound (bandBound_le hr hn2) hx

/-- If $\|n\| \ge 1024$, there is a prime in $(n, 2n]$. -/
lemma exists_prime_of_length (hℓ : (1024 : V) ≤ ‖n‖) : ∃ p, n < p ∧ p ≤ 2 * n ∧ IsPrime p := by
  by_contra! H
  have hn0 : 0 < n :=
    length_pos_iff.mp (lt_of_lt_of_le (by exact_mod_cast (show (0 : ℕ) < 1024 by decide)) hℓ)
  have hn2 : 2 ≤ n := two_le_of_length_ge hℓ
  have hB : 0 < powerBound n := smash_pos _ _
  have hs : 0 < exponent n := mul_pos (length_pos_iff.mpr hn0) (length_pos_iff.mpr hn0)
  have hemb := embeds_domain_codomain hB hs exponent_mul_length_lt
    (fun p h₁ h₂ hp ↦ H p h₁ h₂ hp) hn2
  obtain ⟨R, hR, hinj⟩ := Embeds.extend (definable_domain _ _) (definable_domainEncode n)
    (definable_codomainEncode n) hemb (fun _ hu ↦ Domain.lt hn2 hu) (fun _ ht ↦ Codomain.lt hn2 ht)
    domainEncode_functional (isInj_codomainEncode hℓ) (domainEncode_cover hℓ)
  have hsize := size_inequality hℓ
  have hK : 0 < ratio n := by
    have h1 : (0 : V) < ‖n‖ + 1 := lt_of_lt_of_le zero_lt_one le_add_self
    unfold ratio
    exact mul_pos (mul_pos (by exact_mod_cast (show (0 : ℕ) < 16 by decide)) h1) h1
  set K := ratio n
  set c := (lowerSize n + targetExcess n) / K + 1
  have hc₁ : lowerSize n + targetExcess n ≤ K * c := (lt_mul_div_succ _ hK).le
  have hc₂ : (K + 1) * c ≤ lowerSize n + upperExcess n := by
    have h₁ : K * c ≤ lowerSize n + targetExcess n + K := calc
      K * c = K * ((lowerSize n + targetExcess n) / K) + K := by simp [c, mul_add]
      _ ≤ lowerSize n + targetExcess n + K := add_le_add (mul_div_le _ _) le_rfl
    apply le_of_mul_le_mul_left (a := K) _ hK
    calc K * ((K + 1) * c) = (K + 1) * (K * c) := by grind
      _ ≤ (K + 1) * (lowerSize n + targetExcess n + K) := mul_le_mul_left h₁
      _ = ((K + 1) * targetExcess n + K * (K + 1) + lowerSize n) + K * lowerSize n := by grind
      _ ≤ K * upperExcess n + K * lowerSize n := add_le_add hsize le_rfl
      _ = K * (lowerSize n + upperExcess n) := by grind
  obtain ⟨x, hx, x', hx', y, hy, hne, h, h'⟩ :=
    weakPigeonhole_succ_mul_of_le_length hR (b := c) (I := lengthBound n) (by simp [c]) hK
      (ratio_le_length hℓ) fun x hx ↦ by
        obtain ⟨y, hy⟩ := hinj.1 x (lt_of_lt_of_le hx hc₂)
        use y
        exact ⟨lt_of_lt_of_le (hinj.2.1 x y (lt_of_lt_of_le hx hc₂) hy) hc₁, hy⟩
  exact hne (hinj.2.2 x x' y (lt_of_lt_of_le hx hc₂) (lt_of_lt_of_le hx' hc₂) h h')

end Bertrand

/-- Between $n$ and $2n$ there is a prime, for every $n \ge 1$. -/
def bertrandPostulate : ArithmeticSentence :=
  “∀ n, 1 ≤ n → ∃ p, n < p ∧ p ≤ 2 * n ∧ !isPrime p”

lemma exists_natCast_of_length_le (j : ℕ) {x : V} (h : ‖x‖ ≤ j) : ∃ k : ℕ, x = k := by
  induction j generalizing x with
  | zero =>
    use 0
    simpa using h
  | succ j ih =>
    rcases (Arithmetic.zero_le x).eq_or_lt with rfl | hx
    · use 0
      simp
    have hx₂ : 2 * (x / 2) + x % 2 = x := div_add_mod x 2
    rcases (Arithmetic.zero_le (x / 2)).eq_or_lt with h₀ | h₀
    · rw [← h₀, mul_zero, zero_add] at hx₂
      have : x ≤ 1 := lt_two_iff_le_one.mp (hx₂ ▸ mod_lt x two_pos)
      use 1
      simpa using le_antisymm this (pos_iff_one_le.mp hx)
    have hlen : ‖x‖ = ‖x / 2‖ + 1 := by
      rcases mod_two x with h₁ | h₁
      · rw [h₁, add_zero] at hx₂
        rw [← length_two_mul_of_pos h₀, hx₂]
      · rw [h₁] at hx₂
        rw [← length_two_mul_add_one (x / 2), hx₂]
    obtain ⟨k, hk⟩ := ih (x := x / 2) (by
      rw [hlen, Nat.cast_succ] at h
      exact (add_le_add_iff_right 1).mp h)
    rcases mod_two x with h₁ | h₁
    · use 2 * k
      rw [h₁, add_zero, hk] at hx₂
      simpa using hx₂.symm
    · use 2 * k + 1
      rw [h₁, hk] at hx₂
      simpa using hx₂.symm

lemma isPrime_natCast {p : ℕ} (hp : p.Prime) : IsPrime (p : V) := by
  have h : IsPrime p := ⟨hp.one_lt, fun b hb hd ↦ (Nat.prime_def.mp hp).2 b hd⟩
  simpa using (Defined.sigmaZero_absolute (V := V) (isPrime_defined (V := ℕ))
    (isPrime_defined (V := V)) ![p]).mp h

lemma exists_prime_lt_le_two_mul (n : V) (hn : 1 ≤ n) : ∃ p, n < p ∧ p ≤ 2 * n ∧ IsPrime p := by
  by_cases hℓ : (1024 : V) ≤ ‖n‖
  · exact Bertrand.exists_prime_of_length hℓ
  obtain ⟨k, rfl⟩ := exists_natCast_of_length_le 1023 (x := n) (by
    rw [Nat.cast_ofNat]
    apply lt_succ_iff_le.mp
    rw [show (1023 : V) + 1 = 1024 by norm_num]
    exact not_le.mp hℓ)
  obtain ⟨p, hp, hkp, hpk⟩ := Nat.exists_prime_lt_and_le_two_mul k (by
    rintro rfl
    simp at hn)
  exact ⟨p, by exact_mod_cast hkp, by exact_mod_cast hpk, isPrime_natCast hp⟩

@[simp] lemma models_bertrandPostulate_iff {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] :
    V↓[ℒₒᵣ] ⊧ bertrandPostulate ↔ ∀ n : V, 1 ≤ n → ∃ p, n < p ∧ p ≤ 2 * n ∧ IsPrime p := by
  simp [models_iff, bertrandPostulate]

end

/-- - [HP98, §V.5(f), p. 392]
- [PWW88, remark before Theorem 12] -/
theorem provable_bertrandPostulate_ISigma0_union_Omega1 : 𝗜𝚺₀ ∪ 𝝮₁ ⊢ bertrandPostulate :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀ ∪ 𝝮₁ :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) inferInstance
  complete (𝗜𝚺₀ ∪ 𝝮₁) bertrandPostulate fun (M : Type) _ _ ↦ by
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
    exact models_bertrandPostulate_iff.mpr exists_prime_lt_le_two_mul

/-- $\mathsf{I}\Delta_0$ proves Bertrand's postulate. An open problem.
- [HP98, §V.5(f), p. 393] -/
def ProvableBertrandPostulateISigma0 : Prop := 𝗜𝚺₀ ⊢ bertrandPostulate

end FFL.FirstOrder.Arithmetic
