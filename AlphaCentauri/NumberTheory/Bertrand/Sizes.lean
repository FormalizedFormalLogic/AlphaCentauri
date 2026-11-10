module

public import Foundation.FirstOrder.Arithmetic.Omega1.Basic
public import AlphaCentauri.ToFoundation.Exponential

/-!
# The sizes in the proof of Bertrand's postulate

The parameters of the injection that refutes the failure of Bertrand's postulate at `n`, over a
model of $\mathsf{I}\Sigma_0 + \Omega_1$, and the inequalities between them. With
$\ell = \|n\|$, the exponent is $s = \ell^2$, positions are counted below
$\Lambda = s(\ell + 1) + 1$, the Chebyshev bands are the halvings
$u_r = \lfloor x / 2^r \rfloor$ of $x = \lfloor 2n / 3 \rfloor$, and the injection goes from
$z + a$ into $z + b$ numbers with $(K + 1) b + K (K + 1) + z \le K a$, so that it is one of
$(K + 1) c$ into $K c$ for $c = \lfloor (z + b) / K \rfloor + 1$.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁]

namespace Bertrand

variable (n : V)

/-- The exponent $s = \|n\|^2$. -/
def exponent : V := ‖n‖ * ‖n‖

/-- $\Lambda = s(\|n\| + 1) + 1$, which bounds the scaled lengths of the numbers up to $2n$. -/
def blockWidth : V := exponent n * (‖n‖ + 1) + 1

/-- $x = \lfloor 2n / 3 \rfloor$: under the failure of Bertrand's postulate, no prime power above
`x` contributes to $\binom{2n}{n}$ except the proper prime powers in $(n, 2n]$. -/
def cutoff : V := 2 * n / 3

/-- The number $R = \|x\|$ of Chebyshev bands. -/
def bandCount : V := ‖cutoff n‖

/-- $u_r = \lfloor x / 2^r \rfloor$. -/
def bandSize (r : V) : V := cutoff n / bexp (2 * cutoff n + 1) r

/-- $w = s + \|n\| + 1$, the size per number of a band. -/
def bandUnit : V := exponent n + ‖n‖ + 1

/-- $z = (2R + 2) n \Lambda$, the size of the boxes of the positions that are carried along. -/
def lowerSize : V := (2 * bandCount n + 2) * n * blockWidth n

/-- $a = (2n - 1)s$. -/
def upperExcess : V := (2 * n - 1) * exponent n

/-- $b$, the size of the box of the errors and of the Chebyshev bands. -/
def targetExcess : V :=
  blockWidth n + 2 * n * (‖n‖ + 1) + (√(2 * n) + 1) * blockWidth n +
    2 * cutoff n * bandUnit n + 2 * bandCount n * bandUnit n

/-- $K = 16 (\|n\| + 1)^2$. -/
def ratio : V := 16 * (‖n‖ + 1) * (‖n‖ + 1)

/-- The block width $B$ for the powers $k^s$, $k \le 4n$. -/
def powerBound : V := (n ⨳ n) ⨳ (2 * (2 * n))

/-- A number of length at least $K$. -/
def lengthBound : V := ((2 * n) ⨳ (2 * n)) ⨳ ((2 * n) ⨳ (2 * n))

variable {n}

lemma exponent_mul_length_lt : exponent n * ‖2 * (2 * n)‖ < ‖powerBound n‖ := by
  rw [powerBound, length_smash, length_smash, exponent]
  exact lt_succ_iff_le.mpr (mul_le_mul_right (by simp))

lemma ratio_le_length (hn : (1024 : V) ≤ ‖n‖) : ratio n ≤ ‖lengthBound n‖ := by
  have hpos : 0 < n :=
    length_pos_iff.mp (lt_of_lt_of_le (by exact_mod_cast (show (0 : ℕ) < 1024 by decide)) hn)
  have h16 : (16 : V) ≤ (‖n‖ + 1) * (‖n‖ + 1) := calc
    (16 : V) ≤ 1024 := by exact_mod_cast (show (16 : ℕ) ≤ 1024 by decide)
    _ ≤ ‖n‖ := hn
    _ ≤ (‖n‖ + 1) * (‖n‖ + 1) := le_trans le_self_add (le_mul_of_one_le_left
        (Arithmetic.zero_le _) le_add_self)
  rw [lengthBound, length_smash, length_smash, length_two_mul_of_pos hpos, ratio, mul_assoc]
  calc 16 * ((‖n‖ + 1) * (‖n‖ + 1))
      ≤ ((‖n‖ + 1) * (‖n‖ + 1)) * ((‖n‖ + 1) * (‖n‖ + 1)) := mul_le_mul_right h16
    _ ≤ ((‖n‖ + 1) * (‖n‖ + 1) + 1) * ((‖n‖ + 1) * (‖n‖ + 1) + 1) := by
        apply mul_le_mul <;> simp
    _ ≤ ((‖n‖ + 1) * (‖n‖ + 1) + 1) * ((‖n‖ + 1) * (‖n‖ + 1) + 1) + 1 := le_self_add

lemma sqrt_growth (hn : (1024 : V) ≤ ‖n‖) :
    28 ≤ √(2 * n) ∧ 7 * (‖n‖ + 1) * (√(2 * n) + 2) ≤ n := by
  set g := √(2 * n)
  set m := ‖g‖
  have hgg : g * g ≤ 2 * n := sqrt_spec_le _
  have hlt : 2 * n < (g + 1) * (g + 1) := sqrt_spec_lt _
  have hg1 : ‖g + 1‖ ≤ m + 1 := by
    rw [← length_two_mul_add_one]
    apply length_monotone
    gcongr
    exact le_mul_of_one_le_left (Arithmetic.zero_le _) one_le_two
  have hℓm : ‖n‖ ≤ 2 * m + 2 := calc
    ‖n‖ ≤ ‖(g + 1) * (g + 1)‖ := length_monotone (le_trans (by simp) hlt.le)
    _ ≤ ‖g + 1‖ + ‖g + 1‖ := length_mul_le _ _
    _ ≤ (m + 1) + (m + 1) := add_le_add hg1 hg1
    _ = 2 * m + 2 := by grind
  have hm : (511 : V) ≤ m := by
    have : (2 : V) * 511 + 2 ≤ 2 * m + 2 := le_trans (le_of_eq (by norm_num)) (hn.trans hℓm)
    exact le_of_mul_le_mul_left ((add_le_add_iff_right 2).mp this) two_pos
  have hmm : m * m ≤ 3 * g := by simpa [sq] using sq_len_le_three_mul g
  have h84 : 84 * m ≤ g := by
    have : 3 * (84 * m) ≤ 3 * g := calc
      3 * (84 * m) = 252 * m := by grind
      _ ≤ m * m := mul_le_mul_of_nonneg_right (le_trans (by norm_cast) hm) (Arithmetic.zero_le _)
      _ ≤ 3 * g := hmm
    exact le_of_mul_le_mul_left this (by exact_mod_cast (show (0 : ℕ) < 3 by decide))
  have hm1 : (1 : V) ≤ m := le_trans (by norm_cast) hm
  have hg28 : (28 : V) ≤ g := calc
    (28 : V) ≤ 84 * 1 := by norm_cast
    _ ≤ 84 * m := by gcongr
    _ ≤ g := h84
  have hg2 : g + 2 ≤ 2 * g := calc
    g + 2 ≤ g + g := by gcongr; exact le_trans (by norm_cast) hg28
    _ = 2 * g := by grind
  have hL : ‖n‖ + 1 ≤ 3 * m := calc
    ‖n‖ + 1 ≤ 2 * m + 2 + 1 := by gcongr
    _ ≤ 2 * m + m := by rw [add_assoc]; gcongr; exact le_trans (by norm_cast) hm
    _ = 3 * m := by grind
  constructor
  · exact hg28
  · have : 2 * (7 * (‖n‖ + 1) * (g + 2)) ≤ 2 * n := calc
      2 * (7 * (‖n‖ + 1) * (g + 2)) ≤ 2 * (7 * (3 * m) * (2 * g)) := by gcongr
      _ = 84 * m * g := by grind
      _ ≤ g * g := mul_le_mul_of_nonneg_right h84 (Arithmetic.zero_le _)
      _ ≤ 2 * n := hgg
    exact le_of_mul_le_mul_left this two_pos

section Bounds

variable {ℓ L s g x R K a : V}

private lemma succ_mul_succ_le (hℓ : (408 : V) ≤ ℓ) : (ℓ + 1) * (ℓ + 1) ≤ 2 * (ℓ * ℓ) := calc
  (ℓ + 1) * (ℓ + 1) = ℓ * ℓ + (2 * ℓ + 1) := by grind
  _ ≤ ℓ * ℓ + ℓ * ℓ := by
    gcongr
    calc 2 * ℓ + 1 ≤ 2 * ℓ + ℓ := by gcongr; exact le_trans (by norm_cast) hℓ
      _ = 3 * ℓ := by grind
      _ ≤ ℓ * ℓ := mul_le_mul_of_nonneg_right (le_trans (by norm_cast) hℓ) (Arithmetic.zero_le _)
  _ = 2 * (ℓ * ℓ) := by grind

private lemma mul_succ_le (hℓ : (408 : V) ≤ ℓ) : 204 * (ℓ + 1) ≤ ℓ * ℓ := calc
  204 * (ℓ + 1) ≤ 204 * (ℓ + ℓ) := by gcongr; exact le_trans (by norm_cast) hℓ
  _ = 408 * ℓ := by grind
  _ ≤ ℓ * ℓ := mul_le_mul_of_nonneg_right hℓ (Arithmetic.zero_le _)

private lemma sq_succ_add_one_le (hℓ : (1 : V) ≤ ℓ) :
    ℓ * ℓ * (ℓ + 1) + 1 ≤ 2 * (ℓ * ℓ) * (ℓ + 1) := calc
  ℓ * ℓ * (ℓ + 1) + 1 ≤ ℓ * ℓ * (ℓ + 1) + ℓ * ℓ * (ℓ + 1) := by
    gcongr
    exact one_le_mul (one_le_mul hℓ hℓ) (le_trans hℓ le_self_add)
  _ = 2 * (ℓ * ℓ) * (ℓ + 1) := by grind

private lemma lowerSize_term_le (hL : 1 ≤ L) (hRL : R + 1 ≤ L) (hLs : 204 * L ≤ s) :
    3 * ((2 * R + 2) * n * (s * L + 1)) ≤ 7 * (L * L * n * s) := calc
  3 * ((2 * R + 2) * n * (s * L + 1)) = 6 * (R + 1) * n * (s * L + 1) := by grind
  _ ≤ 6 * L * n * (s * L + 1) := by gcongr
  _ = 6 * (L * L * n * s) + 6 * (L * n) := by grind
  _ ≤ 6 * (L * L * n * s) + (L * s) * (L * n) := by
    gcongr
    calc (6 : V) ≤ 204 * 1 := by norm_cast
      _ ≤ 204 * L := by gcongr
      _ ≤ s := hLs
      _ ≤ L * s := le_mul_of_one_le_left (Arithmetic.zero_le _) hL
  _ = 7 * (L * L * n * s) := by grind

private lemma rootBound_term_le (hK : K + 1 ≤ 17 * L * L) (hΛ : s * L + 1 ≤ 2 * s * L)
    (hG : 7 * L * (g + 2) ≤ n) :
    3 * (K + 1) * ((g + 2) * (s * L + 1)) ≤ 15 * (L * L * n * s) := calc
  3 * (K + 1) * ((g + 2) * (s * L + 1)) ≤ 3 * (17 * L * L) * ((g + 2) * (2 * s * L)) := by
    gcongr
  _ = 102 * (L * L * s) * (L * (g + 2)) := by grind
  _ ≤ 105 * (L * L * s) * (L * (g + 2)) := by gcongr; norm_cast
  _ = 15 * (L * L * s) * (7 * L * (g + 2)) := by grind
  _ ≤ 15 * (L * L * s) * n := by gcongr
  _ = 15 * (L * L * n * s) := by grind

private lemma twoLength_term_le (hK : K + 1 ≤ 17 * L * L) (hLs : 204 * L ≤ s) :
    6 * (K + 1) * (n * L) ≤ L * L * n * s := calc
  6 * (K + 1) * (n * L) ≤ 6 * (17 * L * L) * (n * L) := by gcongr
  _ = L * L * n * (102 * L) := by grind
  _ ≤ L * L * n * (204 * L) := by gcongr; norm_cast
  _ ≤ L * L * n * s := by gcongr

private lemma cutoff_term_le (hK : K + 1 ≤ 17 * L * L) (hLs : 204 * L ≤ s) (hL : 4 ≤ L)
    (h3x : 3 * x ≤ 2 * n) :
    (K + 1) * (3 * x) * (2 * (s + L)) ≤ 4 * K * n * s + 2 * (L * L * n * s) := calc
  (K + 1) * (3 * x) * (2 * (s + L)) ≤ (K + 1) * (2 * n) * (2 * (s + L)) := by gcongr
  _ = 4 * K * n * s + 4 * n * s + 4 * (K + 1) * (n * L) := by grind
  _ ≤ 4 * K * n * s + L * L * n * s + L * L * n * s := by
    have h₁ : 4 * n * s ≤ L * L * n * s := calc
      4 * n * s = 4 * 1 * n * s := by grind
      _ ≤ L * L * n * s := by gcongr; exact le_trans (by norm_cast) hL
    have h₂ : 4 * (K + 1) * (n * L) ≤ L * L * n * s := calc
      4 * (K + 1) * (n * L) ≤ 6 * (K + 1) * (n * L) := by gcongr; norm_cast
      _ ≤ L * L * n * s := twoLength_term_le hK hLs
    grind
  _ = 4 * K * n * s + 2 * (L * L * n * s) := by grind

private lemma bandCount_term_le (hK : K + 1 ≤ 17 * L * L) (hR : R ≤ L) (hLs : s + L ≤ 2 * s)
    (hLn : 204 * L ≤ n) : 6 * (K + 1) * (R * (s + L)) ≤ L * L * n * s := calc
  6 * (K + 1) * (R * (s + L)) ≤ 6 * (17 * L * L) * (L * (2 * s)) := by gcongr
  _ = L * L * s * (204 * L) := by grind
  _ ≤ L * L * s * n := by gcongr
  _ = L * L * n * s := by grind

private lemma ratio_sq_term_le (hK : K = 16 * L * L) (hK1 : K + 1 ≤ 17 * L * L)
    (hLL : L * L ≤ 2 * s) (hn : 1632 ≤ n) : 3 * (K * (K + 1)) ≤ L * L * n * s := calc
  3 * (K * (K + 1)) ≤ 3 * (16 * L * L * (17 * L * L)) := by gcongr; exact hK.le
  _ = 816 * (L * L) * (L * L) := by grind
  _ ≤ 816 * (L * L) * (2 * s) := by gcongr
  _ = L * L * s * 1632 := by grind
  _ ≤ L * L * s * n := by gcongr
  _ = L * L * n * s := by grind

private lemma ratio_exponent_term_le (hK : K = 16 * L * L) (hn : 1632 ≤ n) :
    3 * (K * s) ≤ L * L * n * s := calc
  3 * (K * s) = L * L * s * 48 := by rw [hK]; grind
  _ ≤ L * L * s * n := by gcongr; exact le_trans (by norm_cast) hn
  _ = L * L * n * s := by grind

/-- The sizes of the injection, over abstract values of $L = \|n\| + 1$, $s = \|n\|^2$,
$K = 16 L^2$, $x = \lfloor 2n / 3 \rfloor$, $R = \|x\|$ and $a = (2n - 1) s$. -/
private lemma size_inequality_aux (hK : K = 16 * L * L) (hL : 409 ≤ L) (hg : 28 ≤ g)
    (hG : 7 * L * (g + 2) ≤ n) (hRL : R + 1 ≤ L) (hLs : 204 * L ≤ s) (hLL : L * L ≤ 2 * s)
    (hΛ : s * L + 1 ≤ 2 * s * L) (h3x : 3 * x ≤ 2 * n) (ha : a + s = 2 * n * s) :
    (K + 1) * ((s * L + 1) + 2 * n * L + (g + 1) * (s * L + 1) + 2 * x * (s + L) +
      2 * R * (s + L)) + K * (K + 1) + (2 * R + 2) * n * (s * L + 1) ≤ K * a := by
  have hL1 : (1 : V) ≤ L := le_trans (by norm_cast) hL
  have hLn : 204 * L ≤ n := calc
    204 * L ≤ 210 * L := by gcongr; norm_cast
    _ = 7 * L * (28 + 2) := by grind
    _ ≤ 7 * L * (g + 2) := by gcongr
    _ ≤ n := hG
  have hn : (1632 : V) ≤ n := calc
    (1632 : V) ≤ 204 * 8 := le_of_eq (by norm_num)
    _ ≤ 204 * L := by gcongr; exact le_trans (by norm_cast) hL
    _ ≤ n := hLn
  have hK1 : K + 1 ≤ 17 * L * L := calc
    K + 1 ≤ 16 * L * L + L * L := by rw [hK]; gcongr; exact one_le_mul hL1 hL1
    _ = 17 * L * L := by grind
  have hsL : s + L ≤ 2 * s := calc
    s + L ≤ s + s := by
      gcongr
      exact le_trans (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_cast)) hLs
    _ = 2 * s := by grind
  have key : 3 * ((K + 1) * ((s * L + 1) + 2 * n * L + (g + 1) * (s * L + 1) +
      2 * x * (s + L) + 2 * R * (s + L)) + K * (K + 1) + (2 * R + 2) * n * (s * L + 1) +
      K * s) ≤ 3 * (K * a + K * s) := calc
    _ = 3 * ((2 * R + 2) * n * (s * L + 1)) + 3 * (K + 1) * ((g + 2) * (s * L + 1)) +
        6 * (K + 1) * (n * L) + (K + 1) * (3 * x) * (2 * (s + L)) +
        6 * (K + 1) * (R * (s + L)) + 3 * (K * (K + 1)) + 3 * (K * s) := by grind
    _ ≤ 7 * (L * L * n * s) + 15 * (L * L * n * s) + L * L * n * s +
        (4 * K * n * s + 2 * (L * L * n * s)) + L * L * n * s + L * L * n * s +
        L * L * n * s := by
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (lowerSize_term_le hL1 hRL hLs) (rootBound_term_le hK1 hΛ hG)) (twoLength_term_le hK1 hLs))
        (cutoff_term_le hK1 hLs (le_trans (by norm_cast) hL) h3x))
        (bandCount_term_le hK1 (le_trans le_self_add hRL) hsL hLn))
        (ratio_sq_term_le hK hK1 hLL hn))
        (ratio_exponent_term_le hK hn)
    _ = 4 * K * n * s + 28 * (L * L * n * s) := by grind
    _ ≤ 4 * K * n * s + 32 * (L * L * n * s) := by gcongr; norm_cast
    _ = 6 * K * n * s := by rw [hK]; grind
    _ = 3 * (K * (a + s)) := by rw [ha]; grind
    _ = 3 * (K * a + K * s) := by grind
  exact (add_le_add_iff_right _).mp
    (le_of_mul_le_mul_left key (by exact_mod_cast (show (0 : ℕ) < 3 by decide)))

end Bounds

lemma size_inequality (hn : (1024 : V) ≤ ‖n‖) :
    (ratio n + 1) * targetExcess n + ratio n * (ratio n + 1) + lowerSize n ≤
      ratio n * upperExcess n := by
  obtain ⟨hg, hG⟩ := sqrt_growth hn
  have h408 : (408 : V) ≤ ‖n‖ := le_trans (by norm_cast) hn
  have hn0 : 0 < n := length_pos_iff.mp (lt_of_lt_of_le zero_lt_one (le_trans (by norm_cast) hn))
  have h3x : 3 * cutoff n ≤ 2 * n := mul_div_le _ _
  have hxn : cutoff n ≤ n := le_of_mul_le_mul_left (h3x.trans (by gcongr; norm_cast))
    (by exact_mod_cast (show (0 : ℕ) < 3 by decide))
  have hb : targetExcess n = (exponent n * (‖n‖ + 1) + 1) + 2 * n * (‖n‖ + 1) +
      (√(2 * n) + 1) * (exponent n * (‖n‖ + 1) + 1) +
      2 * cutoff n * (exponent n + (‖n‖ + 1)) + 2 * bandCount n * (exponent n + (‖n‖ + 1)) := by
    simp only [targetExcess, blockWidth, bandUnit, add_assoc]
  have ha : upperExcess n + ‖n‖ * ‖n‖ = 2 * n * (‖n‖ * ‖n‖) := by
    have : 2 * n - 1 + 1 = 2 * n := sub_add_self_of_le (le_trans (pos_iff_one_le.mp hn0)
      (le_mul_of_one_le_left (Arithmetic.zero_le _) one_le_two))
    calc upperExcess n + ‖n‖ * ‖n‖ = (2 * n - 1 + 1) * (‖n‖ * ‖n‖) := by
          simp only [upperExcess, exponent]; grind
      _ = 2 * n * (‖n‖ * ‖n‖) := by rw [this]
  rw [hb]
  exact size_inequality_aux (L := ‖n‖ + 1) (s := ‖n‖ * ‖n‖) (K := ratio n) rfl
    (le_trans (le_of_eq (by norm_num)) (add_le_add_left h408 1)) hg hG
    ((add_le_add_iff_right 1).mpr (length_monotone hxn)) (mul_succ_le h408)
    (succ_mul_succ_le h408) (sq_succ_add_one_le (le_trans (by norm_cast) h408)) h3x ha

lemma bandSize_zero : bandSize n 0 = cutoff n := by
  simp [bandSize]

lemma bandSize_succ {r : V} (hr : r < bandCount n) :
    2 * bandSize n (r + 1) ≤ bandSize n r ∧ bandSize n r ≤ 2 * bandSize n (r + 1) + 1 := by
  have h : r + 1 < ‖2 * cutoff n + 1‖ := by
    rw [length_two_mul_add_one]
    simpa [bandCount] using hr
  have he : cutoff n / bexp (2 * cutoff n + 1) (r + 1) =
      cutoff n / bexp (2 * cutoff n + 1) r / 2 := by
    rw [bexp_succ h, mul_comm 2 (bexp _ _), div_mul]
  unfold bandSize
  rw [he]
  exact ⟨mul_div_le _ _, le_two_mul_div_two_add_one _⟩

lemma bandSize_bandCount : bandSize n (bandCount n) = 0 := by
  unfold bandSize bandCount
  apply div_eq_zero_of_lt
  exact lt_bexp_len (by simp [length_two_mul_add_one])

lemma bandSize_antitone {r r' : V} (h : r ≤ r') (hr' : r' ≤ bandCount n) :
    bandSize n r' ≤ bandSize n r := by
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp h
  clear h
  revert hr'
  induction k using ISigma0.succ_induction
  · unfold bandSize
    definability
  case zero => intro _; simp
  case succ k IH =>
    intro hk
    have hk' : r + k < bandCount n :=
      lt_of_lt_of_le (by rw [← add_assoc]; exact lt_add_one _) hk
    have := (bandSize_succ hk').1
    rw [← add_assoc]
    calc bandSize n (r + k + 1) ≤ 2 * bandSize n (r + k + 1) := le_mul_of_one_le_left
          (Arithmetic.zero_le _) one_le_two
      _ ≤ bandSize n (r + k) := this
      _ ≤ bandSize n r := IH hk'.le

end Bertrand

end

end FFL.FirstOrder.Arithmetic
