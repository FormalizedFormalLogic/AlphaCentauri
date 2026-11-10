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

lemma size_inequality (hn : (1024 : V) ≤ ‖n‖) :
    (ratio n + 1) * targetExcess n + ratio n * (ratio n + 1) + lowerSize n ≤
      ratio n * upperExcess n := by
  sorry

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
