module

public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.Tactic.Ring
public import AlphaCentauri.ToMathlib.Goodstein.Defs

/-!
# Goodstein's theorem

Every Goodstein sequence (`Goodstein.goodsteinSeq`) reaches `0`.

Each term `Goodstein.goodsteinSeq m k`, read in its base `k + 2`, is mapped to an ordinal
(`toOrdinal`) by replacing the base with `ω`. Bumping the base from `k + 2` to `k + 3` leaves
this ordinal unchanged (`toOrdinal_bump`), while subtracting one strictly decreases it
(`toOrdinal_strictMono`), so the ordinal sequence `seqOrd` strictly decreases as long as the
Goodstein sequence is nonzero. Ordinals are well-founded, so no such sequence is infinite, which
forces some term to `0`.
-/

@[expose] public section

namespace Goodstein

open Ordinal

variable (b : ℕ)

/-- Reads `n` in hereditary base `b` as an ordinal, replacing `b` by `ω`. Peeling the top power,
with `e = Nat.log b n`, `c = n / b ^ e`, `r = n % b ^ e`: `toOrdinal b n = ω ^ toOrdinal b e * c +
toOrdinal b r`. -/
noncomputable def toOrdinal (b n : ℕ) : Ordinal.{0} :=
  if h : n = 0 then 0
  else
    ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
      + toOrdinal b (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases eq_or_ne b 0 with rfl | hbpos
      · simp [Nat.log_zero_left]
      · exact Nat.pow_pos (Nat.pos_of_ne_zero hbpos)
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

@[simp] lemma toOrdinal_zero : toOrdinal b 0 = 0 := by rw [toOrdinal]; simp

/-- Unfolds `toOrdinal` at a nonzero argument by peeling its top power. -/
lemma toOrdinal_pos {n : ℕ} (h : n ≠ 0) :
    toOrdinal b n =
      ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
        + toOrdinal b (n % b ^ Nat.log b n) := by
  rw [toOrdinal]; simp [h]

/-- For `b ≥ 2`, `toOrdinal b` is strictly monotone, and every value is bounded by
`ω ^ (toOrdinal b (Nat.log b n) + 1)`. -/
private theorem toOrdinal_strictMono_and_bound (hb : 2 ≤ b) (n : ℕ) :
    (∀ m, m < n → toOrdinal b m < toOrdinal b n) ∧
      (n ≠ 0 → toOrdinal b n < ω ^ (toOrdinal b (Nat.log b n) + 1)) := by
  have hb1 : 1 < b := by omega
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have rb : ∀ r e', e' < n → r < b ^ e' → r < n →
        toOrdinal b r < ω ^ toOrdinal b e' := by
      intro r e' he'n hre' hrn
      rcases eq_or_ne r 0 with rfl | hr0
      · simpa using opow_pos (toOrdinal b e') omega0_pos
      · have hlogr : Nat.log b r < e' := (Nat.log_lt_iff_lt_pow hb1 hr0).2 hre'
        have h1 : toOrdinal b (Nat.log b r) < toOrdinal b e' := (ih e' he'n).1 _ hlogr
        have h2 : toOrdinal b r < ω ^ (toOrdinal b (Nat.log b r) + 1) := (ih r hrn).2 hr0
        refine h2.trans_le (opow_le_opow_right omega0_pos ?_)
        rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt h1
    constructor
    · intro m hmn
      have hn0 : n ≠ 0 := by omega
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn0
      have hc_pos : 0 < n / b ^ Nat.log b n := Nat.div_pos hbe_le hbe_pos
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := hr_lt.trans_le hbe_le
      have he_lt_n : Nat.log b n < n := Nat.log_lt_self b hn0
      have hn_eq := toOrdinal_pos b hn0
      have hrb : toOrdinal b (n % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) :=
        rb _ _ he_lt_n hr_lt hr_lt_n
      have hpos : (0 : Ordinal) < ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ) :=
        mul_pos (opow_pos _ omega0_pos) (by exact_mod_cast hc_pos)
      rcases eq_or_ne m 0 with rfl | hm0
      · rw [toOrdinal_zero, hn_eq]
        exact hpos.trans_le le_self_add
      · have hem_le : Nat.log b m ≤ Nat.log b n := Nat.log_mono_right hmn.le
        rcases lt_or_eq_of_le hem_le with hem_lt | hem_eq
        · -- `log b m < log b n`: `m`'s ordinal already sits below `ω ^ toOrdinal b (log b n)`
          have hmb : toOrdinal b m < ω ^ (toOrdinal b (Nat.log b m) + 1) := (ih m hmn).2 hm0
          have hexp : toOrdinal b (Nat.log b m) + 1 ≤ toOrdinal b (Nat.log b n) := by
            rw [← Order.succ_eq_add_one]
            exact Order.succ_le_of_lt ((ih _ he_lt_n).1 _ hem_lt)
          calc toOrdinal b m
              < ω ^ (toOrdinal b (Nat.log b m) + 1) := hmb
            _ ≤ ω ^ toOrdinal b (Nat.log b n) := opow_le_opow_right omega0_pos hexp
            _ = ω ^ toOrdinal b (Nat.log b n) * 1 := (mul_one _).symm
            _ ≤ ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ) :=
                mul_le_mul_right (by exact_mod_cast hc_pos) _
            _ ≤ toOrdinal b n := by rw [hn_eq]; exact le_self_add
        · -- equal leading exponents: compare the leading digit, then the remainder
          have hbem_pos : 0 < b ^ Nat.log b m := Nat.pow_pos (by omega)
          have hbem_le : b ^ Nat.log b m ≤ m := Nat.pow_log_le_self b hm0
          have hrm_lt : m % b ^ Nat.log b m < b ^ Nat.log b m := Nat.mod_lt _ hbem_pos
          have hm_eq := toOrdinal_pos b hm0
          rw [hm_eq, hn_eq, hem_eq]
          have hcm_le : m / b ^ Nat.log b n ≤ n / b ^ Nat.log b n := by
            rw [← hem_eq]; exact Nat.div_le_div_right hmn.le
          have hrm_lt' : m % b ^ Nat.log b n < b ^ Nat.log b n := hem_eq ▸ hrm_lt
          have hrm_lt_n : m % b ^ Nat.log b n < n := hrm_lt'.trans_le hbe_le
          have hrbm : toOrdinal b (m % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) :=
            rb _ _ he_lt_n hrm_lt' hrm_lt_n
          rcases lt_or_eq_of_le hcm_le with hcm_lt | hcm_eq
          · calc ω ^ toOrdinal b (Nat.log b n) * (m / b ^ Nat.log b n : ℕ)
                  + toOrdinal b (m % b ^ Nat.log b n)
                < ω ^ toOrdinal b (Nat.log b n) * (m / b ^ Nat.log b n : ℕ)
                  + ω ^ toOrdinal b (Nat.log b n) := (add_lt_add_iff_left _).2 hrbm
              _ = ω ^ toOrdinal b (Nat.log b n) * ((m / b ^ Nat.log b n : ℕ) + 1) := by
                    rw [mul_add_one]
              _ ≤ ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ) :=
                    mul_le_mul_right (by exact_mod_cast hcm_lt) _
              _ ≤ ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
                    + toOrdinal b (n % b ^ Nat.log b n) := le_self_add
          · have hrm_rn : m % b ^ Nat.log b n < n % b ^ Nat.log b n := by
              have em := Nat.div_add_mod m (b ^ Nat.log b n)
              have en := Nat.div_add_mod n (b ^ Nat.log b n)
              rw [← hcm_eq] at en; omega
            rw [hcm_eq]
            exact (add_lt_add_iff_left _).2 ((ih _ hr_lt_n).1 _ hrm_rn)
    · intro hn0
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn0
      have hc_lt : n / b ^ Nat.log b n < b := by
        rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']
        exact Nat.lt_pow_succ_log_self hb1 n
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := hr_lt.trans_le hbe_le
      have he_lt_n : Nat.log b n < n := Nat.log_lt_self b hn0
      have hrb : toOrdinal b (n % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) :=
        rb _ _ he_lt_n hr_lt hr_lt_n
      rw [toOrdinal_pos b hn0]
      calc ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
            + toOrdinal b (n % b ^ Nat.log b n)
          < ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
            + ω ^ toOrdinal b (Nat.log b n) := (add_lt_add_iff_left _).2 hrb
        _ = ω ^ toOrdinal b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) + 1) := by
              rw [mul_add_one]
        _ ≤ ω ^ toOrdinal b (Nat.log b n) * ω :=
              mul_le_mul_right (by rw [← Nat.cast_add_one]; exact (natCast_lt_omega0 _).le) _
        _ = ω ^ (toOrdinal b (Nat.log b n) + 1) := by rw [← opow_succ, Order.succ_eq_add_one]

theorem toOrdinal_strictMono (hb : 2 ≤ b) : StrictMono (toOrdinal b) :=
  fun m n hmn => (toOrdinal_strictMono_and_bound b hb n).1 m hmn

/-- The analogue of `toOrdinal_strictMono_and_bound` for `bump`, over `ℕ` with base `b + 1` in
place of `ω`: `bump b` is strictly monotone, with leading bound
`(b + 1) ^ (bump b (Nat.log b n) + 1)`. -/
private theorem bump_strictMono_and_bound (hb : 2 ≤ b) (n : ℕ) :
    (∀ m, m < n → bump b m < bump b n) ∧
      (n ≠ 0 → bump b n < (b + 1) ^ (bump b (Nat.log b n) + 1)) := by
  have hb1 : 1 < b := by omega
  have hb1' : 1 ≤ b + 1 := by omega
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have rb : ∀ r e', e' < n → r < b ^ e' → r < n → bump b r < (b + 1) ^ bump b e' := by
      intro r e' he'n hre' hrn
      rcases eq_or_ne r 0 with rfl | hr0
      · simp
      · have hlogr : Nat.log b r < e' := (Nat.log_lt_iff_lt_pow hb1 hr0).2 hre'
        have h1 : bump b (Nat.log b r) < bump b e' := (ih e' he'n).1 _ hlogr
        have h2 : bump b r < (b + 1) ^ (bump b (Nat.log b r) + 1) := (ih r hrn).2 hr0
        exact h2.trans_le (Nat.pow_le_pow_right hb1' h1)
    constructor
    · intro m hmn
      have hn0 : n ≠ 0 := by omega
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn0
      have hc_pos : 0 < n / b ^ Nat.log b n := Nat.div_pos hbe_le hbe_pos
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := hr_lt.trans_le hbe_le
      have he_lt_n : Nat.log b n < n := Nat.log_lt_self b hn0
      have hn_eq := bump_pos b hn0
      have hrb : bump b (n % b ^ Nat.log b n) < (b + 1) ^ bump b (Nat.log b n) :=
        rb _ _ he_lt_n hr_lt hr_lt_n
      have hpe : 0 < (b + 1) ^ bump b (Nat.log b n) := Nat.pow_pos (by omega)
      rcases eq_or_ne m 0 with rfl | hm0
      · rw [bump_zero, hn_eq]
        have := Nat.mul_pos hc_pos hpe
        omega
      · have hem_le : Nat.log b m ≤ Nat.log b n := Nat.log_mono_right hmn.le
        rcases lt_or_eq_of_le hem_le with hem_lt | hem_eq
        · have hmb : bump b m < (b + 1) ^ (bump b (Nat.log b m) + 1) := (ih m hmn).2 hm0
          have hexp : bump b (Nat.log b m) + 1 ≤ bump b (Nat.log b n) :=
            (ih _ he_lt_n).1 _ hem_lt
          calc bump b m
              < (b + 1) ^ (bump b (Nat.log b m) + 1) := hmb
            _ ≤ (b + 1) ^ bump b (Nat.log b n) := Nat.pow_le_pow_right hb1' hexp
            _ ≤ n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) :=
                  Nat.le_mul_of_pos_left _ hc_pos
            _ ≤ bump b n := by rw [hn_eq]; exact Nat.le_add_right _ _
        · have hbem_pos : 0 < b ^ Nat.log b m := Nat.pow_pos (by omega)
          have hrm_lt : m % b ^ Nat.log b m < b ^ Nat.log b m := Nat.mod_lt _ hbem_pos
          have hm_eq := bump_pos b hm0
          rw [hm_eq, hn_eq, hem_eq]
          have hcm_le : m / b ^ Nat.log b n ≤ n / b ^ Nat.log b n := by
            rw [← hem_eq]; exact Nat.div_le_div_right hmn.le
          have hrm_lt' : m % b ^ Nat.log b n < b ^ Nat.log b n := hem_eq ▸ hrm_lt
          have hrm_lt_n : m % b ^ Nat.log b n < n := hrm_lt'.trans_le hbe_le
          have hrbm : bump b (m % b ^ Nat.log b n) < (b + 1) ^ bump b (Nat.log b n) :=
            rb _ _ he_lt_n hrm_lt' hrm_lt_n
          rcases lt_or_eq_of_le hcm_le with hcm_lt | hcm_eq
          · calc m / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n)
                  + bump b (m % b ^ Nat.log b n)
                < m / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n)
                  + (b + 1) ^ bump b (Nat.log b n) := Nat.add_lt_add_left hrbm _
              _ = (m / b ^ Nat.log b n + 1) * (b + 1) ^ bump b (Nat.log b n) := by ring
              _ ≤ n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) :=
                    Nat.mul_le_mul_right _ hcm_lt
              _ ≤ n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n)
                    + bump b (n % b ^ Nat.log b n) := Nat.le_add_right _ _
          · rw [hcm_eq]
            have hrm_rn : m % b ^ Nat.log b n < n % b ^ Nat.log b n := by
              have em := Nat.div_add_mod m (b ^ Nat.log b n)
              have en := Nat.div_add_mod n (b ^ Nat.log b n)
              rw [← hcm_eq] at en; omega
            exact Nat.add_lt_add_left ((ih _ hr_lt_n).1 _ hrm_rn) _
    · intro hn0
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn0
      have hc_lt : n / b ^ Nat.log b n < b := by
        rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']
        exact Nat.lt_pow_succ_log_self hb1 n
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := hr_lt.trans_le hbe_le
      have he_lt_n : Nat.log b n < n := Nat.log_lt_self b hn0
      have hrb : bump b (n % b ^ Nat.log b n) < (b + 1) ^ bump b (Nat.log b n) :=
        rb _ _ he_lt_n hr_lt hr_lt_n
      rw [bump_pos b hn0]
      calc n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n)
          < n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n)
            + (b + 1) ^ bump b (Nat.log b n) := Nat.add_lt_add_left hrb _
        _ = (n / b ^ Nat.log b n + 1) * (b + 1) ^ bump b (Nat.log b n) := by ring
        _ ≤ (b + 1) * (b + 1) ^ bump b (Nat.log b n) := Nat.mul_le_mul_right _ (by omega)
        _ = (b + 1) ^ (bump b (Nat.log b n) + 1) := by rw [pow_succ]; ring

private lemma bump_lt_pow (hb : 2 ≤ b) {r e : ℕ} (h : r < b ^ e) :
    bump b r < (b + 1) ^ bump b e := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  · have hb1 : 1 < b := by omega
    have hlogr : Nat.log b r < e := (Nat.log_lt_iff_lt_pow hb1 hr0).2 h
    have hmono := (bump_strictMono_and_bound b hb e).1 (Nat.log b r) hlogr
    exact ((bump_strictMono_and_bound b hb r).2 hr0).trans_le
      (Nat.pow_le_pow_right (by omega) hmono)

/-- For `b ≥ 2`, bumping the base does not change the ordinal reading. -/
theorem toOrdinal_bump (hb : 2 ≤ b) (n : ℕ) : toOrdinal (b + 1) (bump b n) = toOrdinal b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hb1 : 1 < b := by omega
      set e := Nat.log b n with he
      have hbe_pos : 0 < b ^ e := Nat.pow_pos (by omega)
      have hbe_le : b ^ e ≤ n := Nat.pow_log_le_self b hn0
      have hc_pos : 0 < n / b ^ e := Nat.div_pos hbe_le hbe_pos
      have hc_lt : n / b ^ e < b := by
        rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']; exact Nat.lt_pow_succ_log_self hb1 n
      have hr_lt : n % b ^ e < b ^ e := Nat.mod_lt _ hbe_pos
      have he_lt_n : e < n := Nat.log_lt_self b hn0
      have hr_lt_n : n % b ^ e < n := hr_lt.trans_le hbe_le
      have hBE_pos : 0 < (b + 1) ^ bump b e := Nat.pow_pos (by omega)
      have hR_lt : bump b (n % b ^ e) < (b + 1) ^ bump b e := bump_lt_pow b hb hr_lt
      have hbump_eq : bump b n = n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) :=
        bump_pos b hn0
      have hbn_pos : 0 < bump b n := by
        rw [hbump_eq]
        have := Nat.mul_pos hc_pos hBE_pos
        omega
      have hlog : Nat.log (b + 1) (bump b n) = bump b e := by
        rw [hbump_eq]
        apply Nat.log_eq_of_pow_le_of_lt_pow
        · calc (b + 1) ^ bump b e
              = 1 * (b + 1) ^ bump b e := (one_mul _).symm
            _ ≤ n / b ^ e * (b + 1) ^ bump b e := Nat.mul_le_mul_right _ hc_pos
            _ ≤ n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := Nat.le_add_right _ _
        · calc n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e)
              < n / b ^ e * (b + 1) ^ bump b e + (b + 1) ^ bump b e := by omega
            _ = (n / b ^ e + 1) * (b + 1) ^ bump b e := by ring
            _ ≤ (b + 1) * (b + 1) ^ bump b e := Nat.mul_le_mul_right _ (by omega)
            _ = (b + 1) ^ (bump b e + 1) := by rw [pow_succ]; ring
      have hdiv : bump b n / (b + 1) ^ bump b e = n / b ^ e := by
        rw [hbump_eq, mul_comm (n / b ^ e), Nat.mul_add_div hBE_pos, Nat.div_eq_of_lt hR_lt,
          Nat.add_zero]
      have hmod : bump b n % (b + 1) ^ bump b e = bump b (n % b ^ e) := by
        rw [hbump_eq, mul_comm (n / b ^ e), Nat.mul_add_mod, Nat.mod_eq_of_lt hR_lt]
      have key : toOrdinal (b + 1) (bump b n)
          = ω ^ toOrdinal (b + 1) (bump b e) * (n / b ^ e : ℕ)
            + toOrdinal (b + 1) (bump b (n % b ^ e)) := by
        conv_lhs => rw [toOrdinal_pos (b + 1) (by omega)]
        rw [hlog, hdiv, hmod]
      rw [key, ih e he_lt_n, ih (n % b ^ e) hr_lt_n]
      exact (toOrdinal_pos b hn0).symm

variable (m k : ℕ)

/-- The ordinal value of the `k`-th Goodstein term, read in its base `k + 2`. -/
noncomputable def seqOrd : Ordinal.{0} := toOrdinal (k + 2) (goodsteinSeq m k)

/-- One Goodstein step strictly lowers the ordinal value while the term is nonzero. -/
theorem seqOrd_step (h : goodsteinSeq m k ≠ 0) : seqOrd m (k + 1) < seqOrd m k := by
  have hstep : goodsteinSeq m (k + 1) = bump (k + 2) (goodsteinSeq m k) - 1 := rfl
  have hMpos : 0 < bump (k + 2) (goodsteinSeq m k) := by
    rw [bump_pos (k + 2) h]
    have h1 : 0 < goodsteinSeq m k / (k + 2) ^ Nat.log (k + 2) (goodsteinSeq m k) :=
      Nat.div_pos (Nat.pow_log_le_self _ h) (Nat.pow_pos (by omega))
    have h2 : 0 < (k + 2 + 1) ^ bump (k + 2) (Nat.log (k + 2) (goodsteinSeq m k)) :=
      Nat.pow_pos (by omega)
    have := Nat.mul_pos h1 h2
    omega
  have hmono := toOrdinal_strictMono (k + 2 + 1) (by omega)
    (show bump (k + 2) (goodsteinSeq m k) - 1 < bump (k + 2) (goodsteinSeq m k) by omega)
  have hinv := toOrdinal_bump (k + 2) (by omega) (goodsteinSeq m k)
  unfold seqOrd
  rw [hstep, show k + 1 + 2 = k + 2 + 1 from by ring]
  exact hmono.trans_le hinv.le

/-- **Goodstein's theorem.** Every Goodstein sequence reaches `0`. -/
theorem goodstein_terminates (m : ℕ) : ∃ N, goodsteinSeq m N = 0 := by
  by_contra hcon
  rw [not_exists] at hcon
  obtain ⟨a, ⟨N, hNa⟩, hmin⟩ :=
    Ordinal.lt_wf.has_min (Set.range (seqOrd m)) ⟨seqOrd m 0, 0, rfl⟩
  exact hmin (seqOrd m (N + 1)) ⟨N + 1, rfl⟩ (hNa ▸ seqOrd_step m N (hcon N))

/-- The **Goodstein length** of `m`: the least step at which the Goodstein sequence seeded at
`m` reaches `0`. Total by `goodstein_terminates`. -/
def goodsteinLength (m : ℕ) : ℕ := Nat.find (goodstein_terminates m)

lemma goodsteinSeq_goodsteinLength (m : ℕ) : goodsteinSeq m (goodsteinLength m) = 0 :=
  Nat.find_spec (goodstein_terminates m)

lemma goodsteinLength_le {m N : ℕ} (h : goodsteinSeq m N = 0) : goodsteinLength m ≤ N :=
  Nat.find_le h

lemma goodsteinSeq_ne_zero_of_lt {m N : ℕ} (h : N < goodsteinLength m) : goodsteinSeq m N ≠ 0 :=
  Nat.find_min (goodstein_terminates m) h

end Goodstein
