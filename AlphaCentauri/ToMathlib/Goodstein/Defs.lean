module

public import Mathlib.Data.Nat.Log

/-!
# Goodstein sequences

For a base `b ≥ 2`, the hereditary base-`b` representation of `n` writes `n` in base `b`, then
rewrites every exponent in base `b`, recursively. `bump b n` replaces every occurrence of the
base `b` in this representation by `b + 1`. The Goodstein sequence seeded at `m` bumps the base
by one at each step and subtracts one.
-/

@[expose] public section

namespace Goodstein

/-- The base read at step `k` of a Goodstein sequence. -/
def base (k : ℕ) : ℕ := k + 2

/-- Reads `n` in hereditary base `b` and replaces every occurrence of `b` by `b + 1`. Peeling the
top power, with `e = Nat.log b n`, `c = n / b ^ e`, `r = n % b ^ e`:
`bump b n = c * (b + 1) ^ bump b e + bump b r`, and `bump b 0 = 0`. -/
def bump (b n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases eq_or_ne b 0 with rfl | hbpos
      · simp [Nat.log_zero_left]
      · exact Nat.pow_pos (Nat.pos_of_ne_zero hbpos)
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

@[simp] lemma bump_zero (b : ℕ) : bump b 0 = 0 := by rw [bump]; simp

/-- Unfolds `bump` at a nonzero argument by peeling its top power. -/
lemma bump_pos (b : ℕ) {n : ℕ} (h : n ≠ 0) :
    bump b n =
      n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n) := by
  rw [bump]; simp [h]

/-- The **Goodstein sequence** seeded at `m`: `goodsteinSeq m 0 = m`, and step `k + 1` reads
`goodsteinSeq m k` in hereditary base `k + 2`, bumps the base to `k + 3`, and subtracts one. -/
def goodsteinSeq (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => bump (base k) (goodsteinSeq m k) - 1

end Goodstein
