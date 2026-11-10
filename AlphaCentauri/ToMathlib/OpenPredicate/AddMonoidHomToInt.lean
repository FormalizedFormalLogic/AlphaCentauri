module

public import AlphaCentauri.ToMathlib.OpenPredicate
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Additive homomorphisms to `ℤ` from a ring with the least number principle

Let `R` be a discretely ordered commutative ring satisfying `LeastNumberPrinciple` with an element
above every natural number. Every additive homomorphism `R →+ ℤ` is zero, so `ℤ` is not a direct
summand of the additive group of `R`.

- [Car16, Lemma 5]
-/

@[expose] public section

namespace OpenPredicate

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [DiscretelyOrdered R]

lemma DiscretelyOrdered.exists_eq_natCast {r : R} (h₀ : 0 ≤ r) {q : ℕ} (h : r < q) :
    ∃ k < q, r = k := by
  induction q with
  | zero => simp at h; linarith
  | succ q ih =>
    rcases lt_or_ge r q with h' | h'
    · obtain ⟨k, hk, rfl⟩ := ih h'
      use k
      exact ⟨by omega, rfl⟩
    · have := DiscretelyOrdered.one_le_of_pos (q + 1 - r) (by push_cast at h; linarith)
      use q
      exact ⟨by omega, by linarith⟩

namespace LeastNumberPrinciple

variable (hL : LeastNumberPrinciple R) (f : R →+ ℤ)

include hL

/-- Every positive element is `a * b` with `a` odd and `b` not divisible by `3`. -/
lemma exists_eq_mul_not_three_dvd {d : R} (hd : 0 < d) :
    ∃ a b j : R, d = a * b ∧ a = 2 * j + 1 ∧ ¬(3 : R) ∣ b := by
  let Φ : (Fin 3 → R) → Prop := fun w ↦ d = w 1 * w 0 ∧ w 1 = 2 * w 2 + 1 ∧ 0 ≤ w 2
  have hB (x : R) : BoundedExists (d + 1) Φ x ↔
      ∃ a j : R, |a| < d + 1 ∧ |j| < d + 1 ∧ d = a * x ∧ a = 2 * j + 1 ∧ 0 ≤ j := by
    simp only [BoundedExists, Φ, Fin.forall_fin_succ, Fin.exists_fin_succ_pi,
      Fin.exists_fin_zero_pi]
    constructor
    · rintro ⟨a, j, ⟨h₁, h₂, -⟩, h₃, h₄, h₅⟩
      use a, j
      exact ⟨h₁, h₂, h₃, h₄, h₅⟩
    · rintro ⟨a, j, h₁, h₂, h₃, h₄, h₅⟩
      use a, j
      exact ⟨⟨h₁, h₂, finZeroElim⟩, h₃, h₄, h₅⟩
  obtain ⟨b, hb₀, hb, hmin⟩ := hL 2 Φ (by is_open) (d + 1) d hd.le <| (hB d).2 <| by
    use 1, 0
    simp [hd]
    linarith
  obtain ⟨a, j, -, -, e, ha, hj⟩ := (hB b).1 hb
  use a, b, j
  and_intros
  · exact e
  · exact ha
  rintro ⟨b₁, rfl⟩
  have hb₁ : 0 < b₁ := by
    rcases hb₀.eq_or_lt with h | h
    · simp [← h] at e; linarith
    · linarith
  have := DiscretelyOrdered.one_le_of_pos _ hb₁
  apply hmin b₁ hb₁.le (by linarith)
  rw [hB]
  use 3 * a, 3 * j + 1
  and_intros
  · rw [abs_of_nonneg (by linarith)]; nlinarith
  · rw [abs_of_nonneg (by linarith)]; nlinarith
  · rw [e]; ring
  · rw [ha]; ring
  · linarith

/-- Every additive homomorphism to `ℤ` from a nonstandard discretely ordered ring with the least
number principle is zero.
- [Car16, Lemma 5] -/
theorem addMonoidHom_eq_zero (hx : ∃ x : R, ∀ n : ℕ, (n : R) < x) : f = 0 := by
  have hmul (c : ℤ) (a : R) : f (c * a) = c * f a := by
    simp [← zsmul_eq_mul, map_zsmul]
  have hdiv (a : R) {q : ℕ} (hq : 0 < q) :
      ∃ (b : R) (k : ℕ), k < q ∧ a = q * b + k ∧ f a = q * f b + k * f 1 := by
    obtain ⟨b, r, e, hr₀, hr⟩ := exists_ediv hL a q (by exact_mod_cast hq)
    obtain ⟨k, hk, rfl⟩ := DiscretelyOrdered.exists_eq_natCast hr₀ hr
    rw [mul_comm] at e
    use b, k
    and_intros
    · exact hk
    · exact e
    · have h₁ : f (q * b) = q * f b := by simpa using hmul q b
      have h₂ : f k = k * f 1 := by simpa using hmul k 1
      rw [e, map_add, h₁, h₂]
  have hpow {m : ℤ} (h : ∀ n : ℕ, (2 : ℤ) ^ n ∣ m) : m = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h m.natAbs) (by simpa using Nat.lt_two_pow_self)
  by_cases hc : f 1 = 0
  · ext a
    apply hpow
    intro n
    obtain ⟨b, k, -, -, h⟩ := hdiv a (q := 2 ^ n) (by positivity)
    simp [h, hc]
  have hker {a : R} (ha : f a = 0) {q : ℕ} (hq : 0 < q) : (q : R) ∣ a := by
    obtain ⟨b, k, -, e, h⟩ := hdiv a (q := q * (f 1).natAbs) (by positivity)
    have : q * (f 1).natAbs ∣ k * (f 1).natAbs := by
      have : ((q * (f 1).natAbs : ℕ) : ℤ) ∣ k * f 1 := ⟨-f b, by linarith⟩
      simpa [Int.natAbs_mul, Int.natAbs_abs] using Int.natAbs_dvd_natAbs.2 this
    obtain ⟨m, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right (Int.natAbs_pos.2 hc) this
    use (f 1).natAbs * b + m
    rw [e]
    push_cast
    ring
  obtain ⟨x, hx⟩ := hx
  set h := (f 1 : R) * x - (f x : R)
  have hfh : f h = 0 := by
    have : f (f x : R) = f x * f 1 := by simpa using hmul (f x) 1
    rw [map_sub, hmul, this, mul_comm, sub_self]
  have hh : h ≠ 0 := by
    intro h0
    have hx₀ : 0 < x := by simpa using hx 0
    have hc₁ : (1 : R) ≤ |(f 1 : R)| := by exact_mod_cast Int.one_le_abs hc
    have hlt : |((f x : ℤ) : R)| < x := by simpa [Nat.cast_natAbs] using hx (f x).natAbs
    have : |(f 1 : R) * x| = |((f x : ℤ) : R)| := by rw [sub_eq_zero.1 h0]
    rw [abs_mul, abs_of_pos hx₀] at this
    nlinarith
  have hd : 0 < |h| := abs_pos.2 hh
  have hfd : f |h| = 0 := by
    rcases abs_cases h with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e, hfh]
  obtain ⟨a, b, j, e, ha, hb⟩ := exists_eq_mul_not_three_dvd hL hd
  have hcop : IsCoprime (2 : R) a := by
    use -j, 1
    rw [ha]
    ring
  have hfb : f b = 0 := by
    apply hpow
    intro n
    obtain ⟨c, rfl⟩ := hcop.pow_left.dvd_of_dvd_mul_left
      (e ▸ (by simpa using hker hfd (q := 2 ^ n) (by positivity)) : (2 : R) ^ n ∣ a * b)
    use f c
    simpa using hmul (2 ^ n) c
  exact (hb <| by simpa using hker hfb (q := 3) (by norm_num)).elim

end LeastNumberPrinciple

end OpenPredicate
