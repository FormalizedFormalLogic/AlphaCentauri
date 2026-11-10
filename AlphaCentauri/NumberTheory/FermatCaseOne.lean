module

public import AlphaCentauri.Model.NonnegativePart
public import AlphaCentauri.Model.OpenInduction
public import AlphaCentauri.NumberTheory.FLT3
public import AlphaCentauri.ToMathlib.PadicIntegralPolynomial
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.NumberTheory.Padics.Hensel

/-!
# Case I of Fermat's Last Theorem for exponents $3$ and $5$ in $\mathsf{IOpen}$

In a model of $\mathsf{IOpen}$ every element is a standard remainder modulo $n^2$ plus a multiple of
$n^2$, so a solution of $x^n + y^n = z^n$ reduces to a solution of the congruence
$a^n + b^n \equiv c^n \pmod{n^2}$ in the standard remainders, which is decided by computation.

- [Smi92b, Lemma 3.6]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] {N n e : ℕ}

lemma exists_pow_add_mul_eq {R : Type*} [CommSemiring R] (a m k : R) (e : ℕ) :
    ∃ u, (a + m * k) ^ e = a ^ e + m * u := by
  induction e with
  | zero => use 0; simp
  | succ e ih =>
    obtain ⟨u, hu⟩ := ih
    use a ^ e * k + u * a + m * u * k
    rw [pow_succ, hu]
    ring

lemma exists_nat_lt_add_mul (hN : 0 < N) (x : V) : ∃ a < N, ∃ q, x = a + N * q := by
  have hN' : (0 : V) < N := by exact_mod_cast hN
  obtain ⟨r, hr, hx⟩ := eq_mul_div_add_of_pos x hN'
  obtain ⟨a, rfl⟩ := eq_nat_of_lt_nat hr
  use a
  and_intros
  · exact_mod_cast hr
  · exact ⟨_, hx.trans (add_comm _ _)⟩

lemma dvd_mul_mul_of_pow_add_pow_eq (hN : 0 < N) (hnN : n ∣ N)
    (H : ∀ a < N, ∀ b < N, ∀ c < N, (a ^ e + b ^ e) % N = c ^ e % N → n ∣ a * b * c)
    {x y z : V} (h : x ^ e + y ^ e = z ^ e) : (n : V) ∣ x * y * z := by
  have hN' : (0 : V) < N := by exact_mod_cast hN
  have hmod (m : ℕ) (u : V) : ((m : V) + N * u) % N = ((m % N : ℕ) : V) := by
    have : (m : V) = N * ↑(m / N) + ↑(m % N) := by exact_mod_cast (Nat.div_add_mod m N).symm
    rw [mod_add_mul' _ _ hN', this, mod_mul_add' _ _ hN',
      mod_eq_self_of_lt (by exact_mod_cast Nat.mod_lt _ hN)]
  obtain ⟨a, ha, qx, rfl⟩ := exists_nat_lt_add_mul hN x
  obtain ⟨b, hb, qy, rfl⟩ := exists_nat_lt_add_mul hN y
  obtain ⟨c, hc, qz, rfl⟩ := exists_nat_lt_add_mul hN z
  obtain ⟨ux, hux⟩ := exists_pow_add_mul_eq (a : V) N qx e
  obtain ⟨uy, huy⟩ := exists_pow_add_mul_eq (b : V) N qy e
  obtain ⟨uz, huz⟩ := exists_pow_add_mul_eq (c : V) N qz e
  have h₁ : ((a ^ e + b ^ e : ℕ) : V) + N * (ux + uy) = ((c ^ e : ℕ) : V) + N * uz := by
    push_cast
    calc
      _ = (a ^ e + N * ux) + (b ^ e + N * uy) := by ring
      _ = _ := by rw [← hux, ← huy, ← huz, h]
  have h₂ := (hmod _ _).symm.trans <| (congrArg (· % (N : V)) h₁).trans (hmod _ _)
  have h₃ : (n : V) ∣ a * b * c := by
    exact_mod_cast Nat.cast_dvd_cast (H a ha b hb c hc (by exact_mod_cast h₂))
  have h₄ : (n : V) ∣ N := Nat.cast_dvd_cast hnN
  calc
    _ ∣ (a : V) * b * c + N * (qx * b * c + a * qy * c + a * b * qz +
        N * (qx * qy * c + qx * b * qz + a * qy * qz) + N * N * qx * qy * qz) :=
      h₃.add <| h₄.mul_right _
    _ = _ := by ring

lemma provable_fermatLastTheoremCaseOne_IOpen_of_forall (hn : 0 < n)
    (H : ∀ a < n ^ 2, ∀ b < n ^ 2, ∀ c < n ^ 2, (a ^ n + b ^ n) % n ^ 2 = c ^ n % n ^ 2 →
      n ∣ a * b * c) :
    𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseOne n := by
  apply complete
  intro (V : Type) _ hV
  suffices ∀ x y z : V, x ^ n + y ^ n = z ^ n → (n : V) ∣ x * y * z by
    simpa [models_iff, fermatLastTheoremCaseOne, numeral_eq_natCast]
  intro x y z h
  exact dvd_mul_mul_of_pow_add_pow_eq (by positivity) (dvd_pow_self n two_ne_zero) H h

/-- $\mathsf{IOpen}$ proves Case I of Fermat's Last Theorem for exponent $3$.
- [Smi92b, Lemma 3.6] -/
theorem provable_fermatLastTheoremCaseOne_three_IOpen : 𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseOne 3 :=
  provable_fermatLastTheoremCaseOne_IOpen_of_forall (by norm_num) (by decide +kernel)

/-- $\mathsf{IOpen}$ proves Case I of Fermat's Last Theorem for exponent $5$.
- [Smi92b, Lemma 3.6] -/
theorem provable_fermatLastTheoremCaseOne_five_IOpen : 𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseOne 5 :=
  provable_fermatLastTheoremCaseOne_IOpen_of_forall (by norm_num) (by decide +kernel)

/-- A model of $\mathsf{ZR}$ with a solution of $x^n + y^n = z^n$ for which $x y z$ leaves a
non-zero remainder modulo $n$ embeds into a model of $\mathsf{IOpen}$ refuting Case I of Fermat's
Last Theorem for exponent $n$.
- [Wil78, Lemma 3.2] -/
lemma not_provable_fermatLastTheoremCaseOne_IOpen_of_models_ZRing {M : Type} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* ZRing] {r : ℕ} (hr₀ : 0 < r) (hr : r < n) {x y z w : M}
    (h : x ^ n + y ^ n = z ^ n) (hxyz : x * y * z = w * n + r) :
    𝗜𝗢𝗽𝗲𝗻 ⊬ fermatLastTheoremCaseOne n := by
  obtain ⟨W, _, hW, ⟨Θ⟩⟩ := exists_embedding_models_IOpen M
  intro hp
  have hC : ∀ a b c : W, a ^ n + b ^ n = c ^ n → (n : W) ∣ a * b * c := by
    simpa [models_iff, fermatLastTheoremCaseOne, numeral_eq_natCast] using
      models_of_provable hW hp
  have hzero : Θ 0 = 0 := by
    simpa [Function.comp_def] using Tarski.Structure.HomClass.func Θ Language.Zero.zero ![]
  have hone : Θ 1 = 1 := by
    simpa [Function.comp_def] using Tarski.Structure.HomClass.func Θ Language.One.one ![]
  have hadd (a b : M) : Θ (a + b) = Θ a + Θ b := by
    simpa [Function.comp_def] using Tarski.Structure.HomClass.func Θ Language.Add.add ![a, b]
  have hmul (a b : M) : Θ (a * b) = Θ a * Θ b := by
    simpa [Function.comp_def] using Tarski.Structure.HomClass.func Θ Language.Mul.mul ![a, b]
  have hpow (a : M) (k : ℕ) : Θ (a ^ k) = Θ a ^ k := by
    induction k with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hcast (k : ℕ) : Θ k = k := by
    induction k with
    | zero => rw [Nat.cast_zero, Nat.cast_zero, hzero]
    | succ k ih => rw [Nat.cast_succ, hadd, ih, hone, Nat.cast_succ]
  have e₁ : Θ x ^ n + Θ y ^ n = Θ z ^ n := by rw [← hpow, ← hpow, ← hpow, ← hadd, h]
  have e₂ : Θ x * Θ y * Θ z = Θ w * n + r := by
    rw [← hmul, ← hmul, ← hcast, ← hcast, ← hmul, ← hadd, hxyz]
  have := hC _ _ _ e₁
  rw [e₂, ← mod_eq_zero_iff_dvd, mod_mul_add_of_lt _ _ (by exact_mod_cast hr)] at this
  exact hr₀.ne' (by exact_mod_cast this)

end FFL.FirstOrder.Arithmetic

open Polynomial

lemma irreducible_X_pow_seven_sub_C : Irreducible (X ^ 7 - C (5 ^ 7 - 1 : ℚ)) := by
  apply X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 7)
  intro b hb
  have hden : b.den = 1 := by
    have := Rat.den_pow b 7
    rw [hb] at this
    simpa using this.symm
  rw [← Rat.coe_int_num_of_den_eq_one hden] at hb
  have hn : b.num ^ 7 = 5 ^ 7 - 1 := by exact_mod_cast hb
  have h₁ : b.num < 5 := by
    by_contra h
    have : (5 : ℤ) ^ 7 ≤ b.num ^ 7 := pow_le_pow_left₀ (by norm_num) (not_lt.mp h) 7
    omega
  have h₂ : 4 < b.num := by
    by_contra h
    have : b.num ^ 7 ≤ 4 ^ 7 := (Odd.pow_le_pow (by decide)).mpr (not_lt.mp h)
    omega
  omega

lemma exists_padicInt_pow_seven_eq [Fact (Nat.Prime 7)] :
    ∃ y : ℤ_[7], y ^ 7 = 5 ^ 7 - 1 ∧ (7 : ℤ_[7]) ∣ y - 4 := by
  have h₇ : ‖(7 : ℤ_[7])‖ = 7⁻¹ := by exact_mod_cast PadicInt.norm_p (p := 7)
  have hu (k : ℤ) (hk : ¬(7 : ℤ) ∣ k) : ‖(k : ℤ_[7])‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _)
      (not_lt.mp ((PadicInt.norm_int_lt_one_iff_dvd k).not.mpr hk))
  have e₁ : (X ^ 7 - C (5 ^ 7 - 1) : ℤ_[7][X]).eval 4 = 7 ^ 3 * ((-180 : ℤ) : ℤ_[7]) := by
    simp only [eval_sub, eval_pow, eval_X, eval_C]
    norm_num
  have e₂ : (derivative (X ^ 7 - C (5 ^ 7 - 1) : ℤ_[7][X])).eval 4 = 7 * ((4096 : ℤ) : ℤ_[7]) := by
    rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero]
    simp
    norm_num
  have hd : ‖(derivative (X ^ 7 - C (5 ^ 7 - 1) : ℤ_[7][X])).eval 4‖ = 7⁻¹ := by
    rw [e₂, norm_mul, h₇, hu _ (by decide), mul_one]
  obtain ⟨y, hy, hy₄, -⟩ := hensels_lemma (R := ℤ_[7]) (F := X ^ 7 - C (5 ^ 7 - 1)) (a := 4) <| by
    change ‖eval 4 _‖ < ‖eval 4 _‖ ^ 2
    rw [hd, e₁, norm_mul, norm_pow, h₇, hu _ (by decide)]
    norm_num
  simp only [coe_aeval_eq_eval] at hy hy₄
  rw [hd] at hy₄
  use y
  and_intros
  · simpa [sub_eq_zero] using hy
  · exact (PadicInt.norm_lt_one_iff_dvd _).mp (hy₄.trans (by norm_num))

