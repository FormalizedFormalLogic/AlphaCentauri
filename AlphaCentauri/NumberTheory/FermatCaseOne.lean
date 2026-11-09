module

public import AlphaCentauri.NumberTheory.FLT3
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-!
# Case I of Fermat's Last Theorem for exponents $3$ and $5$ in $\mathsf{IOpen}$

In a model of $\mathsf{IOpen}$ every element is a standard remainder modulo $n^2$ plus a multiple of
$n^2$, so a solution of $x^n + y^n = z^n$ reduces to a solution of the congruence
$a^n + b^n \equiv c^n \pmod{n^2}$ in the standard remainders, which is decided by computation.

- [Smi92b, §2, Lemma 3.6]
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
  exact ⟨a, by exact_mod_cast hr, _, hx.trans (add_comm _ _)⟩

lemma dvd_mul_mul_of_pow_add_pow_eq (hN : 0 < N) (hnN : n ∣ N)
    (H : ∀ a < N, ∀ b < N, ∀ c < N, (a ^ e + b ^ e) % N = c ^ e % N → n ∣ a * b * c)
    {x y z : V} (h : x ^ e + y ^ e = z ^ e) : (n : V) ∣ x * y * z := by
  obtain ⟨a, ha, qx, rfl⟩ := exists_nat_lt_add_mul hN x
  obtain ⟨b, hb, qy, rfl⟩ := exists_nat_lt_add_mul hN y
  obtain ⟨c, hc, qz, rfl⟩ := exists_nat_lt_add_mul hN z
  obtain ⟨ux, hux⟩ := exists_pow_add_mul_eq (a : V) N qx e
  obtain ⟨uy, huy⟩ := exists_pow_add_mul_eq (b : V) N qy e
  obtain ⟨uz, huz⟩ := exists_pow_add_mul_eq (c : V) N qz e
  rw [hux, huy, huz] at h
  have e₁ : (N : V) * ↑((a ^ e + b ^ e) / N) + ↑((a ^ e + b ^ e) % N) = a ^ e + b ^ e := by
    exact_mod_cast Nat.div_add_mod _ N
  have e₂ : (N : V) * ↑(c ^ e / N) + ↑(c ^ e % N) = c ^ e := by
    exact_mod_cast Nat.div_add_mod _ N
  have key : (N : V) * (↑((a ^ e + b ^ e) / N) + ux + uy) + ↑((a ^ e + b ^ e) % N) =
      N * (↑(c ^ e / N) + uz) + ↑(c ^ e % N) := by
    calc
      _ = ((N : V) * ↑((a ^ e + b ^ e) / N) + ↑((a ^ e + b ^ e) % N)) + N * (ux + uy) := by ring
      _ = (a ^ e + N * ux) + (b ^ e + N * uy) := by rw [e₁]; ring
      _ = c ^ e + N * uz := h
      _ = _ := by rw [← e₂]; ring
  have hlt₁ : (((a ^ e + b ^ e) % N : ℕ) : V) < N := by exact_mod_cast Nat.mod_lt _ hN
  have hlt₂ : ((c ^ e % N : ℕ) : V) < N := by exact_mod_cast Nat.mod_lt _ hN
  have hq := congrArg (· / (N : V)) key
  simp only [div_mul_add' _ _ hlt₁, div_mul_add' _ _ hlt₂] at hq
  rw [hq] at key
  have hr := add_left_cancel key
  obtain ⟨d, hd⟩ := H a ha b hb c hc (by exact_mod_cast hr)
  obtain ⟨m, hm⟩ := hnN
  have hd' : (a : V) * b * c = n * d := by exact_mod_cast congrArg (Nat.cast (R := V)) hd
  have hm' : (N : V) = n * m := by exact_mod_cast congrArg (Nat.cast (R := V)) hm
  use d + m * (qx * b * c + a * qy * c + a * b * qz + N * (qx * qy * c + qx * b * qz + a * qy * qz)
    + N * N * qx * qy * qz)
  calc
    _ = (a : V) * b * c + N * (qx * b * c + a * qy * c + a * b * qz +
        N * (qx * qy * c + qx * b * qz + a * qy * qz) + N * N * qx * qy * qz) := by ring
    _ = _ := by rw [hd', hm']; ring

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
- [Smi92b, §2, Lemma 3.6] -/
theorem provable_fermatLastTheoremCaseOne_three_IOpen : 𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseOne 3 :=
  provable_fermatLastTheoremCaseOne_IOpen_of_forall (by norm_num) (by decide +kernel)

/-- $\mathsf{IOpen}$ proves Case I of Fermat's Last Theorem for exponent $5$.
- [Smi92b, §2, Lemma 3.6] -/
theorem provable_fermatLastTheoremCaseOne_five_IOpen : 𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseOne 5 :=
  provable_fermatLastTheoremCaseOne_IOpen_of_forall (by norm_num) (by decide +kernel)

end FFL.FirstOrder.Arithmetic
