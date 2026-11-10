module

public import AlphaCentauri.Model.OpenInduction
public import AlphaCentauri.NumberTheory.FermatLastTheorem.Basic

/-!
# Case I of Fermat's Last Theorem in $\mathsf{IOpen}$ for exponents $3$ and $5$

$\mathsf{IOpen}$ proves Case I of Fermat's Last Theorem for the exponents $3$ and $5$.

- [Smi92b]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] {N n : ℕ}

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

lemma provable_fermatLastTheoremCaseOne_IOpen_of_forall (hn : 0 < n)
    (H : ∀ a < n ^ 2, ∀ b < n ^ 2, ∀ c < n ^ 2, (a ^ n + b ^ n) % n ^ 2 = c ^ n % n ^ 2 →
      n ∣ a * b * c) :
    𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseOne n := by
  apply complete
  intro (V : Type) _ hV
  suffices ∀ x y z : V, x ^ n + y ^ n = z ^ n → (n : V) ∣ x * y * z by
    simpa [models_iff, fermatLastTheoremCaseOne, numeral_eq_natCast]
  intro x y z h
  have hN : 0 < n ^ 2 := by positivity
  have hnN : n ∣ n ^ 2 := dvd_pow_self n two_ne_zero
  generalize n ^ 2 = N at hN hnN H
  have hN' : (0 : V) < N := by exact_mod_cast hN
  have hmod (m : ℕ) (u : V) : ((m : V) + N * u) % N = ((m % N : ℕ) : V) := by
    have : (m : V) = N * ↑(m / N) + ↑(m % N) := by exact_mod_cast (Nat.div_add_mod m N).symm
    rw [mod_add_mul' _ _ hN', this, mod_mul_add' _ _ hN',
      mod_eq_self_of_lt (by exact_mod_cast Nat.mod_lt _ hN)]
  obtain ⟨a, ha, qx, rfl⟩ := exists_nat_lt_add_mul hN x
  obtain ⟨b, hb, qy, rfl⟩ := exists_nat_lt_add_mul hN y
  obtain ⟨c, hc, qz, rfl⟩ := exists_nat_lt_add_mul hN z
  obtain ⟨ux, hux⟩ := exists_pow_add_mul_eq (a : V) N qx n
  obtain ⟨uy, huy⟩ := exists_pow_add_mul_eq (b : V) N qy n
  obtain ⟨uz, huz⟩ := exists_pow_add_mul_eq (c : V) N qz n
  have h₁ : ((a ^ n + b ^ n : ℕ) : V) + N * (ux + uy) = ((c ^ n : ℕ) : V) + N * uz := by
    push_cast
    calc
      _ = (a ^ n + N * ux) + (b ^ n + N * uy) := by ring
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

/-- $\mathsf{IOpen}$ proves Case I of Fermat's Last Theorem for exponent $3$.
- [Smi92b, Lemma 3.6] -/
theorem provable_fermatLastTheoremCaseOne_three_IOpen : 𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseOne 3 :=
  provable_fermatLastTheoremCaseOne_IOpen_of_forall (by norm_num) (by decide +kernel)

/-- $\mathsf{IOpen}$ proves Case I of Fermat's Last Theorem for exponent $5$.
- [Smi92b, Lemma 3.6] -/
theorem provable_fermatLastTheoremCaseOne_five_IOpen : 𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseOne 5 :=
  provable_fermatLastTheoremCaseOne_IOpen_of_forall (by norm_num) (by decide +kernel)

end FFL.FirstOrder.Arithmetic
