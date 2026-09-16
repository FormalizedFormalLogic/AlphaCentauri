module

public import AlphaCentauri.ToMathlib.Ordinal.Bounds

/-!
# The `ω`-tower

The `ω`-tower `Ordinal.omegaTower c α`, which iterates `ω ^ ·` on `α` `c` times, and its
`ε₀`-closure.
-/

@[expose] public section

namespace Ordinal

open scoped Ordinal

/-- The **`ω`-tower** `ω_c^α`: `ω ^ ·` iterated `c` times over `α`.

- [Tow20, Definition 19.8] -/
noncomputable def omegaTower : ℕ → Ordinal → Ordinal
  | 0, a => a
  | c + 1, a => omegaTower c (ω ^ a)

variable {a : Ordinal}

@[simp, grind =] lemma omegaTower_zero : omegaTower 0 a = a := rfl

@[simp, grind =] lemma omegaTower_one : omegaTower 1 a = ω ^ a := rfl

@[grind =] lemma omegaTower_succ (c : ℕ) : omegaTower (c + 1) a = omegaTower c (ω ^ a) := rfl

lemma omega0_opow_lt_epsilon0 (h : a < ε₀) : ω ^ a < ε₀ := by
  obtain ⟨n, hn⟩ := lt_epsilon_zero.mp h
  refine lt_trans ?_ (iterate_omega0_opow_lt_epsilon_zero (n + 1))
  rw [Function.iterate_succ_apply']
  exact (opow_lt_opow_iff_right one_lt_omega0).mpr hn

lemma omegaTower_lt_epsilon0 (c : ℕ) (h : a < ε₀) : omegaTower c a < ε₀ := by
  induction c generalizing a with
  | zero => simpa using h
  | succ c ih => simpa [omegaTower_succ] using ih (omega0_opow_lt_epsilon0 h)

end Ordinal
