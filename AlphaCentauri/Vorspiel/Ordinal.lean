module

public import Mathlib.SetTheory.Ordinal.Principal
public import Mathlib.SetTheory.Ordinal.Veblen

/-!
# Ordinal arithmetic for cut elimination

The `ω`-tower `Ordinal.omegaTower c α` and ordinal bounds used in cut elimination.
-/

@[expose] public section

namespace Ordinal

open scoped Ordinal

variable (a b : Ordinal) (f : ℕ → Ordinal)

section Principal

variable {a} {θ γ δ : Ordinal}

/-- `ω ^ θ` is nontrivial as soon as `θ` is. -/
lemma one_lt_omega0_opow (h : 0 < θ) : 1 < ω ^ θ := by
  simpa using (opow_lt_opow_iff_right one_lt_omega0 (b := 0) (c := θ)).mpr h

/-- Ordinals below `ω ^ θ` are closed under addition. -/
lemma add_lt_omega0_opow (hγ : γ < ω ^ θ) (hδ : δ < ω ^ θ) : γ + δ < ω ^ θ :=
  isPrincipal_add_omega0_opow θ hγ hδ

/-- Ordinals below `ω ^ θ` are closed under successor, for `θ` nonzero. -/
lemma add_one_lt_omega0_opow (hθ : 0 < θ) (hγ : γ < ω ^ θ) : γ + 1 < ω ^ θ :=
  add_lt_omega0_opow hγ (one_lt_omega0_opow hθ)

end Principal

section Bounds

/-- Successor ordinals are positive. -/
lemma zero_lt_add_one : 0 < a + 1 := one_pos.trans_le le_add_self

/-- `1 < ω ^ (a + 1)`. -/
lemma one_lt_opow_succ : 1 < ω ^ (a + 1) := one_lt_omega0_opow (zero_lt_add_one a)

/-- Anything bounded by `max (ω ^ a) (ω ^ b)` stays below `ω ^ (max a b + 1)`. -/
lemma lt_opow_succ_max_of_le_max {a b x : Ordinal} (hx : x ≤ max (ω ^ a) (ω ^ b)) :
    x < ω ^ (max a b + 1) :=
  hx.trans_lt <| max_lt
    ((opow_lt_opow_iff_right one_lt_omega0).mpr ((le_max_left a b).trans_lt (lt_add_one _)))
    ((opow_lt_opow_iff_right one_lt_omega0).mpr ((le_max_right a b).trans_lt (lt_add_one _)))

/-- `max (ω ^ a) (ω ^ b) + 1 ≤ ω ^ (max a b + 1)`. -/
lemma max_opow_add_one_le : max (ω ^ a) (ω ^ b) + 1 ≤ ω ^ (max a b + 1) :=
  (add_one_lt_omega0_opow (zero_lt_add_one _) (lt_opow_succ_max_of_le_max le_rfl)).le

/-- `ω ^ a + 1 ≤ ω ^ (a + 1)`. -/
lemma opow_add_one_le_opow_succ : ω ^ a + 1 ≤ ω ^ (a + 1) :=
  (add_one_lt_omega0_opow (zero_lt_add_one _)
    ((opow_lt_opow_iff_right one_lt_omega0).mpr (lt_add_one a))).le

/-- `(⨆ n, ω ^ f n) + 1 ≤ ω ^ ((⨆ n, f n) + 1)`. -/
lemma iSup_opow_add_one_le : (⨆ n, ω ^ f n) + 1 ≤ ω ^ ((⨆ n, f n) + 1) := by
  have hsup : (⨆ n, ω ^ f n) ≤ ω ^ ⨆ n, f n :=
    Ordinal.iSup_le fun n => opow_le_opow_right omega0_pos (Ordinal.le_iSup f n)
  refine (add_one_lt_omega0_opow (zero_lt_add_one _) (hsup.trans_lt ?_)).le
  exact (opow_lt_opow_iff_right one_lt_omega0).mpr (lt_add_one _)

variable {a b f}

/-- `max (a + b + 1) (a + c + 1) + 1 ≤ a + (max b c + 1) + 1`. -/
lemma max_add_add_one_add_one_le (a b c : Ordinal) :
    max (a + b + 1) (a + c + 1) + 1 ≤ a + (max b c + 1) + 1 := by
  gcongr
  refine max_le ?_ ?_ <;> rw [add_assoc] <;> gcongr <;> simp

/-- `a + b + 1 + 1 ≤ a + (b + 1) + 1`. -/
lemma add_add_one_add_one_le (a b : Ordinal) : a + b + 1 + 1 ≤ a + (b + 1) + 1 :=
  le_of_eq (by rw [add_assoc a b 1])

/-- `(⨆ n, a + f n + 1) + 1 ≤ a + ((⨆ n, f n) + 1) + 1`. -/
lemma iSup_add_add_one_add_one_le (a : Ordinal) (f : ℕ → Ordinal) :
    (⨆ n, a + f n + 1) + 1 ≤ a + ((⨆ n, f n) + 1) + 1 := by
  gcongr
  refine Ordinal.iSup_le fun n => ?_
  rw [add_assoc]
  gcongr
  exact Ordinal.le_iSup f n

end Bounds

section OmegaTower

/-- The **`ω`-tower** `ω_c^α`: `ω ^ ·` iterated `c` times over `α`.

- [Tow20, Definition 19.8] -/
noncomputable def omegaTower : ℕ → Ordinal → Ordinal
  | 0, a => a
  | c + 1, a => omegaTower c (ω ^ a)

variable {a : Ordinal}

@[simp, grind =] lemma omegaTower_zero : omegaTower 0 a = a := rfl

@[simp, grind =] lemma omegaTower_one : omegaTower 1 a = ω ^ a := rfl

@[grind =] lemma omegaTower_succ (c : ℕ) : omegaTower (c + 1) a = omegaTower c (ω ^ a) := rfl

/-- `ε₀` is closed under `ω ^ ·`. -/
lemma omega0_opow_lt_epsilon0 (h : a < ε₀) : ω ^ a < ε₀ := by
  obtain ⟨n, hn⟩ := lt_epsilon_zero.mp h
  refine lt_trans ?_ (iterate_omega0_opow_lt_epsilon_zero (n + 1))
  rw [Function.iterate_succ_apply']
  exact (opow_lt_opow_iff_right one_lt_omega0).mpr hn

/-- The `ω`-tower over an ordinal below `ε₀` stays below `ε₀`. -/
lemma omegaTower_lt_epsilon0 (c : ℕ) (h : a < ε₀) : omegaTower c a < ε₀ := by
  induction c generalizing a with
  | zero => simpa using h
  | succ c ih => simpa [omegaTower_succ] using ih (omega0_opow_lt_epsilon0 h)

end OmegaTower

end Ordinal
