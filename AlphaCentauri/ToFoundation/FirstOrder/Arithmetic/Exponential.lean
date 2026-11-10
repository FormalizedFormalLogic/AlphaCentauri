module

public import Foundation.FirstOrder.Arithmetic.Exponential
public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import Foundation.FirstOrder.Arithmetic.Omega1.Nuon

/-!
# Pairs below $a^2$, bounded exponentials and bits
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

section Exponential

open scoped FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V]

lemma add_mul_lt_mul_of_lt [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {a b u v : V} (hu : u < a) (hv : v < b) :
    u + a * v < a * b := calc
  u + a * v < a + a * v := by simpa using hu
  _ = a * (v + 1) := by rw [mul_add, mul_one, add_comm]
  _ ≤ a * b := mul_le_mul_left (succ_le_iff_lt.mpr hv)

section ISigma0

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]

lemma add_mul_eq_add_mul_iff {a u u' v v' : V} (hu : u < a) (hu' : u' < a) :
    u + a * v = u' + a * v' ↔ u = u' ∧ v = v' := by
  have hmod : ∀ {u v : V}, u < a → (u + a * v) % a = u := by
    intro u v hu
    rw [add_comm, mul_comm, mod_mul_add_of_lt _ _ hu]
  have hdiv : ∀ {u v : V}, u < a → (u + a * v) / a = v := by
    intro u v hu
    rw [add_comm, mul_comm, div_mul_add _ _ hu]
  constructor
  · intro h
    constructor
    · rw [← hmod (v := v) hu, ← hmod (v := v') hu', h]
    · rw [← hdiv (v := v) hu, ← hdiv (v := v') hu', h]
  · rintro ⟨rfl, rfl⟩
    rfl

lemma bexp_succ {b x : V} (h : x + 1 < ‖b‖) : bexp b (x + 1) = 2 * bexp b x :=
  bexp_eq_of_exp h (exp_bexp_of_lt (lt_of_le_of_lt le_self_add h)).succ

lemma fbit_zero_eq_mod_two (x : V) : fbit x 0 = x % 2 := by
  rcases (Arithmetic.zero_le x).eq_or_lt with rfl | hx
  · simp
  · simp [fbit, bexp_pos_zero hx]

lemma fbit_succ_eq_fbit_div_two (x i : V) : fbit x (i + 1) = fbit (x / 2) i := by
  rcases mod_two x with h | h <;>
  · conv_lhs => rw [← div_add_mod x 2, h]
    simp

lemma fbit_ext {x y : V} (h : ∀ i, fbit x i = fbit y i) : x = y := by
  have key : ∀ z, z ≤ x + y → ∀ u ≤ z, ∀ w ≤ z, (∀ i ≤ x + y, fbit u i = fbit w i) → u = w := by
    intro z
    induction z using ISigma0.order_induction
    · definability
    case _ z IH =>
      intro hz u hu w hw hb
      rcases (Arithmetic.zero_le z).eq_or_lt with rfl | hz0
      · rw [nonpos_iff_eq_zero.mp hu, nonpos_iff_eq_zero.mp hw]
      have hhalf : ∀ i ≤ x + y, fbit (u / 2) i = fbit (w / 2) i := by
        intro i hi
        rcases hi.lt_or_eq with hi | rfl
        · rw [← fbit_succ_eq_fbit_div_two, ← fbit_succ_eq_fbit_div_two]
          exact hb (i + 1) (succ_le_iff_lt.mpr hi)
        · have hle : ∀ {v : V}, v ≤ z → ‖v / 2‖ ≤ x + y := fun {v} hv ↦
            (length_le _).trans <| (div_le v 2).trans <| hv.trans hz
          rw [fbit_eq_zero_of_le (hle hu), fbit_eq_zero_of_le (hle hw)]
      have hlt : z / 2 < z := div_lt_of_pos_of_one_lt hz0 one_lt_two
      have := IH (z / 2) hlt (hlt.le.trans hz) (u / 2) (div_monotone hu 2) (w / 2)
        (div_monotone hw 2) hhalf
      have hmod : u % 2 = w % 2 := by
        rw [← fbit_zero_eq_mod_two, ← fbit_zero_eq_mod_two]
        exact hb 0 (Arithmetic.zero_le _)
      rw [← div_add_mod u 2, ← div_add_mod w 2, this, hmod]
  exact key (x + y) le_rfl x le_self_add y le_add_self fun i _ ↦ h i

section Length

variable {u v : V}

lemma length_mul_le (u v : V) : ‖u * v‖ ≤ ‖u‖ + ‖v‖ := by
  rcases (Arithmetic.zero_le u).eq_or_lt with rfl | hu
  · simp
  rcases (Arithmetic.zero_le v).eq_or_lt with rfl | hv
  · simp
  obtain ⟨a, -, ha, hua⟩ := log_pos hu
  obtain ⟨b, -, hb, hvb⟩ := log_pos hv
  have H := (ha.add_mul hb).add_mul Exponential.exponential_two_four
  have hlt : u * v < a * b * 4 := calc
    u * v < 2 * a * (2 * b) := mul_lt_mul'' hua hvb (Arithmetic.zero_le _) (Arithmetic.zero_le _)
    _ = a * b * (2 * 2) := (mul_mul_mul_comm ..).trans (mul_comm ..)
    _ = a * b * 4 := by simp [← two_add_two_eq_four, two_mul]
  have := (H.lt_iff_log_lt (mul_pos hu hv)).mp hlt
  rw [← one_add_one_eq_two, ← add_assoc, ← le_iff_lt_succ] at this
  rw [length_of_pos hu, length_of_pos hv, length_of_pos (mul_pos hu hv)]
  calc
    log (u * v) + 1 ≤ log u + log v + 1 + 1 := by simpa using this
    _ = log u + 1 + (log v + 1) := by simp [add_assoc, add_left_comm, add_comm]

lemma length_add_length_le (hu : 0 < u) (hv : 0 < v) : ‖u‖ + ‖v‖ ≤ ‖u * v‖ + 1 := by
  obtain ⟨a, hau, ha, -⟩ := log_pos hu
  obtain ⟨b, hbv, hb, -⟩ := log_pos hv
  have := (le_iff_le_log_of_exp (ha.add_mul hb) (mul_pos hu hv)).mp
    (mul_le_mul hau hbv (Arithmetic.zero_le _) (Arithmetic.zero_le _))
  rw [length_of_pos hu, length_of_pos hv, length_of_pos (mul_pos hu hv)]
  simpa [add_assoc, add_left_comm, add_comm] using this

lemma exists_natCast_of_length_le (j : ℕ) {x : V} (h : ‖x‖ ≤ j) : ∃ k : ℕ, x = k := by
  induction j generalizing x with
  | zero =>
    use 0
    simpa using h
  | succ j ih =>
    rcases (Arithmetic.zero_le x).eq_or_lt with rfl | hx
    · use 0
      simp
    have hx₂ : 2 * (x / 2) + x % 2 = x := div_add_mod x 2
    rcases (Arithmetic.zero_le (x / 2)).eq_or_lt with h₀ | h₀
    · rw [← h₀, mul_zero, zero_add] at hx₂
      have : x ≤ 1 := lt_two_iff_le_one.mp (hx₂ ▸ mod_lt x two_pos)
      use 1
      simpa using le_antisymm this (pos_iff_one_le.mp hx)
    have hlen : ‖x‖ = ‖x / 2‖ + 1 := by
      rcases mod_two x with h₁ | h₁
      · rw [h₁, add_zero] at hx₂
        rw [← length_two_mul_of_pos h₀, hx₂]
      · rw [h₁] at hx₂
        rw [← length_two_mul_add_one (x / 2), hx₂]
    obtain ⟨k, hk⟩ := ih (x := x / 2) (by
      rw [hlen, Nat.cast_succ] at h
      exact (add_le_add_iff_right 1).mp h)
    rcases mod_two x with h₁ | h₁
    · use 2 * k
      rw [h₁, add_zero, hk] at hx₂
      simpa using hx₂.symm
    · use 2 * k + 1
      rw [h₁, hk] at hx₂
      simpa using hx₂.symm

end Length

end ISigma0

end

end Exponential

end FFL.FirstOrder.Arithmetic
