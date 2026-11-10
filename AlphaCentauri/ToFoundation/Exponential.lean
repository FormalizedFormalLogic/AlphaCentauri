module

public import Foundation.FirstOrder.Arithmetic.Exponential

/-!
# Pairs below $a^2$, bounded exponentials and bits
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic

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

end ISigma0

end

end FFL.FirstOrder.Arithmetic
