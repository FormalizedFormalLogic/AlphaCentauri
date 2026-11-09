module

public import Foundation.FirstOrder.Arithmetic.Exponential

/-!
# Pairs below $a^2$ and bounded exponentials
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V]

lemma add_mul_lt_mul_self [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {a u v : V} (hu : u < a) (hv : v < a) :
    u + a * v < a * a := calc
  u + a * v < a + a * v := by simpa using hu
  _ = a * (v + 1) := by rw [mul_add, mul_one, add_comm]
  _ ≤ a * a := mul_le_mul_left (succ_le_iff_lt.mpr hv)

lemma bexp_succ [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {b x : V} (h : x + 1 < ‖b‖) : bexp b (x + 1) = 2 * bexp b x :=
  bexp_eq_of_exp h (exp_bexp_of_lt (lt_of_le_of_lt le_self_add h)).succ

end

end FFL.FirstOrder.Arithmetic
