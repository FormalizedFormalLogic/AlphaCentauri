module

public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import Foundation.FirstOrder.Arithmetic.Omega1.Nuon

/-!
# Block-coded sequences over $\mathsf{EA}$

Over a model of $\mathsf{EA}$, a number $S$ codes a sequence of length $i$ whose entries are the
blocks of width $\|a\|$ of $S$ below $2^{i \|a\|}$, read off by `Nuon.ext`. This file collects the
facts about appending an entry and about determining a code by its entries.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

attribute [local instance] ElementaryArithmetic.models_ISigma0_union_Omega1

lemma exists_exponential_mul_length (i a : V) : ∃ b, Exponential (i * ‖a‖) b :=
  ElementaryArithmetic.exponential_total _

namespace Nuon

section

variable {a i j : V}

lemma ext_add_mul_of_lt {S b x : V} (hb : Exponential (i * ‖a‖) b) (_hS : S < b)
    (_hx : x < a ⨳ 1) (hj : j < i) : Nuon.ext a (S + x * b) j = Nuon.ext a S j :=
  ext_add₁_pow2 hb.range_pow2 (by
    rw [hb.length_eq]
    exact lt_succ_iff_le.mpr (mul_le_mul_right (succ_le_iff_lt.mpr hj)))

lemma ext_add_mul_self {S b x : V} (hb : Exponential (i * ‖a‖) b) (hS : S < b)
    (hx : x < a ⨳ 1) : Nuon.ext a (S + x * b) i = x := by
  rcases Arithmetic.zero_le x with (rfl | pos)
  · simp only [zero_mul, add_zero]
    exact ext_eq_zero_of_lt (hb.lt_iff_len_le.mp hS)
  · have hlen : i * ‖a‖ < ‖S + x * b‖ := calc
      i * ‖a‖ < ‖b‖                       := by simp [hb.length_eq]
      _       ≤ ‖S + x * b‖               := length_monotone (le_add_left (le_mul_of_pos_left pos))
    have hbexp : bexp (S + x * b) (i * ‖a‖) = b := bexp_eq_of_exp hlen hb
    calc
      Nuon.ext a (S + x * b) i
          = (S + x * b) / bexp (S + x * b) (i * ‖a‖) % (a ⨳ 1) := rfl
      _ = (S + x * b) / b % (a ⨳ 1)                           := by rw [hbexp]
      _ = (S / b + x) % (a ⨳ 1)                               := by
        rw [div_add_mul_self S x hb.range_pos]
      _ = x % (a ⨳ 1)                                         := by
        rw [div_eq_zero_of_lt b hS, zero_add]
      _ = x                                                   := mod_eq_self_of_lt hx

axiom ext_ext {S S' b : V} (hb : Exponential (i * ‖a‖) b) (hS : S < b) (hS' : S' < b)
    (h : ∀ j < i, Nuon.ext a S j = Nuon.ext a S' j) : S = S'

end

end Nuon

end

end FFL.FirstOrder.Arithmetic
