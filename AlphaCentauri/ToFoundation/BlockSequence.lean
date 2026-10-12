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

private lemma mod_mul_eq_mod_add {p β : V} (S : V) (hp : 0 < p) (hβ : 0 < β) :
    S % (p * β) = S % p + (S / p % β) * p := by
  have e₁ : p * (S / p) + S % p = S := div_add_mod S p
  have e₂ : β * (S / p / β) + S / p % β = S / p := div_add_mod (S / p) β
  have h₁ : S = (S / p / β) * (p * β) + ((S / p % β) * p + S % p) := calc
    S = p * (S / p) + S % p                         := e₁.symm
    _ = p * (β * (S / p / β) + S / p % β) + S % p   := by rw [e₂]
    _ = (S / p / β) * (p * β) + ((S / p % β) * p + S % p) := by grind
  have hr : S % p < p := mod_lt S hp
  have ht : S / p % β < β := mod_lt (S / p) hβ
  have h₂ : (S / p % β) * p + S % p < p * β := calc
    (S / p % β) * p + S % p < (S / p % β) * p + p := by simpa using hr
    _                       = (S / p % β + 1) * p := by grind
    _                       ≤ β * p               := mul_le_mul_right (succ_le_iff_lt.mpr ht)
    _                       = p * β               := mul_comm β p
  calc
    S % (p * β) = ((S / p / β) * (p * β) + ((S / p % β) * p + S % p)) % (p * β) := by rw [← h₁]
    _           = (S / p % β) * p + S % p := mod_mul_add_of_lt _ _ h₂
    _           = S % p + (S / p % β) * p := add_comm _ _

namespace Nuon

section

variable {a i j : V}

lemma ext_add_mul_of_lt {S b x : V} (hb : Exponential (i * ‖a‖) b) (hj : j < i) :
    Nuon.ext a (S + x * b) j = Nuon.ext a S j :=
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

lemma ext_ext {S S' b : V} (hb : Exponential (i * ‖a‖) b) (hS : S < b) (hS' : S' < b)
    (h : ∀ j < i, Nuon.ext a S j = Nuon.ext a S' j) : S = S' := by
  have hib : i * ‖a‖ < ‖b‖ := by simp [hb.length_eq]
  have key : ∀ k ≤ i, S % bexp b (k * ‖a‖) = S' % bexp b (k * ‖a‖) := by
    intro k
    induction k using ISigma0.succ_induction
    · definability
    case zero => intro _; simp [bexp_pos_zero hb.range_pos]
    case succ k IH =>
      intro hk
      have hk' : k < i := succ_le_iff_lt.mp hk
      have hk₁ : (k + 1) * ‖a‖ < ‖b‖ := lt_of_le_of_lt (mul_le_mul_right hk) hib
      have hkb : k * ‖a‖ < ‖b‖ := lt_of_le_of_lt (mul_le_mul_right le_self_add) hk₁
      have hβ : bexp b ((k + 1) * ‖a‖) = bexp b (k * ‖a‖) * (a ⨳ 1) := by
        have hsum : k * ‖a‖ + ‖a‖ < ‖b‖ := by simpa [add_mul] using hk₁
        rw [show (k + 1) * ‖a‖ = k * ‖a‖ + ‖a‖ by simp [add_mul], bexp_add hsum]
        congr 1
        exact bexp_eq_of_exp (lt_of_le_of_lt le_add_self hsum) (exponential_smash_one a)
      have hp : 0 < bexp b (k * ‖a‖) := bexp_pos hkb
      have IHk : S % bexp b (k * ‖a‖) = S' % bexp b (k * ‖a‖) := IH (le_trans (by simp) hk)
      rw [hβ, mod_mul_eq_mod_add S hp (smash_pos a 1), mod_mul_eq_mod_add S' hp (smash_pos a 1),
        ext_eq_of_gt hkb, ext_eq_of_gt hkb, IHk, h k hk']
  have := key i le_rfl
  rwa [bexp_eq_of_exp hib hb, mod_eq_self_of_lt hS, mod_eq_self_of_lt hS'] at this

end

end Nuon

end

end FFL.FirstOrder.Arithmetic
