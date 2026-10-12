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

section Blocks

variable {a : V}

lemma exists_update {I S j v : V} (hS : S < I ⨳ a) (hj : j < ‖I‖) (hv : v < a ⨳ 1) :
    ∃ S' < I ⨳ a, Nuon.ext a S' j = v ∧ ∀ l ≤ ‖I‖, l ≠ j → Nuon.ext a S' l = Nuon.ext a S l := by
  have hj1 : j + 1 ≤ ‖I‖ := succ_le_iff_lt.mpr hj
  have hjI : j ≤ ‖I‖ := le_of_lt hj
  have hPlen : j * ‖a‖ < ‖I ⨳ a‖ := Nuon.mul_len_lt_len_smash hjI
  have hQlen : (j + 1) * ‖a‖ < ‖I ⨳ a‖ := Nuon.mul_len_lt_len_smash hj1
  have hBlen : ‖I‖ * ‖a‖ < ‖I ⨳ a‖ := Nuon.mul_len_lt_len_smash le_rfl
  have hβ : bexp (I ⨳ a) ((j + 1) * ‖a‖) = bexp (I ⨳ a) (j * ‖a‖) * (a ⨳ 1) := by
    have hsum : j * ‖a‖ + ‖a‖ < ‖I ⨳ a‖ := by simpa [add_mul] using hQlen
    rw [show (j + 1) * ‖a‖ = j * ‖a‖ + ‖a‖ by simp [add_mul], bexp_add hsum]
    congr 1
    exact bexp_eq_of_exp (lt_of_le_of_lt le_add_self hsum) (exponential_smash_one a)
  have hPpos : 0 < bexp (I ⨳ a) (j * ‖a‖) := bexp_pos hPlen
  have hQpos : 0 < bexp (I ⨳ a) ((j + 1) * ‖a‖) := bexp_pos hQlen
  have hdvd : bexp (I ⨳ a) ((j + 1) * ‖a‖) ∣ I ⨳ a := by
    have := Pow2.dvd_of_le (bexp_pow2 hQlen) (bexp_pow2 hBlen)
      ((bexp_monotone_le hQlen hBlen).mpr (mul_le_mul_right hj1))
    rwa [bexp_eq_smash] at this
  obtain ⟨D, hD⟩ := hdvd
  have hT : S % bexp (I ⨳ a) (j * ‖a‖) + v * bexp (I ⨳ a) (j * ‖a‖) <
      bexp (I ⨳ a) ((j + 1) * ‖a‖) := by
    have hv' : v + 1 ≤ a ⨳ 1 := succ_le_iff_lt.mpr hv
    calc S % bexp (I ⨳ a) (j * ‖a‖) + v * bexp (I ⨳ a) (j * ‖a‖)
        < bexp (I ⨳ a) (j * ‖a‖) + v * bexp (I ⨳ a) (j * ‖a‖) :=
          add_lt_add_left (mod_lt S hPpos) _
      _ = (v + 1) * bexp (I ⨳ a) (j * ‖a‖) := by grind
      _ ≤ (a ⨳ 1) * bexp (I ⨳ a) (j * ‖a‖) := mul_le_mul_right hv'
      _ = bexp (I ⨳ a) ((j + 1) * ‖a‖) := by rw [hβ, mul_comm]
  have hTlen : ‖S % bexp (I ⨳ a) (j * ‖a‖) + v * bexp (I ⨳ a) (j * ‖a‖)‖ ≤ (j + 1) * ‖a‖ :=
    (exp_bexp_of_lt hQlen).lt_iff_len_le.mp hT
  have hSQ : S % bexp (I ⨳ a) ((j + 1) * ‖a‖) +
      S / bexp (I ⨳ a) ((j + 1) * ‖a‖) * bexp (I ⨳ a) ((j + 1) * ‖a‖) = S := by
    rw [add_comm, mul_comm (S / _) _]
    exact div_add_mod S _
  have hSQlen : ‖S % bexp (I ⨳ a) ((j + 1) * ‖a‖)‖ ≤ (j + 1) * ‖a‖ :=
    (exp_bexp_of_lt hQlen).lt_iff_len_le.mp (mod_lt _ hQpos)
  have hcQ : bexp (I ⨳ a) ((j + 1) * ‖a‖) * (S / bexp (I ⨳ a) ((j + 1) * ‖a‖)) ≤ S := by
    have h := div_add_mod S (bexp (I ⨳ a) ((j + 1) * ‖a‖))
    exact le_self_add.trans_eq h
  have hcD : S / bexp (I ⨳ a) ((j + 1) * ‖a‖) < D := by
    by_contra h
    have h' : D ≤ S / bexp (I ⨳ a) ((j + 1) * ‖a‖) := not_lt.mp h
    have h1 : bexp (I ⨳ a) ((j + 1) * ‖a‖) * D ≤
        bexp (I ⨳ a) ((j + 1) * ‖a‖) * (S / bexp (I ⨳ a) ((j + 1) * ‖a‖)) :=
      mul_le_mul_left h'
    have h2 : I ⨳ a ≤ S := by rw [hD]; exact h1.trans hcQ
    exact absurd hS (not_lt.mpr h2)
  refine ⟨S % bexp (I ⨳ a) (j * ‖a‖) + v * bexp (I ⨳ a) (j * ‖a‖) +
    S / bexp (I ⨳ a) ((j + 1) * ‖a‖) * bexp (I ⨳ a) ((j + 1) * ‖a‖), ?_, ?_, ?_⟩
  · calc S % bexp (I ⨳ a) (j * ‖a‖) + v * bexp (I ⨳ a) (j * ‖a‖) +
        S / bexp (I ⨳ a) ((j + 1) * ‖a‖) * bexp (I ⨳ a) ((j + 1) * ‖a‖)
        < bexp (I ⨳ a) ((j + 1) * ‖a‖) +
          S / bexp (I ⨳ a) ((j + 1) * ‖a‖) * bexp (I ⨳ a) ((j + 1) * ‖a‖) :=
          add_lt_add_left hT _
      _ = (S / bexp (I ⨳ a) ((j + 1) * ‖a‖) + 1) * bexp (I ⨳ a) ((j + 1) * ‖a‖) := by grind
      _ ≤ D * bexp (I ⨳ a) ((j + 1) * ‖a‖) := mul_le_mul_right (succ_le_iff_lt.mpr hcD)
      _ = I ⨳ a := (mul_comm _ _).trans hD.symm
  · rw [Nuon.ext_add₁_bexp (i := j + 1) hj1 (by simp)]
    exact Nuon.ext_append_last I a S hjI (lt_smash_one_iff.mp hv)
  · intro l hl hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [Nuon.ext_add₁_bexp (i := j + 1) hj1 (lt_trans hlt (by simp))]
      exact Nuon.ext_append_lt I a S hjI hlt
    · obtain ⟨k, rfl⟩ := le_iff_exists_add.mp (succ_le_iff_lt.mpr hgt)
      have h1 := Nuon.ext_add₂_bexp (I := I) (L := a) (i := j + 1) (j := k)
        (S₁ := S % bexp (I ⨳ a) (j * ‖a‖) + v * bexp (I ⨳ a) (j * ‖a‖))
        (S₂ := S / bexp (I ⨳ a) ((j + 1) * ‖a‖)) hl hTlen
      have h2 := Nuon.ext_add₂_bexp (I := I) (L := a) (i := j + 1) (j := k)
        (S₁ := S % bexp (I ⨳ a) ((j + 1) * ‖a‖))
        (S₂ := S / bexp (I ⨳ a) ((j + 1) * ‖a‖)) hl hSQlen
      rw [hSQ] at h2
      rw [h1]
      exact h2.symm

lemma exists_swap {I S j k : V} (hS : S < I ⨳ a) (hj : j < ‖I‖) (hk : k < ‖I‖) :
    ∃ S' < I ⨳ a, Nuon.ext a S' j = Nuon.ext a S k ∧ Nuon.ext a S' k = Nuon.ext a S j ∧
      ∀ l ≤ ‖I‖, l ≠ j → l ≠ k → Nuon.ext a S' l = Nuon.ext a S l := by
  have hv : ∀ l, Nuon.ext a S l < a ⨳ 1 := fun l => mod_lt _ (smash_pos a 1)
  obtain ⟨S₁, hS₁, h₁j, h₁l⟩ := exists_update hS hj (hv k)
  obtain ⟨S₂, hS₂, h₂k, h₂l⟩ := exists_update hS₁ hk (hv j)
  refine ⟨S₂, hS₂, ?_, h₂k, ?_⟩
  · rcases eq_or_ne j k with rfl | hjk
    · exact h₂k
    · exact (h₂l j (le_of_lt hj) hjk).trans h₁j
  · intro l hl hlj hlk
    exact (h₂l l hl hlk).trans (h₁l l hl hlj)

lemma ext_mod_smash {I S j : V} (hj : j < ‖I‖) : Nuon.ext a (S % (I ⨳ a)) j = Nuon.ext a S j := by
  have hS : S % (I ⨳ a) + S / (I ⨳ a) * (I ⨳ a) = S := by
    rw [mul_comm, add_comm, div_add_mod]
  have h := Nuon.ext_add₁_bexp (I := I) (L := a) (i := ‖I‖) (j := j)
    (S₁ := S % (I ⨳ a)) (S₂ := S / (I ⨳ a)) le_rfl hj
  rw [bexp_eq_smash, hS] at h
  exact h.symm

end Blocks

end

end FFL.FirstOrder.Arithmetic
