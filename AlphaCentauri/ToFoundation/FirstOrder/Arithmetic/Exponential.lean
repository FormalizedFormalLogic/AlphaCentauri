module

public import Foundation.FirstOrder.Arithmetic.Exponential
public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import Foundation.FirstOrder.Arithmetic.Omega1.Nuon

/-!
# Exponentials, block-coded sequences and bounded powers

Supplements `Foundation.FirstOrder.Arithmetic.Exponential` and
`Foundation.FirstOrder.Arithmetic.Omega1.Nuon`: pairs below $a^2$, bounded exponentials and bits,
sequences coded by blocks of width $\|a\|$, and bounded powers over $\mathsf{I}\Sigma_0 + \Omega_1$.
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

section BlockSequence

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable section

variable {V : Type*} [ORingStructure V]

lemma exists_exponential_mul_length [V↓[ℒₒᵣ] ⊧* 𝗘𝗔] (i a : V) : ∃ b, Exponential (i * ‖a‖) b :=
  ElementaryArithmetic.exponential_total _

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁]

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

private lemma mod_add_div_mul_eq (S q : V) : S % q + S / q * q = S := by
  rw [mul_comm (S / q) q, add_comm]
  exact div_add_mod S q

private lemma bexp_succ_mul_length {a b k : V} (h : (k + 1) * ‖a‖ < ‖b‖) :
    bexp b ((k + 1) * ‖a‖) = bexp b (k * ‖a‖) * (a ⨳ 1) := by
  have hsum : k * ‖a‖ + ‖a‖ < ‖b‖ := by simpa [add_mul] using h
  rw [show (k + 1) * ‖a‖ = k * ‖a‖ + ‖a‖ by simp [add_mul], bexp_add hsum]
  congr 1
  exact bexp_eq_of_exp (lt_of_le_of_lt le_add_self hsum) (exponential_smash_one a)

private lemma mod_add_mul_lt {P Q S v c : V} (hP : 0 < P) (hv : v < c) (hQ : Q = P * c) :
    S % P + v * P < Q := by
  calc S % P + v * P < P + v * P := add_lt_add_left (mod_lt S hP) _
    _ = (v + 1) * P := by grind
    _ ≤ c * P := mul_le_mul_right (succ_le_iff_lt.mpr hv)
    _ = Q := by rw [hQ, mul_comm]

private lemma add_div_mul_lt {B Q S T : V} (hQ : Q ∣ B) (hS : S < B) (hT : T < Q) :
    T + S / Q * Q < B := by
  obtain ⟨D, hD⟩ := hQ
  have hcD : S / Q < D := by
    by_contra h
    have h₁ : Q * D ≤ Q * (S / Q) := mul_le_mul_left (not_lt.mp h)
    have h₂ : Q * (S / Q) ≤ S := le_self_add.trans_eq (div_add_mod S Q)
    exact absurd hS (not_lt.mpr (hD ▸ h₁.trans h₂))
  calc T + S / Q * Q < Q + S / Q * Q := add_lt_add_left hT _
    _ = (S / Q + 1) * Q := by grind
    _ ≤ D * Q := mul_le_mul_right (succ_le_iff_lt.mpr hcD)
    _ = B := (mul_comm _ _).trans hD.symm

namespace Nuon

section

variable {a i j : V}

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
      have hβ := bexp_succ_mul_length (a := a) hk₁
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
  have hβ := bexp_succ_mul_length (a := a) hQlen
  have hPpos : 0 < bexp (I ⨳ a) (j * ‖a‖) := bexp_pos hPlen
  have hQpos : 0 < bexp (I ⨳ a) ((j + 1) * ‖a‖) := bexp_pos hQlen
  have hdvd : bexp (I ⨳ a) ((j + 1) * ‖a‖) ∣ I ⨳ a := by
    have := Pow2.dvd_of_le (bexp_pow2 hQlen) (bexp_pow2 hBlen)
      ((bexp_monotone_le hQlen hBlen).mpr (mul_le_mul_right hj1))
    rwa [bexp_eq_smash] at this
  have hT := mod_add_mul_lt (S := S) hPpos hv hβ
  have hTlen : ‖S % bexp (I ⨳ a) (j * ‖a‖) + v * bexp (I ⨳ a) (j * ‖a‖)‖ ≤ (j + 1) * ‖a‖ :=
    (exp_bexp_of_lt hQlen).lt_iff_len_le.mp hT
  have hSQlen : ‖S % bexp (I ⨳ a) ((j + 1) * ‖a‖)‖ ≤ (j + 1) * ‖a‖ :=
    (exp_bexp_of_lt hQlen).lt_iff_len_le.mp (mod_lt _ hQpos)
  refine ⟨S % bexp (I ⨳ a) (j * ‖a‖) + v * bexp (I ⨳ a) (j * ‖a‖) +
    S / bexp (I ⨳ a) ((j + 1) * ‖a‖) * bexp (I ⨳ a) ((j + 1) * ‖a‖),
    add_div_mul_lt hdvd hS hT, ?_, ?_⟩
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
      rw [mod_add_div_mul_eq] at h2
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

lemma ext_div_pow2 {I S q k m : V} (hm : k + m ≤ ‖I‖) (hq : Exponential (k * ‖a‖) q) :
    Nuon.ext a (S / q) m = Nuon.ext a S (k + m) := by
  have hk : k ≤ ‖I‖ := le_self_add.trans hm
  have hqb : bexp (I ⨳ a) (k * ‖a‖) = q := bexp_eq_of_exp (Nuon.mul_len_lt_len_smash hk) hq
  have hS₁ : ‖S % q‖ ≤ k * ‖a‖ := hq.lt_iff_len_le.mp (mod_lt S hq.range_pos)
  have h := Nuon.ext_add₂_bexp (I := I) (L := a) (i := k) (j := m) (S₁ := S % q)
    (S₂ := S / q) hm hS₁
  rw [hqb, mod_add_div_mul_eq] at h
  exact h.symm

lemma ext_mod_pow2 {I S q k m : V} (hk : k ≤ ‖I‖) (hm : m < k) (hq : Exponential (k * ‖a‖) q) :
    Nuon.ext a (S % q) m = Nuon.ext a S m := by
  have hqb : bexp (I ⨳ a) (k * ‖a‖) = q := bexp_eq_of_exp (Nuon.mul_len_lt_len_smash hk) hq
  have h := Nuon.ext_add₁_bexp (I := I) (L := a) (i := k) (j := m) (S₁ := S % q)
    (S₂ := S / q) hk hm
  rw [hqb, mod_add_div_mul_eq] at h
  exact h.symm

end Blocks

end

end BlockSequence

section Power

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁]

local notation S "{" L "}[" i "]" => Nuon.ext L S i

namespace Power

variable {B x k k' S S' L L' : V}

lemma one_lt_sq_smash (hB : 0 < B) : (1 : V) < (B ⨳ B) ^ 2 := by
  have hB1 : (1 : V) ≤ ‖B‖ := pos_iff_one_le.mp (length_pos_iff.mpr hB)
  have h₁ : (1 : V) < B ⨳ B := lt_smash_iff.mpr (by simpa using one_le_mul hB1 hB1)
  calc (1 : V) < B ⨳ B := h₁
    _ ≤ (B ⨳ B) * (B ⨳ B) := le_mul_of_one_le_left (Arithmetic.zero_le _) h₁.le
    _ = (B ⨳ B) ^ 2 := (sq _).symm

lemma ext_one_zero (hB : 0 < B) : (1 : V){B}[0] = 1 :=
  Nuon.ext_zero_eq_self_of_le (by simpa using pos_iff_one_le.mp (length_pos_iff.mpr hB))

/-- The blocks of `S` of width `‖L‖` list the powers $x^0, \dots, x^k$. -/
def IsSeq (L S x k : V) : Prop := S{L}[0] = 1 ∧ ∀ i < k, S{L}[i + 1] = S{L}[i] * x

def isSeqDef : 𝚺ᴬ₀.Semisentence 4 := .mkSigma
  “L S x k.
    !Nuon.extDef 1 L S 0 ∧
    ∀ i < k, ∃ b <⁺ S, !Nuon.extDef b L S i ∧ !Nuon.extDef (b * x) L S (i + 1)”

instance isSeq_defined :
    𝚺ᴬ₀.Defined (V := V) (fun v ↦ IsSeq (v 0) (v 1) (v 2) (v 3)) isSeqDef := .mk fun v ↦ by
  simp [IsSeq, isSeqDef, Eq.comm]

lemma definable_isSeq : 𝚺ᴬ₀.DefinableRel₄ (IsSeq : V → V → V → V → Prop) :=
  isSeq_defined.to_definable

lemma IsSeq.of_le (H : IsSeq L S x k) (h : k' ≤ k) : IsSeq L S x k' :=
  ⟨H.1, fun i hi ↦ H.2 i (lt_of_lt_of_le hi h)⟩

lemma IsSeq.ext_eq (H : IsSeq L S x k) (H' : IsSeq L' S' x k) :
    ∀ i ≤ k, S{L}[i] = S'{L'}[i] := by
  intro i
  induction i using ISigma0.succ_induction
  · definability
  case zero => intro _; rw [H.1, H'.1]
  case succ i IH =>
    intro hi
    rw [H.2 i (succ_le_iff_lt.mp hi), H'.2 i (succ_le_iff_lt.mp hi), IH (le_trans (by simp) hi)]

lemma exists_isSeq (hB : 0 < B) (hx : 0 < x) (hk : k * ‖x‖ < ‖B‖) :
    ∃ S < (B ⨳ B) ^ 2, IsSeq B S x k ∧ ‖S{B}[k]‖ ≤ k * ‖x‖ + 1 := by
  have hx1 : 1 ≤ ‖x‖ := pos_iff_one_le.mp (length_pos_iff.mpr hx)
  have hone := one_lt_sq_smash hB
  have key : ∀ i ≤ k, ∃ S < (B ⨳ B) ^ 2, IsSeq B S x i ∧ ‖S{B}[i]‖ ≤ i * ‖x‖ + 1 := by
    intro i
    induction i using ISigma0.succ_induction
    · have := definable_isSeq (V := V)
      definability
    case zero =>
      intro _
      use 1
      and_intros
      · exact hone
      · exact ext_one_zero hB
      · simp
      · simp [ext_one_zero hB]
    case succ i IH =>
      intro hi
      obtain ⟨S, -, H, hlen⟩ := IH (le_trans (by simp) hi)
      have hlen' : ‖S{B}[i] * x‖ ≤ (i + 1) * ‖x‖ + 1 := calc
        ‖S{B}[i] * x‖ ≤ ‖S{B}[i]‖ + ‖x‖ := length_mul_le _ _
        _ ≤ i * ‖x‖ + 1 + ‖x‖ := by simpa using hlen
        _ = (i + 1) * ‖x‖ + 1 := by rw [add_mul, one_mul]; grind
      have hiB : (i + 1) * ‖x‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_right hi) hk
      have hiI : i + 1 ≤ ‖B‖ :=
        le_trans (le_mul_of_one_le_right (Arithmetic.zero_le _) hx1) hiB.le
      have hX : ‖S{B}[i] * x‖ ≤ ‖B‖ := hlen'.trans (succ_le_iff_lt.mpr hiB)
      have hlast := Nuon.ext_append_last B B S hiI hX
      have hlt : ∀ j < i + 1, (Nuon.append B B S (i + 1) (S{B}[i] * x)){B}[j] = S{B}[j] :=
        fun j hj ↦ Nuon.ext_append_lt B B S hiI hj
      use Nuon.append B B S (i + 1) (S{B}[i] * x)
      and_intros
      · exact Nuon.append_lt_sq_smash B B S hiI hX hB
      · rw [hlt 0 (by simp)]; exact H.1
      · intro j hj
        rcases lt_succ_iff_le.mp hj with rfl | hj
        · rw [hlast, hlt j (by simp)]
        · rw [hlt (j + 1) (by simpa using hj), hlt j (lt_trans hj (by simp)), H.2 j hj]
      · rwa [hlast]
  exact key k le_rfl

/-- `y` is $x^k$, as listed by a sequence with blocks of width `‖B‖`. -/
def IsPow (B x k y : V) : Prop := ∃ S < (B ⨳ B) ^ 2, IsSeq B S x k ∧ S{B}[k] = y

lemma IsPow.unique {y y' : V} (h : IsPow B x k y) (h' : IsPow B x k y') : y = y' := by
  obtain ⟨S, -, H, rfl⟩ := h
  obtain ⟨S', -, H', rfl⟩ := h'
  exact H.ext_eq H' k le_rfl

lemma definable_isPow (B : V) : 𝚺ᴬ₀.DefinableRel₃ (IsPow B) := by
  have := definable_isSeq (V := V)
  unfold IsPow
  definability

lemma IsPow.lt {y : V} (h : IsPow B x k y) : y < B ⨳ 1 := by
  obtain ⟨S, -, -, rfl⟩ := h
  exact mod_lt _ (smash_pos B 1)

end Power

open Power

open Classical in
/-- $x^k$, computed with blocks of width `‖B‖`; it is $0$ if no such sequence exists. -/
def bpow (B x k : V) : V := if h : ∃ y, IsPow B x k y then h.choose else 0

section bpow

variable {B x y k : V}

lemma Power.IsPow.bpow_eq (h : IsPow B x k y) : bpow B x k = y := by
  unfold bpow
  split_ifs with h'
  · exact h'.choose_spec.unique h
  · exact absurd ⟨y, h⟩ h'

lemma bpow_eq_iff : y = bpow B x k ↔ IsPow B x k y ∨ ((¬∃ y' < B ⨳ 1, IsPow B x k y') ∧ y = 0) := by
  constructor
  · rintro rfl
    by_cases h : ∃ y, IsPow B x k y
    · left
      obtain ⟨y, hy⟩ := h
      rwa [hy.bpow_eq]
    · right
      push Not at h
      constructor
      · rintro ⟨y, -, hy⟩
        exact h y hy
      · unfold bpow
        split_ifs with h'
        · obtain ⟨y, hy⟩ := h'
          exact absurd hy (h y)
        · rfl
  · rintro (h | ⟨h, rfl⟩)
    · exact h.bpow_eq.symm
    · unfold bpow
      split_ifs with h'
      · obtain ⟨y, hy⟩ := h'
        exact absurd ⟨y, hy.lt, hy⟩ h
      · rfl

instance (B : V) : 𝚺ᴬ₀.DefinableFunction₂ (bpow B) := by
  have := definable_isPow B
  simp only [Bounding.HierarchySymbol.DefinableFunction₂,
    Bounding.HierarchySymbol.DefinableFunction, bpow_eq_iff]
  definability

lemma bpow_lt (B x k : V) : bpow B x k < B ⨳ 1 := by
  unfold bpow
  split_ifs with h
  · exact h.choose_spec.lt
  · exact smash_pos B 1

instance (B : V) : Bounded₂ (bpow B) := ⟨&(B ⨳ 1), fun _ ↦ by simpa using (bpow_lt B _ _).le⟩

lemma length_bpow_le (hB : 0 < B) (hx : 0 < x) (hk : k * ‖x‖ < ‖B‖) :
    ‖bpow B x k‖ ≤ k * ‖x‖ + 1 := by
  obtain ⟨S, hS, H, hlen⟩ := exists_isSeq hB hx hk
  rwa [Power.IsPow.bpow_eq (⟨S, hS, H, rfl⟩ : IsPow B x k (S{B}[k]))]

@[simp] lemma bpow_zero (hB : 0 < B) (x : V) : bpow B x 0 = 1 := by
  apply Power.IsPow.bpow_eq
  use 1
  and_intros
  · exact one_lt_sq_smash hB
  · exact ext_one_zero hB
  · simp
  · exact ext_one_zero hB

lemma bpow_succ (hB : 0 < B) (hx : 0 < x) (hk : (k + 1) * ‖x‖ < ‖B‖) :
    bpow B x (k + 1) = bpow B x k * x := by
  obtain ⟨S, hS, H, -⟩ := exists_isSeq hB hx hk
  rw [Power.IsPow.bpow_eq (⟨S, hS, H, rfl⟩ : IsPow B x (k + 1) _),
    Power.IsPow.bpow_eq (⟨S, hS, H.of_le (by simp), rfl⟩ : IsPow B x k _), H.2 k (by simp)]

lemma bpow_pos (hB : 0 < B) (hx : 0 < x) (hk : k * ‖x‖ < ‖B‖) : 0 < bpow B x k := by
  revert hk
  induction k using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [hB]
  case succ k IH =>
    intro hk
    rw [bpow_succ hB hx hk]
    exact mul_pos (IH (lt_of_le_of_lt (mul_le_mul_right (by simp)) hk)) hx

lemma bpow_mul {y : V} (hB : 0 < B) (hx : 0 < x) (hy : 0 < y) (hk : k * ‖x * y‖ < ‖B‖) :
    bpow B (x * y) k = bpow B x k * bpow B y k := by
  revert hk
  induction k using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [hB]
  case succ k IH =>
    intro hk
    have hxy : 0 < x * y := mul_pos hx hy
    have hkx : (k + 1) * ‖x‖ < ‖B‖ :=
      lt_of_le_of_lt (mul_le_mul_left (length_monotone (le_mul_of_one_le_right
        (Arithmetic.zero_le _) (pos_iff_one_le.mp hy)))) hk
    have hky : (k + 1) * ‖y‖ < ‖B‖ :=
      lt_of_le_of_lt (mul_le_mul_left (length_monotone (le_mul_of_one_le_left
        (Arithmetic.zero_le _) (pos_iff_one_le.mp hx)))) hk
    rw [bpow_succ hB hxy hk, bpow_succ hB hx hkx, bpow_succ hB hy hky,
      IH (lt_of_le_of_lt (mul_le_mul_right (by simp)) hk)]
    grind

lemma bpow_monotone {y : V} (hB : 0 < B) (hx : 0 < x) (hxy : x ≤ y) (hk : k * ‖y‖ < ‖B‖) :
    bpow B x k ≤ bpow B y k := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  revert hk
  induction k using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [hB]
  case succ k IH =>
    intro hk
    have hkx : (k + 1) * ‖x‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_left (length_monotone hxy)) hk
    rw [bpow_succ hB hx hkx, bpow_succ hB hy hk]
    exact mul_le_mul (IH (lt_of_le_of_lt (mul_le_mul_right (by simp)) hk)) hxy
      (Arithmetic.zero_le _)
      (Arithmetic.zero_le _)

lemma bpow_one_left (hB : 0 < B) (hk : k < ‖B‖) : bpow B 1 k = 1 := by
  revert hk
  induction k using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [hB]
  case succ k IH =>
    intro hk
    rw [bpow_succ hB one_pos (by simpa using hk), IH (lt_of_le_of_lt (by simp) hk), mul_one]

lemma length_bpow_two_mul {w : V} (hB : 0 < B) (hw : 0 < w) (hk : k * ‖(2 : V)‖ < ‖B‖) :
    ‖bpow B 2 k * w‖ = ‖w‖ + k := by
  revert hk
  induction k using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [hB]
  case succ k IH =>
    intro hk
    rw [bpow_succ hB two_pos hk, mul_comm (bpow B 2 k) 2, mul_assoc,
      length_two_mul_of_pos (mul_pos (bpow_pos hB two_pos
        (lt_of_le_of_lt (mul_le_mul_right (by simp)) hk)) hw),
      IH (lt_of_le_of_lt (mul_le_mul_right (by simp)) hk), add_assoc]

end bpow

end

end Power

end FFL.FirstOrder.Arithmetic
