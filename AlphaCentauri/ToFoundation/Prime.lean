module

public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-!
# Prime factors and prime powers
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {p p' q q' d u v : V}

lemma exists_isPrime_dvd {n : V} (h : 1 < n) : ∃ p, IsPrime p ∧ p ∣ n := by
  obtain ⟨p, ⟨hp1, hpn⟩, hmin⟩ :=
    ISigma0.least_number (P := fun d ↦ 1 < d ∧ d ∣ n) (by definability) ⟨h, dvd_refl n⟩
  refine ⟨p, ⟨hp1, ?_⟩, hpn⟩
  intro b hbp hbd
  by_contra hcon
  push Not at hcon
  obtain ⟨hb1, hbp'⟩ := hcon
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hbd
    simp [hbd] at hp1
  have hb1' : 1 < b := lt_of_le_of_ne (one_le_of_zero_lt b (pos_iff_ne_zero.mpr hb0)) (Ne.symm hb1)
  exact hmin b (lt_of_le_of_ne hbp hbp') ⟨hb1', hbd.trans hpn⟩

lemma dvd_of_dvd_add {a b c : V} (h : a ∣ b) (h' : a ∣ b + c) : a ∣ c := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨t, ht⟩ := h'
  rcases (Arithmetic.zero_le a).eq_or_lt with rfl | ha
  · simpa using ht
  use t - s
  rw [mul_sub (le_of_mul_le_mul_left (ht ▸ le_self_add) ha), ← ht]
  simp

lemma IsPrime.dvd_mul (hp : IsPrime p) (h : p ∣ u * v) : p ∣ u ∨ p ∣ v := by
  obtain ⟨m, ⟨hm0, hmv⟩, hmin⟩ :=
    ISigma0.least_number (P := fun m ↦ 0 < m ∧ p ∣ m * v) (by definability)
      ⟨pos_of_gt hp.1, dvd_mul_right p v⟩
  have key (x : V) (hx : p ∣ x * v) : m ∣ x := by
    have hr : p ∣ x % m * v := by
      apply dvd_of_dvd_add (b := m * (x / m) * v)
      · rw [mul_right_comm]
        exact hmv.mul_right _
      · rwa [← add_mul, div_add_mod]
    by_contra hx0
    exact hmin _ (mod_lt x hm0) ⟨pos_iff_ne_zero.mpr (fun h ↦ hx0 (mod_eq_zero_iff_dvd.mp h)), hr⟩
  rcases hp.2 m (le_of_dvd (pos_of_gt hp.1) (key p (dvd_mul_right p v))) (key p (dvd_mul_right p v))
    with rfl | rfl
  · exact Or.inr (by simpa using hmv)
  · exact Or.inl (key u h)

/-- `q` is a positive power of the prime `p`: its only prime factor is `p`. -/
def IsPrimePower (p q : V) : Prop := IsPrime p ∧ 1 < q ∧ ∀ r ≤ q, IsPrime r → r ∣ q → r = p

@[definability] lemma definable_isPrimePower : 𝚺ᴬ₀.DefinableRel (IsPrimePower : V → V → Prop) := by
  unfold IsPrimePower
  definability

lemma IsPrime.isPrimePower (hp : IsPrime p) : IsPrimePower p p := by
  refine ⟨hp, hp.1, fun r hr hrp hrd ↦ ?_⟩
  exact (hp.2 r hr hrd).resolve_left hrp.1.ne'

namespace IsPrimePower

lemma pos (h : IsPrimePower p q) : 0 < q := pos_of_gt h.2.1

lemma dvd (h : IsPrimePower p q) : p ∣ q := by
  obtain ⟨r, hr, hrq⟩ := exists_isPrime_dvd h.2.1
  exact h.2.2 r (le_of_dvd h.pos hrq) hr hrq ▸ hrq

lemma mul_prime (h : IsPrimePower p q) : IsPrimePower p (q * p) := by
  refine ⟨h.1, h.2.1.trans_le (le_mul_self_of_pos_right (pos_of_gt h.1.1)), fun r hr hrp hrd ↦ ?_⟩
  exact (hrp.dvd_mul hrd).elim (fun hq ↦ h.2.2 r (le_of_dvd h.pos hq) hrp hq)
    (fun hp ↦ h.1.isPrimePower.2.2 r (le_of_dvd (pos_of_gt h.1.1) hp) hrp hp)

lemma of_dvd (h : IsPrimePower p q) (hd : d ∣ q) (hd1 : 1 < d) : IsPrimePower p d :=
  ⟨h.1, hd1, fun r _ hr hrd ↦ h.2.2 r (le_of_dvd h.pos (hrd.trans hd)) hr (hrd.trans hd)⟩

lemma unique (h : IsPrimePower p q) (h' : IsPrimePower p' q) : p = p' :=
  h'.2.2 p (le_of_dvd h'.pos h.dvd) h.1 h.dvd

lemma eq_one_or_isPrimePower (h : IsPrimePower p q) (hd : d ∣ q) :
    d = 1 ∨ IsPrimePower p d := by
  have hd0 : 0 < d := pos_of_ne_zero (by rintro rfl; exact h.pos.ne' (zero_dvd_iff.mp hd))
  rcases (one_le_of_zero_lt d hd0).eq_or_lt with rfl | hd1
  · exact Or.inl rfl
  · exact Or.inr (h.of_dvd hd hd1)

lemma eq_or_exists_mul (h : IsPrimePower p q) : q = p ∨ ∃ s, IsPrimePower p s ∧ q = p * s := by
  obtain ⟨s, rfl⟩ := h.dvd
  rcases h.eq_one_or_isPrimePower (dvd_mul_left s p) with rfl | hs
  · simp
  · exact Or.inr ⟨s, hs, rfl⟩

lemma dvd_or_dvd (h : IsPrimePower p q) (h' : IsPrimePower p q') : q ∣ q' ∨ q' ∣ q := by
  revert h
  induction q using ISigma0.order_induction
  · definability
  case _ q IH =>
    intro h
    rcases h.eq_or_exists_mul with rfl | ⟨s, hs, rfl⟩
    · exact Or.inl h'.dvd
    rcases IH s (lt_mul_of_one_lt_left hs.pos h.1.1) hs with ⟨t, rfl⟩ | hd
    · rcases h'.eq_one_or_isPrimePower (dvd_mul_left t s) with rfl | ht
      · exact Or.inr (by simp)
      obtain ⟨t', rfl⟩ := ht.dvd
      · exact Or.inl ⟨t', by ac_rfl⟩
    · exact Or.inr (hd.trans (dvd_mul_left s p))

lemma mul_le_of_lt (h : IsPrimePower p q) (h' : IsPrimePower p q') (hlt : q < q') :
    q * p ≤ q' := by
  rcases h.dvd_or_dvd h' with ⟨t, rfl⟩ | hd
  · rcases h'.eq_one_or_isPrimePower (dvd_mul_left t q) with rfl | ht
    · simp at hlt
    · obtain ⟨t', rfl⟩ := ht.dvd
      have : 0 < t' := pos_of_ne_zero (by rintro rfl; simpa using h'.pos)
      exact mul_le_mul_left (le_mul_self_of_pos_right this)
  · exact absurd (le_of_dvd h.pos hd) (not_le.mpr hlt)

lemma dvd_of_dvd_mul (h : IsPrimePower p q) (hq : q ∣ u * v) (hv : ¬p ∣ v) : q ∣ u := by
  revert h hq
  induction q using ISigma0.order_induction
  · definability
  case _ q IH =>
    intro h hq
    rcases h.eq_or_exists_mul with rfl | ⟨s, hs, rfl⟩
    · exact (h.1.dvd_mul hq).resolve_right hv
    obtain ⟨w, rfl⟩ := IH s (lt_mul_of_one_lt_left hs.pos h.1.1) hs ((dvd_mul_left s p).trans hq)
    rw [mul_comm p s, mul_assoc] at hq
    rcases h.1.dvd_mul ((mul_dvd_mul_iff_left hs.pos.ne').mp hq) with ⟨c, rfl⟩ | hpv
    · exact ⟨c, by ac_rfl⟩
    · exact absurd hpv hv

lemma ne_of_ne (h : IsPrimePower p q) (h' : IsPrimePower p' q') (hp : p ≠ p') : q ≠ q' :=
  fun hq ↦ hp (h.unique (hq ▸ h'))

end IsPrimePower

end FFL.FirstOrder.Arithmetic
