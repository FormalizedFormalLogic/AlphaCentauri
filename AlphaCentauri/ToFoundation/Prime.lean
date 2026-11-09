module

public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Arithmetic.Exponential

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

/-- Every prime-power divisor of `d` is at most `T`. -/
def PrimePowerDivisorsLE (T d : V) : Prop :=
  ∀ q ≤ d, (∃ p ≤ q, IsPrimePower p q) → q ∣ d → q ≤ T

@[definability] lemma definable_primePowerDivisorsLE :
    𝚺ᴬ₀.DefinableRel (PrimePowerDivisorsLE : V → V → Prop) := by
  unfold PrimePowerDivisorsLE
  definability

lemma primePowerDivisorsLE_one (T : V) : PrimePowerDivisorsLE T 1 := by
  intro q hq ⟨p, _, hp⟩
  exact absurd (hp.2.1.trans_le hq) (lt_irrefl _)

lemma exists_greatest_primePowerDivisorsLE (y T : V) :
    ∃ d, d ≤ y ∧ d ∣ y ∧ PrimePowerDivisorsLE T d ∧
      ∀ d' ≤ y, d' ∣ y → PrimePowerDivisorsLE T d' → d' ≤ d := by
  obtain ⟨e, ⟨d, hdy, hde, hdvd, hd⟩, hmin⟩ := ISigma0.least_number
    (P := fun e ↦ ∃ d ≤ y, d + e = y ∧ d ∣ y ∧ PrimePowerDivisorsLE T d)
    (by unfold PrimePowerDivisorsLE; definability) (x := y - 1) <| by
      rcases (Arithmetic.zero_le y).eq_or_lt with rfl | hy
      · use 0
        simp [PrimePowerDivisorsLE, IsPrimePower]
      · use 1
        and_intros
        · exact one_le_of_zero_lt y hy
        · simpa [add_comm] using add_tsub_cancel_of_le (one_le_of_zero_lt y hy)
        · simp
        · exact primePowerDivisorsLE_one T
  use d
  and_intros
  · exact hdy
  · exact hdvd
  · exact hd
  · intro d' hd'y hd'dvd hd'
    have : e ≤ y - d' := by
      by_contra h
      exact hmin (y - d') (not_le.mp h) ⟨d', hd'y, by simp [hd'y], hd'dvd, hd'⟩
    by_contra h
    have := add_lt_add_of_lt_of_le (not_le.mp h) this
    simp [hde, hd'y] at this

/-- The largest divisor of `y` whose prime-power divisors are all at most `T`. -/
noncomputable def divisorUpTo (y T : V) : V :=
  Classical.choose (exists_greatest_primePowerDivisorsLE y T)

section divisorUpTo

variable {x y T T' : V}

lemma divisorUpTo_le (y T : V) : divisorUpTo y T ≤ y :=
  (Classical.choose_spec (exists_greatest_primePowerDivisorsLE y T)).1

lemma divisorUpTo_dvd (y T : V) : divisorUpTo y T ∣ y :=
  (Classical.choose_spec (exists_greatest_primePowerDivisorsLE y T)).2.1

lemma primePowerDivisorsLE_divisorUpTo (y T : V) : PrimePowerDivisorsLE T (divisorUpTo y T) :=
  (Classical.choose_spec (exists_greatest_primePowerDivisorsLE y T)).2.2.1

lemma le_divisorUpTo_of_le (hdy : d ≤ y) (hd : d ∣ y) (h : PrimePowerDivisorsLE T d) :
    d ≤ divisorUpTo y T :=
  (Classical.choose_spec (exists_greatest_primePowerDivisorsLE y T)).2.2.2 d hdy hd h

lemma le_divisorUpTo (hy : 0 < y) (hd : d ∣ y) (h : PrimePowerDivisorsLE T d) :
    d ≤ divisorUpTo y T :=
  le_divisorUpTo_of_le (le_of_dvd hy hd) hd h

lemma divisorUpTo_eq_iff {z : V} : z = divisorUpTo y T ↔ z ≤ y ∧ z ∣ y ∧ PrimePowerDivisorsLE T z ∧
    ∀ d ≤ y, d ∣ y → PrimePowerDivisorsLE T d → d ≤ z := by
  constructor
  · rintro rfl
    exact ⟨divisorUpTo_le y T, divisorUpTo_dvd y T, primePowerDivisorsLE_divisorUpTo y T,
      fun d hdy hd h ↦ le_divisorUpTo_of_le hdy hd h⟩
  · rintro ⟨hz, hzd, hzp, hmax⟩
    exact le_antisymm (le_divisorUpTo_of_le hz hzd hzp)
      (hmax _ (divisorUpTo_le y T) (divisorUpTo_dvd y T) (primePowerDivisorsLE_divisorUpTo y T))

instance : 𝚺ᴬ₀.DefinableFunction₂ (divisorUpTo : V → V → V) := by
  simp only [Bounding.HierarchySymbol.DefinableFunction₂,
    Bounding.HierarchySymbol.DefinableFunction, divisorUpTo_eq_iff]
  definability

instance : Bounded₂ (divisorUpTo : V → V → V) := ⟨#0, fun _ ↦ by simpa using divisorUpTo_le _ _⟩

lemma divisorUpTo_pos (hy : 0 < y) : 0 < divisorUpTo y T :=
  lt_of_lt_of_le zero_lt_one <| le_divisorUpTo hy (one_dvd y) (primePowerDivisorsLE_one T)

lemma divisorUpTo_monotone (h : T ≤ T') : divisorUpTo y T ≤ divisorUpTo y T' :=
  le_divisorUpTo_of_le (divisorUpTo_le y T) (divisorUpTo_dvd y T) fun q hq hp hqd ↦
    (primePowerDivisorsLE_divisorUpTo y T q hq hp hqd).trans h

lemma divisorUpTo_self (hy : 0 < y) : divisorUpTo y y = y :=
  le_antisymm (divisorUpTo_le y y) (le_divisorUpTo hy dvd_rfl fun _ hq _ _ ↦ hq)

lemma divisorUpTo_zero (hy : 0 < y) : divisorUpTo y 0 = 1 := by
  refine le_antisymm ?_ (one_le_of_zero_lt _ (divisorUpTo_pos hy))
  by_contra h
  obtain ⟨p, hp, hpd⟩ := exists_isPrime_dvd (not_le.mp h)
  have := primePowerDivisorsLE_divisorUpTo y 0 p (le_of_dvd (divisorUpTo_pos hy) hpd)
    ⟨p, le_rfl, hp.isPrimePower⟩ hpd
  exact absurd (pos_of_gt hp.1) (not_lt.mpr this)

lemma exists_isPrimePower_of_divisorUpTo_lt (hy : 0 < y)
    (h : divisorUpTo y T < divisorUpTo y (T + 1)) :
    ∃ p, IsPrimePower p (T + 1) ∧ T + 1 ∣ y ∧ divisorUpTo y (T + 1) ≤ p * divisorUpTo y T := by
  have hepos := divisorUpTo_pos (T := T + 1) hy
  have hle := primePowerDivisorsLE_divisorUpTo y (T + 1)
  by_cases hA : ∃ p, IsPrimePower p (T + 1) ∧ T + 1 ∣ divisorUpTo y (T + 1)
  · obtain ⟨p, hp, hdvd⟩ := hA
    obtain ⟨e', he'⟩ := hp.dvd.trans hdvd
    have he'y : e' ∣ y := (Dvd.intro_left p he'.symm).trans (divisorUpTo_dvd y _)
    use p
    constructor
    · exact hp
    constructor
    · exact hdvd.trans (divisorUpTo_dvd y _)
    · rw [he']
      apply mul_le_mul_left
      apply le_divisorUpTo hy he'y
      intro q hq ⟨r, hrq, hr⟩ hqe'
      have hqe : q ∣ divisorUpTo y (T + 1) := he' ▸ Dvd.dvd.mul_left hqe' p
      have hq1 : q < T + 1 := by
        by_cases hrp : r = p
        · subst hrp
          have hqr : q * r ∣ divisorUpTo y (T + 1) := he' ▸ mul_comm r e' ▸ mul_dvd_mul_right hqe' r
          have := hle (q * r) (le_of_dvd hepos hqr)
            ⟨r, le_mul_self_of_pos_left hr.pos, hr.mul_prime⟩ hqr
          exact lt_of_lt_of_le (lt_mul_of_one_lt_right hr.pos hr.1.1) this
        · exact lt_of_le_of_ne (hle q (le_of_dvd hepos hqe) ⟨r, hrq, hr⟩ hqe) (hr.ne_of_ne hp hrp)
      exact lt_succ_iff_le.mp hq1
  · exfalso
    refine h.not_ge <| le_divisorUpTo hy (divisorUpTo_dvd y _) fun q hq ⟨r, hrq, hr⟩ hqd ↦ ?_
    refine lt_succ_iff_le.mp <| lt_of_le_of_ne (hle q hq ⟨r, hrq, hr⟩ hqd) ?_
    rintro rfl
    exact hA ⟨r, hr, hqd⟩

lemma mul_divisorUpTo_le (hy : 0 < y) (hP : IsPrimePower p (T + 1)) (hdvd : T + 1 ∣ y) :
    p * divisorUpTo y T ≤ divisorUpTo y (T + 1) := by
  have hdpos := divisorUpTo_pos (T := T) hy
  have hle := primePowerDivisorsLE_divisorUpTo y T
  obtain ⟨m, hm⟩ := divisorUpTo_dvd y T
  have hpm : p ∣ m := by
    by_contra hpm
    have := hle (T + 1) (le_of_dvd hdpos (hP.dvd_of_dvd_mul (hm ▸ hdvd) hpm))
      ⟨p, le_of_dvd hP.pos hP.dvd, hP⟩ (hP.dvd_of_dvd_mul (hm ▸ hdvd) hpm)
    exact absurd this (not_le.mpr (lt_succ_iff_le.mpr le_rfl))
  obtain ⟨s, hs⟩ := hpm
  apply le_divisorUpTo hy ⟨s, by rw [hs] at hm; exact hm.trans (by ac_rfl)⟩
  intro q hq ⟨r, hrq, hr⟩ hqd
  by_cases hrp : r = p
  · subst hrp
    rcases hr.eq_or_exists_mul with rfl | ⟨t, ht, rfl⟩
    · exact le_of_dvd hP.pos hP.dvd
    · have htd : t ∣ divisorUpTo y T := (mul_dvd_mul_iff_left (pos_of_gt hr.1.1).ne').mp hqd
      have := hle t (le_of_dvd hdpos htd) ⟨r, le_of_dvd ht.pos ht.dvd, ht⟩ htd
      rw [mul_comm]
      exact ht.mul_le_of_lt hP (lt_succ_iff_le.mpr this)
  · have hrp' : ¬r ∣ p := fun h ↦ by
      rcases hP.1.2 r (le_of_dvd (pos_of_gt hP.1.1) h) h with rfl | rfl
      · exact absurd hr.1.1 (lt_irrefl _)
      · exact hrp rfl
    have hqd' := hr.dvd_of_dvd_mul (u := divisorUpTo y T) (v := p) (mul_comm p _ ▸ hqd) hrp'
    exact (hle q (le_of_dvd hdpos hqd') ⟨r, hrq, hr⟩ hqd').trans (lt_succ_iff_le.mpr le_rfl).le

lemma exists_length_divisorUpTo_le_lt (hy : 0 < y) (hx : x + 1 < ‖y‖) :
    ∃ T, ‖divisorUpTo y T‖ ≤ x + 1 ∧ x + 1 < ‖divisorUpTo y (T + 1)‖ := by
  obtain ⟨T', hT', hmin⟩ := ISigma0.least_number (P := fun T ↦ x + 1 < ‖divisorUpTo y T‖)
    (by definability) (x := y) (by simpa [divisorUpTo_self hy] using hx)
  have hT'0 : T' ≠ 0 := by
    rintro rfl
    simp [divisorUpTo_zero hy] at hT'
  obtain ⟨T, rfl⟩ := eq_succ_of_pos (pos_of_ne_zero hT'0)
  use T
  constructor
  · exact not_lt.mp <| hmin T (lt_succ_iff_le.mpr le_rfl)
  · exact hT'

lemma eq_of_length_divisorUpTo_le_lt {X : V} (h₁ : ‖divisorUpTo y T‖ ≤ X)
    (h₂ : X < ‖divisorUpTo y (T + 1)‖) (h₁' : ‖divisorUpTo y T'‖ ≤ X)
    (h₂' : X < ‖divisorUpTo y (T' + 1)‖) : T = T' := by
  refine le_antisymm (not_lt.mp fun hlt ↦ ?_) (not_lt.mp fun hlt ↦ ?_)
  · exact absurd (h₂'.trans_le <| (length_monotone <| divisorUpTo_monotone
      (lt_iff_succ_le.mp hlt)).trans h₁) (lt_irrefl _)
  · exact absurd (h₂.trans_le <| (length_monotone <| divisorUpTo_monotone
      (lt_iff_succ_le.mp hlt)).trans h₁') (lt_irrefl _)

end divisorUpTo

end FFL.FirstOrder.Arithmetic
