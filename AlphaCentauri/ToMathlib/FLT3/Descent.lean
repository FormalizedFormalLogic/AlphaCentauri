module

public import AlphaCentauri.ToMathlib.FLT3.Eisenstein
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Fermat's Last Theorem for exponent 3 from the least number principle

A solution of `a³ + b³ = u c³` in the Eisenstein integers over a discretely ordered ring `R` with
`LeastNumberPrinciple R` (`Solution`) yields one with a smaller `norm c`
(`EisensteinInteger.descent`), by the descent of Kummer's proof. The existence of a solution is a
bounded existential open predicate in the coordinates of `a`, `b`, `c`, `u`, so
`LeastNumberPrinciple R` rules out every solution (`EisensteinInteger.no_solution`), and hence
every non-trivial solution of `x³ + y³ = z³` in `R` (`FermatThree.flt3_of_leastNumberPrinciple`).
-/

@[expose] public section

open QuadraticAlgebra OpenPredicate

namespace EisensteinInteger

variable {R : Type*} [CommRing R] {a b c d e f g p q r s u v z ε : EisensteinInteger R} {K : R}

lemma isCoprime_of_lin (h : IsCoprime a b) (p q r s : EisensteinInteger R) (ha : a = p * f + q * g)
    (hb : b = r * f + s * g) : IsCoprime f g := by
  obtain ⟨m, n, hmn⟩ := h
  use m * p + n * r, m * q + n * s
  linear_combination hmn - m * ha - n * hb

lemma isCoprime_mul_root (hab : IsCoprime a b) (hε : ε ^ 3 = 1) : IsCoprime a (ε * b) :=
  isCoprime_of_lin hab 1 0 0 (ε ^ 2) (by ring) (by linear_combination -b * hε)

lemma isCoprime_of_cube_eq (hpq : IsCoprime p q) (h : p ^ 3 + q ^ 3 = r ^ 3) : IsCoprime p r := by
  have : IsCoprime p (r ^ 3) := by
    rw [show r ^ 3 = q ^ 3 + p * p ^ 2 by linear_combination -h]
    exact hpq.pow_right.add_mul_left_right _
  exact (IsCoprime.pow_right_iff (by norm_num)).mp this

/-- Coordinates `i + 1` and `j + 1` of `w` as an Eisenstein integer. -/
abbrev coordinate (w : Fin 15 → R) (i j : Fin 14) : EisensteinInteger R := ⟨w i.succ, w j.succ⟩

variable [LinearOrder R]

/-- A solution of `a³ + b³ = u c³` with `λ ∤ a`, `λ ∤ b`, `λ ∣ c ≠ 0`, `u` a unit, and the norms
of `a` and `b` bounded by `K`. -/
structure Solution (K : R) (a b c u : EisensteinInteger R) : Prop where
  norm_a_le : norm a ≤ K
  norm_b_le : norm b ≤ K
  isUnit_u : IsUnit u
  eq : a ^ 3 + b ^ 3 = u * c ^ 3
  not_dvd_a : ¬lambda ∣ a
  not_dvd_b : ¬lambda ∣ b
  dvd_c : lambda ∣ c
  c_ne_zero : c ≠ 0

/-- The open matrix of the descent predicate: the variable `0` is `norm c`, the others are the
coordinates of `a, b, c, u` and of the witnesses `sa, sb, sc` of `a ∓ 1 = λ sa`, `b ∓ 1 = λ sb`,
`c = λ sc`. -/
def descentPredicate (K : R) (w : Fin 15 → R) : Prop :=
  let x (i j) := coordinate w i j
  norm (x 0 1) ≤ K ∧ norm (x 2 3) ≤ K ∧ norm (x 6 7) = 1 ∧
    x 0 1 ^ 3 + x 2 3 ^ 3 = x 6 7 * x 4 5 ^ 3 ∧
    (x 0 1 - 1 = lambda * x 8 9 ∨ x 0 1 + 1 = lambda * x 8 9) ∧
    (x 2 3 - 1 = lambda * x 10 11 ∨ x 2 3 + 1 = lambda * x 10 11) ∧
    x 4 5 = lambda * x 12 13 ∧ x 4 5 ≠ 0 ∧ w 0 = norm (x 4 5)

lemma isOpen_descentPredicate (K : R) : IsOpen (descentPredicate K) := by
  is_open

variable [IsStrictOrderedRing R]

lemma dvd_of_pow_three_dvd [IsBezout (EisensteinInteger R)] (h : d ^ 3 ∣ c ^ 3) : d ∣ c := by
  classical
  let := IsBezout.toGCDDomain (EisensteinInteger R)
  exact (IsIntegrallyClosed.pow_dvd_pow_iff (by norm_num)).mp h

lemma exists_unit_mul_cube [IsBezout (EisensteinInteger R)] (hu : IsUnit u) (hpq : IsCoprime p q)
    (h : p * q = u * c ^ 3) :
    ∃ (P : EisensteinInteger R) (v : (EisensteinInteger R)ˣ), p = v * P ^ 3 := by
  obtain ⟨P, v, hv⟩ := exists_associated_pow_of_associated_pow_mul hpq (c := c) (k := 3)
    ⟨hu.unit, by rw [h, IsUnit.unit_spec]; ring⟩
  use P, v
  rw [← hv]; ring

/-- Dividing a solution of `a³ + b³ = u c³` by the gcd of `a` and `b`. -/
lemma exists_gcd_reduce [IsBezout (EisensteinInteger R)] (ha : a ≠ 0) (hu : IsUnit u)
    (h : a ^ 3 + b ^ 3 = u * c ^ 3) : ∃ d a₀ b₀ c₀ : EisensteinInteger R,
      a = d * a₀ ∧ b = d * b₀ ∧ c = d * c₀ ∧ d ≠ 0 ∧ IsCoprime a₀ b₀ ∧
      a₀ ^ 3 + b₀ ^ 3 = u * c₀ ^ 3 ∧ (IsUnit d → IsCoprime a b) := by
  obtain ⟨d, s, t, hst, ⟨a₀, rfl⟩, ⟨b₀, rfl⟩⟩ :
      ∃ d s t : EisensteinInteger R, s * a + t * b = d ∧ d ∣ a ∧ d ∣ b := by
    obtain ⟨s, t, h⟩ := Ideal.mem_span_pair.mp <|
      IsBezout.span_gcd a b ▸ Ideal.mem_span_singleton_self (IsBezout.gcd a b)
    use IsBezout.gcd a b, s, t
    exact ⟨h, IsBezout.gcd_dvd_left a b, IsBezout.gcd_dvd_right a b⟩
  have hd : d ≠ 0 := left_ne_zero_of_mul ha
  have : d ^ 3 ∣ c ^ 3 := (IsUnit.dvd_mul_left hu).mp <| by
    rw [← h, mul_pow, mul_pow]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)
  obtain ⟨c₀, rfl⟩ := dvd_of_pow_three_dvd this
  have hcop : IsCoprime a₀ b₀ := by
    use s, t
    exact mul_left_cancel₀ hd (by linear_combination hst)
  use d, a₀, b₀, c₀
  refine ⟨rfl, rfl, rfl, hd, hcop,
    mul_left_cancel₀ (pow_ne_zero 3 hd) (by linear_combination h), ?_⟩
  intro hdu
  obtain ⟨e, he⟩ := hdu.exists_right_inv
  use s * e, t * e
  linear_combination e * hst + he

lemma norm_witness_le (h : z - 1 = lambda * s ∨ z + 1 = lambda * s) : norm s ≤ norm z + 1 := by
  have key (e : EisensteinInteger R) (he : norm e = 1) (h : z + e = lambda * s) :
      norm s ≤ norm z + 1 := by
    have := congrArg norm h
    rw [norm_mul, norm_lambda] at this
    linarith [norm_add_le z e, norm_nonneg z]
  rcases h with h | h
  · exact key (-1) (by rw [norm_neg, norm_one]) (by rw [← h]; ring)
  · exact key 1 norm_one h

variable [DiscretelyOrdered R] (hL : LeastNumberPrinciple R)

lemma norm_le_of_dvd (h : p ∣ q) (hq : q ≠ 0) : norm p ≤ norm q := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := right_ne_zero_of_mul hq
  rw [norm_mul]
  nlinarith [one_le_norm hr, norm_nonneg p]

/-- A unit `v` with `λ² ∣ v + e`, `e = ± 1`, is `-e`. -/
lemma eq_neg_of_lambda_sq_dvd (hv : IsUnit v) (he : e = 1 ∨ e = -1) (h : lambda ^ 2 ∣ v + e) :
    v = -e := by
  by_contra hne
  have h₁ := norm_le_of_dvd h fun h₀ => hne (by linear_combination h₀)
  have h₂ := norm_add_le v e
  rw [norm_lambda_sq] at h₁
  rw [isUnit_iff_norm_eq_one.mp hv, show norm e = 1 by rcases he with rfl | rfl <;> simp] at h₂
  linarith

lemma le_of_three_mul_cube_le {n K : R} (hK : 1 ≤ K) (hn : 0 ≤ n) (h : 3 * n ^ 3 ≤ 4 * K) :
    n ≤ K := by
  by_cases h1 : n ≤ 1
  · linarith
  · have h2 : 1 ≤ n - 1 := DiscretelyOrdered.one_le_of_pos _ (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hn (show (0 : R) ≤ n - 2 by linarith))
      (show (0 : R) ≤ n + 2 by linarith)]

lemma not_lambda_dvd_of_isCoprime (hpq : IsCoprime p q) (hp : lambda ∣ p) : ¬lambda ∣ q := by
  intro hq
  have := isUnit_iff_norm_eq_one.mp (hpq.isUnit_of_dvd' hp hq)
  norm_num [norm_lambda] at this

lemma solution_mul_root (h : Solution K a b c u) (hε : ε ^ 3 = 1) :
    Solution K a (ε * b) c u := by
  have hεu := IsUnit.of_pow_eq_one hε (by norm_num)
  exact ⟨h.norm_a_le, by simpa [norm_mul, isUnit_iff_norm_eq_one.mp hεu] using h.norm_b_le,
    h.isUnit_u, by linear_combination h.eq + b ^ 3 * hε, h.not_dvd_a,
    mt hεu.dvd_mul_left.mp h.not_dvd_b, h.dvd_c, h.c_ne_zero⟩

include hL

/-- A unit `v` with `λ³ ∣ Y³ + v Z³`, `λ ∤ Y`, `λ ∤ Z`, squares to `1`. -/
lemma sq_eq_one_of_lambda_cube_dvd {Y Z v : EisensteinInteger R} (hY : ¬lambda ∣ Y)
    (hZ : ¬lambda ∣ Z) (hv : IsUnit v) (h : lambda ^ 3 ∣ Y ^ 3 + v * Z ^ 3) : v ^ 2 = 1 := by
  have hsq (e : EisensteinInteger R) (he : e = 1 ∨ e = -1) : e ^ 2 = 1 := by
    rcases he with rfl | rfl <;> ring
  obtain ⟨e₁, he₁, h₁⟩ := exists_cube_mod hL hY
  obtain ⟨e₂, he₂, h₂⟩ := exists_cube_mod hL hZ
  have h34 : (lambda : EisensteinInteger R) ^ 3 ∣ lambda ^ 4 := pow_dvd_pow _ (by norm_num)
  have h3 : (lambda : EisensteinInteger R) ^ 3 ∣ v + e₁ * e₂ := by
    convert ((h.mul_left e₂).sub ((h34.trans h₁).mul_left e₂)).sub
      ((h34.trans h₂).mul_left (e₂ * v)) using 1
    linear_combination (-v) * hsq e₂ he₂
  have he : e₁ * e₂ = 1 ∨ e₁ * e₂ = -1 := by
    rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;> norm_num
  rw [eq_neg_of_lambda_sq_dvd hv he ((pow_dvd_pow _ (by norm_num)).trans h3), neg_sq]
  exact hsq _ he

/-- Either a solution has coprime `a` and `b`, or dividing by their gcd gives a smaller one. -/
lemma solution_reduce (h : Solution K a b c u) : IsCoprime a b ∨
    ∃ a' b' c' : EisensteinInteger R, Solution K a' b' c' u ∧ norm c' < norm c := by
  have := isBezout hL
  have ha : a ≠ 0 := fun h₀ => h.not_dvd_a (h₀ ▸ dvd_zero _)
  obtain ⟨d, a₀, b₀, c₀, rfl, rfl, rfl, hd, -, heq, hunit⟩ := exists_gcd_reduce ha h.isUnit_u h.eq
  by_cases hdu : IsUnit d
  · exact Or.inl (hunit hdu)
  right
  have h₁ := (one_le_norm hd).lt_of_ne fun h' => hdu (isUnit_iff_norm_eq_one.mpr h'.symm)
  have h₂ := DiscretelyOrdered.one_le_of_pos _ (sub_pos.2 h₁)
  have hc₀ : c₀ ≠ 0 := right_ne_zero_of_mul h.c_ne_zero
  have hld : ¬lambda ∣ d := fun hl => h.not_dvd_a (hl.mul_right _)
  have ha' := h.norm_a_le
  have hb' := h.norm_b_le
  rw [norm_mul] at ha' hb'
  use a₀, b₀, c₀
  refine ⟨⟨by nlinarith [norm_nonneg a₀], by nlinarith [norm_nonneg b₀], h.isUnit_u, heq,
    fun hl => h.not_dvd_a (hl.mul_left _), fun hl => h.not_dvd_b (hl.mul_left _),
    ((prime_lambda hL).dvd_or_dvd h.dvd_c).resolve_left hld, hc₀⟩, ?_⟩
  rw [norm_mul]
  nlinarith [one_le_norm hc₀]

/-- The cubes in `x y z = u c₁³` and the new solution they give. -/
lemma kummer_cubes {x y z u c₁ : EisensteinInteger R} (hu : IsUnit u) (hc₁ : c₁ ≠ 0)
    (hxyz : x * y * z = u * c₁ ^ 3) (hsum : x + ω * y + ω ^ 2 * z = 0) (hxy : IsCoprime x y)
    (hxz : IsCoprime x z) (hyz : IsCoprime y z) (hx : lambda ∣ x) (hy : ¬lambda ∣ y)
    (hz : ¬lambda ∣ z) : ∃ X Y Z v w : EisensteinInteger R, IsUnit w ∧ IsUnit v ∧
      Y ^ 3 + (v * Z) ^ 3 = w * X ^ 3 ∧ norm y = norm Y ^ 3 ∧ norm z = norm Z ^ 3 ∧
      lambda ∣ X ∧ ¬lambda ∣ Y ∧ ¬lambda ∣ Z ∧ X ≠ 0 ∧ norm X ≤ norm c₁ := by
  have := isBezout hL
  have hN (v : (EisensteinInteger R)ˣ) : norm (v : EisensteinInteger R) = 1 :=
    isUnit_iff_norm_eq_one.mp v.isUnit
  obtain ⟨X, u₁, hX⟩ := exists_unit_mul_cube hu (hxy.mul_right hxz) (by rw [← hxyz]; ring)
  obtain ⟨Y, u₂, hY⟩ := exists_unit_mul_cube hu (hyz.mul_right hxy.symm) (by rw [← hxyz]; ring)
  obtain ⟨Z, u₃, hZ⟩ :=
    exists_unit_mul_cube hu (hxz.symm.mul_right hyz.symm) (by rw [← hxyz]; ring)
  have hlY : ¬lambda ∣ Y := fun hl => hy (hY ▸ (dvd_pow hl (by norm_num)).mul_left _)
  have hlZ : ¬lambda ∣ Z := fun hl => hz (hZ ▸ (dvd_pow hl (by norm_num)).mul_left _)
  have hlX : lambda ∣ X :=
    (prime_lambda hL).dvd_of_dvd_pow ((IsUnit.dvd_mul_left u₁.isUnit).mp (hX ▸ hx))
  have hX0 : X ≠ 0 := by
    rintro rfl
    simp [hX, hu.ne_zero, hc₁] at hxyz
  obtain ⟨i, hU, hi⟩ : ∃ i : EisensteinInteger R, u₂ * i = 1 ∧ IsUnit i := by
    use ↑u₂⁻¹
    exact ⟨u₂.mul_inv, u₂⁻¹.isUnit⟩
  have hv : IsUnit ((ω : EisensteinInteger R) * u₃ * i) := (isUnit_omega.mul u₃.isUnit).mul hi
  have heq : Y ^ 3 + ((ω : EisensteinInteger R) * u₃ * i) * Z ^ 3 =
      -((ω : EisensteinInteger R) ^ 2 * u₁ * i) * X ^ 3 := by
    rw [hX, hY, hZ] at hsum
    linear_combination (ω ^ 2 * i) * hsum - Y ^ 3 * u₂ * i * omega_cube (R := R) - Y ^ 3 * hU -
      Z ^ 3 * u₃ * i * ω * omega_cube (R := R)
  have hv2 := sq_eq_one_of_lambda_cube_dvd hL hlY hlZ hv
    (heq ▸ (pow_dvd_pow_of_dvd hlX 3).mul_left _)
  have hle := norm_le_of_dvd (hxyz ▸ dvd_mul_of_dvd_left (dvd_mul_right x y) z)
    (mul_ne_zero hu.ne_zero (pow_ne_zero 3 hc₁))
  simp only [hX, norm_mul, norm_pow, hN, isUnit_iff_norm_eq_one.mp hu, one_mul] at hle
  use X, Y, Z, (ω : EisensteinInteger R) * u₃ * i,
    -((ω : EisensteinInteger R) ^ 2 * u₁ * i)
  exact ⟨(((isUnit_omega.pow 2).mul u₁.isUnit).mul hi).neg, hv,
    by linear_combination heq + ((ω : EisensteinInteger R) * u₃ * i) * Z ^ 3 * hv2,
    by simp [hY, norm_mul, hN], by simp [hZ, norm_mul, hN], hlX, hlY, hlZ, hX0,
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hle⟩

/-- The Kummer step for a solution with coprime `a`, `b` and `λ² ∣ a + b`. -/
lemma kummer_of_sq_dvd (h : Solution K a b c u) (hab : IsCoprime a b) (h2 : lambda ^ 2 ∣ a + b) :
    ∃ a' b' c' u', Solution K a' b' c' u' ∧ norm c' < norm c := by
  obtain ⟨m, hm⟩ := h2
  obtain ⟨c₁, hc⟩ := h.dvd_c
  have hS := one_add_omega_add_omega_sq (R := R)
  have hC := omega_cube (R := R)
  have hx : lambda * (lambda * m) = a + b := by rw [hm]; ring
  have hy : lambda * (lambda * m + b) = a + ω * b := by linear_combination hx
  have hz : lambda * (lambda * m - ω ^ 2 * b) = a + ω ^ 2 * b := by linear_combination hx - b * hC
  have hc₁ : c₁ ≠ 0 := right_ne_zero_of_mul (hc ▸ h.c_ne_zero)
  have hxyz : lambda * m * (lambda * m + b) * (lambda * m - ω ^ 2 * b) = u * c₁ ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 lambda_ne_zero)
    linear_combination (lambda * (lambda * m + b) * (lambda * (lambda * m - ω ^ 2 * b))) * hx +
      ((a + b) * (lambda * (lambda * m - ω ^ 2 * b))) * hy + ((a + b) * (a + ω * b)) * hz -
      sum_cubes_eq a b + h.eq + u * (c ^ 2 + c * (lambda * c₁) + (lambda * c₁) ^ 2) * hc
  have hly : ¬lambda ∣ lambda * m + b := fun hl =>
    h.not_dvd_b <| (dvd_add_right (dvd_mul_right lambda m)).mp hl
  have hlz : ¬lambda ∣ lambda * m - ω ^ 2 * b := fun hl =>
    h.not_dvd_b <| ((isUnit_omega.pow 2).dvd_mul_left).mp <|
      (dvd_sub_right (dvd_mul_right lambda m)).mp hl
  obtain ⟨X, Y, Z, v, w, hw, hv, heq, hNY, hNZ, hlX, hlY, hlZ, hX0, hNX⟩ :=
    kummer_cubes hL h.isUnit_u hc₁ hxyz (by linear_combination (lambda * m) * hS - ω * b * hC)
      (isCoprime_of_lin hab ω (-1) (-1) 1 (by linear_combination -hx) (by ring))
      (isCoprime_of_lin hab (-1) ω ω (-ω) (by linear_combination -hx + b * hC)
        (by linear_combination -b * hC))
      (isCoprime_of_lin hab ω (-1) (-ω ^ 2) (ω ^ 2) (by linear_combination -hx - b * hS)
        (by linear_combination b * hS + b * ω * hC))
      (dvd_mul_right _ _) hly hlz
  have hK : 1 ≤ K :=
    (one_le_norm (z := a) fun h₀ => h.not_dvd_a (h₀ ▸ dvd_zero _)).trans h.norm_a_le
  have hbound (W T : EisensteinInteger R) (hT : lambda * T = a + W * b) (hW : norm W = 1) :
      3 * norm T ≤ 4 * K := by
    have := congrArg norm hT
    rw [norm_mul, norm_lambda] at this
    have := norm_add_le a (W * b)
    rw [norm_mul, hW, one_mul] at this
    linarith [h.norm_a_le, h.norm_b_le]
  use Y, v * Z, X, w
  refine ⟨⟨le_of_three_mul_cube_le hK (norm_nonneg _) (hNY ▸ hbound ω _ hy norm_omega), ?_, hw,
    heq, hlY, mt hv.dvd_mul_left.mp hlZ, hlX, hX0⟩, ?_⟩
  · rw [norm_mul, isUnit_iff_norm_eq_one.mp hv, one_mul]
    exact le_of_three_mul_cube_le hK (norm_nonneg _)
      (hNZ ▸ hbound _ _ hz (by rw [norm_pow, norm_omega, one_pow]))
  · rw [hc, norm_mul, norm_lambda]
    nlinarith [one_le_norm hc₁]

/-- The Kummer step for a solution with coprime `a` and `b`. -/
lemma kummer (h : Solution K a b c u) (hab : IsCoprime a b) :
    ∃ a' b' c' u', Solution K a' b' c' u' ∧ norm c' < norm c := by
  have hC := omega_cube (R := R)
  have hC2 : ((ω : EisensteinInteger R) ^ 2) ^ 3 = 1 := by
    linear_combination (ω ^ 3 + 1 : EisensteinInteger R) * hC
  rcases exists_normalize hL h.not_dvd_a h.not_dvd_b h.dvd_c h.eq with h2 | h2 | h2
  · exact kummer_of_sq_dvd hL h hab h2
  · exact kummer_of_sq_dvd hL (solution_mul_root h hC) (isCoprime_mul_root hab hC) h2
  · exact kummer_of_sq_dvd hL (solution_mul_root h hC2) (isCoprime_mul_root hab hC2) h2

/-- Every solution gives one with a smaller `norm c`. -/
lemma descent (h : Solution K a b c u) :
    ∃ a' b' c' u', Solution K a' b' c' u' ∧ norm c' < norm c := by
  rcases solution_reduce hL h with hab | ⟨a', b', c', h', hlt⟩
  · exact kummer hL h hab
  · use a', b', c', u

lemma exists_solution (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h : a ^ 3 + b ^ 3 = c ^ 3) :
    ∃ (K : R) (a b c u : EisensteinInteger R), Solution K a b c u := by
  have := isBezout hL
  obtain ⟨d, a₀, b₀, c₀, rfl, rfl, rfl, -, hcop, heq, -⟩ :=
    exists_gcd_reduce ha isUnit_one (by rw [h, one_mul])
  rw [one_mul] at heq
  have hsol (x y z : EisensteinInteger R) (h : x ^ 3 + y ^ 3 = z ^ 3) (hx : ¬lambda ∣ x)
      (hy : ¬lambda ∣ y) (hz : lambda ∣ z) (hz0 : z ≠ 0) :
      ∃ (K : R) (a b c u : EisensteinInteger R), Solution K a b c u := by
    use max (norm x) (norm y), x, y, z, 1
    exact ⟨le_max_left _ _, le_max_right _ _, isUnit_one, by rw [one_mul, h], hx, hy, hz, hz0⟩
  by_cases hlc : lambda ∣ c₀
  · exact hsol _ _ _ heq (not_lambda_dvd_of_isCoprime (isCoprime_of_cube_eq hcop heq).symm hlc)
      (not_lambda_dvd_of_isCoprime (isCoprime_of_cube_eq hcop.symm (by linear_combination heq)).symm
        hlc) hlc (right_ne_zero_of_mul hc)
  by_cases hla : lambda ∣ a₀
  · exact hsol c₀ (-b₀) a₀ (by linear_combination -heq) hlc
      (not_lambda_dvd_of_isCoprime hcop hla ∘ dvd_neg.mp) hla (right_ne_zero_of_mul ha)
  by_cases hlb : lambda ∣ b₀
  · exact hsol c₀ (-a₀) b₀ (by linear_combination -heq) hlc
      (not_lambda_dvd_of_isCoprime hcop.symm hlb ∘ dvd_neg.mp) hlb (right_ne_zero_of_mul hb)
  exact absurd heq (case_one hL hla hlb hlc)

lemma not_dvd_iff : ¬lambda ∣ z ↔ ∃ s, z - 1 = lambda * s ∨ z + 1 = lambda * s := by
  constructor
  · intro hz
    rcases lambda_dvd_or hL z with h | ⟨s, hs⟩ | ⟨s, hs⟩
    · exact absurd h hz
    all_goals
      use s
      simp [hs]
  · rintro ⟨s, hs | hs⟩ ⟨t, ht⟩
    · exact not_lambda_dvd_one ⟨t - s, by linear_combination ht - hs⟩
    · exact not_lambda_dvd_one ⟨s - t, by linear_combination hs - ht⟩

lemma solution_iff_boundedExists {K m₀ m : R} (hm : m ≤ m₀) :
    (∃ a b c u : EisensteinInteger R, Solution K a b c u ∧ norm c = m) ↔
      BoundedExists (4 * (K + m₀) + 8) (descentPredicate K) m := by
  constructor
  · rintro ⟨a, b, c, u, h, rfl⟩
    obtain ⟨sa, hsa⟩ := (not_dvd_iff hL).mp h.not_dvd_a
    obtain ⟨sb, hsb⟩ := (not_dvd_iff hL).mp h.not_dvd_b
    obtain ⟨sc, hsc⟩ := h.dvd_c
    have hu := isUnit_iff_norm_eq_one.mp h.isUnit_u
    have hsc' := congrArg norm hsc
    rw [norm_mul, norm_lambda] at hsc'
    have hK := (norm_nonneg a).trans h.norm_a_le
    have hc := norm_nonneg c
    have bnd (z : EisensteinInteger R) (hz : norm z ≤ K + 1 + norm c) :
        |z.re| < 4 * (K + m₀) + 8 ∧ |z.im| < 4 * (K + m₀) + 8 := by
      constructor <;> linarith [abs_re_le z, abs_im_le z, norm_nonneg z]
    use ![a.re, a.im, b.re, b.im, c.re, c.im, u.re, u.im, sa.re, sa.im, sb.re, sb.im,
      sc.re, sc.im]
    constructor
    · intro j
      fin_cases j <;> simp [bnd a (by linarith [h.norm_a_le]), bnd b (by linarith [h.norm_b_le]),
        bnd c (by linarith), bnd u (by linarith), bnd sc (by linarith [norm_nonneg sc]),
        bnd sa (by linarith [norm_witness_le hsa, h.norm_a_le]),
        bnd sb (by linarith [norm_witness_le hsb, h.norm_b_le])]
    · simpa [descentPredicate, coordinate, hu] using
        ⟨h.norm_a_le, h.norm_b_le, h.eq, hsa, hsb, hsc, h.c_ne_zero⟩
  · rintro ⟨ys, -, h⟩
    simp only [descentPredicate, coordinate, Fin.cons_succ, Fin.cons_zero] at h
    obtain ⟨ha, hb, hu, heq, hsa, hsb, hsc, hc0, hm⟩ := h
    exact ⟨_, _, _, _, ⟨ha, hb, isUnit_iff_norm_eq_one.mpr hu, heq,
      (not_dvd_iff hL).mpr ⟨_, hsa⟩, (not_dvd_iff hL).mpr ⟨_, hsb⟩, ⟨_, hsc⟩, hc0⟩, hm.symm⟩

/-- There is no solution. -/
lemma no_solution (h : Solution K a b c u) : False := by
  have hS : BoundedExists (4 * (K + norm c) + 8) (descentPredicate K) (norm c) := by
    apply (solution_iff_boundedExists hL le_rfl).mp
    use a, b, c, u
  obtain ⟨m, -, hm, hleast⟩ := hL 14 _ (isOpen_descentPredicate K) _ _ (norm_nonneg c) hS
  have hmc : m ≤ norm c := not_lt.1 fun hlt => hleast _ (norm_nonneg c) hlt hS
  obtain ⟨a', b', c', u', h', rfl⟩ := (solution_iff_boundedExists hL hmc).mpr hm
  obtain ⟨a'', b'', c'', u'', h'', hlt⟩ := descent hL h'
  apply hleast _ (norm_nonneg _) hlt
  apply (solution_iff_boundedExists hL (hlt.le.trans hmc)).mp
  use a'', b'', c'', u''

end EisensteinInteger

namespace FermatThree

/-- Fermat's Last Theorem for exponent `3` in a discretely ordered ring satisfying
`LeastNumberPrinciple`. -/
theorem flt3_of_leastNumberPrinciple {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [DiscretelyOrdered R] (hL : LeastNumberPrinciple R) (x y z : R)
    (h : x ^ 3 + y ^ 3 = z ^ 3) : x = 0 ∨ y = 0 ∨ z = 0 := by
  by_contra hne
  obtain ⟨hx, hy, hz⟩ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by grind
  have hf := algebraMap_injective (R := R) (a := -1) (b := -1)
  obtain ⟨K, a, b, c, u, hs⟩ := EisensteinInteger.exists_solution hL
    (a := algebraMap R _ x) (b := algebraMap R _ y) (c := algebraMap R _ z)
    ((map_ne_zero_iff _ hf).mpr hx) ((map_ne_zero_iff _ hf).mpr hy)
    ((map_ne_zero_iff _ hf).mpr hz) (by rw [← map_pow, ← map_pow, ← map_add, h, map_pow])
  exact EisensteinInteger.no_solution hL hs

end FermatThree
