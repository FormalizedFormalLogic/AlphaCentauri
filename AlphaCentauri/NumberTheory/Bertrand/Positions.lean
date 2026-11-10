module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Exponential
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Prime
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Pigeonhole

/-!
# Positions in the factorizations of $1, \dots, m$

Over a model of $\mathsf{I}\Sigma_0 + \Omega_1$, fix `B` and `s` with $s \|2m\| < \|B\|$ and write
$\lambda(y) := \|y^s\| - 1 \approx s \log_2 y$. The sets
- $\mathrm{Bits}(m) = \{(k, y) : 1 \le k \le m, y < \lambda(k)\}$,
- $\mathrm{Level}(m) = \{(k, P, o) : 1 \le k \le m, P \mid k, P \text{ a power of the prime } p,
  o < \lambda(p)\}$,
- $\mathrm{Top}(m) = \{(k, i) : 1 \le k \le m, i < \|k\|\}$,
- $\mathrm{K}(m) = \{(P, o) : P \text{ a power of the prime } p, \lfloor 2m / P \rfloor
  \text{ odd}, o < \lambda(p)\}$

stand for $\log_2 m!$, its prime-power decomposition, the rounding errors, and
$\log_2 \binom{2m}{m}$. Between them there are $\Delta_0$-definable injections: cutting the
positions of $k^s$ at the prime-power divisors of $k$, Legendre's matching of the multiples of $P$
in $(m, 2m]$ with those in $[1, m]$, and doubling $\lambda(2k) = \lambda(k) + s$.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁]

namespace Bertrand

variable (B s : V)

/-- $\|y^s\| - 1$, which approximates $s \log_2 y$. -/
def scaledLength (y : V) : V := ‖bpow B y s‖ - 1

instance : 𝚺ᴬ₀.DefinableFunction₁ (scaledLength B s) := by
  unfold scaledLength
  definability

lemma scaledLength_lt (y : V) : scaledLength B s y < B ⨳ 1 :=
  lt_of_le_of_lt ((sub_le_self _ _).trans (length_le _)) (bpow_lt B y s)

instance : Bounded₁ (scaledLength B s) :=
  ⟨&(B ⨳ 1), fun _ ↦ by simpa using (scaledLength_lt B s _).le⟩

variable {B s}

section scaledLength

variable {u v y y' : V} (hB : 0 < B)
include hB

lemma one_le_length_bpow (hy : 0 < y) (h : s * ‖y‖ < ‖B‖) : 1 ≤ ‖bpow B y s‖ :=
  pos_iff_one_le.mp (length_pos_iff.mpr (bpow_pos hB hy h))

lemma scaledLength_one (hs : s < ‖B‖) : scaledLength B s 1 = 0 := by
  simp [scaledLength, bpow_one_left hB hs]

lemma scaledLength_le (hy : 0 < y) (h : s * ‖y‖ < ‖B‖) : scaledLength B s y ≤ s * ‖y‖ := by
  have := length_bpow_le hB hy h
  unfold scaledLength
  exact (tsub_le_iff_right.mpr this)

lemma scaledLength_monotone (hy : 0 < y) (hyy : y ≤ y') (h : s * ‖y'‖ < ‖B‖) :
    scaledLength B s y ≤ scaledLength B s y' :=
  tsub_le_tsub_right (length_monotone (bpow_monotone hB hy hyy h)) 1

lemma scaledLength_two_mul (hy : 0 < y) (h : s * ‖2 * y‖ < ‖B‖) :
    scaledLength B s (2 * y) = scaledLength B s y + s := by
  have hy' : s * ‖y‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_left (length_monotone (by simp))) h
  have h2 : s * ‖(2 : V)‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_left (length_monotone
    (le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hy)))) h
  obtain ⟨L, hL⟩ := le_iff_exists_add.mp (one_le_length_bpow hB hy hy')
  unfold scaledLength
  rw [bpow_mul hB two_pos hy h, length_bpow_two_mul hB (bpow_pos hB hy hy') h2, hL,
    add_comm 1 L, add_right_comm, add_sub_self, add_sub_self]

lemma add_scaledLength_le (hu : 0 < u) (hv : 0 < v) (h : s * ‖u * v‖ < ‖B‖) :
    scaledLength B s u + scaledLength B s v ≤ scaledLength B s (u * v) := by
  have hu' : s * ‖u‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_left (length_monotone
    (le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hv)))) h
  have hv' : s * ‖v‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_left (length_monotone
    (le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp hu)))) h
  have h3 := length_add_length_le (bpow_pos hB hu hu') (bpow_pos hB hv hv')
  obtain ⟨L, hL⟩ := le_iff_exists_add.mp (one_le_length_bpow hB hu hu')
  obtain ⟨L', hL'⟩ := le_iff_exists_add.mp (one_le_length_bpow hB hv hv')
  unfold scaledLength
  rw [bpow_mul hB hu hv h]
  rw [hL, hL'] at h3 ⊢
  rw [add_comm 1 L, add_comm 1 L', add_sub_self, add_sub_self]
  have : L + L' + 1 + 1 ≤ ‖bpow B u s * bpow B v s‖ + 1 := by grind
  exact le_tsub_of_add_le_right (by simpa using this)

lemma scaledLength_mul_le (hu : 0 < u) (hv : 0 < v) (h : s * ‖u * v‖ < ‖B‖) :
    scaledLength B s (u * v) ≤ scaledLength B s u + scaledLength B s v + 1 := by
  have hu' : s * ‖u‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_left (length_monotone
    (le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hv)))) h
  have hv' : s * ‖v‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_left (length_monotone
    (le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp hu)))) h
  have h3 := length_mul_le (bpow B u s) (bpow B v s)
  obtain ⟨L, hL⟩ := le_iff_exists_add.mp (one_le_length_bpow hB hu hu')
  obtain ⟨L', hL'⟩ := le_iff_exists_add.mp (one_le_length_bpow hB hv hv')
  unfold scaledLength
  rw [bpow_mul hB hu hv h]
  rw [hL, hL'] at h3 ⊢
  rw [add_comm 1 L, add_comm 1 L', add_sub_self, add_sub_self]
  exact tsub_le_iff_right.mpr (by grind)

end scaledLength

variable (B s)

/-- $\{(k, y) : 1 \le k \le m, y < \lambda(k)\}$. -/
def Bits (m w : V) : Prop :=
  ∃ k ≤ w, ∃ y ≤ w, w = ⟪k, y⟫ ∧ 0 < k ∧ k ≤ m ∧ y < scaledLength B s k

/-- $\{(k, P, o) : 1 \le k \le m, P \mid k, P \text{ a power of the prime } p, o < \lambda(p)\}$. -/
def Level (m w : V) : Prop :=
  ∃ k ≤ w, ∃ P ≤ w, ∃ o ≤ w, w = ⟪k, P, o⟫ ∧ 0 < k ∧ k ≤ m ∧ P ∣ k ∧
    ∃ p ≤ P, IsPrimePower p P ∧ o < scaledLength B s p

/-- $\{(k, i) : 1 \le k \le m, i < \|k\|\}$. -/
def Top (m w : V) : Prop := ∃ k ≤ w, ∃ i ≤ w, w = ⟪k, i⟫ ∧ 0 < k ∧ k ≤ m ∧ i < ‖k‖

/-- $\{(P, o) : P \text{ a power of the prime } p, \lfloor 2m / P \rfloor \text{ odd},
o < \lambda(p)\}$. -/
def Kummer (m w : V) : Prop :=
  ∃ P ≤ w, ∃ o ≤ w, w = ⟪P, o⟫ ∧ 2 * m / P % 2 = 1 ∧
    ∃ p ≤ P, IsPrimePower p P ∧ o < scaledLength B s p

/-- The numbers below `c`. -/
def Below (c w : V) : Prop := w < c

lemma definable_bits : 𝚺ᴬ₀.DefinableRel (Bits B s) := by
  unfold Bits
  definability

lemma definable_level : 𝚺ᴬ₀.DefinableRel (Level B s) := by
  unfold Level
  definability

lemma definable_top : 𝚺ᴬ₀.DefinableRel (Top : V → V → Prop) := by
  unfold Top
  definability

lemma definable_kummer : 𝚺ᴬ₀.DefinableRel (Kummer B s) := by
  unfold Kummer
  definability

/-- $(k, P, o) \mapsto (k, \lambda(k^{(P - 1)}) + o)$: the level `P` of `k` occupies the
positions of $k^s$ from $\lambda(k^{(P - 1)})$ on. -/
def LevelToBits (w v : V) : Prop :=
  ∃ k ≤ w, ∃ P ≤ w, ∃ o ≤ w, w = ⟪k, P, o⟫ ∧
    v = ⟪k, scaledLength B s (divisorUpTo k (P - 1)) + o⟫

/-- The position `y` of $k^s$ lies in the level `T + 1` of `k`; it goes to that level if its
offset is below $\lambda(p)$, and to `Top` otherwise. -/
def BitsToLevel (t₀ t₁ w v : V) : Prop :=
  ∃ k ≤ w, ∃ y ≤ w, w = ⟪k, y⟫ ∧ ∃ T < k,
    scaledLength B s (divisorUpTo k T) ≤ y ∧ y < scaledLength B s (divisorUpTo k (T + 1)) ∧
    ((∃ p ≤ T + 1, IsPrimePower p (T + 1) ∧
        y - scaledLength B s (divisorUpTo k T) < scaledLength B s p ∧
        v = ⟪t₀, ⟪k, T + 1, y - scaledLength B s (divisorUpTo k T)⟫⟫) ∨
      ((∀ p ≤ T + 1, IsPrimePower p (T + 1) →
          scaledLength B s p ≤ y - scaledLength B s (divisorUpTo k T)) ∧
        v = ⟪t₁, ⟪k, ‖divisorUpTo k T‖⟫⟫))

/-- Legendre's matching: the multiples $qP \le m$ stay, the multiples $qP \in (m, 2m]$ with
$q \le 2 \lfloor m / P \rfloor$ go to $(q - \lfloor m / P \rfloor) P$, and the last one, if
$\lfloor 2m / P \rfloor$ is odd, goes to `Kummer`. -/
def LegendreDown (m t₀ t₁ t₂ w v : V) : Prop :=
  ∃ k ≤ w, ∃ P ≤ w, ∃ o ≤ w, w = ⟪k, P, o⟫ ∧
    ((k ≤ m ∧ v = ⟪t₀, w⟫) ∨
      (m < k ∧ k / P ≤ 2 * (m / P) ∧ v = ⟪t₁, ⟪k - m / P * P, P, o⟫⟫) ∨
      (m < k ∧ 2 * (m / P) < k / P ∧ v = ⟪t₂, ⟪P, o⟫⟫))

/-- The inverse of Legendre's matching. -/
def LegendreUp (m t₀ t₁ t₂ u v : V) : Prop :=
  (π₁ u = t₀ ∧ v = π₂ u) ∨
    (π₁ u = t₁ ∧ ∃ k ≤ u, ∃ P ≤ u, ∃ o ≤ u, π₂ u = ⟪k, P, o⟫ ∧ v = ⟪k + m / P * P, P, o⟫) ∨
    (π₁ u = t₂ ∧ ∃ P ≤ u, ∃ o ≤ u, π₂ u = ⟪P, o⟫ ∧ v = ⟪2 * m / P * P, P, o⟫)

/-- $\lambda(2j) = \lambda(j) + s$ and $\lambda(2j - 1) \le \lambda(j) + s$: the positions of
$2j$ and $2j - 1$ below $\lambda(j)$ go to two copies of $(j, y)$, the others to numbers below
$2ms$. -/
def DoubleUp (m t₀ t₁ t₂ w v : V) : Prop :=
  ∃ k ≤ w, ∃ y ≤ w, w = ⟪k, y⟫ ∧
    ((k % 2 = 0 ∧ y < scaledLength B s (k / 2) ∧ v = ⟪t₀, ⟪k / 2, y⟫⟫) ∨
      (k % 2 = 0 ∧ scaledLength B s (k / 2) ≤ y ∧
        v = ⟪t₂, (k / 2 - 1) * s + (y - scaledLength B s (k / 2))⟫) ∨
      (k % 2 = 1 ∧ y < scaledLength B s (k / 2 + 1) ∧ v = ⟪t₁, ⟪k / 2 + 1, y⟫⟫) ∨
      (k % 2 = 1 ∧ scaledLength B s (k / 2 + 1) ≤ y ∧
        v = ⟪t₂, m * s + k / 2 * s + (y - scaledLength B s (k / 2 + 1))⟫))

/-- The two copies of $(j, y)$ go to $(2j, y)$ and $(2j + 1, y)$ (the last one to a number below
$\lambda(m)$), and $qs + t$ goes to the position $\lambda(j) + t$ of $2j$ or of $2j + 1$. -/
def DoubleDown (m t₀ t₁ t₂ t₃ t₄ u v : V) : Prop :=
  (π₁ u = t₀ ∧ ∃ k ≤ u, ∃ y ≤ u, π₂ u = ⟪k, y⟫ ∧ v = ⟪t₃, ⟪2 * k, y⟫⟫) ∨
    (π₁ u = t₁ ∧ ∃ k ≤ u, ∃ y ≤ u, π₂ u = ⟪k, y⟫ ∧
      ((k < m ∧ v = ⟪t₃, ⟪2 * k + 1, y⟫⟫) ∨ (m ≤ k ∧ v = ⟪t₄, y⟫))) ∨
    (π₁ u = t₂ ∧
      ((π₂ u / s < m ∧
          v = ⟪t₃, ⟪2 * (π₂ u / s + 1), scaledLength B s (π₂ u / s + 1) + π₂ u % s⟫⟫) ∨
        (m ≤ π₂ u / s ∧
          v = ⟪t₃, ⟪2 * (π₂ u / s - m + 1) + 1,
            scaledLength B s (π₂ u / s - m + 1) + π₂ u % s⟫⟫)))

lemma definable_levelToBits : 𝚺ᴬ₀.DefinableRel (LevelToBits B s) := by
  unfold LevelToBits
  definability

lemma definable_bitsToLevel (t₀ t₁ : V) : 𝚺ᴬ₀.DefinableRel (BitsToLevel B s t₀ t₁) := by
  unfold BitsToLevel
  definability

lemma definable_legendreDown (m t₀ t₁ t₂ : V) :
    𝚺ᴬ₀.DefinableRel (LegendreDown m t₀ t₁ t₂ : V → V → Prop) := by
  unfold LegendreDown
  definability

lemma definable_doubleDown (m t₀ t₁ t₂ t₃ t₄ : V) :
    𝚺ᴬ₀.DefinableRel (DoubleDown B s m t₀ t₁ t₂ t₃ t₄) := by
  unfold DoubleDown
  definability

variable {B s}

lemma exists_pair₂ (w : V) : ∃ a b, w = ⟪a, b⟫ := ⟨π₁ w, π₂ w, by simp⟩

lemma exists_pair₃ (w : V) : ∃ a b c, w = ⟪a, b, c⟫ := ⟨π₁ w, π₁ (π₂ w), π₂ (π₂ w), by simp⟩

lemma bits_pair_iff {m k y : V} :
    Bits B s m ⟪k, y⟫ ↔ 0 < k ∧ k ≤ m ∧ y < scaledLength B s k := by
  constructor
  · rintro ⟨k', -, y', -, h, hk⟩
    obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h
    exact hk
  · intro h
    exact ⟨k, by simp, y, by simp, rfl, h⟩

lemma top_pair_iff {m k i : V} : Top m ⟪k, i⟫ ↔ 0 < k ∧ k ≤ m ∧ i < ‖k‖ := by
  constructor
  · rintro ⟨k', -, i', -, h, hk⟩
    obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h
    exact hk
  · intro h
    exact ⟨k, by simp, i, by simp, rfl, h⟩

lemma level_pair_iff {m k P o : V} :
    Level B s m ⟪k, P, o⟫ ↔
      0 < k ∧ k ≤ m ∧ P ∣ k ∧ ∃ p ≤ P, IsPrimePower p P ∧ o < scaledLength B s p := by
  constructor
  · rintro ⟨k', -, P', -, o', -, h, hk⟩
    obtain ⟨rfl, h'⟩ := pair_ext_iff.mp h
    obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h'
    exact hk
  · intro h
    exact ⟨k, by simp, P, le_trans (by simp) (le_pair_right _ _), o,
      le_trans (by simp) (le_pair_right _ _), rfl, h⟩

lemma kummer_pair_iff {m P o : V} :
    Kummer B s m ⟪P, o⟫ ↔
      2 * m / P % 2 = 1 ∧ ∃ p ≤ P, IsPrimePower p P ∧ o < scaledLength B s p := by
  constructor
  · rintro ⟨P', -, o', -, h, hk⟩
    obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h
    exact hk
  · intro h
    exact ⟨P, by simp, o, by simp, rfl, h⟩

lemma levelToBits_pair {k P o v : V} :
    LevelToBits B s ⟪k, P, o⟫ v ↔ v = ⟪k, scaledLength B s (divisorUpTo k (P - 1)) + o⟫ := by
  constructor
  · rintro ⟨k', -, P', -, o', -, h, rfl⟩
    obtain ⟨rfl, h'⟩ := pair_ext_iff.mp h
    obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h'
    rfl
  · rintro rfl
    exact ⟨k, by simp, P, le_trans (by simp) (le_pair_right _ _), o,
      le_trans (by simp) (le_pair_right _ _), rfl, rfl⟩

lemma le_pair_of_le_right {a b : V} (c : V) (h : a ≤ b) : a ≤ ⟪c, b⟫ :=
  h.trans (le_pair_right _ _)

attribute [local simp] le_pair_of_le_right

lemma legendreDown_pair {m t₀ t₁ t₂ k P o v : V} :
    LegendreDown m t₀ t₁ t₂ ⟪k, P, o⟫ v ↔
      (k ≤ m ∧ v = ⟪t₀, ⟪k, P, o⟫⟫) ∨
        (m < k ∧ k / P ≤ 2 * (m / P) ∧ v = ⟪t₁, ⟪k - m / P * P, P, o⟫⟫) ∨
        (m < k ∧ 2 * (m / P) < k / P ∧ v = ⟪t₂, ⟪P, o⟫⟫) := by
  constructor
  · rintro ⟨k', -, P', -, o', -, h, H⟩
    simp only [pair_ext_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact H
  · intro H
    exact ⟨k, by simp, P, by simp, o, by simp, rfl, H⟩

lemma legendreUp_tag_zero {m t₀ t₁ t₂ x v : V} (h₀₁ : t₀ ≠ t₁) (h₀₂ : t₀ ≠ t₂) :
    LegendreUp m t₀ t₁ t₂ ⟪t₀, x⟫ v ↔ v = x := by
  unfold LegendreUp
  simp [h₀₁, h₀₂]

lemma legendreUp_tag_one {m t₀ t₁ t₂ x v : V} (h₀₁ : t₀ ≠ t₁) (h₁₂ : t₁ ≠ t₂) :
    LegendreUp m t₀ t₁ t₂ ⟪t₁, x⟫ v ↔
      ∃ k P o, x = ⟪k, P, o⟫ ∧ v = ⟪k + m / P * P, P, o⟫ := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, k, -, P, -, o, -, h, hv⟩ | ⟨h, -⟩)
    · exact absurd (by simpa using h.symm) h₀₁
    · exact ⟨k, P, o, by simpa using h, hv⟩
    · exact absurd (by simpa using h) h₁₂
  · rintro ⟨k, P, o, rfl, rfl⟩
    right
    left
    exact ⟨by simp, k, by simp, P, by simp, o, by simp, by simp, rfl⟩

lemma legendreUp_tag_two {m t₀ t₁ t₂ x v : V} (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂) :
    LegendreUp m t₀ t₁ t₂ ⟪t₂, x⟫ v ↔ ∃ P o, x = ⟪P, o⟫ ∧ v = ⟪2 * m / P * P, P, o⟫ := by
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, P, -, o, -, h, hv⟩)
    · exact absurd (by simpa using h.symm) h₀₂
    · exact absurd (by simpa using h.symm) h₁₂
    · exact ⟨P, o, by simpa using h, hv⟩
  · rintro ⟨P, o, rfl, rfl⟩
    right
    right
    exact ⟨by simp, P, by simp, o, by simp, by simp, rfl⟩

lemma doubleUp_pair {m t₀ t₁ t₂ k y v : V} :
    DoubleUp B s m t₀ t₁ t₂ ⟪k, y⟫ v ↔
      ((k % 2 = 0 ∧ y < scaledLength B s (k / 2) ∧ v = ⟪t₀, ⟪k / 2, y⟫⟫) ∨
        (k % 2 = 0 ∧ scaledLength B s (k / 2) ≤ y ∧
          v = ⟪t₂, (k / 2 - 1) * s + (y - scaledLength B s (k / 2))⟫) ∨
        (k % 2 = 1 ∧ y < scaledLength B s (k / 2 + 1) ∧ v = ⟪t₁, ⟪k / 2 + 1, y⟫⟫) ∨
        (k % 2 = 1 ∧ scaledLength B s (k / 2 + 1) ≤ y ∧
          v = ⟪t₂, m * s + k / 2 * s + (y - scaledLength B s (k / 2 + 1))⟫)) := by
  constructor
  · rintro ⟨k', -, y', -, h, H⟩
    simp only [pair_ext_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    exact H
  · intro H
    exact ⟨k, by simp, y, by simp, rfl, H⟩

lemma doubleDown_tag_zero {m t₀ t₁ t₂ t₃ t₄ x v : V} (h₀₁ : t₀ ≠ t₁) (h₀₂ : t₀ ≠ t₂) :
    DoubleDown B s m t₀ t₁ t₂ t₃ t₄ ⟪t₀, x⟫ v ↔ ∃ k y, x = ⟪k, y⟫ ∧ v = ⟪t₃, ⟪2 * k, y⟫⟫ := by
  constructor
  · rintro (⟨-, k, -, y, -, h, hv⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact ⟨k, y, by simpa using h, hv⟩
    · exact absurd (by simpa using h) h₀₁
    · exact absurd (by simpa using h) h₀₂
  · rintro ⟨k, y, rfl, rfl⟩
    left
    exact ⟨by simp, k, by simp, y, by simp, by simp, rfl⟩

lemma doubleDown_tag_one {m t₀ t₁ t₂ t₃ t₄ x v : V} (h₀₁ : t₀ ≠ t₁) (h₁₂ : t₁ ≠ t₂) :
    DoubleDown B s m t₀ t₁ t₂ t₃ t₄ ⟪t₁, x⟫ v ↔ ∃ k y, x = ⟪k, y⟫ ∧
      ((k < m ∧ v = ⟪t₃, ⟪2 * k + 1, y⟫⟫) ∨ (m ≤ k ∧ v = ⟪t₄, y⟫)) := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, k, -, y, -, h, hv⟩ | ⟨h, -⟩)
    · exact absurd (by simpa using h.symm) h₀₁
    · exact ⟨k, y, by simpa using h, hv⟩
    · exact absurd (by simpa using h) h₁₂
  · rintro ⟨k, y, rfl, H⟩
    right
    left
    exact ⟨by simp, k, by simp, y, by simp, by simp, H⟩

lemma doubleDown_tag_two {m t₀ t₁ t₂ t₃ t₄ x v : V} (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂) :
    DoubleDown B s m t₀ t₁ t₂ t₃ t₄ ⟪t₂, x⟫ v ↔
      ((x / s < m ∧
          v = ⟪t₃, ⟪2 * (x / s + 1), scaledLength B s (x / s + 1) + x % s⟫⟫) ∨
        (m ≤ x / s ∧
          v = ⟪t₃, ⟪2 * (x / s - m + 1) + 1, scaledLength B s (x / s - m + 1) + x % s⟫⟫)) := by
  unfold DoubleDown
  simp [h₀₂.symm, h₁₂.symm]

section division

variable {k m P : V}

lemma two_mul_div_bounds (hP : 0 < P) :
    2 * (m / P) ≤ 2 * m / P ∧ 2 * m / P ≤ 2 * (m / P) + 1 := by
  have h1 := mul_div_le m P
  have h2 := lt_mul_div m hP
  have h3 := mul_div_le (2 * m) P
  have h4 := lt_mul_div (2 * m) hP
  constructor
  · apply lt_succ_iff_le.mp
    apply lt_of_mul_lt_mul_left (a := P)
    calc
      P * (2 * (m / P)) = 2 * (P * (m / P)) := by grind
      _ ≤ 2 * m := mul_le_mul_left h1
      _ < P * (2 * m / P + 1) := h4
  · apply lt_succ_iff_le.mp
    apply lt_of_mul_lt_mul_left (a := P)
    calc
      P * (2 * m / P) ≤ 2 * m := h3
      _ < 2 * (P * (m / P + 1)) := by
        rw [two_mul, two_mul]
        exact add_lt_add_of_lt_of_le h2 h2.le
      _ = P * (2 * (m / P) + 1 + 1) := by grind

lemma legendre_mid (hP : 0 < P) (hd : P ∣ k) (hmk : m < k) (hq : k / P ≤ 2 * (m / P)) :
    0 < k - m / P * P ∧ k - m / P * P ≤ m ∧ P ∣ k - m / P * P := by
  obtain ⟨q, rfl⟩ := hd
  rw [div_mul_right q hP] at hq
  have hf := mul_div_le m P
  obtain ⟨r, rfl⟩ := exists_add_of_le (lt_of_mul_lt_mul_left (hf.trans_lt hmk)).le
  have e : P * (m / P + r) - m / P * P = P * r := by
    rw [mul_add, mul_comm (m / P) P]
    exact add_sub_self'
  have hr₀ : 0 < r := (lt_add_iff_pos_right _).mp (lt_of_mul_lt_mul_left (hf.trans_lt hmk))
  have hr : r ≤ m / P := by
    rw [two_mul] at hq
    exact le_of_add_le_add_left hq
  rw [e]
  exact ⟨mul_pos hP hr₀, (mul_le_mul_left hr).trans hf, dvd_mul_right P r⟩

lemma legendre_top (hP : 0 < P) (hd : P ∣ k) (hk2 : k ≤ 2 * m) (hq : 2 * (m / P) < k / P) :
    k = P * (2 * m / P) ∧ 2 * m / P % 2 = 1 := by
  obtain ⟨q, rfl⟩ := hd
  rw [div_mul_right q hP] at hq
  have hqx : q ≤ 2 * m / P :=
    lt_succ_iff_le.mp (lt_of_mul_lt_mul_left (a := P) (hk2.trans_lt (lt_mul_div (2 * m) hP)))
  have hq' : q = 2 * (m / P) + 1 :=
    le_antisymm (hqx.trans (two_mul_div_bounds hP).2) (succ_le_iff_lt.mpr hq)
  have hx : 2 * m / P = 2 * (m / P) + 1 :=
    le_antisymm (two_mul_div_bounds hP).2 (by rw [← hq']; exact hqx)
  rw [hx, hq']
  simp

lemma legendre_up_mid (hP : 0 < P) (hd : P ∣ k) (hk : 0 < k) (hkm : k ≤ m) :
    m < k + m / P * P ∧ k + m / P * P ≤ 2 * (m / P * P) ∧ P ∣ k + m / P * P := by
  have h1 : k ≤ m / P * P := calc
    k = P * (k / P) := (mul_div_self_of_dvd.mpr hd).symm
    _ ≤ P * (m / P) := mul_le_mul_left (div_monotone hkm P)
    _ = m / P * P := mul_comm _ _
  obtain ⟨q, hq⟩ := hd
  and_intros
  · calc
      m < P * (m / P + 1) := lt_mul_div m hP
      _ = m / P * P + P := by grind
      _ ≤ m / P * P + k := (add_le_add_iff_left _).mpr (le_of_dvd hk ⟨q, hq⟩)
      _ = k + m / P * P := add_comm _ _
  · rw [two_mul]
    exact (add_le_add_iff_right _).mpr h1
  · use q + m / P
    grind

lemma legendre_up_top (hP : 0 < P) (hodd : 2 * m / P % 2 = 1) :
    0 < 2 * m / P * P ∧ 2 * m / P * P ≤ 2 * m ∧ m < 2 * m / P * P ∧
      2 * (m / P * P) < 2 * m / P * P := by
  have hx : 2 * m / P = 2 * (m / P) + 1 := by
    rcases (two_mul_div_bounds (m := m) hP).1.eq_or_lt with h' | h'
    · simp [← h'] at hodd
    · exact le_antisymm (two_mul_div_bounds hP).2 (succ_le_iff_lt.mpr h')
  have h3 : 2 * m / P * P ≤ 2 * m := div_mul_le (2 * m) P
  have e : (2 * (m / P) + 1) * P = 2 * (m / P * P) + P := by grind
  rw [hx] at h3 ⊢
  rw [e] at h3 ⊢
  refine ⟨lt_of_lt_of_le hP le_add_self, h3, ?_, lt_add_of_pos_right _ hP⟩
  calc
    m < P * (m / P + 1) := lt_mul_div m hP
    _ = m / P * P + P := by grind
    _ ≤ 2 * (m / P * P) + P := by
      rw [two_mul]
      exact (add_le_add_iff_right _).mpr le_self_add

end division

section levels

variable {k m p T T' : V} (hB : 0 < B) (hBm : s * ‖2 * m‖ < ‖B‖)

include hBm in
lemma mul_length_lt_of_le {y : V} (h : y ≤ 2 * m) : s * ‖y‖ < ‖B‖ :=
  lt_of_le_of_lt (mul_le_mul_left (length_monotone h)) hBm

lemma divisorUpTo_succ_eq (hk : 0 < k) (hP : IsPrimePower p (T + 1)) (hd : T + 1 ∣ k) :
    divisorUpTo k (T + 1) = p * divisorUpTo k T := by
  have h1 := mul_divisorUpTo_le hk hP hd
  obtain ⟨p', hp', -, h2⟩ := exists_isPrimePower_of_divisorUpTo_lt hk
    (lt_of_lt_of_le (lt_mul_of_one_lt_left (divisorUpTo_pos (T := T) hk) hP.1.1) h1)
  obtain rfl := hP.unique hp'
  exact le_antisymm h2 h1

lemma length_divisorUpTo_lt_succ (hk : 0 < k) (hP : IsPrimePower p (T + 1)) (hd : T + 1 ∣ k) :
    ‖divisorUpTo k T‖ < ‖divisorUpTo k (T + 1)‖ := by
  have h2 : (2 : V) ≤ p := by simpa [one_add_one_eq_two] using succ_le_iff_lt.mpr hP.1.1
  rw [divisorUpTo_succ_eq hk hP hd]
  calc
    ‖divisorUpTo k T‖ < ‖divisorUpTo k T‖ + 1 := lt_add_one _
    _ = ‖2 * divisorUpTo k T‖ := (length_two_mul_of_pos (divisorUpTo_pos hk)).symm
    _ ≤ ‖p * divisorUpTo k T‖ := length_monotone (mul_le_mul_right h2)

lemma length_divisorUpTo_lt_length (hk : 0 < k) (hP : IsPrimePower p (T + 1)) (hd : T + 1 ∣ k) :
    ‖divisorUpTo k T‖ < ‖k‖ :=
  (length_divisorUpTo_lt_succ hk hP hd).trans_le (length_monotone (divisorUpTo_le k _))

lemma length_divisorUpTo_lt (hk : 0 < k) (hP : IsPrimePower p (T + 1)) (hd : T + 1 ∣ k)
    (hlt : T < T') : ‖divisorUpTo k T‖ < ‖divisorUpTo k T'‖ :=
  (length_divisorUpTo_lt_succ hk hP hd).trans_le
    (length_monotone (divisorUpTo_monotone (succ_le_iff_lt.mpr hlt)))

include hB hBm

lemma scaledLength_divisorUpTo_monotone (hk : 0 < k) (hkm : k ≤ 2 * m) (h : T ≤ T') :
    scaledLength B s (divisorUpTo k T) ≤ scaledLength B s (divisorUpTo k T') :=
  scaledLength_monotone hB (divisorUpTo_pos hk) (divisorUpTo_monotone h)
    (mul_length_lt_of_le hBm ((divisorUpTo_le k T').trans hkm))

lemma scaledLength_divisorUpTo_le (hk : 0 < k) (hkm : k ≤ 2 * m) :
    scaledLength B s (divisorUpTo k T) ≤ scaledLength B s k :=
  scaledLength_monotone hB (divisorUpTo_pos hk) (divisorUpTo_le k T) (mul_length_lt_of_le hBm hkm)

lemma scaledLength_divisorUpTo_succ (hk : 0 < k) (hkm : k ≤ 2 * m)
    (hP : IsPrimePower p (T + 1)) (hd : T + 1 ∣ k) :
    scaledLength B s (divisorUpTo k T) + scaledLength B s p ≤
        scaledLength B s (divisorUpTo k (T + 1)) ∧
      scaledLength B s (divisorUpTo k (T + 1)) ≤
        scaledLength B s (divisorUpTo k T) + scaledLength B s p + 1 := by
  have hle : divisorUpTo k T * p ≤ k := by
    rw [mul_comm, ← divisorUpTo_succ_eq hk hP hd]
    exact divisorUpTo_le _ _
  have hr := mul_length_lt_of_le hBm (hle.trans hkm)
  rw [divisorUpTo_succ_eq hk hP hd, mul_comm p]
  exact ⟨add_scaledLength_le hB (divisorUpTo_pos hk) (pos_of_gt hP.1.1) hr,
    scaledLength_mul_le hB (divisorUpTo_pos hk) (pos_of_gt hP.1.1) hr⟩

lemma add_lt_scaledLength_divisorUpTo_succ {o : V} (hk : 0 < k) (hkm : k ≤ 2 * m)
    (hP : IsPrimePower p (T + 1)) (hd : T + 1 ∣ k) (ho : o < scaledLength B s p) :
    scaledLength B s (divisorUpTo k T) + o < scaledLength B s (divisorUpTo k (T + 1)) :=
  lt_of_lt_of_le ((add_lt_add_iff_left _).mpr ho)
    (scaledLength_divisorUpTo_succ hB hBm hk hkm hP hd).1

lemma exists_segment {y : V} (hk : 0 < k) (hkm : k ≤ 2 * m) (hy : y < scaledLength B s k) :
    ∃ T < k, scaledLength B s (divisorUpTo k T) ≤ y ∧
      y < scaledLength B s (divisorUpTo k (T + 1)) := by
  obtain ⟨T', hT', hmin⟩ := ISigma0.least_number
    (P := fun T ↦ y < scaledLength B s (divisorUpTo k T)) (by definability) (x := k)
    (by simpa [divisorUpTo_self hk] using hy)
  have hT'0 : T' ≠ 0 := by
    rintro rfl
    simp [divisorUpTo_zero hk, scaledLength_one hB
    (lt_of_le_of_lt (le_mul_of_one_le_right (Arithmetic.zero_le _)
      (pos_iff_one_le.mp (length_pos_iff.mpr hk))) (mul_length_lt_of_le hBm hkm))] at hT'
  obtain ⟨T, rfl⟩ := eq_succ_of_pos (pos_of_ne_zero hT'0)
  refine ⟨T, ?_, not_lt.mp (hmin T (lt_succ_iff_le.mpr le_rfl)), hT'⟩
  by_contra! hle
  exact hmin k (lt_succ_iff_le.mpr hle) (by simpa [divisorUpTo_self hk] using hy)

lemma exists_level_of_segment {y : V} (hk : 0 < k) (hkm : k ≤ 2 * m)
    (h : scaledLength B s (divisorUpTo k T) ≤ y)
    (h' : y < scaledLength B s (divisorUpTo k (T + 1))) :
    ∃ p, IsPrimePower p (T + 1) ∧ T + 1 ∣ k := by
  have hlt : divisorUpTo k T < divisorUpTo k (T + 1) := by
    by_contra! hle
    exact absurd (h.trans_lt h') (not_lt.mpr (scaledLength_monotone hB (divisorUpTo_pos hk) hle
      (mul_length_lt_of_le hBm ((divisorUpTo_le k T).trans hkm))))
  obtain ⟨p, hp, hd, -⟩ := exists_isPrimePower_of_divisorUpTo_lt hk hlt
  exact ⟨p, hp, hd⟩

lemma eq_add_scaledLength_of_le {y : V} (hk : 0 < k) (hkm : k ≤ 2 * m)
    (hP : IsPrimePower p (T + 1)) (hd : T + 1 ∣ k)
    (h₂ : y < scaledLength B s (divisorUpTo k (T + 1)))
    (h₁ : scaledLength B s (divisorUpTo k T) ≤ y)
    (h : scaledLength B s p ≤ y - scaledLength B s (divisorUpTo k T)) :
    y = scaledLength B s (divisorUpTo k T) + scaledLength B s p := by
  have h3 := (scaledLength_divisorUpTo_succ hB hBm hk hkm hP hd).2
  have h4 : y < scaledLength B s (divisorUpTo k T) + (scaledLength B s p + 1) := by
    rw [← add_assoc]
    exact h₂.trans_le h3
  rw [← sub_add_self_of_le h₁, add_comm] at h4 ⊢
  have := lt_succ_iff_le.mp ((add_lt_add_iff_left _).mp h4)
  rw [le_antisymm this h]

lemma bitsToLevel_pair {t₀ t₁ y v : V} (hk : 0 < k) (hkm : k ≤ 2 * m) :
    BitsToLevel B s t₀ t₁ ⟪k, y⟫ v ↔ ∃ T < k, ∃ p, IsPrimePower p (T + 1) ∧ T + 1 ∣ k ∧
      scaledLength B s (divisorUpTo k T) ≤ y ∧
      y < scaledLength B s (divisorUpTo k (T + 1)) ∧
      ((y - scaledLength B s (divisorUpTo k T) < scaledLength B s p ∧
          v = ⟪t₀, ⟪k, T + 1, y - scaledLength B s (divisorUpTo k T)⟫⟫) ∨
        (scaledLength B s p ≤ y - scaledLength B s (divisorUpTo k T) ∧
          v = ⟪t₁, ⟪k, ‖divisorUpTo k T‖⟫⟫)) := by
  constructor
  · rintro ⟨k', -, y', -, h, T, hT, h₁, h₂, ⟨p, -, hp, hlt, hv⟩ | ⟨hall, hv⟩⟩
    · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h
      obtain ⟨-, -, hd⟩ := exists_level_of_segment hB hBm hk hkm h₁ h₂
      exact ⟨T, hT, p, hp, hd, h₁, h₂, Or.inl ⟨hlt, hv⟩⟩
    · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h
      obtain ⟨p, hp, hd⟩ := exists_level_of_segment hB hBm hk hkm h₁ h₂
      exact ⟨T, hT, p, hp, hd, h₁, h₂, Or.inr ⟨hall p (le_of_dvd hp.pos hp.dvd) hp, hv⟩⟩
  · rintro ⟨T, hT, p, hp, hd, h₁, h₂, ⟨hlt, hv⟩ | ⟨hle, hv⟩⟩
    · exact ⟨k, by simp, y, by simp, rfl, T, hT, h₁, h₂,
        Or.inl ⟨p, le_of_dvd hp.pos hp.dvd, hp, hlt, hv⟩⟩
    · refine ⟨k, by simp, y, by simp, rfl, T, hT, h₁, h₂, Or.inr ⟨fun p' _ hp' ↦ ?_, hv⟩⟩
      obtain rfl := hp.unique hp'
      exact hle

end levels

section legendre

variable {m t₀ t₁ t₂ u v : V}

lemma legendreUp_shape (h₀₁ : t₀ ≠ t₁) (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂)
    (hu : Tagged t₀ (Level B s m) u ∨ Tagged t₁ (Level B s m) u ∨ Tagged t₂ (Kummer B s m) u)
    (hv : LegendreUp m t₀ t₁ t₂ u v) :
    Level B s (2 * m) v ∧ ∃ K P o, v = ⟪K, P, o⟫ ∧
      ((K ≤ m ∧ u = ⟪t₀, v⟫) ∨
        (m < K ∧ K ≤ 2 * (m / P * P) ∧ ∃ k, u = ⟪t₁, ⟪k, P, o⟫⟫ ∧ K = k + m / P * P) ∨
        (2 * (m / P * P) < K ∧ m < K ∧ u = ⟪t₂, ⟪P, o⟫⟫ ∧ K = 2 * m / P * P)) := by
  obtain ⟨t, x, rfl⟩ := exists_pair₂ u
  simp only [Tagged, pi₁_pair, pi₂_pair] at hu
  rcases hu with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · obtain ⟨k, P, o, rfl⟩ := exists_pair₃ x
    obtain rfl := (legendreUp_tag_zero h₀₁ h₀₂).mp hv
    obtain ⟨hk, hkm, hd, p, hpP, hp, ho⟩ := level_pair_iff.mp hx
    exact ⟨level_pair_iff.mpr ⟨hk, hkm.trans (by simp), hd, p, hpP, hp, ho⟩, k, P, o, rfl,
      Or.inl ⟨hkm, rfl⟩⟩
  · obtain ⟨k, P, o, rfl⟩ := exists_pair₃ x
    obtain ⟨k', P', o', he, rfl⟩ := (legendreUp_tag_one h₀₁ h₁₂).mp hv
    simp only [pair_ext_iff] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨hk, hkm, hd, p, hpP, hp, ho⟩ := level_pair_iff.mp hx
    obtain ⟨h₁, h₂, h₃⟩ := legendre_up_mid hp.pos hd hk hkm
    exact ⟨level_pair_iff.mpr ⟨pos_of_gt h₁, h₂.trans (mul_le_mul_left (div_mul_le m P)), h₃, p,
      hpP, hp, ho⟩, _, P, o, rfl, Or.inr (Or.inl ⟨h₁, h₂, k, rfl, rfl⟩)⟩
  · obtain ⟨P, o, rfl⟩ := exists_pair₂ x
    obtain ⟨P', o', he, rfl⟩ := (legendreUp_tag_two h₀₂ h₁₂).mp hv
    simp only [pair_ext_iff] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hodd, p, hpP, hp, ho⟩ := kummer_pair_iff.mp hx
    obtain ⟨h₁, h₂, h₃, h₄⟩ := legendre_up_top hp.pos hodd
    exact ⟨level_pair_iff.mpr ⟨h₁, h₂, dvd_mul_left P _, p, hpP, hp, ho⟩, _, P, o, rfl,
      Or.inr (Or.inr ⟨h₄, h₃, rfl, rfl⟩)⟩

end legendre

section injections

variable {m t₀ t₁ t₂ t₃ t₄ : V} (hB : 0 < B) (hs : 0 < s) (hBm : s * ‖2 * m‖ < ‖B‖)
include hB hs hBm

omit hs in
lemma isInj_levelToBits : IsInj (LevelToBits B s) (Level B s m) (Bits B s m) := by
  and_intros
  · intro w _
    obtain ⟨k, P, o, rfl⟩ := exists_pair₃ w
    exact ⟨_, levelToBits_pair.mpr rfl⟩
  · intro w v hw hv
    obtain ⟨k, P, o, rfl⟩ := exists_pair₃ w
    obtain rfl := levelToBits_pair.mp hv
    obtain ⟨hk, hkm, hd, p, -, hP, ho⟩ := level_pair_iff.mp hw
    obtain ⟨T, rfl⟩ := eq_succ_of_pos hP.pos
    rw [bits_pair_iff]
    refine ⟨hk, hkm, ?_⟩
    simpa using
      (add_lt_scaledLength_divisorUpTo_succ hB hBm hk (hkm.trans (by simp)) hP hd ho).trans_le
      (scaledLength_divisorUpTo_le hB hBm hk (hkm.trans (by simp)))
  · intro w w' v hw hw' hv hv'
    obtain ⟨k, P, o, rfl⟩ := exists_pair₃ w
    obtain ⟨k', P', o', rfl⟩ := exists_pair₃ w'
    obtain rfl := levelToBits_pair.mp hv
    obtain ⟨rfl, h⟩ := pair_ext_iff.mp (levelToBits_pair.mp hv')
    obtain ⟨hk, hkm, hd, p, -, hP, ho⟩ := level_pair_iff.mp hw
    obtain ⟨-, -, hd', p', -, hP', ho'⟩ := level_pair_iff.mp hw'
    obtain ⟨T, rfl⟩ := eq_succ_of_pos hP.pos
    obtain ⟨T', rfl⟩ := eq_succ_of_pos hP'.pos
    have hkm' : k ≤ 2 * m := hkm.trans (by simp)
    simp only [add_tsub_cancel_right] at h
    have key {T T' p o o'} (hP : IsPrimePower p (T + 1)) (hd : T + 1 ∣ k)
        (ho : o < scaledLength B s p)
        (hlt : T < T') : scaledLength B s (divisorUpTo k T) + o <
          scaledLength B s (divisorUpTo k T') + o' :=
      (add_lt_scaledLength_divisorUpTo_succ hB hBm hk hkm' hP hd ho).trans_le
        ((scaledLength_divisorUpTo_monotone hB hBm hk hkm' (succ_le_iff_lt.mpr hlt)).trans
          le_self_add)
    obtain rfl : T = T' := by
      rcases lt_trichotomy T T' with hlt | heq | hgt
      · exact absurd h (key hP hd ho hlt).ne
      · exact heq
      · exact absurd h.symm (key hP' hd' ho' hgt).ne
    simp [add_left_cancel h]

omit hs in
lemma isInj_bitsToLevel (h₀₁ : t₀ ≠ t₁) :
    IsInj (BitsToLevel B s t₀ t₁) (Bits B s m)
      (fun v ↦ Tagged t₀ (Level B s m) v ∨ Tagged t₁ (Top m) v) := by
  and_intros
  · intro w hw
    obtain ⟨k, y, rfl⟩ := exists_pair₂ w
    obtain ⟨hk, hkm, hy⟩ := bits_pair_iff.mp hw
    have hkm' : k ≤ 2 * m := hkm.trans (by simp)
    obtain ⟨T, hT, h₁, h₂⟩ := exists_segment hB hBm hk hkm' hy
    obtain ⟨p, hp, hd⟩ := exists_level_of_segment hB hBm hk hkm' h₁ h₂
    by_cases hlt : y - scaledLength B s (divisorUpTo k T) < scaledLength B s p
    · exact ⟨_, (bitsToLevel_pair hB hBm hk hkm').mpr ⟨T, hT, p, hp, hd, h₁, h₂, Or.inl ⟨hlt, rfl⟩⟩⟩
    · exact ⟨_, (bitsToLevel_pair hB hBm hk hkm').mpr
        ⟨T, hT, p, hp, hd, h₁, h₂, Or.inr ⟨not_lt.mp hlt, rfl⟩⟩⟩
  · intro w v hw hv
    obtain ⟨k, y, rfl⟩ := exists_pair₂ w
    obtain ⟨hk, hkm, hy⟩ := bits_pair_iff.mp hw
    have hkm' : k ≤ 2 * m := hkm.trans (by simp)
    obtain ⟨T, hT, p, hp, hd, h₁, h₂, ⟨hlt, rfl⟩ | ⟨hle, rfl⟩⟩ :=
      (bitsToLevel_pair hB hBm hk hkm').mp hv
    · left
      refine ⟨by simp, ?_⟩
      rw [pi₂_pair, level_pair_iff]
      exact ⟨hk, hkm, hd, p, le_of_dvd hp.pos hp.dvd, hp, hlt⟩
    · right
      refine ⟨by simp, ?_⟩
      rw [pi₂_pair, top_pair_iff]
      exact ⟨hk, hkm, length_divisorUpTo_lt_length hk hp hd⟩
  · intro w w' v hw hw' hv hv'
    obtain ⟨k, y, rfl⟩ := exists_pair₂ w
    obtain ⟨k', y', rfl⟩ := exists_pair₂ w'
    obtain ⟨hk, hkm, hy⟩ := bits_pair_iff.mp hw
    obtain ⟨hk', hkm', hy'⟩ := bits_pair_iff.mp hw'
    have hkm2 : k ≤ 2 * m := hkm.trans (by simp)
    obtain ⟨T, hT, p, hp, hd, h₁, h₂, H⟩ := (bitsToLevel_pair hB hBm hk hkm2).mp hv
    obtain ⟨T', hT', p', hp', hd', h₁', h₂', H'⟩ :=
      (bitsToLevel_pair hB hBm hk' (hkm'.trans (by simp))).mp hv'
    rcases H with ⟨hlt, e⟩ | ⟨hle, e⟩ <;> rcases H' with ⟨hlt', e'⟩ | ⟨hle', e'⟩ <;>
      have e'' := e.symm.trans e' <;> simp only [pair_ext_iff] at e''
    · obtain ⟨-, rfl, hTT, ho⟩ := e''
      obtain rfl := add_right_cancel hTT
      rw [← sub_add_self_of_le h₁, ← sub_add_self_of_le h₁', ho]
    · exact absurd e''.1 h₀₁
    · exact absurd e''.1.symm h₀₁
    · obtain ⟨-, rfl, hl⟩ := e''
      obtain rfl : T = T' := by
        rcases lt_trichotomy T T' with hlt | heq | hgt
        · exact absurd hl (length_divisorUpTo_lt hk hp hd hlt).ne
        · exact heq
        · exact absurd hl.symm (length_divisorUpTo_lt hk hp' hd' hgt).ne
      rw [eq_add_scaledLength_of_le hB hBm hk hkm2 hp hd h₂ h₁ hle,
        eq_add_scaledLength_of_le hB hBm hk hkm2 hp' hd' h₂' h₁' hle', hp.unique hp']

omit hB hs hBm in
lemma isInj_legendreDown (h₀₁ : t₀ ≠ t₁) (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂) :
    IsInj (LegendreDown m t₀ t₁ t₂) (Level B s (2 * m))
      (fun v ↦
        Tagged t₀ (Level B s m) v ∨ Tagged t₁ (Level B s m) v ∨ Tagged t₂ (Kummer B s m) v) := by
  and_intros
  · intro w hw
    obtain ⟨k, P, o, rfl⟩ := exists_pair₃ w
    by_cases hkm : k ≤ m
    · exact ⟨_, legendreDown_pair.mpr (Or.inl ⟨hkm, rfl⟩)⟩
    by_cases hq : k / P ≤ 2 * (m / P)
    · exact ⟨_, legendreDown_pair.mpr (Or.inr (Or.inl ⟨not_le.mp hkm, hq, rfl⟩))⟩
    · exact ⟨_, legendreDown_pair.mpr (Or.inr (Or.inr ⟨not_le.mp hkm, not_le.mp hq, rfl⟩))⟩
  · intro w v hw hv
    obtain ⟨k, P, o, rfl⟩ := exists_pair₃ w
    obtain ⟨hk, hk₂, hd, p, hpP, hp, ho⟩ := level_pair_iff.mp hw
    rcases legendreDown_pair.mp hv with ⟨hkm, rfl⟩ | ⟨hmk, hq, rfl⟩ | ⟨hmk, hq, rfl⟩
    · left
      refine ⟨by simp, ?_⟩
      rw [pi₂_pair, level_pair_iff]
      exact ⟨hk, hkm, hd, p, hpP, hp, ho⟩
    · right
      left
      refine ⟨by simp, ?_⟩
      rw [pi₂_pair, level_pair_iff]
      obtain ⟨h₁, h₂, h₃⟩ := legendre_mid hp.pos hd hmk hq
      exact ⟨h₁, h₂, h₃, p, hpP, hp, ho⟩
    · right
      right
      refine ⟨by simp, ?_⟩
      rw [pi₂_pair, kummer_pair_iff]
      exact ⟨(legendre_top hp.pos hd hk₂ hq).2, p, hpP, hp, ho⟩
  · intro w w' v hw hw' hv hv'
    obtain ⟨k, P, o, rfl⟩ := exists_pair₃ w
    obtain ⟨k', P', o', rfl⟩ := exists_pair₃ w'
    obtain ⟨hk, hk₂, hd, p, hpP, hp, ho⟩ := level_pair_iff.mp hw
    obtain ⟨hk', hk₂', hd', p', hpP', hp', ho'⟩ := level_pair_iff.mp hw'
    rcases legendreDown_pair.mp hv with ⟨hkm, e⟩ | ⟨hmk, hq, e⟩ | ⟨hmk, hq, e⟩ <;>
      rcases legendreDown_pair.mp hv' with ⟨hkm', e'⟩ | ⟨hmk', hq', e'⟩ | ⟨hmk', hq', e'⟩ <;>
      have e'' := e.symm.trans e' <;> simp only [pair_ext_iff] at e'' <;>
      try first
        | exact absurd e''.1 h₀₁ | exact absurd e''.1.symm h₀₁
        | exact absurd e''.1 h₀₂ | exact absurd e''.1.symm h₀₂
        | exact absurd e''.1 h₁₂ | exact absurd e''.1.symm h₁₂
    · obtain ⟨-, rfl, rfl, rfl⟩ := e''
      rfl
    · obtain ⟨-, he, rfl, rfl⟩ := e''
      have hf := (div_mul_le m P).trans hmk.le
      have hf' := (div_mul_le m P).trans hmk'.le
      have : k = k' := by
        rw [← sub_add_self_of_le hf, he, sub_add_self_of_le hf']
      rw [this]
    · obtain ⟨-, rfl, rfl⟩ := e''
      rw [(legendre_top hp.pos hd hk₂ hq).1, (legendre_top hp.pos hd' hk₂' hq').1]

omit hB hs hBm in
lemma isInj_legendreUp (h₀₁ : t₀ ≠ t₁) (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂) :
    IsInj (LegendreUp m t₀ t₁ t₂)
      (fun u ↦ Tagged t₀ (Level B s m) u ∨ Tagged t₁ (Level B s m) u ∨ Tagged t₂ (Kummer B s m) u)
      (Level B s (2 * m)) := by
  and_intros
  · intro u hu
    obtain ⟨t, x, rfl⟩ := exists_pair₂ u
    simp only [Tagged, pi₁_pair, pi₂_pair] at hu
    rcases hu with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · exact ⟨x, (legendreUp_tag_zero h₀₁ h₀₂).mpr rfl⟩
    · obtain ⟨k, P, o, rfl⟩ := exists_pair₃ x
      exact ⟨_, (legendreUp_tag_one h₀₁ h₁₂).mpr ⟨k, P, o, rfl, rfl⟩⟩
    · obtain ⟨P, o, rfl⟩ := exists_pair₂ x
      exact ⟨_, (legendreUp_tag_two h₀₂ h₁₂).mpr ⟨P, o, rfl, rfl⟩⟩
  · intro u v hu hv
    exact (legendreUp_shape h₀₁ h₀₂ h₁₂ hu hv).1
  · intro u u' v hu hu' hv hv'
    obtain ⟨-, K, P, o, rfl, H⟩ := legendreUp_shape h₀₁ h₀₂ h₁₂ hu hv
    obtain ⟨-, K', P', o', he, H'⟩ := legendreUp_shape h₀₁ h₀₂ h₁₂ hu' hv'
    simp only [pair_ext_iff] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    rcases H with ⟨hA, eA⟩ | ⟨hB₁, hB₂, kB, eB, hKB⟩ | ⟨hC₁, hC₂, eC, hKC⟩ <;>
      rcases H' with ⟨hA', eA'⟩ | ⟨hB₁', hB₂', kB', eB', hKB'⟩ | ⟨hC₁', hC₂', eC', hKC'⟩
    · exact eA.trans eA'.symm
    · exact absurd (hB₁'.trans_le hA) (lt_irrefl _)
    · exact absurd (hC₂'.trans_le hA) (lt_irrefl _)
    · exact absurd (hB₁.trans_le hA') (lt_irrefl _)
    · obtain rfl := add_right_cancel (hKB.symm.trans hKB')
      exact eB.trans eB'.symm
    · exact absurd (hC₁'.trans_le hB₂) (lt_irrefl _)
    · exact absurd (hC₂.trans_le hA') (lt_irrefl _)
    · exact absurd (hC₁.trans_le hB₂') (lt_irrefl _)
    · exact eC.trans eC'.symm

omit hs in
lemma doubleUp_decode {w v : V} (hw : Bits B s (2 * m) w)
    (hv : DoubleUp B s m t₀ t₁ t₂ w v) :
    (Tagged t₀ (Bits B s m) v ∨ Tagged t₁ (Bits B s m) v ∨ Tagged t₂ (Below (2 * m * s)) v) ∧
      ((∃ j y, v = ⟪t₀, ⟪j, y⟫⟫ ∧ w = ⟪2 * j, y⟫) ∨
        (∃ i y, v = ⟪t₁, ⟪i + 1, y⟫⟫ ∧ w = ⟪2 * i + 1, y⟫) ∨
        ∃ z, v = ⟪t₂, z⟫ ∧
          ((z < m * s ∧ w = ⟪2 * (z / s + 1), scaledLength B s (z / s + 1) + z % s⟫) ∨
            (m * s ≤ z ∧ w = ⟪2 * ((z - m * s) / s) + 1,
              scaledLength B s ((z - m * s) / s + 1) + (z - m * s) % s⟫))) := by
  obtain ⟨k, y, rfl⟩ := exists_pair₂ w
  obtain ⟨hk, hk₂, hy⟩ := bits_pair_iff.mp hw
  have hms : m * s ≤ 2 * m * s := mul_le_mul_right (by simp)
  have H := doubleUp_pair.mp hv
  rcases mod_two k with h0 | h1
  · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := mod_eq_zero_iff_dvd.mp h0
    have hj₀ : 0 < j := pos_of_ne_zero (by rintro rfl; simp at hk)
    obtain ⟨i, rfl⟩ := eq_succ_of_pos hj₀
    have hjm : i + 1 ≤ m := le_of_mul_le_mul_left hk₂ two_pos
    have hlam := scaledLength_two_mul hB hj₀ (mul_length_lt_of_le hBm hk₂)
    simp only [mod_mul_self_right, div_mul_right _ (two_pos : (0 : V) < 2), true_and,
      add_tsub_cancel_right, zero_ne_one, false_and, or_self, or_false] at H
    rcases H with ⟨hy', rfl⟩ | ⟨hy', rfl⟩
    · refine ⟨Or.inl ⟨by simp, ?_⟩, Or.inl ⟨i + 1, y, rfl, rfl⟩⟩
      rw [pi₂_pair, bits_pair_iff]
      exact ⟨hj₀, hjm, hy'⟩
    · rw [hlam] at hy
      have hr : y - scaledLength B s (i + 1) < s := (tsub_lt_iff_left hy').mpr hy
      have hz : i * s + (y - scaledLength B s (i + 1)) < m * s := calc
        _ < i * s + s := (add_lt_add_iff_left _).mpr hr
        _ = (i + 1) * s := by grind
        _ ≤ m * s := mul_le_mul_right hjm
      refine ⟨Or.inr (Or.inr ⟨by simp, ?_⟩), Or.inr (Or.inr ⟨_, rfl, Or.inl ⟨hz, ?_⟩⟩)⟩
      · rw [pi₂_pair]
        exact hz.trans_le hms
      · rw [div_mul_add i s hr, mod_mul_add_of_lt i s hr, add_tsub_self_of_le hy']
  · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i + 1 :=
      ⟨k / 2, by have := div_add_mod k 2; rw [h1] at this; exact this.symm⟩
    have hi' : i < m := lt_of_mul_lt_mul_left (a := 2) ((lt_add_one _).trans_le hk₂)
    have hjm : i + 1 ≤ m := succ_le_iff_lt.mpr hi'
    have hj₀ : 0 < i + 1 := by simp
    have hle : 2 * i + 1 ≤ 2 * (i + 1) := by
      have e : 2 * (i + 1) = 2 * i + 1 + 1 := by grind
      rw [e]
      exact le_self_add
    have hlam := scaledLength_two_mul hB hj₀ (mul_length_lt_of_le hBm (mul_le_mul_left hjm))
    have hmono := scaledLength_monotone hB hk hle (mul_length_lt_of_le hBm (mul_le_mul_left hjm))
    have hy₂ : y < scaledLength B s (i + 1) + s := by
      rw [← hlam]
      exact hy.trans_le hmono
    simp only [zero_lt_two, mod_mul_add', Nat.one_lt_ofNat, mod_eq_self_of_lt, _root_.one_ne_zero,
      two_mul_add_one_div_two, false_and, true_and, false_or] at H
    rcases H with ⟨hy', rfl⟩ | ⟨hy', rfl⟩
    · refine ⟨Or.inr (Or.inl ⟨by simp, ?_⟩), Or.inr (Or.inl ⟨i, y, rfl, rfl⟩)⟩
      rw [pi₂_pair, bits_pair_iff]
      exact ⟨hj₀, hjm, hy'⟩
    · have hr : y - scaledLength B s (i + 1) < s := (tsub_lt_iff_left hy').mpr hy₂
      have hz : i * s + (y - scaledLength B s (i + 1)) < m * s := calc
        _ < i * s + s := (add_lt_add_iff_left _).mpr hr
        _ = (i + 1) * s := by grind
        _ ≤ m * s := mul_le_mul_right hjm
      have e : m * s + i * s + (y - scaledLength B s (i + 1)) =
          m * s + (i * s + (y - scaledLength B s (i + 1))) := add_assoc _ _ _
      refine ⟨Or.inr (Or.inr ⟨by simp, ?_⟩), Or.inr (Or.inr ⟨_, rfl, Or.inr ⟨?_, ?_⟩⟩)⟩
      · rw [pi₂_pair, e]
        calc
          _ < m * s + m * s := (add_lt_add_iff_left _).mpr hz
          _ = 2 * m * s := by grind
      · rw [e]
        exact le_self_add
      · rw [e, add_sub_self', div_mul_add i s hr, mod_mul_add_of_lt i s hr,
          add_tsub_self_of_le hy']

omit hs in
lemma isInj_doubleUp (h₀₁ : t₀ ≠ t₁) (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂) :
    IsInj (DoubleUp B s m t₀ t₁ t₂) (Bits B s (2 * m))
      (fun v ↦ Tagged t₀ (Bits B s m) v ∨ Tagged t₁ (Bits B s m) v ∨
        Tagged t₂ (Below (2 * m * s)) v) := by
  and_intros
  · intro w _
    obtain ⟨k, y, rfl⟩ := exists_pair₂ w
    rcases mod_two k with h0 | h1
    · by_cases hy : y < scaledLength B s (k / 2)
      · exact ⟨_, doubleUp_pair.mpr (Or.inl ⟨h0, hy, rfl⟩)⟩
      · exact ⟨_, doubleUp_pair.mpr (Or.inr (Or.inl ⟨h0, not_lt.mp hy, rfl⟩))⟩
    · by_cases hy : y < scaledLength B s (k / 2 + 1)
      · exact ⟨_, doubleUp_pair.mpr (Or.inr (Or.inr (Or.inl ⟨h1, hy, rfl⟩)))⟩
      · exact ⟨_, doubleUp_pair.mpr (Or.inr (Or.inr (Or.inr ⟨h1, not_lt.mp hy, rfl⟩)))⟩
  · intro w v hw hv
    exact (doubleUp_decode hB hBm hw hv).1
  · intro w w' v hw hw' hv hv'
    obtain ⟨-, H⟩ := doubleUp_decode hB hBm hw hv
    obtain ⟨-, H'⟩ := doubleUp_decode hB hBm hw' hv'
    rcases H with ⟨j, y, rfl, rfl⟩ | ⟨i, y, rfl, rfl⟩ | ⟨z, rfl, Hz⟩ <;>
      rcases H' with ⟨j', y', he, rfl⟩ | ⟨i', y', he, rfl⟩ | ⟨z', he, Hz'⟩ <;>
      simp only [pair_ext_iff] at he <;>
      try first
        | exact absurd he.1 h₀₁ | exact absurd he.1.symm h₀₁
        | exact absurd he.1 h₀₂ | exact absurd he.1.symm h₀₂
        | exact absurd he.1 h₁₂ | exact absurd he.1.symm h₁₂
    · obtain ⟨-, rfl, rfl⟩ := he
      rfl
    · obtain ⟨-, hi, rfl⟩ := he
      obtain rfl := add_right_cancel hi
      rfl
    · obtain ⟨-, rfl⟩ := he
      rcases Hz with ⟨hz, e⟩ | ⟨hz, e⟩ <;> rcases Hz' with ⟨hz', e'⟩ | ⟨hz', e'⟩
      · exact e.trans e'.symm
      · exact absurd (hz.trans_le hz') (lt_irrefl _)
      · exact absurd (hz'.trans_le hz) (lt_irrefl _)
      · exact e.trans e'.symm

lemma doubleDown_decode {u v : V} (h₀₁ : t₀ ≠ t₁) (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂)
    (hu : Tagged t₀ (Bits B s m) u ∨ Tagged t₁ (Bits B s m) u ∨
      Tagged t₂ (Below ((2 * m - 1) * s)) u)
    (hv : DoubleDown B s m t₀ t₁ t₂ t₃ t₄ u v) :
    (∃ y, v = ⟪t₄, y⟫ ∧ y < scaledLength B s m ∧ u = ⟪t₁, ⟪m, y⟫⟫) ∨
      ∃ K y, v = ⟪t₃, ⟪K, y⟫⟫ ∧ Bits B s (2 * m) ⟪K, y⟫ ∧
        ((K % 2 = 0 ∧ ((y < scaledLength B s (K / 2) ∧ u = ⟪t₀, ⟪K / 2, y⟫⟫) ∨
            (scaledLength B s (K / 2) ≤ y ∧
              u = ⟪t₂, s * (K / 2 - 1) + (y - scaledLength B s (K / 2))⟫))) ∨
          (K % 2 = 1 ∧ ((y < scaledLength B s (K / 2) ∧ u = ⟪t₁, ⟪K / 2, y⟫⟫) ∨
            (scaledLength B s (K / 2) ≤ y ∧
              u = ⟪t₂, s * (m + (K / 2 - 1)) + (y - scaledLength B s (K / 2))⟫)))) := by
  obtain ⟨t, x, rfl⟩ := exists_pair₂ u
  simp only [Tagged, pi₁_pair, pi₂_pair] at hu
  rcases hu with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · obtain ⟨k, y, rfl, rfl⟩ := (doubleDown_tag_zero h₀₁ h₀₂).mp hv
    obtain ⟨hk, hkm, hy⟩ := bits_pair_iff.mp hx
    have hlam := scaledLength_two_mul hB hk (mul_length_lt_of_le hBm (mul_le_mul_left hkm))
    right
    use 2 * k, y
    and_intros
    · rfl
    · rw [bits_pair_iff]
      exact ⟨mul_pos two_pos hk, mul_le_mul_left hkm, hlam ▸ hy.trans_le le_self_add⟩
    · left
      rw [div_mul_right k two_pos]
      exact ⟨by simp, Or.inl ⟨hy, rfl⟩⟩
  · obtain ⟨k, y, rfl, H⟩ := (doubleDown_tag_one h₀₁ h₁₂).mp hv
    obtain ⟨hk, hkm, hy⟩ := bits_pair_iff.mp hx
    rcases H with ⟨hlt, rfl⟩ | ⟨hmk, rfl⟩
    · right
      have hk₁ : k + 1 ≤ m := succ_le_iff_lt.mpr hlt
      have hle : 2 * k + 1 ≤ 2 * m := calc
        2 * k + 1 ≤ 2 * k + 1 + 1 := le_self_add
        _ = 2 * (k + 1) := by grind
        _ ≤ 2 * m := mul_le_mul_left hk₁
      have hmono := scaledLength_monotone hB hk
        (show k ≤ 2 * k + 1 from (by simp : k ≤ 2 * k).trans le_self_add)
        (mul_length_lt_of_le hBm hle)
      use 2 * k + 1, y
      and_intros
      · rfl
      · rw [bits_pair_iff]
        exact ⟨by simp, hle, hy.trans_le hmono⟩
      · right
        rw [two_mul_add_one_div_two]
        exact ⟨by simp, Or.inl ⟨hy, rfl⟩⟩
    · obtain rfl := le_antisymm hkm hmk
      left
      exact ⟨y, rfl, hy, rfl⟩
  · have hr : x % s < s := mod_lt x hs
    have hq : x / s < 2 * m - 1 := div_lt_of_lt_mul hx
    rcases (doubleDown_tag_two h₀₂ h₁₂).mp hv with ⟨hqm, rfl⟩ | ⟨hmq, rfl⟩
    · right
      have hq₁ : x / s + 1 ≤ m := succ_le_iff_lt.mpr hqm
      have hlam := scaledLength_two_mul hB (by simp : 0 < x / s + 1)
        (mul_length_lt_of_le hBm (mul_le_mul_left hq₁))
      use 2 * (x / s + 1), scaledLength B s (x / s + 1) + x % s
      and_intros
      · rfl
      · rw [bits_pair_iff]
        refine ⟨mul_pos two_pos (by simp), mul_le_mul_left hq₁, ?_⟩
        rw [hlam]
        exact (add_lt_add_iff_left _).mpr hr
      · left
        rw [div_mul_right _ two_pos]
        refine ⟨by simp, Or.inr ⟨le_self_add, ?_⟩⟩
        rw [add_sub_self, add_sub_self']
        conv_lhs => rw [← div_add_mod x s]
    · right
      obtain ⟨i, hi⟩ := exists_add_of_le hmq
      have hi' : x / s - m = i := by
        rw [hi]
        exact add_sub_self'
      rw [hi']
      have h2m : 1 ≤ 2 * m := one_le_of_zero_lt _
        ((Arithmetic.zero_le _).trans_lt (hq.trans_le (sub_le_self _ _)))
      have hi₂ : i + 1 + 1 ≤ m := by
        have h₁ : m + i + 1 ≤ 2 * m - 1 := succ_le_iff_lt.mpr (hi ▸ hq)
        have h₂ : m + (i + 1 + 1) ≤ m + m := calc
          m + (i + 1 + 1) = m + i + 1 + 1 := by grind
          _ ≤ 2 * m - 1 + 1 := (add_le_add_iff_right 1).mpr h₁
          _ = m + m := by rw [sub_add_self_of_le h2m, two_mul]
        exact le_of_add_le_add_left h₂
      have hi₁ : i + 1 ≤ m := (le_self_add).trans hi₂
      have hle : 2 * (i + 1) + 1 ≤ 2 * m := calc
        2 * (i + 1) + 1 ≤ 2 * (i + 1) + 1 + 1 := le_self_add
        _ = 2 * (i + 1 + 1) := by grind
        _ ≤ 2 * m := mul_le_mul_left hi₂
      have hlam := scaledLength_two_mul hB (by simp : 0 < i + 1)
        (mul_length_lt_of_le hBm (mul_le_mul_left hi₁))
      have hmono := scaledLength_monotone hB (mul_pos two_pos (by simp : 0 < i + 1))
        (le_self_add : 2 * (i + 1) ≤ 2 * (i + 1) + 1) (mul_length_lt_of_le hBm hle)
      use 2 * (i + 1) + 1, scaledLength B s (i + 1) + x % s
      and_intros
      · rfl
      · rw [bits_pair_iff]
        refine ⟨by simp, hle, ?_⟩
        calc
          _ < scaledLength B s (i + 1) + s := (add_lt_add_iff_left _).mpr hr
          _ = scaledLength B s (2 * (i + 1)) := hlam.symm
          _ ≤ _ := hmono
      · right
        rw [two_mul_add_one_div_two]
        refine ⟨by simp, Or.inr ⟨le_self_add, ?_⟩⟩
        rw [add_sub_self, add_sub_self', ← hi]
        conv_lhs => rw [← div_add_mod x s]

lemma isInj_doubleDown (h₀₁ : t₀ ≠ t₁) (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂) (h₃₄ : t₃ ≠ t₄) :
    IsInj (DoubleDown B s m t₀ t₁ t₂ t₃ t₄)
      (fun u ↦ Tagged t₀ (Bits B s m) u ∨ Tagged t₁ (Bits B s m) u ∨
        Tagged t₂ (Below ((2 * m - 1) * s)) u)
      (fun v ↦ Tagged t₃ (Bits B s (2 * m)) v ∨ Tagged t₄ (Below (scaledLength B s m)) v) := by
  and_intros
  · intro u hu
    obtain ⟨t, x, rfl⟩ := exists_pair₂ u
    simp only [Tagged, pi₁_pair, pi₂_pair] at hu
    rcases hu with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · obtain ⟨k, y, rfl⟩ := exists_pair₂ x
      exact ⟨_, (doubleDown_tag_zero h₀₁ h₀₂).mpr ⟨k, y, rfl, rfl⟩⟩
    · obtain ⟨k, y, rfl⟩ := exists_pair₂ x
      by_cases hkm : k < m
      · exact ⟨_, (doubleDown_tag_one h₀₁ h₁₂).mpr ⟨k, y, rfl, Or.inl ⟨hkm, rfl⟩⟩⟩
      · exact ⟨_, (doubleDown_tag_one h₀₁ h₁₂).mpr ⟨k, y, rfl, Or.inr ⟨not_lt.mp hkm, rfl⟩⟩⟩
    · by_cases hq : x / s < m
      · exact ⟨_, (doubleDown_tag_two h₀₂ h₁₂).mpr (Or.inl ⟨hq, rfl⟩)⟩
      · exact ⟨_, (doubleDown_tag_two h₀₂ h₁₂).mpr (Or.inr ⟨not_lt.mp hq, rfl⟩)⟩
  · intro u v hu hv
    rcases doubleDown_decode hB hs hBm h₀₁ h₀₂ h₁₂ hu hv with ⟨y, rfl, hy, -⟩ | ⟨K, y, rfl, hK, -⟩
    · right
      exact ⟨by simp, by simpa [Below] using hy⟩
    · left
      exact ⟨by simp, by simpa using hK⟩
  · intro u u' v hu hu' hv hv'
    rcases doubleDown_decode hB hs hBm h₀₁ h₀₂ h₁₂ hu hv with
        ⟨y, rfl, hy, e⟩ | ⟨K, y, rfl, hK, H⟩ <;>
      rcases doubleDown_decode hB hs hBm h₀₁ h₀₂ h₁₂ hu' hv' with
        ⟨y', he, hy', e'⟩ | ⟨K', y', he, hK', H'⟩ <;>
      simp only [pair_ext_iff] at he
    · obtain ⟨-, rfl⟩ := he
      exact e.trans e'.symm
    · exact absurd he.1.symm h₃₄
    · exact absurd he.1 h₃₄
    · obtain ⟨-, rfl, rfl⟩ := he
      rcases H with ⟨hp, ⟨hy₁, e⟩ | ⟨hy₁, e⟩⟩ | ⟨hp, ⟨hy₁, e⟩ | ⟨hy₁, e⟩⟩ <;>
        rcases H' with ⟨hp', ⟨hy₁', e'⟩ | ⟨hy₁', e'⟩⟩ | ⟨hp', ⟨hy₁', e'⟩ | ⟨hy₁', e'⟩⟩ <;>
        first
          | exact e.trans e'.symm
          | exact absurd (hy₁.trans_le hy₁') (lt_irrefl _)
          | exact absurd (hy₁'.trans_le hy₁) (lt_irrefl _)
          | exact absurd (hp.symm.trans hp') (by simp)

end injections

end Bertrand

end

end FFL.FirstOrder.Arithmetic
