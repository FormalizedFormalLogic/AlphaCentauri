module

public import AlphaCentauri.NumberTheory.Primes
public import AlphaCentauri.NumberTheory.Bertrand.Positions
public import AlphaCentauri.NumberTheory.Bertrand.Sizes

/-!
# Bertrand's postulate over $\mathsf{I}\Delta_0 + \Omega_1$

If there is no prime in $(n, 2n]$, the positions of the prime-power decompositions of
$1, \dots, 2n$ and of the Chebyshev bands $\binom{2M_r}{M_r}$, $M_r \approx n / (3 \cdot 2^r)$,
assemble into a $\Delta_0$-definable injection of $z + a$ into $z + b$ numbers with
$a \approx 2ns$ and $b \approx \frac43 ns$: Erdős's estimates $\log_2 \binom{2n}{n} \approx 2n$
and $\log_2 \binom{2n}{n} \lesssim \frac43 n$ become maps of positions, and the common part `z`,
of size about $ns\|n\|^2$, is carried along. The weak pigeonhole principle with ratio
$(K + 1) / K$ for $K \approx 16\|n\|^2$ excludes it.

- [HP98, §V.5(f)]
- [PWW88, remark before Theorem 12]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁]

namespace Bertrand

variable (B s : V)

/-- The bound $\langle 2m, \langle 2m, B \mathbin{\#} 1 + 2ms \rangle \rangle$ of the elements of
the sets of positions occurring in the band of `m`. -/
def payloadBound (m : V) : V := ⟪2 * m, 2 * m, B ⨳ 1 + 2 * m * s⟫

/-- The domain of a band: $\mathrm{K}(m)$ and two copies of $\mathrm{Bits}(m)$. -/
def BandDomain (m u : V) : Prop :=
  Tagged 2 (Kummer B s m) u ∨ Tagged 0 (Bits B s m) u ∨ Tagged 1 (Bits B s m) u

/-- The codomain of a band: two copies of $\mathrm{Bits}(m)$, the $2ms$ numbers of the Chebyshev
estimate, and two copies of $\mathrm{Top}(m)$. -/
def BandCodomain (m u : V) : Prop :=
  (Tagged 0 (Bits B s m) u ∨ Tagged 1 (Bits B s m) u ∨ Tagged 3 (Below (2 * m * s)) u) ∨
    (Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u)

/-- Cut the two copies of $\mathrm{Bits}(m)$ into levels. -/
def bandLevelMap (m : V) : V → V → Prop :=
  UnionMap (Tagged 2 (Kummer B s m)) IdMap
    (fun u ↦ Tagged 0 (Bits B s m) u ∨ Tagged 1 (Bits B s m) u)
    (UnionMap (Tagged 0 (Bits B s m)) (UntagMap 0 (BitsToLev B s 6 4))
      (Tagged 1 (Bits B s m)) (UntagMap 1 (BitsToLev B s 7 5)))

/-- Legendre's matching backwards: two copies of $\mathrm{Lev}(m)$ and $\mathrm{K}(m)$ into
$\mathrm{Lev}(2m)$. -/
def bandLegendreMap (m : V) : V → V → Prop :=
  UnionMap (fun u ↦ Tagged 6 (Lev B s m) u ∨ Tagged 7 (Lev B s m) u ∨ Tagged 2 (Kummer B s m) u)
    (TagOutMap 8 (LegendreUp m 6 7 2)) (fun u ↦ Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u) IdMap

/-- Levels of $1, \dots, 2m$ into positions. -/
def bandBitsMap (m : V) : V → V → Prop :=
  UnionMap (Tagged 8 (Lev B s (2 * m))) (TagMap 8 9 (LevToBits B s))
    (fun u ↦ Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u) IdMap

/-- Halve the positions of $1, \dots, 2m$. -/
def bandDoubleMap (m : V) : V → V → Prop :=
  UnionMap (Tagged 9 (Bits B s (2 * m))) (UntagMap 9 (DoubleUp B s m 0 1 3))
    (fun u ↦ Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u) IdMap

/-- The injection of a band: $\mathrm{K}(m) + 2\,\mathrm{Bits}(m) \le 2\,\mathrm{Bits}(m) + 2ms +
2\,\mathrm{Top}(m)$, i.e. $\log_2 \binom{2m}{m} \lesssim 2m$. -/
def BandStep (m : V) : V → V → Prop :=
  CompMap (⟪10, payloadBound B s m⟫ + 1)
    (CompMap (⟪10, payloadBound B s m⟫ + 1)
      (CompMap (⟪10, payloadBound B s m⟫ + 1) (bandLevelMap B s m) (bandLegendreMap B s m))
      (bandBitsMap B s m))
    (bandDoubleMap B s m)

lemma definable_legendreUp_uniform (t₀ t₁ t₂ : V) :
    𝚺ᴬ₀.DefinableRel₃ fun m u v : V ↦ LegendreUp m t₀ t₁ t₂ u v := by
  unfold LegendreUp
  definability

lemma definable_doubleUp_uniform (t₀ t₁ t₂ : V) :
    𝚺ᴬ₀.DefinableRel₃ fun m u v : V ↦ DoubleUp B s m t₀ t₁ t₂ u v := by
  unfold DoubleUp
  definability

lemma definable_bandLevelMap : 𝚺ᴬ₀.DefinableRel₃ (bandLevelMap B s) := by
  have := definable_bits B s
  have := definable_kummer B s
  have := definable_bitsToLev B s 6 4
  have := definable_bitsToLev B s 7 5
  unfold bandLevelMap UnionMap IdMap UntagMap Tagged
  definability

lemma definable_bandLegendreMap : 𝚺ᴬ₀.DefinableRel₃ (bandLegendreMap B s) := by
  have := definable_lev B s
  have := definable_kummer B s
  have := definable_top (V := V)
  have := definable_legendreUp_uniform (V := V) 6 7 2
  unfold bandLegendreMap UnionMap IdMap TagOutMap Tagged
  definability

lemma definable_bandBitsMap : 𝚺ᴬ₀.DefinableRel₃ (bandBitsMap B s) := by
  have := definable_lev B s
  have := definable_top (V := V)
  have := definable_levToBits B s
  unfold bandBitsMap UnionMap IdMap TagMap Tagged
  definability

lemma definable_bandDoubleMap : 𝚺ᴬ₀.DefinableRel₃ (bandDoubleMap B s) := by
  have := definable_bits B s
  have := definable_top (V := V)
  have := definable_doubleUp_uniform B s 0 1 3
  unfold bandDoubleMap UnionMap IdMap UntagMap Tagged
  definability

lemma definable_bandStep : 𝚺ᴬ₀.DefinableRel₃ (BandStep B s) := by
  have := definable_bandLevelMap B s
  have := definable_bandLegendreMap B s
  have := definable_bandBitsMap B s
  have := definable_bandDoubleMap B s
  unfold BandStep CompMap payloadBound
  definability

variable {B s}

section bounds

variable {m m' w : V}

lemma Bits.le_payloadBound (h : Bits B s m' w) (hm : m' ≤ 2 * m) : w ≤ payloadBound B s m := by
  obtain ⟨k, -, y, -, rfl, -, hk, hy⟩ := h
  apply pair_le_pair (hk.trans hm)
  calc y ≤ B ⨳ 1 := (hy.trans (scaledLength_lt B s k)).le
    _ ≤ B ⨳ 1 + 2 * m * s := le_self_add
    _ ≤ _ := le_pair_right _ _

lemma Lev.le_payloadBound (h : Lev B s m' w) (hm : m' ≤ 2 * m) : w ≤ payloadBound B s m := by
  obtain ⟨k, -, P, -, o, -, rfl, hk0, hk, hP, p, -, -, ho⟩ := h
  apply pair_le_pair (hk.trans hm)
  apply pair_le_pair ((le_of_dvd hk0 hP).trans (hk.trans hm))
  exact (ho.trans (scaledLength_lt B s p)).le.trans le_self_add

lemma Top.le_payloadBound (h : Top m' w) (hm : m' ≤ 2 * m) : w ≤ payloadBound B s m := by
  obtain ⟨k, -, i, -, rfl, -, hk, hi⟩ := h
  apply pair_le_pair (hk.trans hm)
  exact (hi.le.trans ((length_le k).trans (hk.trans hm))).trans (le_pair_left _ _)

lemma Kummer.le_payloadBound (h : Kummer B s m' w) (hm : m' ≤ m) : w ≤ payloadBound B s m := by
  obtain ⟨P, -, o, -, rfl, hodd, p, -, -, ho⟩ := h
  have hP : P ≤ 2 * m' := by
    by_contra hlt
    rw [div_eq_zero_of_lt _ (not_le.mp hlt)] at hodd
    simp at hodd
  apply pair_le_pair (hP.trans (mul_le_mul_left hm))
  exact ((ho.trans (scaledLength_lt B s p)).le.trans le_self_add).trans (le_pair_right _ _)

lemma Below.le_payloadBound (h : Below (2 * m * s) w) : w ≤ payloadBound B s m :=
  (h.le.trans le_add_self).trans ((le_pair_right _ _).trans (le_pair_right _ _))

lemma Below.le_payloadBound_of_scaledLength {y : V} (h : Below (scaledLength B s y) w) :
    w ≤ payloadBound B s m :=
  ((h.trans (scaledLength_lt B s y)).le.trans le_self_add).trans
    ((le_pair_right _ _).trans (le_pair_right _ _))

lemma Tagged.lt_of_le {t t' β u : V} {X : V → Prop} (h : Tagged t X u) (ht : t ≤ t')
    (hX : ∀ x, X x → x ≤ β) : u < ⟪t', β⟫ + 1 := by
  rw [← pair_unpair u, h.1]
  exact lt_succ_iff_le.mpr (pair_le_pair ht (hX _ h.2))

end bounds

/-- An inequality between numerals. -/
macro "numeral_le" : tactic => `(tactic| (norm_cast))

/-- The tags of a union of tagged sets are distinct. -/
macro "tagged_disjoint" : tactic =>
  `(tactic| (intro y hy hy'; simp only [Tagged, Family] at hy hy'; aesop))

section band

variable {m : V} (hB : 0 < B) (hm₄ : s * ‖2 * (2 * m)‖ < ‖B‖)
include hB hm₄

lemma isInj_bandStep : IsInj (BandStep B s m) (BandDomain B s m) (BandCodomain B s m) := by
  have hm : s * ‖2 * m‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_left (length_monotone (by simp))) hm₄
  have h₁ : IsInj (bandLevelMap B s m) (BandDomain B s m) fun u ↦
      Tagged 2 (Kummer B s m) u ∨ ((Tagged 6 (Lev B s m) u ∨ Tagged 4 (Top m) u) ∨
        (Tagged 7 (Lev B s m) u ∨ Tagged 5 (Top m) u)) :=
    IsInj.id.union (((isInj_bitsToLev hB hm (by norm_num)).untag).union
      ((isInj_bitsToLev hB hm (by norm_num)).untag) (by tagged_disjoint)) (by tagged_disjoint)
  have h₂ : IsInj (bandLegendreMap B s m) (fun u ↦
      Tagged 2 (Kummer B s m) u ∨ ((Tagged 6 (Lev B s m) u ∨ Tagged 4 (Top m) u) ∨
        (Tagged 7 (Lev B s m) u ∨ Tagged 5 (Top m) u)))
      (fun u ↦ Tagged 8 (Lev B s (2 * m)) u ∨ (Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u)) :=
    (((isInj_legendreUp (B := B) (s := s) (m := m) (t₀ := 6) (t₁ := 7) (t₂ := 2)
      (by norm_num) (by norm_num) (by norm_num)).tagOut).union IsInj.id
        (by tagged_disjoint)).congr (fun _ ↦ by tauto) (fun _ ↦ Iff.rfl)
  have h₃ : IsInj (bandBitsMap B s m)
      (fun u ↦ Tagged 8 (Lev B s (2 * m)) u ∨ (Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u))
      (fun u ↦ Tagged 9 (Bits B s (2 * m)) u ∨ (Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u)) :=
    (isInj_levToBits hB hm₄).tag.union IsInj.id (by tagged_disjoint)
  have h₄ : IsInj (bandDoubleMap B s m)
      (fun u ↦ Tagged 9 (Bits B s (2 * m)) u ∨ (Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u))
      (BandCodomain B s m) :=
    (isInj_doubleUp hB hm (by norm_num) (by norm_num) (by norm_num)).untag.union IsInj.id
      (by tagged_disjoint)
  have hb : ∀ {t : V} {X : V → Prop}, t ≤ 10 → (∀ x, X x → x ≤ payloadBound B s m) →
      ∀ u, Tagged t X u → u < ⟪10, payloadBound B s m⟫ + 1 := fun ht hX u hu ↦
    Tagged.lt_of_le hu ht hX
  have hbits : ∀ {m'}, m' ≤ 2 * m → ∀ x, Bits B s m' x → x ≤ payloadBound B s m :=
    fun hm' x hx ↦ hx.le_payloadBound hm'
  have hlev : ∀ {m'}, m' ≤ 2 * m → ∀ x, Lev B s m' x → x ≤ payloadBound B s m :=
    fun hm' x hx ↦ hx.le_payloadBound hm'
  have htop : ∀ x, Top m x → x ≤ payloadBound B s m :=
    fun x hx ↦ hx.le_payloadBound (by simp)
  have hkum : ∀ x, Kummer B s m x → x ≤ payloadBound B s m :=
    fun x hx ↦ hx.le_payloadBound le_rfl
  have hle2 : m ≤ 2 * m := by simp
  refine ((h₁.comp h₂ ?_).comp h₃ ?_).comp h₄ ?_
  · rintro u (hu | (hu | hu) | (hu | hu))
    · exact hb (by numeral_le) hkum u hu
    · exact hb (by numeral_le) (hlev hle2) u hu
    · exact hb (by numeral_le) htop u hu
    · exact hb (by numeral_le) (hlev hle2) u hu
    · exact hb (by numeral_le) htop u hu
  · rintro u (hu | hu | hu)
    · exact hb (by numeral_le) (hlev le_rfl) u hu
    · exact hb (by numeral_le) htop u hu
    · exact hb (by numeral_le) htop u hu
  · rintro u (hu | hu | hu)
    · exact hb (by numeral_le) (hbits le_rfl) u hu
    · exact hb (by numeral_le) htop u hu
    · exact hb (by numeral_le) htop u hu

end band

variable (B s)

/-- The domain of the lower part: two copies of $\mathrm{Bits}(n)$ and $(2n - 1)s$ numbers. -/
def LowerDomain (n u : V) : Prop :=
  Tagged 0 (Bits B s n) u ∨ Tagged 1 (Bits B s n) u ∨ Tagged 2 (Below ((2 * n - 1) * s)) u

/-- The codomain of the lower part: two copies of $\mathrm{Bits}(n)$, $\mathrm{K}(n)$, and the
errors $\mathrm{Top}(2n)$ and $\lambda(n)$. -/
def LowerCodomain (n u : V) : Prop :=
  (Tagged 0 (Bits B s n) u ∨ Tagged 1 (Bits B s n) u) ∨
    (Tagged 6 (Kummer B s n) u ∨ Tagged 3 (Top (2 * n)) u ∨
      Tagged 4 (Below (scaledLength B s n)) u)

variable {B s}

lemma definable_tagged_bits (t m : V) : 𝚺ᴬ₀.DefinablePred (Tagged t (Bits B s m)) := by
  have := definable_bits B s
  apply definable_tagged
  definability

lemma definable_tagged_lev (t m : V) : 𝚺ᴬ₀.DefinablePred (Tagged t (Lev B s m)) := by
  have := definable_lev B s
  apply definable_tagged
  definability

lemma definable_tagged_top (t m : V) : 𝚺ᴬ₀.DefinablePred (Tagged t (Top m)) := by
  have := definable_top (V := V)
  apply definable_tagged
  definability

lemma definable_tagged_kummer (t m : V) : 𝚺ᴬ₀.DefinablePred (Tagged t (Kummer B s m)) := by
  have := definable_kummer B s
  apply definable_tagged
  definability

lemma definable_tagged_below (t c : V) : 𝚺ᴬ₀.DefinablePred (Tagged t (Below c)) := by
  apply definable_tagged
  unfold Below
  definability

section lower

variable {n : V} (hB : 0 < B) (hs : 0 < s) (hn₄ : s * ‖2 * (2 * n)‖ < ‖B‖)
include hB hs hn₄

/-- $2\,\mathrm{Bits}(n) + (2n - 1)s \le 2\,\mathrm{Bits}(n) + \mathrm{K}(n) + \mathrm{Top}(2n) +
\lambda(n)$, i.e. $\log_2 \binom{2n}{n} \gtrsim 2n$. -/
lemma embeds_lower : Embeds (LowerDomain B s n) (LowerCodomain B s n) := by
  have hn : s * ‖2 * n‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_left (length_monotone (by simp))) hn₄
  have e₁ : Embeds (LowerDomain B s n) fun u ↦
      Tagged 7 (Bits B s (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u :=
    Embeds.of_isInj (definable_doubleDown B s n 0 1 2 7 4)
      (isInj_doubleDown hB hs hn (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e₂ : Embeds
      (fun u ↦ Tagged 7 (Bits B s (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u)
      (fun u ↦ Tagged 8 (Lev B s (2 * n)) u ∨
        (Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u)) :=
    (((Embeds.of_isInj (definable_bitsToLev B s 8 3)
      (isInj_bitsToLev hB hn₄ (by norm_num))).untag (t := 7)).union (definable_tagged_bits 7 _)
        (definable_tagged_below 4 _) Embeds.refl (by tagged_disjoint)).congr
      (fun _ ↦ Iff.rfl) (fun _ ↦ by tauto)
  have hrest : 𝚺ᴬ₀.DefinablePred fun u : V ↦
      Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u := by
    have := definable_tagged_top (V := V) 3 (2 * n)
    have := definable_tagged_below (V := V) 4 (scaledLength B s n)
    definability
  have e₃ : Embeds
      (fun u ↦ Tagged 8 (Lev B s (2 * n)) u ∨
        (Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u))
      (fun u ↦ (Tagged 9 (Lev B s n) u ∨ Tagged 10 (Lev B s n) u ∨ Tagged 6 (Kummer B s n) u) ∨
        (Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u)) :=
    ((Embeds.of_isInj (definable_legendreDown n 9 10 6)
      (isInj_legendreDown (B := B) (s := s) (by norm_num) (by norm_num) (by norm_num))).untag
        (t := 8)).union (definable_tagged_lev 8 _) hrest Embeds.refl (by tagged_disjoint)
  have hbits : Embeds (Lev B s n) (Bits B s n) :=
    Embeds.of_isInj (definable_levToBits B s) (isInj_levToBits hB hn)
  have h₉₁₀ : 𝚺ᴬ₀.DefinablePred fun u : V ↦ Tagged 9 (Lev B s n) u ∨ Tagged 10 (Lev B s n) u := by
    have := definable_tagged_lev (B := B) (s := s) 9 n
    have := definable_tagged_lev (B := B) (s := s) 10 n
    definability
  have hrest' : 𝚺ᴬ₀.DefinablePred fun u : V ↦ Tagged 6 (Kummer B s n) u ∨
      Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u := by
    have := definable_tagged_kummer (B := B) (s := s) 6 n
    definability
  have e₄ : Embeds
      (fun u ↦ (Tagged 9 (Lev B s n) u ∨ Tagged 10 (Lev B s n) u ∨ Tagged 6 (Kummer B s n) u) ∨
        (Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u))
      (LowerCodomain B s n) :=
    ((((hbits.tag (t := 9) (t' := 0)).union (definable_tagged_lev 9 _)
      (definable_tagged_lev 10 _) (hbits.tag (t := 10) (t' := 1)) (by tagged_disjoint)).union
        h₉₁₀ hrest' Embeds.refl (by tagged_disjoint))).congr (fun _ ↦ by tauto) (fun _ ↦ Iff.rfl)
  have hb : ∀ {t : V} {X : V → Prop}, t ≤ 10 → (∀ x, X x → x ≤ payloadBound B s n) →
      ∀ u, Tagged t X u → u < ⟪10, payloadBound B s n⟫ + 1 := fun ht hX u hu ↦
    Tagged.lt_of_le hu ht hX
  have hle : n ≤ 2 * n := by simp
  refine ((e₁.comp (c := ⟪10, payloadBound B s n⟫ + 1) e₂ ?_).comp
    (c := ⟪10, payloadBound B s n⟫ + 1) e₃ ?_).comp (c := ⟪10, payloadBound B s n⟫ + 1) e₄ ?_
  · rintro u (hu | hu)
    · exact hb (by numeral_le) (fun x hx ↦ Bits.le_payloadBound hx le_rfl) u hu
    · exact hb (by numeral_le) (fun x hx ↦ Below.le_payloadBound_of_scaledLength hx) u hu
  · rintro u (hu | hu | hu)
    · exact hb (by numeral_le) (fun x hx ↦ Lev.le_payloadBound hx le_rfl) u hu
    · exact hb (by numeral_le) (fun x hx ↦ Top.le_payloadBound hx le_rfl) u hu
    · exact hb (by numeral_le) (fun x hx ↦ Below.le_payloadBound_of_scaledLength hx) u hu
  · rintro u ((hu | hu | hu) | hu | hu)
    · exact hb (by numeral_le) (fun x hx ↦ Lev.le_payloadBound hx hle) u hu
    · exact hb (by numeral_le) (fun x hx ↦ Lev.le_payloadBound hx hle) u hu
    · exact hb (by numeral_le) (fun x hx ↦ Kummer.le_payloadBound hx le_rfl) u hu
    · exact hb (by numeral_le) (fun x hx ↦ Top.le_payloadBound hx le_rfl) u hu
    · exact hb (by numeral_le) (fun x hx ↦ Below.le_payloadBound_of_scaledLength hx) u hu

end lower

/-- $M_r = u_{r + 1} + 1$: the band $(M_r, 2M_r]$ of the Chebyshev estimate. -/
def bandBound (n r : V) : V := bandSize n (r + 1) + 1

variable (B s)

/-- $\{(p, o) : p \text{ prime}, p^2 \le 2n, o < \lambda(p)\}$: the proper prime powers in
$(n, 2n]$, recorded by their primes. -/
def Small (n w : V) : Prop :=
  ∃ p ≤ w, ∃ o ≤ w, w = ⟪p, o⟫ ∧ IsPrime p ∧ p * p ≤ 2 * n ∧ o < scaledLength B s p

/-- A position $(P, o)$ of $\binom{2n}{n}$ goes to the Chebyshev band of `P` if $P \le x$, and to
`Small` otherwise. -/
def ChebyshevMap (n u v : V) : Prop :=
  ∃ P ≤ u, ∃ o ≤ u, π₂ u = ⟪6, P, o⟫ ∧
    ((P ≤ cutoff n ∧ ∃ r < bandCount n, (∀ r' < r, P ≤ bandBound n r') ∧ bandBound n r < P ∧
        v = ⟪1, r, 2, P, o⟫) ∨
      (cutoff n < P ∧ ∃ p ≤ P, IsPrimePower p P ∧ v = ⟪0, 5, p, o⟫))

lemma definable_small : 𝚺ᴬ₀.DefinableRel (Small B s) := by
  unfold Small
  definability

lemma definable_chebyshevMap (n : V) : 𝚺ᴬ₀.DefinableRel (ChebyshevMap n : V → V → Prop) := by
  unfold ChebyshevMap bandBound bandSize bandCount
  definability

variable {B s}

section chebyshev

variable {n : V}

lemma bandBound_lt {r : V} (hr : r < bandCount n) {P : V} (hP : P ≤ cutoff n)
    (hmin : ∀ r' < r, P ≤ bandBound n r') (hlt : bandBound n r < P) : P ≤ 2 * bandBound n r := by
  rcases zero_or_succ r with rfl | ⟨r'', rfl⟩
  · calc P ≤ cutoff n := hP
      _ = bandSize n 0 := bandSize_zero.symm
      _ ≤ 2 * bandSize n (0 + 1) + 1 := (bandSize_succ hr).2
      _ ≤ 2 * bandBound n 0 := by
        rw [bandBound, mul_add, mul_one]
        exact (add_le_add_iff_left _).mpr one_le_two
  · calc P ≤ bandBound n r'' := hmin r'' (by simp)
      _ = bandSize n (r'' + 1) + 1 := rfl
      _ ≤ 2 * bandSize n (r'' + 1 + 1) + 1 + 1 := (add_le_add_iff_right 1).mpr (bandSize_succ hr).2
      _ = 2 * bandBound n (r'' + 1) := by rw [bandBound, mul_add, mul_one, add_assoc,
          one_add_one_eq_two]

lemma bandBound_le {r : V} (hr : r < bandCount n) (hn2 : 2 ≤ n) : bandBound n r ≤ n := by
  sorry

lemma Kummer.gt_of_cutoff_lt {P o : V} (h : Kummer B s n ⟪P, o⟫) (hP : cutoff n < P) :
    n < P ∧ P ≤ 2 * n := by
  sorry

variable (H : ∀ p, n < p → p ≤ 2 * n → ¬IsPrime p)
include H

lemma isInj_chebyshevMap : IsInj (ChebyshevMap n) (Tagged 0 (Tagged 6 (Kummer B s n)))
    (fun v ↦ Tagged 1 (Family (bandCount n) fun r ↦ Tagged 2 (Kummer B s (bandBound n r))) v ∨
      Tagged 0 (Tagged 5 (Small B s n)) v) := by
  sorry

end chebyshev

variable (B s)

/-- The two copies of $\mathrm{Bits}(m)$ that a band carries along. -/
def BandCarry (m u : V) : Prop := Tagged 0 (Bits B s m) u ∨ Tagged 1 (Bits B s m) u

/-- The domain of the whole injection. -/
def Domain (n u : V) : Prop :=
  Tagged 0 (LowerDomain B s n) u ∨
    Tagged 1 (Family (bandCount n) fun r ↦ BandCarry B s (bandBound n r)) u

/-- What remains of the lower part after the Chebyshev map. -/
def LowerResidue (n u : V) : Prop :=
  (Tagged 0 (Bits B s n) u ∨ Tagged 1 (Bits B s n) u) ∨
    (Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u ∨
      Tagged 5 (Small B s n) u)

/-- The codomain of the whole injection. -/
def Codomain (n u : V) : Prop :=
  Tagged 0 (LowerResidue B s n) u ∨
    Tagged 1 (Family (bandCount n) fun r ↦ BandCodomain B s (bandBound n r)) u

variable {B s}

lemma definable_tagged_carry (n : V) : 𝚺ᴬ₀.DefinablePred
    (Tagged 1 (Family (bandCount n) fun r ↦ BandCarry B s (bandBound n r))) := by
  have := definable_bits B s
  apply definable_tagged
  unfold Family BandCarry Tagged bandBound bandSize bandCount cutoff
  definability

lemma definable_tagged_lowerDomain (n : V) : 𝚺ᴬ₀.DefinablePred (Tagged 0 (LowerDomain B s n)) := by
  have := definable_bits B s
  apply definable_tagged
  unfold LowerDomain Tagged Below
  definability

lemma definable_tagged_tagged_kummer (n : V) :
    𝚺ᴬ₀.DefinablePred (Tagged 0 (Tagged 6 (Kummer B s n))) :=
  definable_tagged (definable_tagged_kummer 6 n)

lemma definable_rest (n : V) : 𝚺ᴬ₀.DefinablePred fun u ↦
    Tagged 0 (fun w ↦ (Tagged 0 (Bits B s n) w ∨ Tagged 1 (Bits B s n) w) ∨
      (Tagged 3 (Top (2 * n)) w ∨ Tagged 4 (Below (scaledLength B s n)) w)) u ∨
    Tagged 1 (Family (bandCount n) fun r ↦ BandCarry B s (bandBound n r)) u := by
  have h₀ := definable_tagged_bits (B := B) (s := s) 0 n
  have h₁ := definable_tagged_bits (B := B) (s := s) 1 n
  have h₃ := definable_tagged_top (V := V) 3 (2 * n)
  have h₄ := definable_tagged_below (V := V) 4 (scaledLength B s n)
  have h : 𝚺ᴬ₀.DefinablePred fun w ↦ (Tagged 0 (Bits B s n) w ∨ Tagged 1 (Bits B s n) w) ∨
      (Tagged 3 (Top (2 * n)) w ∨ Tagged 4 (Below (scaledLength B s n)) w) := by
    definability
  have := definable_tagged (t := (0 : V)) h
  have := definable_tagged_carry (B := B) (s := s) n
  definability

lemma definable_tagged_lowerResidue (n : V) :
    𝚺ᴬ₀.DefinablePred (Tagged 0 (LowerResidue B s n)) := by
  have h₀ := definable_tagged_bits (B := B) (s := s) 0 n
  have h₁ := definable_tagged_bits (B := B) (s := s) 1 n
  have h₃ := definable_tagged_top (V := V) 3 (2 * n)
  have h₄ := definable_tagged_below (V := V) 4 (scaledLength B s n)
  have h₅ : 𝚺ᴬ₀.DefinablePred (Tagged 5 (Small B s n)) := by
    have := definable_small B s
    apply definable_tagged
    definability
  apply definable_tagged
  unfold LowerResidue
  definability

lemma definable_tagged_bandDomain (n : V) : 𝚺ᴬ₀.DefinablePred
    (Tagged 1 (Family (bandCount n) fun r ↦ BandDomain B s (bandBound n r))) := by
  have := definable_bits B s
  have := definable_kummer B s
  apply definable_tagged
  unfold Family BandDomain Tagged bandBound bandSize bandCount cutoff
  definability

lemma definable_bandStep_bandBound (n : V) :
    𝚺ᴬ₀.DefinableRel₃ fun r u v ↦ BandStep B s (bandBound n r) u v := by
  have := definable_bandStep B s
  unfold bandBound bandSize cutoff
  definability

section whole

variable {n : V} (hB : 0 < B) (hs : 0 < s) (hn₄ : s * ‖2 * (2 * n)‖ < ‖B‖)
  (H : ∀ p, n < p → p ≤ 2 * n → ¬IsPrime p)
include hB hs hn₄ H

lemma embeds_domain_codomain (hn2 : 2 ≤ n) : Embeds (Domain B s n) (Codomain B s n) := by
  have hdefCarry := definable_tagged_carry (B := B) (s := s) n
  have hdefLower := definable_tagged_lowerDomain (B := B) (s := s) n
  have eA : Embeds (Domain B s n) fun u ↦ Tagged 0 (LowerCodomain B s n) u ∨
      Tagged 1 (Family (bandCount n) fun r ↦ BandCarry B s (bandBound n r)) u :=
    (embeds_lower hB hs hn₄).tag.union hdefLower hdefCarry Embeds.refl (by tagged_disjoint)
  have hdef6 := definable_tagged_tagged_kummer (B := B) (s := s) n
  have hdefRest := definable_rest (B := B) (s := s) n
  have eB : Embeds
      (fun u ↦ Tagged 0 (LowerCodomain B s n) u ∨
        Tagged 1 (Family (bandCount n) fun r ↦ BandCarry B s (bandBound n r)) u)
      (fun u ↦ Tagged 0 (LowerResidue B s n) u ∨
        Tagged 1 (Family (bandCount n) fun r ↦ BandDomain B s (bandBound n r)) u) :=
    ((Embeds.of_isInj (definable_chebyshevMap n) (isInj_chebyshevMap H)).union hdef6
      hdefRest Embeds.refl (by
        intro y hy hy'
        simp only [Tagged, Family, BandCarry] at hy hy'
        aesop)).congr
      (fun _ ↦ sorry)
      (fun _ ↦ sorry)
  have hdefResidue := definable_tagged_lowerResidue (B := B) (s := s) n
  have hdefBand := definable_tagged_bandDomain (B := B) (s := s) n
  have hF := definable_bandStep_bandBound (B := B) (s := s) n
  have eC : Embeds
      (fun u ↦ Tagged 0 (LowerResidue B s n) u ∨
        Tagged 1 (Family (bandCount n) fun r ↦ BandDomain B s (bandBound n r)) u)
      (Codomain B s n) :=
    Embeds.refl.union hdefResidue hdefBand
      ((Embeds.family hF fun r hr ↦ isInj_bandStep hB <|
        lt_of_le_of_lt (mul_le_mul_left (length_monotone (mul_le_mul_left (mul_le_mul_left
          (bandBound_le hr hn2))))) hn₄).tag) (by tagged_disjoint)
  exact (eA.comp (c := ⟪1, n, 10, payloadBound B s n⟫ + 1) eB (fun _ hu ↦ sorry)).comp
    (c := ⟪1, n, 10, payloadBound B s n⟫ + 1) eC (fun _ hu ↦ sorry)

end whole

variable (n : V)

/-- The positions $(k, y)$ of a copy `c` of $\mathrm{Bits}(n)$ or of $\mathrm{Bits}(M_r)$, carried
along by the injection, are numbered in blocks of $n \Lambda$. -/
def CarryEncode (u v : V) : Prop :=
  (∃ c ≤ u, ∃ k ≤ u, ∃ y ≤ u, c ≤ 1 ∧ u = ⟪0, c, k, y⟫ ∧
      v = c * (n * blockWidth n) + (k - 1) * blockWidth n + y) ∨
    (∃ r ≤ u, ∃ c ≤ u, ∃ k ≤ u, ∃ y ≤ u, c ≤ 1 ∧ u = ⟪1, r, c, k, y⟫ ∧
      v = (2 + 2 * r + c) * (n * blockWidth n) + (k - 1) * blockWidth n + y)

/-- The encoding of the domain in $[0, z + a)$. -/
def DomainEncode (u v : V) : Prop :=
  CarryEncode n u v ∨ ∃ y ≤ u, u = ⟪0, 2, y⟫ ∧ v = lowerSize n + y

/-- The index of an element of the $r$-th band in $[0, 2 M_r w)$. -/
def BandIndex (r x q : V) : Prop :=
  (∃ y ≤ x, x = ⟪3, y⟫ ∧ q = y) ∨
    (∃ c ≤ x, ∃ k ≤ x, ∃ i ≤ x, 4 ≤ c ∧ c ≤ 5 ∧ x = ⟪c, k, i⟫ ∧
      q = 2 * bandBound n r * exponent n + (c - 4) * (bandBound n r * (‖n‖ + 1)) +
        (k - 1) * (‖n‖ + 1) + i)

/-- The position of the `q`-th element of the $r$-th band: the first $2 u_{r + 1} w$ elements
go to $[w(2x - 2u_r), w(2x - u_r))$, and the remaining $2w$ to the end. -/
def BandPosition (r q v : V) : Prop :=
  (q < 2 * bandSize n (r + 1) * bandUnit n ∧
      v = bandUnit n * (2 * cutoff n - 2 * bandSize n r) + q) ∨
    (2 * bandSize n (r + 1) * bandUnit n ≤ q ∧
      v = 2 * cutoff n * bandUnit n + 2 * r * bandUnit n +
        (q - 2 * bandSize n (r + 1) * bandUnit n))

/-- The offset of the Chebyshev bands. -/
def bandOffset : V :=
  lowerSize n + blockWidth n + 2 * n * (‖n‖ + 1) + (√(2 * n) + 1) * blockWidth n

/-- The encoding of the codomain in $[0, z + b)$. -/
def CodomainEncode (u v : V) : Prop :=
  CarryEncode n u v ∨
    (∃ y ≤ u, u = ⟪0, 4, y⟫ ∧ v = lowerSize n + y) ∨
    (∃ k ≤ u, ∃ i ≤ u, u = ⟪0, 3, k, i⟫ ∧
      v = lowerSize n + blockWidth n + (k - 1) * (‖n‖ + 1) + i) ∨
    (∃ p ≤ u, ∃ o ≤ u, u = ⟪0, 5, p, o⟫ ∧
      v = lowerSize n + blockWidth n + 2 * n * (‖n‖ + 1) + p * blockWidth n + o) ∨
    (∃ r ≤ u, ∃ x ≤ u, ∃ q ≤ u, ∃ w ≤ v, u = ⟪1, r, x⟫ ∧ BandIndex n r x q ∧
      BandPosition n r q w ∧ v = bandOffset n + w)

lemma definable_carryEncode : 𝚺ᴬ₀.DefinableRel (CarryEncode n) := by
  unfold CarryEncode
  definability

lemma definable_domainEncode : 𝚺ᴬ₀.DefinableRel (DomainEncode n) := by
  have := definable_carryEncode n
  unfold DomainEncode
  definability

lemma definable_bandIndex : 𝚺ᴬ₀.DefinableRel₃ (BandIndex n) := by
  unfold BandIndex bandBound bandSize
  definability

lemma definable_bandPosition : 𝚺ᴬ₀.DefinableRel₃ (BandPosition n) := by
  unfold BandPosition bandSize
  definability

lemma definable_codomainEncode : 𝚺ᴬ₀.DefinableRel (CodomainEncode n) := by
  have := definable_carryEncode n
  have := definable_bandIndex n
  have := definable_bandPosition n
  unfold CodomainEncode
  definability

variable {n}

section encode

variable (hℓ : (1024 : V) ≤ ‖n‖)
include hℓ

lemma isInj_codomainEncode :
    IsInj (CodomainEncode n) (Codomain (powerBound n) (exponent n) n)
      (· < lowerSize n + targetExcess n) := by
  sorry

lemma domainEncode_cover :
    ∀ v < lowerSize n + upperExcess n,
      (∀ u, Domain (powerBound n) (exponent n) n u → ¬DomainEncode n u v) →
      v < lowerSize n + targetExcess n ∧
        ∀ t, Codomain (powerBound n) (exponent n) n t → ¬CodomainEncode n t v := by
  sorry

lemma domainEncode_functional :
    ∀ u v v', Domain (powerBound n) (exponent n) n u → DomainEncode n u v →
      DomainEncode n u v' → v = v' := by
  sorry

end encode

lemma definable_domain (B s : V) : 𝚺ᴬ₀.DefinablePred (Domain B s n) := by
  have := definable_bits B s
  unfold Domain LowerDomain BandCarry Family Tagged Below bandBound bandSize bandCount cutoff
  definability

lemma Domain.lt {B s u : V} (h : Domain B s n u) : u < ⟪1, n, 10, payloadBound B s n⟫ + 1 := by
  sorry

lemma Codomain.lt {B s u : V} (h : Codomain B s n u) :
    u < ⟪1, n, 10, payloadBound B s n⟫ + 1 := by
  sorry

/-- If $\|n\| \ge 1024$, there is a prime in $(n, 2n]$. -/
lemma exists_prime_of_length (hℓ : (1024 : V) ≤ ‖n‖) : ∃ p, n < p ∧ p ≤ 2 * n ∧ IsPrime p := by
  by_contra! H
  have hn0 : 0 < n :=
    length_pos_iff.mp (lt_of_lt_of_le (by exact_mod_cast (show (0 : ℕ) < 1024 by decide)) hℓ)
  have hn2 : 2 ≤ n := sorry
  have hB : 0 < powerBound n := smash_pos _ _
  have hs : 0 < exponent n := mul_pos (length_pos_iff.mpr hn0) (length_pos_iff.mpr hn0)
  have hemb := embeds_domain_codomain hB hs exponent_mul_length_lt
    (fun p h₁ h₂ hp ↦ H p h₁ h₂ hp) hn2
  obtain ⟨R, hR, hinj⟩ := Embeds.extend (definable_domain _ _) (definable_domainEncode n)
    (definable_codomainEncode n) hemb (fun _ hu ↦ Domain.lt hu) (fun _ ht ↦ Codomain.lt ht)
    (domainEncode_functional hℓ) (isInj_codomainEncode hℓ) (domainEncode_cover hℓ)
  have hsize := size_inequality hℓ
  have hK : 0 < ratio n := by
    have h1 : (0 : V) < ‖n‖ + 1 := lt_of_lt_of_le zero_lt_one le_add_self
    unfold ratio
    exact mul_pos (mul_pos (by exact_mod_cast (show (0 : ℕ) < 16 by decide)) h1) h1
  set K := ratio n
  set c := (lowerSize n + targetExcess n) / K + 1
  have hc₁ : lowerSize n + targetExcess n ≤ K * c := (lt_mul_div_succ _ hK).le
  have hc₂ : (K + 1) * c ≤ lowerSize n + upperExcess n := sorry
  obtain ⟨x, hx, x', hx', y, hy, hne, h, h'⟩ :=
    weakPigeonhole_succ_mul_of_le_length hR (b := c) (I := lengthBound n) (by simp [c]) hK
      (ratio_le_length hℓ) fun x hx ↦ by
        obtain ⟨y, hy⟩ := hinj.1 x (lt_of_lt_of_le hx hc₂)
        exact ⟨y, lt_of_lt_of_le (hinj.2.1 x y (lt_of_lt_of_le hx hc₂) hy) hc₁, hy⟩
  exact hne (hinj.2.2 x x' y (lt_of_lt_of_le hx hc₂) (lt_of_lt_of_le hx' hc₂) h h')

end Bertrand

/-- Between $n$ and $2n$ there is a prime, for every $n \ge 1$. -/
def bertrandPostulate : ArithmeticSentence :=
  “∀ n, 1 ≤ n → ∃ p, n < p ∧ p ≤ 2 * n ∧ !isPrime p”

open Bertrand in
lemma exists_prime_lt_le_two_mul (n : V) (hn : 1 ≤ n) : ∃ p, n < p ∧ p ≤ 2 * n ∧ IsPrime p := by
  sorry

@[simp] lemma models_bertrandPostulate_iff {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] :
    V↓[ℒₒᵣ] ⊧ bertrandPostulate ↔ ∀ n : V, 1 ≤ n → ∃ p, n < p ∧ p ≤ 2 * n ∧ IsPrime p := by
  simp [models_iff, bertrandPostulate]

end

/-- - [HP98, §V.5(f), p. 392]
- [PWW88, remark before Theorem 12] -/
theorem provable_bertrandPostulate_ISigma0_union_Omega1 : 𝗜𝚺₀ ∪ 𝝮₁ ⊢ bertrandPostulate :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀ ∪ 𝝮₁ :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) inferInstance
  complete (𝗜𝚺₀ ∪ 𝝮₁) bertrandPostulate fun (M : Type) _ _ ↦ by
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
    exact models_bertrandPostulate_iff.mpr exists_prime_lt_le_two_mul

/-- $\mathsf{I}\Delta_0$ proves Bertrand's postulate. An open problem.
- [HP98, §V.5(f), p. 393] -/
def ProvableBertrandPostulateISigma0 : Prop := 𝗜𝚺₀ ⊢ bertrandPostulate

end FFL.FirstOrder.Arithmetic
