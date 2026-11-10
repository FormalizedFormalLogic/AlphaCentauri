module

public import AlphaCentauri.NumberTheory.Primes
public import AlphaCentauri.NumberTheory.Bertrand.Positions
public import AlphaCentauri.NumberTheory.Bertrand.Sizes

/-!
# The injection that refutes the failure of Bertrand's postulate

If there is no prime in $(n, 2n]$, the positions of the prime-power decompositions of
$1, \dots, 2n$ and of the Chebyshev bands $\binom{2M_r}{M_r}$, $M_r \approx n / (3 \cdot 2^r)$,
embed into each other as `Embeds (Domain B s n) (Codomain B s n)`, with the common part carried
along.

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
    (UnionMap (Tagged 0 (Bits B s m)) (UntagMap 0 (BitsToLevel B s 6 4))
      (Tagged 1 (Bits B s m)) (UntagMap 1 (BitsToLevel B s 7 5)))

/-- Legendre's matching backwards: two copies of $\mathrm{Level}(m)$ and $\mathrm{K}(m)$ into
$\mathrm{Level}(2m)$. -/
def bandLegendreMap (m : V) : V → V → Prop :=
  UnionMap (fun u ↦ Tagged 6 (Level B s m) u ∨ Tagged 7 (Level B s m) u ∨ Tagged 2 (Kummer B s m) u)
    (TagOutMap 8 (LegendreUp m 6 7 2)) (fun u ↦ Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u) IdMap

/-- Levels of $1, \dots, 2m$ into positions. -/
def bandBitsMap (m : V) : V → V → Prop :=
  UnionMap (Tagged 8 (Level B s (2 * m))) (TagMap 8 9 (LevelToBits B s))
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

/-- The domain of the lower part: two copies of $\mathrm{Bits}(n)$ and $(2n - 1)s$ numbers. -/
def LowerDomain (n u : V) : Prop :=
  Tagged 0 (Bits B s n) u ∨ Tagged 1 (Bits B s n) u ∨ Tagged 2 (Below ((2 * n - 1) * s)) u

/-- The codomain of the lower part: two copies of $\mathrm{Bits}(n)$, $\mathrm{K}(n)$, and the
errors $\mathrm{Top}(2n)$ and $\lambda(n)$. -/
def LowerCodomain (n u : V) : Prop :=
  (Tagged 0 (Bits B s n) u ∨ Tagged 1 (Bits B s n) u) ∨
    (Tagged 6 (Kummer B s n) u ∨ Tagged 3 (Top (2 * n)) u ∨
      Tagged 4 (Below (scaledLength B s n)) u)

/-- $M_r = u_{r + 1} + 1$: the band $(M_r, 2M_r]$ of the Chebyshev estimate. -/
def bandBound (n r : V) : V := bandSize n (r + 1) + 1

/-- $\{(p, o) : p \text{ prime}, p^2 \le 2n, o < \lambda(p)\}$: the proper prime powers in
$(n, 2n]$, recorded by their primes. -/
def Small (n w : V) : Prop :=
  ∃ p ≤ w, ∃ o ≤ w, w = ⟪p, o⟫ ∧ IsPrime p ∧ p * p ≤ 2 * n ∧ o < scaledLength B s p

/-- A position $(P, o)$ of $\binom{2n}{n}$ goes to the Chebyshev band of `P` if $P \le$
`cutoff n`, and to `Small` otherwise. -/
def ChebyshevMap (n u v : V) : Prop :=
  ∃ P ≤ u, ∃ o ≤ u, π₂ u = ⟪6, P, o⟫ ∧
    ((P ≤ cutoff n ∧ ∃ r < bandCount n, (∀ r' < r, P ≤ bandBound n r') ∧ bandBound n r < P ∧
        v = ⟪1, r, 2, P, o⟫) ∨
      (cutoff n < P ∧ ∃ p ≤ P, IsPrimePower p P ∧ v = ⟪0, 5, p, o⟫))

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

section bounds

variable {n m m' w u : V}

lemma Bits.le_payloadBound (h : Bits B s m' w) (hm : m' ≤ 2 * m) : w ≤ payloadBound B s m := by
  obtain ⟨k, -, y, -, rfl, -, hk, hy⟩ := h
  apply pair_le_pair (hk.trans hm)
  calc y ≤ B ⨳ 1 := (hy.trans (scaledLength_lt B s k)).le
    _ ≤ B ⨳ 1 + 2 * m * s := le_self_add
    _ ≤ _ := le_pair_right _ _

lemma Level.le_payloadBound (h : Level B s m' w) (hm : m' ≤ 2 * m) : w ≤ payloadBound B s m := by
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

lemma Tagged.lt_of_le {t t' β : V} {X : V → Prop} (h : Tagged t X u) (ht : t ≤ t')
    (hX : ∀ x, X x → x ≤ β) : u < ⟪t', β⟫ + 1 := by
  rw [← pair_unpair u, h.1]
  exact lt_succ_iff_le.mpr (pair_le_pair ht (hX _ h.2))

lemma Tagged.le_pair_of_le {t t' β : V} {X : V → Prop} (h : Tagged t X u) (ht : t ≤ t')
    (hX : ∀ x, X x → x ≤ β) : u ≤ ⟪t', β⟫ :=
  lt_succ_iff_le.mp (Tagged.lt_of_le h ht hX)

lemma Tagged.lt_of_tagged_zero {Y : V → Prop} {β : V} (h : Tagged 0 Y u)
    (hY : ∀ w, Y w → w ≤ ⟪10, β⟫) : u < ⟪1, n, 10, β⟫ + 1 :=
  Tagged.lt_of_le h zero_le_one fun w hw ↦ (hY w hw).trans (le_pair_right _ _)

lemma Tagged.lt_of_family {N : V} {Z : V → V → Prop} {β : V} (h : Tagged 1 (Family N Z) u)
    (hN : N ≤ n) (hZ : ∀ r < N, ∀ x, Z r x → x ≤ ⟪10, β⟫) : u < ⟪1, n, 10, β⟫ + 1 := by
  apply Tagged.lt_of_le h le_rfl
  rintro w ⟨hr, hw⟩
  calc w = ⟪π₁ w, π₂ w⟫ := (pair_unpair w).symm
    _ ≤ ⟪n, ⟪10, β⟫⟫ := pair_le_pair (hr.le.trans hN) (hZ _ hr _ hw)

lemma LowerDomain.le_bound (h : LowerDomain B s n w) : w ≤ ⟪10, payloadBound B s n⟫ := by
  rcases h with h | h | h
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx (by simp)
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx (by simp)
  · apply Tagged.le_pair_of_le h (by norm_cast)
    intro x hx
    exact Below.le_payloadBound (show Below (2 * n * s) x from
      lt_of_lt_of_le hx (mul_le_mul_right (sub_le_self _ _)))

lemma LowerCodomain.le_bound (h : LowerCodomain B s n w) : w ≤ ⟪10, payloadBound B s n⟫ := by
  rcases h with (h | h) | h | h | h
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx (by simp)
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx (by simp)
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Kummer.le_payloadBound hx le_rfl
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Top.le_payloadBound hx le_rfl
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Below.le_payloadBound_of_scaledLength hx

lemma LowerResidue.le_bound (h : LowerResidue B s n w) : w ≤ ⟪10, payloadBound B s n⟫ := by
  rcases h with (h | h) | h | h | h
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx (by simp)
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx (by simp)
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Top.le_payloadBound hx le_rfl
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Below.le_payloadBound_of_scaledLength hx
  · apply Tagged.le_pair_of_le h (by norm_cast)
    rintro x ⟨p, -, o, -, rfl, hp, hpp, ho⟩
    apply pair_le_pair ((le_mul_of_one_le_right (Arithmetic.zero_le p) hp.1.le).trans hpp)
    exact ((ho.trans (scaledLength_lt B s p)).le.trans le_self_add).trans (le_pair_right _ _)

lemma BandCarry.le_bound (hm : m ≤ n) (h : BandCarry B s m w) :
    w ≤ ⟪10, payloadBound B s n⟫ := by
  have hm₂ : m ≤ 2 * n := hm.trans (by simp)
  rcases h with h | h
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx hm₂
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx hm₂

lemma BandDomain.le_bound (hm : m ≤ n) (h : BandDomain B s m w) :
    w ≤ ⟪10, payloadBound B s n⟫ := by
  have hm₂ : m ≤ 2 * n := hm.trans (by simp)
  rcases h with h | h | h
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Kummer.le_payloadBound hx hm
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx hm₂
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx hm₂

lemma BandCodomain.le_bound (hm : m ≤ n) (h : BandCodomain B s m w) :
    w ≤ ⟪10, payloadBound B s n⟫ := by
  have hm₂ : m ≤ 2 * n := hm.trans (by simp)
  rcases h with (h | h | h) | h | h
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx hm₂
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Bits.le_payloadBound hx hm₂
  · apply Tagged.le_pair_of_le h (by norm_cast)
    intro x hx
    refine (Below.le_payloadBound (B := B) hx).trans ?_
    unfold payloadBound
    apply pair_le_pair (mul_le_mul_left hm)
    apply pair_le_pair (mul_le_mul_left hm)
    exact add_le_add le_rfl (mul_le_mul_right (mul_le_mul_left hm))
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Top.le_payloadBound hx hm₂
  · exact Tagged.le_pair_of_le h (by norm_cast) fun x hx ↦ Top.le_payloadBound hx hm₂

end bounds

/-- The tags of a union of tagged sets are distinct. -/
macro "tagged_disjoint" : tactic =>
  `(tactic| (intro y hy hy'; simp only [Tagged, Family] at hy hy'; aesop))


lemma definable_tagged_bits (t m : V) : 𝚺ᴬ₀.DefinablePred (Tagged t (Bits B s m)) := by
  have := definable_bits B s
  apply definable_tagged
  definability

lemma definable_tagged_level (t m : V) : 𝚺ᴬ₀.DefinablePred (Tagged t (Level B s m)) := by
  have := definable_level B s
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

lemma definable_tagged_carry (n : V) : 𝚺ᴬ₀.DefinablePred
    (Tagged 1 (Family (bandCount n) fun r ↦ BandCarry B s (bandBound n r))) := by
  have := definable_bits B s
  apply definable_tagged
  unfold Family BandCarry Tagged bandBound bandSize bandCount cutoff
  definability

lemma definable_bandLevelMap_bandBitsMap : 𝚺ᴬ₀.DefinableRel₃ (bandLevelMap B s) ∧
    𝚺ᴬ₀.DefinableRel₃ (bandBitsMap B s) := by
  and_intros
  · have := definable_bits B s
    have := definable_kummer B s
    have := definable_bitsToLevel B s 6 4
    have := definable_bitsToLevel B s 7 5
    unfold bandLevelMap UnionMap IdMap UntagMap Tagged
    definability
  · have := definable_level B s
    have := definable_top (V := V)
    have := definable_levelToBits B s
    unfold bandBitsMap UnionMap IdMap TagMap Tagged
    definability

lemma definable_bandLegendreMap : 𝚺ᴬ₀.DefinableRel₃ (bandLegendreMap B s) := by
  have := definable_level B s
  have := definable_kummer B s
  have := definable_top (V := V)
  have : 𝚺ᴬ₀.DefinableRel₃ fun m u v : V ↦ LegendreUp m 6 7 2 u v := by
    unfold LegendreUp
    definability
  unfold bandLegendreMap UnionMap IdMap TagOutMap Tagged
  definability

lemma definable_bandDoubleMap : 𝚺ᴬ₀.DefinableRel₃ (bandDoubleMap B s) := by
  have := definable_bits B s
  have := definable_top (V := V)
  have : 𝚺ᴬ₀.DefinableRel₃ fun m u v : V ↦ DoubleUp B s m 0 1 3 u v := by
    unfold DoubleUp
    definability
  unfold bandDoubleMap UnionMap IdMap UntagMap Tagged
  definability

lemma definable_bandStep_bandBound (n : V) :
    𝚺ᴬ₀.DefinableRel₃ fun r u v ↦ BandStep B s (bandBound n r) u v := by
  obtain ⟨h₁, h₃⟩ := definable_bandLevelMap_bandBitsMap (B := B) (s := s)
  have h₂ := definable_bandLegendreMap (B := B) (s := s)
  have h₄ := definable_bandDoubleMap (B := B) (s := s)
  have : 𝚺ᴬ₀.DefinableRel₃ (BandStep B s) := by
    unfold BandStep CompMap payloadBound
    definability
  unfold bandBound bandSize cutoff
  definability

lemma definable_pieces (n : V) :
    𝚺ᴬ₀.DefinablePred (Tagged 0 (LowerDomain B s n)) ∧
    𝚺ᴬ₀.DefinablePred (Tagged 0 (Tagged 6 (Kummer B s n))) ∧
    𝚺ᴬ₀.DefinablePred (fun u ↦
      Tagged 0 (fun w ↦ (Tagged 0 (Bits B s n) w ∨ Tagged 1 (Bits B s n) w) ∨
        (Tagged 3 (Top (2 * n)) w ∨ Tagged 4 (Below (scaledLength B s n)) w)) u ∨
      Tagged 1 (Family (bandCount n) fun r ↦ BandCarry B s (bandBound n r)) u) ∧
    𝚺ᴬ₀.DefinablePred (Tagged 0 (LowerResidue B s n)) ∧
    𝚺ᴬ₀.DefinablePred
      (Tagged 1 (Family (bandCount n) fun r ↦ BandDomain B s (bandBound n r))) ∧
    𝚺ᴬ₀.DefinableRel (ChebyshevMap n : V → V → Prop) := by
  and_intros
  · have := definable_bits B s
    apply definable_tagged
    unfold LowerDomain Tagged Below
    definability
  · exact definable_tagged (definable_tagged_kummer 6 n)
  · have := definable_tagged_bits (B := B) (s := s) 0 n
    have := definable_tagged_bits (B := B) (s := s) 1 n
    have := definable_tagged_top (V := V) 3 (2 * n)
    have := definable_tagged_below (V := V) 4 (scaledLength B s n)
    have := definable_tagged_carry (B := B) (s := s) n
    have : 𝚺ᴬ₀.DefinablePred fun w ↦ (Tagged 0 (Bits B s n) w ∨ Tagged 1 (Bits B s n) w) ∨
        (Tagged 3 (Top (2 * n)) w ∨ Tagged 4 (Below (scaledLength B s n)) w) := by
      definability
    have := definable_tagged (t := (0 : V)) this
    definability
  · have := definable_tagged_bits (B := B) (s := s) 0 n
    have := definable_tagged_bits (B := B) (s := s) 1 n
    have := definable_tagged_top (V := V) 3 (2 * n)
    have := definable_tagged_below (V := V) 4 (scaledLength B s n)
    have : 𝚺ᴬ₀.DefinablePred (Tagged 5 (Small B s n)) := by
      apply definable_tagged
      unfold Small
      definability
    apply definable_tagged
    unfold LowerResidue
    definability
  · have := definable_bits B s
    have := definable_kummer B s
    apply definable_tagged
    unfold Family BandDomain Tagged bandBound bandSize bandCount cutoff
    definability
  · unfold ChebyshevMap bandBound bandSize bandCount
    definability


section chebyshev

variable {n : V}

lemma bandBound_le {r : V} (hr : r < bandCount n) (hn2 : 2 ≤ n) : bandBound n r ≤ n := by
  have h₀ : 0 < bandCount n := pos_of_gt hr
  have h₁ : bandSize n (r + 1) ≤ bandSize n (0 + 1) :=
    bandSize_antitone (by simp) (succ_le_iff_lt.mpr hr)
  have h₂ := (bandSize_succ h₀).1
  have h₃ : 3 * cutoff n ≤ 2 * n := mul_div_le (2 * n) 3
  rw [bandSize_zero] at h₂
  have h₄ : 3 * bandSize n (r + 1) ≤ n := by
    apply le_of_mul_le_mul_left (a := 2)
    · calc 2 * (3 * bandSize n (r + 1)) = 3 * (2 * bandSize n (r + 1)) := by grind
        _ ≤ 3 * cutoff n := mul_le_mul_left ((mul_le_mul_left h₁).trans h₂)
        _ ≤ 2 * n := h₃
    · exact two_pos
  unfold bandBound
  rcases (Arithmetic.zero_le (bandSize n (r + 1))).eq_or_lt with h | h
  · rw [← h]
    simpa using one_le_two.trans hn2
  · calc bandSize n (r + 1) + 1 ≤ bandSize n (r + 1) + bandSize n (r + 1) :=
          (add_le_add_iff_left _).mpr (pos_iff_one_le.mp h)
      _ ≤ bandSize n (r + 1) + bandSize n (r + 1) + bandSize n (r + 1) := le_self_add
      _ = 3 * bandSize n (r + 1) := by grind
      _ ≤ n := h₄

lemma Kummer.gt_of_cutoff_lt {P o : V} (h : Kummer B s n ⟪P, o⟫) (hP : cutoff n < P) :
    n < P ∧ P ≤ 2 * n := by
  have hodd := (kummer_pair_iff.mp h).1
  have hP0 : 0 < P := pos_of_gt hP
  have hle : P ≤ 2 * n := by
    by_contra hlt
    rw [div_eq_zero_of_lt _ (not_le.mp hlt)] at hodd
    simp at hodd
  refine ⟨?_, hle⟩
  by_contra hPn
  have h₁ : 2 * n < 3 * P := calc
    2 * n < 3 * (cutoff n + 1) := lt_mul_div_succ (2 * n) (by norm_num)
    _ ≤ 3 * P := mul_le_mul_left (succ_le_iff_lt.mpr hP)
  have h₂ : 2 * n / P < 2 + 1 := by
    simpa only [show (3 : V) = 2 + 1 by norm_num] using div_lt_of_lt_mul h₁
  have h₃ : 2 ≤ 2 * n / P := by
    by_contra h₃
    have h₄ : 2 * n / P + 1 ≤ 2 := succ_le_iff_lt.mpr (not_le.mp h₃)
    have : 2 * n < 2 * n := calc
      2 * n < P * (2 * n / P + 1) := lt_mul_div_succ _ hP0
      _ ≤ P * 2 := mul_le_mul_left h₄
      _ ≤ n * 2 := mul_le_mul_right (not_lt.mp hPn)
      _ = 2 * n := mul_comm _ _
    exact lt_irrefl _ this
  rw [le_antisymm (lt_succ_iff_le.mp h₂) h₃] at hodd
  simp at hodd

lemma bandCount_le : bandCount n ≤ n :=
  calc bandCount n ≤ cutoff n := length_le _
    _ ≤ n := by
      apply le_of_mul_le_mul_left (a := 3) _ (by norm_num)
      calc 3 * cutoff n ≤ 2 * n := mul_div_le _ _
        _ ≤ 3 * n := mul_le_mul_right (by norm_cast)

lemma tagged_pair_iff {t a b : V} {X : V → Prop} : Tagged t X ⟪a, b⟫ ↔ a = t ∧ X b := by
  simp [Tagged]

lemma family_pair_iff {N a b : V} {X : V → V → Prop} : Family N X ⟪a, b⟫ ↔ a < N ∧ X a b := by
  simp [Family]

lemma exists_tagged_tagged_kummer {u : V} (h : Tagged 0 (Tagged 6 (Kummer B s n)) u) :
    ∃ P o, u = ⟪0, 6, P, o⟫ ∧ Kummer B s n ⟪P, o⟫ := by
  obtain ⟨a, b, rfl⟩ := exists_pair₂ u
  obtain ⟨c, w, rfl⟩ := exists_pair₂ b
  obtain ⟨P, o, rfl⟩ := exists_pair₂ w
  simp only [tagged_pair_iff] at h
  obtain ⟨rfl, rfl, hk⟩ := h
  use P, o

lemma chebyshevMap_pair {P o v : V} :
    ChebyshevMap n ⟪0, 6, P, o⟫ v ↔
      (P ≤ cutoff n ∧ ∃ r < bandCount n, (∀ r' < r, P ≤ bandBound n r') ∧ bandBound n r < P ∧
        v = ⟪1, r, 2, P, o⟫) ∨
      (cutoff n < P ∧ ∃ p ≤ P, IsPrimePower p P ∧ v = ⟪0, 5, p, o⟫) := by
  constructor
  · rintro ⟨P', -, o', -, h, hh⟩
    simp only [pi₂_pair, pair_ext_iff, true_and] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hh
  · intro hh
    use P
    and_intros
    · exact (le_pair_left P o).trans ((le_pair_right 6 _).trans (le_pair_right 0 _))
    · use o
      and_intros
      · exact (le_pair_right P o).trans ((le_pair_right 6 _).trans (le_pair_right 0 _))
      · simp
      · exact hh

lemma not_lt_of_isPrimePower {p P P' : V} (hp : IsPrimePower p P) (hp' : IsPrimePower p P')
    (hn : n < P) (hn' : P' ≤ 2 * n) : ¬P < P' := by
  intro hlt
  have h₁ : 2 ≤ p := by simpa [one_add_one_eq_two] using succ_le_iff_lt.mpr hp.1.1
  have h₂ : n + n < P + P := add_lt_add_of_lt_of_le hn hn.le
  have : P * 2 ≤ 2 * n := calc
    P * 2 ≤ P * p := mul_le_mul_left h₁
    _ ≤ P' := hp.mul_le_of_lt hp' hlt
    _ ≤ 2 * n := hn'
  simp only [two_mul, mul_comm P] at this
  exact absurd (lt_of_lt_of_le h₂ this) (lt_irrefl _)

end chebyshev

section assembly

variable {n m : V} (hB : 0 < B) (hs : 0 < s) (hm₄ : s * ‖2 * (2 * m)‖ < ‖B‖)
  (hn₄ : s * ‖2 * (2 * n)‖ < ‖B‖) (H : ∀ p, n < p → p ≤ 2 * n → ¬IsPrime p)

include hB hm₄ in
lemma isInj_bandStep : IsInj (BandStep B s m) (BandDomain B s m) (BandCodomain B s m) := by
  have hm : s * ‖2 * m‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_left (length_monotone (by simp))) hm₄
  have h₁ : IsInj (bandLevelMap B s m) (BandDomain B s m) fun u ↦
      Tagged 2 (Kummer B s m) u ∨ ((Tagged 6 (Level B s m) u ∨ Tagged 4 (Top m) u) ∨
        (Tagged 7 (Level B s m) u ∨ Tagged 5 (Top m) u)) :=
    IsInj.id.union (((isInj_bitsToLevel hB hm (by norm_num)).untag).union
      ((isInj_bitsToLevel hB hm (by norm_num)).untag) (by tagged_disjoint)) (by tagged_disjoint)
  have h₂ : IsInj (bandLegendreMap B s m) (fun u ↦
      Tagged 2 (Kummer B s m) u ∨ ((Tagged 6 (Level B s m) u ∨ Tagged 4 (Top m) u) ∨
        (Tagged 7 (Level B s m) u ∨ Tagged 5 (Top m) u)))
      (fun u ↦ Tagged 8 (Level B s (2 * m)) u ∨ (Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u)) :=
    (((isInj_legendreUp (B := B) (s := s) (m := m) (t₀ := 6) (t₁ := 7) (t₂ := 2)
      (by norm_num) (by norm_num) (by norm_num)).tagOut).union IsInj.id
        (by tagged_disjoint)).congr (fun _ ↦ by tauto) (fun _ ↦ Iff.rfl)
  have h₃ : IsInj (bandBitsMap B s m)
      (fun u ↦ Tagged 8 (Level B s (2 * m)) u ∨ (Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u))
      (fun u ↦ Tagged 9 (Bits B s (2 * m)) u ∨ (Tagged 4 (Top m) u ∨ Tagged 5 (Top m) u)) :=
    (isInj_levelToBits hB hm₄).tag.union IsInj.id (by tagged_disjoint)
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
  have hlevel : ∀ {m'}, m' ≤ 2 * m → ∀ x, Level B s m' x → x ≤ payloadBound B s m :=
    fun hm' x hx ↦ hx.le_payloadBound hm'
  have htop : ∀ x, Top m x → x ≤ payloadBound B s m :=
    fun x hx ↦ hx.le_payloadBound (by simp)
  have hkum : ∀ x, Kummer B s m x → x ≤ payloadBound B s m :=
    fun x hx ↦ hx.le_payloadBound le_rfl
  have hle2 : m ≤ 2 * m := by simp
  refine ((h₁.comp h₂ ?_).comp h₃ ?_).comp h₄ ?_
  · rintro u (hu | (hu | hu) | (hu | hu))
    · exact hb (by norm_cast) hkum u hu
    · exact hb (by norm_cast) (hlevel hle2) u hu
    · exact hb (by norm_cast) htop u hu
    · exact hb (by norm_cast) (hlevel hle2) u hu
    · exact hb (by norm_cast) htop u hu
  · rintro u (hu | hu | hu)
    · exact hb (by norm_cast) (hlevel le_rfl) u hu
    · exact hb (by norm_cast) htop u hu
    · exact hb (by norm_cast) htop u hu
  · rintro u (hu | hu | hu)
    · exact hb (by norm_cast) (hbits le_rfl) u hu
    · exact hb (by norm_cast) htop u hu
    · exact hb (by norm_cast) htop u hu

include hB hs hn₄ in
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
      (fun u ↦ Tagged 8 (Level B s (2 * n)) u ∨
        (Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u)) :=
    (((Embeds.of_isInj (definable_bitsToLevel B s 8 3)
      (isInj_bitsToLevel hB hn₄ (by norm_num))).untag (t := 7)).union (definable_tagged_bits 7 _)
        (definable_tagged_below 4 _) Embeds.refl (by tagged_disjoint)).congr
      (fun _ ↦ Iff.rfl) (fun _ ↦ by tauto)
  have hrest : 𝚺ᴬ₀.DefinablePred fun u : V ↦
      Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u := by
    have := definable_tagged_top (V := V) 3 (2 * n)
    have := definable_tagged_below (V := V) 4 (scaledLength B s n)
    definability
  have e₃ : Embeds
      (fun u ↦ Tagged 8 (Level B s (2 * n)) u ∨
        (Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u))
      (fun u ↦ (Tagged 9 (Level B s n) u ∨ Tagged 10 (Level B s n) u ∨ Tagged 6 (Kummer B s n) u) ∨
        (Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u)) :=
    ((Embeds.of_isInj (definable_legendreDown n 9 10 6)
      (isInj_legendreDown (B := B) (s := s) (by norm_num) (by norm_num) (by norm_num))).untag
        (t := 8)).union (definable_tagged_level 8 _) hrest Embeds.refl (by tagged_disjoint)
  have hbits : Embeds (Level B s n) (Bits B s n) :=
    Embeds.of_isInj (definable_levelToBits B s) (isInj_levelToBits hB hn)
  have h₉₁₀ :
      𝚺ᴬ₀.DefinablePred fun u : V ↦ Tagged 9 (Level B s n) u ∨ Tagged 10 (Level B s n) u := by
    have := definable_tagged_level (B := B) (s := s) 9 n
    have := definable_tagged_level (B := B) (s := s) 10 n
    definability
  have hrest' : 𝚺ᴬ₀.DefinablePred fun u : V ↦ Tagged 6 (Kummer B s n) u ∨
      Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u := by
    have := definable_tagged_kummer (B := B) (s := s) 6 n
    definability
  have e₄ : Embeds
      (fun u ↦ (Tagged 9 (Level B s n) u ∨ Tagged 10 (Level B s n) u ∨ Tagged 6 (Kummer B s n) u) ∨
        (Tagged 3 (Top (2 * n)) u ∨ Tagged 4 (Below (scaledLength B s n)) u))
      (LowerCodomain B s n) :=
    ((((hbits.tag (t := 9) (t' := 0)).union (definable_tagged_level 9 _)
      (definable_tagged_level 10 _) (hbits.tag (t := 10) (t' := 1)) (by tagged_disjoint)).union
        h₉₁₀ hrest' Embeds.refl (by tagged_disjoint))).congr (fun _ ↦ by tauto) (fun _ ↦ Iff.rfl)
  have hb : ∀ {t : V} {X : V → Prop}, t ≤ 10 → (∀ x, X x → x ≤ payloadBound B s n) →
      ∀ u, Tagged t X u → u < ⟪10, payloadBound B s n⟫ + 1 := fun ht hX u hu ↦
    Tagged.lt_of_le hu ht hX
  have hle : n ≤ 2 * n := by simp
  refine ((e₁.comp (c := ⟪10, payloadBound B s n⟫ + 1) e₂ ?_).comp
    (c := ⟪10, payloadBound B s n⟫ + 1) e₃ ?_).comp (c := ⟪10, payloadBound B s n⟫ + 1) e₄ ?_
  · rintro u (hu | hu)
    · exact hb (by norm_cast) (fun x hx ↦ Bits.le_payloadBound hx le_rfl) u hu
    · exact hb (by norm_cast) (fun x hx ↦ Below.le_payloadBound_of_scaledLength hx) u hu
  · rintro u (hu | hu | hu)
    · exact hb (by norm_cast) (fun x hx ↦ Level.le_payloadBound hx le_rfl) u hu
    · exact hb (by norm_cast) (fun x hx ↦ Top.le_payloadBound hx le_rfl) u hu
    · exact hb (by norm_cast) (fun x hx ↦ Below.le_payloadBound_of_scaledLength hx) u hu
  · rintro u ((hu | hu | hu) | hu | hu)
    · exact hb (by norm_cast) (fun x hx ↦ Level.le_payloadBound hx hle) u hu
    · exact hb (by norm_cast) (fun x hx ↦ Level.le_payloadBound hx hle) u hu
    · exact hb (by norm_cast) (fun x hx ↦ Kummer.le_payloadBound hx le_rfl) u hu
    · exact hb (by norm_cast) (fun x hx ↦ Top.le_payloadBound hx le_rfl) u hu
    · exact hb (by norm_cast) (fun x hx ↦ Below.le_payloadBound_of_scaledLength hx) u hu

include H in
lemma isInj_chebyshevMap : IsInj (ChebyshevMap n) (Tagged 0 (Tagged 6 (Kummer B s n)))
    (fun v ↦ Tagged 1 (Family (bandCount n) fun r ↦ Tagged 2 (Kummer B s (bandBound n r))) v ∨
      Tagged 0 (Tagged 5 (Small B s n)) v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨P, o, rfl, hk⟩ := exists_tagged_tagged_kummer hu
    obtain ⟨-, p, hpP, hp, -⟩ := kummer_pair_iff.mp hk
    by_cases hPx : P ≤ cutoff n
    · have hR : 0 < bandCount n := length_pos_iff.mpr (pos_of_gt (lt_of_lt_of_le hp.2.1 hPx))
      obtain ⟨r₀, hr₀⟩ : ∃ r₀, bandCount n = r₀ + 1 := by
        rcases zero_or_succ (bandCount n) with h | ⟨r₀, h⟩
        · exact absurd h hR.ne'
        · use r₀
      have hb₀ : bandBound n r₀ < P := by
        rw [bandBound, ← hr₀, bandSize_bandCount]
        simpa using hp.2.1
      obtain ⟨r, hr, hmin⟩ := ISigma0.least_number (P := fun r ↦ bandBound n r < P)
        (by unfold bandBound bandSize cutoff; definability) hb₀
      have hrR : r < bandCount n := by
        rw [hr₀]
        apply lt_succ_iff_le.mpr
        by_contra h
        exact hmin r₀ (not_le.mp h) hb₀
      use ⟪1, r, 2, P, o⟫
      apply chebyshevMap_pair.mpr
      left
      refine ⟨hPx, ?_⟩
      use r
      exact ⟨hrR, fun r' hr' ↦ not_lt.mp (hmin r' hr'), hr, rfl⟩
    · use ⟪0, 5, p, o⟫
      apply chebyshevMap_pair.mpr
      right
      refine ⟨not_le.mp hPx, ?_⟩
      use p
  · intro u v hu huv
    obtain ⟨P, o, rfl, hk⟩ := exists_tagged_tagged_kummer hu
    obtain ⟨hodd, p, hpP, hp, ho⟩ := kummer_pair_iff.mp hk
    rcases chebyshevMap_pair.mp huv with ⟨hPx, r, hr, hmin, hlt, rfl⟩ | ⟨hPx, p', hp'P, hp', rfl⟩
    · left
      simp only [tagged_pair_iff, family_pair_iff, true_and]
      have h₂ : 2 * bandBound n r < 2 * P := by
        rw [two_mul, two_mul]
        exact add_lt_add_of_lt_of_le hlt hlt.le
      have h₃ : P ≤ 2 * bandBound n r := by
        rcases zero_or_succ r with rfl | ⟨r'', rfl⟩
        · calc P ≤ cutoff n := hPx
            _ = bandSize n 0 := bandSize_zero.symm
            _ ≤ 2 * bandSize n (0 + 1) + 1 := (bandSize_succ hr).2
            _ ≤ 2 * bandBound n 0 := by
              simp only [bandBound, mul_add, mul_one]
              exact (add_le_add_iff_left _).mpr one_le_two
        · calc P ≤ bandBound n r'' := hmin r'' (by simp)
            _ = bandSize n (r'' + 1) + 1 := rfl
            _ ≤ 2 * bandSize n (r'' + 1 + 1) + 1 + 1 :=
              (add_le_add_iff_right 1).mpr (bandSize_succ hr).2
            _ = 2 * bandBound n (r'' + 1) := by
              simp only [bandBound, mul_add, mul_one, add_assoc, one_add_one_eq_two]
      have h₁ : 2 * bandBound n r / P = 1 := by
        apply div_eq_of
        · simpa using h₃
        · calc 2 * bandBound n r < 2 * P := h₂
            _ = P * (1 + 1) := by grind
      refine ⟨hr, kummer_pair_iff.mpr ⟨?_, ?_⟩⟩
      · rw [h₁]
        simp
      · use p
    · right
      simp only [tagged_pair_iff, true_and]
      obtain rfl := hp.unique hp'
      have hn := Kummer.gt_of_cutoff_lt hk hPx
      unfold Small
      use p
      refine ⟨le_pair_left _ _, ?_⟩
      use o
      refine ⟨le_pair_right _ _, rfl, hp.1, ?_, ho⟩
      rcases hp'.eq_or_exists_mul with hPp | ⟨Q, hQ, hPQ⟩
      · exact absurd hp.1 (H p (hPp ▸ hn.1) (hPp ▸ hn.2))
      · calc p * p ≤ p * Q := mul_le_mul_left (le_of_dvd hQ.pos hQ.dvd)
          _ = P := hPQ.symm
          _ ≤ 2 * n := hn.2
  · intro u u' v hu hu' h h'
    obtain ⟨P, o, rfl, hk⟩ := exists_tagged_tagged_kummer hu
    obtain ⟨P', o', rfl, hk'⟩ := exists_tagged_tagged_kummer hu'
    rcases chebyshevMap_pair.mp h with ⟨-, r, -, -, -, rfl⟩ | ⟨hPx, p, -, hp, rfl⟩ <;>
      rcases chebyshevMap_pair.mp h' with ⟨-, r', -, -, -, h₂⟩ | ⟨hPx', p', -, hp', h₂⟩
    · obtain ⟨-, -, -, rfl, rfl⟩ : 1 = 1 ∧ r = r' ∧ 2 = 2 ∧ P = P' ∧ o = o' := by
        simpa only [pair_ext_iff] using h₂
      rfl
    · exact absurd (pair_ext_iff.mp h₂).1 one_ne_zero
    · exact absurd (pair_ext_iff.mp h₂).1 zero_ne_one
    · obtain ⟨-, -, rfl, rfl⟩ : 0 = 0 ∧ 5 = 5 ∧ p = p' ∧ o = o' := by
        simpa only [pair_ext_iff] using h₂
      have hn := Kummer.gt_of_cutoff_lt hk hPx
      have hn' := Kummer.gt_of_cutoff_lt hk' hPx'
      obtain rfl : P = P' := le_antisymm
        (not_lt.mp (not_lt_of_isPrimePower hp' hp hn'.1 hn.2))
        (not_lt.mp (not_lt_of_isPrimePower hp hp' hn.1 hn'.2))
      rfl

include hB hs hn₄ H in
lemma embeds_domain_codomain (hn2 : 2 ≤ n) : Embeds (Domain B s n) (Codomain B s n) := by
  obtain ⟨hdefLower, hdef6, hdefRest, hdefResidue, hdefBand, hdefCheb⟩ :=
    definable_pieces (B := B) (s := s) n
  have hdefCarry := definable_tagged_carry (B := B) (s := s) n
  have eA : Embeds (Domain B s n) fun u ↦ Tagged 0 (LowerCodomain B s n) u ∨
      Tagged 1 (Family (bandCount n) fun r ↦ BandCarry B s (bandBound n r)) u :=
    (embeds_lower hB hs hn₄).tag.union hdefLower hdefCarry Embeds.refl (by tagged_disjoint)
  have eB : Embeds
      (fun u ↦ Tagged 0 (LowerCodomain B s n) u ∨
        Tagged 1 (Family (bandCount n) fun r ↦ BandCarry B s (bandBound n r)) u)
      (fun u ↦ Tagged 0 (LowerResidue B s n) u ∨
        Tagged 1 (Family (bandCount n) fun r ↦ BandDomain B s (bandBound n r)) u) :=
    ((Embeds.of_isInj hdefCheb (isInj_chebyshevMap H)).union hdef6
      hdefRest Embeds.refl (by
        intro y hy hy'
        simp only [Tagged, Family, BandCarry] at hy hy'
        aesop)).congr
      (fun _ ↦ by simp only [Tagged, LowerCodomain]; grind)
      (fun _ ↦ by simp only [Tagged, Family, LowerResidue, BandCarry, BandDomain]; grind)
  have hF := definable_bandStep_bandBound (B := B) (s := s) n
  have eC : Embeds
      (fun u ↦ Tagged 0 (LowerResidue B s n) u ∨
        Tagged 1 (Family (bandCount n) fun r ↦ BandDomain B s (bandBound n r)) u)
      (Codomain B s n) :=
    Embeds.refl.union hdefResidue hdefBand
      ((Embeds.family hF fun r hr ↦ isInj_bandStep hB <|
        lt_of_le_of_lt (mul_le_mul_left (length_monotone (mul_le_mul_left (mul_le_mul_left
          (bandBound_le hr hn2))))) hn₄).tag) (by tagged_disjoint)
  exact (eA.comp (c := ⟪1, n, 10, payloadBound B s n⟫ + 1) eB (fun _ hu ↦ by
      rcases hu with hu | hu
      · exact Tagged.lt_of_tagged_zero hu fun _ ↦ LowerCodomain.le_bound
      · exact Tagged.lt_of_family hu bandCount_le fun r hr x hx ↦
          BandCarry.le_bound (bandBound_le hr hn2) hx)).comp
    (c := ⟪1, n, 10, payloadBound B s n⟫ + 1) eC (fun _ hu ↦ by
      rcases hu with hu | hu
      · exact Tagged.lt_of_tagged_zero hu fun _ ↦ LowerResidue.le_bound
      · exact Tagged.lt_of_family hu bandCount_le fun r hr x hx ↦
          BandDomain.le_bound (bandBound_le hr hn2) hx)

end assembly

end Bertrand

end

end FFL.FirstOrder.Arithmetic
