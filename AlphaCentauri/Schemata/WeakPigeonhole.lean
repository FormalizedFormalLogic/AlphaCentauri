module

public import AlphaCentauri.Schemata.Pigeonhole
public import AlphaCentauri.ToFoundation.BlockSequence

/-!
# The weak pigeonhole principle over $\mathsf{I}\Delta_0 + \Omega_1$

In a model of $\mathsf{I}\Delta_0 + \Omega_1$, no $\Delta_0$-definable relation is an injection of
$a^2$ into $a$, for $a > 1$. An injection folds a binary tree of depth $\|a\|$ whose leaves can be
any $2^{\|a\|}$ values below $a$; diagonalizing against the roots gives a contradiction.

- [PWW88, Theorem 1]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic

noncomputable section

namespace WeakPigeonhole

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁]

variable (R : V → V → Prop) (a : V)

/-- `x` is the left (`β = 0`) or right (`β = 1`) child of `e` in the tree of `R`: `R` sends a pair
with `x` in that coordinate to `e`. -/
def IsChild (β e x : V) : Prop :=
  (β = 0 ∧ ∃ w < a, R (x + a * w) e) ∨ (β = 1 ∧ ∃ w < a, R (w + a * x) e)

/-- The blocks of `s` of width `‖a‖` trace a path of length `d` from `c` along the bits of `τ`,
lowest bit first. -/
def IsPath (d s c τ : V) : Prop :=
  Nuon.ext a s 0 = c ∧
    ∀ i < d, Nuon.ext a s (i + 1) < a ∧
      IsChild R a (fbit τ i) (Nuon.ext a s i) (Nuon.ext a s (i + 1))

/-- The path of length `d` from `c` along `τ` ends at `e`. -/
def IsLeaf (d c τ e : V) : Prop :=
  ∃ s < (2 * a) ⨳ a, IsPath R a d s c τ ∧ Nuon.ext a s d = e

variable {R a}

lemma definable_isChild (hR : 𝚺ᴬ₀.DefinableRel R) : 𝚺ᴬ₀.DefinableRel₃ (IsChild R a) := by
  unfold IsChild
  definability

lemma definable_isLeaf (hR : 𝚺ᴬ₀.DefinableRel R) : 𝚺ᴬ₀.DefinableRel₄ (IsLeaf R a) := by
  have := definable_isChild (a := a) hR
  unfold IsLeaf IsPath
  definability

lemma IsPath.ext_lt {d s c τ i : V} (hc : c < a) (h : IsPath R a d s c τ) (hi : i ≤ d) :
    Nuon.ext a s i < a := by
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · rwa [h.1]
  · exact (h.2 j (succ_le_iff_lt.mp hi)).1

section injective

variable (hinj : ∀ x < a * a, ∀ x' < a * a, ∀ y < a, R x y → R x' y → x = x')
include hinj

lemma IsChild.unique {β e x x' : V} (he : e < a) (hx : x < a) (hx' : x' < a)
    (h : IsChild R a β e x) (h' : IsChild R a β e x') : x = x' := by
  have hlt : ∀ {u v : V}, u < a → v < a → u + a * v < a * a := by
    intro u v hu hv
    calc u + a * v < a + a * v := by simpa using hu
      _ = a * (v + 1) := by rw [mul_add, mul_one, add_comm]
      _ ≤ a * a := mul_le_mul_left (succ_le_iff_lt.mpr hv)
  have hmod : ∀ {u v : V}, u < a → (u + a * v) % a = u := by
    intro u v hu
    rw [add_comm, mul_comm, mod_mul_add_of_lt _ _ hu]
  have hdiv : ∀ {u v : V}, u < a → (u + a * v) / a = v := by
    intro u v hu
    rw [add_comm, mul_comm, div_mul_add _ _ hu]
  rcases h with ⟨rfl, w, hw, hR⟩ | ⟨rfl, w, hw, hR⟩ <;>
    rcases h' with ⟨h0, w', hw', hR'⟩ | ⟨h1, w', hw', hR'⟩
  · have := hinj _ (hlt hx hw) _ (hlt hx' hw') e he hR hR'
    rw [← hmod (v := w) hx, ← hmod (v := w') hx', this]
  · simp at h1
  · simp at h0
  · have := hinj _ (hlt hw hx) _ (hlt hw' hx') e he hR hR'
    rw [← hdiv (v := x) hw, ← hdiv (v := x') hw', this]

lemma IsPath.ext_eq {d s s' c τ : V} (hc : c < a) (h : IsPath R a d s c τ)
    (h' : IsPath R a d s' c τ) : ∀ i ≤ d, Nuon.ext a s i = Nuon.ext a s' i := by
  intro i
  induction i using ISigma0.succ_induction
  · definability
  case zero => intro _; rw [h.1, h'.1]
  case succ i IH =>
    intro hi
    have hid : i < d := succ_le_iff_lt.mp hi
    obtain ⟨hlt, hch⟩ := h.2 i hid
    obtain ⟨hlt', hch'⟩ := h'.2 i hid
    rw [← IH hid.le] at hch'
    exact IsChild.unique hinj (h.ext_lt hc hid.le) hlt hlt' hch hch'

lemma IsLeaf.unique {d c τ e e' : V} (hc : c < a) (h : IsLeaf R a d c τ e)
    (h' : IsLeaf R a d c τ e') : e = e' := by
  obtain ⟨s, -, hs, rfl⟩ := h
  obtain ⟨s', -, hs', rfl⟩ := h'
  exact hs.ext_eq hinj hc hs' d le_rfl

end injective

lemma fbit_two_mul_add_zero {τ β : V} (hβ : β < 2) : fbit (2 * τ + β) 0 = β := by
  rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hβ) with rfl | rfl <;> simp

lemma fbit_two_mul_add_succ {τ β : V} (hβ : β < 2) (i : V) :
    fbit (2 * τ + β) (i + 1) = fbit τ i := by
  rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hβ) with rfl | rfl <;> simp

lemma IsLeaf.cons {d c c' τ β e : V} (ha : 0 < a) (hd : d < ‖a‖) (hc : c < a) (hc' : c' < a)
    (hβ : β < 2) (hch : IsChild R a β c c') (h : IsLeaf R a d c' τ e) :
    IsLeaf R a (d + 1) c (2 * τ + β) e := by
  obtain ⟨s', -, hs', rfl⟩ := h
  have hI : ‖2 * a‖ = ‖a‖ + 1 := length_two_mul_of_pos ha
  have hK : Exponential (1 * ‖a‖) (a ⨳ 1) := by simpa using exponential_smash_one a
  have hK' : Exponential ((d + 1) * ‖a‖) (bexp ((2 * a) ⨳ a) ((d + 1) * ‖a‖)) :=
    exp_bexp_of_lt (Nuon.mul_len_lt_len_smash (by simpa [hI] using hd.le))
  set K := a ⨳ 1
  set q := bexp ((2 * a) ⨳ a) ((d + 1) * ‖a‖)
  have hcK : c < K := lt_of_lt_of_le hc (lt_smash_one_right a).le
  have hext0 : Nuon.ext a (c + s' % q * K) 0 = c := by
    rw [← ext_mod_pow2 (I := 2 * a) (k := 1) (by simp [hI]) (by simp) hK,
      mod_add_mul _ _ hK.range_pos, mod_eq_self_of_lt hcK]
    exact Nuon.ext_zero_eq_self_of_le (length_monotone hc.le)
  have hext : ∀ i ≤ d, Nuon.ext a (c + s' % q * K) (i + 1) = Nuon.ext a s' i := by
    intro i hi
    rw [add_comm i 1, ← ext_div_pow2 (I := 2 * a) (by simpa [hI, add_comm 1 i] using hi.trans hd.le) hK,
      div_add_mul_self _ _ hK.range_pos, div_eq_zero_of_lt _ hcK, zero_add,
      ext_mod_pow2 (I := 2 * a) (by simpa [hI] using hd.le) (lt_succ_iff_le.mpr hi) hK']
  refine ⟨c + s' % q * K, ?_, ⟨hext0, ?_⟩, hext d le_rfl⟩
  · have hqK : Exponential ((d + 1) * ‖a‖ + 1 * ‖a‖) (q * K) := hK'.add_mul hK
    calc c + s' % q * K < K + s' % q * K := by simpa using hcK
      _ = (s' % q + 1) * K := by rw [add_mul, one_mul, add_comm]
      _ ≤ q * K := mul_le_mul_right (succ_le_iff_lt.mpr (mod_lt _ hK'.range_pos))
      _ ≤ (2 * a) ⨳ a := hqK.monotone_le (exponential_smash _ _) (by
        rw [← add_mul, hI]
        exact mul_le_mul_right (add_le_add_left (succ_le_iff_lt.mpr hd) 1))
  · intro i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · rw [hext 0 (Arithmetic.zero_le d), hext0, hs'.1, fbit_two_mul_add_zero hβ]
      exact ⟨hc', hch⟩
    · have hj : j < d := by simpa using hi
      rw [hext (j + 1) (succ_le_iff_lt.mpr hj), hext j hj.le, fbit_two_mul_add_succ hβ]
      exact hs'.2 j hj

end WeakPigeonhole

end

end FFL.FirstOrder.Arithmetic
