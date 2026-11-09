module

public import AlphaCentauri.Schemata.Pigeonhole
public import AlphaCentauri.ToFoundation.BlockSequence
public import AlphaCentauri.ToFoundation.Exponential

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

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁]

namespace WeakPigeonhole

section tree

variable (C : V → V → V → Prop) (a : V)

/-- The blocks of `s` of width `‖a‖` trace a path of length `d` from `c` along the bits of `τ`,
lowest bit first, each step going from a node `e` to a node `x` with `C β e x` for the current bit
`β`.
- [PWW88, proof of Theorem 1] -/
def IsPath (d s c τ : V) : Prop :=
  Nuon.ext a s 0 = c ∧
    ∀ i < d, Nuon.ext a s (i + 1) < a ∧ C (fbit τ i) (Nuon.ext a s i) (Nuon.ext a s (i + 1))

/-- The path of length `d` from `c` along `τ` ends at `e`: $H^d_c(\tau) = e$.
- [PWW88, proof of Theorem 1] -/
def IsLeaf (d c τ e : V) : Prop :=
  ∃ s < (2 * a) ⨳ a, IsPath C a d s c τ ∧ Nuon.ext a s d = e

variable {C a}

lemma definable_isLeaf (hC : 𝚺ᴬ₀.DefinableRel₃ C) : 𝚺ᴬ₀.DefinableRel₄ (IsLeaf C a) := by
  unfold IsLeaf IsPath
  definability

lemma IsPath.ext_lt {d s c τ i : V} (hc : c < a) (h : IsPath C a d s c τ) (hi : i ≤ d) :
    Nuon.ext a s i < a := by
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · rwa [h.1]
  · exact (h.2 j (succ_le_iff_lt.mp hi)).1

lemma IsPath.ext_eq {d s s' c τ τ' : V} (hc : c < a)
    (hC : ∀ i < d, ∀ e < a, ∀ x < a, ∀ x' < a, C (fbit τ i) e x → C (fbit τ' i) e x' → x = x')
    (h : IsPath C a d s c τ) (h' : IsPath C a d s' c τ') :
    ∀ i ≤ d, Nuon.ext a s i = Nuon.ext a s' i := by
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
    exact hC i hid _ (h.ext_lt hc hid.le) _ hlt _ hlt' hch hch'

lemma isLeaf_zero {e : V} (he : e < a) (τ : V) : IsLeaf C a 0 e τ e := by
  have hext : Nuon.ext a e 0 = e := Nuon.ext_zero_eq_self_of_le (length_monotone he.le)
  use e
  and_intros
  · calc e < a := he
      _ < a ⨳ 1 := lt_smash_one_right a
      _ ≤ (2 * a) ⨳ a := smash_monotone (by simp) (pos_iff_one_le.mp (pos_of_gt he))
  · exact hext
  · intro i hi
    simp at hi
  · exact hext

lemma IsLeaf.cons {d c c' τ β e : V} (ha : 0 < a) (hd : d < ‖a‖) (hc : c < a) (hc' : c' < a)
    (hβ : β < 2) (hch : C β c c') (h : IsLeaf C a d c' τ e) :
    IsLeaf C a (d + 1) c (2 * τ + β) e := by
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
    have hi' : 1 + i ≤ ‖2 * a‖ := by simpa [hI, add_comm 1 i] using hi.trans hd.le
    rw [add_comm i 1, ← ext_div_pow2 hi' hK,
      div_add_mul_self _ _ hK.range_pos, div_eq_zero_of_lt _ hcK, zero_add,
      ext_mod_pow2 (I := 2 * a) (by simpa [hI] using hd.le) (lt_succ_iff_le.mpr hi) hK']
  have hfbit : ∀ i, fbit (2 * τ + β) (i + 1) = fbit τ i := by
    intro i
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hβ) with rfl | rfl <;> simp
  use c + s' % q * K
  and_intros
  · have hqK : Exponential ((d + 1) * ‖a‖ + 1 * ‖a‖) (q * K) := hK'.add_mul hK
    calc c + s' % q * K < K + s' % q * K := by simpa using hcK
      _ = (s' % q + 1) * K := by rw [add_mul, one_mul, add_comm]
      _ ≤ q * K := mul_le_mul_right (succ_le_iff_lt.mpr (mod_lt _ hK'.range_pos))
      _ ≤ (2 * a) ⨳ a := hqK.monotone_le (exponential_smash _ _) (by
        rw [← add_mul, hI]
        exact mul_le_mul_right (add_le_add_left (succ_le_iff_lt.mpr hd) 1))
  · exact hext0
  · intro i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · have : fbit (2 * τ + β) 0 = β := by
        rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hβ) with rfl | rfl <;> simp
      rw [hext 0 (Arithmetic.zero_le d), hext0, hs'.1, this]
      exact ⟨hc', hch⟩
    · have hj : j < d := by simpa using hi
      rw [hext (j + 1) (succ_le_iff_lt.mpr hj), hext j hj.le, hfbit]
      exact hs'.2 j hj
  · exact hext d le_rfl

end tree

section square

variable (R : V → V → Prop) (a : V)

/-- `x` is the left (`β = 0`) or right (`β = 1`) child of `e` in the tree of `R`: `R` sends a pair
with `x` in that coordinate to `e`. -/
def IsChild (β e x : V) : Prop :=
  (β = 0 ∧ ∃ w < a, R (x + a * w) e) ∨ (β = 1 ∧ ∃ w < a, R (w + a * x) e)

variable {R a}

lemma definable_isChild (hR : 𝚺ᴬ₀.DefinableRel R) : 𝚺ᴬ₀.DefinableRel₃ (IsChild R a) := by
  unfold IsChild
  definability

section injective

variable (hinj : ∀ x < a * a, ∀ x' < a * a, ∀ y < a, R x y → R x' y → x = x')
include hinj

lemma IsChild.unique {β e x x' : V} (he : e < a) (hx : x < a) (hx' : x' < a)
    (h : IsChild R a β e x) (h' : IsChild R a β e x') : x = x' := by
  rcases h with ⟨rfl, w, hw, hR⟩ | ⟨rfl, w, hw, hR⟩ <;>
    rcases h' with ⟨h0, w', hw', hR'⟩ | ⟨h1, w', hw', hR'⟩
  · exact ((add_mul_eq_add_mul_iff hx hx').mp <|
      hinj _ (add_mul_lt_mul_of_lt hx hw) _ (add_mul_lt_mul_of_lt hx' hw') e he hR hR').1
  · simp at h1
  · simp at h0
  · exact ((add_mul_eq_add_mul_iff hw hw').mp <|
      hinj _ (add_mul_lt_mul_of_lt hw hx) _ (add_mul_lt_mul_of_lt hw' hx') e he hR hR').2

lemma IsLeaf.unique {d c τ e e' : V} (hc : c < a) (h : IsLeaf (IsChild R a) a d c τ e)
    (h' : IsLeaf (IsChild R a) a d c τ e') : e = e' := by
  obtain ⟨s, -, hs, rfl⟩ := h
  obtain ⟨s', -, hs', rfl⟩ := h'
  exact hs.ext_eq hc (fun _ _ _ he _ hx _ hx' ↦ IsChild.unique hinj he hx hx') hs' d le_rfl

end injective

/-- For a $\Delta_0$-definable relation `T` with a value below `a` everywhere, every
$\rho < 2^{\|a\| - d}$ has a root `c < a` whose leaf along each $\tau < 2^d$ is a value of `T`
at $\rho + 2^{\|a\| - d} \tau$.
- [PWW88, Claim in the proof of Theorem 1] -/
lemma exists_root (hR : 𝚺ᴬ₀.DefinableRel R) (ha : 0 < a) (htot : ∀ x < a * a, ∃ y < a, R x y)
    {T : V → V → Prop} (hT : 𝚺ᴬ₀.DefinableRel T) (hTa : ∀ σ, ∃ e < a, T σ e) :
    ∀ d ≤ ‖a‖, ∀ ρ < bexp (2 * a) (‖a‖ - d), ∃ c < a, ∀ τ < bexp (2 * a) d,
      ∃ e < a, T (ρ + bexp (2 * a) (‖a‖ - d) * τ) e ∧ IsLeaf (IsChild R a) a d c τ e := by
  have hI : ‖2 * a‖ = ‖a‖ + 1 := length_two_mul_of_pos ha
  intro d
  induction d using ISigma0.succ_induction
  · have := definable_isLeaf (a := a) (definable_isChild (a := a) hR)
    definability
  case zero =>
    intro _ ρ _
    obtain ⟨e, he, hTe⟩ := hTa ρ
    use e
    constructor
    · exact he
    · intro τ hτ
      have hτ0 : τ = 0 := by simpa [bexp_pos_zero (show 0 < 2 * a by simpa using ha)] using hτ
      subst hτ0
      use e
      and_intros
      · exact he
      · simpa using hTe
      · exact isLeaf_zero he 0
  case succ d IH =>
    intro hd ρ hρ
    have hd' : d < ‖a‖ := succ_le_iff_lt.mp hd
    obtain ⟨k, hk⟩ := le_iff_exists_add.mp hd
    have hP : bexp (2 * a) (‖a‖ - d) = 2 * bexp (2 * a) (‖a‖ - (d + 1)) := by
      have : ‖a‖ - d = ‖a‖ - (d + 1) + 1 := by
        rw [hk, add_tsub_cancel_left, add_assoc, add_tsub_cancel_left, add_comm]
      rw [this, bexp_succ (by rw [hI, ← this]; exact lt_succ_iff_le.mpr (sub_le_self _ _))]
    have hQ : bexp (2 * a) (d + 1) = 2 * bexp (2 * a) d := bexp_succ (by simpa [hI] using hd')
    set p := bexp (2 * a) (‖a‖ - (d + 1))
    obtain ⟨c₀, hc₀, H₀⟩ := IH hd'.le ρ (by rw [hP, two_mul]; exact lt_of_lt_of_le hρ le_self_add)
    obtain ⟨c₁, hc₁, H₁⟩ := IH hd'.le (ρ + p) (by rw [hP, two_mul]; simpa using hρ)
    obtain ⟨c, hc, hRc⟩ := htot (c₀ + a * c₁) (add_mul_lt_mul_of_lt hc₀ hc₁)
    use c
    constructor
    · exact hc
    · intro τ' hτ'
      have hτ : τ' / 2 < bexp (2 * a) d := div_lt_of_lt_mul (by rwa [hQ, mul_comm] at hτ')
      rw [← div_add_mod τ' 2]
      rcases mod_two τ' with h | h <;> rw [h]
      · obtain ⟨e, he, hTe, hl⟩ := H₀ (τ' / 2) hτ
        have heq : ρ + p * (2 * (τ' / 2) + 0) = ρ + bexp (2 * a) (‖a‖ - d) * (τ' / 2) := by
          rw [hP]
          grind
        use e
        and_intros
        · exact he
        · rwa [heq]
        · exact hl.cons ha hd' hc hc₀ (by simp) (Or.inl ⟨rfl, c₁, hc₁, hRc⟩)
      · obtain ⟨e, he, hTe, hl⟩ := H₁ (τ' / 2) hτ
        have heq : ρ + p * (2 * (τ' / 2) + 1) = ρ + p + bexp (2 * a) (‖a‖ - d) * (τ' / 2) := by
          rw [hP]
          grind
        use e
        and_intros
        · exact he
        · rwa [heq]
        · exact hl.cons ha hd' hc hc₁ one_lt_two (Or.inr ⟨rfl, c₀, hc₀, hRc⟩)

lemma definable_diagonal (hR : 𝚺ᴬ₀.DefinableRel R) :
    𝚺ᴬ₀.DefinableRel fun σ e ↦
      (IsLeaf (IsChild R a) a ‖a‖ σ σ 0 ∧ e = 1) ∨ (¬IsLeaf (IsChild R a) a ‖a‖ σ σ 0 ∧ e = 0) := by
  have := definable_isLeaf (a := a) (definable_isChild (a := a) hR)
  definability

end square

end WeakPigeonhole

open WeakPigeonhole in
/-- In a model of $\mathsf{I}\Delta_0 + \Omega_1$, no $\Delta_0$-definable relation is an injection
of $a^2$ into $a$, for $a > 1$.
- [PWW88, Theorem 1] -/
theorem weakPigeonhole {R : V → V → Prop} (hR : 𝚺ᴬ₀.DefinableRel R) {a : V} (ha : 1 < a)
    (total : ∀ x < a * a, ∃ y < a, R x y) :
    ∃ x < a * a, ∃ x' < a * a, ∃ y < a, x ≠ x' ∧ R x y ∧ R x' y := by
  by_contra! hne
  have hinj : ∀ x < a * a, ∀ x' < a * a, ∀ y < a, R x y → R x' y → x = x' := by
    intro x hx x' hx' y hy h h'
    by_contra hxx
    exact hne x hx x' hx' y hy hxx h h'
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hT := definable_diagonal (a := a) hR
  have hTa : ∀ σ, ∃ e < a,
      (IsLeaf (IsChild R a) a ‖a‖ σ σ 0 ∧ e = 1) ∨
        (¬IsLeaf (IsChild R a) a ‖a‖ σ σ 0 ∧ e = 0) := by
    intro σ
    by_cases h : IsLeaf (IsChild R a) a ‖a‖ σ σ 0
    · use 1
      constructor
      · exact ha
      · exact Or.inl ⟨h, rfl⟩
    · use 0
      constructor
      · exact ha0
      · exact Or.inr ⟨h, rfl⟩
  obtain ⟨c, hc, H⟩ := exists_root hR ha0 total hT hTa ‖a‖ le_rfl 0 (by simp [ha0])
  have hcK : c < bexp (2 * a) ‖a‖ :=
    hc.trans (lt_bexp_len (by rw [length_two_mul_of_pos ha0]; exact lt_add_one _))
  obtain ⟨e, -, hTe, hl⟩ := H c hcK
  have h0 : bexp (2 * a) (‖a‖ - ‖a‖) = 1 := by simp [ha0]
  rw [h0, one_mul, zero_add] at hTe
  rcases hTe with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact one_ne_zero (hl.unique hinj hc h)
  · exact h hl

end

/-- $\mathsf{I}\Delta_0 + \Omega_1$ proves the weak pigeonhole principle for $\Delta_0$ formulas.
- [PWW88, Theorem 1] -/
theorem WeakPigeonholeOnPrenexHierarchy_weakerThan_ISigma0_union_Omega1 :
    𝗪𝗣𝗛𝗣 𝚺 0 ⪯ 𝗜𝚺₀ ∪ 𝝮₁ := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀ ∪ 𝝮₁ :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) inferInstance
  exact weakerThan_of_models.{0} _ _ fun V _ _ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
    refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    apply (models_weakPigeonholeAxiom_iff φ).mpr
    intro f a ha total
    apply weakPigeonhole _ ha total
    exact HierarchySymbol.Definable.mkPolarity (Γ := 𝚺) (m := 0) (Rew.rewriteMap f ▹ φ)
      (Bounding.Hierarchy.rew _ (Bounding.PrenexHierarchy.zero_iff.mp hφ))
      fun v ↦ by simp [Semiformula.eval_rewriteMap, ← Matrix.fun_eq_vec_two]

end FFL.FirstOrder.Arithmetic
