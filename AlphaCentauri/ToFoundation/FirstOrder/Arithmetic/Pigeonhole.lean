module

public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Arithmetic.Definability
public import Foundation.FirstOrder.Arithmetic.Exponential.Bit
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Exponential

/-!
# Injections and the pigeonhole principle

Supplements `Foundation.FirstOrder.Arithmetic.Exponential.Bit`: injections between definable sets
of a model, the pigeonhole principle for $\Sigma_m$-definable relations in models of
$\mathsf{I}\Sigma_m$, and for coded injections in models of $\mathsf{EA}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

section Injection

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*}

/-- `R` is an injection of `X` into `Y`. -/
def IsInj (R : V → V → Prop) (X Y : V → Prop) : Prop :=
  (∀ x, X x → ∃ y, R x y) ∧ (∀ x y, X x → R x y → Y y) ∧
    ∀ x x' y, X x → X x' → R x y → R x' y → x = x'

/-- `R` on `X` and `S` on `X'`. -/
def UnionMap (X : V → Prop) (R : V → V → Prop) (X' : V → Prop) (S : V → V → Prop) (x y : V) :
    Prop :=
  (X x ∧ R x y) ∨ (X' x ∧ S x y)

/-- The identity relation. -/
def IdMap (x y : V) : Prop := y = x

/-- `R` followed by `S`, through values below `c`. -/
def CompMap [LT V] (c : V) (R S : V → V → Prop) (x z : V) : Prop := ∃ y < c, R x y ∧ S y z

namespace IsInj

variable {R S : V → V → Prop} {X X' Y Y' W : V → Prop}

lemma union (h : IsInj R X Y) (h' : IsInj S X' Y') (hY : ∀ y, Y y → Y' y → False) :
    IsInj (UnionMap X R X' S) (fun x ↦ X x ∨ X' x) (fun y ↦ Y y ∨ Y' y) := by
  and_intros
  · rintro x (hx | hx)
    · obtain ⟨y, hy⟩ := h.1 x hx
      use y
      exact Or.inl ⟨hx, hy⟩
    · obtain ⟨y, hy⟩ := h'.1 x hx
      use y
      exact Or.inr ⟨hx, hy⟩
  · rintro x y - (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact Or.inl (h.2.1 x y hx hy)
    · exact Or.inr (h'.2.1 x y hx hy)
  · rintro x x' y - - (⟨hx, hy⟩ | ⟨hx, hy⟩) (⟨hx', hy'⟩ | ⟨hx', hy'⟩)
    · exact h.2.2 x x' y hx hx' hy hy'
    · exact absurd (h'.2.1 x' y hx' hy') fun h'' ↦ hY y (h.2.1 x y hx hy) h''
    · exact absurd (h'.2.1 x y hx hy) fun h'' ↦ hY y (h.2.1 x' y hx' hy') h''
    · exact h'.2.2 x x' y hx hx' hy hy'

lemma id : IsInj IdMap X X :=
  ⟨fun x _ ↦ ⟨x, rfl⟩, fun _ _ hx hy ↦ hy ▸ hx, fun _ _ _ _ _ hy hy' ↦ hy.symm.trans hy'⟩

lemma mono (h : IsInj R X Y) (hX : ∀ x, X' x → X x) (hY : ∀ y, Y y → Y' y) : IsInj R X' Y' :=
  ⟨fun x hx ↦ h.1 x (hX x hx), fun x y hx hy ↦ hY y (h.2.1 x y (hX x hx) hy),
    fun x x' y hx hx' ↦ h.2.2 x x' y (hX x hx) (hX x' hx')⟩

lemma congr (h : IsInj R X Y) (hX : ∀ x, X x ↔ X' x) (hY : ∀ y, Y y ↔ Y' y) : IsInj R X' Y' :=
  h.mono (fun x hx ↦ (hX x).mpr hx) (fun y hy ↦ (hY y).mp hy)

lemma comp [LT V] {c : V} (h : IsInj R X Y) (h' : IsInj S Y W) (hY : ∀ y, Y y → y < c) :
    IsInj (CompMap c R S) X W := by
  and_intros
  · intro x hx
    obtain ⟨y, hy⟩ := h.1 x hx
    obtain ⟨z, hz⟩ := h'.1 y (h.2.1 x y hx hy)
    use z, y
    exact ⟨hY y (h.2.1 x y hx hy), hy, hz⟩
  · rintro x z hx ⟨y, -, hy, hz⟩
    exact h'.2.1 y z (h.2.1 x y hx hy) hz
  · rintro x x' z hx hx' ⟨y, -, hy, hz⟩ ⟨y', -, hy', hz'⟩
    obtain rfl := h'.2.2 y y' z (h.2.1 x y hx hy) (h.2.1 x' y' hx' hy') hz hz'
    exact h.2.2 x x' y hx hx' hy hy'

end IsInj

variable [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- `R` on the tag-`t` copy, forgetting the tag. -/
def UntagMap (t : V) (R : V → V → Prop) (u v : V) : Prop := π₁ u = t ∧ R (π₂ u) v

/-- `R`, landing in the tag-`t` copy. -/
def TagOutMap (t : V) (R : V → V → Prop) (u v : V) : Prop := π₁ v = t ∧ R u (π₂ v)

/-- The copy $\{\langle t, x \rangle : x \in X\}$ of `X` with the tag `t`. -/
def Tagged (t : V) (X : V → Prop) (u : V) : Prop := π₁ u = t ∧ X (π₂ u)

/-- `R` acting on the tag-`t` copy and landing in the tag-`t'` copy. -/
def TagMap (t t' : V) (R : V → V → Prop) (u v : V) : Prop := π₁ u = t ∧ π₁ v = t' ∧ R (π₂ u) (π₂ v)

/-- The indexed family $\{\langle r, x \rangle : r < N, x \in X_r\}$. -/
def Family (N : V) (X : V → V → Prop) (u : V) : Prop := π₁ u < N ∧ X (π₁ u) (π₂ u)

/-- `F r` acting on the `r`-th member of a family. -/
def FamilyMap (F : V → V → V → Prop) (u v : V) : Prop := π₁ v = π₁ u ∧ F (π₁ u) (π₂ u) (π₂ v)

lemma Tagged.disjoint {t t' u : V} {X Y : V → Prop} (htt : t ≠ t') (h : Tagged t X u)
    (h' : Tagged t' Y u) : False :=
  htt (h.1.symm.trans h'.1)

namespace IsInj

variable {R : V → V → Prop} {X Y : V → Prop}

lemma tag {t t' : V} (h : IsInj R X Y) : IsInj (TagMap t t' R) (Tagged t X) (Tagged t' Y) := by
  and_intros
  · rintro u ⟨rfl, hu⟩
    obtain ⟨y, hy⟩ := h.1 _ hu
    use ⟪t', y⟫
    and_intros
    · rfl
    · simp
    · simpa using hy
  · rintro u v ⟨-, hu⟩ ⟨-, hv, huv⟩
    exact ⟨hv, h.2.1 _ _ hu huv⟩
  · rintro u u' v ⟨hu₁, hu⟩ ⟨hu₁', hu'⟩ ⟨-, -, huv⟩ ⟨-, -, huv'⟩
    rw [← pair_unpair u, ← pair_unpair u', hu₁, hu₁', h.2.2 _ _ _ hu hu' huv huv']

lemma family {N : V} {F : V → V → V → Prop} {X Y : V → V → Prop}
    (h : ∀ r < N, IsInj (F r) (X r) (Y r)) :
    IsInj (FamilyMap F) (Family N X) (Family N Y) := by
  and_intros
  · rintro u ⟨hr, hu⟩
    obtain ⟨y, hy⟩ := (h _ hr).1 _ hu
    use ⟪π₁ u, y⟫
    and_intros
    · simp
    · simpa using hy
  · rintro u v ⟨hr, hu⟩ ⟨hv, huv⟩
    exact ⟨hv ▸ hr, hv ▸ (h _ hr).2.1 _ _ hu huv⟩
  · rintro u u' v ⟨hr, hu⟩ ⟨hr', hu'⟩ ⟨hv, huv⟩ ⟨hv', huv'⟩
    have h₁ : π₁ u = π₁ u' := hv.symm.trans hv'
    rw [h₁] at hu huv
    rw [← pair_unpair u, ← pair_unpair u', h₁, (h _ hr').2.2 _ _ _ hu hu' huv huv']

lemma untag {t : V} (h : IsInj R X Y) : IsInj (UntagMap t R) (Tagged t X) Y := by
  and_intros
  · rintro u ⟨hu₁, hu⟩
    obtain ⟨y, hy⟩ := h.1 _ hu
    use y
    exact ⟨hu₁, hy⟩
  · rintro u v ⟨-, hu⟩ ⟨-, huv⟩
    exact h.2.1 _ _ hu huv
  · rintro u u' v ⟨hu₁, hu⟩ ⟨hu₁', hu'⟩ ⟨-, huv⟩ ⟨-, huv'⟩
    rw [← pair_unpair u, ← pair_unpair u', hu₁, hu₁', h.2.2 _ _ _ hu hu' huv huv']

lemma tagOut {t : V} (h : IsInj R X Y) : IsInj (TagOutMap t R) X (Tagged t Y) := by
  and_intros
  · intro u hu
    obtain ⟨y, hy⟩ := h.1 _ hu
    use ⟪t, y⟫
    simpa [TagOutMap] using hy
  · rintro u v hu ⟨hv, huv⟩
    exact ⟨hv, h.2.1 _ _ hu huv⟩
  · rintro u u' v hu hu' ⟨-, huv⟩ ⟨-, huv'⟩
    exact h.2.2 _ _ _ hu hu' huv huv'

end IsInj

/-- Some $\Delta_0$-definable relation is an injection of `X` into `Y`. -/
def Embeds (X Y : V → Prop) : Prop := ∃ R : V → V → Prop, 𝚺ᴬ₀.DefinableRel R ∧ IsInj R X Y

namespace Embeds

variable {X X' Y Y' W : V → Prop}

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
lemma of_isInj {R : V → V → Prop} (hR : 𝚺ᴬ₀.DefinableRel R) (h : IsInj R X Y) : Embeds X Y := by
  use R

lemma refl : Embeds X X := ⟨_, by unfold IdMap; definability, IsInj.id⟩

lemma comp {c : V} (h : Embeds X Y) (h' : Embeds Y W) (hY : ∀ y, Y y → y < c) : Embeds X W := by
  obtain ⟨R, hR, h⟩ := h
  obtain ⟨S, hS, h'⟩ := h'
  exact ⟨_, by unfold CompMap; definability, h.comp h' hY⟩

lemma union (hX : 𝚺ᴬ₀.DefinablePred X) (hX' : 𝚺ᴬ₀.DefinablePred X') (h : Embeds X Y)
    (h' : Embeds X' Y') (hY : ∀ y, Y y → Y' y → False) :
    Embeds (fun x ↦ X x ∨ X' x) (fun y ↦ Y y ∨ Y' y) := by
  obtain ⟨R, hR, h⟩ := h
  obtain ⟨S, hS, h'⟩ := h'
  exact ⟨_, by unfold UnionMap; definability, h.union h' hY⟩

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
lemma mono (h : Embeds X Y) (hX : ∀ x, X' x → X x) (hY : ∀ y, Y y → Y' y) : Embeds X' Y' := by
  obtain ⟨R, hR, h⟩ := h
  use R
  exact ⟨hR, h.mono hX hY⟩

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
lemma congr (h : Embeds X Y) (hX : ∀ x, X x ↔ X' x) (hY : ∀ y, Y y ↔ Y' y) : Embeds X' Y' :=
  h.mono (fun x hx ↦ (hX x).mpr hx) (fun y hy ↦ (hY y).mp hy)

lemma tag {t t' : V} (h : Embeds X Y) : Embeds (Tagged t X) (Tagged t' Y) := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨_, by unfold TagMap; definability, h.tag⟩

lemma untag {t : V} (h : Embeds X Y) : Embeds (Tagged t X) Y := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨_, by unfold UntagMap; definability, h.untag⟩

lemma tagOut {t : V} (h : Embeds X Y) : Embeds X (Tagged t Y) := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨_, by unfold TagOutMap; definability, h.tagOut⟩

lemma family {N : V} {F : V → V → V → Prop} (hF : 𝚺ᴬ₀.DefinableRel₃ F) {X Y : V → V → Prop}
    (h : ∀ r < N, IsInj (F r) (X r) (Y r)) : Embeds (Family N X) (Family N Y) :=
  ⟨_, by unfold FamilyMap; definability, IsInj.family h⟩

/-- An injection of `D` into `T` gives one of $[0, N)$ into $[0, N')$, along a functional
encoding `E` of `D` and an injective encoding `E'` of `T` in $[0, N')$, provided every number below
`N` that encodes no element of `D` is below `N'` and encodes no element of `T`. -/
lemma extend {D T : V → Prop} {E E' : V → V → Prop} {N N' c c' : V}
    (hD : 𝚺ᴬ₀.DefinablePred D) (hE : 𝚺ᴬ₀.DefinableRel E) (hE' : 𝚺ᴬ₀.DefinableRel E')
    (h : Embeds D T) (hc : ∀ u, D u → u < c) (hc' : ∀ t, T t → t < c')
    (hfun : ∀ u v v', D u → E u v → E u v' → v = v') (henc' : IsInj E' T (· < N'))
    (hcover : ∀ v < N, (∀ u, D u → ¬E u v) → v < N' ∧ ∀ t, T t → ¬E' t v) :
    Embeds (· < N) (· < N') := by
  obtain ⟨F, hF, hFinj⟩ := h
  use fun v w ↦ ((∀ u < c, D u → ¬E u v) ∧ w = v) ∨
    ∃ u < c, D u ∧ E u v ∧ ∃ t < c', F u t ∧ E' t w
  and_intros
  · definability
  · intro v hv
    by_cases hex : ∃ u, D u ∧ E u v
    · obtain ⟨u, hu, huv⟩ := hex
      obtain ⟨t, ht⟩ := hFinj.1 u hu
      have hT' := hFinj.2.1 u t hu ht
      obtain ⟨w, hw⟩ := henc'.1 t hT'
      use w
      exact Or.inr ⟨u, hc u hu, hu, huv, t, hc' t hT', ht, hw⟩
    · push Not at hex
      use v
      exact Or.inl ⟨fun u _ hu ↦ hex u hu, rfl⟩
  · rintro v w hv (⟨hnot, rfl⟩ | ⟨u, -, hu, -, t, -, ht, hw⟩)
    · exact (hcover w hv fun u hu ↦ hnot u (hc u hu) hu).1
    · exact henc'.2.1 t w (hFinj.2.1 u t hu ht) hw
  · rintro v v' w hv hv' (⟨hnot, rfl⟩ | ⟨u, -, hu, huv, t, -, ht, hw⟩)
      (⟨hnot', hw'⟩ | ⟨u', -, hu', huv', t', -, ht', hw'⟩)
    · exact hw'
    · exact absurd hw' <| (hcover w hv fun u hu ↦ hnot u (hc u hu) hu).2 t'
        (hFinj.2.1 u' t' hu' ht')
    · subst hw'
      exact absurd hw <| (hcover w hv' fun u hu ↦ hnot' u (hc u hu) hu).2 t
        (hFinj.2.1 u t hu ht)
    · obtain rfl := henc'.2.2 t t' w (hFinj.2.1 u t hu ht) (hFinj.2.1 u' t' hu' ht') hw hw'
      obtain rfl := hFinj.2.2 u u' t hu hu' ht ht'
      exact hfun u v v' hu huv huv'

end Embeds

lemma definable_tagged {t : V} {X : V → Prop} (hX : 𝚺ᴬ₀.DefinablePred X) :
    𝚺ᴬ₀.DefinablePred (Tagged t X) := by
  unfold Tagged
  definability

end Injection

section PigeonholeIOpen

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] {m : ℕ} [Fact (1 ≤ m)] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺m]

section

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma exists_set_of_definableRel {R : V → V → Prop} (hR : 𝚺ᴬ_[m].DefinableRel R) (a b : V) :
    ∃ w : V, ∀ x < a, ∀ y < b, ⟪x, y⟫ ∈ w ↔ R x y := by
  have hp : 𝚺ᴬ_[m].DefinableRel₃ fun z x y : V ↦ z = ⟪x, y⟫ :=
    (show 𝚺ᴬ₀.DefinableRel₃ fun z x y : V ↦ z = ⟪x, y⟫ by definability).of_zero
  have : 𝚺ᴬ_[m]-Predicate fun z : V ↦ ∃ x < a, ∃ y < b, z = ⟪x, y⟫ ∧ R x y := by
    apply Bounding.HierarchySymbol.Definable.arithmetic_bexs_blt (by definability)
    apply Bounding.HierarchySymbol.Definable.arithmetic_bexs_blt (by definability)
    apply Bounding.HierarchySymbol.Definable.and
    · simpa using Bounding.HierarchySymbol.Definable.arithmetic_bounded_comp₃
        (R := fun z x y : V ↦ z = ⟪x, y⟫)
        (by definability) (by definability) (by definability)
    · simpa using Bounding.HierarchySymbol.Definable.arithmetic_bounded_comp₂ (R := R)
        (by definability) (by definability)
  obtain ⟨w, hw, H⟩ := finset_comprehension this ⟪a, b⟫
  use w
  intro x hx y hy
  rw [H _ (pair_lt_pair hx hy)]
  simp [pair_ext_iff]
  grind

private def IsInjection (a w : V) : Prop :=
  (∀ x < a + 1, ∃ y < a, ⟪x, y⟫ ∈ w) ∧
  ∀ x < a + 1, ∀ x' < a + 1, ∀ y < a, ⟪x, y⟫ ∈ w → ⟪x', y⟫ ∈ w → x = x'

private lemma exists_isInjection_of_succ {a w : V} (h : IsInjection (a + 1) w) :
    ∃ w', IsInjection a w' := by
  have : Fact (1 ≤ 1) := ⟨le_rfl⟩
  obtain ⟨w', hw'⟩ := exists_set_of_definableRel (m := 1)
    (R := fun x y ↦ ⟪x, y⟫ ∈ w ∨ (⟪x, a⟫ ∈ w ∧ ⟪a + 1, y⟫ ∈ w)) (by definability) (a + 1) a
  obtain ⟨hT, hI⟩ := h
  use w'
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hT x (by simp [lt_succ_iff_le, hx.le])
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hy) with hy | hya
    · use y
      and_intros
      · exact hy
      · exact (hw' x hx y hy).2 (Or.inl hxy)
    · rw [hya] at hxy
      obtain ⟨y', hy', hxy'⟩ := hT (a + 1) (by simp)
      have hne : y' ≠ a := by
        intro hyy
        rw [hyy] at hxy'
        have := hI x (by simp [lt_succ_iff_le, hx.le]) (a + 1) (by simp) a (by simp) hxy hxy'
        exact this.not_lt hx
      have hy'' : y' < a := lt_of_le_of_ne (lt_succ_iff_le.mp hy') hne
      use y'
      and_intros
      · exact hy''
      · exact (hw' x hx y' hy'').2 (Or.inr ⟨hxy, hxy'⟩)
  · intro x hx x' hx' y hy h h'
    rw [hw' x hx y hy] at h
    rw [hw' x' hx' y hy] at h'
    have hx₁ : x < a + 1 + 1 := by simp [lt_succ_iff_le, hx.le]
    have hx₁' : x' < a + 1 + 1 := by simp [lt_succ_iff_le, hx'.le]
    have hy₁ : y < a + 1 := by simp [lt_succ_iff_le, hy.le]
    have ha₁ : a < a + 1 := by simp
    have ha₂ : a + 1 < a + 1 + 1 := by simp
    rcases h with h | ⟨h₁, h₂⟩ <;> rcases h' with h' | ⟨h₁', h₂'⟩
    · exact hI x hx₁ x' hx₁' y hy₁ h h'
    · exact absurd (hI x hx₁ (a + 1) ha₂ y hy₁ h h₂') hx.ne
    · exact absurd (hI x' hx₁' (a + 1) ha₂ y hy₁ h' h₂) hx'.ne
    · exact hI x hx₁ x' hx₁' a ha₁ h₁ h₁'

private lemma not_isInjection (a w : V) : ¬IsInjection a w := by
  suffices ∀ a : V, ∀ w, ¬IsInjection a w from this a w
  intro a
  induction a using ISigma1.pi1_succ_induction
  · unfold IsInjection
    definability
  case zero =>
    intro w h
    obtain ⟨y, hy, _⟩ := h.1 0 (by simp)
    simp at hy
  case succ a ih =>
    intro w h
    obtain ⟨w', h'⟩ := exists_isInjection_of_succ h
    exact ih w' h'

end

/-- A $\Sigma_m$-definable relation giving every `x < a + 1` some value below `a` gives two of
them a common value.
- [HP98, Theorem I.1.41] -/
theorem pigeonhole {R : V → V → Prop} (hR : 𝚺ᴬ_[m].DefinableRel R) (a : V)
    (total : ∀ x < a + 1, ∃ y < a, R x y) :
    ∃ x < a + 1, ∃ x' < a + 1, ∃ y < a, x ≠ x' ∧ R x y ∧ R x' y := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
  by_contra hne
  obtain ⟨w, hw⟩ := exists_set_of_definableRel hR (a + 1) a
  apply not_isInjection a w
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := total x hx
    use y
    and_intros
    · exact hy
    · exact (hw x hx y hy).2 hxy
  · intro x hx x' hx' y hy h h'
    by_contra hxx
    apply hne
    use x
    and_intros
    · exact hx
    · use x'
      and_intros
      · exact hx'
      · use y
        and_intros
        · exact hy
        · exact hxx
        · exact (hw x hx y hy).1 h
        · exact (hw x' hx' y hy).1 h'

end PigeonholeIOpen

section CodedPigeonhole

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

attribute [local instance] ElementaryArithmetic.models_ISigma0_union_Omega1

section

variable {a : V}

lemma pigeonhole_induction {I : V} (hI : ‖I‖ = a + 1) :
    ∀ x ≤ a, ∀ S < I ⨳ a, ¬((∀ j ≤ x, Nuon.ext a S j < x) ∧
      ∀ j ≤ x, ∀ j' ≤ x, Nuon.ext a S j = Nuon.ext a S j' → j = j') := by
  intro x
  induction x using ISigma0.succ_induction
  · definability
  case zero =>
    intro _ S _ h
    have := h.1 0 (by simp)
    simp at this
  case succ x IH =>
    intro hx S hS h
    obtain ⟨hlt, hinj⟩ := h
    have hle : ∀ m ≤ x, m ≤ x + 1 := fun m hm => le_trans hm le_self_add
    have hxa : x ≤ a := le_trans le_self_add hx
    by_cases hc : ∃ j ≤ x + 1, Nuon.ext a S j = x
    · have hxI : x + 1 < ‖I‖ := by rw [hI]; exact lt_succ_iff_le.mpr hx
      have hxx1 : ¬(x + 1 ≤ x) := not_le.mpr (lt_succ_iff_le.mpr le_rfl)
      obtain ⟨j, hjx, hej⟩ := hc
      have hjI : j < ‖I‖ := lt_of_le_of_lt hjx hxI
      obtain ⟨S', hS', e₁, -, e₃⟩ := exists_swap hS hjI hxI
      have hmx : ∀ m ≤ x, m ≠ j → Nuon.ext a S' m = Nuon.ext a S m := fun m hm hmj =>
        e₃ m (le_trans (hle m hm) (le_of_lt hxI)) hmj (fun h => hxx1 (h ▸ hm))
      have hlt' : ∀ m ≤ x, Nuon.ext a S' m < x := by
        intro m hm
        obtain h | hmj := eq_or_ne m j
        · have hne : Nuon.ext a S (x + 1) ≠ x := fun h' => by
            have hx1j : x + 1 = j := hinj (x + 1) le_rfl j hjx (h'.trans hej.symm)
            exact hxx1 (by rw [hx1j, ← h]; exact hm)
          rw [h, e₁]
          exact lt_of_le_of_ne (lt_succ_iff_le.mp (hlt (x + 1) le_rfl)) hne
        · rw [hmx m hm hmj]
          exact lt_of_le_of_ne (lt_succ_iff_le.mp (hlt m (hle m hm)))
            (fun h' => hmj (hinj m (hle m hm) j hjx (h'.trans hej.symm)))
      have hinj' : ∀ m ≤ x, ∀ m' ≤ x, Nuon.ext a S' m = Nuon.ext a S' m' → m = m' := by
        intro m hm m' hm' heq
        obtain h | hmj := eq_or_ne m j
        · obtain h' | hm'j := eq_or_ne m' j
          · exact h.trans h'.symm
          · rw [h, e₁, hmx m' hm' hm'j] at heq
            have hx1 : x + 1 = m' := hinj (x + 1) le_rfl m' (hle m' hm') heq
            exact absurd (by rw [hx1]; exact hm') hxx1
        · obtain h' | hm'j := eq_or_ne m' j
          · rw [h', e₁, hmx m hm hmj] at heq
            have hx1 : m = x + 1 := hinj m (hle m hm) (x + 1) le_rfl heq
            exact absurd (by rw [← hx1]; exact hm) hxx1
          · rw [hmx m hm hmj, hmx m' hm' hm'j] at heq
            exact hinj m (hle m hm) m' (hle m' hm') heq
      exact IH hxa S' hS' ⟨hlt', hinj'⟩
    · have hlt' : ∀ l ≤ x, Nuon.ext a S l < x := fun l hl => by
        have hne : Nuon.ext a S l ≠ x := fun h => hc ⟨l, hle l hl, h⟩
        exact lt_of_le_of_ne (lt_succ_iff_le.mp (hlt l (hle l hl))) hne
      exact IH hxa S hS ⟨hlt', fun l hl l' hl' heq => hinj l (hle l hl) l' (hle l' hl') heq⟩

/-- For $x \le a$, no block-coded sequence of width $\|a\|$ of length $x + 1$ has pairwise distinct
entries below $x$.
- [HP98, Theorem I.1.41(2)]
- [Sla04, Lemma 2.3]
-/
theorem no_coded_injection (a x S : V) (hx : x ≤ a)
    (hlt : ∀ j ≤ x, Nuon.ext a S j < x)
    (hinj : ∀ j ≤ x, ∀ j' ≤ x, Nuon.ext a S j = Nuon.ext a S j' → j = j') : False := by
  obtain ⟨I, hI⟩ := ElementaryArithmetic.exponential_total a
  have hIlen : ‖I‖ = a + 1 := hI.length_eq
  have hxI : x < ‖I‖ := by rw [hIlen]; exact lt_succ_iff_le.mpr hx
  have htr : ∀ j ≤ x, Nuon.ext a (S % (I ⨳ a)) j = Nuon.ext a S j := fun j hj =>
    ext_mod_smash (lt_of_le_of_lt hj hxI)
  exact pigeonhole_induction hIlen x hx (S % (I ⨳ a)) (mod_lt S (smash_pos I a))
    ⟨fun j hj => by rw [htr j hj]; exact hlt j hj,
     fun j hj j' hj' heq => hinj j hj j' hj' ((htr j hj).symm.trans (heq.trans (htr j' hj')))⟩

end

end

end CodedPigeonhole

end FFL.FirstOrder.Arithmetic
