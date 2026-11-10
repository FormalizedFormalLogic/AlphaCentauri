module

public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Arithmetic.Definability

/-!
# Injections between sets of a model

A relation `R` is an injection of a set `X` into `Y` if it relates every element of `X` to some
element, relates elements of `X` only to elements of `Y`, and relates no two elements of `X` to the
same one. Injections compose, combine over disjoint unions, and lift to tagged copies
$\{\langle t, x \rangle : x \in X\}$ and to indexed families
$\{\langle r, x \rangle : r < R, x \in X_r\}$.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

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
  refine ⟨?_, ?_, ?_⟩
  · rintro x (hx | hx)
    · obtain ⟨y, hy⟩ := h.1 x hx
      exact ⟨y, Or.inl ⟨hx, hy⟩⟩
    · obtain ⟨y, hy⟩ := h'.1 x hx
      exact ⟨y, Or.inr ⟨hx, hy⟩⟩
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

lemma congr_rel {R' : V → V → Prop} (h : IsInj R X Y) (hR : ∀ x y, X x → (R x y ↔ R' x y)) :
    IsInj R' X Y :=
  ⟨fun x hx ↦ (h.1 x hx).imp fun y hy ↦ (hR x y hx).mp hy,
    fun x y hx hy ↦ h.2.1 x y hx ((hR x y hx).mpr hy),
    fun x x' y hx hx' hy hy' ↦ h.2.2 x x' y hx hx' ((hR x y hx).mpr hy) ((hR x' y hx').mpr hy')⟩

lemma comp [LT V] {c : V} (h : IsInj R X Y) (h' : IsInj S Y W) (hY : ∀ y, Y y → y < c) :
    IsInj (CompMap c R S) X W := by
  refine ⟨fun x hx ↦ ?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := h.1 x hx
    obtain ⟨z, hz⟩ := h'.1 y (h.2.1 x y hx hy)
    exact ⟨z, y, hY y (h.2.1 x y hx hy), hy, hz⟩
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
  refine ⟨?_, ?_, ?_⟩
  · rintro u ⟨rfl, hu⟩
    obtain ⟨y, hy⟩ := h.1 _ hu
    exact ⟨⟪t', y⟫, rfl, by simp, by simpa using hy⟩
  · rintro u v ⟨-, hu⟩ ⟨-, hv, huv⟩
    exact ⟨hv, h.2.1 _ _ hu huv⟩
  · rintro u u' v ⟨hu₁, hu⟩ ⟨hu₁', hu'⟩ ⟨-, -, huv⟩ ⟨-, -, huv'⟩
    rw [← pair_unpair u, ← pair_unpair u', hu₁, hu₁', h.2.2 _ _ _ hu hu' huv huv']

lemma family {N : V} {F : V → V → V → Prop} {X Y : V → V → Prop}
    (h : ∀ r < N, IsInj (F r) (X r) (Y r)) :
    IsInj (FamilyMap F) (Family N X) (Family N Y) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro u ⟨hr, hu⟩
    obtain ⟨y, hy⟩ := (h _ hr).1 _ hu
    exact ⟨⟪π₁ u, y⟫, by simp, by simpa using hy⟩
  · rintro u v ⟨hr, hu⟩ ⟨hv, huv⟩
    exact ⟨hv ▸ hr, hv ▸ (h _ hr).2.1 _ _ hu huv⟩
  · rintro u u' v ⟨hr, hu⟩ ⟨hr', hu'⟩ ⟨hv, huv⟩ ⟨hv', huv'⟩
    have h₁ : π₁ u = π₁ u' := hv.symm.trans hv'
    rw [h₁] at hu huv
    rw [← pair_unpair u, ← pair_unpair u', h₁, (h _ hr').2.2 _ _ _ hu hu' huv huv']

lemma untag {t : V} (h : IsInj R X Y) : IsInj (UntagMap t R) (Tagged t X) Y := by
  refine ⟨?_, ?_, ?_⟩
  · rintro u ⟨hu₁, hu⟩
    obtain ⟨y, hy⟩ := h.1 _ hu
    exact ⟨y, hu₁, hy⟩
  · rintro u v ⟨-, hu⟩ ⟨-, huv⟩
    exact h.2.1 _ _ hu huv
  · rintro u u' v ⟨hu₁, hu⟩ ⟨hu₁', hu'⟩ ⟨-, huv⟩ ⟨-, huv'⟩
    rw [← pair_unpair u, ← pair_unpair u', hu₁, hu₁', h.2.2 _ _ _ hu hu' huv huv']

lemma tagOut {t : V} (h : IsInj R X Y) : IsInj (TagOutMap t R) X (Tagged t Y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨y, hy⟩ := h.1 _ hu
    exact ⟨⟪t, y⟫, by simpa [TagOutMap] using hy⟩
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
lemma of_isInj {R : V → V → Prop} (hR : 𝚺ᴬ₀.DefinableRel R) (h : IsInj R X Y) : Embeds X Y :=
  ⟨R, hR, h⟩

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
  exact ⟨R, hR, h.mono hX hY⟩

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
  refine ⟨fun v w ↦ ((∀ u < c, D u → ¬E u v) ∧ w = v) ∨
    ∃ u < c, D u ∧ E u v ∧ ∃ t < c', F u t ∧ E' t w, by definability, ?_, ?_, ?_⟩
  · intro v hv
    by_cases hex : ∃ u, D u ∧ E u v
    · obtain ⟨u, hu, huv⟩ := hex
      obtain ⟨t, ht⟩ := hFinj.1 u hu
      have hT' := hFinj.2.1 u t hu ht
      obtain ⟨w, hw⟩ := henc'.1 t hT'
      exact ⟨w, Or.inr ⟨u, hc u hu, hu, huv, t, hc' t hT', ht, hw⟩⟩
    · push Not at hex
      exact ⟨v, Or.inl ⟨fun u _ hu ↦ hex u hu, rfl⟩⟩
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

end FFL.FirstOrder.Arithmetic
