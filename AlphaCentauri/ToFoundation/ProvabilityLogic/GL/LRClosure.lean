module

public import Foundation.ProvabilityLogic.GL.Basic

/-!
# The LR-closure is finite up to $\mathbf{GL}$-equivalence
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Formula Kripke Kripke.Model Kripke.Model.World

universe u

variable {α : Type u}

namespace Logic.GL

variable {A B : Formula α}

lemma of_forces
    (h : ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsFiniteGL] (x : M.World), x ⊩ A) :
    𝐆𝐋 ⊢ A :=
  iff_valid_finite.mpr fun M _ x ↦ h M x

lemma forces {κ : Type*} [Nonempty κ] {M : Model κ α} [M.IsGL] (h : 𝐆𝐋 ⊢ A) (x : M.World) :
    x ⊩ A :=
  sound M h x

end Logic.GL

namespace Kripke.Model.World

variable [DecidableEq α] {κ : Type*} [Nonempty κ] {M : Model κ α}
  {a : α} {x : M.World} {D E : Formula α}

/-- A formula and its instance substituting `⊥` for `a` agree at a world where `a` fails at the
world and above it. -/
lemma forces_subst_bot_iff [IsTrans _ M.Rel] (h : ∀ y, x = y ∨ x ≺ y → ¬M y a) : x ⊩ D ↔ x ⊩ D⟦a ↦ ⊥⟧ := by
  induction D generalizing x with
  | atom b =>
    by_cases hb : b = a
    · subst hb
      simpa using h x (.inl rfl)
    · simp [hb]
  | falsum => rfl
  | imp D E ihD ihE => exact imp_congr (ihD h) (ihE h)
  | box D ih =>
    refine forall_congr' fun y ↦ imp_congr_right fun Rxy ↦ ih fun z hz ↦ h z (.inr ?_)
    rcases hz with rfl | Ryz
    · exact Rxy
    · exact IsTrans.trans _ _ _ Rxy Ryz

omit [DecidableEq α] in
private lemma forces_box_neg_and_box_of [M.IsGL]
    (hDE : ∀ y : M.World, (∀ z, y = z ∨ y ≺ z → ¬M z a) → (y ⊩ D ↔ y ⊩ E))
    (hx : x ⊩ □(∼(#a ⋏ □D))) : x ⊩ □(∼(#a ⋏ □E)) := by
  intro y Rxy hy
  obtain ⟨hya, hyE⟩ := forces_and.mp hy
  have hn : ∀ z, y ≺ z → ¬M z a := by
    intro z Ryz hz
    obtain ⟨t, ⟨Ryt, ht⟩, tmax⟩ := M.terminalOf {t | y ≺ t ∧ M t a} ⟨z, Ryz, hz⟩
    obtain ⟨u, Rtu, hu⟩ := not_forces_box.mp fun h ↦
      hx t (IsTrans.trans _ _ _ Rxy Ryt) (forces_and.mpr ⟨ht, h⟩)
    apply hu
    apply (hDE u _).mpr (hyE u (IsTrans.trans _ _ _ Ryt Rtu))
    intro v huv hv
    rcases huv with rfl | Ruv
    · exact tmax u ⟨IsTrans.trans _ _ _ Ryt Rtu, hv⟩ Rtu
    · exact tmax v ⟨IsTrans.trans _ _ _ (IsTrans.trans _ _ _ Ryt Rtu) Ruv, hv⟩
        (IsTrans.trans _ _ _ Rtu Ruv)
  apply hx y Rxy (forces_and.mpr ⟨hya, fun z Ryz ↦ (hDE z ?_).mpr (hyE z Ryz)⟩)
  rintro w (rfl | Rzw)
  · exact hn _ Ryz
  · exact hn w (IsTrans.trans _ _ _ Ryz Rzw)

end Kripke.Model.World

namespace Logic.GL

variable [DecidableEq α] {a : α} {D : Formula α}

/-- - [Ign91, Lemma 6.3] -/
lemma box_neg_and_box_iff_subst_bot : 𝐆𝐋 ⊢ □(∼(#a ⋏ □D)) 🡘 □(∼(#a ⋏ □D⟦a ↦ ⊥⟧)) := by
  apply of_forces
  intro κ _ M _ x
  have h (y : M.World) (hy : ∀ z, y = z ∨ y ≺ z → ¬M z a) : y ⊩ D ↔ y ⊩ D⟦a ↦ ⊥⟧ :=
    forces_subst_bot_iff hy
  exact forces_iff.mpr ⟨forces_box_neg_and_box_of h, forces_box_neg_and_box_of fun y hy ↦ (h y hy).symm⟩

end Logic.GL

namespace Logic.GL

variable {A B C D : Formula α}

lemma iff_of_forces
    (h : ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsFiniteGL] (x : M.World),
      x ⊩ A ↔ x ⊩ B) :
    𝐆𝐋 ⊢ A 🡘 B :=
  of_forces fun M _ x ↦ forces_iff.mpr (h M x)

lemma forces_iff_of {κ : Type*} [Nonempty κ] {M : Model κ α} [M.IsGL] (h : 𝐆𝐋 ⊢ A 🡘 B)
    (x : M.World) : x ⊩ A ↔ x ⊩ B :=
  forces_iff.mp (forces h x)

lemma iff_refl' : 𝐆𝐋 ⊢ A 🡘 A := iff_of_forces fun _ _ _ ↦ Iff.rfl

lemma iff_trans' (h₁ : 𝐆𝐋 ⊢ A 🡘 B) (h₂ : 𝐆𝐋 ⊢ B 🡘 C) : 𝐆𝐋 ⊢ A 🡘 C :=
  iff_of_forces fun _ _ x ↦ (forces_iff_of h₁ x).trans (forces_iff_of h₂ x)

lemma imp_congr' (h₁ : 𝐆𝐋 ⊢ A 🡘 B) (h₂ : 𝐆𝐋 ⊢ C 🡘 D) : 𝐆𝐋 ⊢ (A 🡒 C) 🡘 (B 🡒 D) :=
  iff_of_forces fun _ _ x ↦ imp_congr (forces_iff_of h₁ x) (forces_iff_of h₂ x)

lemma box_congr' (h : 𝐆𝐋 ⊢ A 🡘 B) : 𝐆𝐋 ⊢ □A 🡘 □B :=
  iff_of_forces fun _ _ _ ↦ forall_congr' fun y ↦ imp_congr_right fun _ ↦ forces_iff_of h y

/-- Every formula in `S` is $\mathbf{GL}$-equivalent to one in some finite set. -/
def FiniteUpToEquiv (S : Set (Formula α)) : Prop :=
  ∃ F : Finset (Formula α), ∀ A ∈ S, ∃ B ∈ F, 𝐆𝐋 ⊢ A 🡘 B

namespace FiniteUpToEquiv

variable {S T : Set (Formula α)}

lemma of_forall_exists (hT : FiniteUpToEquiv T) (h : ∀ A ∈ S, ∃ B ∈ T, 𝐆𝐋 ⊢ A 🡘 B) :
    FiniteUpToEquiv S := by
  obtain ⟨F, hF⟩ := hT
  use F
  intro A hA
  obtain ⟨B, hB, hAB⟩ := h A hA
  obtain ⟨C, hC, hBC⟩ := hF B hB
  exact ⟨C, hC, iff_trans' hAB hBC⟩

lemma of_subset (hT : FiniteUpToEquiv T) (h : S ⊆ T) : FiniteUpToEquiv S :=
  hT.of_forall_exists fun A hA ↦ ⟨A, h hA, iff_refl'⟩

lemma union (hS : FiniteUpToEquiv S) (hT : FiniteUpToEquiv T) : FiniteUpToEquiv (S ∪ T) := by
  classical
  obtain ⟨F, hF⟩ := hS
  obtain ⟨G, hG⟩ := hT
  use F ∪ G
  rintro A (hA | hA)
  · obtain ⟨B, hB, h⟩ := hF A hA
    exact ⟨B, Finset.mem_union_left _ hB, h⟩
  · obtain ⟨B, hB, h⟩ := hG A hA
    exact ⟨B, Finset.mem_union_right _ hB, h⟩

lemma iUnion_finset {ι : Type*} (I : Finset ι) {S : ι → Set (Formula α)}
    (h : ∀ i ∈ I, FiniteUpToEquiv (S i)) : FiniteUpToEquiv (⋃ i ∈ I, S i) := by
  classical
  choose F hF using h
  use I.attach.biUnion fun i ↦ F i.1 i.2
  intro A hA
  simp only [Set.mem_iUnion] at hA
  obtain ⟨i, hi, hA⟩ := hA
  obtain ⟨B, hB, h⟩ := hF i hi A hA
  exact ⟨B, Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, hB⟩, h⟩

/-- A set finite up to $\mathbf{GL}$-equivalence has representatives in itself. -/
lemma exists_finset_subset (h : FiniteUpToEquiv S) :
    ∃ F : Finset (Formula α), ↑F ⊆ S ∧ ∀ A ∈ S, ∃ B ∈ F, 𝐆𝐋 ⊢ A 🡘 B := by
  classical
  obtain ⟨F, hF⟩ := h
  let G := F.filter fun B ↦ ∃ A ∈ S, 𝐆𝐋 ⊢ A 🡘 B
  have hG {B} (hB : B ∈ G) : ∃ A ∈ S, 𝐆𝐋 ⊢ A 🡘 B := (Finset.mem_filter.mp hB).2
  use G.attach.image fun B ↦ (hG B.2).choose
  constructor
  · intro A hA
    obtain ⟨B, -, rfl⟩ := Finset.mem_image.mp hA
    exact (hG B.2).choose_spec.1
  · intro A hA
    obtain ⟨B, hB, hAB⟩ := hF A hA
    have hB' : B ∈ G := Finset.mem_filter.mpr ⟨hB, A, hA, hAB⟩
    refine ⟨(hG hB').choose, Finset.mem_image.mpr ⟨⟨B, hB'⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    exact iff_trans' hAB <| iff_of_forces fun _ _ x ↦
      (forces_iff_of (hG hB').choose_spec.2 x).symm

end FiniteUpToEquiv

end Logic.GL

/-! ### Boolean combinations -/

namespace Formula

/-- The closure of `S` under `⊥` and `🡒`. -/
inductive BooleanCombination (S : Set (Formula α)) : Formula α → Prop
  | mem {A} : A ∈ S → BooleanCombination S A
  | falsum : BooleanCombination S ⊥
  | imp {A B} : BooleanCombination S A → BooleanCombination S B → BooleanCombination S (A 🡒 B)

namespace BooleanCombination

variable {S T : Set (Formula α)} {A B : Formula α}

lemma neg (h : BooleanCombination S A) : BooleanCombination S (∼A) := imp h falsum

lemma top : BooleanCombination S ⊤ := imp falsum falsum

lemma and (hA : BooleanCombination S A) (hB : BooleanCombination S B) :
    BooleanCombination S (A ⋏ B) :=
  neg (imp hA (neg hB))

lemma or (hA : BooleanCombination S A) (hB : BooleanCombination S B) :
    BooleanCombination S (A ⋎ B) :=
  imp (neg hA) hB

lemma disj₂ : {l : List (Formula α)} → (∀ A ∈ l, BooleanCombination S A) →
    BooleanCombination S (⋁l)
  | [], _ => falsum
  | [A], h => h A (by simp)
  | A :: B :: l, h => or (h A (by simp)) (disj₂ (l := B :: l) fun C hC ↦ h C (by simp_all))

lemma disj {F : Finset (Formula α)} (h : ∀ A ∈ F, BooleanCombination S A) :
    BooleanCombination S F.disj :=
  disj₂ fun A hA ↦ h A (Finset.mem_toList.mp hA)

lemma conj₂ : {l : List (Formula α)} → (∀ A ∈ l, BooleanCombination S A) →
    BooleanCombination S (⋀l)
  | [], _ => top
  | [A], h => h A (by simp)
  | A :: B :: l, h => and (h A (by simp)) (conj₂ (l := B :: l) fun C hC ↦ h C (by simp_all))

lemma conj {F : Finset (Formula α)} (h : ∀ A ∈ F, BooleanCombination S A) :
    BooleanCombination S F.conj :=
  conj₂ fun A hA ↦ h A (Finset.mem_toList.mp hA)

open Logic.GL in
lemma exists_of_forall_exists (hST : ∀ A ∈ S, ∃ B, BooleanCombination T B ∧ 𝐆𝐋 ⊢ A 🡘 B)
    (h : BooleanCombination S A) : ∃ B, BooleanCombination T B ∧ 𝐆𝐋 ⊢ A 🡘 B := by
  induction h with
  | mem hA => exact hST _ hA
  | falsum => exact ⟨⊥, falsum, iff_refl'⟩
  | imp _ _ ihA ihB =>
    obtain ⟨A', hA', h₁⟩ := ihA
    obtain ⟨B', hB', h₂⟩ := ihB
    exact ⟨A' 🡒 B', imp hA' hB', imp_congr' h₁ h₂⟩

open Logic.GL in
/-- A Boolean combination of a finite set of formulas is $\mathbf{GL}$-equivalent to a disjunction
of the formulas fixing which members of the set hold. -/
private lemma exists_finset_powerset_of_finset [DecidableEq α] {F : Finset (Formula α)}
    (h : BooleanCombination ↑F A) :
    ∃ 𝒯 ⊆ F.powerset, 𝐆𝐋 ⊢ A 🡘
      (𝒯.image fun T ↦ T.conj ⋏ ((F \ T).image (∼·)).conj).disj := by
  classical
  have key {κ : Type u} [Nonempty κ] {M : Model κ α} (x : M.World) {𝒯 : Finset (Finset (Formula α))}
      (h𝒯 : 𝒯 ⊆ F.powerset) :
      x ⊩ (𝒯.image fun T ↦ T.conj ⋏ ((F \ T).image (∼·)).conj).disj ↔
        F.filter (fun B ↦ Forces M x B) ∈ 𝒯 := by
    rw [forces_disj]
    constructor
    · rintro ⟨C, hC, hx⟩
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨h₁, h₂⟩ := forces_and.mp hx
      convert hT
      ext B
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hB, hx⟩
        by_contra hn
        exact forces_conj.mp h₂ (∼B)
          (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨hB, hn⟩)) hx
      · intro hB
        exact ⟨Finset.mem_powerset.mp (h𝒯 hT) hB, forces_conj.mp h₁ B hB⟩
    · intro h
      refine ⟨_, Finset.mem_image_of_mem _ h, forces_and.mpr ⟨forces_conj.mpr fun B hB ↦
        (Finset.mem_filter.mp hB).2, forces_conj.mpr fun C hC ↦ ?_⟩⟩
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨hB, hn⟩ := Finset.mem_sdiff.mp hB
      exact fun hx ↦ hn (Finset.mem_filter.mpr ⟨hB, hx⟩)
  induction h with
  | @mem A hA =>
    refine ⟨F.powerset.filter (A ∈ ·), Finset.filter_subset _ _, iff_of_forces fun M _ x ↦ ?_⟩
    rw [key x (Finset.filter_subset _ _)]
    simpa [Finset.mem_filter] using fun _ ↦ hA
  | falsum =>
    exact ⟨∅, Finset.empty_subset _, iff_of_forces fun M _ x ↦ by
      rw [key x (Finset.empty_subset _)]; simp⟩
  | @imp A B _ _ ihA ihB =>
    obtain ⟨𝒜, h𝒜, hA⟩ := ihA
    obtain ⟨ℬ, hℬ, hB⟩ := ihB
    refine ⟨(F.powerset \ 𝒜) ∪ ℬ, Finset.union_subset Finset.sdiff_subset hℬ,
      iff_of_forces fun M _ x ↦ ?_⟩
    rw [key x (Finset.union_subset Finset.sdiff_subset hℬ), forces_imp,
      forces_iff_of hA x, forces_iff_of hB x, key x h𝒜, key x hℬ]
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_powerset, Finset.filter_subset,
      true_and]

open Logic.GL in
lemma finiteUpToEquiv (h : FiniteUpToEquiv S) :
    FiniteUpToEquiv {A | BooleanCombination S A} := by
  classical
  obtain ⟨F, hF⟩ := h
  refine ⟨F.powerset.powerset.image fun 𝒯 ↦
    (𝒯.image fun T ↦ T.conj ⋏ ((F \ T).image (∼·)).conj).disj, fun A hA ↦ ?_⟩
  obtain ⟨B, hB, hAB⟩ := exists_of_forall_exists (T := ↑F)
    (fun A hA ↦ (hF A hA).imp fun B hB ↦ ⟨mem hB.1, hB.2⟩) hA
  obtain ⟨𝒯, h𝒯, h⟩ := exists_finset_powerset_of_finset hB
  exact ⟨_, Finset.mem_image.mpr ⟨𝒯, Finset.mem_powerset.mpr h𝒯, rfl⟩, iff_trans' hAB h⟩

end BooleanCombination

end Formula

end FFL.ProvabilityLogic
