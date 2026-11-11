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
lemma forces_subst_bot_iff [IsTrans _ M.Rel] (h : ∀ y, x = y ∨ x ≺ y → ¬M y a) :
    x ⊩ D ↔ x ⊩ D⟦a ↦ ⊥⟧ := by
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
  exact forces_iff.mpr
    ⟨forces_box_neg_and_box_of h, forces_box_neg_and_box_of fun y hy ↦ (h y hy).symm⟩

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

namespace Logic.GL.FiniteUpToEquiv

variable {S : Set (Formula α)}

lemma image {f : Formula α → Formula α} (hf : ∀ {A B}, 𝐆𝐋 ⊢ A 🡘 B → 𝐆𝐋 ⊢ f A 🡘 f B)
    (h : FiniteUpToEquiv S) : FiniteUpToEquiv (f '' S) := by
  classical
  obtain ⟨F, hF⟩ := h
  refine ⟨F.image f, ?_⟩
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨B, hB, h⟩ := hF A hA
  exact ⟨f B, Finset.mem_image_of_mem _ hB, hf h⟩

end Logic.GL.FiniteUpToEquiv

/-! ### The LR-closure -/

/-- The LR-closure of a finite set `P` of atoms. `LRClosure P true` contains `⊥` and the atoms in
`P` and is closed under `A ↦ A ⋏ □∼B` for `B` in either part; `LRClosure P false` contains
`A ⋏ □(B 🡒 ⋁S ⋎ ⋁◇T)` for `A` in either part and `B` and the members of `S` and `T` in
`LRClosure P true`.

- [Ign91, Definition 6.2]
-/
inductive LRClosure [DecidableEq α] (P : Finset α) : Bool → Formula α → Prop
  | falsum : LRClosure P true ⊥
  | atom {a : α} : a ∈ P → LRClosure P true #a
  | and_box_neg {A B : Formula α} {b : Bool} :
      LRClosure P true A → LRClosure P b B → LRClosure P true (A ⋏ □(∼B))
  | and_box_imp {A B : Formula α} {b : Bool} {S T : Finset (Formula α)} :
      LRClosure P b A → LRClosure P true B → (∀ C ∈ S, LRClosure P true C) →
        (∀ C ∈ T, LRClosure P true C) →
        LRClosure P false (A ⋏ □(B 🡒 S.disj ⋎ (T.image (◇·)).disj))

namespace LRClosure

open Logic.GL Formula.BooleanCombination

variable [DecidableEq α] {P : Finset α} {b : Bool} {A B Z : Formula α}

/-- The members of the LR-closure and the formulas `□∼A` for `A` in its first part. -/
def base (P : Finset α) : Set (Formula α) :=
  {A | ∃ b, LRClosure P b A} ∪ (fun A ↦ □(∼A)) '' {A | LRClosure P true A}

/-- Every member of the LR-closure is equivalent to `⊥` or to `#a ⋏ □D` for an atom `a ∈ P` and a
Boolean combination `D` of `base P`. -/
lemma exists_atom_and_box (h : LRClosure P b Z) :
    (𝐆𝐋 ⊢ Z 🡘 ⊥) ∨
      ∃ a ∈ P, ∃ D, BooleanCombination (base P) D ∧ 𝐆𝐋 ⊢ Z 🡘 #a ⋏ □D := by
  induction h with
  | falsum => exact .inl iff_refl'
  | @atom a ha =>
    refine .inr ⟨a, ha, ⊤, top, iff_of_forces fun _ _ x ↦ ?_⟩
    simp [forces_and, forces_box]
  | @and_box_neg A B b' _ hB ih _ =>
    rcases ih with h | ⟨a, ha, D, hD, h⟩
    · refine .inl <| iff_of_forces fun _ _ x ↦ ?_
      simp [forces_and, forces_iff_of h x]
    · refine .inr ⟨a, ha, D ⋏ ∼B, and hD (neg (mem (.inl ⟨b', hB⟩))), iff_of_forces fun _ _ x ↦ ?_⟩
      simp only [forces_and, forces_iff_of h x, forces_box]
      grind
  | @and_box_imp A B b' S T _ hB hS hT ih _ _ _ =>
    have hE : BooleanCombination (base P) (B 🡒 S.disj ⋎ (T.image (◇·)).disj) := by
      refine imp (mem (.inl ⟨true, hB⟩)) (or (disj fun C hC ↦ mem (.inl ⟨true, hS C hC⟩)) ?_)
      refine disj fun C hC ↦ ?_
      obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
      exact neg (mem (.inr ⟨D, hT D hD, rfl⟩))
    rcases ih with h | ⟨a, ha, D, hD, h⟩
    · refine .inl <| iff_of_forces fun _ _ x ↦ ?_
      simp [forces_and, forces_iff_of h x]
    · refine .inr ⟨a, ha, _, and hD hE, iff_of_forces fun _ _ x ↦ ?_⟩
      simp only [forces_and, forces_iff_of h x, forces_box]
      grind

private lemma forces_subst_disj {κ : Type*} [Nonempty κ] {M : Model κ α} {x : M.World}
    {s : Substitution α α} {S : Finset (Formula α)} :
    x ⊩[M] S.disj⟦s⟧ ↔ ∃ C ∈ S, x ⊩[M] C⟦s⟧ := by
  rw [← Model.forces_subst, forces_disj]
  simp only [Model.forces_subst]

/-- Substituting `⊥` for an atom maps the LR-closure of `P` into that of `P.erase a`, up to
equivalence. -/
lemma exists_subst_bot (a : α) (h : LRClosure P b Z) :
    ∃ Z', LRClosure (P.erase a) b Z' ∧ 𝐆𝐋 ⊢ Z⟦a ↦ ⊥⟧ 🡘 Z' := by
  induction h with
  | falsum => exact ⟨⊥, falsum, iff_refl'⟩
  | @atom c hc =>
    by_cases hca : c = a
    · subst hca
      exact ⟨⊥, falsum, by simp⟩
    · exact ⟨#c, atom (Finset.mem_erase.mpr ⟨hca, hc⟩), by simp [hca]⟩
  | and_box_neg _ _ ihA ihB =>
    obtain ⟨A', hA', h₁⟩ := ihA
    obtain ⟨B', hB', h₂⟩ := ihB
    refine ⟨_, and_box_neg hA' hB', iff_of_forces fun _ _ x ↦ ?_⟩
    simp only [subst_and, subst_box, subst_neg, forces_and, forces_iff_of h₁ x, forces_box,
      forces_neg]
    exact and_congr_right fun _ ↦ forall_congr' fun y ↦ imp_congr_right fun _ ↦
      not_congr (forces_iff_of h₂ y)
  | @and_box_imp A B b' S T _ _ _ _ ihA ihB ihS ihT =>
    obtain ⟨A', hA', h₁⟩ := ihA
    obtain ⟨B', hB', h₂⟩ := ihB
    choose f hf hf' using ihS
    choose g hg hg' using ihT
    refine ⟨_, and_box_imp (S := S.attach.image fun C ↦ f C.1 C.2)
      (T := T.attach.image fun C ↦ g C.1 C.2) hA' hB' ?_ ?_, iff_of_forces fun _ _ x ↦ ?_⟩
    · intro C hC
      obtain ⟨⟨D, hD⟩, -, rfl⟩ := Finset.mem_image.mp hC
      exact hf D hD
    · intro C hC
      obtain ⟨⟨D, hD⟩, -, rfl⟩ := Finset.mem_image.mp hC
      exact hg D hD
    simp only [subst_and, subst_box, subst_imp, subst_or, forces_and, forces_iff_of h₁ x,
      forces_box, forces_imp, forces_or, forces_subst_disj, forces_disj]
    refine and_congr_right fun _ ↦ forall_congr' fun y ↦ imp_congr_right fun _ ↦ ?_
    rw [forces_iff_of h₂ y]
    apply or_congr_right
    apply or_congr
    · constructor
      · rintro ⟨C, hC, hy⟩
        exact ⟨f C hC, Finset.mem_image.mpr ⟨⟨C, hC⟩, Finset.mem_attach _ _, rfl⟩,
          (forces_iff_of (hf' C hC) y).mp hy⟩
      · rintro ⟨_, hC, hy⟩
        obtain ⟨⟨D, hD⟩, -, rfl⟩ := Finset.mem_image.mp hC
        exact ⟨D, hD, (forces_iff_of (hf' D hD) y).mpr hy⟩
    · simp only [Finset.mem_image, exists_exists_and_eq_and, subst_dia, forces_dia]
      constructor
      · rintro ⟨C, hC, z, Ryz, hz⟩
        exact ⟨⟨C, hC⟩, Finset.mem_attach _ _, z, Ryz, (forces_iff_of (hg' C hC) z).mp hz⟩
      · rintro ⟨⟨C, hC⟩, -, z, Ryz, hz⟩
        exact ⟨C, hC, z, Ryz, (forces_iff_of (hg' C hC) z).mpr hz⟩

lemma exists_subst_bot_of_mem_base (a : α) (h : A ∈ base P) :
    ∃ A' ∈ base (P.erase a), 𝐆𝐋 ⊢ A⟦a ↦ ⊥⟧ 🡘 A' := by
  rcases h with ⟨b, h⟩ | ⟨A, h, rfl⟩
  · obtain ⟨A', hA', h⟩ := exists_subst_bot a h
    exact ⟨A', .inl ⟨b, hA'⟩, h⟩
  · obtain ⟨A', hA', h⟩ := exists_subst_bot a h
    exact ⟨□(∼A'), .inr ⟨A', hA', rfl⟩, box_congr' (imp_congr' h iff_refl')⟩

lemma exists_subst_bot_of_booleanCombination (a : α) {D : Formula α}
    (h : BooleanCombination (base P) D) :
    ∃ D', BooleanCombination (base (P.erase a)) D' ∧ 𝐆𝐋 ⊢ D⟦a ↦ ⊥⟧ 🡘 D' := by
  induction h with
  | mem hA =>
    obtain ⟨A', hA', h⟩ := exists_subst_bot_of_mem_base a hA
    exact ⟨A', mem hA', h⟩
  | falsum => exact ⟨⊥, BooleanCombination.falsum, iff_refl'⟩
  | imp _ _ ihA ihB =>
    obtain ⟨A', hA', h₁⟩ := ihA
    obtain ⟨B', hB', h₂⟩ := ihB
    exact ⟨A' 🡒 B', imp hA' hB', imp_congr' h₁ h₂⟩

/-- The formulas `□∼A` for `A` in the LR-closure are finitely many up to equivalence, provided the
bases over `P.erase a` are. -/
private lemma finiteUpToEquiv_box_neg
    (ih : ∀ a ∈ P, FiniteUpToEquiv (base (P.erase a))) :
    FiniteUpToEquiv ((fun A ↦ □(∼A)) '' {A | ∃ b, LRClosure P b A}) := by
  have hfin : FiniteUpToEquiv ({□(∼⊥)} ∪ ⋃ a ∈ P,
      (fun D ↦ □(∼(#a ⋏ □D))) '' {D | BooleanCombination (base (P.erase a)) D}) := by
    refine FiniteUpToEquiv.union ⟨{□(∼⊥)}, fun A hA ↦ ⟨A, by simpa using hA, iff_refl'⟩⟩ ?_
    refine FiniteUpToEquiv.iUnion_finset P fun a ha ↦ ?_
    refine (BooleanCombination.finiteUpToEquiv (ih a ha)).image fun h ↦ ?_
    exact box_congr' <| imp_congr' (iff_of_forces fun _ _ x ↦ by
      simp only [forces_and, forces_box]
      exact and_congr_right fun _ ↦ forall_congr' fun y ↦ imp_congr_right fun _ ↦
        forces_iff_of h y) iff_refl'
  refine hfin.of_forall_exists ?_
  rintro _ ⟨Z, ⟨b, hZ⟩, rfl⟩
  rcases exists_atom_and_box hZ with h | ⟨a, ha, D, hD, h⟩
  · exact ⟨□(∼⊥), .inl rfl, box_congr' (imp_congr' h iff_refl')⟩
  · obtain ⟨D', hD', h'⟩ := exists_subst_bot_of_booleanCombination a hD
    refine ⟨□(∼(#a ⋏ □D')), .inr ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_image]
      exact ⟨a, ha, D', hD', rfl⟩
    refine iff_trans' (box_congr' (imp_congr' h iff_refl')) <|
      iff_trans' box_neg_and_box_iff_subst_bot <| box_congr' <| imp_congr' ?_ iff_refl'
    exact iff_of_forces fun _ _ x ↦ by
      simp only [forces_and, forces_box]
      exact and_congr_right fun _ ↦ forall_congr' fun y ↦ imp_congr_right fun _ ↦
        forces_iff_of h' y

/-- - [Ign91, Lemma 6.3] -/
theorem finiteUpToEquiv_base (P : Finset α) : FiniteUpToEquiv (base P) := by
  classical
  induction P using Finset.strongInduction with
  | H P ih =>
  obtain ⟨F, hF⟩ := finiteUpToEquiv_box_neg fun a ha ↦ ih _ (Finset.erase_ssubset ha)
  have hL : ∀ {b Z}, LRClosure P b Z → b = true →
      ∃ B ∈ insert ⊥ (P.biUnion fun a ↦ F.powerset.image fun X ↦ #a ⋏ X.conj), 𝐆𝐋 ⊢ Z 🡘 B := by
    intro b Z h
    induction h with
    | falsum => exact fun _ ↦ ⟨⊥, Finset.mem_insert_self _ _, iff_refl'⟩
    | @atom a ha =>
      refine fun _ ↦ ⟨#a ⋏ (∅ : Finset (Formula α)).conj, Finset.mem_insert_of_mem <|
        Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨∅, by simp, rfl⟩⟩,
        iff_of_forces fun _ _ x ↦ ?_⟩
      simp [forces_and]
    | @and_box_neg A B b' _ hB ihA _ =>
      intro _
      obtain ⟨E, hE, hBE⟩ := hF _ ⟨B, ⟨b', hB⟩, rfl⟩
      obtain ⟨A', hA', hAA'⟩ := ihA rfl
      rcases Finset.mem_insert.mp hA' with rfl | hA'
      · refine ⟨⊥, Finset.mem_insert_self _ _, iff_of_forces fun _ _ x ↦ ?_⟩
        simp [forces_and, forces_iff_of hAA' x]
      · obtain ⟨a, ha, hX⟩ := Finset.mem_biUnion.mp hA'
        obtain ⟨X, hX', rfl⟩ := Finset.mem_image.mp hX
        refine ⟨#a ⋏ (insert E X).conj, Finset.mem_insert_of_mem <| Finset.mem_biUnion.mpr
          ⟨a, ha, Finset.mem_image.mpr ⟨insert E X, Finset.mem_powerset.mpr <|
            Finset.insert_subset hE (Finset.mem_powerset.mp hX'), rfl⟩⟩,
          iff_of_forces fun _ _ x ↦ ?_⟩
        simp only [forces_and, forces_iff_of hAA' x, forces_conj, Finset.mem_insert,
          forall_eq_or_imp, ← forces_iff_of hBE x]
        tauto
    | and_box_imp => exact fun h ↦ Bool.noConfusion h
  obtain ⟨G, hGsub, hG⟩ := FiniteUpToEquiv.exists_finset_subset
    (S := {Z | LRClosure P true Z}) ⟨_, fun Z hZ ↦ hL hZ rfl⟩
  let H := (G ×ˢ (G.powerset ×ˢ G.powerset)).image fun p ↦
    □(p.1 🡒 p.2.1.disj ⋎ (p.2.2.image (◇·)).disj)
  have hR : ∀ {b Z}, LRClosure P b Z → b = false →
      ∃ l ∈ G, ∃ Y ⊆ H, 𝐆𝐋 ⊢ Z 🡘 l ⋏ Y.conj := by
    intro b Z h
    induction h with
    | falsum | atom | and_box_neg => exact fun h ↦ Bool.noConfusion h
    | @and_box_imp A B b' S T hA hB hS hT ihA _ _ _ =>
      intro _
      obtain ⟨B', hB', hBB'⟩ := hG B hB
      choose f hf hf' using fun C (hC : C ∈ S) ↦ hG C (hS C hC)
      choose g hg hg' using fun C (hC : C ∈ T) ↦ hG C (hT C hC)
      let S' := S.attach.image fun C ↦ f C.1 C.2
      let T' := T.attach.image fun C ↦ g C.1 C.2
      have hS' : S' ⊆ G := by
        intro C hC
        obtain ⟨⟨D, hD⟩, -, rfl⟩ := Finset.mem_image.mp hC
        exact hf D hD
      have hT' : T' ⊆ G := by
        intro C hC
        obtain ⟨⟨D, hD⟩, -, rfl⟩ := Finset.mem_image.mp hC
        exact hg D hD
      have hc : □(B' 🡒 S'.disj ⋎ (T'.image (◇·)).disj) ∈ H :=
        Finset.mem_image.mpr ⟨(B', S', T'), Finset.mem_product.mpr ⟨hB',
          Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hS', Finset.mem_powerset.mpr hT'⟩⟩, rfl⟩
      have hbox : ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsFiniteGL] (x : M.World),
          x ⊩ □(B 🡒 S.disj ⋎ (T.image (◇·)).disj) ↔
            x ⊩ □(B' 🡒 S'.disj ⋎ (T'.image (◇·)).disj) := by
        intro κ _ M _ x
        simp only [forces_box, forces_imp, forces_or, forces_disj, Finset.mem_image,
          exists_exists_and_eq_and, forces_dia, S', T']
        refine forall_congr' fun y ↦ imp_congr_right fun _ ↦ ?_
        rw [forces_iff_of hBB' y]
        refine or_congr_right (or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩)
        · rintro ⟨C, hC, hy⟩
          exact ⟨⟨C, hC⟩, Finset.mem_attach _ _, (forces_iff_of (hf' C hC) y).mp hy⟩
        · rintro ⟨⟨C, hC⟩, -, hy⟩
          exact ⟨C, hC, (forces_iff_of (hf' C hC) y).mpr hy⟩
        · rintro ⟨C, hC, z, Ryz, hz⟩
          exact ⟨⟨C, hC⟩, Finset.mem_attach _ _, z, Ryz, (forces_iff_of (hg' C hC) z).mp hz⟩
        · rintro ⟨⟨C, hC⟩, -, z, Ryz, hz⟩
          exact ⟨C, hC, z, Ryz, (forces_iff_of (hg' C hC) z).mpr hz⟩
      cases b' with
      | true =>
        obtain ⟨l, hl, hAl⟩ := hG A hA
        refine ⟨l, hl, {_}, Finset.singleton_subset_iff.mpr hc, iff_of_forces fun M _ x ↦ ?_⟩
        simp only [forces_and, forces_iff_of hAl x, Finset.conj_singleton, hbox M x]
      | false =>
        obtain ⟨l, hl, Y, hY, hAY⟩ := ihA rfl
        refine ⟨l, hl, insert _ Y, Finset.insert_subset hc hY, iff_of_forces fun M _ x ↦ ?_⟩
        simp only [forces_and, forces_iff_of hAY x, forces_conj, Finset.mem_insert,
          forall_eq_or_imp, hbox M x]
        tauto
  refine ⟨G ∪ (G ×ˢ H.powerset).image (fun p ↦ p.1 ⋏ p.2.conj) ∪ F, ?_⟩
  rintro Z (⟨b, hZ⟩ | ⟨A, hA, rfl⟩)
  · cases b with
    | true =>
      obtain ⟨l, hl, h⟩ := hG Z hZ
      exact ⟨l, Finset.mem_union_left _ (Finset.mem_union_left _ hl), h⟩
    | false =>
      obtain ⟨l, hl, Y, hY, h⟩ := hR hZ rfl
      exact ⟨_, Finset.mem_union_left _ <| Finset.mem_union_right _ <| Finset.mem_image.mpr
        ⟨(l, Y), Finset.mem_product.mpr ⟨hl, Finset.mem_powerset.mpr hY⟩, rfl⟩, h⟩
  · obtain ⟨E, hE, h⟩ := hF _ ⟨A, ⟨true, hA⟩, rfl⟩
    exact ⟨E, Finset.mem_union_right _ hE, h⟩

/-- - [Ign91, Lemma 6.3] -/
theorem finiteUpToEquiv (P : Finset α) (b : Bool) :
    FiniteUpToEquiv {Z | LRClosure P b Z} :=
  (finiteUpToEquiv_base P).of_subset fun _ hZ ↦ .inl ⟨b, hZ⟩

/-! ### The `□`-subformulas of the LR-closure -/

private lemma box_mem_subfmls_disj₂ {E : Formula α} :
    {l : List (Formula α)} → □E ∈ (⋁l).subfmls → ∃ C ∈ l, □E ∈ C.subfmls
  | [], h => by simp [subfmls] at h
  | [A], h => ⟨A, by simp, h⟩
  | A :: B :: l, h => by
    change □E ∈ (A ⋎ ⋁(B :: l)).subfmls at h
    simp only [subfmls, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
      reduceCtorEq, false_or, or_false] at h
    rcases h with h | h
    · exact ⟨A, by simp, h⟩
    · obtain ⟨C, hC, h⟩ := box_mem_subfmls_disj₂ h
      exact ⟨C, by simp_all, h⟩

lemma box_mem_subfmls_disj {E : Formula α} {S : Finset (Formula α)} (h : □E ∈ S.disj.subfmls) :
    ∃ C ∈ S, □E ∈ C.subfmls := by
  obtain ⟨C, hC, h⟩ := box_mem_subfmls_disj₂ h
  exact ⟨C, Finset.mem_toList.mp hC, h⟩

/-- The bodies of the `□`-formulas occurring in the LR-closure: `∼B` for `B` in the closure, and
`B 🡒 ⋁S ⋎ ⋁◇T` for `B` and the members of `S` and `T` in its first part. -/
def IsBoxBody (P : Finset α) (E : Formula α) : Prop :=
  (∃ B b, LRClosure P b B ∧ E = ∼B) ∨
    ∃ B, ∃ S T : Finset (Formula α), LRClosure P true B ∧ (∀ C ∈ S, LRClosure P true C) ∧
      (∀ C ∈ T, LRClosure P true C) ∧ E = B 🡒 S.disj ⋎ (T.image (◇·)).disj

lemma isBoxBody_of_box_mem_subfmls {E : Formula α} (h : LRClosure P b Z)
    (hE : □E ∈ Z.subfmls) : IsBoxBody P E := by
  induction h with
  | falsum => simp [subfmls] at hE
  | atom => simp [subfmls] at hE
  | @and_box_neg A B b' _ hB ihA ihB =>
    simp only [subfmls, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
      reduceCtorEq, false_or, or_false, box_inj] at hE
    rcases hE with hE | rfl | hE
    · exact ihA hE
    · exact .inl ⟨B, b', hB, rfl⟩
    · exact ihB hE
  | @and_box_imp A B b' S T _ hB hS hT ihA ihB ihS ihT =>
    simp only [subfmls, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
      reduceCtorEq, false_or, or_false, box_inj] at hE
    rcases hE with hE | rfl | hE | hE | hE
    · exact ihA hE
    · exact .inr ⟨B, S, T, hB, hS, hT, rfl⟩
    · exact ihB hE
    · obtain ⟨C, hC, h⟩ := box_mem_subfmls_disj hE
      exact ihS C hC h
    · obtain ⟨C, hC, h⟩ := box_mem_subfmls_disj hE
      obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
      simp only [subfmls, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
        reduceCtorEq, false_or, or_false, box_inj] at h
      rcases h with rfl | h
      · exact .inl ⟨D, true, hT D hD, rfl⟩
      · exact ihT D hD h

end LRClosure

end FFL.ProvabilityLogic
