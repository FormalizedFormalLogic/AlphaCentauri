module

public import AlphaCentauri.InterpretabilityLogic.Gentzen.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModel
public import Mathlib.Data.Set.Finite.List

/-!
# Veltman semantics of the sequent calculus for $\mathbf{IL}$

The sequent calculus is sound for Veltman models, and a sequent not derivable in it fails at a
world of a finite Veltman model; hence $\mathbf{IL}$, the sequent calculus and finite Veltman
models agree.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

/-! ### Forcing of sequents -/

namespace Veltman

variable {κ α : Type*} [Nonempty κ]

/-- Some formula of the succedent of `S` is forced at `x` if every formula of its antecedent is. -/
def Model.World.ForcesSequent (M : Model κ α) (x : M.World) (S : Sequent α) : Prop :=
  (∀ A ∈ S.ant, Model.World.Forces M x A) → ∃ B ∈ S.suc, Model.World.Forces M x B

namespace Model.World

variable {M : Model κ α} {x : M.World}

lemma forces_conj₂ : {l : List (Formula α)} → (x ⊩ ⋀l ↔ ∀ B ∈ l, x ⊩ B)
  | [] => by simp
  | [B] => by simp
  | B :: C :: l => by simp [forces_and, forces_conj₂ (l := C :: l)]

@[simp]
lemma forces_conj {Γ : FormulaFinset α} : x ⊩ Γ.conj ↔ ∀ B ∈ Γ, x ⊩ B := by
  simp [Finset.conj, forces_conj₂];

lemma forces_disj₂ : {l : List (Formula α)} → (x ⊩ ⋁l ↔ ∃ B ∈ l, x ⊩ B)
  | [] => by simp
  | [B] => by simp
  | B :: C :: l => by simp [forces_or, forces_disj₂ (l := C :: l)]

@[simp]
lemma forces_disj {Γ : FormulaFinset α} : x ⊩ Γ.disj ↔ ∃ B ∈ Γ, x ⊩ B := by
  simp [Finset.disj, forces_disj₂];

end Model.World

/-- Every world of `M` forces `S`. -/
def Model.ValidatesSequent (M : Model κ α) (S : Sequent α) : Prop :=
  ∀ x : M.World, Model.World.ForcesSequent M x S

end Veltman

namespace FormulaFinset

variable {α : Type*} [DecidableEq α] {Γ : FormulaFinset α} {C : Formula α}

/-- The components `A` and `B` of the formulas `A ▷ B` in `Γ`. -/
def rhdComponents (Γ : FormulaFinset α) : FormulaFinset α :=
  Γ.biUnion fun
    | A ▷ B => {A, B}
    | _ => ∅

lemma mem_rhdComponents : C ∈ Γ.rhdComponents ↔ ∃ D, C ▷ D ∈ Γ ∨ D ▷ C ∈ Γ := by
  simp only [rhdComponents, Finset.mem_biUnion];
  constructor;
  · rintro ⟨E, hE, hC⟩;
    cases E with
    | rhd A B =>
      rcases Finset.mem_insert.mp hC with rfl | hC;
      · use B;
        exact Or.inl hE;
      · obtain rfl := Finset.mem_singleton.mp hC;
        use A;
        exact Or.inr hE;
    | _ => simp at hC;
  · rintro ⟨D, h | h⟩;
    · use C ▷ D;
      simpa using h;
    · use D ▷ C;
      simpa using h;

end FormulaFinset

namespace IL

open Veltman Veltman.Model Veltman.Model.World

variable {α : Type*} [DecidableEq α]

/-! ### The modal rules -/

/-- The formulas a world refuting `R` keeps refuting along `≺[w]`. -/
def avoid : Formula α → FormulaFinset α
  | _ ▷ B => {B}
  | _ => ∅

/-- The premise of the modal rule for `R` on the right. -/
def principal (Γ N : FormulaFinset α) : Formula α → Sequent α
  | A ▷ _ => witness Γ N A
  | □B => insert (□B) (Γ ∪ Γ.box ∪ N.boxNeg) ⟹ insert B N
  | _ => ∅ ⟹ ∅

/-- `R` is of the form `A ▷ B` or `□B`. -/
def IsModal : Formula α → Prop
  | _ ▷ _ => True
  | □_ => True
  | _ => False

namespace Gentzen

variable {Γ : FormulaFinset α} {l : List (Formula α × Formula α)} {R : Formula α}

lemma modal (hR : IsModal R)
    (hl : ∀ l₁ p l₂, l = l₁ ++ p :: l₂ → ⊢ᴳ[𝐈𝐋] witness Γ (avoid R ∪ antecedents l₂) p.2)
    (h : ⊢ᴳ[𝐈𝐋] principal Γ (avoid R ∪ antecedents l) R) :
    ⊢ᴳ[𝐈𝐋] Γ.box ∪ rhdFormulas l ⟹ {R} := by
  cases R with
  | rhd A B =>
    apply rhd;
    · simpa [avoid, ← Finset.insert_eq] using hl;
    · simpa [avoid, principal, ← Finset.insert_eq] using h;
  | box B =>
    apply box;
    · simpa [avoid] using hl;
    · simpa [avoid, principal] using h;
  | _ => simp [IsModal] at hR;

end Gentzen

/-! ### Avoiding sets -/

/-- `N` consists of `avoid R` and antecedents of formulas `C ▷ D` on the left of `x`, the premise
`principal x.ant.prebox N R` is not derivable, and neither is `witness x.ant.prebox N D` for any
`C ▷ D` on the left of `x` with `C ∉ N`. -/
structure IsAvoiding (x : Sequent α) (R : Formula α) (N : FormulaFinset α) : Prop where
  avoid_subset : avoid R ⊆ N
  mem : ∀ C ∈ N, C ∈ avoid R ∨ ∃ D, C ▷ D ∈ x.ant
  principal : ⊬ᴳ[𝐈𝐋] principal x.ant.prebox N R
  witness : ∀ {C D}, C ▷ D ∈ x.ant → C ∉ N → ⊬ᴳ[𝐈𝐋] witness x.ant.prebox N D

variable {x : Sequent α} {R : Formula α}

lemma exists_isAvoiding (hx : ⊬ᴳ[𝐈𝐋] x) (hR : R ∈ x.suc) (hRm : IsModal R) :
    ∃ N, IsAvoiding x R N := by
  by_contra hN;
  push Not at hN;
  have step : ∀ l : List (Formula α × Formula α), (∀ p ∈ l, p.1 ▷ p.2 ∈ x.ant) →
      (∀ l₁ p l₂, l = l₁ ++ p :: l₂ →
        ⊢ᴳ[𝐈𝐋] witness x.ant.prebox (avoid R ∪ antecedents l₂) p.2) →
      ∃ C D, C ▷ D ∈ x.ant ∧ C ∉ avoid R ∪ antecedents l ∧
        ⊢ᴳ[𝐈𝐋] witness x.ant.prebox (avoid R ∪ antecedents l) D := by
    intro l hl hprem;
    by_contra hw;
    push Not at hw;
    apply hN (avoid R ∪ antecedents l);
    constructor;
    · exact Finset.subset_union_left;
    · intro C hC;
      rcases Finset.mem_union.mp hC with h | h;
      · left;
        exact h;
      · right;
        obtain ⟨D, hD⟩ := mem_antecedents.mp h;
        use D;
        exact hl _ hD;
    · intro hp;
      apply hx;
      apply Gentzen.wk (Gentzen.modal hRm hprem hp);
      · intro C hC;
        rcases Finset.mem_union.mp hC with h | h;
        · exact FormulaFinset.box_prebox_subset h;
        · obtain ⟨A, B, hAB, rfl⟩ := mem_rhdFormulas.mp h;
          exact hl _ hAB;
      · simpa using hR;
    · intro C D hCD hC;
      exact hw C D hCD hC;
  have chain : ∀ n, ∃ l : List (Formula α × Formula α), (∀ p ∈ l, p.1 ▷ p.2 ∈ x.ant) ∧
      (∀ l₁ p l₂, l = l₁ ++ p :: l₂ →
        ⊢ᴳ[𝐈𝐋] witness x.ant.prebox (avoid R ∪ antecedents l₂) p.2) ∧
      n ≤ (antecedents l).card := by
    intro n;
    induction n with
    | zero =>
      use [];
      simp;
    | succ n ih =>
      obtain ⟨l, hl, hprem, hcard⟩ := ih;
      obtain ⟨C, D, hCD, hC, hD⟩ := step l hl hprem;
      use (C, D) :: l;
      and_intros;
      · intro p hp;
        rcases List.mem_cons.mp hp with rfl | hp;
        · exact hCD;
        · exact hl p hp;
      · intro l₁ p l₂ h;
        cases l₁ with
        | nil =>
          obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp h;
          exact hD;
        | cons q l₁ =>
          exact hprem l₁ p l₂ (List.cons_eq_cons.mp h).2;
      · have hC' : C ∉ antecedents l := fun h ↦ hC (Finset.mem_union_right _ h);
        rw [antecedents_cons, Finset.card_insert_of_notMem hC'];
        omega;
  obtain ⟨l, hl, -, hcard⟩ := chain (x.ant.subformulas.card + 1);
  have : antecedents l ⊆ x.ant.subformulas := by
    intro C hC;
    obtain ⟨D, hD⟩ := mem_antecedents.mp hC;
    exact FormulaFinset.mem_subformulas_subformulas (FormulaFinset.subset_subformulas (hl _ hD))
      (by simp);
  have := Finset.card_le_card this;
  omega;

open Classical in
/-- A chosen avoiding set. -/
noncomputable def avoidance (x : Sequent α) (R : Formula α) : FormulaFinset α :=
  if h : ∃ N, IsAvoiding x R N then h.choose else ∅

lemma isAvoiding_avoidance (hx : ⊬ᴳ[𝐈𝐋] x) (hR : R ∈ x.suc) (hRm : IsModal R) :
    IsAvoiding x R (avoidance x R) := by
  have h := exists_isAvoiding hx hR hRm;
  simpa [avoidance, h] using h.choose_spec;

/-! ### The closure of a sequent -/

/-- The subformulas of `S`, `⊥`, and the formulas `∼A` and `□∼A` for the components `A` of the
formulas `A ▷ B` among them. -/
def closure (S : Sequent α) : FormulaFinset α :=
  insert ⊥ (S.subformulas ∪ S.subformulas.rhdComponents.image (∼·) ∪
    S.subformulas.rhdComponents.boxNeg)

section closure

variable {S : Sequent α} {A B C D : Formula α}

lemma mem_closure_of_mem_subformulas (h : A ∈ S.subformulas) : A ∈ closure S := by
  simp [closure, h];

lemma mem_subformulas_of_mem_rhdComponents (h : C ∈ S.subformulas.rhdComponents) :
    C ∈ S.subformulas := by
  obtain ⟨D, h | h⟩ := FormulaFinset.mem_rhdComponents.mp h <;>
    exact FormulaFinset.mem_subformulas_subformulas h (by simp);

lemma subset_closure : S.ant ∪ S.suc ⊆ closure S := fun _ hA ↦
  mem_closure_of_mem_subformulas (FormulaFinset.subset_subformulas hA)

lemma mem_closure_imp (h : A 🡒 B ∈ closure S) : A ∈ closure S ∧ B ∈ closure S := by
  simp only [closure, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at h;
  rcases h with h | (h | ⟨C, hC, h⟩) | ⟨C, hC, h⟩;
  · simp at h;
  · constructor <;>
      exact mem_closure_of_mem_subformulas (FormulaFinset.mem_subformulas_subformulas h (by simp));
  · obtain ⟨rfl, rfl⟩ := Formula.imp_inj.mp h;
    exact ⟨mem_closure_of_mem_subformulas (mem_subformulas_of_mem_rhdComponents hC),
      Finset.mem_insert_self _ _⟩;
  · simp at h;

lemma mem_closure_box (h : □C ∈ closure S) : C ∈ closure S := by
  simp only [closure, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at h;
  rcases h with h | (h | ⟨D, hD, h⟩) | ⟨D, hD, h⟩;
  · simp at h;
  · exact mem_closure_of_mem_subformulas (FormulaFinset.mem_subformulas_subformulas h (by simp));
  · simp at h;
  · obtain rfl := Formula.box_inj.mp h;
    simp only [closure, Finset.mem_insert, Finset.mem_union, Finset.mem_image];
    right; left; right;
    use D;

lemma mem_closure_rhd (h : C ▷ D ∈ closure S) :
    C ∈ closure S ∧ □(∼C) ∈ closure S ∧ D ∈ closure S ∧ □(∼D) ∈ closure S := by
  have h' : C ▷ D ∈ S.subformulas := by
    simp only [closure, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at h;
    rcases h with h | (h | ⟨E, -, h⟩) | ⟨E, -, h⟩ <;> simp_all;
  have hC : C ∈ S.subformulas.rhdComponents := FormulaFinset.mem_rhdComponents.mpr ⟨D, Or.inl h'⟩;
  have hD : D ∈ S.subformulas.rhdComponents := FormulaFinset.mem_rhdComponents.mpr ⟨C, Or.inr h'⟩;
  and_intros;
  · exact mem_closure_of_mem_subformulas (mem_subformulas_of_mem_rhdComponents hC);
  · simp only [closure, Finset.mem_insert, Finset.mem_union, Finset.mem_image];
    right; right;
    use C;
  · exact mem_closure_of_mem_subformulas (mem_subformulas_of_mem_rhdComponents hD);
  · simp only [closure, Finset.mem_insert, Finset.mem_union, Finset.mem_image];
    right; right;
    use D;

end closure

/-! ### Saturated sequents -/

/-- The sequents from which the countermodel of `BS` is built. -/
structure SaturatedSequent (BS : Sequent α) extends Sequent α where
  saturated : toSequent.Saturated
  ant_subset : ant ⊆ closure BS
  suc_subset : suc ⊆ closure BS
  unprovable : ⊬ᴳ[𝐈𝐋] toSequent

namespace SaturatedSequent

variable {BS : Sequent α} {x : SaturatedSequent BS} {A : Formula α}

@[grind .]
lemma not_mem_both : ¬(A ∈ x.ant ∧ A ∈ x.suc) := fun h ↦ x.unprovable (Gentzen.union' _ h.1 h.2)

@[grind .]
lemma bot_not_mem_ant : ⊥ ∉ x.ant := fun h ↦ x.unprovable (Gentzen.botL_mem h)

lemma mem_suc_of_neg_mem_ant (h : ∼A ∈ x.ant) : A ∈ x.suc :=
  (x.saturated.impL h).resolve_right bot_not_mem_ant

lemma ext {x y : SaturatedSequent BS} (ha : x.ant = y.ant) (hs : x.suc = y.suc) : x = y := by
  obtain ⟨⟨_, _⟩, _⟩ := x;
  obtain ⟨⟨_, _⟩, _⟩ := y;
  grind;

instance : Finite (SaturatedSequent BS) :=
  Finite.of_injective
    (β := (closure BS).powerset × (closure BS).powerset)
    (fun x ↦ (⟨x.ant, Finset.mem_powerset.mpr x.ant_subset⟩,
              ⟨x.suc, Finset.mem_powerset.mpr x.suc_subset⟩))
    (by
      intro x y h;
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h;
      exact ext h.1 h.2)

lemma lindenbaum {S₀ : Sequent α} (h₀ : ⊬ᴳ[𝐈𝐋] S₀) (hant : S₀.ant ⊆ closure BS)
    (hsuc : S₀.suc ⊆ closure BS) : ∃ x : SaturatedSequent BS, S₀ ⊆ x.toSequent := by
  obtain ⟨S, h₁, h₂, h₃, h₄, h₅⟩ :=
    Gentzen.exists_saturated mem_closure_imp h₀ hant hsuc;
  use ⟨S, h₃, h₄, h₅, h₂⟩;

lemma prebox_subset : x.ant.prebox ⊆ closure BS := by
  intro C hC;
  exact mem_closure_box (x.ant_subset (FormulaFinset.mem_prebox.mp hC));

end SaturatedSequent

/-! ### Children -/

/-- `y` is a child of `x` for the formula `R` on the right of `x`. -/
structure IsChild (x : Sequent α) (R : Formula α) (y : Sequent α) : Prop where
  modal : IsModal R
  mem_suc : R ∈ x.suc
  box : ∀ {C}, □C ∈ x.ant → C ∈ y.ant ∧ □C ∈ y.ant
  avoid : ∀ {C}, C ∈ avoidance x R → C ∈ y.suc ∧ □(∼C) ∈ y.ant
  new_box : ∃ C, □C ∈ y.ant ∧ □C ∉ x.ant

/-! ### The countermodel -/

namespace SaturatedSequent

variable {BS : Sequent α} {x : SaturatedSequent BS} {R : Formula α}

lemma avoidance_mem_closure (hR : R ∈ x.suc) (hRm : IsModal R) :
    ∀ C ∈ avoidance x.toSequent R, C ∈ closure BS ∧ □(∼C) ∈ closure BS := by
  intro C hC;
  rcases (isAvoiding_avoidance x.unprovable hR hRm).mem C hC with h | ⟨D, hD⟩;
  · cases R with
    | rhd A B =>
      obtain rfl := Finset.mem_singleton.mp h;
      obtain ⟨-, -, h₁, h₂⟩ := mem_closure_rhd (x.suc_subset hR);
      exact ⟨h₁, h₂⟩;
    | _ => simp [avoid] at h;
  · obtain ⟨h₁, h₂, -, -⟩ := mem_closure_rhd (x.ant_subset hD);
    exact ⟨h₁, h₂⟩;

lemma exists_child (hR : R ∈ x.suc) (hRm : IsModal R) {S₀ : Sequent α} (h₀ : ⊬ᴳ[𝐈𝐋] S₀)
    (hant : S₀.ant ⊆ closure BS) (hsuc : S₀.suc ⊆ closure BS)
    (hΓ : x.ant.prebox ∪ x.ant.prebox.box ⊆ S₀.ant)
    (hN : (avoidance x.toSequent R).boxNeg ⊆ S₀.ant) (hN' : avoidance x.toSequent R ⊆ S₀.suc)
    (hnew : ∀ y : SaturatedSequent BS, S₀ ⊆ y.toSequent → ∃ C, □C ∈ y.ant ∧ □C ∉ x.ant) :
    ∃ y : SaturatedSequent BS, S₀ ⊆ y.toSequent ∧ IsChild x.toSequent R y.toSequent := by
  obtain ⟨y, hy⟩ := lindenbaum h₀ hant hsuc;
  use y;
  and_intros;
  · exact hy;
  · exact {
      modal := hRm
      mem_suc := hR
      box := fun hC ↦ ⟨hy.ant (hΓ (Finset.mem_union_left _ (FormulaFinset.mem_prebox.mpr hC))),
        hy.ant (hΓ (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (FormulaFinset.mem_prebox.mpr hC))))⟩
      avoid := fun hC ↦ ⟨hy.suc (hN' hC), hy.ant (hN (Finset.mem_image_of_mem _ hC))⟩
      new_box := hnew y hy }

end SaturatedSequent

open SaturatedSequent

variable {BS : Sequent α} (x₀ : SaturatedSequent BS)

/-- The last sequent of a list of children, the head of the list, or `x₀` for the empty list. -/
def current : List (Formula α × SaturatedSequent BS) → SaturatedSequent BS
  | [] => x₀
  | (_, y) :: _ => y

/-- Each entry `(R, y)` of the list is a child for `R` of the entry after it, the last one of
`x₀`. -/
def IsPath : List (Formula α × SaturatedSequent BS) → Prop
  | [] => True
  | (R, y) :: l => IsChild (current x₀ l).toSequent R y.toSequent ∧ IsPath l

/-- The worlds of the countermodel. -/
def Path := { l : List (Formula α × SaturatedSequent BS) // IsPath x₀ l }

instance : Nonempty (Path x₀) := ⟨⟨[], trivial⟩⟩

variable {x₀} {u l : List (Formula α × SaturatedSequent BS)} {p : Formula α × SaturatedSequent BS}
  {R C : Formula α} {c : SaturatedSequent BS}

lemma IsPath.of_suffix (hu : IsPath x₀ u) (h : l <:+ u) : IsPath x₀ l := by
  obtain ⟨t, rfl⟩ := h;
  induction t with
  | nil => exact hu;
  | cons q t ih => exact ih hu.2;

lemma IsPath.isChild (hu : IsPath x₀ u) (h : (R, c) :: l <:+ u) :
    IsChild (current x₀ l).toSequent R c.toSequent :=
  (hu.of_suffix h).1

lemma IsPath.box (hu : IsPath x₀ u) (h : p :: l <:+ u) (hC : □C ∈ (current x₀ l).ant) :
    C ∈ (current x₀ u).ant ∧ □C ∈ (current x₀ u).ant := by
  obtain ⟨t, rfl⟩ := h;
  induction t with
  | nil => exact hu.1.box hC;
  | cons q t ih => exact hu.1.box (ih hu.2).2;

lemma IsPath.avoid (hu : IsPath x₀ u) (h : (R, c) :: l <:+ u)
    (hC : C ∈ avoidance (current x₀ l).toSequent R) : C ∈ (current x₀ u).suc := by
  obtain ⟨t, rfl⟩ := h;
  rcases List.eq_nil_or_concat t with rfl | ⟨t, q, rfl⟩;
  · exact (hu.isChild (List.suffix_refl _)).avoid hC |>.1;
  · have hc := hu.isChild (List.suffix_append _ _);
    rw [List.concat_eq_append, List.append_assoc, List.singleton_append] at hu ⊢;
    exact mem_suc_of_neg_mem_ant (hu.box (List.suffix_append t _) (hc.avoid hC).2).1;

lemma IsPath.mem_closure (hu : IsPath x₀ u) : ∀ p ∈ u, p.1 ∈ closure BS := by
  induction u with
  | nil => simp;
  | cons q u ih =>
    intro p hp;
    rcases List.mem_cons.mp hp with rfl | hp;
    · exact (current x₀ u).suc_subset hu.1.mem_suc;
    · exact ih hu.2 p hp;

lemma IsPath.length_le (hu : IsPath x₀ u) :
    u.length + x₀.ant.prebox.card ≤ (current x₀ u).ant.prebox.card := by
  induction u with
  | nil => simp [current];
  | cons q u ih =>
    obtain ⟨R, y⟩ := q;
    have hsub : (current x₀ u).ant.prebox ⊂ y.ant.prebox := by
      rw [Finset.ssubset_iff_of_subset];
      · obtain ⟨C, hC, hC'⟩ := hu.1.new_box;
        use C;
        simpa using ⟨hC, hC'⟩;
      · intro C hC;
        simpa using (hu.1.box (FormulaFinset.mem_prebox.mp hC)).2;
    have := Finset.card_lt_card hsub;
    have := ih hu.2;
    simp only [List.length_cons, current];
    omega;

instance : Finite (Path x₀) := by
  let T := { R // R ∈ closure BS } × SaturatedSequent BS;
  have hsub : { l | IsPath x₀ l } ⊆
      (List.map fun q : T ↦ (q.1.1, q.2)) '' { l | l.length ≤ (closure BS).card } := by
    intro l hl;
    use l.pmap (fun p hp ↦ (⟨p.1, hp⟩, p.2)) (IsPath.mem_closure hl);
    constructor;
    · have h₁ := IsPath.length_le hl;
      have h₂ := Finset.card_le_card (current x₀ l).prebox_subset;
      change (List.pmap _ l _).length ≤ _;
      rw [List.length_pmap];
      omega;
    · simp [List.map_pmap];
  exact (((List.finite_length_le T _).image _).subset hsub).to_subtype

/-- The countermodel of `BS` with root `x₀`: a tree of children, in which `u ≺[w] v` holds when `u`
and `v` pass through children of `w` for the same formula. -/
def countermodel (x₀ : SaturatedSequent BS) : Veltman.Model (Path x₀) α where
  Rel' u v := ∃ p, p :: u.1 <:+ v.1
  S' w u v := ∃ R c c', (R, c) :: w.1 <:+ u.1 ∧ (R, c') :: w.1 <:+ v.1
  Val' u a := #a ∈ (current x₀ u.1).ant

namespace countermodel

instance : IsTrans _ (countermodel x₀).Rel :=
  ⟨fun _ _ _ ⟨p, h₁⟩ ⟨q, h₂⟩ ↦ ⟨p, h₁.trans ((List.suffix_cons q _).trans h₂)⟩⟩

instance : Std.Irrefl (countermodel x₀).Rel :=
  ⟨by
    rintro _ ⟨_, h⟩;
    simpa using h.length_le⟩

instance : (countermodel x₀).IsIL where
  rel_of_s_left := fun ⟨R, c, _, h, _⟩ ↦ ⟨(R, c), h⟩
  rel_of_s_right := fun ⟨R, _, c', _, h⟩ ↦ ⟨(R, c'), h⟩
  s_refl := fun ⟨p, h⟩ ↦ ⟨p.1, p.2, p.2, h, h⟩
  s_trans := by
    rintro w u v z ⟨R, c, c', h₁, h₂⟩ ⟨R', d, d', h₃, h₄⟩;
    have := (List.suffix_of_suffix_length_le h₂ h₃ (by simp)).eq_of_length (by simp);
    obtain ⟨rfl, -⟩ := Prod.mk.inj (List.cons_eq_cons.mp this).1;
    use R, c, d';
  s_of_rel := fun ⟨p, h₁⟩ ⟨q, h₂⟩ ↦ ⟨p.1, p.2, p.2, h₁, h₁.trans ((List.suffix_cons q _).trans h₂)⟩

variable {w : (countermodel x₀).World} {A : Formula α}

lemma truthlemma :
    (A ∈ (current x₀ w.1).ant → w ⊩ A) ∧ (A ∈ (current x₀ w.1).suc → w ⊮ A) := by
  induction A generalizing w with
  | atom a => exact ⟨id, fun h hf ↦ not_mem_both ⟨hf, h⟩⟩;
  | falsum => exact ⟨fun h ↦ absurd h bot_not_mem_ant, fun _ ↦ id⟩;
  | imp A B ihA ihB =>
    constructor;
    · intro h hA;
      rcases (current x₀ w.1).saturated.impL h with hA' | hB;
      · exact absurd hA (ihA.2 hA');
      · exact ihB.1 hB;
    · intro h hf;
      obtain ⟨hA, hB⟩ := (current x₀ w.1).saturated.impR h;
      exact ihB.2 hB (hf (ihA.1 hA));
  | box B ih =>
    constructor;
    · rintro h u ⟨p, hp⟩;
      exact ih.1 (u.2.box hp h).1;
    · intro h;
      apply not_forces_box.mpr;
      have hav := isAvoiding_avoidance (current x₀ w.1).unprovable h trivial;
      have hcl := avoidance_mem_closure h (R := □B) trivial;
      have hB := (current x₀ w.1).suc_subset h;
      obtain ⟨y, hy, hchild⟩ := exists_child h trivial hav.principal
        (by
          intro C hC;
          simp only [principal, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hC;
          rcases hC with rfl | (hC | ⟨D, hD, rfl⟩) | ⟨D, hD, rfl⟩;
          · exact hB;
          · exact prebox_subset hC;
          · exact (current x₀ w.1).ant_subset (FormulaFinset.mem_prebox.mp hD);
          · exact (hcl _ hD).2)
        (by
          intro C hC;
          rcases Finset.mem_insert.mp hC with rfl | hC;
          · exact mem_closure_box hB;
          · exact (hcl _ hC).1)
        (fun _ hC ↦ Finset.mem_insert_of_mem (Finset.mem_union_left _ hC))
        (by intro C hC; simp [principal, hC])
        (by intro C hC; simp [principal, hC])
        (by
          intro y hy;
          use B;
          and_intros;
          · exact hy.ant (by simp [principal]);
          · intro hB';
            exact not_mem_both ⟨hB', h⟩);
      use ⟨(□B, y) :: w.1, hchild, w.2⟩;
      and_intros;
      · use (□B, y);
      · exact ih.2 (hy.suc (by simp [principal]));
  | rhd A B ihA ihB =>
    constructor;
    · rintro h u ⟨⟨R, c⟩, hp⟩ hu;
      have hc := u.2.isChild hp;
      have hav := isAvoiding_avoidance (current x₀ w.1).unprovable hc.mem_suc hc.modal;
      have hcl := avoidance_mem_closure hc.mem_suc hc.modal;
      have hA : A ∉ avoidance (current x₀ w.1).toSequent R := fun hA ↦ ihA.2 (u.2.avoid hp hA) hu;
      obtain ⟨-, -, hB, hB'⟩ := mem_closure_rhd ((current x₀ w.1).ant_subset h);
      obtain ⟨y, hy, hchild⟩ := exists_child hc.mem_suc hc.modal (hav.witness h hA)
        (by
          intro C hC;
          simp only [witness, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hC;
          rcases hC with rfl | rfl | ((hC | ⟨D, hD, rfl⟩) | ⟨D, hD, rfl⟩);
          · exact hB;
          · exact hB';
          · exact prebox_subset hC;
          · exact (current x₀ w.1).ant_subset (FormulaFinset.mem_prebox.mp hD);
          · exact (hcl _ hD).2)
        (fun _ hC ↦ (hcl _ hC).1)
        (fun _ hC ↦
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hC)))
        (by intro C hC; simp [witness, hC])
        (by intro C hC; simpa [witness] using hC)
        (by
          intro y hy;
          use ∼B;
          and_intros;
          · exact hy.ant (by simp [witness]);
          · intro hB'';
            have h₁ : ∼B ∈ y.ant := hy.ant (by simp [witness, hB'']);
            exact not_mem_both ⟨hy.ant (by simp [witness]), mem_suc_of_neg_mem_ant h₁⟩);
      use ⟨(R, y) :: w.1, hchild, w.2⟩;
      and_intros;
      · use R, c, y;
      · exact ihB.1 (hy.ant (by simp [witness]));
    · intro h;
      apply not_forces_rhd.mpr;
      have hav := isAvoiding_avoidance (current x₀ w.1).unprovable h trivial;
      have hcl := avoidance_mem_closure h (R := A ▷ B) trivial;
      obtain ⟨hA, hA', -, -⟩ := mem_closure_rhd ((current x₀ w.1).suc_subset h);
      obtain ⟨y, hy, hchild⟩ := exists_child h trivial hav.principal
        (by
          intro C hC;
          simp only [principal, witness, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image] at hC;
          rcases hC with rfl | rfl | ((hC | ⟨D, hD, rfl⟩) | ⟨D, hD, rfl⟩);
          · exact hA;
          · exact hA';
          · exact prebox_subset hC;
          · exact (current x₀ w.1).ant_subset (FormulaFinset.mem_prebox.mp hD);
          · exact (hcl _ hD).2)
        (fun _ hC ↦ (hcl _ hC).1)
        (fun _ hC ↦
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hC)))
        (by intro C hC; simp [principal, witness, hC])
        (by intro C hC; simpa [principal, witness] using hC)
        (by
          intro y hy;
          use ∼A;
          and_intros;
          · exact hy.ant (by simp [principal, witness]);
          · intro hA'';
            have h₁ : ∼A ∈ y.ant := hy.ant (by simp [principal, witness, hA'']);
            exact not_mem_both
              ⟨hy.ant (by simp [principal, witness]), mem_suc_of_neg_mem_ant h₁⟩);
      use ⟨(A ▷ B, y) :: w.1, hchild, w.2⟩;
      and_intros;
      · use (A ▷ B, y);
      · exact ihA.1 (hy.ant (by simp [principal, witness]));
      · rintro v ⟨R, c, c', h₁, h₂⟩;
        obtain ⟨rfl, -⟩ := Prod.mk.inj (List.cons_eq_cons.mp (h₁.eq_of_length (by simp))).1;
        exact ihB.2 (v.2.avoid h₂ (hav.avoid_subset (by simp [avoid])));

end countermodel


end IL

end FFL.InterpretabilityLogic

end
