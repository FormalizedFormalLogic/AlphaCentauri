module

public import AlphaCentauri.InterpretabilityLogic.Extension
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Zorn

/-!
# Maximal consistent sets of all formulas

Maximal consistent sets of formulas relative to a logic, Lindenbaum's lemma, and, for extensions of
$\mathbf{IL}$, assuring successors, their existence, and the labelling lemmas for $\mathsf{P}_0$ and
$\mathsf{R}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- A set of formulas consistent in `L` that contains `A` or `∼A` for every formula `A`. -/
structure MaximalConsistentTheory (L : Logic α) where
  set : Set (Formula α)
  consistent : set *⊬[L] ⊥
  mem_or_neg_mem (A : Formula α) : A ∈ set ∨ ∼A ∈ set

namespace MaximalConsistentTheory

open Logic

variable {L : Logic α} {Γ Δ Θ Λ : MaximalConsistentTheory L} {X : Set (Formula α)}
  {A B C : Formula α}

instance : Membership (Formula α) (MaximalConsistentTheory L) := ⟨fun Γ A ↦ A ∈ Γ.set⟩

lemma mem_def : A ∈ Γ ↔ A ∈ Γ.set := Iff.rfl

section

variable [Entailment.Cl L]

lemma mem_of_provable (h : Γ.set *⊢[L] A) : A ∈ Γ := by
  rcases Γ.mem_or_neg_mem A with hA | hA;
  · exact hA;
  · exfalso;
    apply Γ.consistent;
    have h₁ : Γ.set *⊢[L] ∼A := Context.by_axm hA;
    cl_prover [h, h₁];

lemma mem_of_theorem (h : L ⊢ A) : A ∈ Γ := mem_of_provable <| Context.of h

lemma mem_of_imp (h : L ⊢ A 🡒 B) (hA : A ∈ Γ) : B ∈ Γ :=
  mem_of_provable <| Context.of h ⨀ Context.by_axm hA

lemma mem_of_imp₂ (h : L ⊢ A 🡒 B 🡒 C) (hA : A ∈ Γ) (hB : B ∈ Γ) : C ∈ Γ :=
  mem_of_provable <| Context.of h ⨀ Context.by_axm hA ⨀ Context.by_axm hB

lemma not_mem_of_neg_mem (h : ∼A ∈ Γ) : A ∉ Γ := fun hA ↦
  Γ.consistent <| Context.bot_of_mem_neg hA h

lemma neg_mem_iff : ∼A ∈ Γ ↔ A ∉ Γ :=
  ⟨not_mem_of_neg_mem, fun h ↦ (Γ.mem_or_neg_mem A).resolve_left h⟩

lemma bot_not_mem : ⊥ ∉ Γ := fun h ↦ Γ.consistent <| Context.by_axm h

lemma imp_mem_iff : A 🡒 B ∈ Γ ↔ (A ∈ Γ → B ∈ Γ) := by
  constructor;
  · intro h hA;
    exact mem_of_imp₂ C_id h hA;
  · intro h;
    by_cases hA : A ∈ Γ;
    · exact mem_of_imp (show L ⊢ B 🡒 A 🡒 B by cl_prover) (h hA);
    · exact mem_of_imp (show L ⊢ ∼A 🡒 A 🡒 B by cl_prover) (neg_mem_iff.mpr hA);

/-! ### Lindenbaum's lemma -/

/-- Every consistent set is contained in a maximal consistent set. -/
lemma exists_superset (h : X *⊬[L] ⊥) : ∃ Γ : MaximalConsistentTheory L, X ⊆ Γ.set := by
  obtain ⟨M, hXM, hM⟩ := zorn_subset_nonempty {Y | Y *⊬[L] ⊥} (by
    intro c hc hchain hne;
    use ⋃₀ c;
    and_intros;
    · intro hb;
      obtain ⟨Δ, hΔ, hb⟩ := Context.provable_iff_finset.mp hb;
      obtain ⟨Y, hY, hΔY⟩ := hchain.directedOn.exists_mem_subset_of_finset_subset_biUnion
        (f := id) hne (by simpa [Set.sUnion_eq_biUnion] using hΔ);
      exact hc hY <| Context.weakening hΔY hb;
    · intro Y hY;
      exact Set.subset_sUnion_of_mem hY) X h;
  have hmax {A} (h : (insert A M) *⊬[L] ⊥) : A ∈ M :=
    hM.2 (y := insert A M) h (Set.subset_insert _ _) (Set.mem_insert _ _);
  use ⟨M, hM.1, ?_⟩;
  intro A;
  by_contra hn;
  rw [not_or] at hn;
  apply hM.1;
  have h₁ : M *⊢[L] ∼A := Context.deduct <| by_contra fun h ↦ hn.1 (hmax h);
  have h₂ : M *⊢[L] ∼∼A := Context.deduct <| by_contra fun h ↦ hn.2 (hmax h);
  exact h₂ ⨀ h₁;

end

/-! ### Assuring successors -/

variable [DecidableEq α]

/-- The formulas `A` with $A ▷ \bigvee_{G ∈ S'} ¬G ∈ Γ$ for some finite $S' \subseteq S$. -/
def antecedents (Γ : MaximalConsistentTheory L) (S : Set (Formula α)) : Set (Formula α) :=
  {A | ∃ T : Finset (Formula α), ↑T ⊆ S ∧ A ▷ (T.image (∼·)).disj ∈ Γ}

/-- The formulas `□∼A` with `A ∈ Γ.antecedents S`.

- [MV20, Definition 5]
-/
def boxLabel (Γ : MaximalConsistentTheory L) (S : Set (Formula α)) : Set (Formula α) :=
  (fun A ↦ □(∼A)) '' Γ.antecedents S

/-- `Δ` is an `S`-assuring successor of `Γ`: `∼A` and `□∼A` belong to `Δ` whenever
$A ▷ \bigvee_{G ∈ S'} ¬G ∈ Γ$ for some finite $S' \subseteq S$.

- [MV20, Definition 4]
-/
def AssuringSuccessor (S : Set (Formula α)) (Γ Δ : MaximalConsistentTheory L) : Prop :=
  ∀ A ∈ Γ.antecedents S, ∼A ∈ Δ ∧ □(∼A) ∈ Δ

variable {S T : Set (Formula α)}

lemma antecedents_mono (h : S ⊆ T) : Γ.antecedents S ⊆ Γ.antecedents T := by
  rintro A ⟨U, hU, hA⟩;
  use U;
  and_intros;
  · exact hU.trans h;
  · exact hA;

lemma boxLabel_mono (h : S ⊆ T) : Γ.boxLabel S ⊆ Γ.boxLabel T :=
  Set.image_mono (antecedents_mono h)

lemma AssuringSuccessor.mono (hST : S ⊆ T) (h : AssuringSuccessor T Γ Δ) :
    AssuringSuccessor S Γ Δ := fun A hA ↦ h A (antecedents_mono hST hA)

section

open Logic.ofAxioms

variable {𝔸 : Set (Formula α)} {Γ Δ Θ Λ : MaximalConsistentTheory (ofAxioms 𝔸)}

lemma bot_mem_antecedents : ⊥ ∈ Γ.antecedents S := by
  use ∅;
  and_intros;
  · simp;
  · exact mem_of_theorem <| rhd_of_provable efq;

lemma or_mem_antecedents (hA : A ∈ Γ.antecedents S) (hB : B ∈ Γ.antecedents S) :
    A ⋎ B ∈ Γ.antecedents S := by
  obtain ⟨U₁, hU₁, h₁⟩ := hA;
  obtain ⟨U₂, hU₂, h₂⟩ := hB;
  use U₁ ∪ U₂;
  and_intros;
  · simpa using ⟨hU₁, hU₂⟩;
  · have e₁ : ofAxioms 𝔸 ⊢ A ▷ (U₁.image (∼·)).disj 🡒 A ▷ ((U₁ ∪ U₂).image (∼·)).disj :=
      rhd_mono_right <| CFDisjFDisj_of_subset <|
        Finset.image_subset_image Finset.subset_union_left;
    have e₂ : ofAxioms 𝔸 ⊢ B ▷ (U₂.image (∼·)).disj 🡒 B ▷ ((U₁ ∪ U₂).image (∼·)).disj :=
      rhd_mono_right <| CFDisjFDisj_of_subset <|
        Finset.image_subset_image Finset.subset_union_right;
    have e₃ : ofAxioms 𝔸 ⊢ Axioms.J3 A B ((U₁ ∪ U₂).image (∼·)).disj := axiomJ3;
    exact mem_of_imp₂ (by cl_prover [e₁, e₂, e₃]) h₁ h₂;

lemma antecedents_of_rhd_mem (h : B ▷ A ∈ Γ) (hA : A ∈ Γ.antecedents S) :
    B ∈ Γ.antecedents S := by
  obtain ⟨U, hU, hA⟩ := hA;
  have e : ofAxioms 𝔸 ⊢ Axioms.J2 B A (U.image (∼·)).disj := axiomJ2;
  use U;
  and_intros;
  · exact hU;
  · exact mem_of_imp₂ (by cl_prover [e]) h hA;

lemma neg_mem_antecedents {G : Formula α} (h : G ∈ S) : ∼G ∈ Γ.antecedents S := by
  use {G};
  and_intros;
  · simpa;
  · exact mem_of_theorem <| rhd_of_provable <| right_Fdisj_intro _ (by simp);

lemma mem_antecedents_empty_iff : A ∈ Γ.antecedents ∅ ↔ □(∼A) ∈ Γ := by
  constructor;
  · rintro ⟨U, hU, hA⟩;
    obtain rfl : U = ∅ := by simpa using hU;
    have e : ofAxioms 𝔸 ⊢ (Finset.image (∼·) (∅ : Finset (Formula α))).disj 🡒 ⊥ :=
      left_Fdisj_intro _ (by simp);
    exact mem_of_imp (C_trans (rhd_mono_right e) rhd_bot) hA;
  · intro h;
    use ∅;
    and_intros;
    · simp;
    · apply mem_of_imp _ h;
      exact C_trans (box_mono (by cl_prover)) axiomJ1;

namespace AssuringSuccessor

lemma box_mem_of_box_mem (h : AssuringSuccessor S Γ Δ) (hA : □A ∈ Γ) : A ∈ Δ ∧ □A ∈ Δ := by
  have h₁ : ∼A ∈ Γ.antecedents S :=
    antecedents_mono (Set.empty_subset _) <| mem_antecedents_empty_iff.mpr <|
      mem_of_imp (box_mono dni) hA;
  obtain ⟨h₂, h₃⟩ := h _ h₁;
  exact ⟨mem_of_imp Entailment.dne h₂, mem_of_imp (box_mono Entailment.dne) h₃⟩

/-- - [MV20, Lemma 6] -/
lemma trans_successor (h₁ : AssuringSuccessor S Γ Δ) (h₂ : AssuringSuccessor ∅ Δ Θ) :
    AssuringSuccessor S Γ Θ := fun A hA ↦ (h₂.box_mem_of_box_mem (h₁ A hA).2)

/-- - [MV20, Lemma 6] -/
lemma subset (h : AssuringSuccessor S Γ Δ) : S ⊆ Δ.set := fun _ hG ↦
  mem_of_imp Entailment.dne (h _ (neg_mem_antecedents hG)).1

/-- - [MV20, Lemma 22] -/
lemma of_boxLabel (h₁ : AssuringSuccessor (Θ.boxLabel S) Γ Δ) (h₂ : AssuringSuccessor ∅ Δ Λ) :
    AssuringSuccessor S Θ Λ := fun A hA ↦ h₂.box_mem_of_box_mem (h₁.subset ⟨A, hA, rfl⟩)

end AssuringSuccessor

/-! ### Existence of assuring successors -/

private lemma consistent_of_not_mem_antecedents (h : B ∉ Γ.antecedents S) :
    (insert B <| insert (□(∼B)) {C | ∃ A ∈ Γ.antecedents S, C = ∼A ∨ C = □(∼A)}) *⊬[ofAxioms 𝔸]
      ⊥ := by
  intro hb;
  obtain ⟨l, hl, hb⟩ := Context.provable_iff.mp hb;
  have key : ∀ l : List (Formula α),
      (∀ C ∈ l, C ∈ insert B (insert (□(∼B)) {C | ∃ A ∈ Γ.antecedents S, C = ∼A ∨ C = □(∼A)})) →
        ∃ A ∈ Γ.antecedents S, ∀ C ∈ l, ofAxioms 𝔸 ⊢ (B ⋏ □(∼B)) ⋏ (∼A ⋏ □(∼A)) 🡒 C := by
    intro l;
    induction l with
    | nil =>
      intro _;
      use ⊥;
      and_intros;
      · exact bot_mem_antecedents;
      · simp;
    | cons C l ih =>
      intro hl;
      obtain ⟨A, hA, hlA⟩ := ih fun D hD ↦ hl D (by simp [hD]);
      rcases hl C (by simp) with rfl | rfl | ⟨A', hA', rfl | rfl⟩;
      · use A;
        and_intros;
        · exact hA;
        · simp only [List.mem_cons, forall_eq_or_imp];
          exact ⟨by cl_prover, hlA⟩;
      · use A;
        and_intros;
        · exact hA;
        · simp only [List.mem_cons, forall_eq_or_imp];
          exact ⟨by cl_prover, hlA⟩;
      all_goals
        use A ⋎ A';
        and_intros;
        · exact or_mem_antecedents hA hA';
        · have e₁ : ofAxioms 𝔸 ⊢ □(∼(A ⋎ A')) 🡒 □(∼A) := box_mono <| by cl_prover;
          have e₂ : ofAxioms 𝔸 ⊢ □(∼(A ⋎ A')) 🡒 □(∼A') := box_mono <| by cl_prover;
          simp only [List.mem_cons, forall_eq_or_imp];
          constructor;
          · cl_prover [e₂];
          · intro D hD;
            have := hlA D hD;
            cl_prover [this, e₁];
  obtain ⟨A, hA, hlA⟩ := key l hl;
  have e₁ : ofAxioms 𝔸 ⊢ (B ⋏ □(∼B)) ⋏ (∼A ⋏ □(∼A)) 🡒 ⋀l := right_Conj₂_intro _ _ hlA;
  have e₂ : ofAxioms 𝔸 ⊢ ⋀l 🡒 ⊥ := FiniteContext.provable_iff.mp hb;
  have e₃ : ofAxioms 𝔸 ⊢ (B ⋏ □(∼B)) ▷ (A ⋎ ◇A) :=
    rhd_of_provable (show ofAxioms 𝔸 ⊢ B ⋏ □(∼B) 🡒 A ⋎ ∼□(∼A) by cl_prover [e₁, e₂]);
  have e₄ : ofAxioms 𝔸 ⊢ (A ⋎ ◇A) ▷ A := or_dia_rhd;
  have e₅ : ofAxioms 𝔸 ⊢ B ▷ (B ⋏ □(∼B)) := rhd_and_box_neg;
  have e₆ : ofAxioms 𝔸 ⊢ Axioms.J2 (B ⋏ □(∼B)) (A ⋎ ◇A) A := axiomJ2;
  have e₇ : ofAxioms 𝔸 ⊢ Axioms.J2 B (B ⋏ □(∼B)) A := axiomJ2;
  exact h <| antecedents_of_rhd_mem (mem_of_theorem (by cl_prover [e₃, e₄, e₅, e₆, e₇])) hA

/-- If $B ▷ \bigvee_{G ∈ S'} ¬G \notin Γ$ for every finite $S' \subseteq S$, then `Γ` has an
`S`-assuring successor containing `B` and `□∼B`. -/
lemma exists_assuringSuccessor (h : B ∉ Γ.antecedents S) :
    ∃ Δ, AssuringSuccessor S Γ Δ ∧ B ∈ Δ ∧ □(∼B) ∈ Δ := by
  obtain ⟨Δ, hΔ⟩ := exists_superset (consistent_of_not_mem_antecedents h);
  use Δ;
  and_intros;
  · intro A hA;
    exact ⟨hΔ <| .inr <| .inr ⟨A, hA, .inl rfl⟩, hΔ <| .inr <| .inr ⟨A, hA, .inr rfl⟩⟩;
  · exact hΔ <| .inl rfl;
  · exact hΔ <| .inr <| .inl rfl;

/-- - [MV20, Lemma 7] -/
lemma exists_assuringSuccessor_of_rhd_not_mem (h : B ▷ C ∉ Γ) :
    ∃ Δ, AssuringSuccessor {∼C} Γ Δ ∧ B ∈ Δ ∧ □(∼B) ∈ Δ := by
  apply exists_assuringSuccessor;
  rintro ⟨U, hU, hB⟩;
  apply h <| mem_of_imp (rhd_mono_right <| left_Fdisj_intro _ _) hB;
  intro D hD;
  obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hD;
  obtain rfl : G = ∼C := hU hG;
  exact Entailment.dne;

/-- - [MV20, Lemma 8] -/
lemma AssuringSuccessor.exists_of_rhd_mem (hBC : B ▷ C ∈ Γ) (h : AssuringSuccessor S Γ Δ)
    (hB : B ∈ Δ) : ∃ Θ, AssuringSuccessor S Γ Θ ∧ C ∈ Θ ∧ □(∼C) ∈ Θ := by
  apply exists_assuringSuccessor;
  intro hC;
  exact not_mem_of_neg_mem (h B (antecedents_of_rhd_mem hBC hC)).1 hB

/-! ### Labelling lemmas -/

lemma exists_of_subset_boxLabel {U : Finset (Formula α)} (hU : ↑U ⊆ Γ.boxLabel S) :
    ∃ B ∈ Γ.antecedents S, ofAxioms 𝔸 ⊢ (U.image (∼·)).disj 🡒 ◇B := by
  induction U using Finset.induction_on with
  | empty =>
    use ⊥;
    and_intros;
    · exact bot_mem_antecedents;
    · exact left_Fdisj_intro _ (by simp);
  | @insert G U _ ih =>
    obtain ⟨B, hB, hUB⟩ := ih <| (Finset.coe_subset.mpr (Finset.subset_insert _ _)).trans hU;
    obtain ⟨B', hB', rfl⟩ := hU (Finset.mem_insert_self G U);
    use B ⋎ B';
    and_intros;
    · exact or_mem_antecedents hB hB';
    · have e₁ : ofAxioms 𝔸 ⊢ □(∼(B ⋎ B')) 🡒 □(∼B) := box_mono <| by cl_prover;
      have e₂ : ofAxioms 𝔸 ⊢ □(∼(B ⋎ B')) 🡒 □(∼B') := box_mono <| by cl_prover;
      have e₃ : ofAxioms 𝔸 ⊢
          (insert (∼□(∼B')) (U.image (∼·))).disj 🡒 ∼□(∼B') ⋎ (U.image (∼·)).disj :=
        CinsertFDisjAFDisj;
      have e₄ : ofAxioms 𝔸 ⊢ (U.image (∼·)).disj 🡒 ∼□(∼B) := hUB;
      rw [Finset.image_insert];
      change ofAxioms 𝔸 ⊢ _ 🡒 ∼□(∼(B ⋎ B'));
      cl_prover [e₁, e₂, e₃, e₄];

/-- - [MV20, Lemma 21] -/
lemma AssuringSuccessor.boxLabel_of_axiomP₀ (hP₀ : ∀ {A B : Formula α}, ofAxioms 𝔸 ⊢ Axioms.P₀ A B)
    (h₁ : AssuringSuccessor ∅ Γ Δ) (h₂ : AssuringSuccessor S Δ Θ) :
    AssuringSuccessor (Δ.boxLabel S) Γ Θ := by
  rintro A ⟨U, hU, hA⟩;
  obtain ⟨B, hB, hUB⟩ := exists_of_subset_boxLabel hU;
  have h₃ : □(A ▷ B) ∈ Γ := mem_of_imp hP₀ <| mem_of_imp (rhd_mono_right hUB) hA;
  exact h₂ A <| antecedents_of_rhd_mem (h₁.box_mem_of_box_mem h₃).1 hB

/-- - [GBJM20, Lemma 6.4] -/
lemma AssuringSuccessor.union_boxLabel_of_axiomM₀
    (hM₀ : ∀ {A B C : Formula α}, ofAxioms 𝔸 ⊢ Axioms.M₀ A B C)
    (h₁ : AssuringSuccessor S Γ Δ) (h₂ : AssuringSuccessor ∅ Δ Θ) :
    AssuringSuccessor (S ∪ Δ.boxLabel ∅) Γ Θ := by
  classical
  rintro A ⟨U, hU, hA⟩;
  have hU₂ : ↑(U.filter (· ∉ S)) ⊆ Δ.boxLabel ∅ := by
    intro G hG;
    rw [Finset.mem_coe, Finset.mem_filter] at hG;
    exact (hU hG.1).resolve_left hG.2;
  obtain ⟨B, hB, hUB⟩ := exists_of_subset_boxLabel hU₂;
  have e₁ : ofAxioms 𝔸 ⊢ (U.image (∼·)).disj 🡒
      ((U.filter (· ∈ S)).image (∼·)).disj ⋎ ((U.filter (· ∉ S)).image (∼·)).disj := by
    have hU' : U.image (∼·) = (U.filter (· ∈ S)).image (∼·) ∪ (U.filter (· ∉ S)).image (∼·) := by
      rw [← Finset.image_union, Finset.filter_union_filter_not_eq];
    rw [hU'];
    exact CFdisjUnionAFdisj;
  have e₂ : ofAxioms 𝔸 ⊢ Axioms.M₀ A (((U.filter (· ∈ S)).image (∼·)).disj ⋎ ◇B) (∼B) := hM₀;
  have e₃ := rhd_mono_right (𝔸 := 𝔸) (C := ◇A ⋏ □(∼B))
    (show ofAxioms 𝔸 ⊢ (((U.filter (· ∈ S)).image (∼·)).disj ⋎ ∼□(∼B)) ⋏ □(∼B) 🡒
      ((U.filter (· ∈ S)).image (∼·)).disj by cl_prover);
  have e₄ := rhd_mono_right (𝔸 := 𝔸) (C := A)
    (show ofAxioms 𝔸 ⊢ (U.image (∼·)).disj 🡒 ((U.filter (· ∈ S)).image (∼·)).disj ⋎ ◇B by
      cl_prover [e₁, hUB]);
  have h₃ : ◇A ⋏ □(∼B) ∈ Γ.antecedents S := by
    use U.filter (· ∈ S);
    and_intros;
    · intro G hG;
      rw [Finset.mem_coe, Finset.mem_filter] at hG;
      exact hG.2;
    · exact mem_of_imp (by cl_prover [e₂, e₃, e₄]) hA;
  have h₄ : □(∼B) ∈ Δ := mem_antecedents_empty_iff.mp hB;
  have h₅ : □(∼A) ∈ Δ :=
    mem_of_imp₂ (show ofAxioms 𝔸 ⊢ ∼(∼□(∼A) ⋏ □(∼B)) 🡒 □(∼B) 🡒 □(∼A) by cl_prover)
      (h₁ _ h₃).1 h₄;
  exact h₂ A (mem_antecedents_empty_iff.mpr h₅)

/-- - [MV20, Lemma 24] -/
lemma AssuringSuccessor.union_boxLabel_of_axiomR
    (hR : ∀ {A B C : Formula α}, ofAxioms 𝔸 ⊢ Axioms.R A B C)
    (h₁ : AssuringSuccessor S Γ Δ) (h₂ : AssuringSuccessor T Δ Θ) :
    AssuringSuccessor (S ∪ Δ.boxLabel T) Γ Θ := by
  classical
  rintro A ⟨U, hU, hA⟩;
  have hU₂ : ↑(U.filter (· ∉ S)) ⊆ Δ.boxLabel T := by
    intro G hG;
    rw [Finset.mem_coe, Finset.mem_filter] at hG;
    exact (hU hG.1).resolve_left hG.2;
  obtain ⟨B, hB, hUB⟩ := exists_of_subset_boxLabel hU₂;
  have e₁ : ofAxioms 𝔸 ⊢ (U.image (∼·)).disj 🡒
      ((U.filter (· ∈ S)).image (∼·)).disj ⋎ ((U.filter (· ∉ S)).image (∼·)).disj := by
    have hU' : U.image (∼·) = (U.filter (· ∈ S)).image (∼·) ∪ (U.filter (· ∉ S)).image (∼·) := by
      rw [← Finset.image_union, Finset.filter_union_filter_not_eq];
    rw [hU'];
    exact CFdisjUnionAFdisj;
  have e₂ : ofAxioms 𝔸 ⊢ Axioms.R A (((U.filter (· ∈ S)).image (∼·)).disj ⋎ ◇B) (∼B) := hR;
  have e₃ : ofAxioms 𝔸 ⊢ ∼(A ▷ B) 🡒 ∼(A ▷ ∼∼B) := by
    have := rhd_mono_right (𝔸 := 𝔸) (C := A) (Entailment.dne (φ := B));
    cl_prover [this];
  have e₄ : ofAxioms 𝔸 ⊢ ∼(A ▷ ∼∼B) ▷ ((((U.filter (· ∈ S)).image (∼·)).disj ⋎ ◇B) ⋏ □(∼B)) 🡒
      ∼(A ▷ B) ▷ ((U.filter (· ∈ S)).image (∼·)).disj := by
    have h₅ := rhd_anti_left (C := (((U.filter (· ∈ S)).image (∼·)).disj ⋎ ◇B) ⋏ □(∼B)) e₃;
    have h₆ := rhd_mono_right (𝔸 := 𝔸) (C := ∼(A ▷ B))
      (show ofAxioms 𝔸 ⊢ (((U.filter (· ∈ S)).image (∼·)).disj ⋎ ∼□(∼B)) ⋏ □(∼B) 🡒
        ((U.filter (· ∈ S)).image (∼·)).disj by cl_prover);
    cl_prover [h₅, h₆];
  have e₅ := rhd_mono_right (𝔸 := 𝔸) (C := A)
    (show ofAxioms 𝔸 ⊢ (U.image (∼·)).disj 🡒 ((U.filter (· ∈ S)).image (∼·)).disj ⋎ ◇B by
      cl_prover [e₁, hUB]);
  have h₃ : ∼(A ▷ B) ∈ Γ.antecedents S := by
    use U.filter (· ∈ S);
    and_intros;
    · intro G hG;
      rw [Finset.mem_coe, Finset.mem_filter] at hG;
      exact hG.2;
    · exact mem_of_imp (by cl_prover [e₂, e₄, e₅]) hA;
  exact h₂ A <| antecedents_of_rhd_mem (mem_of_imp Entailment.dne (h₁ _ h₃).1) hB

/-- - [MV20, Lemma 27] -/
lemma AssuringSuccessor.exists_of_rhd_mem_of_axiomW
    (hW : ∀ {A B : Formula α}, ofAxioms 𝔸 ⊢ Axioms.W A B)
    (hBC : B ▷ C ∈ Γ) (h : AssuringSuccessor S Γ Δ) (hB : B ∈ Δ) :
    ∃ Θ, AssuringSuccessor (S ∪ {□(∼B)}) Γ Θ ∧ C ∈ Θ ∧ □(∼C) ∈ Θ := by
  classical
  apply exists_assuringSuccessor;
  rintro ⟨U, hU, hC⟩;
  have e₁ : ofAxioms 𝔸 ⊢ (U.image (∼·)).disj 🡒 ((U.filter (· ∈ S)).image (∼·)).disj ⋎ ◇B := by
    apply left_Fdisj_intro;
    intro ψ hψ;
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hψ;
    by_cases hGS : G ∈ S;
    · have : ofAxioms 𝔸 ⊢ ∼G 🡒 ((U.filter (· ∈ S)).image (∼·)).disj :=
        right_Fdisj_intro _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hG, hGS⟩));
      cl_prover [this];
    · obtain rfl : G = □(∼B) := by simpa [hGS] using hU hG;
      exact or₂;
  have e₂ : ofAxioms 𝔸 ⊢ Axioms.W B (((U.filter (· ∈ S)).image (∼·)).disj ⋎ ◇B) := hW;
  have e₃ := rhd_mono_right (𝔸 := 𝔸) (C := B)
    (show ofAxioms 𝔸 ⊢ (((U.filter (· ∈ S)).image (∼·)).disj ⋎ ∼□(∼B)) ⋏ □(∼B) 🡒
      ((U.filter (· ∈ S)).image (∼·)).disj by cl_prover);
  have e₄ : ofAxioms 𝔸 ⊢ Axioms.J2 B C (((U.filter (· ∈ S)).image (∼·)).disj ⋎ ◇B) := axiomJ2;
  have e₅ := rhd_mono_right (𝔸 := 𝔸) (C := C) e₁;
  have h₁ : B ∈ Γ.antecedents S := by
    use U.filter (· ∈ S);
    and_intros;
    · intro G hG;
      rw [Finset.mem_coe, Finset.mem_filter] at hG;
      exact hG.2;
    · exact mem_of_imp₂ (by cl_prover [e₂, e₃, e₄, e₅]) hBC hC;
  exact not_mem_of_neg_mem (h B h₁).1 hB

end

end MaximalConsistentTheory

end FFL.InterpretabilityLogic

end
