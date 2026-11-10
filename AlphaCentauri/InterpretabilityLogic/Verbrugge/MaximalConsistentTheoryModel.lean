module

public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentTheory
public import AlphaCentauri.InterpretabilityLogic.Logic.ILR.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILPZero.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Basic

/-!
# The model on maximal consistent theories

A generalised Veltman model whose worlds are maximal consistent sets of all formulas, and the truth
lemma for it, for every extension of $\mathbf{IL}$ by axioms. The model satisfies the frame
condition for $\mathsf{P}_0$ or $\mathsf{R}$ when the logic proves that principle; this gives the
completeness of $\mathbf{ILP}_0$ and $\mathbf{ILR}$ with respect to generalised Veltman models.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula MaximalConsistentTheory

namespace Verbrugge

variable {α : Type*} [DecidableEq α] {𝔸 : Set (Formula α)} {A₀ : Formula α}

/-- The subformulas of `A₀` and their negations. -/
def markers (A₀ : Formula α) : Finset (Formula α) :=
  A₀.subformulas ∪ A₀.subformulas.image (∼·)

lemma mem_markers_of_mem {G : Formula α} (h : G ∈ A₀.subformulas) : G ∈ markers A₀ :=
  Finset.mem_union_left _ h

lemma neg_mem_markers_of_mem {G : Formula α} (h : G ∈ A₀.subformulas) : ∼G ∈ markers A₀ :=
  Finset.mem_union_right _ <| Finset.mem_image_of_mem _ h

/-- The maximal consistent sets containing `G` and `□∼G` for some subformula `G` of `A₀` or
negation of one.

- [MV20, Definition 9]
-/
def CountermodelWorld (𝔸 : Set (Formula α)) (A₀ : Formula α) : Type _ :=
  {Γ : MaximalConsistentTheory (Logic.ofAxioms 𝔸) // ∃ G ∈ markers A₀, G ∈ Γ ∧ □(∼G) ∈ Γ}

/-- The generalised Veltman model on `CountermodelWorld 𝔸 A₀` in which `u ≺[w] V` holds when `u`
and the elements of `V` are successors of `w` and every `S`-assuring successor `u` of `w` has an
`S`-assuring successor of `w` in `V`.

- [MV20, Definition 9]
-/
def countermodel (𝔸 : Set (Formula α)) (A₀ : Formula α) [Nonempty (CountermodelWorld 𝔸 A₀)] :
    Model (CountermodelWorld 𝔸 A₀) α where
  Rel' w u := AssuringSuccessor ∅ w.1 u.1
  S' w u V := AssuringSuccessor ∅ w.1 u.1 ∧ (∀ v ∈ V, AssuringSuccessor ∅ w.1 v.1) ∧
    ∀ S, AssuringSuccessor S w.1 u.1 → ∃ v ∈ V, AssuringSuccessor S w.1 v.1
  Val' w a := #a ∈ w.1

namespace countermodel

open Model Model.World

variable [Nonempty (CountermodelWorld 𝔸 A₀)]

/-- - [MV20, Lemma 11] -/
instance : (countermodel 𝔸 A₀).IsIL where
  trans _ _ _ h₁ h₂ := h₁.trans_successor h₂
  cwf := by
    classical
    let m : CountermodelWorld 𝔸 A₀ → ℕ := fun w ↦
      (markers A₀).card - ((markers A₀).filter (fun G ↦ □(∼G) ∈ w.1)).card;
    apply Subrelation.wf _ (measure m).wf;
    intro u w (h : AssuringSuccessor ∅ w.1 u.1);
    obtain ⟨G, hG, hGu, hGu'⟩ := u.2;
    have hs : (markers A₀).filter (fun G ↦ □(∼G) ∈ w.1) ⊂
        (markers A₀).filter (fun G ↦ □(∼G) ∈ u.1) := by
      apply (Finset.ssubset_iff_of_subset _).mpr;
      · use G;
        and_intros;
        · exact Finset.mem_filter.mpr ⟨hG, hGu'⟩;
        · intro hGw;
          exact not_mem_of_neg_mem (h.box_mem_of_box_mem (Finset.mem_filter.mp hGw).2).1 hGu;
      · intro H hH;
        obtain ⟨hH, hHw⟩ := Finset.mem_filter.mp hH;
        exact Finset.mem_filter.mpr ⟨hH, (h.box_mem_of_box_mem hHw).2⟩;
    have h₁ := Finset.card_lt_card hs;
    have h₂ := Finset.card_le_card (Finset.filter_subset (fun G ↦ □(∼G) ∈ u.1) (markers A₀));
    change (markers A₀).card - _ < (markers A₀).card - _;
    omega;
  rel_of_s h := h.1
  rel_of_mem_of_s h hv := h.2.1 _ hv
  nonempty_of_s h := by
    obtain ⟨v, hv, -⟩ := h.2.2 ∅ h.1;
    use v;
  s_refl {w u} h := by
    and_intros;
    · exact h;
    · intro v hv;
      rw [Set.mem_singleton_iff] at hv;
      subst hv;
      exact h;
    · intro S hS;
      use u;
      simpa using hS;
  s_trans {w u V} Z h hZ := by
    and_intros;
    · exact h.1;
    · simp only [Set.mem_iUnion];
      rintro z ⟨v, hv, hz⟩;
      exact (hZ v hv).2.1 z hz;
    · intro S hS;
      obtain ⟨v, hv, hSv⟩ := h.2.2 S hS;
      obtain ⟨z, hz, hSz⟩ := (hZ v hv).2.2 S hSv;
      use z;
      and_intros;
      · simp only [Set.mem_iUnion];
        use v;
      · exact hSz;
  s_of_rel {w u v} h₁ h₂ := by
    and_intros;
    · exact h₁;
    · simpa using h₁.trans_successor h₂;
    · intro S hS;
      use v;
      simpa using hS.trans_successor h₂;
  s_mono {w u V Z} h hVZ hZ := by
    and_intros;
    · exact h.1;
    · exact hZ;
    · intro S hS;
      obtain ⟨v, hv, hSv⟩ := h.2.2 S hS;
      use v;
      and_intros;
      · exact hVZ hv;
      · exact hSv;

/-- - [MV20, Lemma 11] -/
lemma truthlemma {w : (countermodel 𝔸 A₀).World} {A : Formula α} (hA : A ∈ A₀.subformulas) :
    w ⊩ A ↔ A ∈ w.1 := by
  induction A generalizing w with
  | atom a => rfl;
  | falsum => simpa using bot_not_mem;
  | imp A B ihA ihB =>
    have hA' : A ∈ A₀.subformulas := subformulas_subset_of_mem hA (by simp [subformulas]);
    have hB' : B ∈ A₀.subformulas := subformulas_subset_of_mem hA (by simp [subformulas]);
    exact (imp_congr (ihA hA') (ihB hB')).trans imp_mem_iff.symm;
  | box B ihB =>
    have hB : B ∈ A₀.subformulas := subformulas_subset_of_mem hA (by simp [subformulas]);
    constructor;
    · intro h;
      by_contra hb;
      have h₁ : ∼B ∉ w.1.antecedents ∅ := by
        rw [mem_antecedents_empty_iff];
        exact fun h ↦ hb <| mem_of_imp (Logic.box_mono Entailment.dne) h;
      obtain ⟨u, hwu, hu, hu'⟩ := exists_assuringSuccessor h₁;
      exact not_mem_of_neg_mem hu <|
        (ihB hB).mp <| h ⟨u, ∼B, neg_mem_markers_of_mem hB, hu, hu'⟩ hwu;
    · intro h u hwu;
      exact (ihB hB).mpr (hwu.box_mem_of_box_mem h).1;
  | rhd B C ihB ihC =>
    have hB : B ∈ A₀.subformulas := subformulas_subset_of_mem hA (by simp [subformulas]);
    have hC : C ∈ A₀.subformulas := subformulas_subset_of_mem hA (by simp [subformulas]);
    constructor;
    · intro h;
      by_contra hBC;
      obtain ⟨u, hwu, hu, hu'⟩ := exists_assuringSuccessor_of_rhd_not_mem hBC;
      obtain ⟨V, ⟨-, -, hV⟩, hVC⟩ :=
        h ⟨u, B, mem_markers_of_mem hB, hu, hu'⟩ (hwu.mono (Set.empty_subset _)) ((ihB hB).mpr hu);
      obtain ⟨v, hv, hwv⟩ := hV {∼C} hwu;
      exact not_mem_of_neg_mem (hwv.subset (Set.mem_singleton _)) <| (ihC hC).mp (hVC v hv);
    · intro h u hwu hu;
      use {v | w ≺ v ∧ v ⊩ C};
      and_intros;
      · exact hwu;
      · intro v hv;
        exact hv.1;
      · intro S hS;
        obtain ⟨v, hSv, hv, hv'⟩ := hS.exists_of_rhd_mem h ((ihB hB).mp hu);
        use ⟨v, C, mem_markers_of_mem hC, hv, hv'⟩;
        and_intros;
        · exact hSv.mono (Set.empty_subset _);
        · exact (ihC hC).mpr hv;
        · exact hSv;
      · intro v hv;
        exact hv.2;

/-- - [MV20, Theorem 23] -/
lemma hasP₀ (hP₀ : ∀ {A B : Formula α}, Logic.ofAxioms 𝔸 ⊢ Axioms.P₀ A B) :
    (countermodel 𝔸 A₀).HasP₀ where
  exists_subset_of_rel_rel_s {w x u V Z} hwx hxu h hZ := by
    use {z ∈ Z | x ≺ z};
    and_intros;
    · exact Set.sep_subset _ _;
    · exact hxu;
    · intro z hz;
      exact hz.2;
    · intro S hS;
      obtain ⟨v, hv, hwv⟩ := h.2.2 _ (AssuringSuccessor.boxLabel_of_axiomP₀ hP₀ hwx hS);
      obtain ⟨z, hz, hvz⟩ := hZ v hv;
      have hxz : AssuringSuccessor S x.1 z.1 := hwv.of_boxLabel hvz;
      use z;
      and_intros;
      · exact hz;
      · exact hxz.mono (Set.empty_subset _);
      · exact hxz;

/-- - [MV20, Theorem 25] -/
lemma hasR (hR : ∀ {A B C : Formula α}, Logic.ofAxioms 𝔸 ⊢ Axioms.R A B C) :
    (countermodel 𝔸 A₀).HasR where
  exists_subset_of_rel_rel_s {w x u V} hwx hxu h C hC := by
    have aux : ∀ S, AssuringSuccessor S w.1 x.1 →
        ∃ v ∈ V, AssuringSuccessor (S ∪ x.1.boxLabel ∅) w.1 v.1 ∧ ∀ z, v ≺ z → z ∈ C := by
      intro S hS;
      by_contra hn;
      simp only [not_exists, not_and, not_forall] at hn;
      let Z : Set (countermodel 𝔸 A₀).World :=
        {z | z ∉ C ∧ ∃ v ∈ V, AssuringSuccessor (S ∪ x.1.boxLabel ∅) w.1 v.1 ∧ v ≺ z};
      obtain ⟨z, hzZ, hzC⟩ := hC.2 Z <| by
        and_intros;
        · exact hxu;
        · rintro z ⟨-, v, -, hwv, hvz⟩;
          exact (hwv.mono Set.subset_union_right).of_boxLabel hvz;
        · intro T hT;
          obtain ⟨v, hv, hwv⟩ := h.2.2 _ (AssuringSuccessor.union_boxLabel_of_axiomR hR hS hT);
          have hwv' : AssuringSuccessor (S ∪ x.1.boxLabel ∅) w.1 v.1 :=
            hwv.mono <| Set.union_subset_union_right _ <| boxLabel_mono (Set.empty_subset T);
          obtain ⟨z, hvz, hzC⟩ := hn v hv hwv';
          use z;
          and_intros;
          · exact hzC;
          · use v;
          · exact (hwv.mono Set.subset_union_right).of_boxLabel hvz;
      exact hzZ.1 hzC;
    use {v ∈ V | ∀ z, v ≺ z → z ∈ C};
    and_intros;
    · exact Set.sep_subset _ _;
    · exact hwx;
    · intro v hv;
      exact h.2.1 v hv.1;
    · intro S hS;
      obtain ⟨v, hv, hwv, hvC⟩ := aux S hS;
      use v;
      and_intros;
      · exact hv;
      · exact hvC;
      · exact hwv.mono Set.subset_union_left;
    · intro y hy;
      exact hy.2;

end countermodel

end Verbrugge

/-! ### Completeness -/

namespace Logic.ofAxioms

open Verbrugge Verbrugge.Model.World

variable {α : Type*} [DecidableEq α] {𝔸 : Set (Formula α)} {A : Formula α}

omit [DecidableEq α] in
private lemma exists_neg_mem (h : ofAxioms 𝔸 ⊬ A) :
    ∃ Γ : MaximalConsistentTheory (ofAxioms 𝔸), ∼A ∈ Γ ∧ □(∼∼A) ∈ Γ := by
  have hX : (insert (∼A) (insert (□(∼∼A)) ∅) : Set (Formula α)) *⊬[ofAxioms 𝔸] ⊥ := by
    intro h₁;
    apply h;
    have h₂ : ofAxioms 𝔸 ⊢ □(∼∼A) 🡒 ∼∼A :=
      Context.emptyPrf <| Context.deduct <| Context.deduct h₁;
    have h₃ : ofAxioms 𝔸 ⊢ □(∼∼A) := Logic.ExtendsGL.axiomL ⨀ Logic.provable_box h₂;
    exact Entailment.dne ⨀ (h₂ ⨀ h₃);
  obtain ⟨Γ, hΓ⟩ := MaximalConsistentTheory.exists_superset hX;
  use Γ;
  and_intros;
  · exact hΓ (by simp);
  · exact hΓ (by simp);

lemma nonempty_countermodelWorld (h : ofAxioms 𝔸 ⊬ A) : Nonempty (CountermodelWorld 𝔸 A) := by
  obtain ⟨Γ, hΓ, hΓ'⟩ := exists_neg_mem h;
  exact ⟨⟨Γ, ∼A, neg_mem_markers_of_mem mem_subformulas_self, hΓ, hΓ'⟩⟩

/-- If `ofAxioms 𝔸` does not prove `A`, then `A` fails at some world of the countermodel.

- [MV20, Theorem 12]
-/
lemma not_models_verbrugge_countermodel [Nonempty (CountermodelWorld 𝔸 A)] (h : ofAxioms 𝔸 ⊬ A) :
    ¬countermodel 𝔸 A ⊧ A := by
  intro hM;
  obtain ⟨Γ, hΓ, hΓ'⟩ := exists_neg_mem h;
  exact MaximalConsistentTheory.not_mem_of_neg_mem hΓ <|
    (countermodel.truthlemma mem_subformulas_self).mp <|
      hM ⟨Γ, ∼A, neg_mem_markers_of_mem mem_subformulas_self, hΓ, hΓ'⟩

end Logic.ofAxioms

variable {α : Type} {A : Formula α}

/-- - [MV20, Theorem 23] -/
theorem Logic.ILP₀.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α), [M.IsIL] → [M.HasP₀] → M ⊧ A) :
    𝐈𝐋𝐏₀ ⊢ A := by
  classical
  by_contra hA;
  have := Logic.ofAxioms.nonempty_countermodelWorld hA;
  have := Verbrugge.countermodel.hasP₀ (A₀ := A) fun {_ _} ↦ Logic.ILP₀.axiomP₀;
  exact Logic.ofAxioms.not_models_verbrugge_countermodel hA (h _)

/-- - [MV20, Theorem 25] -/
theorem Logic.ILR.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α), [M.IsIL] → [M.HasR] → M ⊧ A) :
    𝐈𝐋𝐑 ⊢ A := by
  classical
  by_contra hA;
  have := Logic.ofAxioms.nonempty_countermodelWorld hA;
  have := Verbrugge.countermodel.hasR (A₀ := A) fun {_ _ _} ↦ Logic.ILR.axiomR;
  exact Logic.ofAxioms.not_models_verbrugge_countermodel hA (h _)

end FFL.InterpretabilityLogic

end
