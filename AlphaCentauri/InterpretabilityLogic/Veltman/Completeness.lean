module

public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentSet
public import AlphaCentauri.InterpretabilityLogic.Veltman.ILMinus
public import Mathlib.Data.Set.Finite.List

/-!
# Completeness of $\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$ and $\mathbf{IL}$

A finite Veltman model whose worlds are maximal consistent subsets of an adequate set indexed by
finite sequences of formulas, and the truth lemma for it, for every extension of
$\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$ by axioms. For
$\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$ and $\mathbf{IL}$ this gives completeness with respect
to finite $\mathbf{IL}^-$-frames satisfying the frame conditions of their axioms, and for
$\mathbf{IL}$ completeness with respect to finite Veltman models.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula MaximalConsistentSet Logic

namespace Veltman

variable {α : Type*} [DecidableEq α] {L : Logic α} {Φ : Finset (Formula α)}

/-- A maximal consistent subset of `Φ` together with a finite sequence of antecedents and
consequents of `▷`-formulas in `Φ`, no longer than the number of `□`-formulas in the set.

- [dJV90, Theorem 4.1]
-/
structure IndexedSet (L : Logic α) (Φ : Finset (Formula α)) where
  set : MaximalConsistentSet L Φ
  seq : List (Formula α)
  isRhdOperand_of_mem_seq : ∀ A ∈ seq, IsRhdOperand Φ A
  length_seq_le : seq.length ≤ set.prebox.card

namespace IndexedSet

variable {x y z w : IndexedSet L Φ}

lemma ext {x y : IndexedSet L Φ} (h₁ : x.set = y.set) (h₂ : x.seq = y.seq) : x = y := by
  cases x; cases y; simp_all;

instance [Adequate Φ] : Finite (IndexedSet L Φ) := by
  have : Finite {l : List Φ // l.length ≤ Φ.card} := (List.finite_length_le _ _).to_subtype;
  have hc (Γ : MaximalConsistentSet L Φ) : Γ.prebox.card ≤ Φ.card :=
    Finset.card_le_card_of_injOn (□·) (fun _ hA ↦ mem_of_mem (mem_prebox.mp hA))
      fun _ _ _ _ h ↦ box_inj.mp h;
  apply Finite.of_injective (β := MaximalConsistentSet L Φ × {l : List Φ // l.length ≤ Φ.card})
    fun x ↦ (x.set, ⟨x.seq.pmap Subtype.mk fun A hA ↦ (x.isRhdOperand_of_mem_seq A hA).mem,
      by simpa using x.length_seq_le.trans (hc x.set)⟩);
  intro x y h;
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h;
  apply ext h.1;
  simpa [List.map_pmap] using congrArg (List.map Subtype.val) h.2;

instance [Entailment.Cl L] [Entailment.Consistent L] : Nonempty (IndexedSet L Φ) := by
  obtain ⟨Γ, -⟩ := exists_consistent_union (Φ := Φ) (L := L) (X := ∅) <| by
    intro h;
    exact Entailment.Consistent.not_inconsistent (𝓢 := L) fun _ ↦ efq ⨀ Context.emptyPrf h;
  exact ⟨⟨Γ, [], by simp, by simp⟩⟩

/-- `y` extends `x`: the set of `y` is a successor of the set of `x`, and the sequence of `x` is an
initial segment of the sequence of `y`. -/
def Rel (x y : IndexedSet L Φ) : Prop := Successor x.set y.set ∧ x.seq <+: y.seq

/-- `x` and `y` extend `w`, and whenever `x` is a `C`-critical successor of `w` containing `□∼C`
and indexed by `C` after the sequence of `w`, so is `y`, which moreover does not contain `C`.

- [KO21, Theorem 5.4]
-/
def S (w x y : IndexedSet L Φ) : Prop :=
  (w.Rel x ∧ w.Rel y) ∧ ∀ C, w.seq ++ [C] <+: x.seq → CriticalSuccessor C w.set x.set →
    □(∼C) ∈ x.set → w.seq ++ [C] <+: y.seq ∧ CriticalSuccessor C w.set y.set ∧ C ∉ y.set ∧
      □(∼C) ∈ y.set

namespace S

variable {w x y z : IndexedSet L Φ}

lemma trans (h₁ : S w x y) (h₂ : S w y z) : S w x z := by
  constructor;
  · exact ⟨h₁.1.1, h₂.1.2⟩;
  · intro C h₃ h₄ h₅;
    obtain ⟨h₆, h₇, -, h₈⟩ := h₁.2 C h₃ h₄ h₅;
    exact h₂.2 C h₆ h₇ h₈;

lemma of_rel [Entailment.Cl L] (h₁ : w.Rel x) (h₂ : x.Rel y) : S w x y := by
  constructor;
  · exact ⟨h₁, h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩;
  · intro C h₃ h₄ h₅;
    exact ⟨h₃.trans h₂.2, h₄.trans_successor h₂.1, h₂.1.not_mem_of_box_neg_mem h₅,
      h₂.1.box_mem_of_box_mem h₅⟩;

/-- If `L` proves `C ▷ C` for every `C`, then `S w x y` holds as soon as `x` and `y` extend `w` and
`y` is a `C`-critical successor of `w` indexed by `C` after the sequence of `w` whenever `x` is. -/
lemma of_rhd_refl [Entailment.Cl L] [Adequate Φ] (hL : ∀ {A}, L ⊢ A ▷ A) (hx : w.Rel x)
    (hy : w.Rel y) (h : ∀ C, w.seq ++ [C] <+: x.seq → CriticalSuccessor C w.set x.set →
      w.seq ++ [C] <+: y.seq ∧ CriticalSuccessor C w.set y.set) : S w x y := by
  constructor;
  · exact ⟨hx, hy⟩;
  · intro C h₁ h₂ _;
    have hC : IsRhdOperand Φ C := x.isRhdOperand_of_mem_seq C <| h₁.subset (by simp);
    have hCC : C ▷ C ∈ w.set :=
      (mem_iff_provable (Adequate.rhd_mem hC hC)).mpr <| Context.of hL;
    obtain ⟨h₃, h₄⟩ := h C h₁ h₂;
    exact ⟨h₃, h₄, h₄.not_mem hCC, h₄.box_neg_mem hCC⟩;

lemma refl [Entailment.Cl L] [Adequate Φ] (hL : ∀ {A}, L ⊢ A ▷ A) (h : w.Rel x) : S w x x :=
  of_rhd_refl hL h h fun _ h₁ h₂ ↦ ⟨h₁, h₂⟩

end S

/-- The set `Δ` indexed by the sequence of `x`. -/
def successor (x : IndexedSet L Φ) (Δ : MaximalConsistentSet L Φ) (h : Successor x.set Δ) :
    IndexedSet L Φ :=
  ⟨Δ, x.seq, x.isRhdOperand_of_mem_seq,
    x.length_seq_le.trans (Finset.card_le_card h.prebox_ssubset.subset)⟩

/-- The set `Δ` indexed by the sequence of `x` followed by `F`. -/
def criticalSuccessor (x : IndexedSet L Φ) (F : Formula α) (hF : IsRhdOperand Φ F)
    (Δ : MaximalConsistentSet L Φ) (h : Successor x.set Δ) : IndexedSet L Φ :=
  ⟨Δ, x.seq ++ [F], fun A hA ↦ by
      rcases List.mem_append.mp hA with hA | hA;
      · exact x.isRhdOperand_of_mem_seq A hA;
      · obtain rfl := List.mem_singleton.mp hA;
        exact hF,
    by simpa using Nat.succ_le_of_lt <| x.length_seq_le.trans_lt <|
      Finset.card_lt_card h.prebox_ssubset⟩

end IndexedSet

open IndexedSet

/-- - [dJV90, Theorem 4.1]
- [KO21, Theorem 5.4]
-/
def countermodel (L : Logic α) (Φ : Finset (Formula α)) [Nonempty (IndexedSet L Φ)] :
    Model (IndexedSet L Φ) α where
  Rel' := IndexedSet.Rel
  S' := IndexedSet.S
  Val' x a := #a ∈ x.set

namespace countermodel

open Model Model.World

variable [Nonempty (IndexedSet L Φ)]

instance [Adequate Φ] : (countermodel L Φ).IsILMinus where
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  cwf := by
    have : IsTrans _ (flip (countermodel L Φ).Rel) :=
      ⟨fun _ _ _ h₁ h₂ ↦ ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩⟩;
    have : Std.Irrefl (flip (countermodel L Φ).Rel) := ⟨fun _ h ↦ h.1.irrefl⟩;
    exact Finite.wellFounded_of_trans_of_irrefl _;
  rel_of_s_left h := h.1.1

instance : (countermodel L Φ).IsJ2 where
  rel_of_s_right h := h.1.2
  s_trans := S.trans

variable [Entailment.Cl L]

instance : (countermodel L Φ).IsJ5 := ⟨S.of_rel⟩

instance [Adequate Φ] [ILMinusJ1 ⪯ L] : (countermodel L Φ).IsJ1 :=
  ⟨S.refl <| WeakerThan.pbl (𝓢 := ILMinusJ1) ILMinusJ1.axiomJ1'⟩

instance [Adequate Φ] [ILMinusJ1 ⪯ L] : (countermodel L Φ).IsIL where
  rel_of_s_left := IsILMinus.rel_of_s_left
  rel_of_s_right := IsJ4.rel_of_s_right
  s_refl := IsJ1.s_refl
  s_trans := IsJ2.s_trans
  s_of_rel := IsJ5.s_of_rel

variable {𝔸 : Set (Formula α)} [Nonempty (IndexedSet (ofAxiomsMinus 𝔸) Φ)] [ILMinusAdequate Φ]
  [ILMinusJ2Plus ⪯ ofAxiomsMinus 𝔸] [ILMinusJ5 ⪯ ofAxiomsMinus 𝔸]

/-- - [dJV90, Theorem 4.1]
- [KO21, Lemma 5.6]
-/
lemma truthlemma {x : (countermodel (ofAxiomsMinus 𝔸) Φ).World} {A : Formula α} (hA : A ∈ Φ) :
    x ⊩ A ↔ A ∈ x.set := by
  induction A generalizing x with
  | atom a => rfl;
  | falsum => exact ⟨False.elim, fun h ↦ bot_not_mem h⟩;
  | imp A B ihA ihB =>
    have hA' := Adequate.imp_left hA;
    have hB' := Adequate.imp_right hA;
    rw [imp_mem_iff hA hA' hB', ← ihA hA', ← ihB hB'];
    rfl;
  | box A ih =>
    have hA' := Adequate.box hA;
    constructor;
    · intro h;
      by_contra hn;
      obtain ⟨Δ, hΔ, hA⟩ := exists_successor_of_box_not_mem hA hn;
      exact not_mem_of_provable_neg hA (Context.by_axm rfl) <|
        (ih hA').mp <| h (x.successor Δ hΔ) ⟨hΔ, List.prefix_refl _⟩;
    · intro h y Rxy;
      exact (ih hA').mpr <| Rxy.1.mem_of_box_mem h;
  | rhd B C ihB ihC =>
    have hB := Adequate.rhd_left hA;
    have hC := Adequate.rhd_right hA;
    have : ILMinusJ2 ⪯ ofAxiomsMinus 𝔸 :=
      WeakerThan.trans (𝓣 := ILMinusJ2Plus) inferInstance inferInstance;
    constructor;
    · intro h;
      by_contra hn;
      obtain ⟨Δ, hΔ, hBΔ, hCΔ⟩ := exists_criticalSuccessor_box_neg_of_rhd_not_mem hA hn;
      obtain ⟨v, hS, hv⟩ := h (x.criticalSuccessor C (.of_rhd_right hA) Δ hΔ.toSuccessor)
        ⟨hΔ.toSuccessor, List.prefix_append _ _⟩ ((ihB hB).mpr hBΔ);
      exact (hS.2 C (List.prefix_refl _) hΔ hCΔ).2.2.1 <| (ihC hC).mp hv;
    · intro h u Rxu hu;
      replace hu := (ihB hB).mp hu;
      by_cases hc : ∃ F, x.seq ++ [F] <+: u.seq ∧ CriticalSuccessor F x.set u.set ∧
          □(∼F) ∈ u.set;
      · obtain ⟨F, hpre, hcrit, -⟩ := hc;
        have hF : IsRhdOperand Φ F := u.isRhdOperand_of_mem_seq F <| hpre.subset (by simp);
        obtain ⟨Θ, hΘ, hCΘ, hFΘ, hbΘ⟩ :=
          hcrit.weakCriticalSuccessor.exists_criticalSuccessor_box_neg_mem_not_mem hF h hu;
        use x.criticalSuccessor F hF Θ hΘ.toSuccessor;
        and_intros;
        · exact Rxu.1;
        · exact Rxu.2;
        · exact hΘ.toSuccessor;
        · exact List.prefix_append _ _;
        · intro C' hpre' _ _;
          have h₁ : x.seq ++ [C'] = x.seq ++ [F] :=
            (List.prefix_of_prefix_length_le hpre' hpre (by simp)).eq_of_length (by simp);
          obtain rfl : C' = F := by simpa using h₁;
          exact ⟨List.prefix_refl _, hΘ, hFΘ, hbΘ⟩;
        · exact (ihC hC).mpr hCΘ;
      · have hbot := Rxu.1.criticalSuccessor_bot <| K_right ofAxiomsMinus.box_neg_iff_rhd_bot;
        obtain ⟨Θ, hΘ, hCΘ, -⟩ :=
          hbot.weakCriticalSuccessor.exists_criticalSuccessor_box_neg_mem_not_mem .bot h hu;
        use x.successor Θ hΘ.toSuccessor;
        and_intros;
        · exact Rxu.1;
        · exact Rxu.2;
        · exact hΘ.toSuccessor;
        · exact List.prefix_refl _;
        · intro C' hpre' hcrit' hbox';
          exact (hc ⟨C', hpre', hcrit', hbox'⟩).elim;
        · exact (ihC hC).mpr hCΘ;

end countermodel

end Veltman

/-! ### Completeness -/

namespace Logic.ofAxiomsMinus

open Veltman Veltman.Model.World

variable {α : Type*} [DecidableEq α] {𝔸 : Set (Formula α)} {Φ : Finset (Formula α)}
  {A : Formula α}

/-- If an extension of $\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$ does not prove `A`, then `A`
fails at some world of the countermodel over an adequate set containing `A`.

- [KO21, Theorem 5.4]
-/
lemma not_models_countermodel [ILMinusJ2Plus ⪯ ofAxiomsMinus 𝔸] [ILMinusJ5 ⪯ ofAxiomsMinus 𝔸]
    [Entailment.Consistent (ofAxiomsMinus 𝔸)] (h : ofAxiomsMinus 𝔸 ⊬ A) :
    ¬countermodel (ofAxiomsMinus 𝔸) (ilMinusAdequateClosure {A}) ⊧ A := by
  intro hM;
  have hX : ({∼A} : Set (Formula α)) *⊬[ofAxiomsMinus 𝔸] ⊥ := by
    intro h₁;
    apply h;
    have h₂ : ofAxiomsMinus 𝔸 ⊢ ∼A 🡒 ⊥ := Context.emptyPrf <| Context.deduct <| by simpa using h₁;
    cl_prover [h₂];
  obtain ⟨Γ, hΓ⟩ := exists_consistent_union (Φ := ilMinusAdequateClosure {A}) hX;
  have hA : A ∈ ilMinusAdequateClosure {A} := ilMinusAdequateClosure.subset (by simp);
  exact not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (countermodel.truthlemma hA).mp <| hM ⟨Γ, [], by simp, by simp⟩

end Logic.ofAxiomsMinus

namespace Logic

open Veltman Veltman.Model

universe u

variable {α : Type u} {A : Formula α}

/-- - [KO21, Theorem 5.4] -/
theorem ILMinusJ2PlusJ5.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ2PlusJ5 ⊢ A := by
  classical
  by_contra hA;
  have : Entailment.Consistent (ILMinusJ2PlusJ5 : Logic α) := .of_unprovable hA;
  exact ofAxiomsMinus.not_models_countermodel hA <|
    h (countermodel ILMinusJ2PlusJ5 (ilMinusAdequateClosure {A}))

/-- - [KO21, Theorem 5.4] -/
theorem IL.complete_ILMinus
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ2] → [M.IsJ5] → M ⊧ A) :
    𝐈𝐋 ⊢ A := by
  classical
  rw [IL.eq_ofAxiomsMinus];
  by_contra hA;
  have : Entailment.Consistent (ofAxiomsMinus
      ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A})) :=
    .of_unprovable hA;
  have : (ILMinusJ1 : Logic α) ⪯ ofAxiomsMinus
      ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A}) :=
    weakerThan_iff.mpr <| ofAxiomsMinus.subset_of_subset <|
      Set.subset_union_left.trans Set.subset_union_left;
  have : (ILMinusJ5 : Logic α) ⪯ ofAxiomsMinus
      ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A}) :=
    weakerThan_iff.mpr <| ofAxiomsMinus.subset_of_subset Set.subset_union_right;
  have : (ILMinusJ2Plus : Logic α) ⪯ ofAxiomsMinus
      ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A}) :=
    weakerThan_iff.mpr <| ofAxiomsMinus.subset_of_provable <| by
      rintro _ ⟨A, B, C, rfl⟩;
      exact ofAxiomsMinus.subset_of_subset Set.subset_union_left CL.axiomJ2Plus;
  exact ofAxiomsMinus.not_models_countermodel hA <| h (countermodel _ (ilMinusAdequateClosure {A}))

/-- - [dJV90, Theorem 4.1] -/
theorem IL.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A) :
    𝐈𝐋 ⊢ A := by
  apply IL.complete_ILMinus;
  intro κ _ _ M _ _ _ _;
  have : M.IsIL := {
    rel_of_s_left := IsILMinus.rel_of_s_left
    rel_of_s_right := IsJ4.rel_of_s_right
    s_refl := IsJ1.s_refl
    s_trans := IsJ2.s_trans
    s_of_rel := IsJ5.s_of_rel };
  exact h M

end Logic

end FFL.InterpretabilityLogic

end
