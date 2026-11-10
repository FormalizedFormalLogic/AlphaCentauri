module

public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentSet
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import Mathlib.Data.Set.Finite.List

/-!
# Completeness of $\mathbf{IL}$ with respect to finite Veltman models

A finite Veltman model whose worlds are maximal consistent subsets of an adequate set indexed by
finite sequences of formulas, and the truth lemma for it, for every extension of $\mathbf{IL}$ by
axioms. For $\mathbf{IL}$ itself this gives completeness with respect to finite Veltman models.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula MaximalConsistentSet

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

/-- `y` extends `x`: the set of `y` is a successor of the set of `x`, and the sequence of `x` is an
initial segment of the sequence of `y`. -/
def Rel (x y : IndexedSet L Φ) : Prop := Successor x.set y.set ∧ x.seq <+: y.seq

/-- `x` and `y` extend `w`, and whenever `x` is a `C`-critical successor of `w` indexed by
`C` after the sequence of `w`, so is `y`.

- [KO21, Theorem 5.4]
-/
def S (w x y : IndexedSet L Φ) : Prop :=
  (w.Rel x ∧ w.Rel y) ∧ ∀ C, w.seq ++ [C] <+: x.seq → CriticalSuccessor C w.set x.set →
    w.seq ++ [C] <+: y.seq ∧ CriticalSuccessor C w.set y.set

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

variable {𝔸 : Set (Formula α)}

/-- - [dJV90, Theorem 4.1] -/
def countermodel (𝔸 : Set (Formula α)) (Φ : Finset (Formula α))
    [Nonempty (IndexedSet (Logic.ofAxioms 𝔸) Φ)] :
    Model (IndexedSet (Logic.ofAxioms 𝔸) Φ) α where
  Rel' := IndexedSet.Rel
  S' := IndexedSet.S
  Val' x a := #a ∈ x.set

namespace countermodel

open Model Model.World

variable [Nonempty (IndexedSet (Logic.ofAxioms 𝔸) Φ)]

instance [Adequate Φ] : (countermodel 𝔸 Φ).IsIL where
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  cwf := by
    have : IsTrans _ (flip (countermodel 𝔸 Φ).Rel) :=
      ⟨fun _ _ _ h₁ h₂ ↦ ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩⟩;
    have : Std.Irrefl (flip (countermodel 𝔸 Φ).Rel) := ⟨fun _ h ↦ h.1.irrefl⟩;
    exact Finite.wellFounded_of_trans_of_irrefl _;
  rel_of_s_left h := h.1.1
  rel_of_s_right h := h.1.2
  s_refl h := ⟨⟨h, h⟩, fun _ h₁ h₂ ↦ ⟨h₁, h₂⟩⟩
  s_trans h₁ h₂ := ⟨⟨h₁.1.1, h₂.1.2⟩, fun C h₃ h₄ ↦
    have h := h₁.2 C h₃ h₄;
    h₂.2 C h.1 h.2⟩
  s_of_rel h₁ h₂ := ⟨⟨h₁, h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩,
    fun _ h₃ h₄ ↦ ⟨h₃.trans h₂.2, h₄.trans_successor h₂.1⟩⟩

variable [Adequate Φ]

/-- - [dJV90, Theorem 4.1]
- [KO21, Lemma 5.6]
-/
lemma truthlemma {x : (countermodel 𝔸 Φ).World} {A : Formula α} (hA : A ∈ Φ) :
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
    constructor;
    · intro h;
      by_contra hn;
      obtain ⟨Δ, hΔ, hBΔ⟩ := exists_criticalSuccessor_of_rhd_not_mem hA hn;
      have hC' : IsRhdOperand Φ C := .of_rhd_right hA;
      obtain ⟨v, hS, hv⟩ := h (x.criticalSuccessor C hC' Δ hΔ.toSuccessor)
        ⟨hΔ.toSuccessor, List.prefix_append _ _⟩ ((ihB hB).mpr hBΔ);
      have hCC : C ▷ C ∈ x.set :=
        (mem_iff_provable (Adequate.rhd_mem hC' hC')).mpr <| Context.of Logic.ofAxioms.rhd_refl;
      exact (hS.2 C (List.prefix_refl _) hΔ).2.not_mem hCC <| (ihC hC).mp hv;
    · intro h u Rxu hu;
      replace hu := (ihB hB).mp hu;
      by_cases hc : ∃ F, x.seq ++ [F] <+: u.seq ∧ CriticalSuccessor F x.set u.set;
      · obtain ⟨F, hpre, hcrit⟩ := hc;
        have hF : IsRhdOperand Φ F := u.isRhdOperand_of_mem_seq F <| hpre.subset (by simp);
        obtain ⟨Θ, hΘ, hCΘ⟩ := hcrit.exists_criticalSuccessor hF h hu;
        use x.criticalSuccessor F hF Θ hΘ.toSuccessor;
        and_intros;
        · exact Rxu.1;
        · exact Rxu.2;
        · exact hΘ.toSuccessor;
        · exact List.prefix_append _ _;
        · intro C' hpre' _;
          have h₁ : x.seq ++ [C'] = x.seq ++ [F] :=
            (List.prefix_of_prefix_length_le hpre' hpre (by simp)).eq_of_length (by simp);
          obtain rfl : C' = F := by simpa using h₁;
          exact ⟨List.prefix_refl _, hΘ⟩;
        · exact (ihC hC).mpr hCΘ;
      · have hbot := Rxu.1.criticalSuccessor_bot Logic.ofAxioms.rhd_bot;
        obtain ⟨Θ, hΘ, hCΘ⟩ := hbot.exists_criticalSuccessor .bot h hu;
        use x.successor Θ hΘ.toSuccessor;
        and_intros;
        · exact Rxu.1;
        · exact Rxu.2;
        · exact hΘ.toSuccessor;
        · exact List.prefix_refl _;
        · intro C' hpre' hcrit';
          exact (hc ⟨C', hpre', hcrit'⟩).elim;
        · exact (ihC hC).mpr hCΘ;

end countermodel

end Veltman

/-! ### Completeness -/

namespace Logic.ofAxioms

open Veltman Veltman.Model.World

variable {α : Type*} [DecidableEq α] {𝔸 : Set (Formula α)} {Φ : Finset (Formula α)}
  {A : Formula α}

instance [Entailment.Consistent (ofAxioms 𝔸)] : Nonempty (IndexedSet (Logic.ofAxioms 𝔸) Φ) := by
  obtain ⟨Γ, -⟩ := exists_consistent_union (Φ := Φ) (L := ofAxioms 𝔸) (X := ∅) <| by
    intro h;
    exact Entailment.Consistent.not_inconsistent (𝓢 := ofAxioms 𝔸) fun _ ↦
      efq ⨀ Context.emptyPrf h;
  exact ⟨⟨Γ, [], by simp, by simp⟩⟩

/-- If `ofAxioms 𝔸` does not prove `A`, then `A` fails at some world of the countermodel over the
adequate closure of `{A}`.

- [dJV90, Theorem 4.1]
-/
lemma not_models_countermodel [Entailment.Consistent (ofAxioms 𝔸)] (h : ofAxioms 𝔸 ⊬ A) :
    ¬countermodel 𝔸 (adequateClosure {A}) ⊧ A := by
  intro hM;
  have hX : ({∼A} : Set (Formula α)) *⊬[ofAxioms 𝔸] ⊥ := by
    intro h₁;
    apply h;
    have h₂ : ofAxioms 𝔸 ⊢ ∼A 🡒 ⊥ := Context.emptyPrf <| Context.deduct <| by simpa using h₁;
    cl_prover [h₂];
  obtain ⟨Γ, hΓ⟩ := exists_consistent_union (Φ := adequateClosure {A}) hX;
  have hA : A ∈ adequateClosure {A} := adequateClosure.subset (by simp);
  exact not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (countermodel.truthlemma hA).mp <| hM ⟨Γ, [], by simp, by simp⟩

end Logic.ofAxioms

namespace Logic.IL

open Veltman

universe u

variable {α : Type u} {A : Formula α}

/-- - [dJV90, Theorem 4.1] -/
theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A) :
    𝐈𝐋 ⊢ A := by
  classical
  by_contra hA;
  have : Entailment.Consistent (𝐈𝐋 : Logic α) := .of_unprovable hA;
  exact Logic.ofAxioms.not_models_countermodel hA <| h (countermodel ∅ (adequateClosure {A}))

/-- - [dJV90, Theorem 4.1] -/
theorem provable_TFAE : [
    𝐈𝐋 ⊢ A,
    ∀ {κ : Type u} [Nonempty κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A,
    ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := fun h _ _ _ _ ↦ Logic.ofAxioms.sound (by simp) h;
  tfae_have 2 → 3 := fun h _ _ _ M _ ↦ h M;
  tfae_have 3 → 1 := complete;
  tfae_finish;

end Logic.IL

end FFL.InterpretabilityLogic

end
