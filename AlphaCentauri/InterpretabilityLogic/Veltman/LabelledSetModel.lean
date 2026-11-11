module

public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentSet
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import Mathlib.Data.Set.Finite.List

/-!
# The model on labelled sets

The construction behind the completeness of $\mathbf{CL}$ with respect to finite Veltman models.

Finite Veltman models whose worlds are maximal consistent subsets of an adequate set labelled by
antecedents and consequents of `▷`-formulas in it, with `≺[w]` given by a condition on the labelled
sets, and the truth lemma for every condition with two existence properties.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section

open Entailment Formula MaximalConsistentSet Logic

namespace Veltman

variable {α : Type*} [DecidableEq α] {L : Logic α} {Φ : Finset (Formula α)}

/-- A maximal consistent subset of `Φ` labelled by an antecedent or consequent of a `▷`-formula in
`Φ`.

- [KO21, Theorem 5.1]
-/
structure LabelledSet (L : Logic α) (Φ : Finset (Formula α)) where
  set : MaximalConsistentSet L Φ
  label : Formula α
  isRhdOperand_label : IsRhdOperand Φ label

namespace LabelledSet

instance [Adequate Φ] : Finite (LabelledSet L Φ) := by
  apply Finite.of_injective (β := MaximalConsistentSet L Φ × Φ)
    fun x ↦ (x.set, ⟨x.label, x.isRhdOperand_label.mem⟩);
  rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h;
  simp_all;

/-- A condition `P Γ Δ C Θ D` on pairs of labelled sets `⟨Δ, C⟩`, `⟨Θ, D⟩` relative to `Γ`, such
that every `▷`-formula in `Γ` has a witness satisfying it, and every `▷`-formula in `Φ` outside `Γ`
has a counterexample all of whose `P`-successors refute the consequent.

- [KO21, Theorem 5.1]
-/
structure Condition (L : Logic α) (Φ : Finset (Formula α)) where
  toFun : MaximalConsistentSet L Φ → MaximalConsistentSet L Φ → Formula α →
    MaximalConsistentSet L Φ → Formula α → Prop
  exists_of_rhd_mem {Γ Δ : MaximalConsistentSet L Φ} {D E F : Formula α} :
    D ▷ E ∈ Γ → Successor Γ Δ → D ∈ Δ → IsRhdOperand Φ F →
      ∃ Θ G, IsRhdOperand Φ G ∧ E ∈ Θ ∧ toFun Γ Δ F Θ G
  exists_of_rhd_not_mem {Γ : MaximalConsistentSet L Φ} {D E : Formula α} :
    D ▷ E ∈ Φ → D ▷ E ∉ Γ → ∃ Δ, Successor Γ Δ ∧ D ∈ Δ ∧ ∀ Θ G, toFun Γ Δ E Θ G → E ∉ Θ

end LabelledSet

open LabelledSet

/-- - [KO21, Theorem 5.1] -/
def labelledModel (c : Condition L Φ) [Nonempty (LabelledSet L Φ)] :
    Model (LabelledSet L Φ) α where
  Rel' x y := Successor x.set y.set
  S' w x y := Successor w.set x.set ∧ c.toFun w.set x.set x.label y.set y.label
  Val' x a := #a ∈ x.set

namespace labelledModel

open Model Model.World

variable {c : Condition L Φ} [Nonempty (LabelledSet L Φ)]

instance : IsTrans _ (labelledModel c).Rel := ⟨fun _ _ _ h₁ h₂ ↦ h₁.trans h₂⟩

instance : Std.Irrefl (labelledModel c).Rel := ⟨fun _ h ↦ Successor.irrefl h⟩

variable [Entailment.Cl L] [L.ExtendsGL] [Adequate Φ]

/-- - [KO21, Lemma 5.3] -/
lemma truthlemma {x : (labelledModel c).World} {A : Formula α} (hA : A ∈ Φ) :
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
        (ih hA').mp <| h ⟨Δ, ⊥, .bot⟩ hΔ;
    · intro h y Rxy;
      exact (ih hA').mpr <| Rxy.mem_of_box_mem h;
  | rhd B C ihB ihC =>
    have hB := Adequate.rhd_left hA;
    have hC := Adequate.rhd_right hA;
    constructor;
    · intro h;
      by_contra hn;
      obtain ⟨Δ, hΔ, hBΔ, hΔC⟩ := c.exists_of_rhd_not_mem hA hn;
      obtain ⟨⟨Θ, G, hG⟩, hS, hv⟩ := h ⟨Δ, C, .of_rhd_right hA⟩ hΔ ((ihB hB).mpr hBΔ);
      exact hΔC Θ G hS.2 <| (ihC hC).mp hv;
    · intro h u Rxu hu
      obtain ⟨Θ, G, hG, hCΘ, hP⟩ :=
        c.exists_of_rhd_mem h Rxu ((ihB hB).mp hu) u.isRhdOperand_label
      exact ⟨⟨Θ, G, hG⟩, ⟨Rxu, hP⟩, (ihC hC).mpr hCΘ⟩

end labelledModel

/-! ### The conditions -/

namespace LabelledSet.Condition

variable {𝔸 : FormulaSet α} [CLAdequate Φ]
  {Γ Δ Θ : MaximalConsistentSet (ofCLAxioms 𝔸) Φ} {C F : Formula α}

/-- Every successor of `Γ` is a weak `F'`-critical successor for some label `F'`, which is `F` if it
is a weak `F`-critical successor. -/
private lemma exists_weakCriticalSuccessor (hΔ : Successor Γ Δ) (hF : IsRhdOperand Φ F) :
    ∃ F', IsRhdOperand Φ F' ∧ WeakCriticalSuccessor F' Γ Δ ∧
      (WeakCriticalSuccessor F Γ Δ → F' = F) := by
  by_cases h : WeakCriticalSuccessor F Γ Δ
  · exact ⟨F, hF, h, fun _ ↦ rfl⟩
  · exact ⟨⊥, .bot, (hΔ.criticalSuccessor_bot <|
      K_right ofCLAxioms.box_neg_iff_rhd_bot).weakCriticalSuccessor, by tauto⟩

/-- A weak `C`-critical successor of `Γ` does not contain `C`. -/
private lemma not_mem_of_weakCriticalSuccessor
    (hC : IsRhdOperand Φ C) (h : WeakCriticalSuccessor C Γ Δ) : C ∉ Δ :=
  h.not_mem <| (mem_iff_provable (Adequate.rhd_mem hC hC)).mpr <|
    Context.of ofCLAxioms.rhd_refl

/-- The condition for $\mathbf{CL}$.

- [KO21, Theorem 5.1]
-/
def J2Plus : Condition (ofCLAxioms 𝔸) Φ where
  toFun Γ Δ C Θ D := Successor Γ Θ ∧
    (WeakCriticalSuccessor C Γ Δ → D = C ∧ WeakCriticalSuccessor C Γ Θ ∧ C ∉ Θ)
  exists_of_rhd_mem hDE hΔ hD hF := by
    obtain ⟨F', hF', hΔF', hF'F⟩ := exists_weakCriticalSuccessor hΔ hF
    obtain ⟨Θ, hΘ, hEΘ, hFΘ⟩ := hΔF'.exists_weakCriticalSuccessor_mem_not_mem hF' hDE hD
    refine ⟨Θ, F', hF', hEΘ, hΘ.toSuccessor, fun h ↦ ?_⟩
    obtain rfl := hF'F h
    exact ⟨rfl, hΘ, hFΘ⟩
  exists_of_rhd_not_mem hDE hn := by
    obtain ⟨Δ, hΔ, hD⟩ := exists_weakCriticalSuccessor_of_rhd_not_mem hDE hn
    exact ⟨Δ, hΔ.toSuccessor, hD, fun _ _ h ↦ (h.2 hΔ).2.2⟩

/-! ### Frame conditions -/

open Model

variable [Nonempty (LabelledSet (ofCLAxioms 𝔸) Φ)]

/-- - [KO21, Lemma 5.2] -/
instance :
    (labelledModel (J2Plus (𝔸 := 𝔸) (Φ := Φ))).IsJ2 where
  rel_of_s_right h := h.2.1
  s_trans h₁ h₂ := by
    refine ⟨h₁.1, h₂.2.1, fun h ↦ ?_⟩
    obtain ⟨h₃, h₄, -⟩ := h₁.2.2 h
    obtain ⟨h₅, h₆, h₇⟩ := h₂.2.2 (h₃ ▸ h₄)
    exact ⟨h₅.trans h₃, h₃ ▸ h₆, h₃ ▸ h₇⟩

/-- - [KO21, Lemma 5.2] -/
instance :
    (labelledModel (J2Plus (𝔸 := 𝔸) (Φ := Φ))).IsJ1 where
  s_refl {_ x} h :=
    ⟨h, h, fun hx ↦ ⟨rfl, hx, not_mem_of_weakCriticalSuccessor x.isRhdOperand_label hx⟩⟩

instance : (labelledModel (J2Plus (𝔸 := 𝔸) (Φ := Φ))).IsCL where
  rel_of_s_left h := h.1

end LabelledSet.Condition

end Veltman

/-! ### Completeness -/

namespace Logic.ofCLAxioms

open Veltman Veltman.Model.World

variable {α : Type*} [DecidableEq α] {𝔸 : FormulaSet α} {A : Formula α}

/-- If `A` holds in the labelled model over the adequate closure of `{A}` for a condition `c`,
then `ofCLAxioms 𝔸` proves `A`.

- [KO21, Theorem 5.1]
-/
lemma provable_of_models_labelledModel
    (c : LabelledSet.Condition (ofCLAxioms 𝔸) (clAdequateClosure {A}))
    (h : ∀ [Nonempty (LabelledSet (ofCLAxioms 𝔸) (clAdequateClosure {A}))],
      labelledModel c ⊧ A) :
    ofCLAxioms 𝔸 ⊢ A := by
  by_contra hA;
  have hX : ({∼A} : FormulaSet α) *⊬[ofCLAxioms 𝔸] ⊥ := by
    intro h₁;
    apply hA;
    have h₂ : ofCLAxioms 𝔸 ⊢ ∼A 🡒 ⊥ := Context.emptyPrf <| Context.deduct <| by simpa using h₁;
    cl_prover [h₂];
  obtain ⟨Γ, hΓ⟩ := exists_consistent_union (Φ := clAdequateClosure {A}) hX;
  have : Nonempty (LabelledSet (ofCLAxioms 𝔸) (clAdequateClosure {A})) :=
    ⟨⟨Γ, ⊥, .bot⟩⟩;
  exact not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (labelledModel.truthlemma (clAdequateClosure.subset (by simp))).mp <| h ⟨Γ, ⊥, .bot⟩

end Logic.ofCLAxioms


end

end FFL.InterpretabilityLogic

end
