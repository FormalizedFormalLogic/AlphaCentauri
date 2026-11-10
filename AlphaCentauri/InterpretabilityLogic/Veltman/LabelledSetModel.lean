module

public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentSet
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import Mathlib.Data.Set.Finite.List

/-!
# The model on labelled sets

The construction behind the completeness of $\mathbf{IL}^-$, $\mathbf{IL}^-(\mathbf{J1})$,
$\mathbf{IL}^-(\mathbf{J4}^+)$, $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+)$,
$\mathbf{IL}^-(\mathbf{J2}^+)$, $\mathbf{CL}$, $\mathbf{IL}^-(\mathbf{J5})$,
$\mathbf{IL}^-(\mathbf{J1}, \mathbf{J5})$, $\mathbf{IL}^-(\mathbf{J4}^+, \mathbf{J5})$ and
$\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+, \mathbf{J5})$ with respect to finite Veltman models.

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

instance [Adequate Φ] : (labelledModel c).IsILMinus where
  rel_of_s_left h := h.1

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

variable {𝔸 : Set (Formula α)} [ILMinusAdequate Φ]
  {Γ Δ Θ : MaximalConsistentSet (ofAxiomsMinus 𝔸) Φ} {C F : Formula α}

/-- Every successor of `Γ` is a weak `F'`-critical successor for some label `F'`, which is `F` if it
is a weak `F`-critical successor. -/
private lemma exists_weakCriticalSuccessor (hΔ : Successor Γ Δ) (hF : IsRhdOperand Φ F) :
    ∃ F', IsRhdOperand Φ F' ∧ WeakCriticalSuccessor F' Γ Δ ∧
      (WeakCriticalSuccessor F Γ Δ → F' = F) := by
  by_cases h : WeakCriticalSuccessor F Γ Δ
  · exact ⟨F, hF, h, fun _ ↦ rfl⟩
  · exact ⟨⊥, .bot, (hΔ.criticalSuccessor_bot <|
      K_right ofAxiomsMinus.box_neg_iff_rhd_bot).weakCriticalSuccessor, by tauto⟩

/-- In the presence of $\mathbf{J1}$, a weak `C`-critical successor of `Γ` does not contain `C`. -/
private lemma not_mem_of_weakCriticalSuccessor [ILMinusJ1 ⪯ ofAxiomsMinus 𝔸]
    (hC : IsRhdOperand Φ C) (h : WeakCriticalSuccessor C Γ Δ) : C ∉ Δ :=
  h.not_mem <| (mem_iff_provable (Adequate.rhd_mem hC hC)).mpr <|
    Context.of <| WeakerThan.pbl (𝓢 := ILMinusJ1) ILMinusJ1.axiomJ1'

/-- The condition for $\mathbf{IL}^-$ and $\mathbf{IL}^-(\mathbf{J1})$.

- [KO21, Theorem 5.1]
-/
def ILMinus : Condition (ofAxiomsMinus 𝔸) Φ where
  toFun Γ Δ C Θ _ := WeakCriticalSuccessor C Γ Δ → C ∉ Θ
  exists_of_rhd_mem hDE hΔ hD hF := by
    obtain ⟨F', hF', hΔF', hF'F⟩ := exists_weakCriticalSuccessor hΔ hF
    obtain ⟨Θ, hEΘ, hFΘ⟩ := hΔF'.exists_mem_not_mem hF' hDE hD
    exact ⟨Θ, ⊥, .bot, hEΘ, fun h ↦ hF'F h ▸ hFΘ⟩
  exists_of_rhd_not_mem hDE hn := by
    obtain ⟨Δ, hΔ, hD⟩ := exists_weakCriticalSuccessor_of_rhd_not_mem hDE hn
    exact ⟨Δ, hΔ.toSuccessor, hD, fun _ _ h ↦ h hΔ⟩

/-- The condition for $\mathbf{IL}^-(\mathbf{J4}^+)$ and
$\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+)$.

- [KO21, Theorem 5.1]
-/
def J4Plus [ILMinusJ4Plus ⪯ ofAxiomsMinus 𝔸] : Condition (ofAxiomsMinus 𝔸) Φ where
  toFun Γ Δ C Θ _ := Successor Γ Θ ∧ (WeakCriticalSuccessor C Γ Δ → C ∉ Θ)
  exists_of_rhd_mem hDE hΔ hD hF := by
    obtain ⟨F', hF', hΔF', hF'F⟩ := exists_weakCriticalSuccessor hΔ hF
    obtain ⟨Θ, hΘ, hEΘ, hFΘ⟩ := hΔF'.exists_successor_mem_not_mem hF' hDE hD
    exact ⟨Θ, ⊥, .bot, hEΘ, hΘ, fun h ↦ hF'F h ▸ hFΘ⟩
  exists_of_rhd_not_mem hDE hn := by
    obtain ⟨Δ, hΔ, hD⟩ := exists_weakCriticalSuccessor_of_rhd_not_mem hDE hn
    exact ⟨Δ, hΔ.toSuccessor, hD, fun _ _ h ↦ h.2 hΔ⟩

/-- The condition for $\mathbf{IL}^-(\mathbf{J2}^+)$ and $\mathbf{CL}$.

- [KO21, Theorem 5.1]
-/
def J2Plus [ILMinusJ2Plus ⪯ ofAxiomsMinus 𝔸] : Condition (ofAxiomsMinus 𝔸) Φ where
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

/-- The condition for $\mathbf{IL}^-(\mathbf{J5})$ and $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J5})$.

- [KO21, Theorem 5.1]
-/
def J5 [ILMinusJ5 ⪯ ofAxiomsMinus 𝔸] : Condition (ofAxiomsMinus 𝔸) Φ where
  toFun Γ Δ C Θ _ := WeakCriticalSuccessor C Γ Δ → □(∼C) ∈ Δ → C ∉ Θ
  exists_of_rhd_mem hDE hΔ hD hF := by
    obtain ⟨F', hF', hΔF', hF'F⟩ := exists_weakCriticalSuccessor hΔ hF
    obtain ⟨Θ, hEΘ, hFΘ⟩ := hΔF'.exists_mem_not_mem hF' hDE hD
    exact ⟨Θ, ⊥, .bot, hEΘ, fun h _ ↦ hF'F h ▸ hFΘ⟩
  exists_of_rhd_not_mem hDE hn := by
    obtain ⟨Δ, hΔ, hD, hEΔ⟩ := exists_weakCriticalSuccessor_box_neg_of_rhd_not_mem hDE hn
    exact ⟨Δ, hΔ.toSuccessor, hD, fun _ _ h ↦ h hΔ hEΔ⟩

/-- The condition for $\mathbf{IL}^-(\mathbf{J4}^+, \mathbf{J5})$ and
$\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+, \mathbf{J5})$.

- [KO21, Theorem 5.1]
-/
def J4PlusJ5 [ILMinusJ4Plus ⪯ ofAxiomsMinus 𝔸] [ILMinusJ5 ⪯ ofAxiomsMinus 𝔸] :
    Condition (ofAxiomsMinus 𝔸) Φ where
  toFun Γ Δ C Θ _ := Successor Γ Θ ∧ (WeakCriticalSuccessor C Γ Δ → □(∼C) ∈ Δ → C ∉ Θ)
  exists_of_rhd_mem hDE hΔ hD hF := by
    obtain ⟨F', hF', hΔF', hF'F⟩ := exists_weakCriticalSuccessor hΔ hF
    obtain ⟨Θ, hΘ, hEΘ, hFΘ⟩ := hΔF'.exists_successor_mem_not_mem hF' hDE hD
    exact ⟨Θ, ⊥, .bot, hEΘ, hΘ, fun h _ ↦ hF'F h ▸ hFΘ⟩
  exists_of_rhd_not_mem hDE hn := by
    obtain ⟨Δ, hΔ, hD, hEΔ⟩ := exists_weakCriticalSuccessor_box_neg_of_rhd_not_mem hDE hn
    exact ⟨Δ, hΔ.toSuccessor, hD, fun _ _ h ↦ h.2 hΔ hEΔ⟩

/-! ### Frame conditions -/

open Model

variable [Nonempty (LabelledSet (ofAxiomsMinus 𝔸) Φ)]

/-- - [KO21, Lemma 5.2] -/
instance [ILMinusJ1 ⪯ ofAxiomsMinus 𝔸] :
    (labelledModel (ILMinus (𝔸 := 𝔸) (Φ := Φ))).IsJ1 where
  s_refl {_ x} h := ⟨h, not_mem_of_weakCriticalSuccessor x.isRhdOperand_label⟩

/-- - [KO21, Lemma 5.2] -/
instance [ILMinusJ4Plus ⪯ ofAxiomsMinus 𝔸] :
    (labelledModel (J4Plus (𝔸 := 𝔸) (Φ := Φ))).IsJ4 where
  rel_of_s_right h := h.2.1

/-- - [KO21, Lemma 5.2] -/
instance [ILMinusJ4Plus ⪯ ofAxiomsMinus 𝔸] [ILMinusJ1 ⪯ ofAxiomsMinus 𝔸] :
    (labelledModel (J4Plus (𝔸 := 𝔸) (Φ := Φ))).IsJ1 where
  s_refl {_ x} h := ⟨h, h, not_mem_of_weakCriticalSuccessor x.isRhdOperand_label⟩

/-- - [KO21, Lemma 5.2] -/
instance [ILMinusJ2Plus ⪯ ofAxiomsMinus 𝔸] :
    (labelledModel (J2Plus (𝔸 := 𝔸) (Φ := Φ))).IsJ2 where
  rel_of_s_right h := h.2.1
  s_trans h₁ h₂ := by
    refine ⟨h₁.1, h₂.2.1, fun h ↦ ?_⟩
    obtain ⟨h₃, h₄, -⟩ := h₁.2.2 h
    obtain ⟨h₅, h₆, h₇⟩ := h₂.2.2 (h₃ ▸ h₄)
    exact ⟨h₅.trans h₃, h₃ ▸ h₆, h₃ ▸ h₇⟩

/-- - [KO21, Lemma 5.2] -/
instance [ILMinusJ2Plus ⪯ ofAxiomsMinus 𝔸] [ILMinusJ1 ⪯ ofAxiomsMinus 𝔸] :
    (labelledModel (J2Plus (𝔸 := 𝔸) (Φ := Φ))).IsJ1 where
  s_refl {_ x} h :=
    ⟨h, h, fun hx ↦ ⟨rfl, hx, not_mem_of_weakCriticalSuccessor x.isRhdOperand_label hx⟩⟩

/-- - [KO21, Lemma 5.2] -/
instance [ILMinusJ5 ⪯ ofAxiomsMinus 𝔸] : (labelledModel (J5 (𝔸 := 𝔸) (Φ := Φ))).IsJ5 where
  s_of_rel h₁ h₂ := ⟨h₁, fun _ h ↦ h₂.not_mem_of_box_neg_mem h⟩

/-- - [KO21, Lemma 5.2] -/
instance [ILMinusJ5 ⪯ ofAxiomsMinus 𝔸] [ILMinusJ1 ⪯ ofAxiomsMinus 𝔸] :
    (labelledModel (J5 (𝔸 := 𝔸) (Φ := Φ))).IsJ1 where
  s_refl {_ x} h := ⟨h, fun hx _ ↦ not_mem_of_weakCriticalSuccessor x.isRhdOperand_label hx⟩

/-- - [KO21, Lemma 5.2] -/
instance [ILMinusJ4Plus ⪯ ofAxiomsMinus 𝔸] [ILMinusJ5 ⪯ ofAxiomsMinus 𝔸] :
    (labelledModel (J4PlusJ5 (𝔸 := 𝔸) (Φ := Φ))).IsJ4 where
  rel_of_s_right h := h.2.1

/-- - [KO21, Lemma 5.2] -/
instance [ILMinusJ4Plus ⪯ ofAxiomsMinus 𝔸] [ILMinusJ5 ⪯ ofAxiomsMinus 𝔸] :
    (labelledModel (J4PlusJ5 (𝔸 := 𝔸) (Φ := Φ))).IsJ5 where
  s_of_rel h₁ h₂ := ⟨h₁, h₁.trans h₂, fun _ h ↦ h₂.not_mem_of_box_neg_mem h⟩

/-- - [KO21, Lemma 5.2] -/
instance [ILMinusJ4Plus ⪯ ofAxiomsMinus 𝔸] [ILMinusJ5 ⪯ ofAxiomsMinus 𝔸]
    [ILMinusJ1 ⪯ ofAxiomsMinus 𝔸] : (labelledModel (J4PlusJ5 (𝔸 := 𝔸) (Φ := Φ))).IsJ1 where
  s_refl {_ x} h := ⟨h, h, fun hx _ ↦ not_mem_of_weakCriticalSuccessor x.isRhdOperand_label hx⟩

end LabelledSet.Condition

end Veltman

/-! ### Completeness -/

namespace Logic.ofAxiomsMinus

open Veltman Veltman.Model.World

variable {α : Type*} [DecidableEq α] {𝔸 : Set (Formula α)} {A : Formula α}

/-- If `A` holds in the labelled model over the adequate closure of `{A}` for a condition `c`,
then `ofAxiomsMinus 𝔸` proves `A`.

- [KO21, Theorem 5.1]
-/
lemma provable_of_models_labelledModel
    (c : LabelledSet.Condition (ofAxiomsMinus 𝔸) (ilMinusAdequateClosure {A}))
    (h : ∀ [Nonempty (LabelledSet (ofAxiomsMinus 𝔸) (ilMinusAdequateClosure {A}))],
      labelledModel c ⊧ A) :
    ofAxiomsMinus 𝔸 ⊢ A := by
  by_contra hA;
  have hX : ({∼A} : Set (Formula α)) *⊬[ofAxiomsMinus 𝔸] ⊥ := by
    intro h₁;
    apply hA;
    have h₂ : ofAxiomsMinus 𝔸 ⊢ ∼A 🡒 ⊥ := Context.emptyPrf <| Context.deduct <| by simpa using h₁;
    cl_prover [h₂];
  obtain ⟨Γ, hΓ⟩ := exists_consistent_union (Φ := ilMinusAdequateClosure {A}) hX;
  have : Nonempty (LabelledSet (ofAxiomsMinus 𝔸) (ilMinusAdequateClosure {A})) :=
    ⟨⟨Γ, ⊥, .bot⟩⟩;
  exact not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (labelledModel.truthlemma (ilMinusAdequateClosure.subset (by simp))).mp <| h ⟨Γ, ⊥, .bot⟩

end Logic.ofAxiomsMinus

namespace Logic

open Veltman Veltman.Model LabelledSet.Condition ofAxiomsMinus

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinus.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsILMinus] → M ⊧ A) :
    𝐈𝐋⁻ ⊢ A := by
  classical
  exact provable_of_models_labelledModel .ILMinus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → M ⊧ A) :
    ILMinusJ1 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .ILMinus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ4Plus.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → M ⊧ A) :
    ILMinusJ4Plus ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J4Plus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4Plus.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → M ⊧ A) :
    ILMinusJ1J4Plus ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J4Plus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ2Plus.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A) :
    ILMinusJ2Plus ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J2Plus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem CL.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ2] → M ⊧ A) :
    𝐂𝐋 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J2Plus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ5.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ5 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J5 (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J5.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ1J5 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J5 (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ4PlusJ5.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ4PlusJ5 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J4PlusJ5 (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4PlusJ5.complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ1J4PlusJ5 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J4PlusJ5 (h _)

end Logic

end

end FFL.InterpretabilityLogic

end
