module

public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentSet
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import Mathlib.Data.Set.Finite.List

/-!
# Completeness of sublogics of $\mathbf{IL}$ and of $\mathbf{IL}$ with respect to finite frames

Finite Veltman models whose worlds are maximal consistent subsets of an adequate set labelled by
antecedents and consequents of `▷`-formulas in it, with `≺[w]` given by a condition on the labelled
sets, and the truth lemma for every condition with two existence properties. Such conditions give
the completeness of $\mathbf{IL}^-$, $\mathbf{IL}^-(\mathbf{J1})$,
$\mathbf{IL}^-(\mathbf{J4}^+)$, $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+)$,
$\mathbf{IL}^-(\mathbf{J2}^+)$, $\mathbf{CL}$, $\mathbf{IL}^-(\mathbf{J5})$,
$\mathbf{IL}^-(\mathbf{J1}, \mathbf{J5})$, $\mathbf{IL}^-(\mathbf{J4}^+, \mathbf{J5})$ and
$\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+, \mathbf{J5})$ with respect to finite
$\mathbf{IL}^-$-frames satisfying the frame conditions of their axioms.

A finite Veltman model whose worlds are maximal consistent subsets of an adequate set indexed by
finite sequences of formulas gives the completeness of $\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$
and $\mathbf{IL}$ with respect to finite $\mathbf{IL}^-$-frames satisfying the frame conditions of
their axioms, and of $\mathbf{IL}$ with respect to finite Veltman models.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

/-! ## Sublogics of $\mathbf{IL}$ -/

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

universe u

variable {α : Type u} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinus.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsILMinus] → M ⊧ A) :
    𝐈𝐋⁻ ⊢ A := by
  classical
  exact provable_of_models_labelledModel .ILMinus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → M ⊧ A) :
    ILMinusJ1 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .ILMinus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ4Plus.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → M ⊧ A) :
    ILMinusJ4Plus ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J4Plus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4Plus.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → M ⊧ A) :
    ILMinusJ1J4Plus ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J4Plus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ2Plus.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A) :
    ILMinusJ2Plus ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J2Plus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem CL.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ2] → M ⊧ A) :
    𝐂𝐋 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J2Plus (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ5.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ5 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J5 (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J5.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ1J5 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J5 (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ4PlusJ5.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ4PlusJ5 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J4PlusJ5 (h _)

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4PlusJ5.complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ1J4PlusJ5 ⊢ A := by
  classical
  exact provable_of_models_labelledModel .J4PlusJ5 (h _)

end Logic

end

/-! ## $\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$ and $\mathbf{IL}$ -/

section

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

instance : IsTrans _ (countermodel L Φ).Rel :=
  ⟨fun _ _ _ h₁ h₂ ↦ ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩⟩

instance : Std.Irrefl (countermodel L Φ).Rel := ⟨fun _ h ↦ h.1.irrefl⟩

instance [Adequate Φ] : (countermodel L Φ).IsILMinus where
  rel_of_s_left h := h.1.1

instance : (countermodel L Φ).IsJ2 where
  rel_of_s_right h := h.1.2
  s_trans := S.trans

variable [Entailment.Cl L]

instance : (countermodel L Φ).IsJ5 := ⟨S.of_rel⟩

instance [Adequate Φ] [ILMinusJ1 ⪯ L] : (countermodel L Φ).IsJ1 :=
  ⟨S.refl <| WeakerThan.pbl (𝓢 := ILMinusJ1) ILMinusJ1.axiomJ1'⟩

instance [Adequate Φ] [ILMinusJ1 ⪯ L] : (countermodel L Φ).IsIL := .of_isILMinus

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
        refine ⟨x.criticalSuccessor F hF Θ hΘ.toSuccessor,
          ⟨⟨Rxu, hΘ.toSuccessor, List.prefix_append _ _⟩, ?_⟩, (ihC hC).mpr hCΘ⟩
        intro C' hpre' _ _
        have h₁ : x.seq ++ [C'] = x.seq ++ [F] :=
          (List.prefix_of_prefix_length_le hpre' hpre (by simp)).eq_of_length (by simp)
        obtain rfl : C' = F := by simpa using h₁
        exact ⟨List.prefix_refl _, hΘ, hFΘ, hbΘ⟩
      · have hbot := Rxu.1.criticalSuccessor_bot <| K_right ofAxiomsMinus.box_neg_iff_rhd_bot;
        obtain ⟨Θ, hΘ, hCΘ, -⟩ :=
          hbot.weakCriticalSuccessor.exists_criticalSuccessor_box_neg_mem_not_mem .bot h hu;
        exact ⟨x.successor Θ hΘ.toSuccessor,
          ⟨⟨Rxu, hΘ.toSuccessor, List.prefix_refl _⟩,
            fun C' hpre' hcrit' hbox' ↦ (hc ⟨C', hpre', hcrit', hbox'⟩).elim⟩,
          (ihC hC).mpr hCΘ⟩

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
  have : M.IsIL := .of_isILMinus
  exact h M

end Logic

end

end FFL.InterpretabilityLogic

end
