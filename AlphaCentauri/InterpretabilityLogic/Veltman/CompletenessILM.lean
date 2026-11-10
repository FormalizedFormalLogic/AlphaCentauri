module

public import AlphaCentauri.InterpretabilityLogic.Veltman.Completeness
public import AlphaCentauri.InterpretabilityLogic.Veltman.Extension

/-!
# Completeness of $\mathbf{ILM}$ with respect to finite Veltman models

Finite adequate sets closed under conjoining an antecedent or consequent of a `▷`-formula with
`□`-formulas, up to the relation that each of the two formulas implies the other or its
possibility; a finite Veltman model satisfying the frame condition of $\mathbf{M}$ whose worlds are
maximal consistent subsets of such a set, and the completeness of $\mathbf{ILM}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*} [DecidableEq α]

/-! ### Subformulas of conjunctions -/

lemma Formula.exists_mem_subformulas_of_mem_conj₂ {A : Formula α} :
    {l : List (Formula α)} → A ∈ (⋀l).subformulas → (∀ B C, A ≠ B 🡒 C) → A ≠ ⊥ →
      ∃ B ∈ l, A ∈ B.subformulas
  | [], h, himp, hbot => by
    simp only [List.conj₂_nil] at h;
    change A ∈ insert (⊥ 🡒 ⊥) _ at h;
    simp_all [subformulas];
  | [B], h, _, _ => ⟨B, by simp, h⟩
  | B :: C :: l, h, himp, hbot => by
    change A ∈ insert _ _ at h;
    simp only [subformulas, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at h;
    rcases h with h | (h | h | h | h | h) | h;
    all_goals first
      | exact (himp _ _ h).elim
      | exact (hbot h).elim
      | exact ⟨B, by simp, h⟩
      | obtain ⟨D, hD, h⟩ := exists_mem_subformulas_of_mem_conj₂ (l := C :: l) h himp hbot;
        exact ⟨D, by simp_all, h⟩

/-! ### Lemmas of $\mathbf{GL}$ -/

namespace Logic

variable {L : Logic α} [L.ExtendsGL] [Entailment.Cl L] {A B H : Formula α}
  {X Y : Finset (Formula α)}

omit [DecidableEq α] in
lemma or_dia_and_box_neg : L ⊢ A 🡒 (A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A)) := by
  change L ⊢ A 🡒 (A ⋏ □(∼A)) ⋎ ∼□(∼(A ⋏ □(∼A)));
  have h₁ : L ⊢ □(□(∼A) 🡒 ∼A) 🡒 □(∼A) := ExtendsGL.axiomL;
  have h₂ : L ⊢ □(∼(A ⋏ □(∼A))) 🡒 □(□(∼A) 🡒 ∼A) := box_mono <| by cl_prover;
  cl_prover [h₁, h₂];

omit [DecidableEq α] in
lemma dia_mono (h : L ⊢ A 🡒 B) : L ⊢ ◇A 🡒 ◇B := by
  have : L ⊢ □(∼B) 🡒 □(∼A) := box_mono <| by cl_prover [h];
  change L ⊢ ∼□(∼A) 🡒 ∼□(∼B);
  cl_prover [this];

lemma box_iff_conj_image_box : L ⊢ □X.conj 🡘 (X.image (□·)).conj := by
  apply E_intro;
  · apply right_Fconj_intro;
    simp only [Finset.mem_image, forall_exists_index, and_imp];
    rintro _ B hB rfl;
    exact box_mono <| left_Fconj_intro hB;
  · apply FConj_DT.mpr;
    have h : ((X.image (□·) : Finset (Formula α)) : Set (Formula α)) *⊢[L] □X.toList.conj := by
      apply box_conj_of_forall;
      intro B hB;
      exact Context.by_axm <| by simpa using hB;
    exact Context.of (box_mono <| K_right EConj₂Conj) ⨀ h;

lemma conj_imp_box_conj (hX : ∀ B ∈ X, ∃ C, B = □C) : L ⊢ X.conj 🡒 □X.conj := by
  apply C_trans _ <| K_right box_iff_conj_image_box;
  apply right_Fconj_intro;
  simp only [Finset.mem_image, forall_exists_index, and_imp];
  rintro _ B hB rfl;
  obtain ⟨C, rfl⟩ := hX B hB;
  exact C_trans (left_Fconj_intro hB) axiom4;

end Logic

end FFL.InterpretabilityLogic

end
