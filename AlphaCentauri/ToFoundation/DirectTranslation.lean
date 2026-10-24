module

public import Foundation.FirstOrder.LK.Interpretation

/-!
# Translations commute with the embedding of sentences

The translation of a sentence along a `DirectTranslation`, embedded as a formula with free
variables, is the translation of its embedding.
-/

@[expose] public section

namespace FFL.FirstOrder

lemma Rew.emb_comp_subst {L : Language} {n m : ℕ} (w : Fin n → Semiterm L Empty m) :
    (Rew.emb : Rew L Empty m ℕ m).comp (Rew.subst w) =
      (Rew.subst fun i ↦ Rew.emb (w i)).comp Rew.emb := by
  ext x
  · simp [Rew.comp_app]
  · exact x.elim

@[simp] lemma Rew.emb_subst_app {L : Language} {n m : ℕ} (w : Fin n → Semiterm L Empty m)
    (φ : Semiformula L Empty n) :
    Rewriting.emb (Rew.subst w ▹ φ : Semiformula L Empty m) =
      Rew.subst (fun i ↦ Rew.emb (w i)) ▹ (Rewriting.emb φ : Semiformula L ℕ n) := by
  unfold Rewriting.emb
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, Rew.emb_comp_subst]

namespace DirectTranslation

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]
  (π : DirectTranslation T L₂)

lemma varEqual_emb {n : ℕ} (t : Semiterm L₂ Empty n) :
    π.varEqual (Rew.emb t : SyntacticSemiterm L₂ n) = Rewriting.emb (π.varEqual t) := by
  induction t with
  | bvar x => simp [DirectTranslation.varEqual]
  | fvar x => exact x.elim
  | func f v ih =>
    simp [DirectTranslation.varEqual, Rew.func, ih, Rew.hom_operator' _ (π.func f),
      Function.comp_def, Matrix.comp_vecCons']

lemma translate_emb {n : ℕ} (σ : Semisentence L₂ n) :
    π.translate (Rewriting.emb σ : Semiproposition L₂ n) = Rewriting.emb (π.translate σ) := by
  induction σ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v =>
    simp [translate_rel, translateRel, varEqual_emb, Rew.hom_operator' _ (π.rel r),
      Function.comp_def, Matrix.comp_vecCons']
  | hnrel r v =>
    simp [translate_nrel, translateRel, varEqual_emb, Rew.hom_operator' _ (π.rel r),
      Function.comp_def, Matrix.comp_vecCons']
  | hand _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hor _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hall _ ih => simp [translate_all, DirectTranslation.fal, ih]
  | hexs _ ih => simp [translate_ex, DirectTranslation.exs, ih]

end DirectTranslation

end FFL.FirstOrder
