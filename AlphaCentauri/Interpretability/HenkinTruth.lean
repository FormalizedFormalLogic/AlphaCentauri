module

public import AlphaCentauri.Bootstrapping.Completeness.HenkinCongruence
public import AlphaCentauri.Interpretability.HenkinTranslation

/-!
# The truth lemma of the Henkin translation

In the model of the Henkin translation, a formula is true of representatives of free variables
exactly when the formula with those free variables substituted is in the Henkin set.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] (S : Theory L) [S.Δ₁]
  [Theory.Δ₁.Sentential S] [𝗘𝗤 L ⪯ S] (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
  {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] [V↓[ℒₒᵣ] ⊧* T ∪ S.Con]

theorem henkinTranslation_term {n : ℕ} (t : ClosedSemiterm L n)
    {e : Fin n → (henkinTranslation S T).Model V} {u : Fin n → V}
    (h : ∀ i, HenkinEq S (e i : V) (u i)) :
    HenkinSet S (Bootstrapping.Semiformula.equal
      ((⌜t⌝ : Bootstrapping.Semiterm V L n).subst
        (fun i ↦ Bootstrapping.Semiterm.fvar (u i) : Bootstrapping.SemitermVec V L n 0))
      (Bootstrapping.Semiterm.fvar
        ((t.val e Empty.elim : (henkinTranslation S T).Model V) : V)) :
        Bootstrapping.Formula V L).val := by
  sorry

theorem henkinTranslation_truth {n : ℕ} (β : Semisentence L n)
    {e : Fin n → (henkinTranslation S T).Model V} {u : Fin n → V}
    (h : ∀ i, HenkinEq S (e i : V) (u i)) :
    ((henkinTranslation S T).Model V) ⊧/e β ↔
      HenkinSet S ((⌜β⌝ : Bootstrapping.Semiformula V L n).subst
        (fun i ↦ Bootstrapping.Semiterm.fvar (u i) : Bootstrapping.SemitermVec V L n 0)).val := by
  sorry

end FFL.FirstOrder.Arithmetic
