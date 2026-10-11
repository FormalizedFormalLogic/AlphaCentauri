module

public import AlphaCentauri.Bootstrapping.Completeness.HenkinFunction
public import AlphaCentauri.Bootstrapping.Completeness.HenkinOperators
public import AlphaCentauri.Interpretability.Basic
public import AlphaCentauri.ToFoundation.SententialAxioms

/-!
# The Henkin translation

The translation of a language $L$ into arithmetic given by the Henkin set of a theory $S$, over
any arithmetical theory containing $\mathsf{PA}$ and the consistency of $S$.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] (S : Theory L) [S.Δ₁]
  [Theory.Δ₁.Sentential S] [𝗘𝗤 L ⪯ S] (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

instance : 𝗘𝗤 ℒₒᵣ ⪯ T ∪ S.Con :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ T) (inferInstance : T ⪯ T ∪ S.Con)

instance : 𝗣𝗔 ⪯ T ∪ S.Con :=
  Entailment.WeakerThan.trans (inferInstance : 𝗣𝗔 ⪯ T) (inferInstance : T ⪯ T ∪ S.Con)

section models

omit [Theory.Δ₁.Sentential S] [𝗘𝗤 L ⪯ S] [L.Eq] [𝗣𝗔 ⪯ T] in
/-- A model of $T$ and the consistency of $S$ satisfies the consistency of $S$. -/
lemma consistent_of_models_con {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    [V↓[ℒₒᵣ] ⊧* T ∪ S.Con] : S.Consistent V := by
  have h : V↓[ℒₒᵣ] ⊧ (S.consistent : ArithmeticSentence) :=
    Semantics.ModelsSet.models_set (T := T ∪ S.Con) (Or.inr rfl)
  simpa [models_iff] using h

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
  (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)

omit [Theory.Δ₁.Sentential S] [𝗘𝗤 L ⪯ S] [𝗣𝗔 ⪯ T] in
/-- The domain of the Henkin translation is nonempty in every model of $\mathsf{PA}$. -/
lemma henkinDomain_nonempty : ∃ x : V, (henkinDomain S).val ![x] :=
  ⟨0, (henkinDomain_val S 0).mpr fun _ h ↦ absurd h (by simp)⟩

omit [Theory.Δ₁.Sentential S] in
include hS hcons in
/-- Every function symbol is interpreted by a total function on the domain of the Henkin
translation. -/
lemma henkinFunc_existsUnique {k : ℕ} (f : L.Func k) (e : Fin k → V) :
    ∃! y : V, (henkinDomain S).val ![y] ∧ (henkinFunc S f).val (y :> e) :=
  let ⟨y, hy, hf⟩ := exists_isRepresentative_henkinFunc S hS hcons f e
  ⟨y, ⟨(henkinDomain_val S y).mpr hy, (henkinFunc_val S f y e).mpr hf⟩,
    fun _ ⟨hy', hf'⟩ ↦ IsRepresentative.eq_of_henkinFunc S hS hcons f e
      ((henkinDomain_val S _).mp hy') hy ((henkinFunc_val S f _ e).mp hf') hf⟩

omit [Theory.Δ₁.Sentential S] in
include hS hcons in
/-- The Henkin translation of the equality symbol is equality on the domain. -/
lemma henkinRel_eq_iff {a b : V} (ha : (henkinDomain S).val ![a]) (hb : (henkinDomain S).val ![b]) :
    (henkinRel S Language.Eq.eq).val ![a, b] ↔ a = b := by
  rw [henkinRel_val]
  have h : (fun i ↦ Bootstrapping.Semiterm.fvar (![a, b] i) : Fin 2 → Bootstrapping.Semiterm V L 0)
      = ![.fvar a, .fvar b] := funext fun | 0 => rfl | 1 => rfl
  rw [h]
  exact henkinSet_equal_fvar_iff S hS hcons ((henkinDomain_val S a).mp ha)
    ((henkinDomain_val S b).mp hb)

end models

omit [L.Eq] [𝗘𝗤 L ⪯ S] in
/-- An arithmetical sentence that holds in every model of $\mathsf{PA}$ in which `S` is consistent
and its $\Delta_1$ numeration consists of sentences is provable from $T$ and the consistency of
`S`. -/
lemma provable_of_models_henkin (σ : ArithmeticSentence)
    (H : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      (∀ p ∈ S.Δ₁Class (V := V), shift L p = p) → S.Consistent V → V↓[ℒₒᵣ] ⊧ σ) :
    T ∪ S.Con ⊢ σ :=
  Arithmetic.complete.{0} _ _ fun V _ _ ↦
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (T := 𝗣𝗔) (U := T ∪ S.Con) inferInstance
    H V (fun _ h ↦ Theory.Δ₁.Sentential.shift_eq h) (consistent_of_models_con S T)

/-- The translation of `L` into arithmetic by the Henkin set of `S`.

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.27] -/
noncomputable def henkinTranslation : DirectTranslation (T ∪ S.Con) L where
  domain := henkinDomain S
  rel := henkinRel S
  func := henkinFunc S
  domain_nonempty := provable_of_models_henkin S T _ fun V _ _ _ _ ↦ by
    simpa [models_iff] using henkinDomain_nonempty S (V := V)
  func_defined f := provable_of_models_henkin S T _ fun V _ _ hS hcons ↦ by
    simp only [BinderNotation.finSuccItr, Nat.add_zero, Matrix.zero_cons_succ_eq_self, models_iff,
      Semiformula.eval_allClosure, LogicalConnective.HomClass.map_imply, Matrix.conj_hom_prop,
      Semiformula.eval_operator, Matrix.comp₁, Semiterm.val_bvar, Semiformula.eval_existsUnique,
      Nat.succ_eq_add_one, LogicalConnective.HomClass.map_and, Matrix.cons_val_zero,
      LogicalConnective.Prop.and_eq, LogicalConnective.Prop.arrow_eq]
    intro e _
    simpa only [Function.comp_def, Semiterm.val_bvar] using henkinFunc_existsUnique S hS hcons f e
  preserve_eq := provable_of_models_henkin S T _ fun V _ _ hS hcons ↦ by
    simp only [Nat.reduceAdd, Fin.isValue, models_iff, Semiformula.eval_all, Nat.succ_eq_add_one,
      LogicalConnective.HomClass.map_imply, Semiformula.eval_operator, Matrix.comp₁,
      Semiterm.val_bvar, Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_zero, LogicalConnective.HomClass.map_iff, Matrix.comp₂,
      Tarski.Structure.eq_iff_eq, LogicalConnective.Prop.iff_eq, LogicalConnective.Prop.arrow_eq]
    intro a b ha hb
    exact henkinRel_eq_iff S hS hcons ha hb

end FFL.FirstOrder.Arithmetic
