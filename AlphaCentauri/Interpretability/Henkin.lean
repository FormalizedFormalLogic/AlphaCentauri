module

public import AlphaCentauri.Bootstrapping.Completeness.Henkin
public import AlphaCentauri.Interpretability.Basic
public import AlphaCentauri.ToFoundation.SententialAxioms

/-!
# Interpretation of a theory in itself plus its consistency

The translation of a language $L$ into arithmetic given by the Henkin set of a theory $S$, over
any arithmetical theory containing $\mathsf{PA}$ and the consistency of $S$. In its model, a
formula is true of representatives of free variables exactly when the formula with those free
variables substituted is in the Henkin set. Hence a theory $S$ with a $\Delta_1$ numeration and
the equality axioms is interpretable in $T + \mathrm{Con}_S$ for every arithmetical theory
$T \supseteq \mathsf{PA}$.

## References

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.27], [HP98, 2.43]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

section translation

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
    H V (Theory.Δ₁.Sentential.forall_shift_eq S) (consistent_of_models_con S T)

/-- The translation of `L` into arithmetic by the Henkin set of `S`.

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.27] -/
noncomputable def henkinTranslation : DirectTranslation (T ∪ S.Con) L where
  domain := henkinDomain S
  rel := henkinRel S
  func := henkinFunc S
  domain_nonempty := provable_of_models_henkin S T _ fun _ _ _ _ _ ↦
    (DirectTranslation.models_domainNonempty_iff _).mpr (henkinDomain_nonempty S)
  func_defined f := provable_of_models_henkin S T _ fun _ _ _ hS hcons ↦
    (DirectTranslation.models_funcDefined_iff _ _).mpr fun e _ ↦
      henkinFunc_existsUnique S hS hcons f e
  preserve_eq := provable_of_models_henkin S T _ fun _ _ _ hS hcons ↦
    (DirectTranslation.models_preserveEq_iff _ _).mpr fun _ _ ha hb ↦
      henkinRel_eq_iff S hS hcons ha hb

section truth

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] [V↓[ℒₒᵣ] ⊧* T ∪ S.Con]

theorem henkinTranslation_term {n : ℕ} (t : ClosedSemiterm L n)
    {e : Fin n → (henkinTranslation S T).Model V} {u : Fin n → V}
    (h : ∀ i, HenkinEq S (e i : V) (u i)) :
    HenkinSet S (Bootstrapping.Semiformula.equal
      ((⌜t⌝ : Bootstrapping.Semiterm V L n).subst
        (fun i ↦ Bootstrapping.Semiterm.fvar (u i) : Bootstrapping.SemitermVec V L n 0))
      (Bootstrapping.Semiterm.fvar
        ((t.val e Empty.elim : (henkinTranslation S T).Model V) : V)) :
        Bootstrapping.Formula V L).val := by
  have hS := Theory.Δ₁.Sentential.forall_shift_eq (V := V) S
  have hcons : S.Consistent V := consistent_of_models_con S T
  induction t with
  | bvar i =>
    simp only [Semiterm.empty_typed_quote_bvar, Semiterm.substs_bvar, Semiterm.val_bvar]
    exact HenkinEq.symm S hS hcons (h i)
  | fvar x => exact x.elim
  | func f v ih =>
    have h₁ := DirectTranslation.Model.eval_func (π := henkinTranslation S T) (M := V) f
      fun i ↦ (v i).val e Empty.elim
    have h₂ := (henkinFunc_val S f _ _).mp h₁
    simp only [Semiterm.empty_typed_quote_func, Semiterm.substs_func, Semiterm.val_func]
    exact henkinSet_equal_trans S hS hcons (henkinSet_equal_func S hS hcons f ih) h₂

section quote

omit [L.Eq]

variable {n : ℕ}

private lemma subst_fvar_cons (x : V) (u : Fin n → V) (φ : Bootstrapping.Semiformula V L (n + 1)) :
    (φ.subst (Bootstrapping.SemitermVec.q fun i ↦ Bootstrapping.Semiterm.fvar (u i) :
        Bootstrapping.SemitermVec V L (n + 1) 1)).subst ![Bootstrapping.Semiterm.fvar x] =
      φ.subst (fun i ↦ Bootstrapping.Semiterm.fvar ((x :> u) i) :
        Bootstrapping.SemitermVec V L (n + 1) 0) := by
  rw [Bootstrapping.Semiformula.substs_q_substs_single]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

end quote

section model

omit [V↓[ℒₒᵣ] ⊧* T ∪ S.Con] in
private lemma exists_model_henkinEq (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (x : V) :
    ∃ a : (henkinTranslation S T).Model V, HenkinEq S (a : V) x := by
  obtain ⟨r, hr, hrx⟩ := exists_isRepresentative S hS hcons x
  exact ⟨⟨r, (henkinDomain_val S r).mpr hr⟩, hrx⟩

omit [V↓[ℒₒᵣ] ⊧* T ∪ S.Con] in
private lemma henkinEq_cons {n : ℕ} {e : Fin n → (henkinTranslation S T).Model V} {u : Fin n → V}
    {a : (henkinTranslation S T).Model V} {x : V} (ha : HenkinEq S (a : V) x)
    (h : ∀ i, HenkinEq S (e i : V) (u i)) : ∀ i, HenkinEq S ((a :> e) i : V) ((x :> u) i) :=
  Fin.cases ha h

end model

theorem henkinTranslation_truth {n : ℕ} (β : Semisentence L n)
    {e : Fin n → (henkinTranslation S T).Model V} {u : Fin n → V}
    (h : ∀ i, HenkinEq S (e i : V) (u i)) :
    ((henkinTranslation S T).Model V) ⊧/e β ↔
      HenkinSet S ((⌜β⌝ : Bootstrapping.Semiformula V L n).subst
        (fun i ↦ Bootstrapping.Semiterm.fvar (u i) : Bootstrapping.SemitermVec V L n 0)).val := by
  have hS := Theory.Δ₁.Sentential.forall_shift_eq (V := V) S
  have hcons : S.Consistent V := consistent_of_models_con S T
  induction β using Semiformula.rec' with
  | hrel R v =>
    rw [quote_rel_sentence, Bootstrapping.Semiformula.substs_rel, Semiformula.eval_rel]
    exact (henkinRel_val S R _).trans
      (henkinSet_rel_iff S hS hcons R fun i ↦ henkinTranslation_term S T (v i) h).symm
  | hnrel R v =>
    rw [quote_nrel_sentence, Bootstrapping.Semiformula.substs_nrel, Semiformula.eval_nrel,
      ← Bootstrapping.Semiformula.neg_rel, henkinSet_neg_iff S hS hcons]
    exact not_congr <| (henkinRel_val S R _).trans
      (henkinSet_rel_iff S hS hcons R fun i ↦ henkinTranslation_term S T (v i) h).symm
  | hverum =>
    simp only [LogicalConnective.HomClass.map_top, «Prop».top_eq_true, LCWQIsoGödelQuote.top,
      Bootstrapping.Semiformula.substs_verum, true_iff]
    exact henkinSet_of_tprovable S (φ := (⊤ : Bootstrapping.Formula V L)) (by simp)
  | hfalsum =>
    simp only [LogicalConnective.HomClass.map_bot, «Prop».bot_eq_false, LCWQIsoGödelQuote.bot,
      Bootstrapping.Semiformula.substs_falsum, false_iff]
    exact henkinSet_not_falsum S hS hcons
  | hand φ ψ ihφ ihψ =>
    rw [LCWQIsoGödelQuote.and, Bootstrapping.Semiformula.substs_and,
      henkinSet_and_iff S hS hcons, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq]
    exact and_congr (ihφ h) (ihψ h)
  | hor φ ψ ihφ ihψ =>
    rw [LCWQIsoGödelQuote.or, Bootstrapping.Semiformula.substs_or,
      henkinSet_or_iff S hS hcons, LogicalConnective.HomClass.map_or,
      LogicalConnective.Prop.or_eq]
    exact or_congr (ihφ h) (ihψ h)
  | hall φ ih =>
    rw [LCWQIsoGödelQuote.all, Bootstrapping.Semiformula.substs_all,
      henkinSet_all_iff S hS hcons, Semiformula.eval_all]
    simp only [subst_fvar_cons]
    constructor
    · intro hφ x
      obtain ⟨a, ha⟩ := exists_model_henkinEq S T hS hcons x
      exact (ih (henkinEq_cons S T ha h)).mp (hφ a)
    · intro hφ a
      exact (ih (henkinEq_cons S T (HenkinEq.refl S _) h)).mpr (hφ a)
  | hexs φ ih =>
    rw [LCWQIsoGödelQuote.exs, Bootstrapping.Semiformula.substs_ex,
      henkinSet_exs_iff S hS hcons, Semiformula.eval_ex]
    simp only [subst_fvar_cons]
    constructor
    · rintro ⟨a, hφ⟩
      exact ⟨a, (ih (henkinEq_cons S T (HenkinEq.refl S _) h)).mp hφ⟩
    · rintro ⟨x, hφ⟩
      obtain ⟨a, ha⟩ := exists_model_henkinEq S T hS hcons x
      exact ⟨a, (ih (henkinEq_cons S T ha h)).mpr hφ⟩

end truth

end translation

section interpretation

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] (S : Theory L) [S.Δ₁]
  [𝗘𝗤 L ⪯ S] (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

section sentential

variable [Theory.Δ₁.Sentential S]

/-- The Henkin translation interprets `S` in `T ∪ S.Con` when the numeration of `S` consists of
sentences. -/
noncomputable abbrev henkinInterpretationOfSentential : T ∪ S.Con ⊳ S where
  trln := henkinTranslation S T
  interpret_theory σ hσ := Arithmetic.complete.{0} _ _ fun V _ _ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (T := 𝗣𝗔) (U := T ∪ S.Con) inferInstance
    have hcons := consistent_of_models_con S T (V := V)
    have hS := Theory.Δ₁.Sentential.forall_shift_eq (V := V) S
    have : Nonempty V := ⟨0⟩
    rw [DirectTranslation.Model.translate_iff]
    simp only [models_iff]
    have h := henkinTranslation_truth S T (V := V) σ (e := ![]) (u := ![]) (fun i ↦ i.elim0)
    refine h.mpr ?_
    rw [Bootstrapping.Semiformula.subst_nil_eq_self]
    exact HenkinSet.of_provable S (by simp) (internalize_provability (Entailment.by_axm hσ))

end sentential

omit [𝗘𝗤 L ⪯ S] [L.Eq] in
/-- The consistency statement of `S` for the numeration restricted to sentences follows from its
consistency statement for the given numeration. -/
lemma weakerThan_con_sentential :
    T ∪ @Theory.Con L _ _ S (Theory.Δ₁.sentential S inferInstance) ⪯ T ∪ S.Con :=
  Arithmetic.weakerThan_of_models.{0} _ _ fun (V : Type) _ _ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (T := 𝗣𝗔) (U := T ∪ S.Con) inferInstance
    have h₀ := Theory.Δ₁.sentential_consistent S (consistent_of_models_con S T (V := V))
    have hT : V↓[ℒₒᵣ] ⊧* T := models_of_ss (U := T ∪ S.Con) inferInstance Set.subset_union_left
    refine ⟨fun σ hσ ↦ ?_⟩
    rcases hσ with hσ | rfl
    · exact Semantics.ModelsSet.models_set hσ
    · simpa [models_iff] using h₀

/-- The theory `S` is interpretable in `T` and the consistency of `S`.

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.27], [HP98, 2.43] -/
noncomputable abbrev henkinInterpretation : T ∪ S.Con ⊳ S :=
  haveI := weakerThan_con_sentential S T
  (@henkinInterpretationOfSentential L _ _ _ S (Theory.Δ₁.sentential S inferInstance) _ T _ _
    ).ofWeakerThanLeft

end interpretation

end FFL.FirstOrder.Arithmetic
