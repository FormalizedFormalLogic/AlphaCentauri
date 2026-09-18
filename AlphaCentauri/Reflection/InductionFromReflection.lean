module

public import AlphaCentauri.Reflection.UniformReflection
public import AlphaCentauri.Schemata.ParameterFreeInduction
public import AlphaCentauri.ToFoundation.Provable
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.PeanoMinus
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.EquationalTheory

@[expose] public section
/-!
# Induction from uniform reflection

Each instance of the parameter-free induction schema follows, over a base theory `T₀ ⊇ 𝗜𝚺₁`,
from uniform reflection for `T₀` together with that instance's induction hypothesis, and
conversely each $\Pi_{n + 2}$ sentence has an induction instance proving that implication for
every reflection instance.

- [Bek99, Proposition 2.1]
- [Bek99, Proposition 2.2]
- [Bek99, Lemma 5.1]
-/

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping Bootstrapping.Arithmetic

/-- The induction hypothesis of `φ`: `φ(0) ⋏ ∀ x, φ(x) 🡒 φ(x + 1)`. -/
def inductionHypothesis (φ : ArithmeticSemisentence 1) : ArithmeticSentence :=
  “!φ 0 ∧ ∀ x, !φ x → !φ(x + 1)”

private lemma step_aux {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] (φ : ArithmeticSemisentence 1)
    (h : T ⊢ (“∀ x, !φ x → !φ(x + 1)” : ArithmeticSentence)) {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (x : V) (hx : Provable T (substNumeral (⌜φ⌝ : V) x)) :
    Provable T (substNumeral (⌜φ⌝ : V) (x + 1)) := by
  have h1 : Provable T (⌜(“∀ x, !φ x → !φ(x + 1)” : ArithmeticSentence)⌝ : V) :=
    internalize_provability h
  have h2 : T.internalize V ⊢ (⌜(“∀ x, !φ x → !φ(x + 1)” : ArithmeticSentence)⌝ :
      Bootstrapping.Formula V ℒₒᵣ) := tprovable_iff_provable.mpr h1
  simp only [LCWQIsoGödelQuote.all, LCWQIsoGödelQuote.imply] at h2
  have h3 := TProof.specialize! h2 (𝕹 x)
  simp only [Semiformula.substs_imp, Sentence.typed_quote_def,
    Rewriting.emb_subst_eq_subst_coe₁, Semiformula.typed_quote_substs] at h3
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue, Rew.emb_bvar,
    Matrix.cons_val_fin_one, Semiterm.typed_quote_bvar, ← Sentence.typed_quote_def,
    Semiformula.substs_substs, Matrix.vecMap_cons', Matrix.head_fin_const, Semiterm.substs_bvar,
    Matrix.vecMap_nil, Rew.finitary2, Rew.finitary0, Semiterm.typed_quote_add,
    Semiterm.typed_quote_numeral_eq_numeral, Nat.cast_one, subst_add, subst_numeral] at h3
  have : 𝗣𝗔⁻ ⪯ T := Entailment.WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ 𝗜𝚺₁) ‹𝗜𝚺₁ ⪯ T›
  have hadd : T.internalize V ⊢ (𝕹 x + 𝕹 1 : Bootstrapping.Semiterm V ℒₒᵣ 0) ≐ 𝕹 (x + 1) :=
    Bootstrapping.Arithmetic.numeral_add T x 1
  have hrep := Bootstrapping.Arithmetic.replace T ⌜φ⌝ (𝕹 x + 𝕹 1) (𝕹 (x + 1)) ⨀ hadd
  have hxTyped : T.internalize V ⊢ (⌜φ⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1).subst ![𝕹 x] :=
    tprovable_iff_provable.mpr (by simpa [substNumeral, Sentence.quote_eq] using hx)
  have := hrep ⨀ (h3 ⨀ hxTyped)
  simpa [substNumeral, Sentence.quote_eq] using tprovable_iff_provable.mp this

/-- Each instance of parameter-free induction for `φ` follows over `T₀` from `φ`'s induction
hypothesis together with uniform reflection for `T₀` and that induction hypothesis, provided `Γ`
places `φ` in the reflection schema.
- [Bek99, Proposition 2.1] -/
theorem provable_all_of_uniformReflection {T₀ : ArithmeticTheory} [T₀.Δ₁] [𝗜𝚺₁ ⪯ T₀]
    {Γ : ∀ {k : ℕ}, ArithmeticSemisentence k → Prop} (φ : ArithmeticSemisentence 1) (hφ : Γ φ) :
    (T₀ ∪ {inductionHypothesis φ}) ∪ 𝗥𝗙𝗡[Γ] (T₀ ∪ {inductionHypothesis φ}) ⊢ ∀¹ φ := by
  set U : ArithmeticTheory := T₀ ∪ {inductionHypothesis φ}
  have hU : 𝗜𝚺₁ ⪯ U := Entailment.WeakerThan.trans ‹𝗜𝚺₁ ⪯ T₀› inferInstance
  have hUR : 𝗜𝚺₁ ⪯ (U ∪ 𝗥𝗙𝗡[Γ] U) := Entailment.WeakerThan.trans hU inferInstance
  have hEQ : 𝗘𝗤 ℒₒᵣ ⪯ (U ∪ 𝗥𝗙𝗡[Γ] U) :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₁) hUR
  apply Arithmetic.complete.{0} (U ∪ 𝗥𝗙𝗡[Γ] U) (∀¹ φ)
  intro (V : Type) _ hVmod
  have hVI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory hVmod
  have hIH : U ⊢ inductionHypothesis φ := Axiomatized.by_axm (Set.mem_union_right _ rfl)
  have hbase : Provable U (substNumeral (⌜φ⌝ : V) 0) := by
    have hIH0 : U ⊢ (“!φ 0” : ArithmeticSentence) := K_left hIH
    have h0 : Provable U (⌜(“!φ 0” : ArithmeticSentence)⌝ : V) := internalize_provability hIH0
    have heq : (substNumeral (⌜φ⌝ : V) 0) = ⌜(“!φ 0” : ArithmeticSentence)⌝ := by
      have h := substNumerals_app_quote (V := V) φ (fun _ : Fin 1 ↦ (0 : ℕ))
      simp only [substNumerals, substNumeral, Matrix.constant_eq_singleton, Nat.cast_zero] at h ⊢
      exact h
    rw [heq]; exact h0
  have hstep : ∀ x : V, Provable U (substNumeral (⌜φ⌝ : V) x) →
      Provable U (substNumeral (⌜φ⌝ : V) (x + 1)) := by
    intro x hx
    have hIHstep : U ⊢ (“∀ x, !φ x → !φ(x + 1)” : ArithmeticSentence) := K_right hIH
    exact step_aux φ hIHstep x hx
  have hall : ∀ x : V, Provable U (substNumeral (⌜φ⌝ : V) x) := by
    intro x
    induction x using ISigma1.sigma1_succ_induction
    · definability
    case zero => exact hbase
    case succ x ih => exact hstep x ih
  have hσmem : U.globalReflectionSchema φ ∈ (U ∪ 𝗥𝗙𝗡[Γ] U) :=
    Set.mem_union_right _ ⟨1, φ, hφ, rfl⟩
  have hσmodel : V↓[ℒₒᵣ] ⊧ U.globalReflectionSchema φ := hVmod.models_set hσmem
  have hrfn := (models_globalReflectionSchema_iff U φ).mp (by simpa [models_iff] using hσmodel)
  simp only [models_iff, Semiformula.eval_all]
  intro x
  have hx' : Provable U (substNumerals (⌜φ⌝ : V) ![x]) := by
    simpa [substNumerals, substNumeral] using hall x
  simpa using hrfn ![x] hx'

/-- The converse of `provable_all_of_uniformReflection`, quoted by Bek99 from Beklemishev 1997
without proof: every $\Pi_{n + 2}$ sentence `P` has a $\Pi_{n + 1}$ induction instance over `T₀`
proving `P 🡒 σ`, for every uniform $\Pi_{n + 1}$ reflection instance `σ` for `T₀ ∪ {P}`.
- [Bek99, Proposition 2.1]
- [Bek99, Lemma 5.1] -/
axiom uniformReflection_of_parameterFreeInduction {n : ℕ} {T₀ : ArithmeticTheory} [T₀.Δ₁]
    (hT₀ : 𝗜𝚺₁ ⪯ T₀) (P : ArithmeticSentence) (hP : StrictHierarchy 𝚷 (n + 2) P) :
    ∃ φ : ArithmeticSemisentence 1, StrictHierarchy 𝚷 (n + 1) φ ∧
      ∀ σ ∈ 𝗥𝗙𝗡[StrictHierarchy 𝚷 (n + 1)] (T₀ ∪ {P}),
        T₀ ∪ {parameterFreeSuccInd ℒₒᵣ φ} ⊢ P 🡒 σ

end FFL.FirstOrder.Arithmetic
