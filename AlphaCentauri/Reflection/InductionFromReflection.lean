module

public import AlphaCentauri.Reflection.UniformReflection
public import AlphaCentauri.Schemata.ParameterFreeInduction
public import AlphaCentauri.ToFoundation.Fvar
public import AlphaCentauri.ToFoundation.PrenexCombination
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

/-- `∀ x, φ(x)` follows over `T₀` from `φ`'s induction hypothesis together with uniform reflection
for `T₀` and that induction hypothesis, provided `Γ` places `φ` in the reflection schema.
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
  have hσmem : U.uniformReflectionSchema φ ∈ (U ∪ 𝗥𝗙𝗡[Γ] U) :=
    Set.mem_union_right _ ⟨1, φ, hφ, rfl⟩
  have hσmodel : V↓[ℒₒᵣ] ⊧ U.uniformReflectionSchema φ := hVmod.models_set hσmem
  have hrfn := (models_uniformReflectionSchema_iff U φ).mp (by simpa [models_iff] using hσmodel)
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
    (hT₀ : 𝗜𝚺₁ ⪯ T₀) (P : ArithmeticSentence) (hP : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2) P) :
    ∃ φ : ArithmeticSemisentence 1, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 1) φ ∧
      ∀ σ ∈ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 1)] (T₀ ∪ {P}),
        T₀ ∪ {parameterFreeSuccInd ℒₒᵣ φ} ⊢ P 🡒 σ

section inductionImplication

open Bounding

universe u

variable {ξ : Type*} {n m : ℕ}

/-- The induction instance of a prenex $\Sigma_n$ formula `ψ(x, p⃗)` at `x` is equivalent, in every
model of `𝗜𝗢𝗽𝗲𝗻`, to a prenex $\Pi_{n + 2}$ formula. -/
lemma exists_inductionImplication (ψ : ℬ[<, ℒₒᵣ].Prenex 𝚺 n ξ (m + 1)) :
    ∃ θ : Semiformula ℒₒᵣ ξ (m + 1), ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2) θ ∧
      ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (f : ξ → V) (x : V) (p : Fin m → V),
        Semiformula.Eval (x :> p) f θ ↔
          (Semiformula.Eval (0 :> p) f ψ.val →
            (∀ y, Semiformula.Eval (y :> p) f ψ.val → Semiformula.Eval ((y + 1) :> p) f ψ.val) →
              Semiformula.Eval (x :> p) f ψ.val) := by
  obtain ⟨_, ⟨A, rfl⟩, hA⟩ := (PrenexHierarchy.rew (Rew.subst (‘0’ :> fun i ↦ #i.succ))
    ψ.val_prenexHierarchy).neg.exists_eval_iff_of_lt.{_, u} 𝚺 (Nat.lt_succ_self n)
  obtain ⟨_, ⟨B, rfl⟩, hB⟩ := (PrenexHierarchy.rew (Rew.subst (‘#0 + 1’ :> fun i ↦ #i.succ.succ))
    ψ.val_prenexHierarchy).neg.exists_eval_iff_of_lt.{_, u} 𝚺 (Nat.lt_succ_self n)
  obtain ⟨_, ⟨θ, rfl⟩, hθ⟩ := (Prenex.pairOr A <| Prenex.pairOr
      (Prenex.pairExs <| Prenex.pairAnd (ψ.rew (Rew.subst (#0 :> fun i ↦ #i.succ.succ))).succ B)
      ψ.succ).val_prenexHierarchy.exists_eval_iff_of_lt.{_, u} 𝚷 (Nat.lt_succ_self (n + 1))
  refine ⟨θ.val, θ.val_prenexHierarchy, fun V _ _ f x p ↦ ?_⟩
  have h₀ : (fun i ↦ Semiterm.val (x :> p) f
      ((‘0’ :> fun i ↦ #i.succ : Fin (m + 1) → ArithmeticSemiterm ξ (m + 1)) i)) = 0 :> p :=
    funext <| Fin.cases (by simp) (by simp)
  have h₁ (y : V) : (fun i ↦ Semiterm.val (y :> x :> p) f
      ((#0 :> fun i ↦ #i.succ.succ : Fin (m + 1) → ArithmeticSemiterm ξ (m + 2)) i)) = y :> p :=
    funext <| Fin.cases (by simp) (by simp)
  have h₂ (y : V) : (fun i ↦ Semiterm.val (y :> x :> p) f
      ((‘#0 + 1’ :> fun i ↦ #i.succ.succ : Fin (m + 1) → ArithmeticSemiterm ξ (m + 2)) i)) =
      (y + 1) :> p :=
    funext <| Fin.cases (by simp) (by simp)
  simp only [← hθ, Prenex.eval_pairOr, Prenex.eval_pairExs, Prenex.eval_pairAnd,
    Prenex.models_succ, ← hA, ← hB, LogicalConnective.HomClass.map_neg, Prenex.val_rew,
    Semiformula.eval_rew, Function.comp_def, Rew.subst_bvar, Rew.subst_fvar, Semiterm.val_fvar,
    h₀, h₁, h₂, LogicalConnective.Prop.neg_eq]
  grind

end inductionImplication

section uniformReflection

variable {m : ℕ} {ψ θ : ArithmeticSemisentence (m + 1)}

section

variable (hθ : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (f : Empty → V) (x : V)
  (p : Fin m → V), Semiformula.Eval (x :> p) f θ ↔
    (Semiformula.Eval (0 :> p) f ψ →
      (∀ y, Semiformula.Eval (y :> p) f ψ → Semiformula.Eval ((y + 1) :> p) f ψ) →
        Semiformula.Eval (x :> p) f ψ))
include hθ

private lemma provable_inductionImplication_zero :
    𝗘𝗔 ⊢ ∀¹* (Rew.subst (‘0’ :> fun i ↦ #i) ▹ θ) := by
  apply Arithmetic.complete.{0}
  intro V _ _
  have h (p : Fin m → V) : (fun i ↦ Semiterm.val p Empty.elim
      ((‘0’ :> fun i ↦ #i : Fin (m + 1) → ArithmeticSemiterm Empty m) i)) = 0 :> p :=
    funext <| Fin.cases (by simp) (by simp)
  simp only [models_iff, Semiformula.eval_allClosure]
  intro p
  simp only [Semiformula.eval_rew, Function.comp_def, Rew.subst_bvar, h,
    show ∀ g : Empty → V, g = Empty.elim from fun _ ↦ funext (·.elim), hθ]
  intro h₀ _
  exact h₀

private lemma provable_inductionImplication_succ :
    𝗘𝗔 ⊢ ∀¹* (θ 🡒 Rew.subst (‘#0 + 1’ :> fun i ↦ #i.succ) ▹ θ) := by
  apply Arithmetic.complete.{0}
  intro V _ _
  have h (x : V) (p : Fin m → V) : (fun i ↦ Semiterm.val (x :> p) Empty.elim
      ((‘#0 + 1’ :> fun i ↦ #i.succ : Fin (m + 1) → ArithmeticSemiterm Empty (m + 1)) i)) =
      (x + 1) :> p :=
    funext <| Fin.cases (by simp) (by simp)
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  obtain ⟨x, p, rfl⟩ : ∃ x p, e = x :> p := ⟨_, _, (Matrix.cons_head_tail e).symm⟩
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_rew, Function.comp_def,
    Rew.subst_bvar, h, show ∀ g : Empty → V, g = Empty.elim from fun _ ↦ funext (·.elim),
    LogicalConnective.Prop.arrow_eq, hθ]
  intro hx h₀ hs
  exact hs _ (hx h₀ hs)

end

/-- A model of `𝗜𝚺₁` and of uniform prenex $\Pi_{n + 2}$ reflection for `𝗘𝗔` satisfies induction
for prenex $\Sigma_n$ formulas.
- [Bek05, Theorem 7] -/
lemma models_succInd_of_uniformReflection {n : ℕ} {V : Type} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔]
    {φ : ArithmeticSemiformula ℕ 1} (hφ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n φ) :
    V↓[ℒₒᵣ] ⊧ .univCl (succInd φ) := by
  obtain ⟨χ, rfl⟩ := hφ
  set ψ := χ.rew (χ.val.paramSubst ![#0])
  obtain ⟨θ, hθ, hθψ⟩ := exists_inductionImplication.{0} ψ
  simp only [models_iff, Semiformula.eval_univCl, succInd]
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Semiformula.eval_all,
    LogicalConnective.Prop.arrow_eq]
  intro f
  have hψ (x : V) :
      Semiformula.Eval (x :> fun i ↦ f i) Empty.elim ψ.val ↔ χ.val.Eval ![x] f :=
    (χ.val_rew _).symm ▸ Semiformula.eval_toSemisentence_one χ.val x f
  have hrfn : V ⊧/![] (𝗘𝗔.uniformReflectionSchema θ) :=
    models_iff.mp <| Semantics.ModelsSet.models _
      (show _ ∈ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔 from ⟨_, θ, hθ, rfl⟩)
  intro h₀ hs x
  have hprov := provable_substNumerals_of_provable_zero_of_provable_succ θ
    (provable_inductionImplication_zero hθψ) (provable_inductionImplication_succ hθψ) x
    (fun i ↦ f i)
  have h := (hθψ V Empty.elim x _).mp ((models_uniformReflectionSchema_iff 𝗘𝗔 θ).mp hrfn _ hprov)
  simp only [hψ] at h
  simpa using h (by simpa using h₀) (by simpa using hs)

/-- Uniform prenex $\Pi_{n + 2}$ reflection for `𝗘𝗔` over `𝗜𝚺₁` yields `𝗜𝚺 n`.
- [Bek05, Theorem 7] -/
theorem ISigma_weakerThan_ISigma1_union_uniformReflectionOn_Pi (n : ℕ) :
    𝗜𝚺 n ⪯ 𝗜𝚺₁ ∪ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔 :=
  weakerThan_of_models.{0} _ _ fun V _ hV ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
      ModelsTheory.of_add_left V 𝗜𝚺₁ (𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔)
    have : V↓[ℒₒᵣ] ⊧* 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔 :=
      ModelsTheory.of_add_right V 𝗜𝚺₁ (𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔)
    simp only [Semantics.ModelsSet.union_iff, InductionScheme]
    and_intros
    · infer_instance
    · apply Semantics.ModelsSet.setOf_iff.mpr
      rintro _ ⟨φ, hφ, rfl⟩
      exact models_succInd_of_uniformReflection hφ

end uniformReflection

end FFL.FirstOrder.Arithmetic
