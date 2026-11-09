module

public import Foundation.FirstOrder.Incompleteness.Reflection.Uniform
public import Foundation.FirstOrder.Incompleteness.Definability
public import AlphaCentauri.ToFoundation.Syntax
public import AlphaCentauri.ToFoundation.Coding

/-!
# $\Delta_1$ presentation of the uniform reflection schema

The uniform reflection schema of a $\Delta_1$ theory over the prenex classes is $\Delta_1$.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open FFL.FirstOrder.Theory Bootstrapping Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section ssnums

/-- `ssnumsConjunct i` is the code of the `i`-th conjunct of `ssnums`. -/
noncomputable def ssnumsConjunct (i : V) : V :=
  ^∃ (subst ℒₒᵣ ?[^#0, ^#1, numeral i] ⌜nthDef.val⌝ ^⋏
    subst ℒₒᵣ ?[^#0, ^#(i + 4)] ⌜numeralGraph.val⌝)

noncomputable def ssnumsConjunctGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y i.
    ∃ z₀, !qqBvarDef z₀ 0 ∧ ∃ z₁, !qqBvarDef z₁ 1 ∧ ∃ m, !numeralGraph m i ∧
    ∃ v₂, !adjoinDef v₂ m 0 ∧ ∃ v₁, !adjoinDef v₁ z₁ v₂ ∧ ∃ v₀, !adjoinDef v₀ z₀ v₁ ∧
    ∃ a, !(substsGraph ℒₒᵣ) a v₀ ↑(⌜nthDef.val⌝ : ℕ) ∧
    ∃ z₄, !qqBvarDef z₄ (i + 4) ∧ ∃ w₁, !adjoinDef w₁ z₄ 0 ∧ ∃ w₀, !adjoinDef w₀ z₀ w₁ ∧
    ∃ b, !(substsGraph ℒₒᵣ) b w₀ ↑(⌜numeralGraph.val⌝ : ℕ) ∧
    ∃ c, !qqAndDef c a b ∧ !qqExsDef y c”

instance ssnumsConjunct.defined :
    𝚺ᴬ₁-Function₁ (ssnumsConjunct : V → V) via ssnumsConjunctGraph := .mk fun v ↦ by
  simp [ssnumsConjunctGraph, ssnumsConjunct]

noncomputable def ssnumsConjuncts.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = 0”
  succ := .mkSigma “y ih n. ∃ c, !ssnumsConjunctGraph c n ∧ !concatDef y ih c”

noncomputable def ssnumsConjuncts.construction : PR.Construction V ssnumsConjuncts.blueprint where
  zero := fun _ ↦ 0
  succ := fun _ n ih ↦ concat ih (ssnumsConjunct n)
  zero_defined := .mk fun v ↦ by simp [ssnumsConjuncts.blueprint]
  succ_defined := .mk fun v ↦ by simp [ssnumsConjuncts.blueprint]

/-- `ssnumsConjuncts k = ⟨ssnumsConjunct 0, …, ssnumsConjunct (k - 1)⟩`. -/
noncomputable def ssnumsConjuncts (k : V) : V := ssnumsConjuncts.construction.result ![] k

@[simp] lemma ssnumsConjuncts_zero : ssnumsConjuncts (0 : V) = 0 := by
  simp [ssnumsConjuncts, ssnumsConjuncts.construction]

@[simp] lemma ssnumsConjuncts_succ (k : V) :
    ssnumsConjuncts (k + 1) = concat (ssnumsConjuncts k) (ssnumsConjunct k) := by
  simp [ssnumsConjuncts, ssnumsConjuncts.construction]

noncomputable def ssnumsConjunctsGraph : 𝚺ᴬ₁.Semisentence 2 := ssnumsConjuncts.blueprint.resultDef

instance ssnumsConjuncts.defined :
    𝚺ᴬ₁-Function₁ (ssnumsConjuncts : V → V) via ssnumsConjunctsGraph := .mk fun v ↦ by
  simp [ssnumsConjuncts.construction.result_defined_iff, ssnumsConjunctsGraph]; rfl

instance ssnumsConjuncts.definable : 𝚺ᴬ₁-Function₁ (ssnumsConjuncts : V → V) :=
  ssnumsConjuncts.defined.to_definable

@[simp] lemma len_ssnumsConjuncts (k : V) : len (ssnumsConjuncts k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

lemma nth_ssnumsConjuncts (k : V) : ∀ i < k, (ssnumsConjuncts k).[i] = ssnumsConjunct i := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro i hi
    rcases (lt_succ_iff_le.mp hi).lt_or_eq with hlt | rfl
    · rw [ssnumsConjuncts_succ, concat_nth_lt _ _ (by simpa using hlt)]; exact ih i hlt
    · rw [ssnumsConjuncts_succ, concat_nth_len' _ _ (by simp)]

/-- `ssnumsCode k` is the code of `ssnums` with `k` parameters. -/
noncomputable def ssnumsCode (k : V) : V :=
  ^∃ (subst ℒₒᵣ ?[numeral k, ^#0] ⌜lenDef.val⌝ ^⋏
    ((^⋀ ssnumsConjuncts k) ^⋏ subst ℒₒᵣ ?[^#1, ^#0, ^#2] ⌜(substsGraph ℒₒᵣ).val⌝))

noncomputable def ssnumsCodeGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y k.
    ∃ z₀, !qqBvarDef z₀ 0 ∧ ∃ z₁, !qqBvarDef z₁ 1 ∧ ∃ z₂, !qqBvarDef z₂ 2 ∧
    ∃ m, !numeralGraph m k ∧ ∃ v₁, !adjoinDef v₁ z₀ 0 ∧ ∃ v₀, !adjoinDef v₀ m v₁ ∧
    ∃ a, !(substsGraph ℒₒᵣ) a v₀ ↑(⌜lenDef.val⌝ : ℕ) ∧
    ∃ w₂, !adjoinDef w₂ z₂ 0 ∧ ∃ w₁, !adjoinDef w₁ z₀ w₂ ∧ ∃ w₀, !adjoinDef w₀ z₁ w₁ ∧
    ∃ b, !(substsGraph ℒₒᵣ) b w₀ ↑(⌜(substsGraph ℒₒᵣ).val⌝ : ℕ) ∧
    ∃ cs, !ssnumsConjunctsGraph cs k ∧ ∃ c, !qqConjGraph c cs ∧
    ∃ d, !qqAndDef d c b ∧ ∃ e, !qqAndDef e a d ∧ !qqExsDef y e”

instance ssnumsCode.defined : 𝚺ᴬ₁-Function₁ (ssnumsCode : V → V) via ssnumsCodeGraph :=
  .mk fun v ↦ by simp [ssnumsCodeGraph, ssnumsCode]

lemma ssnumsCode_quote (k : ℕ) : ssnumsCode (k : V) = ⌜(ssnums (k := k)).val⌝ := by
  unfold ssnums
  simp only [Bounding.HierarchySymbol.Semiformula.val_mkSigma, ssnumsCode, Sentence.quote_ex,
    Sentence.quote_and]
  congr 2
  · simp [Sentence.quote_def, Rewriting.emb_subst_eq_subst_emb, Semiformula.quote_substs,
      Matrix.vecHead, Matrix.vecTail, Semiterm.quote_def]
  · congr 1
    · rw [Semisentence.quote_conj]
      congr 1
      rw [eq_matrixToVec_iff]
      constructor
      · simp
      · intro i
        rw [nth_ssnumsConjuncts _ _ (by simp)]
        simp only [ssnumsConjunct, Sentence.quote_ex, Sentence.quote_and]
        congr 2
        · sorry
        · sorry
    · simp [Sentence.quote_def, Rewriting.emb_subst_eq_subst_emb, Semiformula.quote_substs,
        Matrix.vecHead, Matrix.vecTail, Semiterm.quote_def]
      sorry

end ssnums

end FFL.FirstOrder.Arithmetic
