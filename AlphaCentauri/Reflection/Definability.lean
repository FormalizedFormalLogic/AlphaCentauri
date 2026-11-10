module

public import Foundation.FirstOrder.Incompleteness.Reflection.Uniform
public import Foundation.FirstOrder.Incompleteness.Definability
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Coding
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Iteration
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
public import AlphaCentauri.ToFoundation.FirstOrder.BinderNotation
public import AlphaCentauri.ToFoundation.FirstOrder.Fvar
public import AlphaCentauri.ToFoundation.FirstOrder.Rew
public import AlphaCentauri.ToFoundation.FirstOrder.Semiformula
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions

/-!
# $\Delta_1$ presentation of the uniform reflection schema

The code of `ssnums` as a function of the arity, the code of the uniform reflection schema as a
function of the arity and the code of the formula, the $\Delta_1$ predicate on codes defining the
schema, and the resulting $\Delta_1$ presentation of `𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n] T`.
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
  rw [Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  rw [Sentence.quote_ex, Sentence.quote_and, Sentence.quote_and, Semisentence.quote_substs,
    Semisentence.quote_substs, Semisentence.quote_conj]
  have hc : (matrixToVec fun i : Fin k ↦ (⌜(∃¹ ((nthDef.val : ArithmeticSemisentence 3) ⇜
      ![#0, #1, ↑(i : ℕ)] ⋏ (numeralGraph.val : ArithmeticSemisentence 2) ⇜
        ![#0, #i.succ.succ.succ.succ]) : ArithmeticSemisentence (k + 2 + 1))⌝ : V)) =
      ssnumsConjuncts (k : V) := by
    symm
    rw [eq_matrixToVec_iff]
    constructor
    · simp
    · intro i
      rw [nth_ssnumsConjuncts _ _ (by simp)]
      rw [Sentence.quote_ex, Sentence.quote_and, Semisentence.quote_substs,
        Semisentence.quote_substs]
      simp only [matrixToVec_succ, matrixToVec_nil, Matrix.vecHead, Matrix.vecTail,
        Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_succ, Semiterm.empty_quote_bvar,
        Semiterm.empty_quote_numeral, Fin.val_succ, ssnumsConjunct]
      have h : ((i : ℕ) : V) + 1 + 1 + 1 + 1 = (i : ℕ) + 4 := by
        simp only [add_assoc]; norm_num
      simp [h]
  rw [hc]
  simp only [matrixToVec_succ, matrixToVec_nil, Matrix.vecHead, Matrix.vecTail, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Semiterm.empty_quote_bvar,
    Semiterm.empty_quote_numeral, ssnumsCode]
  simp [Nat.mod_eq_of_lt (show 2 < k + 2 + 1 by omega)]

end ssnums

section uniformReflectionCode

lemma quote_bShift {k : ℕ} (φ : ArithmeticSemisentence k) :
    (⌜(Rew.bShift ▹ φ : ArithmeticSemisentence (k + 1))⌝ : V) =
      subst ℒₒᵣ (bvarVec 1 (k : V)) ⌜φ⌝ := by
  erw [Rew.bShift_eq_subst, Semisentence.quote_substs]
  simp [bvarVec_eq_matrixToVec]

lemma subst_quote_bShift {k : ℕ} (φ : ArithmeticSemisentence k) :
    subst ℒₒᵣ (numeral 0 ∷ bvarVec 0 (k : V))
      (⌜(Rew.bShift ▹ φ : ArithmeticSemisentence (k + 1))⌝ : V) = ⌜φ⌝ := by
  have h : (Rew.bShift ▹ φ : ArithmeticSemisentence (k + 1)) ⇜
      ((↑(0 : ℕ) : ClosedSemiterm ℒₒᵣ k) :> fun i ↦ #i) = φ := by
    change (Rew.subst _) ▹ (Rew.bShift ▹ φ) = φ
    rw [← TransitiveRewriting.comp_app]
    have hid : (Rew.subst ((↑(0 : ℕ) : ClosedSemiterm ℒₒᵣ k) :> fun i ↦ #i)).comp Rew.bShift =
        Rew.id := by
      ext x
      · simp [Rew.comp_app]
      · exact x.elim
    simp [hid]
  have e := Semisentence.quote_substs (V := V)
    ((↑(0 : ℕ) : ClosedSemiterm ℒₒᵣ k) :> fun i ↦ #i) (Rew.bShift ▹ φ)
  rw [h] at e
  rw [e]
  simp [bvarVec_eq_matrixToVec, Matrix.vecHead, Matrix.vecTail, Function.comp_def]

variable (T : ArithmeticTheory) [T.Δ₁]

/-- The code of `T.uniformReflectionSchema φ` as a function of the arity `k` and the code `q` of
`φ`. -/
noncomputable def uniformReflectionCode (k q : V) : V :=
  qqAlls (^∀ (imp ℒₒᵣ (subst ℒₒᵣ (^#0 ∷ numeral q ∷ bvarVec 1 k) (ssnumsCode k))
    (imp ℒₒᵣ (subst ℒₒᵣ ?[^#0] ⌜T.standardProvability.prov⌝) (subst ℒₒᵣ (bvarVec 1 k) q)))) k

lemma uniformReflectionCode_quote {k : ℕ} (φ : ArithmeticSemisentence k) :
    uniformReflectionCode T (k : V) ⌜φ⌝ = ⌜T.uniformReflectionSchema φ⌝ := by
  rw [Theory.uniformReflectionSchema, Bootstrapping.quote_allClosure_sentence, Sentence.quote_all,
    Semisentence.quote_imp, Semisentence.quote_imp]
  erw [Semisentence.quote_substs, Semisentence.quote_substs, Rew.bShift_eq_subst,
    Semisentence.quote_substs]
  simp only [matrixToVec_succ, Matrix.vecHead, Matrix.vecTail, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_succ, matrixToVec_nil,
    Semiterm.empty_quote_bvar, Semiterm.empty_quote_numeral, Fin.val_succ, Nat.cast_succ,
    ← bvarVec_eq_matrixToVec, ← ssnumsCode_quote, ← Sentence.quote_eq_encode]
  simp [uniformReflectionCode]

noncomputable def uniformReflectionCodeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y k q.
    ∃ z₀, !qqBvarDef z₀ 0 ∧ ∃ m, !numeralGraph m q ∧ ∃ bs, !bvarVecDef bs 1 k ∧
    ∃ v₁, !adjoinDef v₁ m bs ∧ ∃ v₀, !adjoinDef v₀ z₀ v₁ ∧ ∃ c, !ssnumsCodeGraph c k ∧
    ∃ a, !(substsGraph ℒₒᵣ) a v₀ c ∧ ∃ u, !adjoinDef u z₀ 0 ∧
    ∃ pr, !(substsGraph ℒₒᵣ) pr u ↑(Encodable.encode T.standardProvability.prov) ∧
    ∃ sh, !(substsGraph ℒₒᵣ) sh bs q ∧ ∃ i₂, !(impGraph ℒₒᵣ) i₂ pr sh ∧
    ∃ i₁, !(impGraph ℒₒᵣ) i₁ a i₂ ∧ ∃ al, !qqAllDef al i₁ ∧ !qqAllsDef y al k”

instance uniformReflectionCode.defined :
    𝚺ᴬ₁-Function₂ (uniformReflectionCode T : V → V → V) via uniformReflectionCodeGraph T :=
  .mk fun v ↦ by
    simp [uniformReflectionCodeGraph, uniformReflectionCode, Sentence.quote_eq_encode,
      numeral_eq_natCast]

lemma le_uniformReflectionCode (k q : V) :
    subst ℒₒᵣ (bvarVec 1 k) q ≤ uniformReflectionCode T k q :=
  (lt_or_right _ _).le.trans <| (lt_or_right _ _).le.trans <| (le_qqAll _).trans <| le_qqAlls _ _

/-- `UniformReflectionR T S p` holds when `p` codes `T.uniformReflectionSchema φ` for a
semisentence `φ` whose code satisfies `S`. -/
def UniformReflectionR (S : V → Prop) (p : V) : Prop :=
  ∃ k ≤ p, ∃ b ≤ p, ∃ q, q = subst ℒₒᵣ (numeral 0 ∷ bvarVec 0 k) b ∧
    IsSemiformula ℒₒᵣ k q ∧ shift ℒₒᵣ q = q ∧ S q ∧ p = uniformReflectionCode T k q

noncomputable def chUniformReflection (cond : 𝚫ᴬ₁.Semisentence 1) : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “p.
    ∃ k < p + 1, ∃ b < p + 1, ∃ w, !bvarVecDef w 0 k ∧ ∃ z, !numeralGraph z 0 ∧
      ∃ v, !adjoinDef v z w ∧ ∃ q, !(substsGraph ℒₒᵣ) q v b ∧
        !(isSemiformula ℒₒᵣ).sigma k q ∧ !(shiftGraph ℒₒᵣ) q q ∧ !cond.sigma q ∧
          !(uniformReflectionCodeGraph T) p k q”)
  (.mkPi “p.
    ∃ k < p + 1, ∃ b < p + 1, ∀ w, !bvarVecDef w 0 k → ∀ z, !numeralGraph z 0 →
      ∀ v, !adjoinDef v z w → ∀ q, !(substsGraph ℒₒᵣ) q v b →
        !(isSemiformula ℒₒᵣ).pi k q ∧ (∀ y, !(shiftGraph ℒₒᵣ) y q → y = q) ∧ !cond.pi q ∧
          ∀ y, !(uniformReflectionCodeGraph T) y k q → p = y”)

instance UniformReflectionR.defined {S : V → Prop} {cond : 𝚫ᴬ₁.Semisentence 1}
    [hcond : 𝚫ᴬ₁-Predicate[V] S via cond] :
    𝚫ᴬ₁-Predicate[V] (UniformReflectionR T S : V → Prop) via chUniformReflection T cond := .mk <| by
  constructor
  · intro v; simp [chUniformReflection, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm]
  · intro v
    simp [chUniformReflection, Bounding.HierarchySymbol.Semiformula.val_sigma, UniformReflectionR,
      lt_succ_iff_le, eq_comm]

lemma uniformReflectionR_quote_iff {S : ℕ → Prop} {Γ : ∀ {k : ℕ}, ArithmeticSemisentence k → Prop}
    (hS : ∀ k (φ : ArithmeticSemisentence k), S ⌜φ⌝ ↔ Γ φ) (ψ : ArithmeticSemiproposition 0) :
    UniformReflectionR T S (⌜ψ⌝ : ℕ) ↔ ∃ σ ∈ 𝗥𝗙𝗡[Γ] T, ψ = σ := by
  constructor
  · rintro ⟨k, -, b, -, q, -, hq, hsh, hSq, hp⟩
    obtain ⟨F, rfl⟩ := IsSemiformula.sound hq
    have hfree : F.freeVariables = ∅ := Semiformula.freeVariables_eq_empty_of_shift_eq <|
      (Semiformula.quote_inj_iff (V := ℕ)).mp <| by rw [Semiformula.quote_shift]; exact hsh
    set φ := F.toEmpty hfree
    have hφ : (⌜φ⌝ : ℕ) = ⌜F⌝ := by simp [φ, Sentence.quote_def, Semiformula.emb_toEmpty]
    use T.uniformReflectionSchema φ
    and_intros
    · use k, φ
      and_intros
      · exact (hS k φ).mp <| hφ ▸ hSq
      · rfl
    · apply (Semiformula.quote_inj_iff (V := ℕ)).mp
      rw [hp, ← hφ, ← Sentence.quote_def]
      simpa using uniformReflectionCode_quote (V := ℕ) T φ
  · rintro ⟨_, ⟨k, φ, hφ, rfl⟩, rfl⟩
    have hp : (⌜(T.uniformReflectionSchema φ : ArithmeticSemiproposition 0)⌝ : ℕ) =
        uniformReflectionCode T k ⌜φ⌝ := by
      simpa [← Sentence.quote_def] using (uniformReflectionCode_quote (V := ℕ) T φ).symm
    rw [hp]
    use k
    and_intros
    · exact index_le_qqAlls _ _
    · use ⌜(Rew.bShift ▹ φ : ArithmeticSemisentence (k + 1))⌝
      and_intros
      · rw [quote_bShift]
        simpa using le_uniformReflectionCode (V := ℕ) T k ⌜φ⌝
      · use ⌜φ⌝
        and_intros
        · simpa using (subst_quote_bShift (V := ℕ) φ).symm
        · simpa using Sentence.quote_isSemiformula (V := ℕ) φ
        · exact Semisentence.shift_quote φ
        · exact (hS k φ).mpr hφ
        · simp

noncomputable abbrev _root_.FFL.FirstOrder.Theory.uniformReflectionOn.delta1_of
    {Γ : ∀ {k : ℕ}, ArithmeticSemisentence k → Prop} {cond : 𝚫ᴬ₁.Semisentence 1}
    {S : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V → Prop}
    (hS : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], 𝚫ᴬ₁-Predicate[V] S V via cond)
    (hC : ∀ k (φ : ArithmeticSemisentence k), S ℕ ⌜φ⌝ ↔ Γ φ) :
    Theory.Δ₁ (𝗥𝗙𝗡[Γ] T) where
  ch := chUniformReflection T cond
  mem_iff ψ := by
    have := hS ℕ
    simpa using uniformReflectionR_quote_iff T hC ψ
  isDelta1 :=
    Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
      fun V _ _ ↦ (UniformReflectionR.defined T (hcond := hS V)).proper

noncomputable instance _root_.FFL.FirstOrder.Theory.uniformReflectionOn.delta1_prenexHierarchy
    (Γ : Polarity) (n : ℕ) : Theory.Δ₁ (𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n] T) :=
  Theory.uniformReflectionOn.delta1_of T (fun _ _ _ ↦ IsPrenexHierarchy.defined Γ n)
    fun _ ↦ isPrenexHierarchy_quote_iff

end uniformReflectionCode

end FFL.FirstOrder.Arithmetic
