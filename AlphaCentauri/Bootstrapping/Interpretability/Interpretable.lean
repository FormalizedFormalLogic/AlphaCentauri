module

public import AlphaCentauri.Bootstrapping.Interpretability.CaseSplit
public import AlphaCentauri.Bootstrapping.Interpretability.Composition
public import AlphaCentauri.Bootstrapping.Interpretability.Identity
public import AlphaCentauri.Bootstrapping.Interpretability.Soundness
public import AlphaCentauri.Bootstrapping.Interpretability.TranslationTable
public import AlphaCentauri.Bootstrapping.Proof.Deduction
public import AlphaCentauri.Bootstrapping.Proof.ProofByCases

/-!
# Interpretability in a model

In a model `V` of $\mathsf{I}\Sigma_1$, a theory `U` of $L_2$ is interpretable in a theory `S` of
$L_1$ when there is a table of a translation of $L_2$ in `S` along which every axiom of `U` in `V`
translates to a formula provable in `S`. The sentence `interpretableDef S U` defines this in every
model of $\mathsf{I}\Sigma_1$. Consistency transfers along interpretability.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding



/-! ## Graphs of the codes of the conditions on a table -/

section graphs

variable (L : Language) [L.Encodable] [L.LORDefinable] [L.Eq]

/-- The $\Sigma_1$ graph of `funcExistsCode`, with argument order `(y, tbl, k, f)`. -/
noncomputable def funcExistsCodeGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y tbl k f. ∃ dv, !(domainVecGraph L) dv tbl 0 k ∧ ∃ c, !qqConjGraph c dv ∧
    ∃ d, !(domainAtGraph L) d tbl 0 ∧ ∃ g, !tableFuncGraph g tbl k f ∧ ∃ b, !qqBvarDef b 0 ∧
    ∃ bs, !bvarVecDef bs 1 k ∧ ∃ w, !adjoinDef w b bs ∧ ∃ sg, !(substsGraph L) sg w g ∧
    ∃ a, !qqAndDef a d sg ∧ ∃ e, !qqExsDef e a ∧ !(impGraph L) y c e”

/-- The $\Sigma_1$ graph of `funcUniqueCode`, with argument order `(y, tbl, k, f)`. -/
noncomputable def funcUniqueCodeGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y tbl k f. ∃ dv, !(domainVecGraph L) dv tbl 2 k ∧ ∃ c, !qqConjGraph c dv ∧
    ∃ d₀, !(domainAtGraph L) d₀ tbl 0 ∧ ∃ d₁, !(domainAtGraph L) d₁ tbl 1 ∧
    ∃ g, !tableFuncGraph g tbl k f ∧ ∃ b₀, !qqBvarDef b₀ 0 ∧ ∃ b₁, !qqBvarDef b₁ 1 ∧
    ∃ bs, !bvarVecDef bs 2 k ∧ ∃ w₀, !adjoinDef w₀ b₀ bs ∧ ∃ w₁, !adjoinDef w₁ b₁ bs ∧
    ∃ s₀, !(substsGraph L) s₀ w₀ g ∧ ∃ s₁, !(substsGraph L) s₁ w₁ g ∧
    ∃ a₃, !qqAndDef a₃ s₀ s₁ ∧ ∃ a₂, !qqAndDef a₂ d₁ a₃ ∧ ∃ a₁, !qqAndDef a₁ d₀ a₂ ∧
    ∃ a₀, !qqAndDef a₀ c a₁ ∧ ∃ e, !mkVec₂Def e b₀ b₁ ∧
    ∃ r, !qqRelDef r 2 ↑(Encodable.encode (Language.Eq.eq : L.Rel 2)) e ∧ !(impGraph L) y a₀ r”

/-- The $\Sigma_1$ graph of `funcCongrCode`, with argument order `(y, tbl, k, f)`. -/
noncomputable def funcCongrCodeGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y tbl k f. ∃ ev, !(equationVecGraph L) ev 0 (k + 1) (k + 1) ∧ ∃ c, !qqConjGraph c ev ∧
    ∃ g, !tableFuncGraph g tbl k f ∧ ∃ bs₀, !bvarVecDef bs₀ 0 (k + 1) ∧
    ∃ bs₁, !bvarVecDef bs₁ (k + 1) (k + 1) ∧ ∃ s₀, !(substsGraph L) s₀ bs₀ g ∧
    ∃ s₁, !(substsGraph L) s₁ bs₁ g ∧ ∃ i, !(impGraph L) i s₀ s₁ ∧ !(impGraph L) y c i”

variable {L}

instance funcExistsCode.defined :
    𝚺ᴬ₁-Function₃[V] funcExistsCode L via funcExistsCodeGraph L :=
  .mk fun v ↦ by simp [funcExistsCodeGraph, funcExistsCode]

instance funcUniqueCode.defined :
    𝚺ᴬ₁-Function₃[V] funcUniqueCode L via funcUniqueCodeGraph L :=
  .mk fun v ↦ by simp [funcUniqueCodeGraph, funcUniqueCode, numeral_eq_natCast]

instance funcCongrCode.defined :
    𝚺ᴬ₁-Function₃[V] funcCongrCode L via funcCongrCodeGraph L :=
  .mk fun v ↦ by simp [funcCongrCodeGraph, funcCongrCode]

variable (L₁ L₂ : Language) [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq]

/-- The $\Sigma_1$ graph of `preserveEqCode`, with argument order `(y, tbl)`. -/
noncomputable def preserveEqCodeGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y tbl. ∃ d₁, !(domainAtGraph L₁) d₁ tbl 1 ∧ ∃ d₀, !(domainAtGraph L₁) d₀ tbl 0 ∧
    ∃ b₁, !qqBvarDef b₁ 1 ∧ ∃ b₀, !qqBvarDef b₀ 0 ∧ ∃ w, !mkVec₂Def w b₁ b₀ ∧
    ∃ r, !tableRelGraph r tbl 2 ↑(Encodable.encode (Language.Eq.eq : L₂.Rel 2)) ∧
    ∃ s, !(substsGraph L₁) s w r ∧
    ∃ e, !qqRelDef e 2 ↑(Encodable.encode (Language.Eq.eq : L₁.Rel 2)) w ∧
    ∃ i, !(iffGraph L₁) i s e ∧ ∃ j, !(impGraph L₁) j d₀ i ∧ !(impGraph L₁) y d₁ j”

variable {L₁ L₂}

instance preserveEqCode.defined :
    𝚺ᴬ₁-Function₁[V] preserveEqCode L₁ L₂ via preserveEqCodeGraph L₁ L₂ :=
  .mk fun v ↦ by simp [preserveEqCodeGraph, preserveEqCode, numeral_eq_natCast]

end graphs

/-! ## Interpretability in a model -/

section interpretable

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq]

/-- `tbl` is a table of a translation of `L₂` in `S` along which every axiom of `U` in `V`
translates to a formula provable in `S`.
- [Vis90, §5.5] -/
structure IsInterpretationTable (S : Theory L₁) [S.Δ₁] (U : Theory L₂) [U.Δ₁] (tbl : V) : Prop
    extends IsTranslationTable L₂ S tbl where
  translate_axiom {p : V} :
    p ∈ U.Δ₁Class → IsFormula L₂ p → Provable S (translate L₁ L₂ tbl p)

variable (V) in
/-- `U` is interpretable in `S` in the model `V`: some table interprets `U` in `S`.
- [Vis90, §5.5] -/
def Interpretable (S : Theory L₁) [S.Δ₁] (U : Theory L₂) [U.Δ₁] : Prop :=
  ∃ tbl : V, IsInterpretationTable S U tbl

/-- If `U` is interpretable in `S` and `S` is consistent in `V`, so is `U`. -/
theorem Interpretable.consistent {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S] {U : Theory L₂} [U.Δ₁]
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p) (hL₂ : L₂.SymbolsStandard V)
    (h : Interpretable V S U) (hcon : S.Consistent V) : U.Consistent V := by
  obtain ⟨tbl, h⟩ := h
  exact consistent_of_translate hS h.toIsTranslationTable hL₂
    (fun _ hp hf ↦ h.translate_axiom hp hf) hcon

end interpretable

section provableIff

open _root_.FFL.Entailment

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] {U : Theory L₂} [U.Δ₁]
  {tbl tbl' : V}
  {hT : IsTable L₁ L₂ tbl} {hT' : IsTable L₁ L₂ tbl'}
  (hd : ∀ u : Term V L₁, S.internalize V ⊢ hT.domT.subst ![u] 🡘 hT'.domT.subst ![u])
  (hr : ∀ {k : ℕ} (R : L₂.Rel k) (w : Fin k → Term V L₁),
    S.internalize V ⊢ (hT.relT R).subst w 🡘 (hT'.relT R).subst w)
  (hf : ∀ {k : ℕ} (F : L₂.Func k) (w : Fin (k + 1) → Term V L₁),
    S.internalize V ⊢ (hT.funcT F).subst w 🡘 (hT'.funcT F).subst w)

include hd hr hf in
/-- A table whose entries are provably equivalent in `S` to those of a table interpreting `U` in
`S` interprets `U` in `S`. -/
theorem IsInterpretationTable.of_provable_iff (h : IsInterpretationTable S U tbl)
    (hL : L₂.SymbolsStandard V) : IsInterpretationTable S U tbl' where
  toIsTranslationTable := h.toIsTranslationTable.of_provable_iff hd hr hf hL
  translate_axiom {p} hp hp' := by
    have hq := IsSemiformula.translate hT hp'
    have h₁ := (provable_iff_iff_tprovable hq (IsSemiformula.translate hT' hp')).mp
      (provable_iff_translate_of_equiv hd hr hf hL hp')
    have h₂ : S.internalize V ⊢ (⟨_, hq⟩ : Formula V L₁) :=
      tprovable_iff_provable.mpr (h.translate_axiom hp hp')
    exact tprovable_iff_provable.mp (K_left h₁ ⨀ h₂)

lemma IsInterpretationTable.of_subset {S' : Theory L₁} [S'.Δ₁] (h : IsInterpretationTable S U tbl)
    (hS : S.Δ₁Class (V := V) ⊆ S'.Δ₁Class) : IsInterpretationTable S' U tbl where
  toIsTable := h.toIsTable
  exs_domain := Derivable.of_ss hS h.exs_domain
  func_exists hf := Derivable.of_ss hS (h.func_exists hf)
  func_unique hf := Derivable.of_ss hS (h.func_unique hf)
  func_congr hf := Derivable.of_ss hS (h.func_congr hf)
  preserve_eq := Derivable.of_ss hS h.preserve_eq
  translate_axiom hp hp' := Derivable.of_ss hS (h.translate_axiom hp hp')

end provableIff

section caseSplit

variable (φ : ArithmeticSentence) {L₂ : Language} [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq]
  {tbl₁ tbl₂ : V}
  {S : ArithmeticTheory} [S.Δ₁] {U : Theory L₂} [U.Δ₁]

/-- Along a table `tbl₁` interpreting `U` in `S`, the case-split table of `tbl₁` and `tbl₂` by a
sentence `φ` provable in `S` interprets `U` in `S`. -/
lemma IsInterpretationTable.caseTable_left (h₁ : IsInterpretationTable S U tbl₁)
    (hT₂ : IsTable ℒₒᵣ L₂ tbl₂) (hφ : S.internalize V ⊢ ⌜φ⌝) (hL : L₂.SymbolsStandard V) :
    IsInterpretationTable S U (caseTable ℒₒᵣ ⌜φ⌝ tbl₁ tbl₂) := by
  have hT := h₁.toIsTable.caseTable φ hT₂
  have hd (u : Term V ℒₒᵣ) : S.internalize V ⊢ h₁.domT.subst ![u] 🡘 hT.domT.subst ![u] := by
    rw [subst_eq_of_val_eq_caseCode φ (h₁.toIsTable.caseTable_domT_val φ hT₂)]
    cl_prover [hφ]
  have hr {k : ℕ} (R : L₂.Rel k) (w : Fin k → Term V ℒₒᵣ) :
      S.internalize V ⊢ (h₁.relT R).subst w 🡘 (hT.relT R).subst w := by
    rw [subst_eq_of_val_eq_caseCode φ (h₁.toIsTable.caseTable_relT_val φ hT₂ R)]
    cl_prover [hφ]
  have hf {k : ℕ} (F : L₂.Func k) (w : Fin (k + 1) → Term V ℒₒᵣ) :
      S.internalize V ⊢ (h₁.funcT F).subst w 🡘 (hT.funcT F).subst w := by
    rw [subst_eq_of_val_eq_caseCode φ (h₁.toIsTable.caseTable_funcT_val φ hT₂ F)]
    cl_prover [hφ]
  exact h₁.of_provable_iff hd hr hf hL

/-- Along a table `tbl₂` interpreting `U` in `S`, the case-split table of `tbl₁` and `tbl₂` by a
sentence `φ` refutable in `S` interprets `U` in `S`. -/
lemma IsInterpretationTable.caseTable_right (h₂ : IsInterpretationTable S U tbl₂)
    (hT₁ : IsTable ℒₒᵣ L₂ tbl₁) (hφ : S.internalize V ⊢ ∼⌜φ⌝) (hL : L₂.SymbolsStandard V) :
    IsInterpretationTable S U (caseTable ℒₒᵣ ⌜φ⌝ tbl₁ tbl₂) := by
  have hT := hT₁.caseTable φ h₂.toIsTable
  have hd (u : Term V ℒₒᵣ) : S.internalize V ⊢ h₂.domT.subst ![u] 🡘 hT.domT.subst ![u] := by
    rw [subst_eq_of_val_eq_caseCode φ (hT₁.caseTable_domT_val φ h₂.toIsTable)]
    cl_prover [hφ]
  have hr {k : ℕ} (R : L₂.Rel k) (w : Fin k → Term V ℒₒᵣ) :
      S.internalize V ⊢ (h₂.relT R).subst w 🡘 (hT.relT R).subst w := by
    rw [subst_eq_of_val_eq_caseCode φ (hT₁.caseTable_relT_val φ h₂.toIsTable R)]
    cl_prover [hφ]
  have hf {k : ℕ} (F : L₂.Func k) (w : Fin (k + 1) → Term V ℒₒᵣ) :
      S.internalize V ⊢ (h₂.funcT F).subst w 🡘 (hT.funcT F).subst w := by
    rw [subst_eq_of_val_eq_caseCode φ (hT₁.caseTable_funcT_val φ h₂.toIsTable F)]
    cl_prover [hφ]
  exact h₂.of_provable_iff hd hr hf hL

end caseSplit

/-- Every theory of arithmetic has, in every model of $\mathsf{I}\Sigma_1$, a table of a
translation of arithmetic along which every provable formula translates to a provable formula.
- [Vis90, §5.5] -/
theorem exists_isTranslationTable_provable_translate (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (S : ArithmeticTheory) [S.Δ₁] [𝗘𝗤 ℒₒᵣ ⪯ S] :
    ∃ tbl : V, IsTranslationTable ℒₒᵣ S tbl ∧
      ∀ p : V, Provable S p → Provable S (translate ℒₒᵣ ℒₒᵣ tbl p) := by
  have h := isTableOf_arithmeticTable (V := V) (DirectTranslation.id S)
  use arithmeticTable (DirectTranslation.id S)
  and_intros
  · exact h.isTranslationTable Language.SymbolsStandard.oRing
  · intro p hp
    exact h.id_provable_translate Language.SymbolsStandard.oRing hp

open _root_.FFL.Entailment in
/-- Interpretability is transitive.
- [Vis90, §6.1] -/
theorem Interpretable.trans {S U W : ArithmeticTheory} [S.Δ₁] [U.Δ₁] [W.Δ₁] [𝗘𝗤 ℒₒᵣ ⪯ S]
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift ℒₒᵣ p = p)
    (hW : ∀ p ∈ W.Δ₁Class (V := V), Bootstrapping.shift ℒₒᵣ p = p)
    (h₁ : Interpretable V S U) (h₂ : Interpretable V U W) : Interpretable V S W := by
  obtain ⟨tbl₁, h₁⟩ := h₁
  obtain ⟨tbl₂, h₂⟩ := h₂
  have hL := Language.SymbolsStandard.oRing (V := V)
  have hsound : ∀ φ : V, Bootstrapping.shift ℒₒᵣ φ = φ → Provable U φ →
      Provable S (translate ℒₒᵣ ℒₒᵣ tbl₁ φ) := fun φ hφ hpr ↦
    provable_translate hS h₁.toIsTranslationTable hL (fun _ hp hf ↦ h₁.translate_axiom hp hf) hφ hpr
  have hc := h₁.toIsTable.compTable h₂.toIsTable
  use compTable ℒₒᵣ ℒₒᵣ tbl₁ tbl₂
  exact { toIsTranslationTable := h₁.toIsTranslationTable.compTable h₂.toIsTranslationTable hsound
          translate_axiom := fun {p} hp hp' ↦ by
            have hps := hW p hp
            have h₃ := hsound _ (by rw [← translate_shift h₂.toIsTable hp', hps])
              (h₂.translate_axiom hp hp')
            have ha := IsSemiformula.translate hc hp'
            have hb := IsSemiformula.translate h₁.toIsTable
              (IsSemiformula.translate h₂.toIsTable hp')
            have h₄ := (provable_iff_iff_tprovable ha hb).mp
              (provable_comp_translate_iff h₁.toIsTranslationTable h₂.toIsTable hc hS hL hp' hps)
            have h₅ : S.internalize V ⊢ (⟨_, hb⟩ : Formula V ℒₒᵣ) := tprovable_iff_provable.mpr h₃
            exact tprovable_iff_provable.mp (K_right h₄ ⨀ h₅) }

/-- If `W` is interpretable both in `T + φ` and in `T + ψ`, it is interpretable in
`T + (φ ∨ ψ)`.
- [Vis90, §6.1] -/
theorem Interpretable.union_or {T W : ArithmeticTheory} [T.Δ₁] [W.Δ₁] {φ ψ : ArithmeticSentence}
    (h₁ : Interpretable V (T ∪ {φ}) W) (h₂ : Interpretable V (T ∪ {ψ}) W) :
    Interpretable V (T ∪ {φ ⋎ ψ}) W := by
  obtain ⟨tbl₁, h₁⟩ := h₁
  obtain ⟨tbl₂, h₂⟩ := h₂
  have hL := Language.SymbolsStandard.oRing (V := V)
  have hφ : (T ∪ {ψ} ∪ {∼φ}).internalize V ⊢ ∼⌜φ⌝ := by
    have h₃ : (T ∪ {ψ} ∪ {∼φ}).internalize V ⊢ (⌜∼φ⌝ : Formula V ℒₒᵣ) :=
      tprovable_union_singleton _
    rwa [show (⌜∼φ⌝ : Formula V ℒₒᵣ) = ∼⌜φ⌝ by ext; simp [← Sentence.quote_eq]] at h₃
  have c₁ := h₁.caseTable_left φ h₂.toIsTable (tprovable_union_singleton φ) hL
  have c₂ := (h₂.of_subset (S' := T ∪ {ψ} ∪ {∼φ}) (by intro p hp; simp [hp])).caseTable_right φ
    h₁.toIsTable hφ hL
  use caseTable ℒₒᵣ ⌜φ⌝ tbl₁ tbl₂
  exact { toIsTable := c₁.toIsTable
          exs_domain := provable_union_or c₁.exs_domain c₂.exs_domain
          func_exists hf := provable_union_or (c₁.func_exists hf) (c₂.func_exists hf)
          func_unique hf := provable_union_or (c₁.func_unique hf) (c₂.func_unique hf)
          func_congr hf := provable_union_or (c₁.func_congr hf) (c₂.func_congr hf)
          preserve_eq := provable_union_or c₁.preserve_eq c₂.preserve_eq
          translate_axiom hp hp' :=
            provable_union_or (c₁.translate_axiom hp hp') (c₂.translate_axiom hp hp') }


/-! ## The sentence of interpretability -/

section sentence

variable (L₁ L₂ : Language) [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq]

/-- The formula defining `IsTable L₁ L₂`. -/
noncomputable def isTableDef : ArithmeticSemisentence 1 :=
  “tbl. ∃ d, !tableDomainGraph.val d tbl ∧ !(isSemiformula L₁).val 1 d ∧
    !(shiftGraph L₁).val d d ∧
    (∀ k r, !L₂.isRel.val k r → ∃ e, !tableRelGraph.val e tbl k r ∧
      !(isSemiformula L₁).val k e ∧ !(shiftGraph L₁).val e e) ∧
    (∀ k f, !L₂.isFunc.val k f → ∃ e, !tableFuncGraph.val e tbl k f ∧
      !(isSemiformula L₁).val (k + 1) e ∧ !(shiftGraph L₁).val e e)”

omit [L₂.Eq] in
variable {L₁ L₂} in
lemma eval_isTableDef (tbl : V) : V ⊧/![tbl] (isTableDef L₁ L₂) ↔ IsTable L₁ L₂ tbl := by
  simp only [isTableDef, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Semiformula.eval_ex,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp₂, Semiterm.val_bvar,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one,
    Bounding.HierarchySymbol.Defined.iff, Fin.succ_zero_eq_one, Semiterm.val_operator, Matrix.comp₀,
    Tarski.Structure.numeral_eq_numeral, ORingStructure.one_eq_one, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, Matrix.comp₄, Matrix.cons_app_four, Matrix.cons_app_three,
    Matrix.cons_app_two, Fin.succ_one_eq_two, Fin.succ_two_eq_three, LogicalConnective.Prop.and_eq,
    exists_eq_left, LogicalConnective.Prop.arrow_eq, Tarski.Structure.Add.add]
  constructor
  · rintro ⟨hd, hds, hr, hf⟩
    exact ⟨hd, hds.symm, fun h ↦ (hr _ _ h).1, fun h ↦ (hr _ _ h).2.symm, fun h ↦ (hf _ _ h).1,
      fun h ↦ (hf _ _ h).2.symm⟩
  · intro h
    exact ⟨h.domain, h.domain_shift.symm, fun _ _ hr ↦ ⟨h.rel hr, (h.rel_shift hr).symm⟩,
      fun _ _ hf ↦ ⟨h.func hf, (h.func_shift hf).symm⟩⟩

variable (S : Theory L₁) [S.Δ₁] (U : Theory L₂) [U.Δ₁]

/-- The sentence saying that `U` is interpretable in `S`.
- [Vis90, §5.5] -/
noncomputable def interpretableDef : ArithmeticSentence :=
  “∃ tbl, !(isTableDef L₁ L₂) tbl ∧
    (∃ d, !tableDomainGraph.val d tbl ∧ ∃ e, !qqExsDef.val e d ∧ !(provable S).val e) ∧
    (∃ c, !(preserveEqCodeGraph L₁ L₂).val c tbl ∧ ∃ a, !qqAllsDef.val a c 2 ∧
      !(provable S).val a) ∧
    (∀ k f, !L₂.isFunc.val k f →
      (∃ c, !(funcExistsCodeGraph L₁).val c tbl k f ∧ ∃ a, !qqAllsDef.val a c k ∧
        !(provable S).val a) ∧
      (∃ c, !(funcUniqueCodeGraph L₁).val c tbl k f ∧ ∃ a, !qqAllsDef.val a c (k + 2) ∧
        !(provable S).val a) ∧
      (∃ c, !(funcCongrCodeGraph L₁).val c tbl k f ∧ ∃ a, !qqAllsDef.val a c (k + 1 + (k + 1)) ∧
        !(provable S).val a)) ∧
    ∀ p, !U.Δ₁ch.val p → !(isSemiformula L₂).val 0 p →
      ∃ q, !(translateGraph L₁ L₂).val q tbl p ∧ !(provable S).val q”

variable {L₁ L₂ S U}

lemma isInterpretationTable_iff {tbl : V} : IsInterpretationTable S U tbl ↔
    IsTable L₁ L₂ tbl ∧ Provable S (^∃ tableDomain tbl) ∧
      Provable S (qqAlls (preserveEqCode L₁ L₂ tbl) 2) ∧
      (∀ k f : V, L₂.IsFunc k f → Provable S (qqAlls (funcExistsCode L₁ tbl k f) k) ∧
        Provable S (qqAlls (funcUniqueCode L₁ tbl k f) (k + 2)) ∧
        Provable S (qqAlls (funcCongrCode L₁ tbl k f) (k + 1 + (k + 1)))) ∧
      ∀ p ∈ U.Δ₁Class, IsFormula L₂ p → Provable S (translate L₁ L₂ tbl p) := by
  constructor
  · intro h
    exact ⟨h.toIsTable, h.exs_domain, h.preserve_eq,
      fun _ _ hf ↦ ⟨h.func_exists hf, h.func_unique hf, h.func_congr hf⟩,
      fun _ hp hf ↦ h.translate_axiom hp hf⟩
  · rintro ⟨hT, hd, he, hf, ha⟩
    exact { toIsTable := hT, exs_domain := hd, func_exists := fun h ↦ (hf _ _ h).1
            func_unique := fun h ↦ (hf _ _ h).2.1, func_congr := fun h ↦ (hf _ _ h).2.2
            preserve_eq := he, translate_axiom := fun hp hf ↦ ha _ hp hf }

lemma models_interpretableDef_iff [Nonempty V] :
    V↓[ℒₒᵣ] ⊧ interpretableDef L₁ L₂ S U ↔ Interpretable V S U := by
  simp [interpretableDef, models_iff, eval_isTableDef, Interpretable, isInterpretationTable_iff]

end sentence

end

end Bootstrapping
end FFL.FirstOrder.Arithmetic
