module

public import AlphaCentauri.Bootstrapping.Interpretability.Soundness

/-!
# Formalized relative interpretability

In a model `V` of $\mathsf{I}\Sigma_1$, a theory `U` of $L_2$ is interpretable in a theory `S` of
$L_1$ when there is a table of a translation of $L_2$ in `S` along which every axiom of `U` in `V`
translates to a formula provable in `S`. The sentence `interpretableDef S U` defines this in every
model of $\mathsf{I}\Sigma_1$. Consistency transfers along interpretability.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

end graphs

/-! ## Interpretability in a model -/

section interpretable

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

/-- `tbl` is a table of a translation of `L₂` in `S` along which every axiom of `U` in `V`
translates to a formula provable in `S`.
- [Vis90, §5.5] -/
structure IsInterpretationTable (S : Theory L₁) [S.Δ₁] (U : Theory L₂) [U.Δ₁] (tbl : V) : Prop
    extends IsTranslationTable L₂ S tbl where
  translate_axiom {p : V} : p ∈ U.Δ₁Class → Provable S (translate L₁ L₂ tbl p)

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
  exact consistent_of_translate hS h.toIsTranslationTable hL₂ (fun _ hp ↦ h.translate_axiom hp)
    hcon

end interpretable

/-! ## The sentence of interpretability -/

section sentence

variable (L₁ L₂ : Language) [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

/-- The formula defining `IsTable L₁ L₂`. -/
noncomputable def isTableDef : ArithmeticSemisentence 1 :=
  “tbl. ∃ d, !tableDomainGraph.val d tbl ∧ !(isSemiformula L₁).val 1 d ∧
    !(shiftGraph L₁).val d d ∧
    (∀ k r, !L₂.isRel.val k r → ∃ e, !tableRelGraph.val e tbl k r ∧
      !(isSemiformula L₁).val k e ∧ !(shiftGraph L₁).val e e) ∧
    (∀ k f, !L₂.isFunc.val k f → ∃ e, !tableFuncGraph.val e tbl k f ∧
      !(isSemiformula L₁).val (k + 1) e ∧ !(shiftGraph L₁).val e e)”

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
    (∀ k f, !L₂.isFunc.val k f →
      (∃ c, !(funcExistsCodeGraph L₁).val c tbl k f ∧ ∃ a, !qqAllsDef.val a c k ∧
        !(provable S).val a) ∧
      (∃ c, !(funcUniqueCodeGraph L₁).val c tbl k f ∧ ∃ a, !qqAllsDef.val a c (k + 2) ∧
        !(provable S).val a) ∧
      (∃ c, !(funcCongrCodeGraph L₁).val c tbl k f ∧ ∃ a, !qqAllsDef.val a c (k + 1 + (k + 1)) ∧
        !(provable S).val a)) ∧
    ∀ p, !U.Δ₁ch.val p → ∃ q, !(translateGraph L₁ L₂).val q tbl p ∧ !(provable S).val q”

variable {L₁ L₂ S U}

lemma isInterpretationTable_iff {tbl : V} : IsInterpretationTable S U tbl ↔
    IsTable L₁ L₂ tbl ∧ Provable S (^∃ tableDomain tbl) ∧
      (∀ k f : V, L₂.IsFunc k f → Provable S (qqAlls (funcExistsCode L₁ tbl k f) k) ∧
        Provable S (qqAlls (funcUniqueCode L₁ tbl k f) (k + 2)) ∧
        Provable S (qqAlls (funcCongrCode L₁ tbl k f) (k + 1 + (k + 1)))) ∧
      ∀ p ∈ U.Δ₁Class, Provable S (translate L₁ L₂ tbl p) := by
  constructor
  · intro h
    exact ⟨h.toIsTable, h.exs_domain,
      fun _ _ hf ↦ ⟨h.func_exists hf, h.func_unique hf, h.func_congr hf⟩,
      fun _ hp ↦ h.translate_axiom hp⟩
  · rintro ⟨hT, hd, hf, ha⟩
    exact { toIsTable := hT, exs_domain := hd, func_exists := fun h ↦ (hf _ _ h).1
            func_unique := fun h ↦ (hf _ _ h).2.1, func_congr := fun h ↦ (hf _ _ h).2.2
            translate_axiom := fun hp ↦ ha _ hp }

lemma models_interpretableDef_iff [Nonempty V] :
    V↓[ℒₒᵣ] ⊧ interpretableDef L₁ L₂ S U ↔ Interpretable V S U := by
  simp [interpretableDef, models_iff, eval_isTableDef, Interpretable, isInterpretationTable_iff]

end sentence

end FFL.FirstOrder.Arithmetic.Bootstrapping
