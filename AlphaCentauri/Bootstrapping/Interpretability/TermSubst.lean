module

public import AlphaCentauri.Bootstrapping.Interpretability.ValueLemma

/-!
# Substitution of a closed term into the defining formulas of values

Along a table of a direct translation, the defining formula of the value of a closed term `t` is
transported along a substitution of `t` for a variable; this module proves that the resulting
equivalence of the defining formulas is derivable.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section defs

variable (L₁ L₂ : Language) [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

/-- The coded set of `¬δ(&b)`, `¬E_t(&b)` and `¬δ(&i)` for `i < t`, where `δ` is the domain formula
of the table and `E_t` is the coded formula of the value of `t`. -/
noncomputable def substHyp (tbl t b : V) : V :=
  insert (neg L₁ (substs1 L₁ (^&b) tbl.[0]))
    (insert (neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t))) (negDomSet L₁ tbl.[0] t))

instance substHyp.definable : 𝚺ᴬ₁-Function₃[V] substHyp L₁ L₂ := by
  definability

/-- The code of `∀ z (δ z → (E_{s[t]}(z) ↔ E_{s[&b]}(z)))`. -/
noncomputable def termSubstEquiv (tbl t b s : V) : V :=
  ^∀ (imp L₁ tbl.[0] (iff L₁ (varEqual L₁ L₂ tbl (termSubst L₂ ?[t] s))
    (varEqual L₁ L₂ tbl (termSubst L₂ ?[^&b] s))))

instance termSubstEquiv.definable : 𝚺ᴬ₁-Function₄[V] termSubstEquiv L₁ L₂ := by
  definability

end defs

section tautology

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

lemma tprovable_all_imp_all (d φ : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ φ 🡒 ∀¹ (d 🡒 φ) :=
  TProof.all_imp_all_of_free (by simp [Semiformula.free])

end tautology

section value

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {π : DirectTranslation S L₂} {tbl : V}

omit [L₂.Eq] in
lemma isFormulaSet_substHyp (hT : IsTable L₁ L₂ tbl) {t : V} (ht : IsSemiterm L₂ 0 t) (b : V) :
    IsFormulaSet L₁ (substHyp L₁ L₂ tbl t b) := by
  have h₁ : IsSemiformula L₁ 1 (varEqual L₁ L₂ tbl t) := by
    simpa using IsSemiformula.varEqual hT ht
  exact IsFormulaSet.insert_iff.mpr ⟨(IsSemiformula.substs1 (n := 0) (by simp) hT.domain).neg,
    IsFormulaSet.insert_iff.mpr ⟨(IsSemiformula.substs1 (n := 0) (by simp) h₁).neg,
      IsFormulaSet.negDomSet hT.domain t⟩⟩

lemma derivable_definesElement_substHyp
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {t : V} (ht : IsSemiterm L₂ 0 t) (b : V) :
    Derivable S (insert (definesElement (domT π)
      (varEqualT (h.isTable hL₂) (⟨t, ht⟩ : Term V L₂))).val (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.isTable hL₂
  have hd : tbl.[0] = (domT π).val := h.domain
  have hv : (definesElement (domT π) (varEqualT hT (⟨t, ht⟩ : Term V L₂))).val =
      definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t) := by
    rw [definesElement_val, varEqualT_val, ← hd]
  have hF : IsFormulaSet L₁ (insert (definesElement (domT π)
      (varEqualT hT (⟨t, ht⟩ : Term V L₂))).val (substHyp L₁ L₂ tbl t b)) :=
    IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, isFormulaSet_substHyp hT ht b⟩
  have hsub : insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t)) (negDomSet L₁ tbl.[0] t)
      ⊆ insert (definesElement (domT π) (varEqualT hT (⟨t, ht⟩ : Term V L₂))).val
        (substHyp L₁ L₂ tbl t b) := by
    intro x hx
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · exact mem_bitInsert_iff.mpr (Or.inl hv.symm)
    · exact mem_bitInsert_iff.mpr (Or.inr (by simp [substHyp, hx]))
  exact Derivable.wk hF hsub (derivable_definesElement hS h hL₂ ht)

omit [S.Δ₁] in
lemma termSubstEquiv_eq_typed (h : IsTableOf π tbl) (hT : IsTable L₁ L₂ tbl) {t b s : V}
    {u u' : Term V L₂} (hu : u.val = termSubst L₂ ?[t] s) (hu' : u'.val = termSubst L₂ ?[^&b] s) :
    termSubstEquiv L₁ L₂ tbl t b s = (∀¹ (domT π 🡒 (varEqualT hT u 🡘 varEqualT hT u'))).val := by
  have hd : tbl.[0] = (domT π).val := h.domain
  simp only [termSubstEquiv, Semiformula.val_all, Semiformula.val_imp, Semiformula.val_iff,
    varEqualT_val, hu, hu', hd]

omit [L₂.Eq] in
lemma termSubst_func_val {k : ℕ} (F : L₂.Func k) {c v : V} (hc : IsSemiterm L₂ 0 c)
    (hv : IsSemitermVec L₂ (k : V) 1 v) :
    ∃ u : Fin k → Term V L₂, (∀ i : Fin k, (u i).val = termSubst L₂ ?[c] v.[(i : ℕ)]) ∧
      termSubst L₂ ?[c] (^func (k : V) ⌜F⌝ v) = (Semiterm.func F u).val := by
  have hw : IsSemitermVec L₂ (1 : V) 0 ?[c] := by simp [hc]
  have hi (i : Fin k) : IsSemiterm L₂ 0 (termSubst L₂ ?[c] v.[(i : ℕ)]) :=
    IsSemitermVec.termSubst hw (hv.nth (by simp))
  refine ⟨fun i ↦ ⟨termSubst L₂ ?[c] v.[(i : ℕ)], hi i⟩, fun i ↦ rfl, ?_⟩
  rw [termSubst_func (codeIn_func_quote F) hv.isUTerm, Semiterm.func_val]
  congr 1
  change termSubstVec L₂ (k : V) ?[c] v = matrixToVec fun i : Fin k ↦ termSubst L₂ ?[c] v.[(i : ℕ)]
  rw [eq_matrixToVec_iff]
  constructor
  · simp [hv.isUTerm]
  · intro i
    rw [nth_termSubstVec hv.isUTerm (by simp)]

lemma derivable_termSubstEquiv_bvar
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {t b : V} (ht : IsSemiterm L₂ 0 t) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b (^#0)) (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.isTable hL₂
  have hd : tbl.[0] = (domT π).val := h.domain
  have hH := isFormulaSet_substHyp hT ht b
  have hD := derivable_definesElement_substHyp hS h hL₂ ht b
  have hTP := definesElement_iff_equal (T := S) (domT π) (varEqualT hT (⟨t, ht⟩ : Term V L₂)) b
  have h₁ := Derivable.of_tprovable_imp hTP hD
  have hφδ : ((domT π).subst ![Semiterm.fvar b] : Formula V L₁).val = substs1 L₁ (^&b) tbl.[0] := by
    rw [Semiformula.val_subst_fvar, hd]
  have hφA : ((varEqualT hT (⟨t, ht⟩ : Term V L₂)).subst ![Semiterm.fvar b] : Formula V L₁).val =
      substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t) := by
    rw [Semiformula.val_subst_fvar, varEqualT_val]
  have hm₁ : neg L₁ (substs1 L₁ (^&b) tbl.[0]) ∈ substHyp L₁ L₂ tbl t b :=
    mem_bitInsert_iff.mpr (Or.inl rfl)
  have hm₂ : neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t)) ∈ substHyp L₁ L₂ tbl t b :=
    mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inl rfl)))
  have hδ : Derivable S (insert ((domT π).subst ![Semiterm.fvar b] : Formula V L₁).val
      (substHyp L₁ L₂ tbl t b)) :=
    Derivable.em (IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, hH⟩)
      ((domT π).subst ![Semiterm.fvar b] : Formula V L₁).val
      (mem_bitInsert_iff.mpr (Or.inl rfl))
      (mem_bitInsert_iff.mpr (Or.inr (by rw [hφδ]; exact hm₁)))
  have hE : Derivable S (insert ((varEqualT hT (⟨t, ht⟩ : Term V L₂)).subst ![Semiterm.fvar b] :
      Formula V L₁).val (substHyp L₁ L₂ tbl t b)) :=
    Derivable.em (IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, hH⟩)
      ((varEqualT hT (⟨t, ht⟩ : Term V L₂)).subst ![Semiterm.fvar b] : Formula V L₁).val
      (mem_bitInsert_iff.mpr (Or.inl rfl))
      (mem_bitInsert_iff.mpr (Or.inr (by rw [hφA]; exact hm₂)))
  have h₂ := Derivable.modusPonens_typed h₁ hδ
  have h₃ := Derivable.modusPonens_typed h₂ hE
  have hu : (⟨t, ht⟩ : Term V L₂).val = termSubst L₂ ?[t] ^#0 := by simp
  have hu' : (Semiterm.fvar b : Term V L₂).val = termSubst L₂ ?[^&b] ^#0 := by simp
  have hC : (∀¹ (domT π 🡒 (varEqualT hT (⟨t, ht⟩ : Term V L₂) 🡘
      varEqualT hT (Semiterm.fvar b)))) = ∀¹ (domT π 🡒 (varEqualT hT (⟨t, ht⟩ : Term V L₂) 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar b))) := by
    rw [varEqualT_fvar]
    rfl
  rw [termSubstEquiv_eq_typed h hT hu hu', hC]
  exact h₃

lemma derivable_termSubstEquiv_fvar (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V)
    {t b : V} (ht : IsSemiterm L₂ 0 t) (x : V) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b (^&x)) (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.isTable hL₂
  have hH := isFormulaSet_substHyp hT ht b
  have hA : S.internalize V ⊢ ∀¹ (domT π 🡒 (varEqualT hT (Semiterm.fvar x : Term V L₂) 🡘
      varEqualT hT (Semiterm.fvar x : Term V L₂))) := by
    apply TProof.all!
    simp only [Semiformula.free, Nat.succ_eq_add_one, Nat.reduceAdd, Semiformula.shift_imp,
      Semiformula.shift_iff, Semiformula.substs_imp, Semiformula.substs_imply]
    cl_prover
  have hV := termSubstEquiv_eq_typed h hT (t := t) (b := b) (s := ^&x)
    (u := (Semiterm.fvar x : Term V L₂)) (u' := (Semiterm.fvar x : Term V L₂)) (by simp) (by simp)
  rw [hV]
  exact Derivable.of_tprovable hH hA

lemma derivable_termSubstEquiv_func
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {t b : V} (ht : IsSemiterm L₂ 0 t)
    {k : ℕ} (F : L₂.Func k) {v : V} (hv : IsSemitermVec L₂ (k : V) 1 v)
    (ih : ∀ i < (k : V), Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b v.[i])
      (substHyp L₁ L₂ tbl t b))) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b (^func (k : V) ⌜F⌝ v))
      (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.isTable hL₂
  have hH := isFormulaSet_substHyp hT ht b
  obtain ⟨u, hu, hfu⟩ := termSubst_func_val F ht hv
  obtain ⟨u', hu', hfu'⟩ := termSubst_func_val F (c := ^&b) (by simp) hv
  have hΦ (i : Fin k) : Derivable S (insert (∀¹ (domT π 🡒
      (varEqualT hT (u i) 🡘 varEqualT hT (u' i)))).val (substHyp L₁ L₂ tbl t b)) := by
    rw [← termSubstEquiv_eq_typed h hT (hu i) (hu' i)]
    exact ih ((i : ℕ) : V) (by simp)
  have hc : Derivable S (insert (Matrix.conj fun i : Fin k ↦ ∀¹ (domT π 🡒
      (varEqualT hT (u i) 🡘 varEqualT hT (u' i)))).val (substHyp L₁ L₂ tbl t b)) :=
    Derivable.conj_typed hH hΦ
  have hg := Derivable.of_tprovable_imp (funcGraph_congr (domT π)
    (fun i ↦ varEqualT hT (u i)) (fun i ↦ varEqualT hT (u' i)) (funcT π F)) hc
  have hg' := Derivable.of_tprovable_imp (tprovable_all_imp_all (T := S) (domT π) _) hg
  rw [termSubstEquiv_eq_typed h hT hfu.symm hfu'.symm, varEqualT_func h hT F u,
    varEqualT_func h hT F u']
  exact hg'

theorem derivable_termSubstEquiv (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {t b s : V} (ht : IsSemiterm L₂ 0 t)
    (hs : IsSemiterm L₂ 1 s) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b s) (substHyp L₁ L₂ tbl t b)) := by
  have hP : 𝚺ᴬ₁-Predicate fun s : V ↦
      Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b s) (substHyp L₁ L₂ tbl t b)) := by
    definability
  exact IsSemiterm.sigma1_induction hP
    (fun z hz ↦ by
      obtain rfl : z = 0 := by simpa using hz
      exact derivable_termSubstEquiv_bvar hS h hL₂ ht)
    (fun x ↦ derivable_termSubstEquiv_fvar h hL₂ ht x)
    (fun k f v hf hv ih ↦ by
      obtain ⟨k', F, rfl, rfl⟩ := hL₂.2 _ _ hf
      exact derivable_termSubstEquiv_func h hL₂ ht F hv ih)
    s hs

end value

end FFL.FirstOrder.Arithmetic.Bootstrapping
