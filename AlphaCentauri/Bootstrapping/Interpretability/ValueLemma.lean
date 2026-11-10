module

public import AlphaCentauri.Bootstrapping.Interpretability.TranslationTable
public import AlphaCentauri.Bootstrapping.Proof.ExistsElimination
public import AlphaCentauri.Interpretability.Basic
public import AlphaCentauri.ToFoundation.InternalEquality
public import AlphaCentauri.ToFoundation.Provable
public import AlphaCentauri.ToFoundation.TypedProof

/-!
# Values of closed terms along the internal translation

Along a table, the internal translation of a typed term or formula of $L_2$ is the typed formula
built from the entries of the table. Along a table of a translation, the internal value of a closed
typed term is defined by a formula, these defining formulas are derivable under the negated domain
instances of the term, and the defining formula is transported along the substitution of a closed
term for a variable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

attribute [local simp] Semiformula.substs_substs

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


/-! ## Translation of typed formulas -/

section typedShapes

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] {tbl : V}

/-- The coded translation of a closed typed term, as a typed formula in one variable. -/
noncomputable def varEqualT (hT : IsTable L₁ L₂ tbl) (t : Term V L₂) : Semiformula V L₁ 1 :=
  ⟨varEqual L₁ L₂ tbl t.val, by simpa using IsSemiformula.varEqual hT t.isSemiterm⟩

@[simp] lemma varEqualT_val (hT : IsTable L₁ L₂ tbl) (t : Term V L₂) :
    (varEqualT hT t).val = varEqual L₁ L₂ tbl t.val := rfl

lemma varEqualT_fvar (hT : IsTable L₁ L₂ tbl) (x : V) :
    varEqualT hT (Semiterm.fvar x) =
      Semiformula.rel (Language.Eq.eq : L₁.Rel 2) ![Semiterm.bvar 0, Semiterm.fvar x] := by
  ext
  simp [varEqual_fvar]
  rfl

omit [L₁.Eq] in
lemma val_bvar_addCast_vec {k l : ℕ} :
    SemitermVec.val (fun i : Fin k ↦ (Semiterm.bvar (i.addCast l) : Semiterm V L₁ (l + k))) =
      bvarVec 0 (k : V) := by
  rw [bvarVec_zero_eq_matrixToVec (L := L₁) l k]
  rfl

section guard

lemma varEqualVec_typed (hT : IsTable L₁ L₂ tbl) {k : ℕ} (v : Fin k → Term V L₂) :
    varEqualVec L₁ L₂ tbl k (SemitermVec.val v) = matrixToVec fun i ↦ (varEqualT hT (v i)).val := by
  change varEqualVec L₁ L₂ tbl k (matrixToVec fun i ↦ (v i).val) = _
  have hv : IsUTermVec L₂ (k : V) (matrixToVec fun i ↦ (v i).val) :=
    (SemitermVec.isSemitermVec v).isUTerm
  rw [eq_matrixToVec_iff]
  constructor
  · exact (len_varEqualVec hv).symm
  · intro i
    rw [nth_varEqualVec (i := (i : V)) hv (by simp)]
    simp

omit [L₁.Eq] in
lemma domainAt_typed {n k : ℕ} (d : Semiformula V L₁ 1) (hd : d.val = tableDomain tbl)
    (i : Fin k) : domainAt L₁ tbl (i : V) = (d.subst ![Semiterm.bvar (i.addCast n)]).val := by
  rw [Semiformula.val_substs, hd, domainAt]
  simp

omit [L₁.Eq] in
lemma relocate_typed {n k : ℕ} (s : V) (A : Semiformula V L₁ 1) (i : Fin k) :
    relocate L₁ (i : V) s A.val = (A.subst ![Semiterm.bvar (i.addCast n)]).val := by
  rw [relocate_eq_subst (L := L₁) (n := 0) (by simp),
    Semiformula.val_substs]
  simp

omit [L₁.Eq] in
lemma guardVec_typed {n k : ℕ} (s : V) (d : Semiformula V L₁ 1) (hd : d.val = tableDomain tbl)
    (A : Fin k → Semiformula V L₁ 1) :
    guardVec L₁ tbl s (matrixToVec fun i ↦ (A i).val) k =
      matrixToVec fun i ↦ (d.subst ![Semiterm.bvar (i.addCast n)] ⋏
        (A i).subst ![Semiterm.bvar (i.addCast n)]).val := by
  rw [eq_matrixToVec_iff]
  constructor
  · simp
  · intro i
    rw [nth_guardVec _ _ _ _ _ (by simp), matrixToVec_nth, Semiformula.val_and,
      domainAt_typed d hd, relocate_typed]

end guard

section table

variable (hT : IsTable L₁ L₂ tbl)

lemma funcTail_typed {k : ℕ} (F : L₂.Func k) :
    funcTail L₁ tbl (k : V) (⌜F⌝ : V) =
      ((hT.funcT F).subst (Semiterm.bvar (Fin.cast (Nat.add_comm k 1) (Fin.last k)) :>
        fun i : Fin k ↦ Semiterm.bvar (i.addCast 1))).val := by
  have hw : SemitermVec.val (Semiterm.bvar (Fin.cast (Nat.add_comm k 1) (Fin.last k)) :>
      fun i : Fin k ↦ (Semiterm.bvar (i.addCast 1) : Semiterm V L₁ (1 + k))) =
        ^#(k : V) ∷ bvarVec 0 (k : V) := by
    rw [SemitermVec.val_cons, val_bvar_addCast_vec]
    simp
  rw [funcTail, Semiformula.val_substs, hw]
  rfl

lemma tableRel_typed {k : ℕ} (R : L₂.Rel k) :
    tableRel tbl (k : V) (⌜R⌝ : V) =
      ((hT.relT R).subst (fun i : Fin k ↦ Semiterm.bvar (i.addCast 0))).val := by
  rw [Semiformula.val_substs, val_bvar_addCast_vec]
  symm
  exact subst_eq_self (hT.relT R).isSemiformula (IsSemitermVec.bvarVec (by simp))
    (fun i hi ↦ by simp [nth_bvarVec _ _ _ hi])

lemma varEqualT_func {k : ℕ} (F : L₂.Func k) (v : Fin k → Term V L₂) :
    varEqualT hT (Semiterm.func F v) =
      funcGraph hT.domT (fun i ↦ varEqualT hT (v i)) (hT.funcT F) := by
  ext
  rw [varEqualT_val, Semiterm.func_val, varEqual_func (f := (⌜F⌝ : V)) (by simp)
    (SemitermVec.isUTermVec v), varEqualVec_typed hT v,
    guardVec_typed (A := fun i ↦ varEqualT hT (v i)) (d := hT.domT) (n := 1) (k + 1 : V) rfl,
    funcGraph, val_allItr_imp_conj, funcTail_typed hT F]

lemma translate_rel_typed {k : ℕ} (R : L₂.Rel k) (v : Fin k → Term V L₂) :
    translate L₁ L₂ tbl (Semiformula.rel R v : Formula V L₂).val =
      (relativizedImp hT.domT (fun i ↦ varEqualT hT (v i))
        ((hT.relT R).subst (fun i ↦ Semiterm.bvar (i.addCast 0)))).val := by
  rw [Semiformula.rel_val, translate_rel (by simp) (SemitermVec.isUTermVec v), translateRel,
    varEqualVec_typed hT v, guardVec_typed (A := fun i ↦ varEqualT hT (v i))
      (d := hT.domT) (n := 0) (k : V) rfl,
    tableRel_typed hT R, relativizedImp, val_allItr_imp_conj]

end table

end typedShapes

/-! ## Derivability of the defining formulas -/

section valueLemma

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

section definesCode

variable (L : Language) [L.Encodable] [L.LORDefinable] [L.Eq]

/-- The code of `definesElement`. -/
noncomputable def definesCode (d e : V) : V :=
  ^∃ (d ^⋏ ^∀ (imp L (subst L ?[^#0] d) (iff L (subst L ?[^#0] e)
    (^rel 2 (Encodable.encode (Language.Eq.eq : L.Rel 2) : V) ?[^#0, ^#1]))))

instance definesCode.definable : 𝚺ᴬ₁-Function₂[V] definesCode L := by
  definability

end definesCode

section definesElementVal

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq]

lemma definesElement_val (d A : Semiformula V L 1) :
    (definesElement d A).val = definesCode L d.val A.val := by
  simp only [definesElement, definesElementBody, definesCode, Semiformula.val_exs,
    Semiformula.val_and, Semiformula.val_all, Semiformula.val_imp, Semiformula.val_iff,
    Semiformula.val_substs]
  simp [Semiformula.equal]
  rfl

end definesElementVal

section fvar

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {T : Theory L} [T.Δ₁]

lemma tprovable_definesElement_fvar [𝗘𝗤 L ⪯ T] (d : Semiformula V L 1) (x : V) :
    T.internalize V ⊢ d.subst ![Semiterm.fvar x] 🡒
      definesElement d
        (Semiformula.rel (Language.Eq.eq : L.Rel 2) ![Semiterm.bvar 0, Semiterm.fvar x]) := by
  change T.internalize V ⊢ d.subst ![Semiterm.fvar x] 🡒
    definesElement d (Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x))
  have h₁ : T.internalize V ⊢
      ∀¹ (uniqueAt d (Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x)) x) := by
    apply TProof.all!
    simp only [uniqueAt, Semiformula.free_imp, Semiformula.free_iff]
    cl_prover
  have h₂ : T.internalize V ⊢ d.subst ![Semiterm.fvar x] 🡒
      (definesElementBody d (Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x))).subst
        ![Semiterm.fvar x] := by
    rw [definesElementBody_subst_fvar]
    cl_prover [h₁]
  have h₃ := TProof.subst_imp_exs (T := T)
    (definesElementBody d (Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x)))
    (Semiterm.fvar x)
  unfold definesElement
  cl_prover [h₂, h₃]

end fvar

section value

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {tbl : V}

omit [𝗘𝗤 L₁ ⪯ S] in
lemma definesElement_domT_val (h : IsTranslationTable L₂ S tbl) (t : Term V L₂) :
    (definesElement h.domT (varEqualT h.toIsTable t)).val =
      definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t.val) := by
  have hd : tbl.[0] = h.domT.val := rfl
  rw [definesElement_val, varEqualT_val, ← hd]

lemma derivable_definesElement_fvar (h : IsTranslationTable L₂ S tbl) (x : V) :
    Derivable S (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl ^&x))
      (negDomSet L₁ tbl.[0] ^&x)) := by
  have hT := h.toIsTable
  have hd : tbl.[0] = h.domT.val := rfl
  have hs : IsFormulaSet L₁ (negDomSet L₁ tbl.[0] ^&x) :=
    IsFormulaSet.negDomSet hT.domain _
  have hφv : (h.domT.subst ![Semiterm.fvar x] : Formula V L₁).val = substs1 L₁ ^&x tbl.[0] := by
    rw [Semiformula.val_subst_fvar, hd]
  have hm : neg L₁ (h.domT.subst ![Semiterm.fvar x] : Formula V L₁).val ∈
      negDomSet L₁ tbl.[0] ^&x := by
    rw [mem_negDomSet_iff]
    exact ⟨x, var_lt_qqFvar x, by rw [hφv]⟩
  have hF : IsFormulaSet L₁ (insert (h.domT.subst ![Semiterm.fvar x] : Formula V L₁).val
      (negDomSet L₁ tbl.[0] ^&x)) :=
    IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, hs⟩
  have hφD : Derivable S (insert (h.domT.subst ![Semiterm.fvar x] : Formula V L₁).val
      (negDomSet L₁ tbl.[0] ^&x)) :=
    Derivable.em hF ((h.domT.subst ![Semiterm.fvar x] : Formula V L₁).val)
      (mem_bitInsert_iff.mpr (Or.inl rfl)) (mem_bitInsert_iff.mpr (Or.inr hm))
  have hTP := tprovable_definesElement_fvar (T := S) h.domT x
  rw [← varEqualT_fvar hT x] at hTP
  have h₁ := Derivable.of_tprovable_imp hTP hφD
  rw [definesElement_domT_val h] at h₁
  exact h₁

omit [L₂.Eq] in
lemma exists_func_termVec (hL₂ : L₂.SymbolsStandard V) {k f v : V}
    (ht : IsSemiterm L₂ 0 (^func k f v)) :
    ∃ (k' : ℕ) (F : L₂.Func k') (u : Fin k' → Term V L₂),
      k = k' ∧ f = (⌜F⌝ : V) ∧ SemitermVec.val u = v := by
  obtain ⟨hfun, hv⟩ := IsSemiterm.func.mp ht
  obtain ⟨k', F, rfl, rfl⟩ := hL₂.2 _ _ hfun
  obtain ⟨u, hu⟩ := exists_termVec hv
  exact ⟨k', F, u, rfl, rfl, hu⟩

lemma derivable_definesElement_func (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) {k : ℕ} (F : L₂.Func k) (u : Fin k → Term V L₂)
    (ih : ∀ i, Derivable S (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (u i).val))
      (negDomSet L₁ tbl.[0] (u i).val))) :
    Derivable S (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (Semiterm.func F u).val))
      (negDomSet L₁ tbl.[0] (Semiterm.func F u).val)) := by
  have hT := h.toIsTable
  have hd : tbl.[0] = h.domT.val := rfl
  have hsF : IsFormulaSet L₁ (negDomSet L₁ tbl.[0] (Semiterm.func F u).val) :=
    IsFormulaSet.negDomSet hT.domain _
  have hlt (i : Fin k) : (u i).val < (Semiterm.func F u).val := by
    have h₁ := nth_lt_qqFunc_of_lt (i := ((i : ℕ) : V)) (k := (k : V)) (f := (⌜F⌝ : V))
      (v := SemitermVec.val u) (by simp)
    rw [Semiterm.func_val]
    simpa using h₁
  have hsU (i : Fin k) : Derivable S (insert (definesElement h.domT (varEqualT hT (u i))).val
      (negDomSet L₁ tbl.[0] (Semiterm.func F u).val)) := by
    have hv := definesElement_domT_val h (u i)
    have hF : IsFormulaSet L₁ (insert (definesElement h.domT (varEqualT hT (u i))).val
        (negDomSet L₁ tbl.[0] (Semiterm.func F u).val)) :=
      IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, hsF⟩
    have hsub : insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (u i).val))
        (negDomSet L₁ tbl.[0] (u i).val) ⊆ insert (definesElement h.domT (varEqualT hT (u i))).val
          (negDomSet L₁ tbl.[0] (Semiterm.func F u).val) := by
      intro x hx
      rcases mem_bitInsert_iff.mp hx with rfl | hx
      · exact mem_bitInsert_iff.mpr (Or.inl hv.symm)
      · exact mem_bitInsert_iff.mpr (Or.inr ((negDomSet_mono (L := L₁) (hlt i).le) hx))
    exact Derivable.wk hF hsub (ih i)
  have hY (c : Fin k → V) : S.internalize V ⊢
      Matrix.conj (fun i ↦ (definesElementBody h.domT (varEqualT hT (u i))).subst
        ![Semiterm.fvar (c i)]) 🡒
        definesElement h.domT (funcGraph h.domT (fun i ↦ varEqualT hT (u i)) (h.funcT F)) :=
    definesElement_funcGraph h.domT (h.funcT F) (h.domT_shift) (h.funcT_shift F)
      (fun i ↦ varEqualT hT (u i)) (h.tprovable_func_unique F) (h.tprovable_func_congr F)
      (h.tprovable_func_exists F) c
  have hfin := Derivable.conj_exs_elim hS (fun i ↦ definesElementBody h.domT (varEqualT hT (u i)))
    (definesElement h.domT (funcGraph h.domT (fun i ↦ varEqualT hT (u i)) (h.funcT F))) hsF
    hY hsU
  have hYeq : definesElement h.domT (funcGraph h.domT (fun i ↦ varEqualT hT (u i))
      (h.funcT F)) = definesElement h.domT (varEqualT hT (Semiterm.func F u)) := by
    rw [varEqualT_func hT F u]
  rw [hYeq, definesElement_domT_val h] at hfin
  exact hfin

lemma derivable_definesElement_func' (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {k f v : V}
    (ht : IsSemiterm L₂ 0 (^func k f v))
    (ih : ∀ i < k, Derivable S (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl v.[i]))
      (negDomSet L₁ tbl.[0] v.[i]))) :
    Derivable S (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (^func k f v)))
      (negDomSet L₁ tbl.[0] (^func k f v))) := by
  obtain ⟨k', F, u, rfl, rfl, rfl⟩ := exists_func_termVec hL₂ ht
  have ih' (i : Fin k') : Derivable S
      (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (u i).val))
        (negDomSet L₁ tbl.[0] (u i).val)) := by
    have h₁ := ih ((i : ℕ) : V) (by simp)
    simpa using h₁
  have h₂ := derivable_definesElement_func hS h F u ih'
  rw [Semiterm.func_val] at h₂
  exact h₂

theorem derivable_definesElement (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {t : V}
    (ht : IsSemiterm L₂ 0 t) :
    Derivable S
      (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t)) (negDomSet L₁ tbl.[0] t)) := by
  have hP : 𝚺ᴬ₁-Predicate fun t : V ↦
      Derivable S
        (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t)) (negDomSet L₁ tbl.[0] t)) := by
    definability
  exact IsSemiterm.sigma1_induction hP (fun z hz ↦ absurd hz (by simp))
    (fun x ↦ derivable_definesElement_fvar h x)
    (fun k f v hf hv ih ↦
      derivable_definesElement_func' hS h hL₂ (IsSemiterm.func.mpr ⟨hf, hv⟩) ih)
    t ht

end value

end valueLemma

/-! ## Substitution of a closed term -/

section termSubst

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

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

section value

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {tbl : V}

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
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {t : V}
    (ht : IsSemiterm L₂ 0 t) (b : V) :
    Derivable S (insert (definesElement h.domT
      (varEqualT h.toIsTable (⟨t, ht⟩ : Term V L₂))).val (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.toIsTable
  have hd : tbl.[0] = h.domT.val := rfl
  have hv := definesElement_domT_val h (⟨t, ht⟩ : Term V L₂)
  have hF : IsFormulaSet L₁ (insert (definesElement h.domT
      (varEqualT hT (⟨t, ht⟩ : Term V L₂))).val (substHyp L₁ L₂ tbl t b)) :=
    IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, isFormulaSet_substHyp hT ht b⟩
  have hsub : insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t)) (negDomSet L₁ tbl.[0] t)
      ⊆ insert (definesElement h.domT (varEqualT hT (⟨t, ht⟩ : Term V L₂))).val
        (substHyp L₁ L₂ tbl t b) := by
    intro x hx
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · exact mem_bitInsert_iff.mpr (Or.inl hv.symm)
    · exact mem_bitInsert_iff.mpr (Or.inr (by simp [substHyp, hx]))
  exact Derivable.wk hF hsub (derivable_definesElement hS h hL₂ ht)

omit [𝗘𝗤 L₁ ⪯ S] in
lemma termSubstEquiv_eq_typed (h : IsTranslationTable L₂ S tbl) {t b s : V}
    {u u' : Term V L₂} (hu : u.val = termSubst L₂ ?[t] s) (hu' : u'.val = termSubst L₂ ?[^&b] s) :
    termSubstEquiv L₁ L₂ tbl t b s =
      (∀¹ (h.domT 🡒 (varEqualT h.toIsTable u 🡘 varEqualT h.toIsTable u'))).val := by
  have hd : tbl.[0] = h.domT.val := rfl
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
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {t b : V}
    (ht : IsSemiterm L₂ 0 t) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b (^#0)) (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.toIsTable
  have hd : tbl.[0] = h.domT.val := rfl
  have hH := isFormulaSet_substHyp hT ht b
  have hD := derivable_definesElement_substHyp hS h hL₂ ht b
  have hTP := definesElement_iff_equal (T := S) h.domT (varEqualT hT (⟨t, ht⟩ : Term V L₂)) b
  have h₁ := Derivable.of_tprovable_imp hTP hD
  have hφδ : (h.domT.subst ![Semiterm.fvar b] : Formula V L₁).val = substs1 L₁ (^&b) tbl.[0] := by
    rw [Semiformula.val_subst_fvar, hd]
  have hφA : ((varEqualT hT (⟨t, ht⟩ : Term V L₂)).subst ![Semiterm.fvar b] : Formula V L₁).val =
      substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t) := by
    rw [Semiformula.val_subst_fvar, varEqualT_val]
  have hm₁ : neg L₁ (substs1 L₁ (^&b) tbl.[0]) ∈ substHyp L₁ L₂ tbl t b :=
    mem_bitInsert_iff.mpr (Or.inl rfl)
  have hm₂ : neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t)) ∈ substHyp L₁ L₂ tbl t b :=
    mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inl rfl)))
  have hδ : Derivable S (insert (h.domT.subst ![Semiterm.fvar b] : Formula V L₁).val
      (substHyp L₁ L₂ tbl t b)) :=
    Derivable.em (IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, hH⟩)
      (h.domT.subst ![Semiterm.fvar b] : Formula V L₁).val
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
  have hC : (∀¹ (h.domT 🡒 (varEqualT hT (⟨t, ht⟩ : Term V L₂) 🡘
      varEqualT hT (Semiterm.fvar b)))) = ∀¹ (h.domT 🡒 (varEqualT hT (⟨t, ht⟩ : Term V L₂) 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar b))) := by
    rw [varEqualT_fvar]
    rfl
  rw [termSubstEquiv_eq_typed h hu hu', hC]
  exact h₃

omit [𝗘𝗤 L₁ ⪯ S] in
lemma derivable_termSubstEquiv_fvar (h : IsTranslationTable L₂ S tbl)
    {t b : V} (ht : IsSemiterm L₂ 0 t) (x : V) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b (^&x)) (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.toIsTable
  have hH := isFormulaSet_substHyp hT ht b
  have hA : S.internalize V ⊢ ∀¹ (h.domT 🡒 (varEqualT hT (Semiterm.fvar x : Term V L₂) 🡘
      varEqualT hT (Semiterm.fvar x : Term V L₂))) := by
    apply TProof.all!
    simp only [Semiformula.free, Nat.succ_eq_add_one, Nat.reduceAdd, Semiformula.shift_imp,
      Semiformula.shift_iff, Semiformula.substs_imp, Semiformula.substs_imply]
    cl_prover
  have hV := termSubstEquiv_eq_typed h (t := t) (b := b) (s := ^&x)
    (u := (Semiterm.fvar x : Term V L₂)) (u' := (Semiterm.fvar x : Term V L₂)) (by simp) (by simp)
  rw [hV]
  exact Derivable.of_tprovable hH hA

omit [𝗘𝗤 L₁ ⪯ S] in
lemma derivable_termSubstEquiv_func
    (h : IsTranslationTable L₂ S tbl) {t b : V} (ht : IsSemiterm L₂ 0 t)
    {k : ℕ} (F : L₂.Func k) {v : V} (hv : IsSemitermVec L₂ (k : V) 1 v)
    (ih : ∀ i < (k : V), Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b v.[i])
      (substHyp L₁ L₂ tbl t b))) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b (^func (k : V) ⌜F⌝ v))
      (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.toIsTable
  have hH := isFormulaSet_substHyp hT ht b
  obtain ⟨u, hu, hfu⟩ := termSubst_func_val F ht hv
  obtain ⟨u', hu', hfu'⟩ := termSubst_func_val F (c := ^&b) (by simp) hv
  have hΦ (i : Fin k) : Derivable S (insert (∀¹ (h.domT 🡒
      (varEqualT hT (u i) 🡘 varEqualT hT (u' i)))).val (substHyp L₁ L₂ tbl t b)) := by
    rw [← termSubstEquiv_eq_typed h (hu i) (hu' i)]
    exact ih ((i : ℕ) : V) (by simp)
  have hc : Derivable S (insert (Matrix.conj fun i : Fin k ↦ ∀¹ (h.domT 🡒
      (varEqualT hT (u i) 🡘 varEqualT hT (u' i)))).val (substHyp L₁ L₂ tbl t b)) :=
    Derivable.conj_typed hH hΦ
  have hg := Derivable.of_tprovable_imp (funcGraph_congr h.domT
    (fun i ↦ varEqualT hT (u i)) (fun i ↦ varEqualT hT (u' i)) (h.funcT F)) hc
  have hg' := Derivable.of_tprovable_imp (tprovable_all_imp_all (T := S) h.domT _) hg
  rw [termSubstEquiv_eq_typed h hfu.symm hfu'.symm, varEqualT_func hT F u,
    varEqualT_func hT F u']
  exact hg'

theorem derivable_termSubstEquiv (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {t b s : V}
    (ht : IsSemiterm L₂ 0 t)
    (hs : IsSemiterm L₂ 1 s) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b s) (substHyp L₁ L₂ tbl t b)) := by
  have hP : 𝚺ᴬ₁-Predicate fun s : V ↦
      Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b s) (substHyp L₁ L₂ tbl t b)) := by
    definability
  exact IsSemiterm.sigma1_induction hP
    (fun z hz ↦ by
      obtain rfl : z = 0 := by simpa using hz
      exact derivable_termSubstEquiv_bvar hS h hL₂ ht)
    (fun x ↦ derivable_termSubstEquiv_fvar h ht x)
    (fun k f v hf hv ih ↦ by
      obtain ⟨k', F, rfl, rfl⟩ := hL₂.2 _ _ hf
      exact derivable_termSubstEquiv_func h ht F hv ih)
    s hs

end value

end termSubst

end FFL.FirstOrder.Arithmetic.Bootstrapping
