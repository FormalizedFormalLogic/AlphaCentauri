module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.ToFoundation.DefinesElement

/-!
# The internal translation of typed formulas

Along a table of a direct translation `π`, the internal translation of a typed term or formula of
$L_2$ is the typed formula prescribed by `π`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] {tbl : V}

section typedVal

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma val_allItr {n k : ℕ} (φ : Semiformula V L (n + k)) :
    (∀¹^[k] φ).val = qqAlls φ.val k := by
  induction k with
  | zero => simp
  | succ k ih => simpa [allItr_succ, qqAlls_all] using ih (∀¹ φ)

lemma val_conj_typed {n m : ℕ} (v : Fin m → Semiformula V L n) :
    (Matrix.conj v).val = ^⋀ matrixToVec fun i ↦ (v i).val := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Matrix.conj, ih, matrixToVec_succ, qqConj_cons, Semiformula.val_and]
    rfl

lemma val_allItr_imp_conj {n k : ℕ} (d : Semiformula V L 1) (A : Fin k → Semiformula V L 1)
    (C : Semiformula V L (n + k)) :
    (∀¹^[k] (Matrix.conj (fun i : Fin k ↦
        d.subst ![Semiterm.bvar (i.addCast n)] ⋏ (A i).subst ![Semiterm.bvar (i.addCast n)])
          🡒 C)).val =
      qqAlls (imp L (^⋀ matrixToVec fun i ↦
        (d.subst ![Semiterm.bvar (i.addCast n)] ⋏ (A i).subst ![Semiterm.bvar (i.addCast n)]).val)
          C.val) k := by
  rw [val_allItr, Semiformula.val_imp, val_conj_typed]

end typedVal

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
  change matrixToVec (fun i : Fin k ↦
    (Semiterm.bvar (i.addCast l) : Semiterm V L₁ (l + k)).val) = _
  symm
  rw [eq_matrixToVec_iff]
  constructor
  · simp
  · intro i
    have hi : ((i : ℕ) : V) < (k : V) := by simp
    simp [nth_bvarVec _ _ _ hi]

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

section direct

variable {S : Theory L₁} [𝗘𝗤 _ ⪯ S] [L₂.Eq] {π : DirectTranslation S L₂}

omit [L₂.LORDefinable] in
lemma funcTail_typed (h : IsTableOf π tbl) {k : ℕ} (F : L₂.Func k) :
    funcTail L₁ tbl (k : V) (⌜F⌝ : V) =
      ((⌜(π.func F).sentence⌝ : Semiformula V L₁ (k + 1)).subst
        (Semiterm.bvar (Fin.cast (Nat.add_comm k 1) (Fin.last k)) :>
          fun i : Fin k ↦ Semiterm.bvar (i.addCast 1))).val := by
  have hw : SemitermVec.val (Semiterm.bvar (Fin.cast (Nat.add_comm k 1) (Fin.last k)) :>
      fun i : Fin k ↦ (Semiterm.bvar (i.addCast 1) : Semiterm V L₁ (1 + k))) =
        ^#(k : V) ∷ bvarVec 0 (k : V) := by
    rw [SemitermVec.val_cons, val_bvar_addCast_vec]
    simp
  rw [funcTail, Semiformula.val_substs, hw, h.func F]
  rfl

omit [L₂.LORDefinable] in
lemma tableRel_typed (h : IsTableOf π tbl) {k : ℕ} (R : L₂.Rel k) :
    tableRel tbl (k : V) (⌜R⌝ : V) =
      ((⌜(π.rel R).sentence⌝ : Semiformula V L₁ k).subst
        (fun i : Fin k ↦ Semiterm.bvar (i.addCast 0))).val := by
  rw [h.rel R, Semiformula.val_substs, val_bvar_addCast_vec]
  symm
  exact subst_eq_self (Sentence.quote_isSemiformula _) (IsSemitermVec.bvarVec (by simp))
    (fun i hi ↦ by simp [nth_bvarVec _ _ _ hi])

lemma varEqualT_func (h : IsTableOf π tbl) (hT : IsTable L₁ L₂ tbl) {k : ℕ} (F : L₂.Func k)
    (v : Fin k → Term V L₂) :
    varEqualT hT (Semiterm.func F v) =
      funcGraph (⌜π.domain.sentence⌝ : Semiformula V L₁ 1) (fun i ↦ varEqualT hT (v i))
        (⌜(π.func F).sentence⌝ : Semiformula V L₁ (k + 1)) := by
  ext
  rw [varEqualT_val, Semiterm.func_val, varEqual_func (f := (⌜F⌝ : V)) (by simp)
    (SemitermVec.isUTermVec v), varEqualVec_typed hT v,
    guardVec_typed (A := fun i ↦ varEqualT hT (v i))
      (d := (⌜π.domain.sentence⌝ : Semiformula V L₁ 1)) (n := 1) (k + 1 : V) h.domain.symm,
    funcGraph, val_allItr_imp_conj, funcTail_typed h F]

lemma translate_rel_typed (h : IsTableOf π tbl) (hT : IsTable L₁ L₂ tbl) {k : ℕ} (R : L₂.Rel k)
    (v : Fin k → Term V L₂) :
    translate L₁ L₂ tbl (Semiformula.rel R v : Formula V L₂).val =
      (relativizedImp (⌜π.domain.sentence⌝ : Semiformula V L₁ 1) (fun i ↦ varEqualT hT (v i))
        ((⌜(π.rel R).sentence⌝ : Semiformula V L₁ k).subst
          (fun i ↦ Semiterm.bvar (i.addCast 0)))).val := by
  rw [Semiformula.rel_val, translate_rel (by simp) (SemitermVec.isUTermVec v), translateRel,
    varEqualVec_typed hT v, guardVec_typed (A := fun i ↦ varEqualT hT (v i))
      (d := (⌜π.domain.sentence⌝ : Semiformula V L₁ 1)) (n := 0) (k : V) h.domain.symm,
    tableRel_typed h R, relativizedImp, val_allItr_imp_conj]

omit [L₂.Eq] in
lemma translate_nrel_typed {k : ℕ} (R : L₂.Rel k) (v : Fin k → Term V L₂) :
    translate L₁ L₂ tbl (Semiformula.nrel R v : Formula V L₂).val =
      neg L₁ (translate L₁ L₂ tbl (Semiformula.rel R v : Formula V L₂).val) := by
  rw [Semiformula.nrel_val, Semiformula.rel_val,
    translate_nrel (by simp) (SemitermVec.isUTermVec v),
    translate_rel (by simp) (SemitermVec.isUTermVec v)]

end direct

section symbols

lemma exists_termVec {k : ℕ} {v : V} (hv : IsSemitermVec L₂ (k : V) 0 v) :
    ∃ u : Fin k → Term V L₂, SemitermVec.val u = v := by
  have hu : ∀ i : Fin k, IsSemiterm L₂ 0 v.[((i : ℕ) : V)] := fun i ↦ hv.nth (by simp)
  exact ⟨fun i ↦ ⟨v.[((i : ℕ) : V)], hu i⟩, by
    change matrixToVec (fun i : Fin k ↦ v.[((i : ℕ) : V)]) = v
    symm
    rw [eq_matrixToVec_iff]
    exact ⟨hv.lh.symm, fun i ↦ rfl⟩⟩

lemma exists_func_typed (hL₂ : L₂.SymbolsStandard V) {t : V} (ht : IsSemiterm L₂ 0 t)
    {k f v : V} (hf : t = ^func k f v) :
    ∃ (k' : ℕ) (F : L₂.Func k') (u : Fin k' → Term V L₂),
      k = k' ∧ f = (⌜F⌝ : V) ∧ t = (Semiterm.func F u).val := by
  subst hf
  obtain ⟨hfun, hv⟩ := IsSemiterm.func.mp ht
  obtain ⟨k', F, rfl, rfl⟩ := hL₂.2 _ _ hfun
  obtain ⟨u, hu⟩ := exists_termVec hv
  exact ⟨k', F, u, rfl, rfl, by rw [Semiterm.func_val, hu]⟩

lemma exists_rel_typed (hL₂ : L₂.SymbolsStandard V) {p k R v : V} (hp : IsSemiformula L₂ 0 p)
    (hrel : p = ^rel k R v) :
    ∃ (k' : ℕ) (R' : L₂.Rel k') (u : Fin k' → Term V L₂),
      k = k' ∧ R = (⌜R'⌝ : V) ∧ p = (Semiformula.rel R' u : Formula V L₂).val := by
  subst hrel
  obtain ⟨hR, hv⟩ := IsSemiformula.rel.mp hp
  obtain ⟨k', R', rfl, rfl⟩ := hL₂.1 _ _ hR
  obtain ⟨u, hu⟩ := exists_termVec hv
  exact ⟨k', R', u, rfl, rfl, by rw [Semiformula.rel_val, hu]⟩

lemma exists_nrel_typed (hL₂ : L₂.SymbolsStandard V) {p k R v : V} (hp : IsSemiformula L₂ 0 p)
    (hnrel : p = ^nrel k R v) :
    ∃ (k' : ℕ) (R' : L₂.Rel k') (u : Fin k' → Term V L₂),
      k = k' ∧ R = (⌜R'⌝ : V) ∧ p = (Semiformula.nrel R' u : Formula V L₂).val := by
  subst hnrel
  obtain ⟨hR, hv⟩ := IsSemiformula.nrel.mp hp
  obtain ⟨k', R', rfl, rfl⟩ := hL₂.1 _ _ hR
  obtain ⟨u, hu⟩ := exists_termVec hv
  exact ⟨k', R', u, rfl, rfl, by rw [Semiformula.nrel_val, hu]⟩

end symbols

end FFL.FirstOrder.Arithmetic.Bootstrapping
