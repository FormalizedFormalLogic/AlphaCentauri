module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.Bootstrapping.Interpretability.PiFacts
public import AlphaCentauri.Bootstrapping.Interpretability.TypedShapes
public import AlphaCentauri.Bootstrapping.Proof.ExistsElimination
public import AlphaCentauri.Bootstrapping.Proof.NegDomSet
public import AlphaCentauri.ToFoundation.DefinesElement
public import AlphaCentauri.ToFoundation.TypedBridge

/-!
# Derivability of the defining formulas of values of typed terms

Along a table of a direct translation, the internal value of a closed typed term is defined by a
formula; this module proves that these defining formulas are derivable, under the negated domain
instances of the term.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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
  simp only [definesElement, definesCode, Semiformula.val_exs, Semiformula.val_and,
    Semiformula.val_all, Semiformula.val_imp, Semiformula.val_iff, Semiformula.val_substs]
  simp [Semiformula.equal]
  rfl

end definesElementVal

section fvar

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {T : Theory L} [T.Δ₁]

lemma tprovable_definesElement_fvar [𝗘𝗤 L ⪯ T] (d : Semiformula V L 1) (x : V) :
    T.internalize V ⊢ d.subst ![Semiterm.fvar x] 🡒
      definesElement d
        (Semiformula.rel (Language.Eq.eq : L.Rel 2) ![Semiterm.bvar 0, Semiterm.fvar x]) := by
  have h₁ : T.internalize V ⊢ ∀¹ (d.subst ![Semiterm.bvar 0] 🡒
      ((Semiformula.rel (Language.Eq.eq : L.Rel 2) ![Semiterm.bvar 0, Semiterm.fvar x]).subst
          ![Semiterm.bvar 0] 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x))) := by
    apply TProof.all!
    simp only [Semiformula.free, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue,
      Semiformula.subst_eq_self₁, Semiformula.substs_rel, Matrix.vecMap_cons', Matrix.head_cons,
      Semiterm.substs_bvar, Matrix.cons_val_fin_one, Matrix.tail_cons, Semiterm.substs_fvar,
      Matrix.vecMap_nil, Semiformula.equal, Semiformula.shift_imp, Semiformula.shift_iff,
      Semiformula.shift_rel, Semiterm.shift_bvar, Semiterm.shift_fvar, Semiformula.substs_imp,
      Semiformula.substs_imply]
    cl_prover
  have h₂ : T.internalize V ⊢ d.subst ![Semiterm.fvar x] 🡒
      (definesElementBody d
        (Semiformula.rel (Language.Eq.eq : L.Rel 2) ![Semiterm.bvar 0, Semiterm.fvar x])).subst
          ![Semiterm.fvar x] := by
    rw [definesElementBody_subst_fvar]
    cl_prover [h₁]
  have h₃ := TProof.subst_imp_exs (T := T) (definesElementBody d
    (Semiformula.rel (Language.Eq.eq : L.Rel 2) ![Semiterm.bvar 0, Semiterm.fvar x]))
    (Semiterm.fvar x)
  rw [definesElement_eq]
  cl_prover [h₂, h₃]

end fvar

section value

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {π : DirectTranslation S L₂} {tbl : V}

lemma derivable_definesElement_fvar (hT : IsTable L₁ L₂ tbl) (h : IsTableOf π tbl) (x : V) :
    Derivable S (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl ^&x))
      (negDomSet L₁ tbl.[0] ^&x)) := by
  have hd : tbl.[0] = (domT π).val := h.domain
  have hs : IsFormulaSet L₁ (negDomSet L₁ tbl.[0] ^&x) :=
    IsFormulaSet.negDomSet hT.domain _
  have hφv : ((domT π).subst ![Semiterm.fvar x] : Formula V L₁).val = substs1 L₁ ^&x tbl.[0] := by
    rw [Semiformula.val_subst_fvar, hd]
  have hm : neg L₁ ((domT π).subst ![Semiterm.fvar x] : Formula V L₁).val ∈
      negDomSet L₁ tbl.[0] ^&x := by
    rw [mem_negDomSet_iff]
    exact ⟨x, var_lt_qqFvar x, by rw [hφv]⟩
  have hF : IsFormulaSet L₁ (insert ((domT π).subst ![Semiterm.fvar x] : Formula V L₁).val
      (negDomSet L₁ tbl.[0] ^&x)) :=
    IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, hs⟩
  have hφD : Derivable S (insert ((domT π).subst ![Semiterm.fvar x] : Formula V L₁).val
      (negDomSet L₁ tbl.[0] ^&x)) :=
    Derivable.em hF (((domT π).subst ![Semiterm.fvar x] : Formula V L₁).val)
      (mem_bitInsert_iff.mpr (Or.inl rfl)) (mem_bitInsert_iff.mpr (Or.inr hm))
  have hTP := tprovable_definesElement_fvar (T := S) (domT π) x
  rw [← varEqualT_fvar hT x] at hTP
  have h₁ := Derivable.of_tprovable_imp hTP hφD
  have hv : (definesElement (domT π) (varEqualT hT (Semiterm.fvar x))).val =
      definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl ^&x) := by
    rw [definesElement_val, varEqualT_val, ← hd]
    simp
  rw [hv] at h₁
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
    (h : IsTableOf π tbl) (hT : IsTable L₁ L₂ tbl) {k : ℕ} (F : L₂.Func k) (u : Fin k → Term V L₂)
    (ih : ∀ i, Derivable S (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (u i).val))
      (negDomSet L₁ tbl.[0] (u i).val))) :
    Derivable S (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (Semiterm.func F u).val))
      (negDomSet L₁ tbl.[0] (Semiterm.func F u).val)) := by
  have hd : tbl.[0] = (domT π).val := h.domain
  have hsF : IsFormulaSet L₁ (negDomSet L₁ tbl.[0] (Semiterm.func F u).val) :=
    IsFormulaSet.negDomSet hT.domain _
  have hlt (i : Fin k) : (u i).val < (Semiterm.func F u).val := by
    have h₁ := nth_lt_qqFunc_of_lt (i := ((i : ℕ) : V)) (k := (k : V)) (f := (⌜F⌝ : V))
      (v := SemitermVec.val u) (by simp)
    rw [Semiterm.func_val]
    simpa using h₁
  have hsU (i : Fin k) : Derivable S (insert (definesElement (domT π) (varEqualT hT (u i))).val
      (negDomSet L₁ tbl.[0] (Semiterm.func F u).val)) := by
    have hv : (definesElement (domT π) (varEqualT hT (u i))).val =
        definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (u i).val) := by
      rw [definesElement_val, varEqualT_val, ← hd]
    have hF : IsFormulaSet L₁ (insert (definesElement (domT π) (varEqualT hT (u i))).val
        (negDomSet L₁ tbl.[0] (Semiterm.func F u).val)) :=
      IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, hsF⟩
    have hsub : insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (u i).val))
        (negDomSet L₁ tbl.[0] (u i).val) ⊆ insert (definesElement (domT π) (varEqualT hT (u i))).val
          (negDomSet L₁ tbl.[0] (Semiterm.func F u).val) := by
      intro x hx
      rcases mem_bitInsert_iff.mp hx with rfl | hx
      · exact mem_bitInsert_iff.mpr (Or.inl hv.symm)
      · exact mem_bitInsert_iff.mpr (Or.inr ((negDomSet_mono (L := L₁) (hlt i).le) hx))
    exact Derivable.wk hF hsub (ih i)
  have hY (c : Fin k → V) : S.internalize V ⊢
      Matrix.conj (fun i ↦ (definesElementBody (domT π) (varEqualT hT (u i))).subst
        ![Semiterm.fvar (c i)]) 🡒
        definesElement (domT π) (funcGraph (domT π) (fun i ↦ varEqualT hT (u i)) (funcT π F)) :=
    definesElement_funcGraph (domT π) (funcT π F) (fun i ↦ varEqualT hT (u i)) (domT_shift π)
      (funcT_shift π F) (tprovable_func_exists π F) (tprovable_func_unique π F)
      (tprovable_func_congr π F) c
  have hfin := Derivable.conj_exs_elim hS (fun i ↦ definesElementBody (domT π) (varEqualT hT (u i)))
    (definesElement (domT π) (funcGraph (domT π) (fun i ↦ varEqualT hT (u i)) (funcT π F))) hsF
    hY hsU
  have hYeq : definesElement (domT π) (funcGraph (domT π) (fun i ↦ varEqualT hT (u i))
      (funcT π F)) = definesElement (domT π) (varEqualT hT (Semiterm.func F u)) := by
    rw [varEqualT_func h hT F u]
  have hv : (definesElement (domT π) (varEqualT hT (Semiterm.func F u))).val =
      definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (Semiterm.func F u).val) := by
    rw [definesElement_val, varEqualT_val, ← hd]
  rw [hYeq, hv] at hfin
  exact hfin

lemma derivable_definesElement_func' (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hT : IsTable L₁ L₂ tbl) (hL₂ : L₂.SymbolsStandard V) {k f v : V}
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
  have h₂ := derivable_definesElement_func hS h hT F u ih'
  rw [Semiterm.func_val] at h₂
  exact h₂

theorem derivable_definesElement (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {t : V} (ht : IsSemiterm L₂ 0 t) :
    Derivable S
      (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t)) (negDomSet L₁ tbl.[0] t)) := by
  have hT := h.isTable hL₂
  have hP : 𝚺ᴬ₁-Predicate fun t : V ↦
      Derivable S
        (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t)) (negDomSet L₁ tbl.[0] t)) := by
    definability
  exact IsSemiterm.sigma1_induction hP (fun z hz ↦ absurd hz (by simp))
    (fun x ↦ derivable_definesElement_fvar hT h x)
    (fun k f v hf hv ih ↦
      derivable_definesElement_func' hS h hT hL₂ (IsSemiterm.func.mpr ⟨hf, hv⟩) ih)
    t ht

end value

end FFL.FirstOrder.Arithmetic.Bootstrapping
