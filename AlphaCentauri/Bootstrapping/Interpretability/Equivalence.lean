module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.Bootstrapping.Interpretability.Soundness
public import AlphaCentauri.Bootstrapping.Interpretability.Value

/-!
# Translations along equivalent tables and along the identity

If the domain formulas, the formulas of the relation symbols and the graphs of the function symbols
of two tables are provably equivalent in `S`, every formula code has provably equivalent
translations along the two tables. Along a table of the identity translation
`DirectTranslation.id S`, the coded formula of the value of a closed term `t` is provably
equivalent to `^#0 = t`, every formula code is provably equivalent to its translation, and so the
translation of every formula code provable in `S` is provable in `S`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding



open _root_.FFL.Entailment

section congruence

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] {S : Theory L₁} [S.Δ₁] {tbl tbl' : V}
  {hT : IsTable L₁ L₂ tbl} {hT' : IsTable L₁ L₂ tbl'}
  (hd : ∀ u : Term V L₁, S.internalize V ⊢ hT.domT.subst ![u] 🡘 hT'.domT.subst ![u])
  (hr : ∀ {k : ℕ} (R : L₂.Rel k) (w : Fin k → Term V L₁),
    S.internalize V ⊢ (hT.relT R).subst w 🡘 (hT'.relT R).subst w)
  (hf : ∀ {k : ℕ} (F : L₂.Func k) (w : Fin (k + 1) → Term V L₁),
    S.internalize V ⊢ (hT.funcT F).subst w 🡘 (hT'.funcT F).subst w)

include hd in
lemma tprovable_all_domT_iff : S.internalize V ⊢ ∀¹ (hT.domT 🡘 hT'.domT) := by
  apply TProof.all!
  rw [Semiformula.free_iff, Semiformula.free, Semiformula.free, hT.domT_shift, hT'.domT_shift]
  exact hd _

include hd in
lemma tprovable_all_and_imp_and {A B : Semiformula V L₁ 1}
    (h : S.internalize V ⊢ ∀¹ (A 🡘 B)) :
    S.internalize V ⊢ ∀¹ (hT'.domT ⋏ B 🡒 hT.domT ⋏ A) := by
  have h₁ : S.internalize V ⊢ ∀¹ ((hT.domT 🡘 hT'.domT) 🡒 (A 🡘 B) 🡒
      (hT'.domT ⋏ B 🡒 hT.domT ⋏ A)) := by
    apply TProof.all!
    simp only [Semiformula.free_imp, Semiformula.free_iff, Semiformula.free_and]
    cl_prover
  exact tprovable_all_of_all_imp_imp h₁ (tprovable_all_domT_iff hd) h

include hd hf in
lemma tprovable_funcGraph_iff {k : ℕ} (F : L₂.Func k) (A B : Fin k → Semiformula V L₁ 1)
    (h : ∀ i, S.internalize V ⊢ ∀¹ (A i 🡘 B i)) :
    S.internalize V ⊢ ∀¹ (funcGraph hT.domT A (hT.funcT F) 🡘
      funcGraph hT'.domT B (hT'.funcT F)) := by
  have e (γ : Semiformula V L₁ (k + 1)) (hγ : γ.shift = γ) :
      (Semiformula.shift^[k] (γ.subst ((Semiterm.fvar 0 : Semiterm V L₁ (0 + k)) :>
        fun i : Fin k ↦ Semiterm.bvar (i.addCast 0)))).subst
          (fun i : Fin (0 + k) ↦ (Semiterm.fvar (i : V) : Term V L₁)) =
      γ.subst fun j ↦ (Semiterm.shift^[k] (((Semiterm.fvar 0 : Semiterm V L₁ (0 + k)) :>
        fun i : Fin k ↦ Semiterm.bvar (i.addCast 0)) j)).subst
          fun i : Fin (0 + k) ↦ (Semiterm.fvar (i : V) : Term V L₁) := by
    rw [Semiformula.shift_iterate_subst, Function.iterate_fixed hγ, Semiformula.substs_substs]
    rfl
  have hs (i : Fin k) : S.internalize V ⊢ ∀¹ ((A i).shift 🡘 (B i).shift) := by
    simpa only [Semiformula.shift_all, Semiformula.shift_iff] using TProof.shift! (h i)
  have hd' (u : Term V L₁) : S.internalize V ⊢ hT'.domT.subst ![u] 🡘 hT.domT.subst ![u] := by
    have := hd u
    cl_prover [this]
  let w : Fin (k + 1) → Semiterm V L₁ (0 + k) :=
    Semiterm.fvar 0 :> fun i : Fin k ↦ Semiterm.bvar (i.addCast 0)
  have h₁ := relativizedImp_imp_relativizedImp_of_imp hT.domT hT'.domT
    (fun i ↦ (A i).shift) (fun i ↦ (B i).shift) ((hT.funcT F).subst w) ((hT'.funcT F).subst w)
    (fun i ↦ tprovable_all_and_imp_and hd (hs i)) (by
      rw [e _ (hT.funcT_shift F), e _ (hT'.funcT_shift F)]
      exact K_left (hf F _))
  have h₂ := relativizedImp_imp_relativizedImp_of_imp hT'.domT hT.domT
    (fun i ↦ (B i).shift) (fun i ↦ (A i).shift) ((hT'.funcT F).subst w) ((hT.funcT F).subst w)
    (fun i ↦ tprovable_all_and_imp_and hd' (by
      have h₃ : S.internalize V ⊢ ∀¹ (((A i).shift 🡘 (B i).shift) 🡒
          ((B i).shift 🡘 (A i).shift)) := by
        apply TProof.all!
        simp only [Semiformula.free_imp, Semiformula.free_iff]
        cl_prover
      exact tprovable_all_imp_imp_all _ _ ⨀ h₃ ⨀ hs i)) (by
      rw [e _ (hT.funcT_shift F), e _ (hT'.funcT_shift F)]
      exact K_right (hf F _))
  apply TProof.all!
  rw [Semiformula.free_iff, Semiformula.free, Semiformula.free, shift_funcGraph, shift_funcGraph,
    funcGraph_subst_fvar, funcGraph_subst_fvar, hT.domT_shift, hT'.domT_shift, hT.funcT_shift,
    hT'.funcT_shift]
  cl_prover [h₁, h₂]

include hd hf in
lemma tprovable_varEqualT_iff (hL : L₂.SymbolsStandard V) (t : Term V L₂) :
    S.internalize V ⊢ ∀¹ (varEqualT hT t 🡘 varEqualT hT' t) := by
  have hE (t : Term V L₂) : (∀¹ (varEqualT hT t 🡘 varEqualT hT' t)).val =
      ^∀ iff L₁ (varEqual L₁ L₂ tbl t.val) (varEqual L₁ L₂ tbl' t.val) := by
    simp only [Semiformula.val_all, Semiformula.val_iff, varEqualT_val]
  have hP : 𝚺ᴬ₁-Predicate fun t : V ↦
      Provable S (^∀ iff L₁ (varEqual L₁ L₂ tbl t) (varEqual L₁ L₂ tbl' t)) := by
    definability
  have key := IsSemiterm.sigma1_induction hP (n := 0) (fun z hz ↦ by simp at hz) ?_ ?_ t.val
    t.isSemiterm
  · rw [tprovable_iff_provable, hE]
    exact key
  · intro x
    have h₁ : S.internalize V ⊢ ∀¹ (varEqualT hT (Semiterm.fvar x) 🡘
        varEqualT hT' (Semiterm.fvar x)) := by
      rw [varEqualT_fvar, varEqualT_fvar]
      apply TProof.all!
      rw [Semiformula.free_iff]
      cl_prover
    rw [tprovable_iff_provable, hE] at h₁
    exact h₁
  · intro k f v hf' hv ih
    obtain ⟨k, F, u, rfl, rfl, rfl⟩ := exists_func_termVec hL (IsSemiterm.func.mpr ⟨hf', hv⟩)
    have ih' (i : Fin k) : S.internalize V ⊢ ∀¹ (varEqualT hT (u i) 🡘 varEqualT hT' (u i)) := by
      rw [tprovable_iff_provable, hE]
      simpa using ih ((i : ℕ) : V) (by simp)
    have h₁ := tprovable_funcGraph_iff hd hf F _ _ ih'
    rw [← varEqualT_func, ← varEqualT_func, tprovable_iff_provable, hE, Semiterm.func_val] at h₁
    exact h₁

include hd hr hf in
lemma tprovable_translate_rel_iff (hL : L₂.SymbolsStandard V) {k : ℕ} (R : L₂.Rel k)
    (u : Fin k → Term V L₂) :
    S.internalize V ⊢ relativizedImp hT.domT (fun i ↦ varEqualT hT (u i))
        ((hT.relT R).subst fun i ↦ Semiterm.bvar (i.addCast 0)) 🡘
      relativizedImp hT'.domT (fun i ↦ varEqualT hT' (u i))
        ((hT'.relT R).subst fun i ↦ Semiterm.bvar (i.addCast 0)) := by
  have e (γ : Semiformula V L₁ k) (hγ : γ.shift = γ) :
      (Semiformula.shift^[k] (γ.subst fun i : Fin k ↦
        (Semiterm.bvar (i.addCast 0) : Semiterm V L₁ (0 + k)))).subst
          (fun i : Fin (0 + k) ↦ (Semiterm.fvar (i : V) : Term V L₁)) =
      γ.subst fun j ↦ (Semiterm.shift^[k] (Semiterm.bvar (j.addCast 0) :
        Semiterm V L₁ (0 + k))).subst
          fun i : Fin (0 + k) ↦ (Semiterm.fvar (i : V) : Term V L₁) := by
    rw [Semiformula.shift_iterate_subst, Function.iterate_fixed hγ, Semiformula.substs_substs]
    rfl
  have hu (i : Fin k) := tprovable_varEqualT_iff hd hf hL (u i)
  have hd' (u : Term V L₁) : S.internalize V ⊢ hT'.domT.subst ![u] 🡘 hT.domT.subst ![u] := by
    have := hd u
    cl_prover [this]
  have h₁ := relativizedImp_imp_relativizedImp_of_imp hT.domT hT'.domT _ _
    ((hT.relT R).subst fun i ↦ Semiterm.bvar (i.addCast 0))
    ((hT'.relT R).subst fun i ↦ Semiterm.bvar (i.addCast 0))
    (fun i ↦ tprovable_all_and_imp_and hd (hu i)) (by
      rw [e _ (hT.relT_shift R), e _ (hT'.relT_shift R)]
      exact K_left (hr R _))
  have h₂ := relativizedImp_imp_relativizedImp_of_imp hT'.domT hT.domT _ _
    ((hT'.relT R).subst fun i ↦ Semiterm.bvar (i.addCast 0))
    ((hT.relT R).subst fun i ↦ Semiterm.bvar (i.addCast 0))
    (fun i ↦ tprovable_all_and_imp_and hd' (tprovable_all_iff_symm (hu i))) (by
      rw [e _ (hT.relT_shift R), e _ (hT'.relT_shift R)]
      exact K_right (hr R _))
  cl_prover [h₁, h₂]

include hd hr hf in
lemma provable_iff_translate_rel_of_equiv (hL : L₂.SymbolsStandard V) {k r v : V}
    (hR : L₂.IsRel k r) (hv : IsTermVec L₂ k v) :
    Provable S (iff L₁ (translate L₁ L₂ tbl (^rel k r v)) (translate L₁ L₂ tbl' (^rel k r v))) := by
  obtain ⟨k, R, rfl, rfl⟩ := hL.1 _ _ hR
  obtain ⟨u, rfl⟩ := exists_termVec hv
  have h₁ := tprovable_translate_rel_iff hd hr hf hL R u
  rw [tprovable_iff_provable, Semiformula.val_iff, ← translate_rel_typed,
    ← translate_rel_typed] at h₁
  rwa [Semiformula.rel_val] at h₁

include hd hr hf in
/-- Along two tables whose entries are provably equivalent in `S`, every formula code has
provably equivalent translations. -/
theorem provable_iff_translate_of_equiv (hL : L₂.SymbolsStandard V) {p : V}
    (hp : IsFormula L₂ p) :
    Provable S (iff L₁ (translate L₁ L₂ tbl p) (translate L₁ L₂ tbl' p)) := by
  have hdd : Provable S (^∀ iff L₁ tbl.[0] tbl'.[0]) := by
    simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff,
      IsTable.domT_val, tableDomain] using tprovable_all_domT_iff hd
  apply IsFormula.sigma1_structural_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro k r v hR hv
    exact provable_iff_translate_rel_of_equiv hd hr hf hL hR hv
  · intro k r v hR hv
    have h₁ := provable_iff_translate_rel_of_equiv hd hr hf hL hR hv
    have h₂ : IsFormula L₂ (^rel k r v) := IsSemiformula.rel.mpr ⟨hR, hv⟩
    rw [translate_nrel hR hv.isUTerm, translate_nrel hR hv.isUTerm, ← translate_rel hR hv.isUTerm,
      ← translate_rel hR hv.isUTerm (tbl := tbl')]
    exact provable_iff_neg (IsSemiformula.translate hT h₂) (IsSemiformula.translate hT' h₂) h₁
  · have h₁ : S.internalize V ⊢ (⊤ : Formula V L₁) 🡘 ⊤ := by cl_prover
    simpa only [translate_verum, tprovable_iff_provable, Semiformula.val_iff,
      Semiformula.val_verum] using h₁
  · have h₁ : S.internalize V ⊢ (⊥ : Formula V L₁) 🡘 ⊥ := by cl_prover
    simpa only [translate_falsum, tprovable_iff_provable, Semiformula.val_iff,
      Semiformula.val_falsum] using h₁
  · intro p q hp hq ihp ihq
    rw [translate_and hp.isUFormula hq.isUFormula, translate_and hp.isUFormula hq.isUFormula]
    exact provable_iff_and (IsSemiformula.translate hT hp) (IsSemiformula.translate hT' hp)
      (IsSemiformula.translate hT hq) (IsSemiformula.translate hT' hq) ihp ihq
  · intro p q hp hq ihp ihq
    rw [translate_or hp.isUFormula hq.isUFormula, translate_or hp.isUFormula hq.isUFormula]
    exact provable_iff_or (IsSemiformula.translate hT hp) (IsSemiformula.translate hT' hp)
      (IsSemiformula.translate hT hq) (IsSemiformula.translate hT' hq) ihp ihq
  · intro p hp ih
    rw [translate_free hT hp, translate_free hT' hp] at ih
    rw [translate_all hp.isUFormula, translate_all hp.isUFormula, domainAt_zero hT,
      domainAt_zero hT']
    exact provable_all_imp_iff_all_imp hT.domain hT'.domain hdd (IsSemiformula.translate hT hp)
      (IsSemiformula.translate hT' hp) ih
  · intro p hp ih
    rw [translate_free hT hp, translate_free hT' hp] at ih
    rw [translate_exs hp.isUFormula, translate_exs hp.isUFormula, domainAt_zero hT,
      domainAt_zero hT']
    exact provable_exs_and_iff_exs_and hT.domain hT'.domain hdd (IsSemiformula.translate hT hp)
      (IsSemiformula.translate hT' hp) ih

include hd in
lemma tprovable_conj_domT_imp {m : ℕ} (u : Fin m → Term V L₁) :
    S.internalize V ⊢ Matrix.conj (fun i ↦ hT'.domT.subst ![u i]) 🡒
      Matrix.conj (fun i ↦ hT.domT.subst ![u i]) := by
  have h₁ := matrixConj_imp_matrixConj (𝓢 := S.internalize V) (φ := ⊤)
    (v := fun i ↦ hT'.domT.subst ![u i]) (u := fun i ↦ hT.domT.subst ![u i]) fun i ↦ by
      have := hd (u i)
      cl_prover [this]
  cl_prover [h₁]

include hd hf in
lemma tprovable_funcUniqueBody_imp {k : ℕ} (F : L₂.Func k) (w : Fin (k + 2) → Term V L₁) :
    S.internalize V ⊢ (funcUniqueBody hT.domT (hT.funcT F)).subst w 🡒
      (funcUniqueBody hT'.domT (hT'.funcT F)).subst w := by
  simp only [funcUniqueBody, Semiformula.substs_imp, Semiformula.substs_and,
    Semiformula.substs_conj, Semiformula.substs_substs, Semiformula.substs_equal,
    Matrix.vecMap_cons', Matrix.head_cons, Matrix.vecMap_nil, Semiterm.substs_bvar]
  have key {C C' D₀ D₀' D₁ D₁' G₀ G₀' G₁ G₁' E : Formula V L₁}
      (h₁ : S.internalize V ⊢ C' 🡒 C) (h₂ : S.internalize V ⊢ D₀ 🡘 D₀')
      (h₃ : S.internalize V ⊢ D₁ 🡘 D₁') (h₄ : S.internalize V ⊢ G₀ 🡘 G₀')
      (h₅ : S.internalize V ⊢ G₁ 🡘 G₁') :
      S.internalize V ⊢ (C ⋏ D₀ ⋏ D₁ ⋏ G₀ ⋏ G₁ 🡒 E) 🡒 (C' ⋏ D₀' ⋏ D₁' ⋏ G₀' ⋏ G₁' 🡒 E) := by
    have h₆ : S.internalize V ⊢ C' ⋏ D₀' ⋏ D₁' ⋏ G₀' ⋏ G₁' 🡒 C ⋏ D₀ ⋏ D₁ ⋏ G₀ ⋏ G₁ := by
      cl_prover 100 [h₁, h₂, h₃, h₄, h₅]
    cl_prover [h₆]
  exact key (tprovable_conj_domT_imp hd _) (hd _) (hd _) (hf F _) (hf F _)

include hf in
lemma tprovable_funcCongrBody_imp {k : ℕ} (F : L₂.Func k)
    (w : Fin (k + 1 + (k + 1)) → Term V L₁) :
    S.internalize V ⊢ (funcCongrBody (hT.funcT F)).subst w 🡒
      (funcCongrBody (hT'.funcT F)).subst w := by
  simp only [funcCongrBody, Semiformula.substs_imp, Semiformula.substs_substs]
  have key {E G₀ G₀' G₁ G₁' : Formula V L₁} (h₁ : S.internalize V ⊢ G₀ 🡘 G₀')
      (h₂ : S.internalize V ⊢ G₁ 🡘 G₁') :
      S.internalize V ⊢ (E 🡒 G₀ 🡒 G₁) 🡒 (E 🡒 G₀' 🡒 G₁') := by
    cl_prover [h₁, h₂]
  exact key (hf F _) (hf F _)

include hd hf in
lemma tprovable_funcExistsBody_imp {k : ℕ} (F : L₂.Func k) (w : Fin k → Term V L₁) :
    S.internalize V ⊢ (funcExistsBody hT.domT (hT.funcT F)).subst w 🡒
      (funcExistsBody hT'.domT (hT'.funcT F)).subst w := by
  have key {C C' : Formula V L₁} {X X' : Semiformula V L₁ 1} (h₁ : S.internalize V ⊢ C' 🡒 C)
      (h₂ : S.internalize V ⊢ ∀¹ (X 🡘 X')) :
      S.internalize V ⊢ (C 🡒 ∃¹ X) 🡒 (C' 🡒 ∃¹ X') := by
    have h₃ := tprovable_all_iff_exs X X' ⨀ h₂
    cl_prover [h₁, h₃]
  have key₂ {D D' G G' : Formula V L₁} (h₁ : S.internalize V ⊢ D 🡘 D')
      (h₂ : S.internalize V ⊢ G 🡘 G') : S.internalize V ⊢ D ⋏ G 🡘 D' ⋏ G' := by
    cl_prover [h₁, h₂]
  simp only [funcExistsBody, Semiformula.substs_imp, Semiformula.substs_conj,
    Semiformula.substs_substs, Semiformula.substs_ex, Matrix.vecMap_cons', Matrix.head_cons,
    Matrix.vecMap_nil, Semiterm.substs_bvar]
  apply key (tprovable_conj_domT_imp hd _)
  apply TProof.all!
  simp only [Semiformula.free, Semiformula.shift_iff, Semiformula.shift_and,
    Semiformula.shift_substs, Semiformula.substs_imply, Semiformula.substs_and,
    Semiformula.substs_substs, hT.domT_shift, hT'.domT_shift, hT.funcT_shift, hT'.funcT_shift,
    Matrix.vecMap_cons', Matrix.head_cons, Matrix.vecMap_nil]
  exact key₂ (hd _) (hf F _)

include hd hr in
lemma tprovable_preserveEqBody_imp [L₂.Eq] (w : Fin 2 → Term V L₁) :
    S.internalize V ⊢ (preserveEqBody hT.domT (hT.relT (Language.Eq.eq : L₂.Rel 2))).subst w 🡒
      (preserveEqBody hT'.domT (hT'.relT (Language.Eq.eq : L₂.Rel 2))).subst w := by
  simp only [preserveEqBody, LogicalConnective.iff, Semiformula.substs_imp, Semiformula.substs_and,
    Semiformula.substs_substs, Matrix.vecMap_cons', Matrix.head_cons, Matrix.vecMap_nil,
    Semiterm.substs_bvar]
  have key {D₁ D₁' D₀ D₀' E E' Q : Formula V L₁} (h₁ : S.internalize V ⊢ D₁ 🡘 D₁')
      (h₂ : S.internalize V ⊢ D₀ 🡘 D₀') (h₃ : S.internalize V ⊢ E 🡘 E') :
      S.internalize V ⊢ (D₁ 🡒 D₀ 🡒 (E 🡒 Q) ⋏ (Q 🡒 E)) 🡒 (D₁' 🡒 D₀' 🡒 (E' 🡒 Q) ⋏ (Q 🡒 E')) := by
    cl_prover 100 [h₁, h₂, h₃]
  exact key (hd _) (hd _) (hr _ _)

include hd hr hf in
/-- A table whose domain formula and the entries of whose symbols are provably equivalent in `S`
to those of a table of a translation in `S` is itself a table of a translation in `S`. -/
theorem IsTranslationTable.of_provable_iff [L₂.Eq] (h : IsTranslationTable L₂ S tbl)
    (hL : L₂.SymbolsStandard V) : IsTranslationTable L₂ S tbl' where
  toIsTable := hT'
  exs_domain := by
    have h₁ : S.internalize V ⊢ ∃¹ hT.domT := tprovable_iff_provable.mpr h.exs_domain
    exact tprovable_iff_provable.mp <| K_left (tprovable_all_iff_exs _ _ ⨀
      tprovable_all_domT_iff hd) ⨀ h₁
  func_exists {k f} hf' := by
    obtain ⟨k, F, rfl, rfl⟩ := hL.2 _ _ hf'
    rw [← funcExistsBody_val hT'.domT rfl (hT'.funcT F) rfl]
    apply provable_qqAlls_of_forall_tprovable _ (funcExistsBody_shift hT'.domT_shift
      (hT'.funcT_shift F))
    intro w
    apply tprovable_funcExistsBody_imp hd hf F w ⨀ tprovable_subst_of_provable_qqAlls _ w _
    rw [funcExistsBody_val _ rfl _ rfl]
    exact h.func_exists hf'
  func_unique {k f} hf' := by
    obtain ⟨k, F, rfl, rfl⟩ := hL.2 _ _ hf'
    have h₁ := provable_qqAlls_of_forall_tprovable (S := S) _ (funcUniqueBody_shift
      hT'.domT_shift (hT'.funcT_shift F)) fun w ↦
        tprovable_funcUniqueBody_imp hd hf F w ⨀ tprovable_subst_of_provable_qqAlls _ w (by
          rw [funcUniqueBody_val _ rfl _ rfl]
          simpa [add_assoc, one_add_one_eq_two] using h.func_unique hf')
    rw [funcUniqueBody_val _ rfl _ rfl] at h₁
    simpa [add_assoc, one_add_one_eq_two] using h₁
  func_congr {k f} hf' := by
    obtain ⟨k, F, rfl, rfl⟩ := hL.2 _ _ hf'
    have h₁ := provable_qqAlls_of_forall_tprovable (S := S) _ (funcCongrBody_shift
      (hT'.funcT_shift F)) fun w ↦
        tprovable_funcCongrBody_imp hf F w ⨀ tprovable_subst_of_provable_qqAlls _ w (by
          rw [funcCongrBody_val _ rfl]
          simpa using h.func_congr hf')
    rw [funcCongrBody_val _ rfl] at h₁
    simpa using h₁
  preserve_eq := by
    have h₁ := provable_qqAlls_of_forall_tprovable (S := S) _ (preserveEqBody_shift
      hT'.domT_shift (hT'.relT_shift (Language.Eq.eq : L₂.Rel 2))) fun w ↦
        tprovable_preserveEqBody_imp hd hr w ⨀ tprovable_subst_of_provable_qqAlls _ w (by
          rw [preserveEqBody_val _ rfl (hT.relT (Language.Eq.eq : L₂.Rel 2)) rfl]
          simpa using h.preserve_eq)
    rw [preserveEqBody_val _ rfl (hT'.relT (Language.Eq.eq : L₂.Rel 2)) rfl] at h₁
    simpa using h₁

end congruence

end

section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding



open _root_.FFL.Entailment

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {S : Theory L} [S.Δ₁] [𝗘𝗤 L ⪯ S]
  {tbl : V} (h : IsTableOf (DirectTranslation.id S) tbl) (hL : L.SymbolsStandard V)

namespace IsTableOf

include h hL

omit [S.Δ₁] in
lemma id_domT : (h.isTable hL).domT = ⊤ := by
  rw [show (h.isTable hL).domT = ⌜(DirectTranslation.id S).domain.sentence⌝ from
    Semiformula.ext h.domain]
  simp [DirectTranslation.id]

omit [S.Δ₁] in
lemma id_relT {k : ℕ} (R : L.Rel k) : (h.isTable hL).relT R = Semiformula.rel R Semiterm.bvar := by
  rw [show (h.isTable hL).relT R = ⌜((DirectTranslation.id S).rel R).sentence⌝ from
    Semiformula.ext (h.rel R)]
  simp [DirectTranslation.id_rel_def]

omit [S.Δ₁] in
lemma id_funcT {k : ℕ} (F : L.Func k) : (h.isTable hL).funcT F =
    Semiformula.equal (Semiterm.bvar 0) (Semiterm.func F fun i ↦ Semiterm.bvar i.succ) := by
  rw [show (h.isTable hL).funcT F = ⌜((DirectTranslation.id S).func F).sentence⌝ from
    Semiformula.ext (h.func F)]
  simp [DirectTranslation.id_func_def]

lemma id_tprovable_domT_subst (t : Term V L) :
    S.internalize V ⊢ (h.isTable hL).domT.subst ![t] := by
  rw [h.id_domT hL, Semiformula.substs_verum]
  cl_prover

lemma id_tprovable_varEqualT_func {k : ℕ} (F : L.Func k) (u : Fin k → Term V L)
    (ih : ∀ i, S.internalize V ⊢ ∀¹ (varEqualT (h.isTable hL) (u i) 🡘
      Semiformula.equal (Semiterm.bvar 0) (u i).bShift)) :
    S.internalize V ⊢ ∀¹ (varEqualT (h.isTable hL) (Semiterm.func F u) 🡘
      Semiformula.equal (Semiterm.bvar 0) (Semiterm.func F u).bShift) := by
  have hs (j : ℕ) : Semiformula.shift^[j]
      (Semiformula.equal (Semiterm.fvar 0) (Semiterm.func F Semiterm.bvar) : Semiformula V L k) =
        Semiformula.equal (Semiterm.fvar (j : V)) (Semiterm.func F Semiterm.bvar) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, Semiformula.shift_equal]
      simp only [Semiterm.shift_fvar, Semiterm.shift_func]
      congr 2
      funext i
      simp
  have hX (j : ℕ) (s w : Fin k → Term V L) : S.internalize V ⊢
      Matrix.conj (fun i ↦ Semiformula.equal (s i) (w i)) 🡒
        (Semiformula.shift^[j] (Semiformula.equal (Semiterm.fvar 0)
          (Semiterm.func F Semiterm.bvar))).subst w 🡒
        (Semiformula.shift^[j] (Semiformula.equal (Semiterm.fvar 0)
          (Semiterm.func F Semiterm.bvar))).subst s := by
    rw [hs]
    simp only [Semiformula.substs_equal, Semiterm.substs_fvar, Semiterm.substs_func,
      Semiterm.substs_vecMap_bvar_id]
    have h₁ := tprovable_equal_func_imp S F s w
    have h₂ := tprovable_equal_symm_imp S (Semiterm.func F s) (Semiterm.func F w)
    have h₃ := tprovable_equal_trans_imp S (Semiterm.fvar (j : V)) (Semiterm.func F w)
      (Semiterm.func F s)
    cl_prover [h₁, h₂, h₃]
  have h₄ := tprovable_relativizedImp_equal_iff (T := S) (h.isTable hL).domT
    (h.id_tprovable_domT_subst hL) (fun i ↦ (u i).shift) _ hX
  have h₅ : S.internalize V ⊢ ∀¹ (funcGraph (h.isTable hL).domT
      (fun i ↦ Semiformula.equal (Semiterm.bvar 0) (u i).bShift) ((h.isTable hL).funcT F) 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.func F u).bShift) := by
    apply TProof.all!
    rw [Semiformula.free_iff, Semiformula.free, Semiformula.free, shift_funcGraph,
      funcGraph_subst_fvar, (h.isTable hL).domT_shift, (h.isTable hL).funcT_shift, h.id_funcT hL]
    simp only [Semiformula.substs_equal, Semiterm.substs_fvar, Semiterm.substs_func,
      Semiterm.substs_vecMap_bvar_id, Semiformula.shift_equal, Semiterm.shift_bvar,
      Semiterm.substs_bvar, Matrix.cons_val_zero, Semiterm.substs_vecMap_bvar, Matrix.cons_val_succ,
      Semiterm.bShift_func, Semiterm.shift_func, Matrix.cons_val_fin_one] at h₄ ⊢
    convert h₄ using 4 <;> try funext i
    · simp [Semiterm.bShift_shift_comm]
    · change ((u i).bShift.shift).subst ![Semiterm.fvar 0] = (u i).shift
      rw [← Semiterm.bShift_shift_comm, Semiterm.bShift_substs_sing]
  have h₁ := funcGraph_congr (T := S) (h.isTable hL).domT
    (fun i ↦ varEqualT (h.isTable hL) (u i))
    (fun i ↦ Semiformula.equal (Semiterm.bvar 0) (u i).bShift) ((h.isTable hL).funcT F)
  have h₂ : S.internalize V ⊢ Matrix.conj fun i ↦ ∀¹ ((h.isTable hL).domT 🡒
      (varEqualT (h.isTable hL) (u i) 🡘 Semiformula.equal (Semiterm.bvar 0) (u i).bShift)) :=
    tprovable_conj S fun i ↦ tprovable_all_imp_all _ _ ⨀ ih i
  rw [varEqualT_func]
  exact tprovable_all_iff_trans (h₁ ⨀ h₂) h₅

lemma id_tprovable_varEqualT (t : Term V L) :
    S.internalize V ⊢ ∀¹ (varEqualT (h.isTable hL) t 🡘
      Semiformula.equal (Semiterm.bvar 0) t.bShift) := by
  have hE (t : Term V L) : (∀¹ (varEqualT (h.isTable hL) t 🡘
      Semiformula.equal (Semiterm.bvar 0) t.bShift)).val = ^∀ iff L (varEqual L L tbl t.val)
        (^rel 2 (Encodable.encode (Language.Eq.eq : L.Rel 2) : V) ?[^#0, t.val]) := by
    simp [Semiformula.equal, termBShift_zero t.isSemiterm]
    rfl
  have hP : 𝚺ᴬ₁-Predicate fun t : V ↦ Provable S (^∀ iff L (varEqual L L tbl t)
      (^rel 2 (Encodable.encode (Language.Eq.eq : L.Rel 2) : V) ?[^#0, t])) := by
    definability
  have key := IsSemiterm.sigma1_induction hP (n := 0) (fun z hz ↦ by simp at hz) ?_ ?_ t.val
    t.isSemiterm
  · rw [tprovable_iff_provable, hE]
    exact key
  · intro x
    have h₁ : S.internalize V ⊢ ∀¹ (varEqualT (h.isTable hL) (Semiterm.fvar x) 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x : Term V L).bShift) := by
      rw [varEqualT_fvar, Semiterm.bShift_fvar]
      apply TProof.all!
      rw [Semiformula.free_iff]
      cl_prover
    rw [tprovable_iff_provable, hE] at h₁
    exact h₁
  · intro k f v hf hv ih
    obtain ⟨k, F, u, rfl, rfl, rfl⟩ := exists_func_termVec hL (IsSemiterm.func.mpr ⟨hf, hv⟩)
    have ih' (i : Fin k) : S.internalize V ⊢ ∀¹ (varEqualT (h.isTable hL) (u i) 🡘
        Semiformula.equal (Semiterm.bvar 0) (u i).bShift) := by
      rw [tprovable_iff_provable, hE]
      simpa using ih ((i : ℕ) : V) (by simp)
    have h₁ := h.id_tprovable_varEqualT_func hL F u ih'
    rw [tprovable_iff_provable, hE, Semiterm.func_val] at h₁
    exact h₁

lemma id_tprovable_rel_iff {k : ℕ} (R : L.Rel k) (u : Fin k → Term V L) :
    S.internalize V ⊢ Semiformula.rel R u 🡘 relativizedImp (h.isTable hL).domT
      (fun i ↦ varEqualT (h.isTable hL) (u i))
      (((h.isTable hL).relT R).subst fun i ↦ Semiterm.bvar (i.addCast 0)) := by
  have hX (j : ℕ) (s w : Fin k → Term V L) : S.internalize V ⊢
      Matrix.conj (fun i ↦ Semiformula.equal (s i) (w i)) 🡒
        (Semiformula.shift^[j] (Semiformula.rel R Semiterm.bvar)).subst w 🡒
          (Semiformula.shift^[j] (Semiformula.rel R Semiterm.bvar)).subst s := by
    have h₀ : (Semiformula.rel R Semiterm.bvar : Semiformula V L k).shift =
        Semiformula.rel R Semiterm.bvar := by
      rw [Semiformula.shift_rel]
      congr 1
      funext i
      simp
    rw [Function.iterate_fixed h₀ j]
    have h₁ := tprovable_rel_congr_imp S R w s
    have h₂ := matrixConj_imp_matrixConj (𝓢 := S.internalize V) (φ := ⊤)
      (v := fun i ↦ Semiformula.equal (s i) (w i)) (u := fun i ↦ Semiformula.equal (w i) (s i))
      fun i ↦ by
        have := tprovable_equal_symm_imp S (s i) (w i)
        cl_prover [this]
    simp only [Semiformula.substs_rel, Semiterm.substs_vecMap_bvar_id]
    cl_prover [h₁, h₂]
  have h₁ := relativizedImp_congr (T := S) (h.isTable hL).domT
    (fun i ↦ varEqualT (h.isTable hL) (u i))
    (fun i ↦ Semiformula.equal (Semiterm.bvar 0) (u i).bShift)
    (((h.isTable hL).relT R).subst fun i ↦ Semiterm.bvar (i.addCast 0))
  have h₂ : S.internalize V ⊢ Matrix.conj fun i ↦ ∀¹ ((h.isTable hL).domT 🡒
      (varEqualT (h.isTable hL) (u i) 🡘 Semiformula.equal (Semiterm.bvar 0) (u i).bShift)) :=
    tprovable_conj S fun i ↦ tprovable_all_imp_all _ _ ⨀ h.id_tprovable_varEqualT hL (u i)
  have h₃ := tprovable_relativizedImp_equal_iff (T := S) (h.isTable hL).domT
    (h.id_tprovable_domT_subst hL) u _ hX
  rw [h.id_relT hL] at h₁ ⊢
  simp only [Semiformula.substs_rel, Semiterm.substs_vecMap_bvar_id] at h₁ h₃ ⊢
  cl_prover [h₁, h₂, h₃]

lemma id_provable_iff_translate_rel {k r v : V} (hR : L.IsRel k r) (hv : IsTermVec L k v) :
    Provable S (iff L (^rel k r v) (translate L L tbl (^rel k r v))) := by
  obtain ⟨k, R, rfl, rfl⟩ := hL.1 _ _ hR
  obtain ⟨u, rfl⟩ := exists_termVec hv
  have h₁ := h.id_tprovable_rel_iff hL R u
  rw [tprovable_iff_provable, Semiformula.val_iff, ← translate_rel_typed] at h₁
  rwa [Semiformula.rel_val] at h₁

/-- Along a table of the identity translation, every formula code is provably equivalent to its
translation. -/
theorem id_provable_iff_translate {p : V} (hp : IsFormula L p) :
    Provable S (iff L p (translate L L tbl p)) := by
  have hT := h.isTable hL
  have hd : Provable S (^∀ tbl.[0]) := by
    have h₁ : S.internalize V ⊢ ∀¹ hT.domT := by
      rw [h.id_domT hL]
      exact TProof.all! (by simp [Semiformula.free])
    exact tprovable_iff_provable.mp h₁
  apply IsFormula.sigma1_structural_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro k r v hR hv
    exact h.id_provable_iff_translate_rel hL hR hv
  · intro k r v hR hv
    have h₁ := h.id_provable_iff_translate_rel hL hR hv
    have h₂ : IsFormula L (^rel k r v) := IsSemiformula.rel.mpr ⟨hR, hv⟩
    rw [translate_nrel hR hv.isUTerm, ← translate_rel hR hv.isUTerm, ← neg_rel hR hv.isUTerm]
    exact provable_iff_neg h₂ (IsSemiformula.translate hT h₂) h₁
  · have h₁ : S.internalize V ⊢ (⊤ : Formula V L) 🡘 ⊤ := by cl_prover
    simpa only [translate_verum, tprovable_iff_provable, Semiformula.val_iff,
      Semiformula.val_verum] using h₁
  · have h₁ : S.internalize V ⊢ (⊥ : Formula V L) 🡘 ⊥ := by cl_prover
    simpa only [translate_falsum, tprovable_iff_provable, Semiformula.val_iff,
      Semiformula.val_falsum] using h₁
  · intro p q hp hq ihp ihq
    rw [translate_and hp.isUFormula hq.isUFormula]
    exact provable_iff_and hp (IsSemiformula.translate hT hp) hq (IsSemiformula.translate hT hq)
      ihp ihq
  · intro p q hp hq ihp ihq
    rw [translate_or hp.isUFormula hq.isUFormula]
    exact provable_iff_or hp (IsSemiformula.translate hT hp) hq (IsSemiformula.translate hT hq)
      ihp ihq
  · intro p hp ih
    rw [translate_free hT hp] at ih
    rw [translate_all hp.isUFormula, domainAt_zero hT]
    exact provable_all_iff_all_of_domain hT.domain hd hp (IsSemiformula.translate hT hp) ih
  · intro p hp ih
    rw [translate_free hT hp] at ih
    rw [translate_exs hp.isUFormula, domainAt_zero hT]
    exact provable_exs_iff_exs_of_domain hT.domain hd hp (IsSemiformula.translate hT hp) ih

/-- Along a table of the identity translation, the translation of a provable formula code is
provable. -/
theorem id_provable_translate {p : V} (hpr : Provable S p) : Provable S (translate L L tbl p) := by
  have hp : IsFormula L p := (IsFormulaSet.insert_iff.mp hpr.toDerivable.isFormulaSet).1
  have hq : IsFormula L (translate L L tbl p) := IsSemiformula.translate (h.isTable hL) hp
  have h₁ := (provable_iff_iff_tprovable hp hq).mp (h.id_provable_iff_translate hL hp)
  have h₂ : S.internalize V ⊢ (⟨p, hp⟩ : Formula V L) := tprovable_iff_provable.mpr hpr
  exact tprovable_iff_provable.mp (K_left h₁ ⨀ h₂)

end IsTableOf

end

end FFL.FirstOrder.Arithmetic.Bootstrapping
