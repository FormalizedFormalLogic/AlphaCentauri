module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.Bootstrapping.Interpretability.SoundnessRules
public import AlphaCentauri.Bootstrapping.Interpretability.ValueLemma

/-!
# The internal identity translation

Along a table of the identity translation `DirectTranslation.id S`, the coded formula of the value
of a closed term `t` is provably equivalent to `^#0 = t`, every formula code is provably equivalent
to its translation, and so the translation of every formula code provable in `S` is provable in `S`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

lemma id_tprovable_varEqualT_func {k : ℕ} (F : L.Func k) (u : Fin k → Term V L)
    (ih : ∀ i, S.internalize V ⊢ ∀¹ (varEqualT (h.isTable hL) (u i) 🡘
      Semiformula.equal (Semiterm.bvar 0) (u i).bShift)) :
    S.internalize V ⊢ ∀¹ (varEqualT (h.isTable hL) (Semiterm.func F u) 🡘
      Semiformula.equal (Semiterm.bvar 0) (Semiterm.func F u).bShift) := by
  have hd (t : Term V L) : S.internalize V ⊢ (h.isTable hL).domT.subst ![t] := by
    rw [h.id_domT hL, Semiformula.substs_verum]
    cl_prover
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
  have h₄ := tprovable_relativizedImp_equal_iff (T := S) (h.isTable hL).domT hd
    (fun i ↦ (u i).shift) _ hX
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
  have hd (t : Term V L) : S.internalize V ⊢ (h.isTable hL).domT.subst ![t] := by
    rw [h.id_domT hL, Semiformula.substs_verum]
    cl_prover
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
  have h₃ := tprovable_relativizedImp_equal_iff (T := S) (h.isTable hL).domT hd u _ hX
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
  have hd : S.internalize V ⊢ ∀¹ hT.domT := by
    rw [h.id_domT hL]
    exact TProof.all! (by simp [Semiformula.free])
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
    have hq : IsSemiformula L 1 (translate L L tbl p) := IsSemiformula.translate hT hp
    rw [translate_free hT hp] at ih
    have h₁ := provable_all_iff_of_free hp hq ih
    have h₂ : S.internalize V ⊢ ∀¹ ((⟨p, by simpa using hp⟩ : Semiformula V L 1) 🡘
        ⟨_, by simpa using hq⟩) := by
      simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using h₁
    have h₃ := tprovable_all_iff_all_of_domain hd _ _ ⨀ h₂
    rw [translate_all hp.isUFormula, domainAt_zero hT]
    simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_all,
      Semiformula.val_imp, IsTable.domT_val, tableDomain] using h₃
  · intro p hp ih
    have hq : IsSemiformula L 1 (translate L L tbl p) := IsSemiformula.translate hT hp
    rw [translate_free hT hp] at ih
    have h₁ := provable_all_iff_of_free hp hq ih
    have h₂ : S.internalize V ⊢ ∀¹ ((⟨p, by simpa using hp⟩ : Semiformula V L 1) 🡘
        ⟨_, by simpa using hq⟩) := by
      simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using h₁
    have h₃ := tprovable_exs_iff_exs_of_domain hd _ _ ⨀ h₂
    rw [translate_exs hp.isUFormula, domainAt_zero hT]
    simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_exs,
      Semiformula.val_and, IsTable.domT_val, tableDomain] using h₃

/-- Along a table of the identity translation, the translation of a provable formula code is
provable. -/
theorem id_provable_translate {p : V} (hpr : Provable S p) : Provable S (translate L L tbl p) := by
  have hp : IsFormula L p := (IsFormulaSet.insert_iff.mp hpr.toDerivable.isFormulaSet).1
  have hq : IsFormula L (translate L L tbl p) := IsSemiformula.translate (h.isTable hL) hp
  have h₁ := (provable_iff_iff_tprovable hp hq).mp (h.id_provable_iff_translate hL hp)
  have h₂ : S.internalize V ⊢ (⟨p, hp⟩ : Formula V L) := tprovable_iff_provable.mpr hpr
  exact tprovable_iff_provable.mp (K_left h₁ ⨀ h₂)

end IsTableOf

end FFL.FirstOrder.Arithmetic.Bootstrapping
