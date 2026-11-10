module

public import AlphaCentauri.Bootstrapping.Interpretability.SoundnessRules
public import AlphaCentauri.Bootstrapping.Interpretability.ValueLemma

/-!
# Translations along provably equivalent tables

If the domain formulas, the formulas of the relation symbols and the graphs of the function symbols
of two tables are provably equivalent in `S`, every formula code has provably equivalent
translations along the two tables.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

end congruence

end FFL.FirstOrder.Arithmetic.Bootstrapping
