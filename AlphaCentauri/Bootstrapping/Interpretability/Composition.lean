module

public import AlphaCentauri.Bootstrapping.Interpretability.CompositeTable
public import AlphaCentauri.Bootstrapping.Interpretability.RelativizedBlocks
public import AlphaCentauri.Bootstrapping.Interpretability.TypedTranslation

/-!
# Composition of translations

Along the composite of two tables, every formula code has a translation provably equivalent to the
translation along `tbl₁` of its translation along `tbl₂`. If every theorem of `U` translates to a
theorem of `S` along `tbl₁`, the composite of a table of a translation in `S` and a table of a
translation in `U` is a table of a translation in `S`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open _root_.FFL.Entailment

/-! ## Translations of equations -/

section equalBlock

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {T : Theory L} [T.Δ₁] [𝗘𝗤 L ⪯ T]

lemma relativizedImp_equal_specialize {k : ℕ} (d : Semiformula V L 1) (u : Fin k → Term V L)
    (X : Semiformula V L k) :
    T.internalize V ⊢ relativizedImp d (fun i ↦ Semiformula.equal (Semiterm.bvar 0) (u i).bShift)
      (X.subst fun i ↦ Semiterm.bvar (i.addCast 0)) 🡒
        Matrix.conj (fun i ↦ d.subst ![u i]) 🡒 X.subst u := by
  have h₁ := TProof.allItr_specialize (T := T) (Matrix.conj (fun i : Fin k ↦
      d.subst ![Semiterm.bvar (i.addCast 0)] ⋏
        (Semiformula.equal (Semiterm.bvar 0) (u i).bShift).subst ![Semiterm.bvar (i.addCast 0)]) 🡒
      X.subst fun i ↦ Semiterm.bvar (i.addCast 0)) (fun j ↦ u (Fin.cast (zero_add k) j))
  simp only [Semiformula.substs_equal, Semiterm.substs_bvar, Matrix.cons_val_fin_one,
    Semiterm.bShift_substs_succ, Matrix.tail_cons, Semiformula.substs_imp, Semiformula.substs_conj,
    Semiformula.substs_and, Semiformula.substs_substs, Matrix.vecMap_cons', Matrix.head_cons,
    Matrix.vecMap_nil, Semiterm.substs_substs, Semiterm.bShift_substs_zero,
    Semiterm.substs_vecMap_bvar] at h₁
  have hc := matrixConj_imp_matrixConj (𝓢 := T.internalize V) (φ := ⊤)
    (v := fun i : Fin k ↦ d.subst ![u i])
    (u := fun i : Fin k ↦ d.subst ![u i] ⋏ Semiformula.equal (u i) (u i)) fun i ↦ by
      have := tprovable_equal_refl T (u i)
      cl_prover [this]
  unfold relativizedImp
  simp only [Semiformula.substs_equal, Semiterm.substs_bvar, Matrix.cons_val_fin_one,
    Semiterm.bShift_substs_succ, Matrix.tail_cons]
  cl_prover [h₁, hc]

omit [𝗘𝗤 L ⪯ T] in
lemma relativizedImp_equal_generalize {k : ℕ} {d : Semiformula V L 1} (hd : d.shift = d)
    (u : Fin k → Term V L) (X : Semiformula V L k)
    (hX : ∀ (j : ℕ) (s w : Fin k → Term V L), T.internalize V ⊢
      Matrix.conj (fun i ↦ d.subst ![s i]) 🡒 Matrix.conj (fun i ↦ d.subst ![w i]) 🡒
        Matrix.conj (fun i ↦ Semiformula.equal (s i) (w i)) 🡒
          (Semiformula.shift^[j] X).subst w 🡒 (Semiformula.shift^[j] X).subst s) :
    T.internalize V ⊢ Matrix.conj (fun i ↦ d.subst ![u i]) ⋏ X.subst u 🡒
      relativizedImp d (fun i ↦ Semiformula.equal (Semiterm.bvar 0) (u i).bShift)
        (X.subst fun i ↦ Semiterm.bvar (i.addCast 0)) := by
  have hdk : Semiformula.shift^[k] d = d := Function.iterate_fixed hd k
  unfold relativizedImp
  apply TProof.allItr_generalize_imp
  simp only [Semiformula.shift_iterate_subst, Semiformula.substs_equal, Semiterm.substs_bvar,
    Matrix.cons_val_fin_one, Semiterm.bShift_substs_succ, Matrix.tail_cons,
    Semiformula.shift_iterate_imp, Semiformula.shift_iterate_conj, Semiformula.shift_iterate_and,
    Matrix.vecMap_cons', Matrix.head_cons, Semiterm.shift_iterate_bvar, Matrix.vecMap_nil,
    Semiformula.shift_iterate_equal, Semiterm.shift_iterate_subst_nil,
    Semiterm.shift_iterate_vecMap_bvar, Semiformula.substs_imp, Semiformula.substs_conj,
    Semiformula.substs_and, Semiformula.substs_substs, Fin.addCast_val, Semiterm.subst_nil_subst,
    Semiterm.bShift_substs_zero, Semiterm.substs_vecMap_bvar, hdk]
  have h₃ := hX k (fun i ↦ Semiterm.fvar ((i : ℕ) : V)) (fun i ↦ Semiterm.shift^[k] (u i))
  rw [show (Semiterm.shift^[k] ⨟ u) = fun i ↦ Semiterm.shift^[k] (u i) from rfl]
  have h₄ := matrixConj_imp_matrixConj (𝓢 := T.internalize V) (φ := ⊤)
    (v := fun i : Fin k ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
      Semiformula.equal (Semiterm.fvar ((i : ℕ) : V)) (Semiterm.shift^[k] (u i)))
    (u := fun i : Fin k ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) fun i ↦ by cl_prover
  have h₅ := matrixConj_imp_matrixConj (𝓢 := T.internalize V) (φ := ⊤)
    (v := fun i : Fin k ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
      Semiformula.equal (Semiterm.fvar ((i : ℕ) : V)) (Semiterm.shift^[k] (u i)))
    (u := fun i : Fin k ↦
      Semiformula.equal (Semiterm.fvar ((i : ℕ) : V)) (Semiterm.shift^[k] (u i))) fun i ↦ by
      cl_prover
  cl_prover 60 [h₃, h₄, h₅]

end equalBlock

section equation

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {S : Theory L} [S.Δ₁] [𝗘𝗤 L ⪯ S]
  {tbl : V} (h : IsTranslationTable L S tbl)

omit [L.Eq] in
lemma eq_vec_two {α : Type*} (s : Fin 2 → α) : s = ![s 0, s 1] := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

omit [𝗘𝗤 L ⪯ S] in
lemma IsTranslationTable.transT_equal_fvar {x y : V} {u : Fin 2 → Term V L}
    (hu : u = ![Semiterm.fvar x, Semiterm.fvar y]) :
    h.transT (Semiformula.equal (Semiterm.fvar x) (Semiterm.fvar y)) =
      relativizedImp h.domT (fun i ↦ Semiformula.equal (Semiterm.bvar 0) (u i).bShift)
        ((h.relT (Language.Eq.eq : L.Rel 2)).subst fun i ↦ Semiterm.bvar (i.addCast 0)) := by
  subst hu
  ext
  rw [IsTable.transT_val, Semiformula.equal, translate_rel_typed h.toIsTable]
  congr 3
  funext i
  match i with
  | 0 => simpa [Semiformula.equal] using varEqualT_fvar h.toIsTable x
  | 1 => simpa [Semiformula.equal] using varEqualT_fvar h.toIsTable y

lemma IsTranslationTable.tprovable_relT_equal_transport (j : ℕ) (s w : Fin 2 → Term V L) :
    S.internalize V ⊢ Matrix.conj (fun i ↦ h.domT.subst ![s i]) 🡒
      Matrix.conj (fun i ↦ h.domT.subst ![w i]) 🡒
        Matrix.conj (fun i ↦ Semiformula.equal (s i) (w i)) 🡒
          (Semiformula.shift^[j] (h.relT (Language.Eq.eq : L.Rel 2))).subst w 🡒
            (Semiformula.shift^[j] (h.relT (Language.Eq.eq : L.Rel 2))).subst s := by
  rw [Function.iterate_fixed (h.relT_shift _) j]
  have hs := h.tprovable_preserve_eq (s 0) (s 1)
  have hw := h.tprovable_preserve_eq (w 0) (w 1)
  rw [← eq_vec_two s] at hs
  rw [← eq_vec_two w] at hw
  have a₀ := matrixConj_elim (𝓢 := S.internalize V) (fun i ↦ h.domT.subst ![s i]) 0
  have a₁ := matrixConj_elim (𝓢 := S.internalize V) (fun i ↦ h.domT.subst ![s i]) 1
  have b₀ := matrixConj_elim (𝓢 := S.internalize V) (fun i ↦ h.domT.subst ![w i]) 0
  have b₁ := matrixConj_elim (𝓢 := S.internalize V) (fun i ↦ h.domT.subst ![w i]) 1
  have c₀ := matrixConj_elim (𝓢 := S.internalize V)
    (fun i ↦ Semiformula.equal (s i) (w i)) 0
  have c₁ := matrixConj_elim (𝓢 := S.internalize V)
    (fun i ↦ Semiformula.equal (s i) (w i)) 1
  have t₁ := tprovable_equal_trans_imp S (s 0) (w 0) (w 1)
  have t₂ := tprovable_equal_symm_imp S (s 1) (w 1)
  have t₃ := tprovable_equal_trans_imp S (s 0) (w 1) (s 1)
  have t₄ : S.internalize V ⊢ Semiformula.equal (s 0) (w 0) 🡒 Semiformula.equal (s 1) (w 1) 🡒
      Semiformula.equal (w 0) (w 1) 🡒 Semiformula.equal (s 0) (s 1) := by
    cl_prover [t₁, t₂, t₃]
  have key {Cs Cw Ce Ew Es D0s D1s D0w D1w e0 e1 Qs Qw : Formula V L}
      (hs : S.internalize V ⊢ D0s 🡒 D1s 🡒 (Es 🡘 Qs))
      (hw : S.internalize V ⊢ D0w 🡒 D1w 🡒 (Ew 🡘 Qw))
      (a₀ : S.internalize V ⊢ Cs 🡒 D0s) (a₁ : S.internalize V ⊢ Cs 🡒 D1s)
      (b₀ : S.internalize V ⊢ Cw 🡒 D0w) (b₁ : S.internalize V ⊢ Cw 🡒 D1w)
      (c₀ : S.internalize V ⊢ Ce 🡒 e0) (c₁ : S.internalize V ⊢ Ce 🡒 e1)
      (t₄ : S.internalize V ⊢ e0 🡒 e1 🡒 Qw 🡒 Qs) :
      S.internalize V ⊢ Cs 🡒 Cw 🡒 Ce 🡒 Ew 🡒 Es := by
    cl_prover 100 [hs, hw, a₀, a₁, b₀, b₁, c₀, c₁, t₄]
  exact key hs hw a₀ a₁ b₀ b₁ c₀ c₁ t₄

/-- On the domain, the translation of an equation between free variables is equivalent to the
equation. -/
lemma IsTranslationTable.tprovable_transT_equal_iff (x y : V) :
    S.internalize V ⊢ h.domT.subst ![Semiterm.fvar x] 🡒 h.domT.subst ![Semiterm.fvar y] 🡒
      (h.transT (Semiformula.equal (Semiterm.fvar x) (Semiterm.fvar y)) 🡘
        Semiformula.equal (Semiterm.fvar x) (Semiterm.fvar y)) := by
  rw [h.transT_equal_fvar rfl]
  have hp := h.tprovable_preserve_eq (Semiterm.fvar x) (Semiterm.fvar y)
  have h₁ := relativizedImp_equal_specialize (T := S) (k := 2) h.domT
    ![(Semiterm.fvar x : Term V L), Semiterm.fvar y] (h.relT (Language.Eq.eq : L.Rel 2))
  have h₂ := relativizedImp_equal_generalize (T := S) (k := 2) h.domT_shift
    ![(Semiterm.fvar x : Term V L), Semiterm.fvar y] (h.relT (Language.Eq.eq : L.Rel 2))
    (h.tprovable_relT_equal_transport)
  have h₃ : S.internalize V ⊢ h.domT.subst ![Semiterm.fvar x] 🡒 h.domT.subst ![Semiterm.fvar y] 🡒
      Matrix.conj (fun i : Fin 2 ↦
        h.domT.subst ![(![(Semiterm.fvar x : Term V L), Semiterm.fvar y] i)]) := by
    apply CC_of_CK
    apply matrixConj_intro
    intro i
    match i with
    | 0 => exact and₁
    | 1 => exact and₂
  have key {Dx Dy RI E Q C : Formula V L} (hp : S.internalize V ⊢ Dx 🡒 Dy 🡒 (E 🡘 Q))
      (h₁ : S.internalize V ⊢ RI 🡒 C 🡒 E) (h₂ : S.internalize V ⊢ C ⋏ E 🡒 RI)
      (h₃ : S.internalize V ⊢ Dx 🡒 Dy 🡒 C) : S.internalize V ⊢ Dx 🡒 Dy 🡒 (RI 🡘 Q) := by
    cl_prover 100 [hp, h₁, h₂, h₃]
  exact key hp h₁ h₂ h₃

end equation


/-! ## Translations along the composite table -/

section compShapes

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {tbl₁ tbl₂ : V}
  (hT₁ : IsTable L L tbl₁) (hT₂ : IsTable L L tbl₂)
  (hc : IsTable L L (Bootstrapping.compTable L L tbl₁ tbl₂))

include hT₁ in
lemma IsTable.compTable_domT : hc.domT = hT₁.domT ⋏ hT₁.transT hT₂.domT := by
  ext; simp [tableDomain_compTable]

include hT₁ in
lemma IsTable.compTable_relT {k : ℕ} (R : L.Rel k) : hc.relT R = hT₁.transT (hT₂.relT R) := by
  ext; simp [tableRel_compTable (hT₂.lt_len_rel (codeIn_rel_quote R))]

include hT₁ in
lemma IsTable.compTable_funcT {k : ℕ} (F : L.Func k) : hc.funcT F = hT₁.transT (hT₂.funcT F) := by
  ext; simp [tableFunc_compTable (hT₂.lt_len_func (codeIn_func_quote F))]

omit [L.Eq] in
lemma IsVarVec.two_bvar {m : ℕ} (a b : Fin m) :
    IsVarVec (![Semiterm.bvar a, Semiterm.bvar b] : SemitermVec V L 2 m) := fun j ↦ by
  match j with
  | 0 => exact Or.inl ⟨a, rfl⟩
  | 1 => exact Or.inl ⟨b, rfl⟩

omit [L.Eq] in
lemma IsVarVec.fvar {n : ℕ} (f : Fin n → V) :
    IsVarVec (fun i ↦ (Semiterm.fvar (f i) : Term V L)) := fun _ ↦ Or.inr ⟨_, rfl⟩

omit [L.Eq] in
lemma IsVarVec.single_bvar {m : ℕ} (a : Fin m) :
    IsVarVec (![Semiterm.bvar a] : SemitermVec V L 1 m) := fun j ↦ Or.inl ⟨a, by
  match j with
  | 0 => rfl⟩

lemma IsTable.transT_relativizedImp {k : ℕ} (d : Semiformula V L 1) (A : Fin k → Semiformula V L 1)
    (G : Semiformula V L (0 + k)) :
    hT₁.transT (relativizedImp d A G) = relAllItr hT₁.domT k (Matrix.conj (fun i : Fin k ↦
      (hT₁.transT d).subst ![Semiterm.bvar (i.addCast 0)] ⋏
        (hT₁.transT (A i)).subst ![Semiterm.bvar (i.addCast 0)]) 🡒 hT₁.transT G) := by
  unfold relativizedImp
  rw [IsTable.transT_allItr, IsTable.transT_imp, IsTable.transT_conj]
  congr 3
  funext i
  rw [IsTable.transT_and, hT₁.transT_subst _ (IsVarVec.single_bvar _),
    hT₁.transT_subst _ (IsVarVec.single_bvar _)]

lemma IsTable.comp_varEqual_val (t : Term V L) :
    (∀¹ (hT₁.domT 🡒 (varEqualT hc t 🡘 hT₁.transT (varEqualT hT₂ t)))).val =
      ^∀ imp L tbl₁.[0] (iff L (varEqual L L (Bootstrapping.compTable L L tbl₁ tbl₂) t.val)
        (translate L L tbl₁ (varEqual L L tbl₂ t.val))) := by
  simp only [Semiformula.val_all, Semiformula.val_imp, Semiformula.val_iff, varEqualT_val,
    IsTable.transT_val, IsTable.domT_val, tableDomain]

end compShapes

/-! ## Values of terms along the composite table -/

section compValue

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {S : Theory L} [S.Δ₁] [𝗘𝗤 L ⪯ S]
  {tbl₁ tbl₂ : V} (h₁ : IsTranslationTable L S tbl₁) (hT₂ : IsTable L L tbl₂)
  (hc : IsTable L L (Bootstrapping.compTable L L tbl₁ tbl₂))

lemma tprovable_comp_varEqualT_fvar (x : V) :
    S.internalize V ⊢ h₁.domT.subst ![Semiterm.fvar x] 🡒
      ∀¹ (h₁.domT 🡒 (varEqualT hc (Semiterm.fvar x) 🡘
        h₁.transT (varEqualT hT₂ (Semiterm.fvar x)))) := by
  rw [varEqualT_fvar, varEqualT_fvar]
  change S.internalize V ⊢ h₁.domT.subst ![Semiterm.fvar x] 🡒
    ∀¹ (h₁.domT 🡒 (Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x) 🡘
      h₁.transT (Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x))))
  apply TProof.generalize_imp
  rw [Semiformula.free_imp, Semiformula.free_iff, ← IsTable.transT_free]
  simp only [Semiformula.free, Semiformula.shift_substs, IsTable.domT_shift,
    Semiformula.shift_equal, Semiformula.substs_equal, Matrix.vecMap_cons', Matrix.vecMap_nil,
    Matrix.head_cons, Semiterm.shift_fvar, Semiterm.shift_bvar, Semiterm.substs_bvar,
    Semiterm.substs_fvar, Matrix.cons_val_fin_one]
  have hp := h₁.tprovable_transT_equal_iff 0 (x + 1)
  have key {A B E Q : Formula V L} (hp : S.internalize V ⊢ A 🡒 B 🡒 (E 🡘 Q)) :
      S.internalize V ⊢ B 🡒 A 🡒 (Q 🡘 E) := by
    cl_prover [hp]
  exact key hp

omit [L.Eq] [S.Δ₁] [𝗘𝗤 L ⪯ S] in
lemma IsVarVec.fvar_cons_bvar {k : ℕ} (x : V) :
    IsVarVec (Semiterm.fvar x :>
      fun i : Fin k ↦ (Semiterm.bvar (i.addCast 0) : Semiterm V L (0 + k))) := by
  intro j
  cases j using Fin.cases with
  | zero => exact Or.inr ⟨x, rfl⟩
  | succ j => exact Or.inl ⟨_, rfl⟩

omit [𝗘𝗤 L ⪯ S] in
lemma tprovable_comp_varEqualT_func {k : ℕ} (F : L.Func k) (u : Fin k → Term V L) :
    S.internalize V ⊢ Matrix.conj (fun i ↦ ∀¹ (h₁.domT 🡒 (varEqualT hc (u i) 🡘
        h₁.transT (varEqualT hT₂ (u i))))) 🡒
      ∀¹ (h₁.domT 🡒 (varEqualT hc (Semiterm.func F u) 🡘
        h₁.transT (varEqualT hT₂ (Semiterm.func F u)))) := by
  rw [varEqualT_func hc, varEqualT_func hT₂, IsTable.compTable_domT h₁.toIsTable hT₂ hc,
    IsTable.compTable_funcT h₁.toIsTable hT₂ hc]
  apply TProof.generalize_imp
  rw [Semiformula.free_imp, Semiformula.free_iff, ← IsTable.transT_free]
  have hd₂ : (h₁.transT hT₂.domT).shift = h₁.transT hT₂.domT := by
    rw [← IsTable.transT_shift, hT₂.domT_shift]
  have hg : (h₁.transT (hT₂.funcT F)).shift = h₁.transT (hT₂.funcT F) := by
    rw [← IsTable.transT_shift, hT₂.funcT_shift]
  simp only [Semiformula.free, shift_funcGraph, Semiformula.shift_and, h₁.domT_shift, hd₂, hg,
    hT₂.domT_shift, hT₂.funcT_shift, funcGraph_subst_fvar, Semiformula.shift_conj,
    Semiformula.shift_all, Semiformula.shift_imp, Semiformula.shift_iff]
  rw [IsTable.transT_relativizedImp h₁.toIsTable,
    h₁.toIsTable.transT_subst _ (IsVarVec.fvar_cons_bvar 0)]
  simp only [← IsTable.transT_shift]
  have hr := relativizedImp_iff_relAllItr (T := S) h₁.domT_shift (h₁.transT hT₂.domT)
    (fun i ↦ (varEqualT hc (u i)).shift) (fun i ↦ h₁.transT (varEqualT hT₂ (u i)).shift)
    ((h₁.transT (hT₂.funcT F)).subst (Semiterm.fvar 0 :> fun i ↦ Semiterm.bvar (i.addCast 0)))
  have key {H D X Y : Formula V L} (hr : S.internalize V ⊢ H 🡒 (X 🡘 Y)) :
      S.internalize V ⊢ H 🡒 D 🡒 (X 🡘 Y) := by
    cl_prover [hr]
  exact key hr

omit [L.Eq] [𝗘𝗤 L ⪯ S] in
lemma derivable_insert_negDomSet_mono {d a b : V} (hd : IsSemiformula L 1 d) (φ : Formula V L)
    (hab : a ≤ b) (h : Derivable S (insert φ.val (negDomSet L d a))) :
    Derivable S (insert φ.val (negDomSet L d b)) := by
  have hφ : IsFormula L φ.val := by simp
  apply Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨hφ, IsFormulaSet.negDomSet hd b⟩) _ h
  intro x hx
  rcases mem_bitInsert_iff.mp hx with rfl | hx
  · exact mem_bitInsert_iff.mpr (Or.inl rfl)
  · exact mem_bitInsert_iff.mpr (Or.inr (negDomSet_mono hab hx))

/-- Along the composite table and along the composite of the translations, the formulas saying
that a variable is the value of a term are equivalent on the domain of `tbl₁`, given the domain
of `tbl₁` at the free variables. -/
lemma derivable_comp_varEqual (hL : L.SymbolsStandard V) (t : Term V L) :
    Derivable S (insert (∀¹ (h₁.domT 🡒 (varEqualT hc t 🡘 h₁.transT (varEqualT hT₂ t)))).val
      (negDomSet L tbl₁.[0] t.val)) := by
  have hP : 𝚺ᴬ₁-Predicate fun t : V ↦ Derivable S (insert (^∀ imp L tbl₁.[0]
      (iff L (varEqual L L (Bootstrapping.compTable L L tbl₁ tbl₂) t)
        (translate L L tbl₁ (varEqual L L tbl₂ t)))) (negDomSet L tbl₁.[0] t)) := by
    definability
  have hdom : IsSemiformula L 1 tbl₁.[0] := h₁.domain.isSemiformula
  have key := IsSemiterm.sigma1_induction hP (n := 0) (fun z hz ↦ by simp at hz) ?_ ?_ t.val
    t.isSemiterm
  · rw [IsTable.comp_varEqual_val h₁.toIsTable hT₂ hc]
    exact key
  · intro x
    have h₀ := Derivable.insert_neg_of_imp <| Derivable.of_tprovable (T := S)
      (IsFormulaSet.negDomSet (L := L) hdom (^&x)) (tprovable_comp_varEqualT_fvar h₁ hT₂ hc x)
    have hmem : (∼(h₁.domT.subst ![Semiterm.fvar x]) : Formula V L).val ∈
        negDomSet L tbl₁.[0] (^&x) := by
      rw [Semiformula.val_neg, Semiformula.val_subst_fvar]
      exact mem_negDomSet_iff.mpr ⟨x, var_lt_qqFvar x, rfl⟩
    have h₂ : Derivable S (insert (∀¹ (h₁.domT 🡒 (varEqualT hc (Semiterm.fvar x) 🡘
        h₁.transT (varEqualT hT₂ (Semiterm.fvar x))))).val (negDomSet L tbl₁.[0] (^&x))) :=
      Derivable.ofSetEq (fun y ↦ by
        simp only [mem_bitInsert_iff]
        constructor
        · rintro (rfl | h)
          · exact Or.inr hmem
          · exact h
        · intro h; exact Or.inr h) h₀
    rw [IsTable.comp_varEqual_val h₁.toIsTable hT₂ hc] at h₂
    simpa using h₂
  · intro k f v hf' hv ih
    obtain ⟨k, F, u, rfl, rfl, rfl⟩ := exists_func_termVec hL (IsSemiterm.func.mpr ⟨hf', hv⟩)
    have hs := IsFormulaSet.negDomSet (L := L) hdom (Semiterm.func F u).val
    have ih' (i : Fin k) : Derivable S
        (insert (∀¹ (h₁.domT 🡒 (varEqualT hc (u i) 🡘 h₁.transT (varEqualT hT₂ (u i))))).val
          (negDomSet L tbl₁.[0] (Semiterm.func F u).val)) := by
      apply derivable_insert_negDomSet_mono hdom _ (le_of_lt ?_)
      · rw [IsTable.comp_varEqual_val h₁.toIsTable hT₂ hc]
        simpa using ih ((i : ℕ) : V) (by simp)
      · rw [Semiterm.func_val]
        simpa using nth_lt_qqFunc_of_lt (i := ((i : ℕ) : V)) (k := (k : V)) (f := (⌜F⌝ : V))
          (v := SemitermVec.val u) (by simp)
    have h₂ := Derivable.of_tprovable_imp (tprovable_comp_varEqualT_func h₁ hT₂ hc F u)
      (Derivable.conj_typed hs ih')
    rw [IsTable.comp_varEqual_val h₁.toIsTable hT₂ hc, Semiterm.func_val] at h₂
    exact h₂

end compValue

/-! ## Translations of formulas along the composite table -/

section compFormula

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {S : Theory L} [S.Δ₁] [𝗘𝗤 L ⪯ S]
  {tbl₁ tbl₂ : V} (h₁ : IsTranslationTable L S tbl₁) (hT₂ : IsTable L L tbl₂)
  (hc : IsTable L L (Bootstrapping.compTable L L tbl₁ tbl₂))

omit [L.Eq] [S.Δ₁] [𝗘𝗤 L ⪯ S] in
lemma IsVarVec.addCast_bvar {k : ℕ} :
    IsVarVec (fun i : Fin k ↦ (Semiterm.bvar (i.addCast 0) : Semiterm V L (0 + k))) :=
  fun _ ↦ Or.inl ⟨_, rfl⟩

omit [𝗘𝗤 L ⪯ S] in
lemma tprovable_comp_rel {k : ℕ} (R : L.Rel k) (u : Fin k → Term V L) :
    S.internalize V ⊢ Matrix.conj (fun i ↦ ∀¹ (h₁.domT 🡒 (varEqualT hc (u i) 🡘
        h₁.transT (varEqualT hT₂ (u i))))) 🡒
      (hc.transT (Semiformula.rel R u) 🡘 h₁.transT (hT₂.transT (Semiformula.rel R u))) := by
  have e₁ : hc.transT (Semiformula.rel R u) = relativizedImp hc.domT (fun i ↦ varEqualT hc (u i))
      ((hc.relT R).subst fun i ↦ Semiterm.bvar (i.addCast 0)) := by
    ext; exact translate_rel_typed hc R u
  have e₂ : hT₂.transT (Semiformula.rel R u) = relativizedImp hT₂.domT
      (fun i ↦ varEqualT hT₂ (u i)) ((hT₂.relT R).subst fun i ↦ Semiterm.bvar (i.addCast 0)) := by
    ext; exact translate_rel_typed hT₂ R u
  rw [e₁, e₂, IsTable.transT_relativizedImp h₁.toIsTable,
    h₁.toIsTable.transT_subst _ IsVarVec.addCast_bvar, IsTable.compTable_domT h₁.toIsTable hT₂ hc,
    IsTable.compTable_relT h₁.toIsTable hT₂ hc]
  exact relativizedImp_iff_relAllItr h₁.domT_shift (h₁.transT hT₂.domT) _ _ _

omit [𝗘𝗤 L ⪯ S] in
lemma IsTable.comp_iff_val (φ : Formula V L) :
    (hc.transT φ 🡘 h₁.transT (hT₂.transT φ)).val =
      iff L (translate L L (Bootstrapping.compTable L L tbl₁ tbl₂) φ.val)
        (translate L L tbl₁ (translate L L tbl₂ φ.val)) := by
  simp only [Semiformula.val_iff, IsTable.transT_val]

lemma derivable_comp_rel (hL : L.SymbolsStandard V) {k : ℕ} (R : L.Rel k) (u : Fin k → Term V L)
    {M : V} (hM : ∀ i, (u i).val < M) :
    Derivable S (insert (hc.transT (Semiformula.rel R u) 🡘
      h₁.transT (hT₂.transT (Semiformula.rel R u))).val (negDomSet L tbl₁.[0] M)) := by
  have hdom : IsSemiformula L 1 tbl₁.[0] := h₁.domain.isSemiformula
  have ih' (i : Fin k) := derivable_insert_negDomSet_mono hdom _ (le_of_lt (hM i))
    (derivable_comp_varEqual h₁ hT₂ hc hL (u i))
  exact Derivable.of_tprovable_imp (tprovable_comp_rel h₁ hT₂ hc R u)
    (Derivable.conj_typed (IsFormulaSet.negDomSet hdom M) ih')

omit [S.Δ₁] [𝗘𝗤 L ⪯ S] in
lemma fvSubst_freshVec_translate_free {tbl p u j : V} (hT : IsTable L L tbl)
    (hp : IsSemiformula L 1 p) (hpu : p ≤ u) (hj : u < j) :
    fvSubst L (freshVec j) (translate L L tbl (free L p)) =
      shift L (translate L L tbl (free L p)) := by
  rw [← translate_fvSubst hT (freshVec_fvar j) (IsSemiformula.free hp),
    fvSubst_freshVec_free hp hpu hj, translate_shift hT (IsSemiformula.free hp)]

omit [S.Δ₁] [𝗘𝗤 L ⪯ S] in
lemma fvSubst_freshVec_translate_translate_free {tbl tbl' p u j : V} (hT : IsTable L L tbl)
    (hT' : IsTable L L tbl') (hp : IsSemiformula L 1 p) (hpu : p ≤ u) (hj : u < j) :
    fvSubst L (freshVec j) (translate L L tbl (translate L L tbl' (free L p))) =
      shift L (translate L L tbl (translate L L tbl' (free L p))) := by
  have h₁ := IsSemiformula.translate hT' (IsSemiformula.free hp)
  rw [← translate_fvSubst hT (freshVec_fvar j) h₁, fvSubst_freshVec_translate_free hT' hp hpu hj,
    translate_shift hT h₁]

omit [L.Eq] [S.Δ₁] [𝗘𝗤 L ⪯ S] in
lemma fvSubst_iff_code {w p q : V} (hw : IsSemitermVec L (len w) 0 w) (hp : IsFormula L p)
    (hq : IsFormula L q) : fvSubst L w (iff L p q) = iff L (fvSubst L w p) (fvSubst L w q) := by
  rw [Bootstrapping.iff, fvSubst_and (by simp [hp.isUFormula, hq.isUFormula])
    (by simp [hp.isUFormula, hq.isUFormula]), fvSubst_imp hw hp hq, fvSubst_imp hw hq hp]
  rfl

omit [L.Eq] [S.Δ₁] [𝗘𝗤 L ⪯ S] in
lemma shift_iff_code {p q : V} (hp : IsFormula L p) (hq : IsFormula L q) :
    shift L (iff L p q) = iff L (shift L p) (shift L q) := by
  rw [Bootstrapping.iff, shift_and (by simp [hp.isUFormula, hq.isUFormula])
    (by simp [hp.isUFormula, hq.isUFormula]), shift_imp hp hq, shift_imp hq hp]
  rfl

omit [L.Eq] [S.Δ₁] [𝗘𝗤 L ⪯ S] in
lemma free_subst_bvar_zero {d : Semiformula V L 1} (hd : d.shift = d) :
    (d.subst ![Semiterm.bvar 0]).free = d.subst ![Semiterm.fvar 0] := by
  simp [Semiformula.free, hd]

omit [𝗘𝗤 L ⪯ S] in
lemma derivable_comp_quant (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (P : Semiformula V L 1) {M : V} (hM : P.val ≤ M)
    (ih : Derivable S (insert (hc.transT P.free 🡘 h₁.transT (hT₂.transT P.free)).val
      (negDomSet L tbl₁.[0] P.free.val))) :
    Derivable S (insert (∼(h₁.domT.subst ![Semiterm.fvar 0]) ⋎
      (hc.transT P 🡘 h₁.transT (hT₂.transT P)).free).val
        (setShift L (negDomSet L tbl₁.[0] M))) := by
  have hdom : L.IsFVFree 1 tbl₁.[0] := h₁.domain
  have hp : IsSemiformula L 1 P.val := by simp
  set Xf : Formula V L := hc.transT P.free 🡘 h₁.transT (hT₂.transT P.free) with hXf
  have hX : IsFormula L Xf.val := by simp
  have h₁' : Derivable S (insert Xf.val
      (negDomSet L tbl₁.[0] (P.free.val + (M + 1)))) :=
    derivable_insert_negDomSet_mono hdom.isSemiformula Xf (le_add_right le_rfl) ih
  have h₂ : Derivable S (insert Xf.val ∅ ∪ negDomSet L tbl₁.[0] (P.free.val + (M + 1))) :=
    Derivable.ofSetEq (fun x ↦ by simp) h₁'
  have hfresh : ∀ j, M + 1 ≤ j → j < P.free.val + (M + 1) →
      fvSubstImage (L := L) (freshVec j) (insert Xf.val ∅) = setShift L (insert Xf.val ∅) := by
    intro j hj _
    have hj' : M < j := lt_of_lt_of_le (lt_add_one _) hj
    rw [fvSubstImage_insert, fvSubstImage_empty, mem_setShift_insert, setShift_empty]
    congr 1
    have ha := IsSemiformula.translate hc (IsSemiformula.free hp)
    have hb := IsSemiformula.translate h₁.toIsTable
      (IsSemiformula.translate hT₂ (IsSemiformula.free hp))
    rw [hXf, Semiformula.val_iff, IsTable.transT_val, IsTable.transT_val, IsTable.transT_val,
      Semiformula.free_val, fvSubst_iff_code (isSemitermVec_freshVec j) ha hb,
      fvSubst_freshVec_translate_free hc hp hM hj',
      fvSubst_freshVec_translate_translate_free h₁.toIsTable hT₂ hp hM hj', shift_iff_code ha hb]
  have h₃ := Derivable.elim_negDomSet hS hdom h₁.exs_domain
    (by simp) (le_add_left le_rfl) hfresh h₂
  rw [negDomSet_succ_eq_insert_setShift hdom] at h₃
  have hnd : IsFormula L (neg L (substs1 L (^&0) tbl₁.[0])) :=
    (IsSemiformula.substs1 (n := 0) (by simp) hdom.isSemiformula).neg
  have h₄ : Derivable S (insert (neg L (substs1 L (^&0) tbl₁.[0])) (insert Xf.val
      (setShift L (negDomSet L tbl₁.[0] M)))) :=
    Derivable.ofSetEq (fun x ↦ by simp; tauto) h₃
  have h₅ := derivable_insert_or
    (IsFormulaSet.setShift (IsFormulaSet.negDomSet hdom.isSemiformula _)) hnd hX h₄
  have e : (∼(h₁.domT.subst ![Semiterm.fvar 0]) ⋎
      (hc.transT P 🡘 h₁.transT (hT₂.transT P)).free).val =
        neg L (substs1 L (^&0) tbl₁.[0]) ^⋎ Xf.val := by
    rw [hXf, Semiformula.free_iff, ← IsTable.transT_free, ← IsTable.transT_free,
      ← IsTable.transT_free, Semiformula.val_or, Semiformula.val_neg, Semiformula.val_subst_fvar]
    rfl
  rw [e]
  exact h₅

omit [𝗘𝗤 L ⪯ S] in
lemma derivable_comp_all (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (P : Semiformula V L 1)
    (ih : Derivable S (insert (hc.transT P.free 🡘 h₁.transT (hT₂.transT P.free)).val
      (negDomSet L tbl₁.[0] P.free.val))) :
    Derivable S (insert (hc.transT (∀¹ P) 🡘 h₁.transT (hT₂.transT (∀¹ P))).val
      (negDomSet L tbl₁.[0] (∀¹ P).val)) := by
  have h₀ := derivable_comp_quant h₁ hT₂ hc hS P (M := (∀¹ P).val)
    (by simpa using (lt_forall P.val).le) ih
  have hd₂ : (h₁.transT hT₂.domT).shift = h₁.transT hT₂.domT := by
    rw [← IsTable.transT_shift, hT₂.domT_shift]
  have key : S.internalize V ⊢ ∼(h₁.domT.subst ![Semiterm.fvar 0]) ⋎
      (hc.transT P 🡘 h₁.transT (hT₂.transT P)).free 🡒
        ((hc.domT.subst ![Semiterm.bvar 0] 🡒 hc.transT P) 🡘
          (h₁.domT.subst ![Semiterm.bvar 0] 🡒 ((h₁.transT hT₂.domT).subst ![Semiterm.bvar 0] 🡒
            h₁.transT (hT₂.transT P)))).free := by
    simp only [Semiformula.free_iff, Semiformula.free_imp]
    rw [free_subst_bvar_zero hc.domT_shift, free_subst_bvar_zero h₁.domT_shift,
      free_subst_bvar_zero hd₂, IsTable.compTable_domT h₁.toIsTable hT₂ hc, Semiformula.substs_and]
    cl_prover
  have h₁' := Derivable.of_tprovable_imp key h₀
  rw [Semiformula.free_val] at h₁'
  have hP1 : IsSemiformula L 1 P.val := by simp
  have h₂ := Derivable.all (by
    simp [hc.domain.isSemiformula, h₁.domain.isSemiformula, IsSemiformula.translate hc hP1,
      IsSemiformula.translate h₁.toIsTable hT₂.domain.isSemiformula,
      IsSemiformula.translate h₁.toIsTable (IsSemiformula.translate hT₂ hP1)]) h₁'
  rw [← Semiformula.val_all] at h₂
  have h₃ := Derivable.of_tprovable_imp (tprovable_all_iff_all _ _) h₂
  simp only [IsTable.transT_all, IsTable.transT_imp,
    h₁.toIsTable.transT_subst _ (IsVarVec.single_bvar _)]
  exact h₃

omit [𝗘𝗤 L ⪯ S] in
lemma derivable_comp_exs (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (P : Semiformula V L 1)
    (ih : Derivable S (insert (hc.transT P.free 🡘 h₁.transT (hT₂.transT P.free)).val
      (negDomSet L tbl₁.[0] P.free.val))) :
    Derivable S (insert (hc.transT (∃¹ P) 🡘 h₁.transT (hT₂.transT (∃¹ P))).val
      (negDomSet L tbl₁.[0] (∃¹ P).val)) := by
  have h₀ := derivable_comp_quant h₁ hT₂ hc hS P (M := (∃¹ P).val)
    (by simpa using (lt_exists P.val).le) ih
  have hd₂ : (h₁.transT hT₂.domT).shift = h₁.transT hT₂.domT := by
    rw [← IsTable.transT_shift, hT₂.domT_shift]
  have key : S.internalize V ⊢ ∼(h₁.domT.subst ![Semiterm.fvar 0]) ⋎
      (hc.transT P 🡘 h₁.transT (hT₂.transT P)).free 🡒
        ((hc.domT.subst ![Semiterm.bvar 0] ⋏ hc.transT P) 🡘
          (h₁.domT.subst ![Semiterm.bvar 0] ⋏ ((h₁.transT hT₂.domT).subst ![Semiterm.bvar 0] ⋏
            h₁.transT (hT₂.transT P)))).free := by
    simp only [Semiformula.free_iff, Semiformula.free_and]
    rw [free_subst_bvar_zero hc.domT_shift, free_subst_bvar_zero h₁.domT_shift,
      free_subst_bvar_zero hd₂, IsTable.compTable_domT h₁.toIsTable hT₂ hc, Semiformula.substs_and]
    cl_prover
  have h₁' := Derivable.of_tprovable_imp key h₀
  rw [Semiformula.free_val] at h₁'
  have hP1 : IsSemiformula L 1 P.val := by simp
  have h₂ := Derivable.all (by
    simp [hc.domain.isSemiformula, h₁.domain.isSemiformula, IsSemiformula.translate hc hP1,
      IsSemiformula.translate h₁.toIsTable hT₂.domain.isSemiformula,
      IsSemiformula.translate h₁.toIsTable (IsSemiformula.translate hT₂ hP1)]) h₁'
  rw [← Semiformula.val_all] at h₂
  have h₃ := Derivable.of_tprovable_imp (tprovable_all_iff_exs _ _) h₂
  simp only [IsTable.transT_exs, IsTable.transT_and,
    h₁.toIsTable.transT_subst _ (IsVarVec.single_bvar _)]
  exact h₃

include h₁ hT₂ hc in
/-- Along the composite table and along the composite of the translations, every formula code
has equivalent translations, given the domain of `tbl₁` at its free variables. -/
theorem derivable_comp_translate (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hL : L.SymbolsStandard V) {p : V} (hp : IsFormula L p) :
    Derivable S (insert (iff L (translate L L (Bootstrapping.compTable L L tbl₁ tbl₂) p)
      (translate L L tbl₁ (translate L L tbl₂ p))) (negDomSet L tbl₁.[0] p)) := by
  have hdom : IsSemiformula L 1 tbl₁.[0] := h₁.domain.isSemiformula
  have hs (M : V) := IsFormulaSet.negDomSet (L := L) hdom M
  have hv := IsTable.comp_iff_val h₁ hT₂ hc
  apply IsFormula.sigma1_structural_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro k r v hR hv'
    obtain ⟨k, R, rfl, rfl⟩ := hL.1 _ _ hR
    obtain ⟨u, rfl⟩ := exists_termVec hv'
    have h := derivable_comp_rel h₁ hT₂ hc hL R u (M := (Semiformula.rel R u : Formula V L).val)
      (fun i ↦ by
        rw [Semiformula.rel_val, ← SemitermVec.val_nth_eq]
        exact lt_trans (nth_lt_self (by simp)) (v_lt_rel _ _ _))
    rw [hv, Semiformula.rel_val] at h
    exact h
  · intro k r v hR hv'
    obtain ⟨k, R, rfl, rfl⟩ := hL.1 _ _ hR
    obtain ⟨u, rfl⟩ := exists_termVec hv'
    have h := derivable_comp_rel h₁ hT₂ hc hL R u (M := (Semiformula.nrel R u : Formula V L).val)
      (fun i ↦ by
        rw [Semiformula.nrel_val, ← SemitermVec.val_nth_eq]
        exact lt_trans (nth_lt_self (by simp)) (v_lt_nrel _ _ _))
    have key {A B : Formula V L} : S.internalize V ⊢ (A 🡘 B) 🡒 (∼A 🡘 ∼B) := by cl_prover
    have h' := Derivable.of_tprovable_imp key h
    rw [← IsTable.transT_neg, ← IsTable.transT_neg, ← IsTable.transT_neg, hv,
      Semiformula.neg_rel, Semiformula.nrel_val] at h'
    exact h'
  · have h := Derivable.of_tprovable (hs ^⊤) (show S.internalize V ⊢
      hc.transT (⊤ : Formula V L) 🡘 h₁.transT (hT₂.transT ⊤) by
        simp only [IsTable.transT_verum]; cl_prover)
    rw [hv] at h
    simpa using h
  · have h := Derivable.of_tprovable (hs ^⊥) (show S.internalize V ⊢
      hc.transT (⊥ : Formula V L) 🡘 h₁.transT (hT₂.transT ⊥) by
        simp only [IsTable.transT_falsum]; cl_prover)
    rw [hv] at h
    simpa using h
  · intro p q hp hq ihp ihq
    let P : Formula V L := ⟨p, by simpa using hp⟩
    let Q : Formula V L := ⟨q, by simpa using hq⟩
    have hP := derivable_insert_negDomSet_mono hdom _ (le_of_lt (lt_K!_left p q))
      (show Derivable S (insert (hc.transT P 🡘 h₁.transT (hT₂.transT P)).val _) by
        rw [hv]; exact ihp)
    have hQ := derivable_insert_negDomSet_mono hdom _ (le_of_lt (lt_K!_right p q))
      (show Derivable S (insert (hc.transT Q 🡘 h₁.transT (hT₂.transT Q)).val _) by
        rw [hv]; exact ihq)
    have h := Derivable.of_tprovable_imp₂ (show S.internalize V ⊢
      (hc.transT P 🡘 h₁.transT (hT₂.transT P)) 🡒 (hc.transT Q 🡘 h₁.transT (hT₂.transT Q)) 🡒
        (hc.transT (P ⋏ Q) 🡘 h₁.transT (hT₂.transT (P ⋏ Q))) by
          simp only [IsTable.transT_and]; cl_prover) hP hQ
    rw [hv] at h
    exact h
  · intro p q hp hq ihp ihq
    let P : Formula V L := ⟨p, by simpa using hp⟩
    let Q : Formula V L := ⟨q, by simpa using hq⟩
    have hP := derivable_insert_negDomSet_mono hdom _ (le_of_lt (lt_or_left p q))
      (show Derivable S (insert (hc.transT P 🡘 h₁.transT (hT₂.transT P)).val _) by
        rw [hv]; exact ihp)
    have hQ := derivable_insert_negDomSet_mono hdom _ (le_of_lt (lt_or_right p q))
      (show Derivable S (insert (hc.transT Q 🡘 h₁.transT (hT₂.transT Q)).val _) by
        rw [hv]; exact ihq)
    have h := Derivable.of_tprovable_imp₂ (show S.internalize V ⊢
      (hc.transT P 🡘 h₁.transT (hT₂.transT P)) 🡒 (hc.transT Q 🡘 h₁.transT (hT₂.transT Q)) 🡒
        (hc.transT (P ⋎ Q) 🡘 h₁.transT (hT₂.transT (P ⋎ Q))) by
          simp only [IsTable.transT_or]; cl_prover) hP hQ
    rw [hv] at h
    exact h
  · intro p hp ih
    let P : Semiformula V L 1 := ⟨p, by simpa using hp⟩
    have h := derivable_comp_all h₁ hT₂ hc hS P (by rw [hv, Semiformula.free_val]; exact ih)
    rw [hv] at h
    exact h
  · intro p hp ih
    let P : Semiformula V L 1 := ⟨p, by simpa using hp⟩
    have h := derivable_comp_exs h₁ hT₂ hc hS P (by rw [hv, Semiformula.free_val]; exact ih)
    rw [hv] at h
    exact h

include h₁ hT₂ hc in
/-- Along the composite table and along the composite of the translations, every formula code
without free variables has provably equivalent translations. -/
theorem provable_comp_translate_iff (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hL : L.SymbolsStandard V) {p : V} (hp : L.IsFVFree 0 p) :
    Provable S (iff L (translate L L (Bootstrapping.compTable L L tbl₁ tbl₂) p)
      (translate L L tbl₁ (translate L L tbl₂ p))) := by
  have hp' := hp.isSemiformula
  have ha := IsSemiformula.translate hc hp'
  have hb := IsSemiformula.translate h₁.toIsTable (IsSemiformula.translate hT₂ hp')
  have h₀ := derivable_comp_translate h₁ hT₂ hc hS hL hp'
  set X := iff L (translate L L (Bootstrapping.compTable L L tbl₁ tbl₂) p)
    (translate L L tbl₁ (translate L L tbl₂ p)) with hXdef
  have hX : IsFormula L X := by simp [hXdef, ha, hb]
  have hXs : shift L X = X := by
    rw [hXdef, shift_iff_code ha hb, ← translate_shift hc hp',
      ← translate_shift h₁.toIsTable (IsSemiformula.translate hT₂ hp'), ← translate_shift hT₂ hp',
      hp.shift_eq]
  have h₂ : Derivable S (insert X ∅ ∪ negDomSet L tbl₁.[0] p) :=
    Derivable.ofSetEq (fun x ↦ by simp) h₀
  have hfresh : ∀ j, 0 ≤ j → j < p →
      fvSubstImage (L := L) (freshVec j) (insert X ∅) = setShift L (insert X ∅) := by
    intro j _ _
    rw [fvSubstImage_insert, fvSubstImage_empty, mem_setShift_insert, setShift_empty,
      Language.IsFVFree.fvSubst_eq_self ⟨hX, hXs⟩, hXs]
  have h₃ := Derivable.elim_negDomSet hS h₁.domain h₁.exs_domain (by simp [hX]) zero_le hfresh h₂
  rw [negDomSet_zero] at h₃
  exact internal_provable_iff_internal_derivable.mpr (Derivable.ofSetEq (fun x ↦ by simp) h₃)

end compFormula

/-! ## The conditions on the composite table -/

section generalizeFvar

variable {L : Language} [L.Encodable] [L.LORDefinable] {S : Theory L} [S.Δ₁]

lemma provable_qqAlls_of_tprovable_fvar : ∀ {n : ℕ} (φ : Semiformula V L n), φ.shift = φ →
    S.internalize V ⊢ φ.subst (fun i ↦ Semiterm.fvar ((i : ℕ) : V)) → Provable S (qqAlls φ.val n)
  | 0, φ, _, h => by
    rw [Semiformula.subst_nil_eq_self] at h
    simpa using tprovable_iff_provable.mp h
  | n + 1, φ, hφ, h => by
    have h₁ := provable_qqAlls_of_tprovable_fvar (∀¹ φ) (by rw [Semiformula.shift_all, hφ]) (by
      rw [Semiformula.substs_all]
      apply TProof.all!
      rw [free_subst_q_fvar', hφ]
      exact h)
    simpa [qqAlls_all] using h₁

lemma tprovable_conj_and_split {k : ℕ} (a b : Fin k → Formula V L) :
    S.internalize V ⊢ Matrix.conj (fun i ↦ a i ⋏ b i) 🡒 Matrix.conj a ⋏ Matrix.conj b := by
  have h₁ := matrixConj_imp_matrixConj (𝓢 := S.internalize V) (φ := ⊤)
    (v := fun i ↦ a i ⋏ b i) (u := a) fun i ↦ by cl_prover
  have h₂ := matrixConj_imp_matrixConj (𝓢 := S.internalize V) (φ := ⊤)
    (v := fun i ↦ a i ⋏ b i) (u := b) fun i ↦ by cl_prover
  cl_prover [h₁, h₂]

lemma tprovable_exs_and_assoc (A B G : Semiformula V L 1) :
    S.internalize V ⊢ ∃¹ (A ⋏ (B ⋏ G)) 🡒 ∃¹ ((A ⋏ B) ⋏ G) := by
  have h : S.internalize V ⊢ ∀¹ ((A ⋏ (B ⋏ G)) 🡘 ((A ⋏ B) ⋏ G)) := by
    apply TProof.all!
    rw [Semiformula.free_iff, Semiformula.free_and, Semiformula.free_and, Semiformula.free_and,
      Semiformula.free_and]
    cl_prover
  exact K_left (tprovable_all_iff_exs _ _ ⨀ h)

lemma tprovable_conj_succ_succ {k : ℕ} (f : Fin (k + 2) → Formula V L) :
    S.internalize V ⊢ Matrix.conj (fun i : Fin k ↦ f i.succ.succ) ⋏ f 0 ⋏ f 1 🡒 Matrix.conj f := by
  apply matrixConj_intro
  intro i
  cases i using Fin.cases with
  | zero => cl_prover
  | succ i =>
    cases i using Fin.cases with
    | zero => cl_prover
    | succ i =>
      have := matrixConj_elim (𝓢 := S.internalize V) (fun i : Fin k ↦ f i.succ.succ) i
      cl_prover [this]

end generalizeFvar

section leibniz

open Arithmetic

variable {S : ArithmeticTheory} [S.Δ₁] [𝗘𝗤 ℒₒᵣ ⪯ S]

omit [S.Δ₁] [𝗘𝗤 ℒₒᵣ ⪯ S] in
lemma Semiterm.subst_closed (t : Term V ℒₒᵣ) (w : SemitermVec V ℒₒᵣ 0 0) : t.subst w = t := by
  ext
  rw [Semiterm.val_substs]
  exact termSubst_eq_self t.isSemiterm (by simp)

/-- Equal arguments may be replaced in any formula. -/
lemma tprovable_subst_congr : ∀ {m : ℕ} (γ : Semiformula V ℒₒᵣ m) (s t : Fin m → Term V ℒₒᵣ),
    S.internalize V ⊢ Matrix.conj (fun i ↦ Semiformula.equal (s i) (t i)) 🡒
      γ.subst s 🡒 γ.subst t
  | 0, γ, s, t => by
    rw [show s = t from funext fun i ↦ i.elim0]
    cl_prover
  | m + 1, γ, s, t => by
    let φ₀ : Semiformula V ℒₒᵣ 1 :=
      γ.subst (Semiterm.bvar 0 :> fun i ↦ ((s i.succ).subst ![] : Semiterm V ℒₒᵣ 1))
    have e₀ (u : Term V ℒₒᵣ) : φ₀.subst ![u] = γ.subst (u :> fun i ↦ s i.succ) := by
      simp only [φ₀, Semiformula.substs_substs]
      congr 1
      funext j
      cases j using Fin.cases with
      | zero => simp
      | succ j => simp [Semiterm.subst_nil_subst, Semiterm.subst_closed]
    let γ' : Semiformula V ℒₒᵣ m := γ.subst (((t 0).subst ![] : Semiterm V ℒₒᵣ m) :> Semiterm.bvar)
    have e₁ (v : Fin m → Term V ℒₒᵣ) : γ'.subst v = γ.subst (t 0 :> v) := by
      simp only [γ', Semiformula.substs_substs]
      congr 1
      funext j
      cases j using Fin.cases with
      | zero => simp [Semiterm.subst_nil_subst, Semiterm.subst_closed]
      | succ j => simp
    have h₁ := Arithmetic.replace S φ₀ (s 0) (t 0)
    rw [e₀, e₀, show (s 0 :> fun i ↦ s i.succ) = s from Matrix.cons_head_tail s] at h₁
    have h₂ := tprovable_subst_congr γ' (fun i ↦ s i.succ) (fun i ↦ t i.succ)
    rw [e₁, e₁, show (t 0 :> fun i ↦ t i.succ) = t from Matrix.cons_head_tail t] at h₂
    have eqv : Semiformula.equal (s 0) (t 0) = (s 0 ≐ t 0) := by simp [Semiformula.equal]
    simp only [Matrix.conj, eqv]
    have key {E C A B D : Formula V ℒₒᵣ} (h₁ : S.internalize V ⊢ E 🡒 A 🡒 B)
        (h₂ : S.internalize V ⊢ C 🡒 B 🡒 D) : S.internalize V ⊢ E ⋏ C 🡒 A 🡒 D := by
      cl_prover [h₁, h₂]
    exact key h₁ h₂

end leibniz

section compConditions

variable {S U : ArithmeticTheory} [S.Δ₁] [U.Δ₁] [𝗘𝗤 ℒₒᵣ ⪯ S] {tbl₁ tbl₂ : V}
  (h₁ : IsTranslationTable ℒₒᵣ S tbl₁) (h₂ : IsTranslationTable ℒₒᵣ U tbl₂)
  (hc : IsTable ℒₒᵣ ℒₒᵣ (Bootstrapping.compTable ℒₒᵣ ℒₒᵣ tbl₁ tbl₂))
  (hsound : ∀ φ : V, shift ℒₒᵣ φ = φ → Provable U φ →
    Provable S (translate ℒₒᵣ ℒₒᵣ tbl₁ φ))

omit [𝗘𝗤 ℒₒᵣ ⪯ S] in
include h₁ h₂ hsound in
lemma comp_exs_domain :
    Provable S (^∃ tableDomain (Bootstrapping.compTable ℒₒᵣ ℒₒᵣ tbl₁ tbl₂)) := by
  have hs : shift ℒₒᵣ (^∃ tableDomain tbl₂) = ^∃ tableDomain tbl₂ := by
    simp [h₂.domain.isSemiformula.isUFormula, h₂.domain.shift_eq]
  have h := hsound _ hs h₂.exs_domain
  rwa [translate_exs h₂.domain.isSemiformula.isUFormula, domainAt_zero h₁.toIsTable, ← tableDomain,
    ← tableDomain_compTable] at h

omit [𝗘𝗤 ℒₒᵣ ⪯ S] in
include h₁ hsound in
/-- `τ₁` applied to a block of universal quantifiers provable in `U` yields the block relativized
to the domain of `tbl₁`, provable in `S`. -/
lemma tprovable_relAllItr_of_provable {k : ℕ} (φ : Semiformula V ℒₒᵣ (0 + k)) (hφ : φ.shift = φ)
    (h : Provable U (∀¹^[k] φ).val) :
    S.internalize V ⊢ relAllItr h₁.domT k (h₁.transT φ) := by
  have hs : shift ℒₒᵣ (∀¹^[k] φ).val = (∀¹^[k] φ).val := by
    rw [← Semiformula.val_shift, Semiformula.shift_allItr, hφ]
  have h' := hsound _ hs h
  rw [← IsTable.transT_val h₁.toIsTable, IsTable.transT_allItr] at h'
  exact tprovable_iff_provable.mpr h'

omit [𝗘𝗤 ℒₒᵣ ⪯ S] in
lemma conj_two_fvar (d : Semiformula V ℒₒᵣ 1) :
    S.internalize V ⊢ d.subst ![Semiterm.fvar 0] ⋏ d.subst ![Semiterm.fvar 1] 🡒
      Matrix.conj (fun i : Fin (0 + 2) ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) := by
  apply matrixConj_intro
  intro i
  match i with
  | 0 => simp
  | 1 => simp

omit [U.Δ₁] in
include h₁ in
lemma tprovable_comp_preserveEqBody (d : Semiformula V ℒₒᵣ 1) (E : Semiformula V ℒₒᵣ 2)
    (hb : S.internalize V ⊢ relAllItr h₁.domT 2 (h₁.transT (preserveEqBody d E))) :
    S.internalize V ⊢ (preserveEqBody (h₁.domT ⋏ h₁.transT d) (h₁.transT E)).subst
      (fun i ↦ Semiterm.fvar ((i : ℕ) : V)) := by
  have hs := relAllItr_specialize (T := S) (k := 2) h₁.domT (h₁.transT (preserveEqBody d E))
    (fun i ↦ Semiterm.fvar ((i : ℕ) : V)) ⨀ hb
  simp only [preserveEqBody, IsTable.transT_imp, IsTable.transT_iff,
    h₁.toIsTable.transT_subst _ (IsVarVec.single_bvar _),
    h₁.toIsTable.transT_subst _ (IsVarVec.two_bvar _ _)] at hs ⊢
  simp only [LogicalConnective.iff, Semiformula.substs_imp, Semiformula.substs_and,
    Semiformula.substs_substs, Semiformula.substs_equal, Matrix.vecMap_cons', Matrix.vecMap_nil,
    Matrix.head_cons, Semiterm.substs_bvar] at hs ⊢
  rw [← h₁.toIsTable.transT_subst _ (IsVarVec.fvar _), Semiformula.substs_equal,
    Semiterm.substs_bvar, Semiterm.substs_bvar] at hs
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one] at hs ⊢
  have hp := h₁.tprovable_transT_equal_iff ((1 : ℕ) : V) ((0 : ℕ) : V)
  simp only [LogicalConnective.iff, Nat.cast_zero, Nat.cast_one] at hp
  have hcj := conj_two_fvar (S := S) h₁.domT
  have key {C D0 D1 E0 E1 X T Q : Formula V ℒₒᵣ}
      (hs : S.internalize V ⊢ C 🡒 E1 🡒 E0 🡒 (X 🡒 T) ⋏ (T 🡒 X))
      (hcj : S.internalize V ⊢ D0 ⋏ D1 🡒 C)
      (hp : S.internalize V ⊢ D1 🡒 D0 🡒 (T 🡒 Q) ⋏ (Q 🡒 T)) :
      S.internalize V ⊢ D1 ⋏ E1 🡒 D0 ⋏ E0 🡒 (X 🡒 Q) ⋏ (Q 🡒 X) := by
    have h₄ := C_trans hcj hs
    cl_prover 100 [h₄, hp]
  exact key hs hcj hp

include h₁ h₂ hc hsound in
lemma comp_preserve_eq :
    Provable S (qqAlls (preserveEqCode ℒₒᵣ ℒₒᵣ (Bootstrapping.compTable ℒₒᵣ ℒₒᵣ tbl₁ tbl₂)) 2) := by
  have hb := tprovable_relAllItr_of_provable h₁ hsound (k := 2)
    (preserveEqBody h₂.domT (h₂.relT (Language.Eq.eq : (ℒₒᵣ).Rel 2)))
    (preserveEqBody_shift h₂.domT_shift (h₂.relT_shift _))
    (by rw [val_allItr, preserveEqBody_val _ rfl _ rfl]; simpa using h₂.preserve_eq)
  rw [← preserveEqBody_val hc.domT rfl (hc.relT (Language.Eq.eq : (ℒₒᵣ).Rel 2)) rfl]
  apply provable_qqAlls_of_tprovable_fvar _ (preserveEqBody_shift hc.domT_shift (hc.relT_shift _))
  rw [IsTable.compTable_domT h₁.toIsTable h₂.toIsTable hc,
    IsTable.compTable_relT h₁.toIsTable h₂.toIsTable hc]
  exact tprovable_comp_preserveEqBody h₁ _ _ hb

omit [𝗘𝗤 ℒₒᵣ ⪯ S] in
include h₁ hsound in
lemma tprovable_relAlls_of_provable {n : ℕ} (φ : Semiformula V ℒₒᵣ n) (hφ : φ.shift = φ)
    (h : Provable U (qqAlls φ.val n)) : S.internalize V ⊢ relAlls h₁.domT (h₁.transT φ) := by
  have hs : shift ℒₒᵣ (qqAlls φ.val n) = qqAlls φ.val n := by
    rw [shift_qqAlls φ.isSemiformula.isUFormula, ← Semiformula.val_shift, hφ]
  have h' := hsound _ hs h
  rw [IsTable.translate_qqAlls h₁.toIsTable] at h'
  exact tprovable_iff_provable.mpr h'

omit [S.Δ₁] [U.Δ₁] [𝗘𝗤 ℒₒᵣ ⪯ S] in
lemma IsVarVec.bvar_cons_succ {k : ℕ} :
    IsVarVec (Semiterm.bvar 0 :>
      fun i : Fin k ↦ (Semiterm.bvar i.succ : Semiterm V ℒₒᵣ (k + 1))) := by
  intro j
  cases j using Fin.cases with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ j => exact Or.inl ⟨_, rfl⟩

omit [𝗘𝗤 ℒₒᵣ ⪯ S] in
include h₁ h₂ hc hsound in
lemma comp_func_exists {k : ℕ} (F : (ℒₒᵣ).Func k) :
    Provable S (qqAlls (funcExistsCode ℒₒᵣ (Bootstrapping.compTable ℒₒᵣ ℒₒᵣ tbl₁ tbl₂) k ⌜F⌝)
      k) := by
  have hb := tprovable_relAlls_of_provable h₁ hsound (funcExistsBody h₂.domT (h₂.funcT F))
    (funcExistsBody_shift h₂.domT_shift (h₂.funcT_shift F))
    (by rw [funcExistsBody_val _ rfl _ rfl]; exact h₂.func_exists (codeIn_func_quote F))
  rw [← funcExistsBody_val hc.domT rfl (hc.funcT F) rfl]
  apply provable_qqAlls_of_forall_tprovable _
    (funcExistsBody_shift hc.domT_shift (hc.funcT_shift F))
  intro w
  have hs := relAlls_specialize (T := S) h₁.domT _ w ⨀ hb
  rw [IsTable.compTable_domT h₁.toIsTable h₂.toIsTable hc,
    IsTable.compTable_funcT h₁.toIsTable h₂.toIsTable hc]
  simp only [funcExistsBody, IsTable.transT_imp, IsTable.transT_conj, IsTable.transT_exs,
    IsTable.transT_and, h₁.toIsTable.transT_subst _ (IsVarVec.single_bvar _),
    h₁.toIsTable.transT_subst _ IsVarVec.bvar_cons_succ] at hs ⊢
  simp only [Semiformula.substs_imp, Semiformula.substs_conj, Semiformula.substs_and,
    Semiformula.substs_ex, Semiformula.substs_substs, Matrix.vecMap_cons', Matrix.head_cons,
    Matrix.vecMap_nil, Semiterm.substs_bvar] at hs ⊢
  have key {CA CB CAB EX EY : Formula V ℒₒᵣ} (hs : S.internalize V ⊢ CA 🡒 CB 🡒 EX)
      (hsp : S.internalize V ⊢ CAB 🡒 CA ⋏ CB) (h₃ : S.internalize V ⊢ EX 🡒 EY) :
      S.internalize V ⊢ CAB 🡒 EY := by
    cl_prover [hs, hsp, h₃]
  exact key hs (tprovable_conj_and_split _ _) (tprovable_exs_and_assoc _ _ _)

omit [U.Δ₁] in
include hc in
lemma comp_func_congr {k : ℕ} (F : (ℒₒᵣ).Func k) :
    Provable S (qqAlls (funcCongrCode ℒₒᵣ (Bootstrapping.compTable ℒₒᵣ ℒₒᵣ tbl₁ tbl₂) k ⌜F⌝)
      (k + 1 + (k + 1))) := by
  have h := provable_qqAlls_of_forall_tprovable (S := S) (funcCongrBody (hc.funcT F))
    (funcCongrBody_shift (hc.funcT_shift F)) fun w ↦ by
      simp only [funcCongrBody, Semiformula.substs_imp, Semiformula.substs_conj,
        Semiformula.substs_equal, Semiformula.substs_substs, Semiterm.substs_bvar,
        Semiterm.substs_vecMap_bvar]
      exact tprovable_subst_congr (hc.funcT F) (fun j ↦ w (Fin.castAdd (k + 1) j))
        (fun j ↦ w (Fin.natAdd (k + 1) j))
  rw [funcCongrBody_val _ rfl] at h
  simpa using h

omit [S.Δ₁] [U.Δ₁] [𝗘𝗤 ℒₒᵣ ⪯ S] in
lemma IsVarVec.bvar_cons_succ_succ {k : ℕ} (a : Fin (k + 2)) :
    IsVarVec (Semiterm.bvar a :>
      fun i : Fin k ↦ (Semiterm.bvar i.succ.succ : Semiterm V ℒₒᵣ (k + 2))) := by
  intro j
  cases j using Fin.cases with
  | zero => exact Or.inl ⟨a, rfl⟩
  | succ j => exact Or.inl ⟨_, rfl⟩

omit [U.Δ₁] in
include h₁ in
lemma tprovable_comp_funcUniqueBody {k : ℕ} (d : Semiformula V ℒₒᵣ 1)
    (γ : Semiformula V ℒₒᵣ (k + 1))
    (hb : S.internalize V ⊢ relAlls h₁.domT (h₁.transT (funcUniqueBody d γ))) :
    S.internalize V ⊢ (funcUniqueBody (h₁.domT ⋏ h₁.transT d) (h₁.transT γ)).subst
      (fun i ↦ Semiterm.fvar ((i : ℕ) : V)) := by
  have hs := relAlls_specialize (T := S) h₁.domT _ (fun i ↦ Semiterm.fvar ((i : ℕ) : V)) ⨀ hb
  have hcj := tprovable_conj_succ_succ (S := S)
    (fun i : Fin (k + 2) ↦ h₁.domT.subst ![Semiterm.fvar ((i : ℕ) : V)])
  simp only [funcUniqueBody, IsTable.transT_imp, IsTable.transT_and, IsTable.transT_conj,
    h₁.toIsTable.transT_subst _ (IsVarVec.single_bvar _),
    h₁.toIsTable.transT_subst _ (IsVarVec.bvar_cons_succ_succ _)] at hs ⊢
  simp only [Semiformula.substs_imp, Semiformula.substs_and, Semiformula.substs_conj,
    Semiformula.substs_substs, Semiformula.substs_equal, Matrix.vecMap_cons', Matrix.vecMap_nil,
    Matrix.head_cons, Semiterm.substs_bvar] at hs ⊢
  rw [← h₁.toIsTable.transT_subst _ (IsVarVec.fvar _), Semiformula.substs_equal,
    Semiterm.substs_bvar, Semiterm.substs_bvar] at hs
  have hp := h₁.tprovable_transT_equal_iff (((0 : Fin (k + 2)) : ℕ) : V)
    (((1 : Fin (k + 2)) : ℕ) : V)
  have key {CK CD CE CDE D0 D1 E0 E1 G0 G1 T Q : Formula V ℒₒᵣ}
      (hs : S.internalize V ⊢ CK 🡒 CE ⋏ E0 ⋏ E1 ⋏ G0 ⋏ G1 🡒 T)
      (hcj : S.internalize V ⊢ CD ⋏ D0 ⋏ D1 🡒 CK) (hsp : S.internalize V ⊢ CDE 🡒 CD ⋏ CE)
      (hp : S.internalize V ⊢ D0 🡒 D1 🡒 (T 🡘 Q)) :
      S.internalize V ⊢ CDE ⋏ (D0 ⋏ E0) ⋏ (D1 ⋏ E1) ⋏ G0 ⋏ G1 🡒 Q := by
    have h₄ := C_trans hcj hs
    cl_prover 100 [h₄, hsp, hp]
  exact key hs hcj (tprovable_conj_and_split _ _) hp


include h₁ h₂ hc hsound in
lemma comp_func_unique {k : ℕ} (F : (ℒₒᵣ).Func k) :
    Provable S (qqAlls (funcUniqueCode ℒₒᵣ (Bootstrapping.compTable ℒₒᵣ ℒₒᵣ tbl₁ tbl₂) k ⌜F⌝)
      (k + 2)) := by
  have hb := tprovable_relAlls_of_provable h₁ hsound (funcUniqueBody h₂.domT (h₂.funcT F))
    (funcUniqueBody_shift h₂.domT_shift (h₂.funcT_shift F)) (by
      rw [funcUniqueBody_val _ rfl _ rfl]
      simpa [add_assoc, one_add_one_eq_two] using h₂.func_unique (codeIn_func_quote F))
  have h := provable_qqAlls_of_tprovable_fvar _
    (funcUniqueBody_shift hc.domT_shift (hc.funcT_shift F)) (by
      rw [IsTable.compTable_domT h₁.toIsTable h₂.toIsTable hc,
        IsTable.compTable_funcT h₁.toIsTable h₂.toIsTable hc]
      exact tprovable_comp_funcUniqueBody h₁ _ _ hb)
  rw [funcUniqueBody_val _ rfl _ rfl] at h
  simpa [add_assoc, one_add_one_eq_two] using h

include h₁ h₂ hsound in
/-- The composite of a table of a translation in `S` and a table of a translation in `U`, along
the first of which every theorem of `U` translates to a theorem of `S`, is a table of a
translation in `S`. -/
theorem IsTranslationTable.compTable :
    IsTranslationTable ℒₒᵣ S (Bootstrapping.compTable ℒₒᵣ ℒₒᵣ tbl₁ tbl₂) where
  toIsTable := h₁.toIsTable.compTable h₂.toIsTable
  exs_domain := comp_exs_domain h₁ h₂ hsound
  func_exists hf := by
    obtain ⟨k, F, rfl, rfl⟩ := Language.SymbolsStandard.oRing.2 _ _ hf
    exact comp_func_exists h₁ h₂ (h₁.toIsTable.compTable h₂.toIsTable) hsound F
  func_unique hf := by
    obtain ⟨k, F, rfl, rfl⟩ := Language.SymbolsStandard.oRing.2 _ _ hf
    exact comp_func_unique h₁ h₂ (h₁.toIsTable.compTable h₂.toIsTable) hsound F
  func_congr hf := by
    obtain ⟨k, F, rfl, rfl⟩ := Language.SymbolsStandard.oRing.2 _ _ hf
    exact comp_func_congr (h₁.toIsTable.compTable h₂.toIsTable) F
  preserve_eq := comp_preserve_eq h₁ h₂ (h₁.toIsTable.compTable h₂.toIsTable) hsound

end compConditions

end Bootstrapping
end FFL.FirstOrder.Arithmetic
