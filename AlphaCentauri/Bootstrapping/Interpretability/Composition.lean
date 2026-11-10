module

public import AlphaCentauri.Bootstrapping.Interpretability.CaseSplit
public import AlphaCentauri.Bootstrapping.Interpretability.Soundness

/-!
# The composite table

For a table `tbl₁` of a translation of $L_2$ into $L_1$ and a table `tbl₂` of a translation of
$L_3$ into $L_2$, the composite table has as domain formula the conjunction of the domain formula
of `tbl₁` and the translation along `tbl₁` of the domain formula of `tbl₂`, and as the entries of
the symbols the translations along `tbl₁` of the entries of `tbl₂`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open _root_.FFL.Entailment

/-! ## The composite table -/

section compTable

variable (L₁ L₂ : Language) [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

noncomputable def translateVec.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y tbl u. y = 0”
  succ := .mkSigma
    “y ih k tbl u. ∃ a, !nthDef a u k ∧ ∃ c, !(translateGraph L₁ L₂) c tbl a ∧ !concatDef y ih c”

noncomputable def translateVec.construction : PR.Construction V (translateVec.blueprint L₁ L₂) where
  zero := fun _ ↦ 0
  succ := fun x k ih ↦ concat ih (translate L₁ L₂ (x 0) (x 1).[k])
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

/-- `translateVec L₁ L₂ tbl u k` is the vector of length `k` whose `j`-th entry is the translation
of `u.[j]` along `tbl`. -/
noncomputable def translateVec (tbl u k : V) : V :=
  (translateVec.construction L₁ L₂).result ![tbl, u] k

/-- The composite of the tables `tbl₁` and `tbl₂`: its domain formula is `δ₁ ∧ τ₁(δ₂)` and its
entries for the symbols are the translations along `tbl₁` of those of `tbl₂`. -/
noncomputable def compTable (tbl₁ tbl₂ : V) : V :=
  ?[tbl₁.[0] ^⋏ translate L₁ L₂ tbl₁ tbl₂.[0],
    translateVec L₁ L₂ tbl₁ tbl₂.[1] (len tbl₂.[1]),
    translateVec L₁ L₂ tbl₁ tbl₂.[2] (len tbl₂.[2])]

/-- The $\Sigma_1$ graph of `translateVec`, with argument order `(y, tbl, u, k)`. -/
noncomputable def translateVecGraph : 𝚺ᴬ₁.Semisentence 4 :=
  (translateVec.blueprint L₁ L₂).resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

variable {L₁ L₂}

instance translateVec.defined :
    𝚺ᴬ₁-Function₃[V] translateVec L₁ L₂ via translateVecGraph L₁ L₂ := .mk fun v ↦ by
  simp [(translateVec.construction L₁ L₂).result_defined_iff, translateVecGraph]; rfl

instance translateVec.definable : 𝚺ᴬ₁-Function₃[V] translateVec L₁ L₂ :=
  translateVec.defined.to_definable

@[simp] lemma translateVec_zero (tbl u : V) : translateVec L₁ L₂ tbl u 0 = 0 := by
  simp [translateVec, translateVec.construction]

@[simp] lemma translateVec_succ (tbl u k : V) :
    translateVec L₁ L₂ tbl u (k + 1) =
      concat (translateVec L₁ L₂ tbl u k) (translate L₁ L₂ tbl u.[k]) := by
  simp [translateVec, translateVec.construction]

@[simp] lemma len_translateVec (tbl u k : V) : len (translateVec L₁ L₂ tbl u k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

lemma nth_translateVec (tbl u k : V) :
    ∀ j < k, (translateVec L₁ L₂ tbl u k).[j] = translate L₁ L₂ tbl u.[j] := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro j hj
    rcases (lt_succ_iff_le.mp hj).lt_or_eq with hlt | rfl
    · rw [translateVec_succ, concat_nth_lt _ _ (by simpa using hlt)]
      exact ih j hlt
    · rw [translateVec_succ, concat_nth_len' _ _ (by simp)]

lemma tableDomain_compTable (tbl₁ tbl₂ : V) :
    tableDomain (compTable L₁ L₂ tbl₁ tbl₂) =
      tableDomain tbl₁ ^⋏ translate L₁ L₂ tbl₁ (tableDomain tbl₂) := by
  simp [compTable, tableDomain]

lemma tableRel_compTable {tbl₁ tbl₂ k r : V} (h : ⟪k, r⟫ < len tbl₂.[1]) :
    tableRel (compTable L₁ L₂ tbl₁ tbl₂) k r = translate L₁ L₂ tbl₁ (tableRel tbl₂ k r) := by
  simp [compTable, tableRel, nth_translateVec _ _ _ _ h]

lemma tableFunc_compTable {tbl₁ tbl₂ k f : V} (h : ⟪k, f⟫ < len tbl₂.[2]) :
    tableFunc (compTable L₁ L₂ tbl₁ tbl₂) k f = translate L₁ L₂ tbl₁ (tableFunc tbl₂ k f) := by
  simp [compTable, tableFunc, nth_translateVec _ _ _ _ h]

variable {L₃ : Language} [L₂.Eq] [L₃.Encodable] [L₃.LORDefinable] {tbl₁ tbl₂ : V}

/-- The composite of two tables is a table. -/
lemma IsTable.compTable (hT₁ : IsTable L₁ L₂ tbl₁) (hT₂ : IsTable L₂ L₃ tbl₂) :
    IsTable L₁ L₃ (compTable L₁ L₂ tbl₁ tbl₂) where
  domain := by
    rw [tableDomain_compTable]
    simp [hT₁.domain, IsSemiformula.translate hT₁ hT₂.domain]
  domain_shift := by
    rw [tableDomain_compTable]
    simp [hT₁.domain.isUFormula, (IsSemiformula.translate hT₁ hT₂.domain).isUFormula,
      ← translate_shift hT₁ hT₂.domain, hT₁.domain_shift, hT₂.domain_shift]
  rel h := by
    rw [tableRel_compTable (hT₂.lt_len_rel h)]
    exact IsSemiformula.translate hT₁ (hT₂.rel h)
  rel_shift h := by
    rw [tableRel_compTable (hT₂.lt_len_rel h), ← translate_shift hT₁ (hT₂.rel h),
      hT₂.rel_shift h]
  func h := by
    rw [tableFunc_compTable (hT₂.lt_len_func h)]
    exact IsSemiformula.translate hT₁ (hT₂.func h)
  func_shift h := by
    rw [tableFunc_compTable (hT₂.lt_len_func h), ← translate_shift hT₁ (hT₂.func h),
      hT₂.func_shift h]

end compTable

/-! ## Typed translations -/

section relAllItr

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- `∀ x₁ (d(x₁) → ∀ x₂ (d(x₂) → … φ))`, the block of `k` universal quantifiers relativized to
`d`. -/
noncomputable def relAllItr {n : ℕ} (d : Semiformula V L 1) :
    (k : ℕ) → Semiformula V L (n + k) → Semiformula V L n
  | 0, φ => φ
  | k + 1, φ => relAllItr d k (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 φ))

@[simp] lemma relAllItr_zero {n : ℕ} (d : Semiformula V L 1) (φ : Semiformula V L (n + 0)) :
    relAllItr d 0 φ = φ := rfl

lemma relAllItr_succ {n k : ℕ} (d : Semiformula V L 1) (φ : Semiformula V L (n + (k + 1))) :
    relAllItr d (k + 1) φ = relAllItr d k (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 φ)) := rfl

end relAllItr

section typed

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] {tbl : V} (hT : IsTable L₁ L₂ tbl)

/-- The translation along a table of a typed formula, as a typed formula. -/
noncomputable def IsTable.transT {n : ℕ} (φ : Semiformula V L₂ n) : Semiformula V L₁ n :=
  ⟨translate L₁ L₂ tbl φ.val, IsSemiformula.translate hT φ.isSemiformula⟩

namespace IsTable

@[simp] lemma transT_val {n : ℕ} (φ : Semiformula V L₂ n) :
    (hT.transT φ).val = translate L₁ L₂ tbl φ.val := rfl

@[simp] lemma transT_verum {n : ℕ} : hT.transT (⊤ : Semiformula V L₂ n) = ⊤ := by
  ext; simp

@[simp] lemma transT_falsum {n : ℕ} : hT.transT (⊥ : Semiformula V L₂ n) = ⊥ := by
  ext; simp

@[simp] lemma transT_and {n : ℕ} (φ ψ : Semiformula V L₂ n) :
    hT.transT (φ ⋏ ψ) = hT.transT φ ⋏ hT.transT ψ := by
  ext; simp [φ.isSemiformula.isUFormula, ψ.isSemiformula.isUFormula]

@[simp] lemma transT_or {n : ℕ} (φ ψ : Semiformula V L₂ n) :
    hT.transT (φ ⋎ ψ) = hT.transT φ ⋎ hT.transT ψ := by
  ext; simp [φ.isSemiformula.isUFormula, ψ.isSemiformula.isUFormula]

@[simp] lemma transT_neg {n : ℕ} (φ : Semiformula V L₂ n) :
    hT.transT (∼φ) = ∼hT.transT φ := by
  ext; simp [translate_neg hT φ.isSemiformula]

@[simp] lemma transT_imp {n : ℕ} (φ ψ : Semiformula V L₂ n) :
    hT.transT (φ 🡒 ψ) = hT.transT φ 🡒 hT.transT ψ := by
  simp [Semiformula.imp_def]

@[simp] lemma transT_iff {n : ℕ} (φ ψ : Semiformula V L₂ n) :
    hT.transT (φ 🡘 ψ) = hT.transT φ 🡘 hT.transT ψ := by
  simp [LogicalConnective.iff]

@[simp] lemma transT_conj {n m : ℕ} (v : Fin m → Semiformula V L₂ n) :
    hT.transT (Matrix.conj v) = Matrix.conj fun i ↦ hT.transT (v i) :=
  Matrix.conj_map hT.transT (transT_verum hT) (transT_and hT) v

lemma domainAt_zero_typed {n : ℕ} :
    domainAt L₁ tbl 0 = (hT.domT.subst ![Semiterm.bvar 0] : Semiformula V L₁ (n + 1)).val := by
  rw [Semiformula.val_substs, domT_val, domainAt]
  simp

@[simp] lemma transT_all {n : ℕ} (φ : Semiformula V L₂ (n + 1)) :
    hT.transT (∀¹ φ) = ∀¹ (hT.domT.subst ![Semiterm.bvar 0] 🡒 hT.transT φ) := by
  ext
  simp [φ.isSemiformula.isUFormula, domainAt_zero_typed hT (n := n)]

@[simp] lemma transT_exs {n : ℕ} (φ : Semiformula V L₂ (n + 1)) :
    hT.transT (∃¹ φ) = ∃¹ (hT.domT.subst ![Semiterm.bvar 0] ⋏ hT.transT φ) := by
  ext
  simp [φ.isSemiformula.isUFormula, domainAt_zero_typed hT (n := n)]

lemma transT_allItr {n : ℕ} : ∀ (k : ℕ) (φ : Semiformula V L₂ (n + k)),
    hT.transT (∀¹^[k] φ) = relAllItr hT.domT k (hT.transT φ)
  | 0, φ => rfl
  | k + 1, φ => by
    rw [allItr_succ, transT_allItr k, transT_all, relAllItr_succ]

lemma transT_shift {n : ℕ} (φ : Semiformula V L₂ n) :
    hT.transT φ.shift = (hT.transT φ).shift := by
  ext; simp [translate_shift hT φ.isSemiformula]

lemma transT_free (φ : Semiformula V L₂ 1) : hT.transT φ.free = (hT.transT φ).free := by
  ext
  simpa using translate_free hT (by simp)

end IsTable

/-- A vector of terms each of which is a variable. -/
def IsVarVec {L : Language} [L.Encodable] [L.LORDefinable] {n m : ℕ}
    (w : SemitermVec V L n m) : Prop :=
  ∀ i, (∃ z, w i = Semiterm.bvar z) ∨ (∃ x, w i = Semiterm.fvar x)

lemma IsTable.transT_subst {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {tbl : V}
    (hT : IsTable L L tbl) {n m : ℕ} (w : SemitermVec V L n m) (hw : IsVarVec w)
    (φ : Semiformula V L n) : hT.transT (φ.subst w) = (hT.transT φ).subst w := by
  ext
  simp only [IsTable.transT_val, Semiformula.val_substs]
  apply translate_subst hT w.isSemitermVec ?_ φ.isSemiformula
  intro i hi
  obtain ⟨i, rfl⟩ := eq_fin_of_lt_nat hi
  rw [SemitermVec.val_nth_eq]
  rcases hw i with ⟨z, hz⟩ | ⟨x, hx⟩
  · exact Or.inl ⟨z, by simp [hz]⟩
  · exact Or.inr ⟨x, by simp [hx]⟩

namespace IsTable

end IsTable

end typed

/-! ## Relativized blocks of quantifiers -/

section relAllItrProof

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

lemma shift_iterate_relAllItr {n : ℕ} {d : Semiformula V L 1} (hd : d.shift = d) (j : ℕ) :
    ∀ (k : ℕ) (φ : Semiformula V L (n + k)),
      Semiformula.shift^[j] (relAllItr d k φ) = relAllItr d k (Semiformula.shift^[j] φ)
  | 0, φ => rfl
  | k + 1, φ => by
    have hd' : Semiformula.shift^[j] d = d := Function.iterate_fixed hd j
    rw [relAllItr_succ, relAllItr_succ, shift_iterate_relAllItr hd j k]
    simp [Semiformula.shift_iterate_subst, hd']

/-- Specialisation of a relativized block of `k` universal quantifiers. -/
lemma relAllItr_specialize (d : Semiformula V L 1) :
    ∀ {k : ℕ} (φ : Semiformula V L (0 + k)) (w : SemitermVec V L (0 + k) 0),
      T.internalize V ⊢ relAllItr d k φ 🡒 Matrix.conj (fun i ↦ d.subst ![w i]) 🡒 φ.subst w
  | 0, φ, w => by
    rw [Semiformula.subst_nil_eq_self]
    simp only [relAllItr_zero]
    cl_prover
  | k + 1, φ, w => by
    have h₁ := relAllItr_specialize d (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 φ)) (Matrix.vecTail w)
    rw [Semiformula.substs_all] at h₁
    have h₂ := TProof.all_imp_subst (T := T)
      ((d.subst ![Semiterm.bvar 0] 🡒 φ).subst (SemitermVec.q (Matrix.vecTail w))) (w 0)
    rw [Semiformula.substs_q_substs_single,
      show (w 0 :> Matrix.vecTail w) = w from Matrix.cons_head_tail w] at h₂
    simp only [Semiformula.substs_imp, Semiformula.substs_substs, Matrix.vecMap_cons',
      Matrix.head_cons, Matrix.vecMap_nil, Semiterm.substs_bvar] at h₁ h₂
    rw [relAllItr_succ]
    simp only [Matrix.conj]
    cl_prover [h₁, h₂]

omit [T.Δ₁] in
lemma free_subst_q_fvar' {k : ℕ} (ψ : Semiformula V L (k + 1)) :
    (ψ.subst (SemitermVec.q fun i : Fin k ↦ Semiterm.fvar (i : V))).free =
      ψ.shift.subst fun i ↦ Semiterm.fvar (i : V) := by
  rw [Semiformula.free, Semiformula.shift_substs, Semiformula.substs_substs]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

/-- Generalisation of a relativized block of `k` universal quantifiers over `k` fresh free
variables under a hypothesis. -/
lemma relAllItr_generalize_imp {d : Semiformula V L 1} (hd : d.shift = d) :
    ∀ {k : ℕ} {C : Formula V L} {φ : Semiformula V L (0 + k)},
      T.internalize V ⊢ Semiformula.shift^[k] C 🡒
        Matrix.conj (fun i : Fin (0 + k) ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) 🡒
          (Semiformula.shift^[k] φ).subst (fun i ↦ Semiterm.fvar ((i : ℕ) : V)) →
      T.internalize V ⊢ C 🡒 relAllItr d k φ
  | 0, C, φ, h => by
    rw [Semiformula.subst_nil_eq_self] at h
    simp only [Function.iterate_zero, id_eq, relAllItr_zero, Matrix.conj] at h ⊢
    cl_prover [h]
  | k + 1, C, φ, h => by
    rw [relAllItr_succ]
    apply relAllItr_generalize_imp hd
    rw [Semiformula.shift_iterate_all, Semiformula.substs_all]
    apply CC_of_CK
    apply TProof.generalize_imp
    rw [free_subst_q_fvar' (k := 0 + k), ← Function.iterate_succ_apply' Semiformula.shift]
    simp only [Semiformula.shift_and, Semiformula.shift_conj, Semiformula.shift_substs, hd,
      Semiformula.shift_iterate_imp, Semiformula.substs_imp, Semiformula.shift_iterate_subst,
      Function.iterate_fixed hd, Semiformula.substs_substs, Matrix.vecMap_cons', Matrix.vecMap_nil,
      Semiterm.shift_fvar, Semiterm.shift_iterate_bvar, Matrix.head_cons, Semiterm.substs_bvar,
      ← Function.iterate_succ_apply' Semiformula.shift] at h ⊢
    simp only [Matrix.conj] at h
    simp only [Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply, Nat.reduceAdd,
      Fin.coe_ofNat_eq_mod, zero_add, Nat.zero_mod, Nat.cast_zero] at h ⊢
    cl_prover [h]

omit [T.Δ₁] in
lemma conj_fin_zero_add {α : Type*} [Top α] [Wedge α] (k : ℕ) (f : ℕ → α) :
    Matrix.conj (fun i : Fin (0 + k) ↦ f i) = Matrix.conj (fun i : Fin k ↦ f i) := by
  have : ∀ m (_ : m = k),
      Matrix.conj (fun i : Fin m ↦ f i) = Matrix.conj (fun i : Fin k ↦ f i) := by
    rintro m rfl; rfl
  exact this _ (zero_add k)

/-- Under hypotheses that `B i` and `C i` agree on `d`, the block `relativizedImp (d ⋏ e) B G` is
equivalent to the block of quantifiers relativized to `d` over `⋀ᵢ (e(wᵢ) ∧ Cᵢ(wᵢ)) → G`. -/
lemma relativizedImp_iff_relAllItr {k : ℕ} {d : Semiformula V L 1} (hd : d.shift = d)
    (e : Semiformula V L 1) (B C : Fin k → Semiformula V L 1) (G : Semiformula V L (0 + k)) :
    T.internalize V ⊢ Matrix.conj (fun i ↦ ∀¹ (d 🡒 (B i 🡘 C i))) 🡒
      (relativizedImp (d ⋏ e) B G 🡘 relAllItr d k (Matrix.conj (fun i : Fin k ↦
        e.subst ![Semiterm.bvar (i.addCast 0)] ⋏ (C i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒
          G)) := by
  have hdk : Semiformula.shift^[k] d = d := Function.iterate_fixed hd k
  have hH (i : Fin k) : T.internalize V ⊢
      Semiformula.shift^[k] (Matrix.conj fun i ↦ ∀¹ (d 🡒 (B i 🡘 C i))) 🡒
        d.subst ![Semiterm.fvar ((i : ℕ) : V)] 🡒
          ((Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)] 🡘
            (Semiformula.shift^[k] (C i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) := by
    rw [Semiformula.shift_iterate_conj]
    have h₁ := matrixConj_elim (𝓢 := T.internalize V)
      (fun i ↦ Semiformula.shift^[k] (∀¹ (d 🡒 (B i 🡘 C i)))) i
    have h₂ := TProof.all_imp_subst (T := T) (Semiformula.shift^[k] (d 🡒 (B i 🡘 C i)))
      (Semiterm.fvar ((i : ℕ) : V))
    simp only [Semiformula.shift_iterate_all, Semiformula.shift_iterate_imp,
      Semiformula.shift_iterate_iff, hdk] at h₁ h₂ ⊢
    simp only [LogicalConnective.iff, Semiformula.substs_imp, Semiformula.substs_and] at h₁ h₂ ⊢
    exact C_trans h₁ h₂
  have h₁ : T.internalize V ⊢ Matrix.conj (fun i ↦ ∀¹ (d 🡒 (B i 🡘 C i))) ⋏
      relativizedImp (d ⋏ e) B G 🡒 relAllItr d k (Matrix.conj (fun i : Fin k ↦
        e.subst ![Semiterm.bvar (i.addCast 0)] ⋏ (C i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒
          G) := by
    apply relAllItr_generalize_imp (k := k) hd
    have hs := TProof.allItr_specialize (T := T) (Semiformula.shift^[k]
      (Matrix.conj (fun i : Fin k ↦ (d ⋏ e).subst ![Semiterm.bvar (i.addCast 0)] ⋏
        (B i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒 G))
      (fun i ↦ Semiterm.fvar ((i : ℕ) : V))
    simp only [relativizedImp, Semiformula.shift_iterate_and, Semiformula.shift_iterate_allItr,
      Semiformula.shift_iterate_imp, Semiformula.substs_imp, Semiformula.shift_iterate_conj,
      Semiformula.substs_conj, Semiformula.substs_and, Semiformula.subst_shift_iterate_subst_bvar,
      Fin.addCast_val, hdk] at hs ⊢
    simp only [conj_fin_zero_add k (fun j ↦ d.subst ![Semiterm.fvar (j : V)])] at hs ⊢
    have hZ : T.internalize V ⊢ (Matrix.conj fun i ↦ Semiformula.shift^[k] (∀¹ (d 🡒 (B i 🡘 C i)))) ⋏
        (Matrix.conj fun i : Fin k ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
        (Matrix.conj fun i : Fin k ↦
          (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
          (Semiformula.shift^[k] (C i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) 🡒
        Matrix.conj fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
          (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
          (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)] :=
      matrixConj_intro fun i ↦ by
        have a := matrixConj_elim (𝓢 := T.internalize V)
          (fun i : Fin k ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) i
        have b := matrixConj_elim (𝓢 := T.internalize V)
          (fun i : Fin k ↦ (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
            (Semiformula.shift^[k] (C i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) i
        have c := hH i
        rw [Semiformula.shift_iterate_conj] at c
        cl_prover [a, b, c]
    cl_prover [hs, hZ]
  have h₂ : T.internalize V ⊢ Matrix.conj (fun i ↦ ∀¹ (d 🡒 (B i 🡘 C i))) ⋏
      relAllItr d k (Matrix.conj (fun i : Fin k ↦
        e.subst ![Semiterm.bvar (i.addCast 0)] ⋏ (C i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒
          G) 🡒 relativizedImp (d ⋏ e) B G := by
    unfold relativizedImp
    apply TProof.allItr_generalize_imp
    have hs := relAllItr_specialize (T := T) d (Semiformula.shift^[k]
      (Matrix.conj (fun i : Fin k ↦ e.subst ![Semiterm.bvar (i.addCast 0)] ⋏
        (C i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒 G))
      (fun i ↦ Semiterm.fvar ((i : ℕ) : V))
    simp only [Semiformula.shift_iterate_and, shift_iterate_relAllItr hd,
      Semiformula.shift_iterate_imp, Semiformula.substs_imp, Semiformula.shift_iterate_conj,
      Semiformula.substs_conj, Semiformula.substs_and, Semiformula.subst_shift_iterate_subst_bvar,
      Fin.addCast_val, hdk] at hs ⊢
    simp only [conj_fin_zero_add k (fun j ↦ d.subst ![Semiterm.fvar (j : V)])] at hs ⊢
    have hXY : T.internalize V ⊢
        (Matrix.conj fun i ↦ Semiformula.shift^[k] (∀¹ (d 🡒 (B i 🡘 C i)))) ⋏
        (Matrix.conj fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
          (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
          (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) 🡒
        (Matrix.conj fun i : Fin k ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
        (Matrix.conj fun i : Fin k ↦
          (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
          (Semiformula.shift^[k] (C i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) := by
      have a := matrixConj_intro (𝓢 := T.internalize V)
        (φ := (Matrix.conj fun i ↦ Semiformula.shift^[k] (∀¹ (d 🡒 (B i 🡘 C i)))) ⋏
          (Matrix.conj fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
            (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
            (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)]))
        (v := fun i : Fin k ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) fun i ↦ by
          have b := matrixConj_elim (𝓢 := T.internalize V)
            (fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
              (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
              (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) i
          cl_prover [b]
      have b := matrixConj_intro (𝓢 := T.internalize V)
        (φ := (Matrix.conj fun i ↦ Semiformula.shift^[k] (∀¹ (d 🡒 (B i 🡘 C i)))) ⋏
          (Matrix.conj fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
            (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
            (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)]))
        (v := fun i : Fin k ↦ (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
          (Semiformula.shift^[k] (C i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) fun i ↦ by
          have b := matrixConj_elim (𝓢 := T.internalize V)
            (fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
              (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
              (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) i
          have c := hH i
          rw [Semiformula.shift_iterate_conj] at c
          cl_prover [b, c]
      cl_prover [a, b]
    cl_prover [hs, hXY]
  cl_prover [h₁, h₂]

end relAllItrProof

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
  have hdom : IsSemiformula L 1 tbl₁.[0] := h₁.domain
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

end FFL.FirstOrder.Arithmetic.Bootstrapping
