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
  have hdom : IsSemiformula L 1 tbl₁.[0] := h₁.domain
  have ih' (i : Fin k) := derivable_insert_negDomSet_mono hdom _ (le_of_lt (hM i))
    (derivable_comp_varEqual h₁ hT₂ hc hL (u i))
  exact Derivable.of_tprovable_imp (tprovable_comp_rel h₁ hT₂ hc R u)
    (Derivable.conj_typed (IsFormulaSet.negDomSet hdom M) ih')

omit [L.Eq] [S.Δ₁] [𝗘𝗤 L ⪯ S] in
lemma freshVec_fvar (j : V) : ∀ i < len (freshVec j : V), ∃ x, (freshVec j : V).[i] = ^&x := by
  intro i hi
  rw [len_freshVec] at hi
  rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with h' | rfl
  · exact ⟨i + 1, nth_freshVec_of_lt h'⟩
  · exact ⟨0, by simp⟩

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
/-- The step of a quantifier: from the derivability for `free p`, the hypotheses for the fresh
variables are discharged and the hypothesis for `&0` is put in a disjunction. -/
lemma derivable_comp_quant (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (P : Semiformula V L 1) {M : V} (hM : P.val ≤ M)
    (ih : Derivable S (insert (hc.transT P.free 🡘 h₁.transT (hT₂.transT P.free)).val
      (negDomSet L tbl₁.[0] P.free.val))) :
    Derivable S (insert (∼(h₁.domT.subst ![Semiterm.fvar 0]) ⋎
      (hc.transT P 🡘 h₁.transT (hT₂.transT P)).free).val
        (setShift L (negDomSet L tbl₁.[0] M))) := by
  have hdom : IsSemiformula L 1 tbl₁.[0] := h₁.domain
  have hds : shift L tbl₁.[0] = tbl₁.[0] := h₁.domain_shift
  have hp : IsSemiformula L 1 P.val := by simp
  set Xf : Formula V L := hc.transT P.free 🡘 h₁.transT (hT₂.transT P.free) with hXf
  have hX : IsFormula L Xf.val := by simp
  have h₁' : Derivable S (insert Xf.val
      (negDomSet L tbl₁.[0] (P.free.val + (M + 1)))) :=
    derivable_insert_negDomSet_mono hdom Xf (le_add_right le_rfl) ih
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
  have h₃ := Derivable.elim_negDomSet hS hdom hds h₁.exs_domain
    (by simp) (le_add_left le_rfl) hfresh h₂
  rw [negDomSet_succ_eq_insert_setShift hdom hds] at h₃
  have hnd : IsFormula L (neg L (substs1 L (^&0) tbl₁.[0])) :=
    (IsSemiformula.substs1 (n := 0) (by simp) hdom).neg
  have h₄ : Derivable S (insert (neg L (substs1 L (^&0) tbl₁.[0])) (insert Xf.val
      (setShift L (negDomSet L tbl₁.[0] M)))) :=
    Derivable.ofSetEq (fun x ↦ by simp; tauto) h₃
  have h₅ := derivable_insert_or (IsFormulaSet.setShift (IsFormulaSet.negDomSet hdom _)) hnd hX h₄
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
    simp [hc.domain, h₁.domain, IsSemiformula.translate hc hP1,
      IsSemiformula.translate h₁.toIsTable hT₂.domain,
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
    simp [hc.domain, h₁.domain, IsSemiformula.translate hc hP1,
      IsSemiformula.translate h₁.toIsTable hT₂.domain,
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
  have hdom : IsSemiformula L 1 tbl₁.[0] := h₁.domain
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
fixed by the shift has provably equivalent translations. -/
theorem provable_comp_translate_iff (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hL : L.SymbolsStandard V) {p : V} (hp : IsFormula L p) (hps : shift L p = p) :
    Provable S (iff L (translate L L (Bootstrapping.compTable L L tbl₁ tbl₂) p)
      (translate L L tbl₁ (translate L L tbl₂ p))) := by
  have hdom : IsSemiformula L 1 tbl₁.[0] := h₁.domain
  have hds : shift L tbl₁.[0] = tbl₁.[0] := h₁.domain_shift
  have ha := IsSemiformula.translate hc hp
  have hb := IsSemiformula.translate h₁.toIsTable (IsSemiformula.translate hT₂ hp)
  have h₀ := derivable_comp_translate h₁ hT₂ hc hS hL hp
  set X := iff L (translate L L (Bootstrapping.compTable L L tbl₁ tbl₂) p)
    (translate L L tbl₁ (translate L L tbl₂ p)) with hXdef
  have hX : IsFormula L X := by simp [hXdef, ha, hb]
  have hXs : shift L X = X := by
    rw [hXdef, shift_iff_code ha hb, ← translate_shift hc hp,
      ← translate_shift h₁.toIsTable (IsSemiformula.translate hT₂ hp), ← translate_shift hT₂ hp,
      hps]
  have h₂ : Derivable S (insert X ∅ ∪ negDomSet L tbl₁.[0] p) :=
    Derivable.ofSetEq (fun x ↦ by simp) h₀
  have hfresh : ∀ j, 0 ≤ j → j < p →
      fvSubstImage (L := L) (freshVec j) (insert X ∅) = setShift L (insert X ∅) := by
    intro j _ _
    rw [fvSubstImage_insert, fvSubstImage_empty, mem_setShift_insert, setShift_empty,
      fvSubst_eq_self_of_shift hX hXs, hXs]
  have h₃ := Derivable.elim_negDomSet hS hdom hds h₁.exs_domain (by simp [hX]) zero_le hfresh h₂
  rw [negDomSet_zero] at h₃
  exact internal_provable_iff_internal_derivable.mpr (Derivable.ofSetEq (fun x ↦ by simp) h₃)

end compFormula

end FFL.FirstOrder.Arithmetic.Bootstrapping
