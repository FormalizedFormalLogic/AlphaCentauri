module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.Bootstrapping.Interpretability.DefinesElement
public import AlphaCentauri.Bootstrapping.Proof.ExistsElimination
public import AlphaCentauri.Interpretability.Basic
public import AlphaCentauri.ToFoundation.InternalEquality
public import AlphaCentauri.ToFoundation.Provable
public import AlphaCentauri.ToFoundation.TypedProof

/-!
# Values of closed terms along the internal translation

For a direct translation `π`, the domain formula of `π` is provably nonempty, and the graph of
each function symbol of `π` defines a unique value on the domain, respects equality and is
invariant under the substitution of equal arguments. Along a table of `π`, the internal
translation of a typed term or formula of $L_2$ is the typed formula prescribed by `π`. The
internal value of a closed typed term is defined by a formula, these defining formulas are
derivable under the negated domain instances of the term, and the defining formula is transported
along the substitution of a closed term for a variable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

attribute [local simp] Semiformula.substs_substs

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Facts about the domain and the graphs -/

section piFacts

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  (π : DirectTranslation S L₂)

variable {k : ℕ}

section domain

omit [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq] in
lemma operator_bvar_eq_sentence (o : Semiformula.Operator L₁ 1) :
    (o.operator ![#0] : Semisentence L₁ 1) = o.sentence := by
  simp [Semiformula.Operator.operator, Rewriting.emb]

/-- The code of the domain formula of `π`. -/
noncomputable abbrev domT : Semiformula V L₁ 1 := ⌜π.domain.sentence⌝


/-- The code of the graph of the function symbol `F` of `π`. -/
noncomputable abbrev funcT (F : L₂.Func k) : Semiformula V L₁ (k + 1) := ⌜(π.func F).sentence⌝

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma domT_shift : (domT π : Semiformula V L₁ 1).shift = domT π :=
  Semisentence.shift_typed_quote _

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma funcT_shift (F : L₂.Func k) : (funcT π F : Semiformula V L₁ (k + 1)).shift = funcT π F :=
  Semisentence.shift_typed_quote _

end domain

section provable

variable {tbl : V}

omit [L₂.LORDefinable] in
lemma provable_exs_domain (h : IsTableOf π tbl) : Provable S (^∃ tbl.[0]) := by
  have h₁ := internalize_provability (V := V) π.domain_nonempty
  rw [Sentence.quote_ex, operator_bvar_eq_sentence] at h₁
  have h₂ : tbl.[0] = ⌜π.domain.sentence⌝ := h.domain
  rw [h₂]
  exact h₁

end provable

section quote

omit [L₁.Eq] in
lemma quote_operator_bvar {m n : ℕ} (o : Semiformula.Operator L₁ m) (f : Fin m → Fin n) :
    (⌜(o.operator (fun i ↦ #(f i)) : Semisentence L₁ n)⌝ : Semiformula V L₁ n) =
      (⌜o.sentence⌝ : Semiformula V L₁ m).subst (fun i ↦ Semiterm.bvar (f i)) := by
  rw [Sentence.typed_quote_def, Sentence.typed_quote_def]
  simp [Semiformula.Operator.operator, Rewriting.emb]

omit [L₁.Eq] in
lemma quote_operator_cons {m n : ℕ} (o : Semiformula.Operator L₁ (m + 1)) (a : Fin n)
    (f : Fin m → Fin n) :
    (⌜(o.operator (#a :> fun i ↦ #(f i)) : Semisentence L₁ n)⌝ : Semiformula V L₁ n) =
      (⌜o.sentence⌝ : Semiformula V L₁ (m + 1)).subst
        (Semiterm.bvar a :> fun i ↦ Semiterm.bvar (f i)) := by
  have h : (#a :> fun i : Fin m ↦ (#(f i) : FirstOrder.Semiterm L₁ Empty n)) =
      fun j ↦ #((a :> f : Fin (m + 1) → Fin n) j) := by
    funext j
    cases j using Fin.cases <;> rfl
  rw [h, quote_operator_bvar]
  congr 1
  funext j
  cases j using Fin.cases <;> rfl

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma quote_domain_bvar {n : ℕ} (i : Fin n) :
    (⌜(π.domain.operator ![#i] : Semisentence L₁ n)⌝ : Semiformula V L₁ n) =
      (domT π).subst ![Semiterm.bvar i] := by
  have h : (![#i] : Fin 1 → FirstOrder.Semiterm L₁ Empty n) = fun j ↦ #((fun _ ↦ i) j) := by
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl
  rw [h, quote_operator_bvar]
  congr 1
  funext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rfl

lemma quote_eq_bvar {n : ℕ} (i j : Fin n) :
    (⌜(op(=).operator ![#i, #j] : Semisentence L₁ n)⌝ : Semiformula V L₁ n) =
      Semiformula.equal (Semiterm.bvar i) (Semiterm.bvar j) := by
  rw [Sentence.typed_quote_def]
  simp only [Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.rew_rel_eq_comp, Rew.emb_eq_id, Semiformula.typed_quote_rel, Function.comp_apply,
    Rew.id_app, Rew.subst_bvar, Semiformula.equal]
  congr 1
  funext t
  match t with
  | 0 => rfl
  | 1 => rfl

end quote

section external

noncomputable abbrev funcExistsSent (F : L₂.Func k) : Semisentence L₁ k :=
  (Matrix.conj fun i : Fin k ↦ π.domain.operator ![#i]) 🡒
    ∃¹ (π.domain.operator ![#0] ⋏ (π.func F).operator (#0 :> fun i ↦ #i.succ))

omit [L₁.Encodable] [L₁.LORDefinable] [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma funcExists_external (F : L₂.Func k) : S ⊢ ∀¹* (funcExistsSent π F) := by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ _ _ hT
  have h := (DirectTranslation.models_funcDefined_iff _ _).mp
    (models_of_provable hT (π.func_defined F))
  simpa [models_iff, funcExistsSent, Function.comp_def, Matrix.constant_eq_singleton] using
    fun e' hD ↦ (h e' hD).exists

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma quote_funcExistsSent (F : L₂.Func k) :
    (⌜funcExistsSent π F⌝ : Semiformula V L₁ k) =
      Matrix.conj (fun i ↦ (domT π).subst ![Semiterm.bvar i]) 🡒
        ∃¹ ((domT π).subst ![Semiterm.bvar 0] ⋏
          (funcT π F).subst (Semiterm.bvar 0 :> fun i ↦ Semiterm.bvar i.succ)) := by
  simp only [funcExistsSent, LCWQIsoGödelQuote.imply, LCWQIsoGödelQuote.exs,
    LCWQIsoGödelQuote.and, quote_conj, quote_domain_bvar, quote_operator_cons]

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma funcExistsSent_subst (F : L₂.Func k) (w : Fin k → Term V L₁) :
    (⌜funcExistsSent π F⌝ : Semiformula V L₁ k).subst w =
      Matrix.conj (fun i ↦ (domT π).subst ![w i]) 🡒
        ∃¹ (domT π ⋏ (funcT π F).subst (Semiterm.bvar 0 :> fun i ↦ (w i).bShift)) := by
  rw [quote_funcExistsSent]
  simp [SemitermVec.q_eq_cons]

noncomputable abbrev uniqSent (F : L₂.Func k) : Semisentence L₁ (k + 2) :=
  (Matrix.conj (fun i : Fin k ↦ π.domain.operator ![#i.succ.succ]) ⋏ π.domain.operator ![#0] ⋏
    π.domain.operator ![#1] ⋏ (π.func F).operator (#0 :> fun i ↦ #i.succ.succ) ⋏
    (π.func F).operator (#1 :> fun i ↦ #i.succ.succ)) 🡒 op(=).operator ![#0, #1]

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma quote_uniqSent (F : L₂.Func k) :
    (⌜uniqSent π F⌝ : Semiformula V L₁ (k + 2)) =
      (Matrix.conj (fun i ↦ (domT π).subst ![Semiterm.bvar i.succ.succ]) ⋏
        (domT π).subst ![Semiterm.bvar 0] ⋏ (domT π).subst ![Semiterm.bvar 1] ⋏
        (funcT π F).subst (Semiterm.bvar 0 :> fun i ↦ Semiterm.bvar i.succ.succ) ⋏
        (funcT π F).subst (Semiterm.bvar 1 :> fun i ↦ Semiterm.bvar i.succ.succ)) 🡒
          Semiformula.equal (Semiterm.bvar 0) (Semiterm.bvar 1) := by
  simp only [uniqSent, LCWQIsoGödelQuote.imply, LCWQIsoGödelQuote.and, quote_conj,
    quote_domain_bvar, quote_operator_cons, quote_eq_bvar]

omit [L₁.Encodable] [L₁.LORDefinable] [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma uniqSent_external (F : L₂.Func k) : S ⊢ ∀¹* (uniqSent π F) := by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ _ _ hT
  have h := (DirectTranslation.models_funcDefined_iff _ _).mp
    (models_of_provable hT (π.func_defined F))
  have key (e' : Fin (k + 2) → M) (a : Fin (k + 2)) :
      (FirstOrder.Semiterm.val (L := L₁) (M := M) e' Empty.elim ∘
        (#a :> fun i : Fin k ↦ #i.succ.succ) : Fin (k + 1) → M) =
          (e' a :> fun i ↦ e' i.succ.succ) := by
    funext j
    cases j using Fin.cases <;> simp
  suffices H : ∀ e' : Fin (k + 2) → M, (∀ i : Fin k, π.domain.val ![e' i.succ.succ]) →
      π.domain.val ![e' 0] → π.domain.val ![e' 1] →
      (π.func F).val (e' 0 :> fun i ↦ e' i.succ.succ) →
      (π.func F).val (e' 1 :> fun i ↦ e' i.succ.succ) → e' 0 = e' 1 by
    simpa [models_iff, uniqSent, key] using H
  intro e' hW hD0 hD1 hG0 hG1
  obtain ⟨x, -, hu⟩ := h (fun i ↦ e' i.succ.succ) hW
  exact (hu _ ⟨hD0, hG0⟩).trans (hu _ ⟨hD1, hG1⟩).symm

noncomputable abbrev congrSent (F : L₂.Func k) : Semisentence L₁ ((k + 1) + (k + 1)) :=
  (op(=).operator ![#(Fin.castAdd (k + 1) 0), #(Fin.natAdd (k + 1) 0)] ⋏
    Matrix.conj (fun i : Fin k ↦
      op(=).operator ![#(Fin.castAdd (k + 1) i.succ), #(Fin.natAdd (k + 1) i.succ)])) 🡒
    ((π.func F).operator (fun j ↦ #(Fin.castAdd (k + 1) j)) 🡒
      (π.func F).operator (fun j ↦ #(Fin.natAdd (k + 1) j)))

omit [L₁.Encodable] [L₁.LORDefinable] [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma congrSent_external (F : L₂.Func k) : S ⊢ ∀¹* (congrSent π F) := by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ _ _ hT
  simp only [congrSent, Fin.natAdd_eq_addNat, models_iff, Semiformula.eval_allClosure,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_operator, Matrix.comp₂, Nat.succ_eq_add_one, Nat.reduceAdd,
    Semiterm.val_bvar, Tarski.Structure.eq_iff_eq, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one, Matrix.conj_hom_prop,
    LogicalConnective.Prop.and_eq, LogicalConnective.Prop.arrow_eq, and_imp]
  intro e' h0 hconj hG
  have hv : (fun j : Fin (k + 1) ↦ e' (j.addNat (k + 1))) =
      (fun j ↦ e' (Fin.castAdd (k + 1) j)) := by
    funext j
    cases j using Fin.cases with
    | zero => exact h0.symm
    | succ i => exact (hconj i).symm
  simpa [Function.comp_def, hv] using hG

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma uniqSent_subst (F : L₂.Func k) (y z : Term V L₁) (w : Fin k → Term V L₁) :
    (⌜uniqSent π F⌝ : Semiformula V L₁ (k + 2)).subst (y :> z :> w) =
      Matrix.conj (fun i ↦ (domT π).subst ![w i]) ⋏ (domT π).subst ![y] ⋏
        (domT π).subst ![z] ⋏ (funcT π F).subst (y :> w) ⋏ (funcT π F).subst (z :> w) 🡒
          Semiformula.equal y z := by
  rw [quote_uniqSent]
  simp

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma quote_congrSent (F : L₂.Func k) :
    (⌜congrSent π F⌝ : Semiformula V L₁ ((k + 1) + (k + 1))) =
      (Semiformula.equal (Semiterm.bvar (Fin.castAdd (k + 1) 0))
          (Semiterm.bvar (Fin.natAdd (k + 1) 0)) ⋏
        Matrix.conj (fun i : Fin k ↦
          Semiformula.equal (Semiterm.bvar (Fin.castAdd (k + 1) i.succ))
            (Semiterm.bvar (Fin.natAdd (k + 1) i.succ)))) 🡒
        ((funcT π F).subst (fun j ↦ Semiterm.bvar (Fin.castAdd (k + 1) j)) 🡒
          (funcT π F).subst (fun j ↦ Semiterm.bvar (Fin.natAdd (k + 1) j))) := by
  simp only [congrSent, LCWQIsoGödelQuote.imply, LCWQIsoGödelQuote.and, quote_conj,
    quote_eq_bvar, quote_operator_bvar]

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma congrSent_subst (F : L₂.Func k) (y z : Term V L₁) (w w' : Fin k → Term V L₁) :
    (⌜congrSent π F⌝ : Semiformula V L₁ ((k + 1) + (k + 1))).subst (Fin.append (y :> w) (z :> w')) =
      (Semiformula.equal y z ⋏ Matrix.conj (fun i ↦ Semiformula.equal (w i) (w' i))) 🡒
        ((funcT π F).subst (y :> w) 🡒 (funcT π F).subst (z :> w')) := by
  rw [quote_congrSent]
  simp [Fin.append_addNat]

end external

section func

omit [L₂.Encodable] [L₂.LORDefinable] in
lemma tprovable_func_exists (F : L₂.Func k) (w : Fin k → Term V L₁) :
    S.internalize V ⊢ Matrix.conj (fun i ↦ (domT π).subst ![w i]) 🡒
      ∃¹ (domT π ⋏ (funcT π F).subst (Semiterm.bvar 0 :> fun i ↦ (w i).bShift)) := by
  have h₁ := tprovable_subst_of_allClosure (S := S) (σ := funcExistsSent π F) w
    (internal_provable_of_outer_provable (V := V) (funcExists_external π F))
  rw [funcExistsSent_subst] at h₁
  exact h₁

omit [L₂.Encodable] [L₂.LORDefinable] in
lemma tprovable_func_unique (F : L₂.Func k) (y z : Term V L₁) (w : Fin k → Term V L₁) :
    S.internalize V ⊢ Matrix.conj (fun i ↦ (domT π).subst ![w i]) ⋏ (domT π).subst ![y] ⋏
      (domT π).subst ![z] ⋏ (funcT π F).subst (y :> w) ⋏ (funcT π F).subst (z :> w) 🡒
        Semiformula.equal y z := by
  have h₁ := tprovable_subst_of_allClosure (S := S) (σ := uniqSent π F) (y :> z :> w)
    (internal_provable_of_outer_provable (V := V) (uniqSent_external π F))
  rw [uniqSent_subst] at h₁
  exact h₁

omit [L₂.Encodable] [L₂.LORDefinable] in
lemma tprovable_func_congr (F : L₂.Func k) (y z : Term V L₁) (w w' : Fin k → Term V L₁) :
    S.internalize V ⊢ Semiformula.equal y z ⋏
      Matrix.conj (fun i ↦ Semiformula.equal (w i) (w' i)) 🡒
        (funcT π F).subst (y :> w) 🡒 (funcT π F).subst (z :> w') := by
  have h₁ := tprovable_subst_of_allClosure (S := S) (σ := congrSent π F)
    (Fin.append (y :> w) (z :> w'))
    (internal_provable_of_outer_provable (V := V) (congrSent_external π F))
  rw [congrSent_subst] at h₁
  exact h₁

end func

end piFacts

/-! ## Translation of typed formulas -/

section typedShapes

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

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

end symbols

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
    definesElement_funcGraph (domT π) (funcT π F) (domT_shift π) (funcT_shift π F)
      (fun i ↦ varEqualT hT (u i)) (tprovable_func_unique π F) (tprovable_func_congr π F)
      (tprovable_func_exists π F) c
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

end termSubst

end FFL.FirstOrder.Arithmetic.Bootstrapping
