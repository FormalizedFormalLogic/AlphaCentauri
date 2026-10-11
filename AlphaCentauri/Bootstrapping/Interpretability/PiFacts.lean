module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.Bootstrapping.Interpretability.Quote
public import AlphaCentauri.ToFoundation.InternalEquality
public import AlphaCentauri.ToFoundation.Provable

/-!
# Internal facts about the domain and the graphs of a direct translation

For a direct translation `π`, the domain formula of `π` is provably nonempty, and the graph of
each function symbol of `π` defines a unique value on the domain, respects equality and is
invariant under the substitution of equal arguments.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  (π : DirectTranslation S L₂)

variable {k : ℕ}

section domain

omit [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq] in
lemma operator_bvar_eq_sentence (o : Semiformula.Operator L₁ 1) :
    (o.operator ![#0] : Semisentence L₁ 1) = o.sentence := by
  simp [Semiformula.Operator.operator, Rewriting.emb]

omit [L₁.Eq] in
lemma shift_quote_typed {n : ℕ} (σ : Semisentence L₁ n) :
    (⌜σ⌝ : Semiformula V L₁ n).shift = ⌜σ⌝ := by
  have h₁ : Rewriting.shift (Rewriting.emb σ : Semiproposition L₁ n) = Rewriting.emb σ := by
    simpa [Rewriting.shifts] using Rewriting.shifts_emb ({σ} : Multiset (Semisentence L₁ n))
  rw [Sentence.typed_quote_def, ← Semiformula.typed_quote_shift, h₁]

/-- The code of the domain formula of `π`. -/
noncomputable abbrev domT : Semiformula V L₁ 1 := ⌜π.domain.sentence⌝


/-- The code of the graph of the function symbol `F` of `π`. -/
noncomputable abbrev funcT (F : L₂.Func k) : Semiformula V L₁ (k + 1) := ⌜(π.func F).sentence⌝

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma domT_shift : (domT π : Semiformula V L₁ 1).shift = domT π :=
  shift_quote_typed _

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma funcT_shift (F : L₂.Func k) : (funcT π F : Semiformula V L₁ (k + 1)).shift = funcT π F :=
  shift_quote_typed _

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

omit [L₁.Eq] in
lemma subst_vec_bvar {n m : ℕ} (w : Fin n → Semiterm V L₁ m) (i : Fin n) :
    (Semiterm.subst w) ⨟ ![Semiterm.bvar i] = ![w i] := by
  funext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp

omit [L₁.Eq] in
lemma subst_vec_cons {n m p : ℕ} (w : Fin n → Semiterm V L₁ m) (a : Fin n)
    (u : Fin p → Fin n) :
    (Semiterm.subst w) ⨟ (Semiterm.bvar a :> fun i ↦ Semiterm.bvar (u i)) =
      (w a :> fun i ↦ w (u i)) := by
  funext j
  cases j using Fin.cases <;> simp

end quote

section external

noncomputable abbrev funcExistsSent (F : L₂.Func k) : Semisentence L₁ k :=
  (Matrix.conj fun i : Fin k ↦ π.domain.operator ![#i]) 🡒
    ∃¹ (π.domain.operator ![#0] ⋏ (π.func F).operator (#0 :> fun i ↦ #i.succ))

omit [L₁.Encodable] [L₁.LORDefinable] [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma funcExists_external (F : L₂.Func k) : S ⊢ ∀¹* (funcExistsSent π F) := by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ _ _ hT
  have h := models_of_provable hT (π.func_defined F)
  simp only [BinderNotation.finSuccItr, Nat.add_zero, Matrix.zero_cons_succ_eq_self, models_iff,
    Semiformula.eval_allClosure, LogicalConnective.HomClass.map_imply, Matrix.conj_hom_prop,
    Semiformula.eval_operator, Matrix.comp₁, Semiterm.val_bvar, Semiformula.eval_existsUnique,
    Nat.succ_eq_add_one, LogicalConnective.HomClass.map_and, Matrix.cons_val_zero,
    LogicalConnective.Prop.and_eq, LogicalConnective.Prop.arrow_eq, funcExistsSent,
    Semiformula.eval_ex] at h ⊢
  intro e' hD
  obtain ⟨x, hx, -⟩ := h e' hD
  exact ⟨x, hx⟩

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma quote_funcExistsSent (F : L₂.Func k) :
    (⌜funcExistsSent π F⌝ : Semiformula V L₁ k) =
      Matrix.conj (fun i ↦ (domT π).subst ![Semiterm.bvar i]) 🡒
        ∃¹ ((domT π).subst ![Semiterm.bvar 0] ⋏
          (funcT π F).subst (Semiterm.bvar 0 :> fun i ↦ Semiterm.bvar i.succ)) := by
  simp only [funcExistsSent, LCWQIsoGödelQuote.imply, LCWQIsoGödelQuote.exs,
    LCWQIsoGödelQuote.and, quote_conj, quote_domain_bvar, quote_operator_cons]

omit [L₁.Eq] in
lemma q_eq_cons (w : Fin k → Term V L₁) :
    SemitermVec.q w = (Semiterm.bvar 0 :> fun i ↦ (w i).bShift) := by
  funext j
  cases j using Fin.cases <;> simp [SemitermVec.q]

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma funcExistsSent_subst (F : L₂.Func k) (w : Fin k → Term V L₁) :
    (⌜funcExistsSent π F⌝ : Semiformula V L₁ k).subst w =
      Matrix.conj (fun i ↦ (domT π).subst ![w i]) 🡒
        ∃¹ (domT π ⋏ (funcT π F).subst (Semiterm.bvar 0 :> fun i ↦ (w i).bShift)) := by
  rw [quote_funcExistsSent]
  simp only [Semiformula.substs_imp, Semiformula.substs_conj, Semiformula.substs_ex,
    Semiformula.substs_and, Semiformula.substs_substs, subst_vec_bvar, q_eq_cons,
    subst_vec_cons]
  simp

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
  have h := models_of_provable hT (π.func_defined F)
  simp only [BinderNotation.finSuccItr, Nat.add_zero, Matrix.zero_cons_succ_eq_self, models_iff,
    Semiformula.eval_allClosure, LogicalConnective.HomClass.map_imply, Matrix.conj_hom_prop,
    Semiformula.eval_operator, Matrix.comp₁, Semiterm.val_bvar, Semiformula.eval_existsUnique,
    Nat.succ_eq_add_one, LogicalConnective.HomClass.map_and, Matrix.cons_val_zero,
    LogicalConnective.Prop.and_eq, LogicalConnective.Prop.arrow_eq, uniqSent, Matrix.comp₂,
    Nat.reduceAdd, Tarski.Structure.eq_iff_eq, Fin.isValue, Matrix.cons_val_one, Fin.Fin1.eq_one,
    Matrix.cons_val_fin_one, and_imp] at h ⊢
  intro e' hW hD0 hD1 hG0 hG1
  obtain ⟨x, -, hu⟩ := h (fun i ↦ e' i.succ.succ) hW
  have v₀ : (FirstOrder.Semiterm.val (L := L₁) (M := M)
        (e' 0 :> fun i ↦ e' i.succ.succ) Empty.elim ∘ FirstOrder.Semiterm.bvar) =
      (FirstOrder.Semiterm.val (L := L₁) (M := M) e' Empty.elim ∘
        (#0 :> fun i : Fin k ↦ #i.succ.succ) : Fin (k + 1) → M) := by
    funext j
    cases j using Fin.cases <;> simp
  have v₁ : (FirstOrder.Semiterm.val (L := L₁) (M := M)
        (e' 1 :> fun i ↦ e' i.succ.succ) Empty.elim ∘ FirstOrder.Semiterm.bvar) =
      (FirstOrder.Semiterm.val (L := L₁) (M := M) e' Empty.elim ∘
        (#1 :> fun i : Fin k ↦ #i.succ.succ) : Fin (k + 1) → M) := by
    funext j
    cases j using Fin.cases <;> simp
  have h₀ := hu (e' 0) ⟨hD0, by rw [v₀]; exact hG0⟩
  have h₁ := hu (e' 1) ⟨hD1, by rw [v₁]; exact hG1⟩
  exact h₀.trans h₁.symm

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
  simp only [Semiformula.substs_imp, Semiformula.substs_conj, Semiformula.substs_and,
    Semiformula.substs_equal, Semiformula.substs_substs, subst_vec_bvar, subst_vec_cons]
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

omit [L₁.Eq] in
lemma subst_vec_fun {n m p : ℕ} (w : Fin n → Semiterm V L₁ m) (u : Fin p → Fin n) :
    (Semiterm.subst w) ⨟ (fun i ↦ Semiterm.bvar (u i)) = fun i ↦ w (u i) := by
  funext i
  simp

private lemma append_addNat_same {α : Type*} {k : ℕ} (s u : Fin k → α) (i : Fin k) :
    Fin.append s u (i.addNat k) = u i := by
  have : i.addNat k = Fin.natAdd k i := Fin.ext (Nat.add_comm _ _)
  rw [this, Fin.append_right]

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma congrSent_subst (F : L₂.Func k) (y z : Term V L₁) (w w' : Fin k → Term V L₁) :
    (⌜congrSent π F⌝ : Semiformula V L₁ ((k + 1) + (k + 1))).subst (Fin.append (y :> w) (z :> w')) =
      (Semiformula.equal y z ⋏ Matrix.conj (fun i ↦ Semiformula.equal (w i) (w' i))) 🡒
        ((funcT π F).subst (y :> w) 🡒 (funcT π F).subst (z :> w')) := by
  rw [quote_congrSent]
  simp only [Semiformula.substs_imp, Semiformula.substs_and, Semiformula.substs_conj,
    Semiformula.substs_equal, Semiformula.substs_substs, subst_vec_fun, Fin.append_left,
    Fin.append_right]
  simp [append_addNat_same]

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

end FFL.FirstOrder.Arithmetic.Bootstrapping
