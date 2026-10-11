module

public import AlphaCentauri.Bootstrapping.Interpretability.Translation
public import AlphaCentauri.Bootstrapping.Syntax.SubstCongruence
public import AlphaCentauri.ToFoundation.DirectTranslation
public import AlphaCentauri.ToFoundation.Quote

/-!
# The internal translation of quoted formulas

A table of a direct translation `π` lists the codes of the domain formula of `π`, of the formulas
interpreting the relation symbols and of the formulas of the graphs of the function symbols. Along
such a table, `varEqual` sends the code of a term to the code of its translation by `π`, and
`translate` sends the code of a formula or of a sentence to the code of its translation by `π`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section relocate

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma relocate_quote {m l : ℕ} (ψ : Semiproposition L (m + 1)) (x : Fin l) (s : ℕ)
    (y : Fin m → Fin l) (hy : ∀ j, (y j : ℕ) = s + j) :
    relocate L (x : V) (s : V) ⌜ψ⌝ =
      ⌜(Rew.subst (#x :> fun j ↦ #(y j)) ▹ ψ : Semiproposition L l)⌝ := by
  have hψ : IsSemiformula L ↑(m + 1) (⌜ψ⌝ : V) := Semiformula.quote_isSemiformula ψ
  have hw : IsUTermVec L (bv L ⌜ψ⌝ + 1) (^#(x : V) ∷ bvarVec (s : V) (bv L ⌜ψ⌝)) :=
    (IsSemitermVec.bvarVec (L := L) le_rfl).isUTerm.adjoin (by simp)
  let w : Fin (m + 1) → SyntacticSemiterm L l := #x :> fun j ↦ #(y j)
  have hw' : IsUTermVec L ↑(m + 1) (matrixToVec fun i ↦ (⌜w i⌝ : V)) :=
    (SemitermVec.isSemitermVec fun i ↦ (⌜w i⌝ : Bootstrapping.Semiterm V L l)).isUTerm
  rw [relocate, Semiformula.quote_substs]
  apply subst_congr hψ.isUFormula.isSemiformula hw hw' (by simp) hψ.bv_le
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp [Matrix.vecHead, w]
  · have hi' : i < (m : V) := by simpa using lt_of_lt_of_le hi hψ.bv_le
    obtain ⟨j, rfl⟩ := eq_fin_of_lt_nat hi'
    rw [nth_adjoin_succ, nth_bvarVec _ _ _ (lt_trans (by simp) hi), matrixToVec_succ,
      nth_adjoin_succ]
    simp [Matrix.vecTail, w, hy]

lemma isUTermVec_matrixToVec_quote {n k : ℕ} (v : Fin k → SyntacticSemiterm L n) :
    IsUTermVec L (k : V) (matrixToVec fun i ↦ (⌜v i⌝ : V)) :=
  (SemitermVec.isSemitermVec fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V L n)).isUTerm

lemma bvarVec_zero_eq_matrixToVec (l k : ℕ) :
    bvarVec (0 : V) k =
      matrixToVec fun i : Fin k ↦ (⌜(#(i.addCast l) : SyntacticSemiterm L (l + k))⌝ : V) := by
  rw [eq_matrixToVec_iff]
  constructor
  · simp
  · intro i
    rw [nth_bvarVec _ _ _ (by simp)]
    simp

end relocate

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]

/-- `tbl` is a table of the direct translation `π`: it lists the codes of the domain formula of
`π`, of the formulas interpreting the relation symbols and of the formulas of the graphs of the
function symbols. -/
structure IsTableOf (π : DirectTranslation T L₂) (tbl : V) : Prop where
  domain : tableDomain tbl = ⌜π.domain.sentence⌝
  rel {k : ℕ} (R : L₂.Rel k) : tableRel tbl k ⌜R⌝ = ⌜(π.rel R).sentence⌝
  func {k : ℕ} (f : L₂.Func k) : tableFunc tbl k ⌜f⌝ = ⌜(π.func f).sentence⌝

namespace IsTableOf

variable {π : DirectTranslation T L₂} {tbl : V}

section

omit [L₂.LORDefinable]

lemma domainAt_quote (h : IsTableOf π tbl) {l : ℕ} (x : Fin l) :
    domainAt L₁ tbl (x : V) = ⌜(π.domain.operator ![#x] : Semiproposition L₁ l)⌝ := by
  rw [domainAt, h.domain, Semiformula.Operator.operator, Semiformula.quote_substs,
    Sentence.quote_def]
  simp [Matrix.vecHead, Matrix.vecTail]

lemma guardVec_quote (h : IsTableOf π tbl) {m l k : ℕ} (ψ : Fin k → Semiproposition L₁ (m + 1))
    (s : ℕ) (y : Fin m → Fin (l + k)) (hy : ∀ j, (y j : ℕ) = s + j) :
    guardVec L₁ tbl (s : V) (matrixToVec fun i ↦ (⌜ψ i⌝ : V)) (k : V) =
      matrixToVec fun i ↦ (⌜π.domain.operator ![#(i.addCast l)] ⋏
        Rew.subst (#(i.addCast l) :> fun j ↦ #(y j)) ▹ ψ i⌝ : V) := by
  rw [eq_matrixToVec_iff]
  constructor
  · simp
  · intro i
    have hd := h.domainAt_quote (i.addCast l)
    have hr := relocate_quote (V := V) (ψ i) (i.addCast l) s y hy
    simp only [Fin.addCast_val] at hd hr
    rw [nth_guardVec _ _ _ _ _ (by simp), matrixToVec_nth, Semiformula.quote_and, hd, hr]

lemma tableRel_eq_quote (h : IsTableOf π tbl) {n k : ℕ} (R : L₂.Rel k) :
    tableRel tbl (k : V) ⌜R⌝ =
      ⌜((π.rel R).operator fun i ↦ #(i.addCast n) : Semiproposition L₁ (n + k))⌝ := by
  rw [h.rel, Semiformula.Operator.operator, Semiformula.quote_substs,
    ← bvarVec_zero_eq_matrixToVec, Sentence.quote_def,
    subst_eq_self (Semiformula.quote_isSemiformula _) (IsSemitermVec.bvarVec (by simp))
      (fun i hi ↦ by simp [nth_bvarVec _ _ _ hi])]

lemma funcTail_eq_quote (h : IsTableOf π tbl) {n k : ℕ} (f : L₂.Func k) :
    funcTail L₁ tbl (k : V) ⌜f⌝ = ⌜((π.func f).operator
      (#((0 : Fin (n + 1)).addNat k) :> fun i ↦ #(i.addCast (n + 1))) :
        Semiproposition L₁ (n + 1 + k))⌝ := by
  rw [funcTail, h.func, Semiformula.Operator.operator, Semiformula.quote_substs,
    Sentence.quote_def, matrixToVec_succ, bvarVec_zero_eq_matrixToVec (L := L₁) (n + 1) k]
  simp [Matrix.vecHead, Matrix.vecTail, Function.comp_def]

end

private lemma varEqualVec_quote_of {n k : ℕ} {v : Fin k → SyntacticSemiterm L₂ n}
    (H : ∀ i, varEqual L₁ L₂ tbl (⌜v i⌝ : V) = ⌜π.varEqual (v i)⌝) :
    varEqualVec L₁ L₂ tbl (k : V) (matrixToVec fun i ↦ (⌜v i⌝ : V)) =
      matrixToVec fun i ↦ (⌜π.varEqual (v i)⌝ : V) := by
  have hv := isUTermVec_matrixToVec_quote (V := V) v
  rw [eq_matrixToVec_iff]
  constructor
  · exact (len_varEqualVec hv).symm
  · intro i
    rw [nth_varEqualVec hv (by simp), matrixToVec_nth, H]

lemma varEqual_quote (h : IsTableOf π tbl) {n : ℕ} (t : SyntacticSemiterm L₂ n) :
    varEqual L₁ L₂ tbl (⌜t⌝ : V) = ⌜π.varEqual t⌝ := by
  induction t with
  | bvar x =>
    simp [DirectTranslation.varEqual, Semiformula.Operator.operator,
      Semiformula.Operator.Eq.sentence_eq, Matrix.vecHead, Matrix.vecTail, quote_rel_def]
  | fvar x =>
    simp [DirectTranslation.varEqual, Semiformula.Operator.operator,
      Semiformula.Operator.Eq.sentence_eq, Matrix.vecHead, Matrix.vecTail, quote_rel_def]
  | func f v ih =>
    rename_i k
    have hG := h.guardVec_quote (fun i ↦ π.varEqual (v i)) (k + 1)
      (fun j ↦ (j.addNat 1).addNat k) (fun j ↦ by simp [add_comm, add_left_comm])
    rw [Nat.cast_succ] at hG
    change varEqual L₁ L₂ tbl (^func (k : V) ⌜f⌝ (matrixToVec fun i ↦ (⌜v i⌝ : V))) = _
    rw [varEqual_func (by simp) (isUTermVec_matrixToVec_quote v), varEqualVec_quote_of ih, hG,
      h.funcTail_eq_quote, DirectTranslation.varEqual, Semiformula.quote_allItr,
      Semiformula.quote_imp, Semiformula.quote_conj]

lemma translateRel_quote (h : IsTableOf π tbl) {n k : ℕ} (R : L₂.Rel k)
    (v : Fin k → SyntacticSemiterm L₂ n) :
    translateRel L₁ L₂ tbl (k : V) ⌜R⌝ (matrixToVec fun i ↦ (⌜v i⌝ : V)) =
      ⌜π.translateRel R v⌝ := by
  rw [translateRel, varEqualVec_quote_of fun i ↦ h.varEqual_quote (v i),
    h.guardVec_quote (fun i ↦ π.varEqual (v i)) k (fun j ↦ j.addNat k)
      (fun j ↦ by simp [add_comm]),
    h.tableRel_eq_quote (n := n) R, DirectTranslation.translateRel, Semiformula.quote_allItr,
    Semiformula.quote_imp, Semiformula.quote_conj]

lemma translate_quote (h : IsTableOf π tbl) {n : ℕ} (φ : Semiproposition L₂ n) :
    translate L₁ L₂ tbl (⌜φ⌝ : V) = ⌜π.translate φ⌝ := by
  induction φ using Semiformula.rec' with
  | hrel R v =>
    change translate L₁ L₂ tbl (^rel _ ⌜R⌝ (matrixToVec fun i ↦ (⌜v i⌝ : V))) = _
    rw [translate_rel (by simp) (isUTermVec_matrixToVec_quote v), h.translateRel_quote,
      DirectTranslation.translate_rel]
  | hnrel R v =>
    change translate L₁ L₂ tbl (^nrel _ ⌜R⌝ (matrixToVec fun i ↦ (⌜v i⌝ : V))) = _
    rw [translate_nrel (by simp) (isUTermVec_matrixToVec_quote v), h.translateRel_quote,
      DirectTranslation.translate_nrel, Semiformula.quote_neg]
  | hverum => simp
  | hfalsum => simp
  | hand φ ψ ihφ ihψ =>
    rw [Semiformula.quote_and, translate_and (Semiformula.quote_isSemiformula φ).isUFormula
      (Semiformula.quote_isSemiformula ψ).isUFormula, ihφ, ihψ]
    simp
  | hor φ ψ ihφ ihψ =>
    rw [Semiformula.quote_or, translate_or (Semiformula.quote_isSemiformula φ).isUFormula
      (Semiformula.quote_isSemiformula ψ).isUFormula, ihφ, ihψ]
    simp
  | hall φ ih =>
    rw [Semiformula.quote_all, translate_all (Semiformula.quote_isSemiformula φ).isUFormula, ih]
    simp [DirectTranslation.translate_all, DirectTranslation.fal, ball,
      ← h.domainAt_quote (0 : Fin (_ + 1))]
  | hexs φ ih =>
    rw [Semiformula.quote_ex, translate_exs (Semiformula.quote_isSemiformula φ).isUFormula, ih]
    simp [DirectTranslation.translate_ex, DirectTranslation.exs, bexs,
      ← h.domainAt_quote (0 : Fin (_ + 1))]

lemma translate_quote_sentence (h : IsTableOf π tbl) {n : ℕ} (σ : Semisentence L₂ n) :
    translate L₁ L₂ tbl (⌜σ⌝ : V) = ⌜π.translate σ⌝ := by
  rw [Sentence.quote_def, h.translate_quote, DirectTranslation.translate_emb, Sentence.quote_def]

end IsTableOf

end FFL.FirstOrder.Arithmetic.Bootstrapping
