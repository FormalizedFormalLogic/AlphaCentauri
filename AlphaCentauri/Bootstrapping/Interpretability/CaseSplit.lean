module

public import AlphaCentauri.Bootstrapping.Interpretability.Composition
public import AlphaCentauri.Bootstrapping.Interpretability.Identity
public import AlphaCentauri.Bootstrapping.Interpretability.Soundness
public import AlphaCentauri.Bootstrapping.Interpretability.TranslationTable
public import AlphaCentauri.Bootstrapping.Proof.Deduction

/-!
# The case-split table

For a sentence `φ` and two tables, the case-split table has as each entry the formula
`(φ ∧ e₁) ∨ (¬φ ∧ e₂)` built from the corresponding entries `e₁` and `e₂` of the two tables.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding



open _root_.FFL.Entailment

section caseCode

variable (L : Language) [L.Encodable] [L.LORDefinable]

/-- The code of `(σ ∧ p) ∨ (¬σ ∧ q)`. -/
noncomputable def caseCode (s p q : V) : V := (s ^⋏ p) ^⋎ (neg L s ^⋏ q)

/-- The $\Sigma_1$ graph of `caseCode`, with argument order `(y, s, p, q)`. -/
noncomputable def caseCodeGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y s p q. ∃ n, !(negGraph L) n s ∧ ∃ a, !qqAndDef a s p ∧ ∃ b, !qqAndDef b n q ∧
    !qqOrDef y a b”

noncomputable def caseVec.blueprint : PR.Blueprint 3 where
  zero := .mkSigma “y s u v. y = 0”
  succ := .mkSigma
    “y ih k s u v. ∃ a, !nthDef a u k ∧ ∃ b, !nthDef b v k ∧ ∃ c, !(caseCodeGraph L) c s a b ∧
      !concatDef y ih c”

variable {L}

instance caseCode.defined : 𝚺ᴬ₁-Function₃[V] caseCode L via caseCodeGraph L :=
  .mk fun v ↦ by simp [caseCodeGraph, caseCode]

variable (L)

noncomputable def caseVec.construction : PR.Construction V (caseVec.blueprint L) where
  zero := fun _ ↦ 0
  succ := fun x k ih ↦ concat ih (caseCode L (x 0) (x 1).[k] (x 2).[k])
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

/-- `caseVec L s u v k` is the vector of length `k` whose `j`-th entry is
`caseCode L s u.[j] v.[j]`. -/
noncomputable def caseVec (s u v k : V) : V := (caseVec.construction L).result ![s, u, v] k

/-- The table whose entries are `(σ ∧ e₁) ∨ (¬σ ∧ e₂)` for the entries `e₁` of `tbl₁` and `e₂` of
`tbl₂`. -/
noncomputable def caseTable (s tbl₁ tbl₂ : V) : V :=
  ?[caseCode L s tbl₁.[0] tbl₂.[0], caseVec L s tbl₁.[1] tbl₂.[1] (len tbl₁.[1]),
    caseVec L s tbl₁.[2] tbl₂.[2] (len tbl₁.[2])]

/-- The $\Sigma_1$ graph of `caseVec`, with argument order `(y, s, u, v, k)`. -/
noncomputable def caseVecGraph : 𝚺ᴬ₁.Semisentence 5 :=
  (caseVec.blueprint L).resultDef |>.rew (Rew.subst ![#0, #4, #1, #2, #3])

variable {L}

instance caseCode.definable : 𝚺ᴬ₁-Function₃[V] caseCode L := caseCode.defined.to_definable

instance caseVec.defined : 𝚺ᴬ₁-Function₄[V] caseVec L via caseVecGraph L := .mk fun v ↦ by
  simp [(caseVec.construction L).result_defined_iff, caseVecGraph]; rfl

instance caseVec.definable : 𝚺ᴬ₁-Function₄[V] caseVec L := caseVec.defined.to_definable

@[simp] lemma caseVec_zero (s u v : V) : caseVec L s u v 0 = 0 := by
  simp [caseVec, caseVec.construction]

@[simp] lemma caseVec_succ (s u v k : V) :
    caseVec L s u v (k + 1) = concat (caseVec L s u v k) (caseCode L s u.[k] v.[k]) := by
  simp [caseVec, caseVec.construction]

@[simp] lemma len_caseVec (s u v k : V) : len (caseVec L s u v k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

lemma nth_caseVec (s u v k : V) :
    ∀ j < k, (caseVec L s u v k).[j] = caseCode L s u.[j] v.[j] := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro j hj
    rcases (lt_succ_iff_le.mp hj).lt_or_eq with hlt | rfl
    · rw [caseVec_succ, concat_nth_lt _ _ (by simpa using hlt)]
      exact ih j hlt
    · rw [caseVec_succ, concat_nth_len' _ _ (by simp)]

lemma tableDomain_caseTable (s tbl₁ tbl₂ : V) :
    tableDomain (caseTable L s tbl₁ tbl₂) = caseCode L s (tableDomain tbl₁) (tableDomain tbl₂) := by
  simp [caseTable, tableDomain]

lemma tableRel_caseTable {s tbl₁ tbl₂ k r : V} (h : ⟪k, r⟫ < len tbl₁.[1]) :
    tableRel (caseTable L s tbl₁ tbl₂) k r =
      caseCode L s (tableRel tbl₁ k r) (tableRel tbl₂ k r) := by
  simp [caseTable, tableRel, nth_caseVec _ _ _ _ _ h]

lemma tableFunc_caseTable {s tbl₁ tbl₂ k f : V} (h : ⟪k, f⟫ < len tbl₁.[2]) :
    tableFunc (caseTable L s tbl₁ tbl₂) k f =
      caseCode L s (tableFunc tbl₁ k f) (tableFunc tbl₂ k f) := by
  simp [caseTable, tableFunc, nth_caseVec _ _ _ _ _ h]

end caseCode

section sentence

variable (φ : ArithmeticSentence) {L₂ : Language} [L₂.Encodable] [L₂.LORDefinable] {tbl₁ tbl₂ : V}

lemma IsSemiformula.caseCode {n p q : V} (hp : IsSemiformula ℒₒᵣ n p)
    (hq : IsSemiformula ℒₒᵣ n q) : IsSemiformula ℒₒᵣ n (caseCode ℒₒᵣ ⌜φ⌝ p q) := by
  have hφ : IsSemiformula ℒₒᵣ n (⌜φ⌝ : V) := (Sentence.quote_isSemiformula₀ φ).weaken (by simp)
  simp [Bootstrapping.caseCode, hφ, hp, hq]

lemma shift_caseCode {n p q : V} (hp : IsSemiformula ℒₒᵣ n p) (hq : IsSemiformula ℒₒᵣ n q) :
    shift ℒₒᵣ (caseCode ℒₒᵣ ⌜φ⌝ p q) = caseCode ℒₒᵣ ⌜φ⌝ (shift ℒₒᵣ p) (shift ℒₒᵣ q) := by
  have hφ : IsSemiformula ℒₒᵣ 0 (⌜φ⌝ : V) := Sentence.quote_isSemiformula₀ φ
  simp [Bootstrapping.caseCode, hp.isUFormula, hq.isUFormula, hφ.isUFormula, shift_neg hφ]

/-- The case-split table of two tables is a table. -/
lemma IsTable.caseTable (hT₁ : IsTable ℒₒᵣ L₂ tbl₁) (hT₂ : IsTable ℒₒᵣ L₂ tbl₂) :
    IsTable ℒₒᵣ L₂ (caseTable ℒₒᵣ ⌜φ⌝ tbl₁ tbl₂) where
  domain := by
    rw [tableDomain_caseTable]
    exact IsSemiformula.caseCode φ hT₁.domain hT₂.domain
  domain_shift := by
    rw [tableDomain_caseTable, shift_caseCode φ hT₁.domain hT₂.domain, hT₁.domain_shift,
      hT₂.domain_shift]
  rel h := by
    rw [tableRel_caseTable (hT₁.lt_len_rel h)]
    exact IsSemiformula.caseCode φ (hT₁.rel h) (hT₂.rel h)
  rel_shift h := by
    rw [tableRel_caseTable (hT₁.lt_len_rel h), shift_caseCode φ (hT₁.rel h) (hT₂.rel h),
      hT₁.rel_shift h, hT₂.rel_shift h]
  func h := by
    rw [tableFunc_caseTable (hT₁.lt_len_func h)]
    exact IsSemiformula.caseCode φ (hT₁.func h) (hT₂.func h)
  func_shift h := by
    rw [tableFunc_caseTable (hT₁.lt_len_func h), shift_caseCode φ (hT₁.func h) (hT₂.func h),
      hT₁.func_shift h, hT₂.func_shift h]

section

variable (hT₁ : IsTable ℒₒᵣ L₂ tbl₁) (hT₂ : IsTable ℒₒᵣ L₂ tbl₂)

lemma IsTable.caseTable_domT_val :
    (hT₁.caseTable φ hT₂).domT.val = caseCode ℒₒᵣ ⌜φ⌝ hT₁.domT.val hT₂.domT.val := by
  simp only [IsTable.domT_val, tableDomain_caseTable]

lemma IsTable.caseTable_relT_val {k : ℕ} (R : L₂.Rel k) :
    ((hT₁.caseTable φ hT₂).relT R).val = caseCode ℒₒᵣ ⌜φ⌝ (hT₁.relT R).val (hT₂.relT R).val := by
  simp only [IsTable.relT_val, tableRel_caseTable (hT₁.lt_len_rel (codeIn_rel_quote R))]

lemma IsTable.caseTable_funcT_val {k : ℕ} (F : L₂.Func k) :
    ((hT₁.caseTable φ hT₂).funcT F).val =
      caseCode ℒₒᵣ ⌜φ⌝ (hT₁.funcT F).val (hT₂.funcT F).val := by
  simp only [IsTable.funcT_val, tableFunc_caseTable (hT₁.lt_len_func (codeIn_func_quote F))]

end

lemma subst_eq_of_val_eq_caseCode {n : ℕ} {e e₁ e₂ : Semiformula V ℒₒᵣ n}
    (h : e.val = caseCode ℒₒᵣ ⌜φ⌝ e₁.val e₂.val) (w : SemitermVec V ℒₒᵣ n 0) :
    e.subst w = ((⌜φ⌝ : Formula V ℒₒᵣ) ⋏ e₁.subst w) ⋎ (∼⌜φ⌝ ⋏ e₂.subst w) := by
  have hφ : IsSemiformula ℒₒᵣ 0 (⌜φ⌝ : V) := Sentence.quote_isSemiformula₀ φ
  have hw : IsUTermVec ℒₒᵣ (n : V) w.val := w.isSemitermVec.isUTerm
  have h₁ : subst ℒₒᵣ w.val (⌜φ⌝ : V) = ⌜φ⌝ :=
    subst_eq_self_of_le hφ hw (by simp) (by simp)
  ext
  rw [Semiformula.val_substs, h]
  simp [Bootstrapping.caseCode, Semiformula.val_substs, e₁.isSemiformula.isUFormula,
    e₂.isSemiformula.isUFormula, ← Sentence.quote_eq, h₁,
    substs_neg (hφ.weaken (by simp : (0 : V) ≤ n)) w.isSemitermVec]

end sentence

end

end Bootstrapping
end FFL.FirstOrder.Arithmetic
