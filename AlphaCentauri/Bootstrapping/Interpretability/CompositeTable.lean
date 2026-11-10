module

public import AlphaCentauri.Bootstrapping.Interpretability.Soundness

/-!
# The composite table

For a table `tbl₁` of a translation of $L_2$ into $L_1$ and a table `tbl₂` of a translation of
$L_3$ into $L_2$, the composite table has as domain formula the conjunction of the domain formula
of `tbl₁` and the translation along `tbl₁` of the domain formula of `tbl₂`, and as the entries of
the symbols the translations along `tbl₁` of the entries of `tbl₂`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

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

end FFL.FirstOrder.Arithmetic.Bootstrapping
