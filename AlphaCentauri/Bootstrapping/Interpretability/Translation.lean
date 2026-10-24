module

public import AlphaCentauri.ToFoundation.Syntax
public import AlphaCentauri.ToFoundation.DirectTranslation
public import AlphaCentauri.ToFoundation.Quote

/-!
# Internal translation of formulas along a table of operators

A table `tbl` lists the codes of the formulas of a direct translation of a language $L_2$ into a
language $L_1$: its entry `tbl.[0]` is the domain formula, `(tbl.[1]).[⟪k, r⟫]` is the formula
interpreting the `k`-ary relation symbol `r`, and `(tbl.[2]).[⟪k, f⟫]` is the formula of the graph
of the `k`-ary function symbol `f`. Along such a table, `varEqual` sends a coded $L_2$-term to the
coded $L_1$-formula saying that the variable `^#0` is its value, and `translate` sends a coded
$L_2$-formula to its relativized translation, a coded $L_1$-formula.

A table of a direct translation `π` lists the codes of the domain formula of `π`, of the formulas
interpreting the relation symbols and of the formulas of the graphs of the function symbols. Along
such a table, `varEqual` sends the code of a term to the code of its translation by `π`, and
`translate` sends the code of a formula or of a sentence to the code of its translation by `π`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Tables of operators -/

section table

/-- The code of the domain formula listed in the table `tbl`. -/
noncomputable def tableDomain (tbl : V) : V := tbl.[0]

/-- The code of the formula interpreting the `k`-ary relation symbol `r`, listed in `tbl`. -/
noncomputable def tableRel (tbl k r : V) : V := (tbl.[1]).[⟪k, r⟫]

/-- The code of the formula of the graph of the `k`-ary function symbol `f`, listed in `tbl`. -/
noncomputable def tableFunc (tbl k f : V) : V := (tbl.[2]).[⟪k, f⟫]

def tableDomainGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “y tbl. !nthDef y tbl 0”

def tableRelGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y tbl k r. ∃ rs, !nthDef rs tbl 1 ∧ ∃ i, !pairDef i k r ∧ !nthDef y rs i”

def tableFuncGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y tbl k f. ∃ fs, !nthDef fs tbl 2 ∧ ∃ i, !pairDef i k f ∧ !nthDef y fs i”

variable {Γ : SigmaPiDelta} {m : ℕ}

instance tableDomain.defined : 𝚺ᴬ₁-Function₁ (tableDomain : V → V) via tableDomainGraph :=
  .mk fun v ↦ by simp [tableDomainGraph, tableDomain]

instance tableDomain.definable : 𝚺ᴬ₁-Function₁ (tableDomain : V → V) :=
  tableDomain.defined.to_definable

instance tableDomain.definable' : Γᴬ_[m + 1]-Function₁ (tableDomain : V → V) :=
  tableDomain.definable.of_sigmaOne

instance tableRel.defined : 𝚺ᴬ₁-Function₃ (tableRel : V → V → V → V) via tableRelGraph :=
  .mk fun v ↦ by simp [tableRelGraph, tableRel]

instance tableRel.definable : 𝚺ᴬ₁-Function₃ (tableRel : V → V → V → V) :=
  tableRel.defined.to_definable

instance tableRel.definable' : Γᴬ_[m + 1]-Function₃ (tableRel : V → V → V → V) :=
  tableRel.definable.of_sigmaOne

instance tableFunc.defined : 𝚺ᴬ₁-Function₃ (tableFunc : V → V → V → V) via tableFuncGraph :=
  .mk fun v ↦ by simp [tableFuncGraph, tableFunc]

instance tableFunc.definable : 𝚺ᴬ₁-Function₃ (tableFunc : V → V → V → V) :=
  tableFunc.defined.to_definable

instance tableFunc.definable' : Γᴬ_[m + 1]-Function₃ (tableFunc : V → V → V → V) :=
  tableFunc.definable.of_sigmaOne

end table

/-! ## Relocated formulas -/

section relocate

variable (L : Language) [L.Encodable] [L.LORDefinable]

/-- `relocate L i s p` substitutes `^#i` for the bound variable `^#0` of `p` and `^#(s + j)` for
`^#(j + 1)`, for every `j < bv L p`. -/
noncomputable def relocate (i s p : V) : V := subst L (^#i ∷ bvarVec s (bv L p)) p

/-- `domainAt L tbl i` is the domain formula of `tbl` applied to the bound variable `^#i`. -/
noncomputable def domainAt (tbl i : V) : V := subst L ?[^#i] (tableDomain tbl)

/-- `funcTail L tbl k f` is the formula of the graph of the `k`-ary function symbol `f` applied to
`^#k, ^#0, …, ^#(k - 1)`. -/
noncomputable def funcTail (tbl k f : V) : V := subst L (^#k ∷ bvarVec 0 k) (tableFunc tbl k f)

noncomputable def relocateGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y i s p. ∃ b, !qqBvarDef b i ∧ ∃ m, !(bvGraph L) m p ∧ ∃ bs, !bvarVecDef bs s m ∧
    ∃ w, !adjoinDef w b bs ∧ !(substsGraph L) y w p”

noncomputable def domainAtGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y tbl i. ∃ d, !tableDomainGraph d tbl ∧ ∃ b, !qqBvarDef b i ∧ ∃ w, !mkVec₁Def w b ∧
    !(substsGraph L) y w d”

noncomputable def funcTailGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y tbl k f. ∃ g, !tableFuncGraph g tbl k f ∧ ∃ b, !qqBvarDef b k ∧ ∃ bs, !bvarVecDef bs 0 k ∧
    ∃ w, !adjoinDef w b bs ∧ !(substsGraph L) y w g”

variable {L}

variable {Γ : SigmaPiDelta} {m : ℕ}

instance relocate.defined : 𝚺ᴬ₁-Function₃[V] relocate L via relocateGraph L :=
  .mk fun v ↦ by simp [relocateGraph, relocate]

instance relocate.definable : 𝚺ᴬ₁-Function₃[V] relocate L := relocate.defined.to_definable

instance relocate.definable' : Γᴬ_[m + 1]-Function₃[V] relocate L :=
  relocate.definable.of_sigmaOne

lemma relocate_eq_subst {n i s p : V} (hp : IsSemiformula L (n + 1) p) :
    relocate L i s p = subst L (^#i ∷ bvarVec s n) p := by
  have h₁ : IsSemiformula L (bv L p) p := isSemiformula_iff.mpr ⟨hp.isUFormula, le_rfl⟩
  have h₂ : IsUTermVec L (bv L p + 1) (^#i ∷ bvarVec s (bv L p)) :=
    (IsSemitermVec.bvarVec (L := L) (n := s + bv L p) le_rfl).isUTerm.adjoin (by simp)
  have h₃ : IsUTermVec L (n + 1) (^#i ∷ bvarVec s n) :=
    (IsSemitermVec.bvarVec (L := L) (n := s + n) le_rfl).isUTerm.adjoin (by simp)
  rw [relocate]
  apply subst_congr h₁ h₂ h₃ (by simp) hp.bv_le
  intro j hj
  rcases zero_or_succ j with (rfl | ⟨j, rfl⟩)
  · simp
  · have h₄ : j < n := by
      have h₅ : j + 1 < n + 1 := lt_of_lt_of_le hj hp.bv_le
      simpa using h₅
    have h₆ : j < bv L p := lt_trans (by simp) hj
    rw [nth_adjoin_succ, nth_adjoin_succ, nth_bvarVec _ _ _ h₆, nth_bvarVec _ _ _ h₄]

instance domainAt.defined : 𝚺ᴬ₁-Function₂[V] domainAt L via domainAtGraph L :=
  .mk fun v ↦ by simp [domainAtGraph, domainAt]

instance domainAt.definable : 𝚺ᴬ₁-Function₂[V] domainAt L := domainAt.defined.to_definable

instance domainAt.definable' : Γᴬ_[m + 1]-Function₂[V] domainAt L :=
  domainAt.definable.of_sigmaOne

instance funcTail.defined : 𝚺ᴬ₁-Function₃[V] funcTail L via funcTailGraph L :=
  .mk fun v ↦ by simp [funcTailGraph, funcTail]

instance funcTail.definable : 𝚺ᴬ₁-Function₃[V] funcTail L := funcTail.defined.to_definable

instance funcTail.definable' : Γᴬ_[m + 1]-Function₃[V] funcTail L :=
  funcTail.definable.of_sigmaOne

end relocate

/-! ## Vectors of guards -/

section guardVec

variable (L : Language) [L.Encodable] [L.LORDefinable]

noncomputable def guardVec.blueprint : PR.Blueprint 3 where
  zero := .mkSigma “y tbl s w. y = 0”
  succ := .mkSigma
    “y ih k tbl s w. ∃ d, !(domainAtGraph L) d tbl k ∧ ∃ wk, !nthDef wk w k ∧
      ∃ r, !(relocateGraph L) r k s wk ∧ ∃ c, !qqAndDef c d r ∧ !concatDef y ih c”

noncomputable def guardVec.construction : PR.Construction V (guardVec.blueprint L) where
  zero := fun _ ↦ 0
  succ := fun x k ih ↦ concat ih (domainAt L (x 0) k ^⋏ relocate L k (x 1) (x 2).[k])
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

/-- `guardVec L tbl s w k` is the vector whose `j`-th entry, for `j < k`, is the conjunction of
the domain formula of `tbl` at `^#j` and `relocate L j s w.[j]`. -/
noncomputable def guardVec (tbl s w k : V) : V := (guardVec.construction L).result ![tbl, s, w] k

/-- The $\Sigma_1$ graph of `guardVec`, with argument order `(y, tbl, s, w, k)`. -/
noncomputable def guardVecGraph : 𝚺ᴬ₁.Semisentence 5 :=
  (guardVec.blueprint L).resultDef |>.rew (Rew.subst ![#0, #4, #1, #2, #3])

variable {L}

@[simp] lemma guardVec_zero (tbl s w : V) : guardVec L tbl s w 0 = 0 := by
  simp [guardVec, guardVec.construction]

@[simp] lemma guardVec_succ (tbl s w k : V) :
    guardVec L tbl s w (k + 1) =
      concat (guardVec L tbl s w k) (domainAt L tbl k ^⋏ relocate L k s w.[k]) := by
  simp [guardVec, guardVec.construction]

section

variable {Γ : SigmaPiDelta} {m : ℕ}

instance guardVec.defined : 𝚺ᴬ₁-Function₄[V] guardVec L via guardVecGraph L := .mk fun v ↦ by
  simp [(guardVec.construction L).result_defined_iff, guardVecGraph]; rfl

instance guardVec.definable : 𝚺ᴬ₁-Function₄[V] guardVec L := guardVec.defined.to_definable

instance guardVec.definable' : Γᴬ_[m + 1]-Function₄[V] guardVec L :=
  guardVec.definable.of_sigmaOne

end

@[simp] lemma len_guardVec (tbl s w k : V) : len (guardVec L tbl s w k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

lemma nth_guardVec (tbl s w k : V) :
    ∀ j < k, (guardVec L tbl s w k).[j] = domainAt L tbl j ^⋏ relocate L j s w.[j] := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro j hj
    rcases (lt_succ_iff_le.mp hj).lt_or_eq with hlt | rfl
    · rw [guardVec_succ, concat_nth_lt _ _ (by simpa using hlt)]
      exact ih j hlt
    · rw [guardVec_succ, concat_nth_len' _ _ (by simp)]

end guardVec

/-! ## Translation of terms -/

section varEqual

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

namespace VarEqual

variable (L₁)

noncomputable def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma
    “y z tbl. ∃ a, !qqBvarDef a 0 ∧ ∃ b, !qqBvarDef b (z + 1) ∧ ∃ e, !mkVec₂Def e a b ∧
      !qqRelDef y 2 ↑(Encodable.encode (Language.Eq.eq : L₁.Rel 2)) e”
  fvar := .mkSigma
    “y x tbl. ∃ a, !qqBvarDef a 0 ∧ ∃ b, !qqFvarDef b x ∧ ∃ e, !mkVec₂Def e a b ∧
      !qqRelDef y 2 ↑(Encodable.encode (Language.Eq.eq : L₁.Rel 2)) e”
  func := .mkSigma
    “y k f v w tbl. ∃ g, !(guardVecGraph L₁) g tbl (k + 1) w k ∧ ∃ c, !qqConjGraph c g ∧
      ∃ h, !(funcTailGraph L₁) h tbl k f ∧ ∃ i, !(impGraph L₁) i c h ∧ !qqAllsDef y i k”

noncomputable def construction : Language.TermRec.Construction V (blueprint L₁) where
  bvar (_ z) := ^rel 2 (Encodable.encode (Language.Eq.eq : L₁.Rel 2) : V) ?[^#0, ^#(z + 1)]
  fvar (_ x) := ^rel 2 (Encodable.encode (Language.Eq.eq : L₁.Rel 2) : V) ?[^#0, ^&x]
  func (param k f _ w) :=
    qqAlls (imp L₁ (^⋀ guardVec L₁ (param 0) (k + 1) w k) (funcTail L₁ (param 0) k f)) k
  bvar_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]
  fvar_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]
  func_defined := .mk fun v ↦ by simp [blueprint]

end VarEqual

open VarEqual

variable (L₁ L₂)

/-- `varEqual L₁ L₂ tbl t` is the coded $L_1$-formula saying, along the table `tbl`, that the
bound variable `^#0` is the value of the coded $L_2$-term `t`, whose bound variable `^#x` becomes
`^#(x + 1)`. -/
noncomputable def varEqual (tbl t : V) : V := (construction L₁).result L₂ ![tbl] t

/-- `varEqual L₁ L₂ tbl` applied entrywise to the coded `k`-vector `v`. -/
noncomputable def varEqualVec (tbl k v : V) : V := (construction L₁).resultVec L₂ ![tbl] k v

/-- The $\Sigma_1$ graph of `varEqual`, with argument order `(y, tbl, t)`. -/
noncomputable def varEqualGraph : 𝚺ᴬ₁.Semisentence 3 :=
  (blueprint L₁).result L₂ |>.rew <| Rew.subst ![#0, #2, #1]

/-- The $\Sigma_1$ graph of `varEqualVec`, with argument order `(y, tbl, k, v)`. -/
noncomputable def varEqualVecGraph : 𝚺ᴬ₁.Semisentence 4 :=
  (blueprint L₁).resultVec L₂ |>.rew <| Rew.subst ![#0, #2, #3, #1]

variable {L₁ L₂}

section

variable {Γ : SigmaPiDelta} {m : ℕ}

instance varEqual.defined : 𝚺ᴬ₁-Function₂[V] varEqual L₁ L₂ via varEqualGraph L₁ L₂ :=
  .mk fun v ↦ by
    simpa [varEqualGraph, varEqual, Matrix.constant_eq_singleton, Matrix.comp_vecCons'] using
      (construction L₁).result_defined.defined ![v 0, v 2, v 1]

instance varEqual.definable : 𝚺ᴬ₁-Function₂[V] varEqual L₁ L₂ := varEqual.defined.to_definable

instance varEqual.definable' : Γᴬ_[m + 1]-Function₂[V] varEqual L₁ L₂ :=
  varEqual.definable.of_sigmaOne

instance varEqualVec.defined : 𝚺ᴬ₁-Function₃[V] varEqualVec L₁ L₂ via varEqualVecGraph L₁ L₂ :=
  .mk fun v ↦ by
    simpa [varEqualVecGraph, varEqualVec, Matrix.constant_eq_singleton, Matrix.comp_vecCons'] using
      (construction L₁).resultVec_defined.defined ![v 0, v 2, v 3, v 1]

instance varEqualVec.definable : 𝚺ᴬ₁-Function₃[V] varEqualVec L₁ L₂ :=
  varEqualVec.defined.to_definable

instance varEqualVec.definable' : Γᴬ_[m + 1]-Function₃[V] varEqualVec L₁ L₂ :=
  varEqualVec.definable.of_sigmaOne

end

@[simp] lemma varEqual_bvar (tbl z : V) :
    varEqual L₁ L₂ tbl ^#z =
      ^rel 2 (Encodable.encode (Language.Eq.eq : L₁.Rel 2) : V) ?[^#0, ^#(z + 1)] := by
  simp [varEqual, construction]

@[simp] lemma varEqual_fvar (tbl x : V) :
    varEqual L₁ L₂ tbl ^&x =
      ^rel 2 (Encodable.encode (Language.Eq.eq : L₁.Rel 2) : V) ?[^#0, ^&x] := by
  simp [varEqual, construction]

@[simp] lemma varEqual_func {tbl k f v : V} (hf : L₂.IsFunc k f) (hv : IsUTermVec L₂ k v) :
    varEqual L₁ L₂ tbl (^func k f v) =
      qqAlls (imp L₁ (^⋀ guardVec L₁ tbl (k + 1) (varEqualVec L₁ L₂ tbl k v) k)
        (funcTail L₁ tbl k f)) k := by
  simp [varEqual, varEqualVec, construction, hf, hv]

lemma varEqual_not_uterm {tbl t : V} (ht : ¬IsUTerm L₂ t) : varEqual L₁ L₂ tbl t = 0 :=
  (construction L₁).result_prop_not _ _ ht

@[simp] lemma len_varEqualVec {tbl k v : V} (hv : IsUTermVec L₂ k v) :
    len (varEqualVec L₁ L₂ tbl k v) = k := (construction L₁).resultVec_lh L₂ _ hv

@[simp] lemma nth_varEqualVec {tbl k v i : V} (hv : IsUTermVec L₂ k v) (hi : i < k) :
    (varEqualVec L₁ L₂ tbl k v).[i] = varEqual L₁ L₂ tbl v.[i] :=
  (construction L₁).nth_resultVec L₂ _ hv hi

@[simp] lemma varEqualVec_nil (tbl : V) : varEqualVec L₁ L₂ tbl 0 0 = 0 :=
  (construction L₁).resultVec_nil L₂ _

lemma varEqualVec_cons {tbl k t v : V} (ht : IsUTerm L₂ t) (hv : IsUTermVec L₂ k v) :
    varEqualVec L₁ L₂ tbl (k + 1) (t ∷ v) = varEqual L₁ L₂ tbl t ∷ varEqualVec L₁ L₂ tbl k v :=
  (construction L₁).resultVec_cons L₂ ![tbl] hv ht

end varEqual

/-! ## Translation of formulas -/

section translate

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

variable (L₁ L₂)

/-- `translateRel L₁ L₂ tbl k R v` is the translation along `tbl` of the coded atomic formula
`^rel k R v`. -/
noncomputable def translateRel (tbl k R v : V) : V :=
  qqAlls (imp L₁ (^⋀ guardVec L₁ tbl k (varEqualVec L₁ L₂ tbl k v) k) (tableRel tbl k R)) k

/-- The $\Sigma_1$ graph of `translateRel`, with argument order `(y, tbl, k, R, v)`. -/
noncomputable def translateRelGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “y tbl k R v. ∃ w, !(varEqualVecGraph L₁ L₂) w tbl k v ∧ ∃ g, !(guardVecGraph L₁) g tbl k w k ∧
    ∃ c, !qqConjGraph c g ∧ ∃ r, !tableRelGraph r tbl k R ∧ ∃ i, !(impGraph L₁) i c r ∧
    !qqAllsDef y i k”

variable {L₁ L₂}

section

variable {Γ : SigmaPiDelta} {m : ℕ}

instance translateRel.defined :
    𝚺ᴬ₁-Function₄[V] translateRel L₁ L₂ via translateRelGraph L₁ L₂ :=
  .mk fun v ↦ by simp [translateRelGraph, translateRel]

instance translateRel.definable : 𝚺ᴬ₁-Function₄[V] translateRel L₁ L₂ :=
  translateRel.defined.to_definable

instance translateRel.definable' : Γᴬ_[m + 1]-Function₄[V] translateRel L₁ L₂ :=
  translateRel.definable.of_sigmaOne

end

namespace Translate

variable (L₁ L₂)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := translateRelGraph L₁ L₂
  nrel := .mkSigma “y tbl k R v. ∃ r, !(translateRelGraph L₁ L₂) r tbl k R v ∧ !(negGraph L₁) y r”
  verum := .mkSigma “y tbl. !qqVerumDef y”
  falsum := .mkSigma “y tbl. !qqFalsumDef y”
  and := .mkSigma “y tbl p q p' q'. !qqAndDef y p' q'”
  or := .mkSigma “y tbl p q p' q'. !qqOrDef y p' q'”
  all := .mkSigma
    “y tbl p ys. ∃ d, !(domainAtGraph L₁) d tbl 0 ∧ ∃ p', !nthDef p' ys 0 ∧
      ∃ i, !(impGraph L₁) i d p' ∧ !qqAllDef y i”
  exs := .mkSigma
    “y tbl p ys. ∃ d, !(domainAtGraph L₁) d tbl 0 ∧ ∃ p', !nthDef p' ys 0 ∧
      ∃ c, !qqAndDef c d p' ∧ !qqExsDef y c”

noncomputable def construction : UformulaRec1.Construction V (blueprint L₁ L₂) where
  rel tbl := fun k R v ↦ translateRel L₁ L₂ tbl k R v
  nrel tbl := fun k R v ↦ neg L₁ (translateRel L₁ L₂ tbl k R v)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ := fun _ _ p q ↦ p ^⋏ q
  or _ := fun _ _ p q ↦ p ^⋎ q
  all tbl := fun _ ys ↦ ^∀ imp L₁ (domainAt L₁ tbl 0) ys.[0]
  exs tbl := fun _ ys ↦ ^∃ (domainAt L₁ tbl 0 ^⋏ ys.[0])
  rel_defined := translateRel.defined
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]

end Translate

open Translate

variable (L₁ L₂)

/-- `translate L₁ L₂ tbl p` is the translation along `tbl` of the coded $L_2$-formula `p` into a
coded $L_1$-formula, with quantifiers relativized to the domain formula of `tbl`. -/
noncomputable def translate (tbl p : V) : V := (construction L₁ L₂).result L₂ tbl p

/-- The $\Sigma_1$ graph of `translate`, with argument order `(y, tbl, p)`. -/
noncomputable def translateGraph : 𝚺ᴬ₁.Semisentence 3 := (blueprint L₁ L₂).result L₂

variable {L₁ L₂}

section

variable {Γ : SigmaPiDelta} {m : ℕ}

instance translate.defined : 𝚺ᴬ₁-Function₂[V] translate L₁ L₂ via translateGraph L₁ L₂ :=
  (construction L₁ L₂).result_defined

instance translate.definable : 𝚺ᴬ₁-Function₂[V] translate L₁ L₂ := translate.defined.to_definable

instance translate.definable' : Γᴬ_[m + 1]-Function₂[V] translate L₁ L₂ :=
  translate.definable.of_sigmaOne

end

@[simp] lemma translate_rel {tbl k R v : V} (hR : L₂.IsRel k R) (hv : IsUTermVec L₂ k v) :
    translate L₁ L₂ tbl (^rel k R v) = translateRel L₁ L₂ tbl k R v := by
  simp [translate, hR, hv, construction]

@[simp] lemma translate_nrel {tbl k R v : V} (hR : L₂.IsRel k R) (hv : IsUTermVec L₂ k v) :
    translate L₁ L₂ tbl (^nrel k R v) = neg L₁ (translateRel L₁ L₂ tbl k R v) := by
  simp [translate, hR, hv, construction]

@[simp] lemma translate_verum (tbl : V) : translate L₁ L₂ tbl ^⊤ = ^⊤ := by
  simp [translate, construction]

@[simp] lemma translate_falsum (tbl : V) : translate L₁ L₂ tbl ^⊥ = ^⊥ := by
  simp [translate, construction]

@[simp] lemma translate_and {tbl p q : V} (hp : IsUFormula L₂ p) (hq : IsUFormula L₂ q) :
    translate L₁ L₂ tbl (p ^⋏ q) = translate L₁ L₂ tbl p ^⋏ translate L₁ L₂ tbl q := by
  simp [translate, hp, hq, construction]

@[simp] lemma translate_or {tbl p q : V} (hp : IsUFormula L₂ p) (hq : IsUFormula L₂ q) :
    translate L₁ L₂ tbl (p ^⋎ q) = translate L₁ L₂ tbl p ^⋎ translate L₁ L₂ tbl q := by
  simp [translate, hp, hq, construction]

@[simp] lemma translate_all {tbl p : V} (hp : IsUFormula L₂ p) :
    translate L₁ L₂ tbl (^∀ p) = ^∀ imp L₁ (domainAt L₁ tbl 0) (translate L₁ L₂ tbl p) := by
  simp [translate, hp, construction]

@[simp] lemma translate_exs {tbl p : V} (hp : IsUFormula L₂ p) :
    translate L₁ L₂ tbl (^∃ p) = ^∃ (domainAt L₁ tbl 0 ^⋏ translate L₁ L₂ tbl p) := by
  simp [translate, hp, construction]

lemma translate_not_uformula {tbl p : V} (hp : ¬IsUFormula L₂ p) : translate L₁ L₂ tbl p = 0 :=
  (construction L₁ L₂).result_prop_not _ hp

end translate

/-! ## Quoted formulas -/

section relocateQuote

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma relocate_quote {m l : ℕ} (ψ : Semiproposition L (m + 1)) (x : Fin l) (s : ℕ)
    (y : Fin m → Fin l) (hy : ∀ j, (y j : ℕ) = s + j) :
    relocate L (x : V) (s : V) ⌜ψ⌝ =
      ⌜(Rew.subst (#x :> fun j ↦ #(y j)) ▹ ψ : Semiproposition L l)⌝ := by
  have hψ : IsSemiformula L ((m : V) + 1) (⌜ψ⌝ : V) := by
    simpa using Semiformula.quote_isSemiformula (V := V) ψ
  rw [relocate_eq_subst hψ, Semiformula.quote_substs]
  congr 1
  rw [eq_matrixToVec_iff]
  refine ⟨by simp, fun i ↦ ?_⟩
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp [nth_bvarVec _ _ _ (show (j : V) < m by simp), hy]

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

end relocateQuote

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
