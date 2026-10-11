module

public import AlphaCentauri.Bootstrapping.Completeness.HenkinRepresentative

/-!
# The arithmetical operators of the Henkin translation

The domain, relation and function operators of the translation of a language $L$ into
arithmetic that is read off from the Henkin set of a theory $S$: the domain consists of the
representatives of provably equal free variables, a relation holds of representatives when the
atomic formula on the corresponding free variables is in the Henkin set, and a function symbol is
interpreted by the graph given by the equation of its application with a free variable.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Bounding

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq]

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma eq_matrixToVec_iff {k : ℕ} {w : V} {u : Fin k → V} :
    w = matrixToVec u ↔ (k : V) = len w ∧ ∀ i : Fin k, w.[((i : ℕ) : V)] = u i := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h₁, h₂⟩
    apply nth_ext' (k : V) h₁.symm (by simp)
    intro i hi
    obtain ⟨i, rfl⟩ := eq_fin_of_lt_nat hi
    simp [h₂]

end

variable (S : Theory L) [S.Δ₁]

/-- The $\Pi_2$ formula of `henkinDomain S`. -/
noncomputable def henkinDomainDef : 𝚷ᴬ_[2].Semisentence 1 := .mkPi
  “a. ∀ y < a, ∀ t, !qqFvarDef t y → ∀ s, !qqFvarDef s a → ∀ e, !mkVec₂Def e t s →
    ∀ c, !qqRelDef c 2 ↑(Encodable.encode (Language.Eq.eq : L.Rel 2)) e →
    ¬!(henkinSetDef S).sigma.val c”
  (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt])

/-- The $\Sigma_2$ formula of `henkinRel S R`. -/
noncomputable def henkinRelDef {k : ℕ} (R : L.Rel k) : 𝚺ᴬ_[2].Semisentence k := .mkSigma
  “∃ w, !lenDef ↑k w ∧ (⋀ i, ∃ z, !nthDef z w ↑(i : Fin k).val ∧ !qqFvarDef z #i.succ.succ) ∧
    ∃ c, !qqRelDef c ↑k ↑(Encodable.encode R) w ∧ !(henkinSetDef S).sigma.val c”
  (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt])

/-- The $\Sigma_2$ formula of `henkinFunc S f`. -/
noncomputable def henkinFuncDef {k : ℕ} (f : L.Func k) : 𝚺ᴬ_[2].Semisentence (k + 1) := .mkSigma
  “z. ∃ w, !lenDef ↑k w ∧
    (⋀ i, ∃ t, !nthDef t w ↑(i : Fin k).val ∧ !qqFvarDef t #i.succ.succ.succ) ∧
    ∃ t, !qqFuncDef t ↑k ↑(Encodable.encode f) w ∧ ∃ s, !qqFvarDef s z ∧ ∃ e, !mkVec₂Def e t s ∧
    ∃ c, !qqRelDef c 2 ↑(Encodable.encode (Language.Eq.eq : L.Rel 2)) e ∧
    !(henkinSetDef S).sigma.val c”
  (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt])

/-- The representatives of the free variables up to provable equality. -/
noncomputable def henkinDomain : Semiformula.Operator ℒₒᵣ 1 := ⟨(henkinDomainDef S).val⟩

/-- The relation symbol `R` holds of the free variables `y₀, …, y_{k-1}` when `R(^&y₀, …)` is in
the Henkin set. -/
noncomputable def henkinRel {k : ℕ} (R : L.Rel k) : Semiformula.Operator ℒₒᵣ k :=
  ⟨(henkinRelDef S R).val⟩

/-- The function symbol `f` maps the free variables `y₀, …, y_{k-1}` to `z` when
`f(^&y₀, …) = ^&z` is in the Henkin set. -/
noncomputable def henkinFunc {k : ℕ} (f : L.Func k) : Semiformula.Operator ℒₒᵣ (k + 1) :=
  ⟨(henkinFuncDef S f).val⟩

section semantics

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem henkinDomain_val (a : V) : (henkinDomain S).val ![a] ↔ IsRepresentative S a := by
  simp [henkinDomain, henkinDomainDef, Semiformula.Operator.val, IsRepresentative, HenkinEq,
    Semiformula.equal, numeral_eq_natCast, quote_rel_def]

omit [L.Eq] in
theorem henkinRel_val {k : ℕ} (R : L.Rel k) (v : Fin k → V) :
    (henkinRel S R).val v ↔
      HenkinSet S (Semiformula.rel R (fun i ↦ Semiterm.fvar (v i)) : Formula V L).val := by
  simp [henkinRel, henkinRelDef, Semiformula.Operator.val]
  simp only [numeral_eq_natCast, ← and_assoc, ← eq_matrixToVec_iff, exists_eq_left]
  rfl

theorem henkinFunc_val {k : ℕ} (f : L.Func k) (z : V) (v : Fin k → V) :
    (henkinFunc S f).val (z :> v) ↔
      HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
        (Semiterm.fvar z) : Formula V L).val := by
  simp [henkinFunc, henkinFuncDef, Semiformula.Operator.val]
  simp only [numeral_eq_natCast, ← and_assoc, ← eq_matrixToVec_iff, exists_eq_left]
  rfl

end semantics

end FFL.FirstOrder.Arithmetic.Bootstrapping
