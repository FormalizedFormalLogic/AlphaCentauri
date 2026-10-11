module

public import AlphaCentauri.Bootstrapping.Completeness.HenkinSequence

/-!
# An explicit $\Delta_2$ definition of the Henkin set

A $\Delta_2$ formula `henkinSetDef S`, independent of the model, defining the Henkin set of `S` in
every model of $\mathsf{PA}$.

## References

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.25]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

section formula

variable (L : Language) [L.Encodable] [L.LORDefinable]

/-- The graph of `formulaOfCode L`. -/
noncomputable def formulaOfCodeGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y n. (!(isSemiformula L).sigma 0 n ∧ y = n) ∨ (¬!(isSemiformula L).pi 0 n ∧ !qqVerumDef y)”

/-- The graph of `henkinFormula L`. -/
noncomputable def henkinFormulaGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y n u.
    (!(isSemiformula L).sigma 0 n ∧ (∃ p < n, !qqExsDef n p) ∧
      ∃ m, !subDef m n 1 ∧ ∃ q, !pi₂Def q m ∧ ∃ w, !qqFvarDef w u ∧
        ∃ r, !(substs1Graph L) r w q ∧ !(impGraph L) y n r) ∨
    (¬(!(isSemiformula L).pi 0 n ∧ ∃ p < n, !qqExsDef n p) ∧ !qqVerumDef y)”

variable {L}

instance formulaOfCode.defined :
    𝚺ᴬ₁-Function₁[V] formulaOfCode L via formulaOfCodeGraph L := .mk fun v ↦ by
  by_cases h : IsFormula L (v 1) <;> simp [formulaOfCodeGraph, formulaOfCode, h]

instance henkinFormula.defined :
    𝚺ᴬ₁-Function₂[V] henkinFormula L via henkinFormulaGraph L := .mk fun v ↦ by
  by_cases h : IsSemiformula L 0 (v 1) ∧ ∃ p < v 1, v 1 = ^∃ p
  · simp [henkinFormulaGraph, henkinFormula, h]
  · have h' : ¬(IsFormula L (v 1) ∧ ∃ p < v 1, v 1 = ^∃ p) := h
    simp only [not_and, not_exists] at h
    simp [henkinFormulaGraph, henkinFormula, h']
    tauto

end formula

variable {L : Language} [L.Encodable] [L.LORDefinable] (S : Theory L) [S.Δ₁]

/-- The $\Sigma_2$ graph of `henkinStep S`. -/
noncomputable def henkinStepGraph : 𝚺ᴬ_[2].Semisentence 3 := .mkSigma
  “y n s. ∃ h, !(henkinFormulaGraph L) h n (n + s) ∧ ∃ nh, !(negGraph L) nh h ∧
    ∃ f, !(formulaOfCodeGraph L) f n ∧ ∃ a, !insertDef a f s ∧ ∃ b, !insertDef b nh a ∧
    ((!(derivable S) b ∧ ∃ nf, !(negGraph L) nf f ∧ ∃ c, !insertDef c nf s ∧ !insertDef y nh c) ∨
      (¬!(derivable S) b ∧ !insertDef y nh a))”
  (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt])

/-- The $\Delta_2$ formula saying that `y` is a decision sequence of length `n + 1`. -/
noncomputable def isHenkinSeq : 𝚫ᴬ_[2].Semisentence 2 := .mkDelta
  (.mkSigma “n y. !seqDef y ∧ !lhDef (n + 1) y ∧ !znthDef 0 y 0 ∧
    ∀ i < n, ∃ a, !znthDef a y (i + 1) ∧ ∃ b, !znthDef b y i ∧ !(henkinStepGraph S).val a i b”)
  (.mkPi “n y. !seqDef y ∧ !lhDef (n + 1) y ∧ !znthDef 0 y 0 ∧
    ∀ i < n, ∀ a, !znthDef a y (i + 1) → ∀ b, !znthDef b y i →
      !(henkinStepGraph S).graphDelta.pi.val a i b”)

/-- The $\Delta_2$ graph of `henkinContext S`. -/
noncomputable def henkinContextGraph : 𝚫ᴬ_[2].Semisentence 2 := .mkDelta
  (.mkSigma “c n. ∃ y, !(isHenkinSeq S).sigma.val n y ∧ !znthDef c y n”)
  (.mkPi “c n. ∀ y, !(isHenkinSeq S).sigma.val n y → !znthDef c y n”)

/-- The $\Sigma_1$ formula saying that `x` is decided positively along the context `c`. -/
noncomputable def henkinMemDef : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “x c. !(isSemiformula L).sigma 0 x ∧ ∃ h, !(henkinFormulaGraph L) h x (x + c) ∧
    ∃ nh, !(negGraph L) nh h ∧ ∃ a, !insertDef a x c ∧ ∃ b, !insertDef b nh a ∧ !(derivable S) b”

/-- The $\Delta_2$ formula defining the Henkin set of `S`. -/
noncomputable def henkinSetDef : 𝚫ᴬ_[2].Semisentence 1 := .mkDelta
  (.mkSigma “x. ∃ c, !(henkinContextGraph S).sigma.val c x ∧ !(henkinMemDef S) x c”
    (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt]))
  (.mkPi “x. ∀ c, !(henkinContextGraph S).sigma.val c x → !(henkinMemDef S) x c”
    (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt]))

instance henkinStep.defined : 𝚺ᴬ_[2]-Function₂[V] henkinStep S via henkinStepGraph S :=
  .mk fun v ↦ by
    by_cases h : Derivable S (insert (neg L (henkinFormula L (v 1) (v 1 + v 2)))
      (insert (formulaOfCode L (v 1)) (v 2))) <;> simp [henkinStepGraph, henkinStep, h]

instance henkinStep.graphDelta_defined :
    𝚫ᴬ_[2]-Function₂[V] henkinStep S via (henkinStepGraph S).graphDelta :=
  (henkinStep.defined S).graph_delta

instance IsHenkinSeq.defined : 𝚫ᴬ_[2]-Relation[V] IsHenkinSeq S via isHenkinSeq S := .mk
  ⟨by intro v; simp [isHenkinSeq], by
    intro v
    simp [isHenkinSeq, IsHenkinSeq, emptyset_def, eq_comm (a := lh (v 1)),
      eq_comm (a := znth (v 1) 0)]⟩

instance henkinMemDef.defined :
    𝚺ᴬ₁-Relation[V] (fun x c ↦ IsFormula L x ∧
      Derivable S (insert (neg L (henkinFormula L x (x + c))) (insert x c))) via henkinMemDef S :=
  .mk fun v ↦ by simp [henkinMemDef]

variable {S} in
lemma IsHenkinSeq.znth_eq_henkinContext {n y : V} (hy : IsHenkinSeq S n y) :
    znth y n = henkinContext S n := by
  have hc := isHenkinContext_henkinContext (V := V) S
  have : 𝚺ᴬ_[2]-Function₁[V] henkinContext S := (henkinContext_definable S).of_delta
  have key : ∀ n : V, ∃ y, IsHenkinSeq S n y ∧ znth y n = henkinContext S n := by
    apply InductionOnHierarchy.succ_induction_sigma 𝚺 2
      (P := fun n : V ↦ ∃ y, IsHenkinSeq S n y ∧ znth y n = henkinContext S n) (by definability)
    · obtain ⟨y, hy⟩ := exists_isHenkinSeq S (0 : V)
      exact ⟨y, hy, by rw [hy.2.2.1, hc.1]⟩
    · rintro n ⟨y, hy, e⟩
      obtain ⟨y', hy'⟩ := exists_isHenkinSeq S (n + 1)
      exact ⟨y', hy', by
        rw [hy'.2.2.2 n (lt_add_one n), hy'.znth_eq hy le_self_add le_rfl, e, hc.2]⟩
  obtain ⟨y', hy', e⟩ := key n
  rw [hy.znth_eq hy' le_rfl le_rfl, e]

variable {S}

lemma eq_henkinContext_iff_exists {c n : V} :
    c = henkinContext S n ↔ ∃ y, IsHenkinSeq S n y ∧ c = znth y n := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := exists_isHenkinSeq S n
    exact ⟨y, hy, h.trans hy.znth_eq_henkinContext.symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy.znth_eq_henkinContext

lemma eq_henkinContext_iff_forall {c n : V} :
    c = henkinContext S n ↔ ∀ y, IsHenkinSeq S n y → c = znth y n := by
  constructor
  · rintro rfl y hy
    exact hy.znth_eq_henkinContext.symm
  · intro h
    obtain ⟨y, hy⟩ := exists_isHenkinSeq S n
    exact (h y hy).trans hy.znth_eq_henkinContext

variable (S)

instance henkinContext.defined :
    𝚫ᴬ_[2]-Function₁[V] henkinContext S via henkinContextGraph S := .mk
  ⟨fun v ↦ by
    simpa [henkinContextGraph] using
      eq_henkinContext_iff_exists.symm.trans (eq_henkinContext_iff_forall (c := v 0) (n := v 1)),
  fun v ↦ by simpa [henkinContextGraph] using (eq_henkinContext_iff_exists (S := S)).symm⟩

instance HenkinSet.defined : 𝚫ᴬ_[2]-Predicate[V] (HenkinSet S) via henkinSetDef S := .mk
  ⟨by intro v; simp [henkinSetDef], by intro v; simp [henkinSetDef, HenkinSet, HenkinMem]⟩

end FFL.FirstOrder.Arithmetic.Bootstrapping
