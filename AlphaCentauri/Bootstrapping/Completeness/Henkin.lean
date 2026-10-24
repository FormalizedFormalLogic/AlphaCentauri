module

public import AlphaCentauri.Bootstrapping.Proof.Substitution
public import AlphaCentauri.ToFoundation.InternalEquality
public import AlphaCentauri.ToFoundation.Coding
public import AlphaCentauri.ToFoundation.TypedProof
public import Foundation.FirstOrder.Incompleteness.Consistency

/-!
# Henkin completion inside $\mathsf{PA}$

Henkin's construction carried out in a model `V` of $\mathsf{PA}$: the Henkin formulas, the
contexts of the decision sequence, and the closure properties of the formulas decided positively.
The free variables `^&u` of internal formulas play the role of the Henkin constants. The decision
sequence exists and is unique, and the set of formulas decided positively along it, the Henkin set,
is $\Delta_2$-definable, by a formula `henkinSetDef S` that does not depend on the model.

The Henkin set of a theory $S$ in a model of $\mathsf{PA}$ in which $S$ is consistent behaves like
the set of sentences true in a term model: it is a complete theory closed under internal
provability with the Henkin property. Provable equality of free variables is an equivalence
relation, every class has a least element, its representative, and every application of a function
symbol to free variables equals the free variable of a unique representative. Equality of
arbitrary terms is symmetric and transitive, and function and relation symbols respect it.

The arithmetical operators of the Henkin translation of a language $L$ into arithmetic are read
off from the Henkin set: the domain consists of the representatives, a relation holds of
representatives when the atomic formula on the corresponding free variables is in the Henkin set,
and a function symbol is interpreted by the graph given by the equation of its application with a
free variable.

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

open Classical in
/-- The formula with code `n`, and `⊤` if `n` is not the code of a formula. -/
noncomputable def formulaOfCode (n : V) : V := if IsFormula L n then n else ^⊤

open Classical in
/-- The Henkin formula `∃x α → α(^&u)` of the code `n = ⌜∃x α⌝` with the free variable `^&u` as
its witness, and `⊤` if `n` is not the code of an existential formula. -/
noncomputable def henkinFormula (n u : V) : V :=
  if IsFormula L n ∧ ∃ p < n, n = ^∃ p then imp L n (substs1 L ^&u (π₂ (n - 1))) else ^⊤

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

instance formulaOfCode.definable : 𝚺ᴬ₁-Function₁ (formulaOfCode (V := V) L) :=
  formulaOfCode.defined.to_definable

instance henkinFormula.defined :
    𝚺ᴬ₁-Function₂[V] henkinFormula L via henkinFormulaGraph L := .mk fun v ↦ by
  by_cases h : IsSemiformula L 0 (v 1) ∧ ∃ p < v 1, v 1 = ^∃ p
  · simp [henkinFormulaGraph, henkinFormula, h]
  · have h' : ¬(IsFormula L (v 1) ∧ ∃ p < v 1, v 1 = ^∃ p) := h
    simp only [not_and, not_exists] at h
    simp [henkinFormulaGraph, henkinFormula, h']
    tauto

instance henkinFormula.definable : 𝚺ᴬ₁-Function₂ (henkinFormula (V := V) L) :=
  henkinFormula.defined.to_definable

@[simp] lemma isFormula_formulaOfCode (n : V) : IsFormula L (formulaOfCode L n) := by
  unfold formulaOfCode
  split_ifs with h <;> simp [h]

@[simp] lemma formulaOfCode_of_isFormula {n : V} (h : IsFormula L n) : formulaOfCode L n = n :=
  ite_eq_left h

lemma henkinFormula_exs {α : V} (hα : IsSemiformula L 1 α) (u : V) :
    henkinFormula L (^∃ α) u = imp L (^∃ α) (substs1 L ^&u α) := by
  unfold henkinFormula
  rw [ite_eq_left ⟨by simpa using hα, α, by simp, rfl⟩]
  simp [qqExs]

@[simp] lemma isFormula_henkinFormula (n u : V) : IsFormula L (henkinFormula L n u) := by
  unfold henkinFormula
  split_ifs with h
  · obtain ⟨hn, α, -, rfl⟩ := h
    have hα : IsSemiformula L 1 α := by simpa using hn
    have e : π₂ ((^∃ α) - 1) = α := by simp [qqExs]
    rw [e]
    exact IsSemiformula.imp.mpr ⟨hn, IsSemiformula.substs1 (by simp) hα⟩
  · simp

end formula

section derivable

variable {L : Language} [L.Encodable] [L.LORDefinable] {S : Theory L} [S.Δ₁]

lemma Derivable.of_and {s p q c : V} (hc : c = p ∨ c = q) (h : Derivable S (insert (p ^⋏ q) s)) :
    Derivable S (insert c s) := by
  obtain ⟨hpq, hs⟩ := IsFormulaSet.insert_iff.mp h.isFormulaSet
  obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq
  have hF : IsFormulaSet L (insert (p ^⋏ q) (insert c s)) := by
    rcases hc with rfl | rfl <;> simp [hpq, hp, hq, hs]
  have h₁ : (p ^⋏ q ⫽ s) ⊆ (p ^⋏ q ⫽ c ⫽ s) := by
    intro x hx
    simp at hx ⊢
    tauto
  apply Derivable.cut (p ^⋏ q) (.wk hF h₁ h)
  rw [neg_and hp.isUFormula hq.isUFormula]
  rcases hc with rfl | rfl <;> exact .or (.em (by simp [hp, hq, hs]) c (by simp) (by simp))

private lemma not_derivable_insert_neg_henkinFormula (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    {Γ : V} (hΓ : IsFormulaSet L Γ) (n : V) (h : ¬Derivable S Γ) :
    ¬Derivable S (insert (neg L (henkinFormula L n (n + Γ))) Γ) := by
  intro hd
  by_cases hn : IsFormula L n ∧ ∃ p < n, n = ^∃ p
  · obtain ⟨hn, α, hαn, rfl⟩ := hn
    have hα : IsSemiformula L 1 α := by simpa using hn
    have hβ : IsFormula L (substs1 L ^&((^∃ α) + Γ) α) := IsSemiformula.substs1 (by simp) hα
    rw [henkinFormula_exs hα, imp, neg_or hn.isUFormula.neg hβ.isUFormula,
      IsUFormula.neg_neg hn.isUFormula] at hd
    have h₁ : Derivable S (insert (^∃ α) Γ) := hd.of_and (.inl rfl)
    have h₂ : Derivable S (insert (neg L (^∃ α)) Γ) :=
      Derivable.neg_exs_of_fresh hS le_add_self
        (le_trans hαn.le le_self_add) hα (hd.of_and (.inr rfl))
    exact h (h₁.cut _ h₂)
  · rw [henkinFormula, ite_eq_right hn, neg_verum] at hd
    exact h (.cut ^⊤ (.verum (by simp [hΓ]) (by simp)) (by rwa [neg_verum]))

end derivable

section sequence

variable {L : Language} [L.Encodable] [L.LORDefinable] (S : Theory L) [S.Δ₁]

open Classical in
/-- The context after the `n`-th decision, given the context `s` before it. It extends `s` by the
negation of the Henkin formula of `n` with the witness `^&(n + s)`, and by the negation of the
formula with code `n` if the sequent of `s`, that negated Henkin formula and the formula is
derivable, and by the formula itself otherwise. -/
noncomputable def henkinStep (n s : V) : V :=
  insert (neg L (henkinFormula L n (n + s)))
    (insert (if Derivable S (insert (neg L (henkinFormula L n (n + s)))
        (insert (formulaOfCode L n) s)) then neg L (formulaOfCode L n) else formulaOfCode L n) s)

/-- The $\Sigma_2$ graph of `henkinStep S`. -/
noncomputable def henkinStepGraph : 𝚺ᴬ_[2].Semisentence 3 := .mkSigma
  “y n s. ∃ h, !(henkinFormulaGraph L) h n (n + s) ∧ ∃ nh, !(negGraph L) nh h ∧
    ∃ f, !(formulaOfCodeGraph L) f n ∧ ∃ a, !insertDef a f s ∧ ∃ b, !insertDef b nh a ∧
    ((!(derivable S) b ∧ ∃ nf, !(negGraph L) nf f ∧ ∃ c, !insertDef c nf s ∧ !insertDef y nh c) ∨
      (¬!(derivable S) b ∧ !insertDef y nh a))”
  (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt])

instance henkinStep.defined : 𝚺ᴬ_[2]-Function₂[V] henkinStep S via henkinStepGraph S :=
  .mk fun v ↦ by
    by_cases h : Derivable S (insert (neg L (henkinFormula L (v 1) (v 1 + v 2)))
      (insert (formulaOfCode L (v 1)) (v 2))) <;> simp [henkinStepGraph, henkinStep, h]

instance henkinStep.graphDelta_defined :
    𝚫ᴬ_[2]-Function₂[V] henkinStep S via (henkinStepGraph S).graphDelta :=
  (henkinStep.defined S).graph_delta

instance henkinStep.definable : 𝚫ᴬ_[2]-Function₂ (henkinStep (V := V) S) :=
  (henkinStep.graphDelta_defined S).to_definable

/-- `y` is the sequence of the first `n + 1` contexts of the decision sequence of the Henkin
completion of `S`. -/
def IsHenkinSeq (n y : V) : Prop :=
  Seq y ∧ lh y = n + 1 ∧ znth y 0 = ∅ ∧ ∀ i < n, znth y (i + 1) = henkinStep S i (znth y i)

/-- The $\Delta_2$ formula saying that `y` is a decision sequence of length `n + 1`. -/
noncomputable def isHenkinSeq : 𝚫ᴬ_[2].Semisentence 2 := .mkDelta
  (.mkSigma “n y. !seqDef y ∧ !lhDef (n + 1) y ∧ !znthDef 0 y 0 ∧
    ∀ i < n, ∃ a, !znthDef a y (i + 1) ∧ ∃ b, !znthDef b y i ∧ !(henkinStepGraph S).val a i b”)
  (.mkPi “n y. !seqDef y ∧ !lhDef (n + 1) y ∧ !znthDef 0 y 0 ∧
    ∀ i < n, ∀ a, !znthDef a y (i + 1) → ∀ b, !znthDef b y i →
      !(henkinStepGraph S).graphDelta.pi.val a i b”)

instance IsHenkinSeq.defined : 𝚫ᴬ_[2]-Relation[V] IsHenkinSeq S via isHenkinSeq S := .mk
  ⟨by intro v; simp [isHenkinSeq], by
    intro v
    simp [isHenkinSeq, IsHenkinSeq, emptyset_def, eq_comm (a := lh (v 1)),
      eq_comm (a := znth (v 1) 0)]⟩

instance IsHenkinSeq.definable : 𝚫ᴬ_[2]-Relation (IsHenkinSeq (V := V) S) :=
  (IsHenkinSeq.defined S).to_definable

lemma exists_isHenkinSeq (n : V) : ∃ y, IsHenkinSeq S n y := by
  apply InductionOnHierarchy.succ_induction_sigma 𝚺 2 (P := fun n : V ↦ ∃ y, IsHenkinSeq S n y)
    (by definability)
  · exact ⟨∅ ⁀' ∅, seq_empty.seqCons ∅, by simp,
      (seq_empty.seqCons ∅).znth_eq_of_mem (by simp), by simp⟩
  · rintro n ⟨y, hy, hlh, h0, hstep⟩
    have hcons := hy.seqCons (henkinStep S n (znth y n))
    have hlt : ∀ {i}, i ≤ n → znth (y ⁀' henkinStep S n (znth y n)) i = znth y i := by
      intro i hi
      exact hcons.znth_eq_of_mem <| Seq.subset_seqCons _ _ <| hy.znth <| by
        rw [hlh]; exact lt_succ_iff_le.mpr hi
    have hlast : znth (y ⁀' henkinStep S n (znth y n)) (n + 1) = henkinStep S n (znth y n) := by
      simpa [hlh] using hcons.znth_eq_of_mem (Seq.mem_seqCons y (henkinStep S n (znth y n)))
    have hstep' : ∀ i < n + 1, znth (y ⁀' henkinStep S n (znth y n)) (i + 1) =
        henkinStep S i (znth (y ⁀' henkinStep S n (znth y n)) i) := by
      intro i hi
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with (hi | rfl)
      · rw [hlt (succ_le_iff_lt.mpr hi), hlt hi.le, hstep i hi]
      · rw [hlast, hlt le_rfl]
    exact ⟨y ⁀' henkinStep S n (znth y n), hcons, by simp [hy, hlh], by rw [hlt zero_le, h0],
      hstep'⟩

variable {S} in
private lemma IsHenkinSeq.znth_eq {n m y y' : V} (hy : IsHenkinSeq S n y) (hy' : IsHenkinSeq S m y')
    {i : V} (hn : i ≤ n) (hm : i ≤ m) : znth y i = znth y' i := by
  revert hn hm
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _ _; rw [hy.2.2.1, hy'.2.2.1]
  case succ i ih =>
    intro hn hm
    have hn' : i < n := succ_le_iff_lt.mp hn
    have hm' : i < m := succ_le_iff_lt.mp hm
    rw [hy.2.2.2 i hn', hy'.2.2.2 i hm', ih hn'.le hm'.le]

/-- The contexts of the decision sequence of the Henkin completion of `S`. -/
noncomputable def henkinContext (n : V) : V := znth (Classical.choose (exists_isHenkinSeq S n)) n

variable {S} in
private lemma IsHenkinSeq.znth_eq_henkinContext {n y : V} (hy : IsHenkinSeq S n y) :
    znth y n = henkinContext S n :=
  hy.znth_eq (Classical.choose_spec (exists_isHenkinSeq S n)) le_rfl le_rfl

@[simp] lemma henkinContext_zero : henkinContext S (0 : V) = ∅ := by
  obtain ⟨y, hy⟩ := exists_isHenkinSeq S (0 : V)
  rw [← hy.znth_eq_henkinContext, hy.2.2.1]

lemma henkinContext_succ (n : V) :
    henkinContext S (n + 1) = henkinStep S n (henkinContext S n) := by
  obtain ⟨y, hy⟩ := exists_isHenkinSeq S (n + 1)
  rw [← hy.znth_eq_henkinContext, hy.2.2.2 n (lt_add_one n)]
  exact congrArg (henkinStep S n) <| hy.znth_eq (Classical.choose_spec (exists_isHenkinSeq S n))
    le_self_add le_rfl

/-- The $\Delta_2$ graph of `henkinContext S`. -/
noncomputable def henkinContextGraph : 𝚫ᴬ_[2].Semisentence 2 := .mkDelta
  (.mkSigma “c n. ∃ y, !(isHenkinSeq S).sigma.val n y ∧ !znthDef c y n”)
  (.mkPi “c n. ∀ y, !(isHenkinSeq S).sigma.val n y → !znthDef c y n”)

variable {S} in
private lemma eq_henkinContext_iff_exists {c n : V} :
    c = henkinContext S n ↔ ∃ y, IsHenkinSeq S n y ∧ c = znth y n :=
  ⟨fun h ↦ let ⟨y, hy⟩ := exists_isHenkinSeq S n; ⟨y, hy, h.trans hy.znth_eq_henkinContext.symm⟩,
    by rintro ⟨y, hy, rfl⟩; exact hy.znth_eq_henkinContext⟩

variable {S} in
private lemma eq_henkinContext_iff_forall {c n : V} :
    c = henkinContext S n ↔ ∀ y, IsHenkinSeq S n y → c = znth y n :=
  ⟨by rintro rfl y hy; exact hy.znth_eq_henkinContext.symm,
    fun h ↦ let ⟨y, hy⟩ := exists_isHenkinSeq S n; (h y hy).trans hy.znth_eq_henkinContext⟩

instance henkinContext.defined :
    𝚫ᴬ_[2]-Function₁[V] henkinContext S via henkinContextGraph S := .mk
  ⟨fun v ↦ by
    simpa [henkinContextGraph] using
      eq_henkinContext_iff_exists.symm.trans (eq_henkinContext_iff_forall (c := v 0) (n := v 1)),
  fun v ↦ by simpa [henkinContextGraph] using (eq_henkinContext_iff_exists (S := S)).symm⟩

instance henkinContext.definable : 𝚫ᴬ_[2]-Function₁ (henkinContext (V := V) S) :=
  (henkinContext.defined S).to_definable

/-- The Henkin set of `S`: the formulas `x` such that the sequent of `henkinContext S x`, `x` and
the negated Henkin formula of `x` with the witness `^&(x + henkinContext S x)` is derivable. -/
def HenkinSet (x : V) : Prop :=
  IsFormula L x ∧ Derivable S (insert (neg L (henkinFormula L x (x + henkinContext S x)))
    (insert x (henkinContext S x)))

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

instance henkinMemDef.defined :
    𝚺ᴬ₁-Relation[V] (fun x c ↦ IsFormula L x ∧
      Derivable S (insert (neg L (henkinFormula L x (x + c))) (insert x c))) via henkinMemDef S :=
  .mk fun v ↦ by simp [henkinMemDef]

instance HenkinSet.defined : 𝚫ᴬ_[2]-Predicate[V] (HenkinSet S) via henkinSetDef S := .mk
  ⟨by intro v; simp [henkinSetDef], by intro v; simp [henkinSetDef, HenkinSet]⟩

/-- The Henkin set is $\Delta_2$-definable.

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.25] -/
theorem henkinSet_definable : 𝚫ᴬ_[2]-Predicate[V] (HenkinSet S) :=
  (HenkinSet.defined S).to_definable

section context

variable {S}

lemma HenkinSet.isFormula {x : V} (h : HenkinSet S x) : IsFormula L x := h.1

private lemma neg_henkinFormula_mem_henkinContext (n : V) :
    neg L (henkinFormula L n (n + henkinContext S n)) ∈ henkinContext S (n + 1) := by
  simp [henkinContext_succ, henkinStep]

private lemma mem_henkinContext_succ_of_mem {n x : V} (h : x ∈ henkinContext S n) :
    x ∈ henkinContext S (n + 1) := by
  simp [henkinContext_succ, henkinStep, h]

private lemma mem_henkinContext_decision (n : V) :
    (open Classical in
      if Derivable S (insert (neg L (henkinFormula L n (n + henkinContext S n)))
        (insert (formulaOfCode L n) (henkinContext S n))) then neg L (formulaOfCode L n)
      else formulaOfCode L n) ∈ henkinContext S (n + 1) := by
  simp [henkinContext_succ, henkinStep]

private lemma henkinSet_iff {n : V} (hn : IsFormula L n) :
    HenkinSet S n ↔ Derivable S (insert (neg L (henkinFormula L n (n + henkinContext S n)))
      (insert (formulaOfCode L n) (henkinContext S n))) := by
  simp [HenkinSet, hn]

private lemma neg_mem_henkinContext_of_henkinSet {n : V} (h : HenkinSet S n) :
    neg L n ∈ henkinContext S (n + 1) := by
  have := mem_henkinContext_decision (S := S) n
  rwa [ite_eq_left ((henkinSet_iff h.isFormula).mp h), formulaOfCode_of_isFormula h.isFormula]
    at this

private lemma mem_henkinContext_of_not_henkinSet {n : V} (hn : IsFormula L n) (h : ¬HenkinSet S n) :
    n ∈ henkinContext S (n + 1) := by
  have := mem_henkinContext_decision (S := S) n
  rwa [ite_eq_right (mt (henkinSet_iff hn).mpr h), formulaOfCode_of_isFormula hn] at this

@[simp] private lemma isFormulaSet_henkinContext (n : V) : IsFormulaSet L (henkinContext S n) := by
  have : 𝚫ᴬ_[2]-Predicate[V] IsFormulaSet L :=
    Bounding.HierarchySymbol.Definable.of_lt IsFormulaSet.definable (by simp)
  apply InductionOnHierarchy.succ_induction_sigma 𝚫 2
    (P := fun n ↦ IsFormulaSet L (henkinContext S n)) (by definability)
  · simp
  · intro n ih
    rw [henkinContext_succ, henkinStep]
    split_ifs <;> simp [ih]

private lemma mem_henkinContext_of_le {n m x : V} (hnm : n ≤ m) (h : x ∈ henkinContext S n) :
    x ∈ henkinContext S m := by
  obtain ⟨k, rfl⟩ := exists_add_of_le hnm
  clear hnm
  revert k
  apply InductionOnHierarchy.succ_induction_sigma 𝚫 2 (P := fun k ↦ x ∈ henkinContext S (n + k))
    (by definability)
  · simpa using h
  · intro k ih
    rw [← add_assoc]
    exact mem_henkinContext_succ_of_mem ih

private lemma exists_forall_mem_henkinContext {s : V}
    (h : ∀ p ∈ s, ∃ m : V, p ∈ henkinContext S m) :
    ∃ m : V, ∀ p ∈ s, p ∈ henkinContext S m := by
  have key : ∀ y : V, ∃ m : V, ∀ p ∈ s, p < y → p ∈ henkinContext S m := by
    apply InductionOnHierarchy.succ_induction_sigma 𝚺 2
      (P := fun y : V ↦ ∃ m : V, ∀ p ∈ s, p < y → p ∈ henkinContext S m) (by definability)
    · use 0
      intro p _ hp
      simp at hp
    · rintro y ⟨m, hm⟩
      by_cases hy : y ∈ s
      · obtain ⟨m', hm'⟩ := h y hy
        use max m m'
        intro p hp hpy
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hpy) with hpy | rfl
        · exact mem_henkinContext_of_le (le_max_left _ _) (hm p hp hpy)
        · exact mem_henkinContext_of_le (le_max_right _ _) hm'
      · use m
        intro p hp hpy
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hpy) with hpy | rfl
        · exact hm p hp hpy
        · exact absurd hp hy
  obtain ⟨m, hm⟩ := key (s + 1)
  exact ⟨m, fun p hp ↦ hm p hp (lt_of_lt_of_le (lt_of_mem hp) le_self_add)⟩

end context

section theorems

/-- Provable formulas are in the Henkin set. -/
theorem HenkinSet.of_provable {φ : V} (hφ : IsFormula L φ) (h : Provable S φ) : HenkinSet S φ := by
  apply (henkinSet_iff hφ).mpr
  apply h.toDerivable.wk
  · simp
  · intro x hx
    obtain rfl : x = φ := by simpa using hx
    simp [hφ]

variable {S} (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

/-- No context of the decision sequence is derivable when `S` is consistent. -/
theorem not_derivable_henkinContext (n : V) : ¬Derivable S (henkinContext S n) := by
  have : 𝚫ᴬ_[2]-Predicate[V] Derivable S :=
    Bounding.HierarchySymbol.Definable.of_lt (Derivable.definable (T := S)) (by simp)
  apply InductionOnHierarchy.succ_induction_sigma 𝚫 2
    (P := fun n ↦ ¬Derivable S (henkinContext S n)) (by definability)
  · rw [henkinContext_zero]
    intro h
    apply hcons
    have : (⌜(⊥ : Sentence L)⌝ : V) = ^⊥ := by simp [Sentence.quote_def, Semiformula.quote_def]
    rw [this]
    exact (h.wk (by simp) (by simp)).toProvable
  · intro n ih h
    rw [henkinContext_succ, henkinStep] at h
    by_cases hD : Derivable S (insert (neg L (henkinFormula L n (n + henkinContext S n)))
        (insert (formulaOfCode L n) (henkinContext S n)))
    · rw [ite_eq_left hD] at h
      exact not_derivable_insert_neg_henkinFormula hS (isFormulaSet_henkinContext n) n ih
        (.cut (formulaOfCode L n) hD.exchange h.exchange)
    · rw [ite_eq_right hD] at h
      exact hD h

private lemma henkinSet_of_forall_mem {s ψ : V} (hψ : IsFormula L ψ)
    (hs : ∃ m : V, ∀ p ∈ s, p ∈ henkinContext S m) (h : Derivable S (insert ψ s)) :
    HenkinSet S ψ := by
  by_contra hM
  obtain ⟨m, hm⟩ := hs
  have h₁ : (ψ ⫽ s) ⊆ henkinContext S (max m (ψ + 1)) := by
    intro x hx
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · exact mem_henkinContext_of_le (le_max_right _ _) (mem_henkinContext_of_not_henkinSet hψ hM)
    · exact mem_henkinContext_of_le (le_max_left _ _) (hm x hx)
  exact not_derivable_henkinContext hS hcons (max m (ψ + 1))
    (h.wk (isFormulaSet_henkinContext _) h₁)

/-- If `ψ` is derivable from the negations of formulas in the Henkin set, then `ψ` is in the
Henkin set. -/
theorem HenkinSet.of_derivable {s ψ : V} (hψ : IsFormula L ψ)
    (hs : ∀ p ∈ s, HenkinSet S (neg L p)) (h : Derivable S (insert ψ s)) : HenkinSet S ψ := by
  have h₁ : ∀ p ∈ s, ∃ m : V, p ∈ henkinContext S m := by
    intro p hp
    have hM := hs p hp
    have hp' : IsFormula L p := IsSemiformula.neg_iff.mp hM.isFormula
    use neg L p + 1
    simpa [IsUFormula.neg_neg hp'.isUFormula] using neg_mem_henkinContext_of_henkinSet hM
  exact henkinSet_of_forall_mem hS hcons hψ (exists_forall_mem_henkinContext h₁) h

/-- The negation of a formula is in the Henkin set if and only if the formula is not.

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.25] -/
theorem HenkinSet.neg_iff {φ : V} (hφ : IsFormula L φ) :
    HenkinSet S (neg L φ) ↔ ¬HenkinSet S φ := by
  constructor
  · intro h₁ h₂
    have e₁ := neg_mem_henkinContext_of_henkinSet h₂
    have e₂ := neg_mem_henkinContext_of_henkinSet h₁
    rw [IsUFormula.neg_neg hφ.isUFormula] at e₂
    exact not_derivable_henkinContext hS hcons (max (φ + 1) (neg L φ + 1))
      (.em (isFormulaSet_henkinContext _) φ (mem_henkinContext_of_le (le_max_right _ _) e₂)
        (mem_henkinContext_of_le (le_max_left _ _) e₁))
  · intro h
    exact henkinSet_of_forall_mem hS hcons (s := {φ}) hφ.neg
      ⟨φ + 1, by simpa using mem_henkinContext_of_not_henkinSet hφ h⟩
      (.em (by simp [hφ]) φ (by simp) (by simp))

/-- Every Henkin formula with witness `^&(n + henkinContext S n)` is in the Henkin set. -/
theorem HenkinSet.henkinFormula_henkinContext (n : V) :
    HenkinSet S (henkinFormula L n (n + henkinContext S n)) := by
  have hH := isFormula_henkinFormula (L := L) n (n + henkinContext S n)
  exact henkinSet_of_forall_mem hS hcons (s := {neg L (henkinFormula L n (n + henkinContext S n))})
    hH ⟨n + 1, by simpa using neg_henkinFormula_mem_henkinContext n⟩
    (.em (by simp [hH]) (henkinFormula L n (n + henkinContext S n)) (by simp) (by simp))

/-- The Henkin set is closed under modus ponens. -/
theorem HenkinSet.modus_ponens {α β : V} (hα : HenkinSet S α) (hαβ : HenkinSet S (imp L α β)) :
    HenkinSet S β := by
  have hF : IsFormula L α ∧ IsFormula L β := by simpa using hαβ.isFormula
  have e : neg L (imp L α β) = α ^⋏ neg L β := by
    rw [imp, neg_or hF.1.isUFormula.neg hF.2.isUFormula, IsUFormula.neg_neg hF.1.isUFormula]
  apply HenkinSet.of_derivable hS hcons (s := insert (neg L α) {neg L (imp L α β)}) hF.2
  · intro p hp
    obtain rfl | rfl : p = neg L α ∨ p = neg L (imp L α β) := by simpa using hp
    · simpa [IsUFormula.neg_neg hF.1.isUFormula] using hα
    · simpa [IsUFormula.neg_neg hαβ.isFormula.isUFormula] using hαβ
  · exact .ofSetEq (s' := insert (α ^⋏ neg L β) (insert β (insert (neg L α) (∅ : V))))
      (fun x ↦ by simp [e]; tauto)
      (.and (.em (by simp [hF.1, hF.2]) α (by simp) (by simp))
        (.em (by simp [hF.1, hF.2]) β (by simp) (by simp)))

/-- If an existential formula is in the Henkin set, so is one of its instances at a free
variable.

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.25] -/
theorem HenkinSet.exists_substs1 {α : V} (hα : IsSemiformula L 1 α) (h : HenkinSet S (^∃ α)) :
    ∃ u, HenkinSet S (substs1 L ^&u α) := by
  have h₁ := HenkinSet.henkinFormula_henkinContext hS hcons (^∃ α)
  rw [henkinFormula_exs hα] at h₁
  exact ⟨_, HenkinSet.modus_ponens hS hcons h h₁⟩

end theorems

end sequence

section termModel

variable {L : Language} [L.Encodable] [L.LORDefinable] (S : Theory L) [S.Δ₁]

section closure

theorem henkinSet_of_tprovable {φ : Formula V L} (h : S.internalize V ⊢ φ) :
    HenkinSet S φ.val :=
  HenkinSet.of_provable S (Semiformula.isSemiformula_zero φ) (tprovable_iff_provable.mp h)

variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

theorem henkinSet_of_tprovable_imp {φ ψ : Formula V L} (h : S.internalize V ⊢ φ 🡒 ψ)
    (hφ : HenkinSet S φ.val) : HenkinSet S ψ.val :=
  HenkinSet.modus_ponens hS hcons hφ (henkinSet_of_tprovable S h)

theorem henkinSet_neg_iff {φ : Formula V L} : HenkinSet S (∼φ).val ↔ ¬HenkinSet S φ.val :=
  HenkinSet.neg_iff hS hcons (Semiformula.isSemiformula_zero φ)

theorem henkinSet_not_falsum : ¬HenkinSet S (⊥ : Formula V L).val := by
  have h : HenkinSet S (∼(⊥ : Formula V L)).val :=
    henkinSet_of_tprovable S <| by simp [Entailment.verum]
  exact (henkinSet_neg_iff S hS hcons).mp h

theorem henkinSet_and_iff {φ ψ : Formula V L} :
    HenkinSet S (φ ⋏ ψ).val ↔ HenkinSet S φ.val ∧ HenkinSet S ψ.val := by
  constructor
  · intro h
    exact ⟨henkinSet_of_tprovable_imp S hS hcons Entailment.and₁ h,
      henkinSet_of_tprovable_imp S hS hcons Entailment.and₂ h⟩
  · rintro ⟨h₁, h₂⟩
    exact HenkinSet.modus_ponens hS hcons h₂
      (henkinSet_of_tprovable_imp S hS hcons Entailment.and₃ h₁)

theorem henkinSet_or_iff {φ ψ : Formula V L} :
    HenkinSet S (φ ⋎ ψ).val ↔ HenkinSet S φ.val ∨ HenkinSet S ψ.val := by
  have e : φ ⋎ ψ = ∼(∼φ ⋏ ∼ψ) := by simp
  simp only [e, henkinSet_neg_iff S hS hcons, henkinSet_and_iff S hS hcons]
  tauto

theorem henkinSet_exs_iff {φ : Semiformula V L 1} :
    HenkinSet S (∃¹ φ).val ↔
      ∃ u : V, HenkinSet S (φ.subst ![(Semiterm.fvar u : Semiterm V L 0)]).val := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := HenkinSet.exists_substs1 hS hcons (Semiformula.isSemiformula_one φ) h
    exact ⟨u, by simpa [substs1] using hu⟩
  · rintro ⟨u, hu⟩
    exact henkinSet_of_tprovable_imp S hS hcons (TProof.subst_imp_exs (T := S) φ _) hu

theorem henkinSet_all_iff {φ : Semiformula V L 1} :
    HenkinSet S (∀¹ φ).val ↔
      ∀ u : V, HenkinSet S (φ.subst ![(Semiterm.fvar u : Semiterm V L 0)]).val := by
  constructor
  · intro h u
    exact henkinSet_of_tprovable_imp S hS hcons (TProof.all_imp_subst (T := S) φ _) h
  · intro h
    by_contra hn
    have h₁ : HenkinSet S (∼(∀¹ φ)).val := (henkinSet_neg_iff S hS hcons).mpr hn
    rw [Semiformula.neg_all] at h₁
    obtain ⟨u, hu⟩ := (henkinSet_exs_iff S hS hcons).mp h₁
    rw [Semiformula.substs_neg, henkinSet_neg_iff S hS hcons] at hu
    exact hu (h u)

theorem henkinSet_conj_iff {k : ℕ} (v : Fin k → Formula V L) :
    HenkinSet S (Matrix.conj v).val ↔ ∀ i, HenkinSet S (v i).val := by
  induction k with
  | zero =>
    simpa using henkinSet_of_tprovable S (φ := (⊤ : Formula V L)) (by simp)
  | succ k ih =>
    rw [Matrix.conj, henkinSet_and_iff S hS hcons, ih, Fin.forall_fin_succ]
    exact Iff.rfl

end closure

section equality

variable [L.Eq] [𝗘𝗤 L ⪯ S]

/-- The free variables `^&u` and `^&v` are provably equal in the Henkin set. -/
def HenkinEq (u v : V) : Prop :=
  HenkinSet S (Semiformula.equal (Semiterm.fvar u) (Semiterm.fvar v) : Formula V L).val

/-- The free variable `^&a` is the least of the free variables provably equal to it. -/
def IsRepresentative (a : V) : Prop := ∀ y < a, ¬HenkinEq S y a

omit [𝗘𝗤 L ⪯ S] in
private lemma henkinEq_definable (u : V) : 𝚫ᴬ_[2]-Predicate[V] fun a ↦ HenkinEq S a u := by
  have hf : 𝚺ᴬ₁-Function₁[V] fun a ↦
      (Semiformula.equal (Semiterm.fvar a) (Semiterm.fvar u) : Formula V L).val := by
    simp only [Semiformula.equal, Semiformula.rel_val, Nat.cast_ofNat, SemitermVec.val_succ,
      Matrix.head_cons, Semiterm.fvar_val, Matrix.tail_cons, SemitermVec.val_nil]
    definability
  exact (henkinSet_definable S).comp (hf.of_lt (by simp))

theorem henkinSet_equal_refl (t : Semiterm V L 0) : HenkinSet S (Semiformula.equal t t).val :=
  henkinSet_of_tprovable S <| tprovable_equal_refl S t

theorem HenkinEq.refl (u : V) : HenkinEq S u u := henkinSet_equal_refl S (Semiterm.fvar u)

variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

theorem henkinSet_equal_symm {s t : Semiterm V L 0}
    (h : HenkinSet S (Semiformula.equal s t).val) : HenkinSet S (Semiformula.equal t s).val :=
  henkinSet_of_tprovable_imp S hS hcons (tprovable_equal_symm_imp S s t) h

theorem henkinSet_equal_trans {s t u : Semiterm V L 0}
    (h₁ : HenkinSet S (Semiformula.equal s t).val)
    (h₂ : HenkinSet S (Semiformula.equal t u).val) : HenkinSet S (Semiformula.equal s u).val :=
  henkinSet_of_tprovable_imp S hS hcons (tprovable_equal_trans_imp S s t u)
    ((henkinSet_and_iff S hS hcons).mpr ⟨h₁, h₂⟩)

theorem henkinSet_equal_func {k : ℕ} (f : L.Func k) {s u : SemitermVec V L k 0}
    (h : ∀ i, HenkinSet S (Semiformula.equal (s i) (u i)).val) :
    HenkinSet S (Semiformula.equal (Semiterm.func f s) (Semiterm.func f u)).val :=
  henkinSet_of_tprovable_imp S hS hcons (tprovable_equal_func_imp S f s u)
    ((henkinSet_conj_iff S hS hcons _).mpr h)

private theorem henkinSet_rel_imp {k : ℕ} (R : L.Rel k) {s u : SemitermVec V L k 0}
    (h : ∀ i, HenkinSet S (Semiformula.equal (s i) (u i)).val)
    (hs : HenkinSet S (Semiformula.rel R s).val) : HenkinSet S (Semiformula.rel R u).val :=
  HenkinSet.modus_ponens hS hcons hs <|
    henkinSet_of_tprovable_imp S hS hcons (tprovable_rel_congr_imp S R s u)
      ((henkinSet_conj_iff S hS hcons _).mpr h)

theorem henkinSet_rel_iff {k : ℕ} (R : L.Rel k) {s u : SemitermVec V L k 0}
    (h : ∀ i, HenkinSet S (Semiformula.equal (s i) (u i)).val) :
    HenkinSet S (Semiformula.rel R s).val ↔ HenkinSet S (Semiformula.rel R u).val :=
  ⟨henkinSet_rel_imp S hS hcons R h,
    henkinSet_rel_imp S hS hcons R fun i ↦ henkinSet_equal_symm S hS hcons (h i)⟩

theorem HenkinEq.symm {u v : V} (h : HenkinEq S u v) : HenkinEq S v u :=
  henkinSet_equal_symm S hS hcons h

theorem HenkinEq.trans {u v w : V} (h₁ : HenkinEq S u v) (h₂ : HenkinEq S v w) :
    HenkinEq S u w :=
  henkinSet_equal_trans S hS hcons h₁ h₂

theorem exists_isRepresentative (u : V) : ∃ a, IsRepresentative S a ∧ HenkinEq S a u := by
  obtain ⟨a, ha, hmin⟩ := InductionOnHierarchy.least_number_sigma 𝚫 2
    (P := fun a ↦ HenkinEq S a u) (henkinEq_definable S u) (x := u) (HenkinEq.refl S u)
  exact ⟨a, fun y hy hya ↦ hmin y hy (HenkinEq.trans S hS hcons hya ha), ha⟩

theorem IsRepresentative.eq_of_henkinEq {a b : V} (ha : IsRepresentative S a)
    (hb : IsRepresentative S b) (h : HenkinEq S a b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (hb a hab h).elim
  · exact hab
  · exact (ha b hab (HenkinEq.symm S hS hcons h)).elim

theorem exists_isRepresentative_henkinFunc {k : ℕ} (f : L.Func k) (v : Fin k → V) :
    ∃ y, IsRepresentative S y ∧
      HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
        (Semiterm.fvar y) : Formula V L).val := by
  set t : Semiterm V L 0 := Semiterm.func f (fun i ↦ Semiterm.fvar (v i))
  have h₁ : S.internalize V ⊢ ∃¹ (Semiformula.equal t.bShift (Semiterm.bvar 0)) :=
    TProof.ex_intro! _ t <| by simpa [Semiformula.equal] using tprovable_equal_refl S t
  obtain ⟨u, hu⟩ := (henkinSet_exs_iff S hS hcons).mp (henkinSet_of_tprovable S h₁)
  obtain ⟨a, ha, hau⟩ := exists_isRepresentative S hS hcons u
  have h₂ : HenkinSet S (Semiformula.equal t (Semiterm.fvar u) : Formula V L).val := by
    simpa [Semiformula.equal] using hu
  exact ⟨a, ha, henkinSet_equal_trans S hS hcons h₂ (HenkinEq.symm S hS hcons hau)⟩

theorem IsRepresentative.eq_of_henkinFunc {k : ℕ} (f : L.Func k) (v : Fin k → V) {y y' : V}
    (hy : IsRepresentative S y) (hy' : IsRepresentative S y')
    (h : HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
      (Semiterm.fvar y) : Formula V L).val)
    (h' : HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
      (Semiterm.fvar y') : Formula V L).val) : y = y' :=
  hy.eq_of_henkinEq S hS hcons hy'
    (henkinSet_equal_trans S hS hcons (henkinSet_equal_symm S hS hcons h) h')

theorem henkinSet_equal_fvar_iff {a b : V} (ha : IsRepresentative S a) (hb : IsRepresentative S b) :
    HenkinSet S (Semiformula.equal (Semiterm.fvar a) (Semiterm.fvar b) : Formula V L).val ↔
      a = b :=
  ⟨fun h ↦ ha.eq_of_henkinEq S hS hcons hb h, by rintro rfl; exact HenkinEq.refl S a⟩

end equality

section operators

variable [L.Eq]

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

@[simp] theorem henkinDomain_val (a : V) : (henkinDomain S).val ![a] ↔ IsRepresentative S a := by
  simp [henkinDomain, henkinDomainDef, Semiformula.Operator.val, IsRepresentative, HenkinEq,
    Semiformula.equal, numeral_eq_natCast, quote_rel_def]

omit [L.Eq] in
@[simp] theorem henkinRel_val {k : ℕ} (R : L.Rel k) (v : Fin k → V) :
    (henkinRel S R).val v ↔
      HenkinSet S (Semiformula.rel R (fun i ↦ Semiterm.fvar (v i)) : Formula V L).val := by
  simp [henkinRel, henkinRelDef, Semiformula.Operator.val]
  simp only [numeral_eq_natCast, ← and_assoc, ← eq_matrixToVec_iff, exists_eq_left]
  rfl

@[simp] theorem henkinFunc_val {k : ℕ} (f : L.Func k) (z : V) (v : Fin k → V) :
    (henkinFunc S f).val (z :> v) ↔
      HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
        (Semiterm.fvar z) : Formula V L).val := by
  simp [henkinFunc, henkinFuncDef, Semiformula.Operator.val]
  simp only [numeral_eq_natCast, ← and_assoc, ← eq_matrixToVec_iff, exists_eq_left]
  rfl

end operators

end termModel

end FFL.FirstOrder.Arithmetic.Bootstrapping
