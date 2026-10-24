module

public import AlphaCentauri.Bootstrapping.Proof.Substitution
public import Foundation.FirstOrder.Incompleteness.Consistency

/-!
# Henkin completion inside $\mathsf{PA}$

Henkin's construction carried out in a model `V` of $\mathsf{PA}$: the Henkin formulas, the
contexts of the decision sequence, and the closure properties of the formulas decided positively.
The free variables `^&u` of internal formulas play the role of the Henkin constants. The decision
sequence exists and is unique, and the set of formulas decided positively along it, the Henkin set,
is $\Delta_2$-definable, by a formula `henkinSetDef S` that does not depend on the model.

## References

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.25]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

section construction

variable (L : Language) [L.Encodable] [L.LORDefinable]

open Classical in
/-- The formula with code `n`, and `⊤` if `n` is not the code of a formula. -/
noncomputable def formulaOfCode (n : V) : V := if IsFormula L n then n else ^⊤

open Classical in
/-- The Henkin formula `∃x α → α(^&u)` of the code `n = ⌜∃x α⌝` with the free variable `^&u` as
its witness, and `⊤` if `n` is not the code of an existential formula. -/
noncomputable def henkinFormula (n u : V) : V :=
  if IsFormula L n ∧ ∃ p < n, n = ^∃ p then imp L n (substs1 L ^&u (π₂ (n - 1))) else ^⊤

variable {L} (S : Theory L) [S.Δ₁]

open Classical in
/-- The context after the `n`-th decision, given the context `s` before it. It extends `s` by the
negation of the Henkin formula of `n` with the witness `^&(n + s)`, and by the negation of the
formula with code `n` if the sequent of `s`, that negated Henkin formula and the formula is
derivable, and by the formula itself otherwise. -/
noncomputable def henkinStep (n s : V) : V :=
  insert (neg L (henkinFormula L n (n + s)))
    (insert (if Derivable S (insert (neg L (henkinFormula L n (n + s)))
        (insert (formulaOfCode L n) s)) then neg L (formulaOfCode L n) else formulaOfCode L n) s)

/-- `c` is the sequence of contexts of the decisions: `c 0` is empty and `c (n + 1)` is
`henkinStep S n (c n)`. -/
def IsHenkinContext (c : V → V) : Prop := c 0 = ∅ ∧ ∀ n, c (n + 1) = henkinStep S n (c n)

/-- The formula `x` is decided positively along the contexts `c`: the sequent of `c x`, `x` and
the negated Henkin formula of `x` with the witness `^&(x + c x)` is derivable. -/
def HenkinMem (c : V → V) (x : V) : Prop :=
  IsFormula L x ∧ Derivable S (insert (neg L (henkinFormula L x (x + c x))) (insert x (c x)))

lemma HenkinMem.isFormula {c : V → V} {x : V} (h : HenkinMem S c x) : IsFormula L x := h.1

section formula

lemma isFormula_formulaOfCode (n : V) : IsFormula L (formulaOfCode L n) := by
  unfold formulaOfCode
  split_ifs with h <;> simp [h]

lemma formulaOfCode_of_isFormula {n : V} (h : IsFormula L n) : formulaOfCode L n = n :=
  ite_eq_left h

lemma henkinFormula_exs {α : V} (hα : IsSemiformula L 1 α) (u : V) :
    henkinFormula L (^∃ α) u = imp L (^∃ α) (substs1 L ^&u α) := by
  unfold henkinFormula
  rw [ite_eq_left ⟨by simpa using hα, α, by simp, rfl⟩]
  simp [qqExs]

lemma isFormula_henkinFormula (n u : V) : IsFormula L (henkinFormula L n u) := by
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

variable {S}

lemma Derivable.of_and_left {s p q : V} (h : Derivable S (insert (p ^⋏ q) s)) :
    Derivable S (insert p s) := by
  obtain ⟨hpq, hs⟩ := IsFormulaSet.insert_iff.mp h.isFormulaSet
  obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq
  have hF : IsFormulaSet L (insert (p ^⋏ q) (insert p s)) := by simp [hpq, hp, hs]
  have h₁ : (p ^⋏ q ⫽ s) ⊆ (p ^⋏ q ⫽ p ⫽ s) := by
    intro x hx
    simp at hx ⊢
    tauto
  apply Derivable.cut (p ^⋏ q) (.wk hF h₁ h)
  rw [neg_and hp.isUFormula hq.isUFormula]
  exact .or (.em (by simp [hp, hq, hs]) p (by simp) (by simp))

lemma Derivable.of_and_right {s p q : V} (h : Derivable S (insert (p ^⋏ q) s)) :
    Derivable S (insert q s) := by
  obtain ⟨hpq, hs⟩ := IsFormulaSet.insert_iff.mp h.isFormulaSet
  obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq
  have hF : IsFormulaSet L (insert (p ^⋏ q) (insert q s)) := by simp [hpq, hq, hs]
  have h₁ : (p ^⋏ q ⫽ s) ⊆ (p ^⋏ q ⫽ q ⫽ s) := by
    intro x hx
    simp at hx ⊢
    tauto
  apply Derivable.cut (p ^⋏ q) (.wk hF h₁ h)
  rw [neg_and hp.isUFormula hq.isUFormula]
  exact .or (.em (by simp [hp, hq, hs]) q (by simp) (by simp))

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
    have h₁ : Derivable S (insert (^∃ α) Γ) := hd.of_and_left
    have h₂ : Derivable S (insert (neg L (^∃ α)) Γ) :=
      Derivable.neg_exs_of_fresh hS le_add_self
        (le_trans hαn.le le_self_add) hα hd.of_and_right
    exact h (h₁.cut _ h₂)
  · rw [henkinFormula, ite_eq_right hn, neg_verum] at hd
    exact h (.cut ^⊤ (.verum (by simp [hΓ]) (by simp)) (by rwa [neg_verum]))

end derivable

section context

variable {S} {c : V → V}

private lemma IsHenkinContext.neg_henkinFormula_mem (hc : IsHenkinContext S c) (n : V) :
    neg L (henkinFormula L n (n + c n)) ∈ c (n + 1) := by
  rw [hc.2 n, henkinStep]
  simp

private lemma IsHenkinContext.mem_succ_of_mem (hc : IsHenkinContext S c) {n x : V} (h : x ∈ c n) :
    x ∈ c (n + 1) := by
  rw [hc.2 n, henkinStep]
  simp [h]

private lemma IsHenkinContext.mem_decision (hc : IsHenkinContext S c) (n : V) :
    (open Classical in
      if Derivable S (insert (neg L (henkinFormula L n (n + c n)))
        (insert (formulaOfCode L n) (c n))) then neg L (formulaOfCode L n)
      else formulaOfCode L n) ∈ c (n + 1) := by
  rw [hc.2 n, henkinStep]
  simp

private lemma henkinMem_iff {n : V} (hn : IsFormula L n) :
    HenkinMem S c n ↔ Derivable S (insert (neg L (henkinFormula L n (n + c n)))
      (insert (formulaOfCode L n) (c n))) := by
  simp [HenkinMem, hn, formulaOfCode_of_isFormula hn]

private lemma IsHenkinContext.neg_mem_of_henkinMem (hc : IsHenkinContext S c) {n : V}
    (h : HenkinMem S c n) : neg L n ∈ c (n + 1) := by
  have := hc.mem_decision n
  rwa [ite_eq_left ((henkinMem_iff h.isFormula).mp h), formulaOfCode_of_isFormula h.isFormula]
    at this

private lemma IsHenkinContext.mem_of_not_henkinMem (hc : IsHenkinContext S c) {n : V}
    (hn : IsFormula L n) (h : ¬HenkinMem S c n) : n ∈ c (n + 1) := by
  have := hc.mem_decision n
  rwa [ite_eq_right (mt (henkinMem_iff hn).mpr h), formulaOfCode_of_isFormula hn] at this

private lemma isFormulaSet_context (hc : IsHenkinContext S c)
    (hdef : 𝚫ᴬ_[2]-Function₁[V] c) (n : V) : IsFormulaSet L (c n) := by
  have : 𝚫ᴬ_[2]-Predicate[V] IsFormulaSet L :=
    Bounding.HierarchySymbol.Definable.of_lt IsFormulaSet.definable (by simp)
  apply InductionOnHierarchy.succ_induction_sigma 𝚫 2 (P := fun n ↦ IsFormulaSet L (c n))
    (by definability)
  · simp [hc.1]
  · intro n ih
    rw [hc.2 n, henkinStep]
    simp only [IsFormulaSet.insert_iff]
    exact ⟨by simpa using isFormula_henkinFormula n (n + c n),
      by split_ifs <;> simp [isFormula_formulaOfCode], ih⟩

private lemma IsHenkinContext.mem_of_le (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c)
    {n m x : V} (hnm : n ≤ m) (h : x ∈ c n) : x ∈ c m := by
  obtain ⟨k, rfl⟩ := exists_add_of_le hnm
  clear hnm
  revert k
  apply InductionOnHierarchy.succ_induction_sigma 𝚫 2 (P := fun k ↦ x ∈ c (n + k))
    (by definability)
  · simpa using h
  · intro k ih
    rw [← add_assoc]
    exact hc.mem_succ_of_mem ih

end context

section theorems

variable {c : V → V}

/-- No context of the decision sequence is derivable when `S` is consistent. -/
theorem not_derivable_of_isHenkinContext (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) (n : V) :
    ¬Derivable S (c n) := by
  have : 𝚫ᴬ_[2]-Predicate[V] Derivable S :=
    Bounding.HierarchySymbol.Definable.of_lt (Derivable.definable (T := S)) (by simp)
  apply InductionOnHierarchy.succ_induction_sigma 𝚫 2 (P := fun n ↦ ¬Derivable S (c n))
    (by definability)
  · rw [hc.1]
    intro h
    apply hcons
    have : (⌜(⊥ : Sentence L)⌝ : V) = ^⊥ := by simp [Sentence.quote_def, Semiformula.quote_def]
    rw [this]
    exact (h.wk (by simp) (by simp)).toProvable
  · intro n ih h
    rw [hc.2 n, henkinStep] at h
    by_cases hD : Derivable S (insert (neg L (henkinFormula L n (n + c n)))
        (insert (formulaOfCode L n) (c n)))
    · rw [ite_eq_left hD] at h
      exact not_derivable_insert_neg_henkinFormula hS (isFormulaSet_context hc hdef n) n ih
        (.cut (formulaOfCode L n) hD.exchange h.exchange)
    · rw [ite_eq_right hD] at h
      exact hD h

private lemma henkinMem_of_forall_mem (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c)
    {s ψ : V} (hψ : IsFormula L ψ) (hs : ∃ m, ∀ p ∈ s, p ∈ c m)
    (h : Derivable S (insert ψ s)) : HenkinMem S c ψ := by
  by_contra hM
  obtain ⟨m, hm⟩ := hs
  have h₁ : (ψ ⫽ s) ⊆ c (max m (ψ + 1)) := by
    intro x hx
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · exact hc.mem_of_le hdef (le_max_right _ _) (hc.mem_of_not_henkinMem hψ hM)
    · exact hc.mem_of_le hdef (le_max_left _ _) (hm x hx)
  exact not_derivable_of_isHenkinContext S hS hcons hc hdef (max m (ψ + 1))
    (h.wk (isFormulaSet_context hc hdef _) h₁)

private lemma exists_forall_mem_context (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c)
    {s : V} (h : ∀ p ∈ s, ∃ m, p ∈ c m) : ∃ m, ∀ p ∈ s, p ∈ c m := by
  have key : ∀ y, ∃ m, ∀ p ∈ s, p < y → p ∈ c m := by
    apply InductionOnHierarchy.succ_induction_sigma 𝚺 2
      (P := fun y ↦ ∃ m, ∀ p ∈ s, p < y → p ∈ c m) (by definability)
    · use 0
      intro p _ hp
      simp at hp
    · rintro y ⟨m, hm⟩
      by_cases hy : y ∈ s
      · obtain ⟨m', hm'⟩ := h y hy
        use max m m'
        intro p hp hpy
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hpy) with hpy | rfl
        · exact hc.mem_of_le hdef (le_max_left _ _) (hm p hp hpy)
        · exact hc.mem_of_le hdef (le_max_right _ _) hm'
      · use m
        intro p hp hpy
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hpy) with hpy | rfl
        · exact hm p hp hpy
        · exact absurd hp hy
  obtain ⟨m, hm⟩ := key (s + 1)
  exact ⟨m, fun p hp ↦ hm p hp (lt_of_lt_of_le (lt_of_mem hp) le_self_add)⟩

/-- If `ψ` is derivable from the negations of formulas decided positively, then `ψ` is decided
positively. -/
theorem henkinMem_of_derivable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) {s ψ : V}
    (hψ : IsFormula L ψ) (hs : ∀ p ∈ s, HenkinMem S c (neg L p)) (h : Derivable S (insert ψ s)) :
    HenkinMem S c ψ := by
  have h₁ : ∀ p ∈ s, ∃ m, p ∈ c m := by
    intro p hp
    have hM := hs p hp
    have hp' : IsFormula L p := IsSemiformula.neg_iff.mp hM.isFormula
    use neg L p + 1
    simpa [IsUFormula.neg_neg hp'.isUFormula] using hc.neg_mem_of_henkinMem hM
  exact henkinMem_of_forall_mem S hS hcons hc hdef hψ (exists_forall_mem_context S hc hdef h₁) h

/-- Provable formulas are decided positively. -/
theorem henkinMem_of_provable (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) {φ : V}
    (hφ : IsFormula L φ) (h : Provable S φ) : HenkinMem S c φ := by
  apply (henkinMem_iff hφ).mpr
  apply h.toDerivable.wk
  · simp [isFormula_henkinFormula, isFormula_formulaOfCode, isFormulaSet_context hc hdef]
  · intro x hx
    obtain rfl : x = φ := by simpa using hx
    simp [formulaOfCode_of_isFormula hφ]

/-- The negation of a formula is decided positively if and only if the formula is not.

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.25] -/
theorem henkinMem_neg_iff (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) {φ : V}
    (hφ : IsFormula L φ) : HenkinMem S c (neg L φ) ↔ ¬HenkinMem S c φ := by
  constructor
  · intro h₁ h₂
    have e₁ := hc.neg_mem_of_henkinMem h₂
    have e₂ := hc.neg_mem_of_henkinMem h₁
    rw [IsUFormula.neg_neg hφ.isUFormula] at e₂
    exact not_derivable_of_isHenkinContext S hS hcons hc hdef (max (φ + 1) (neg L φ + 1))
      (.em (isFormulaSet_context hc hdef _) φ (hc.mem_of_le hdef (le_max_right _ _) e₂)
        (hc.mem_of_le hdef (le_max_left _ _) e₁))
  · intro h
    exact henkinMem_of_forall_mem S hS hcons hc hdef (s := {φ}) hφ.neg
      ⟨φ + 1, by simpa using hc.mem_of_not_henkinMem hφ h⟩
      (.em (by simp [hφ]) φ (by simp) (by simp))

/-- Every Henkin formula with witness `^&(n + c n)` is decided positively. -/
theorem henkinMem_henkinFormula (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) (n : V) :
    HenkinMem S c (henkinFormula L n (n + c n)) := by
  have hH := isFormula_henkinFormula (L := L) n (n + c n)
  exact henkinMem_of_forall_mem S hS hcons hc hdef (s := {neg L (henkinFormula L n (n + c n))})
    hH ⟨n + 1, by simpa using hc.neg_henkinFormula_mem n⟩
    (.em (by simp [hH]) (henkinFormula L n (n + c n)) (by simp) (by simp))

/-- The formulas decided positively are closed under modus ponens. -/
theorem henkinMem_modus_ponens (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) {α β : V}
    (hα : HenkinMem S c α) (hαβ : HenkinMem S c (imp L α β)) : HenkinMem S c β := by
  have hF : IsFormula L α ∧ IsFormula L β := by simpa using hαβ.isFormula
  have e : neg L (imp L α β) = α ^⋏ neg L β := by
    rw [imp, neg_or hF.1.isUFormula.neg hF.2.isUFormula, IsUFormula.neg_neg hF.1.isUFormula]
  apply henkinMem_of_derivable S hS hcons hc hdef
    (s := insert (neg L α) {neg L (imp L α β)}) hF.2
  · intro p hp
    obtain rfl | rfl : p = neg L α ∨ p = neg L (imp L α β) := by simpa using hp
    · simpa [IsUFormula.neg_neg hF.1.isUFormula] using hα
    · simpa [IsUFormula.neg_neg hαβ.isFormula.isUFormula] using hαβ
  · exact .ofSetEq (s' := insert (α ^⋏ neg L β) (insert β (insert (neg L α) (∅ : V))))
      (fun x ↦ by simp [e]; tauto)
      (.and (.em (by simp [hF.1, hF.2]) α (by simp) (by simp))
        (.em (by simp [hF.1, hF.2]) β (by simp) (by simp)))

/-- If an existential formula is decided positively, so is one of its instances at a free
variable.

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.25] -/
theorem exists_henkinMem_substs1 (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) {α : V}
    (hα : IsSemiformula L 1 α) (h : HenkinMem S c (^∃ α)) :
    ∃ u, HenkinMem S c (substs1 L ^&u α) := by
  have h₁ := henkinMem_henkinFormula S hS hcons hc hdef (^∃ α)
  rw [henkinFormula_exs hα] at h₁
  exact ⟨_, henkinMem_modus_ponens S hS hcons hc hdef h h₁⟩

end theorems

end construction

section sequence

variable {L : Language} [L.Encodable] [L.LORDefinable] (S : Theory L) [S.Δ₁]

section definability

instance formulaOfCode.definable : 𝚺ᴬ₁-Function₁ (formulaOfCode (V := V) L) := by
  have : 𝚺ᴬ₁.Definable fun v : Fin 2 → V ↦
      (IsFormula L (v 1) ∧ v 0 = v 1) ∨ (¬IsFormula L (v 1) ∧ v 0 = ^⊤) := by
    definability
  apply this.of_iff
  intro v
  by_cases h : IsFormula L (v 1) <;> simp [formulaOfCode, h]

instance henkinFormula.definable : 𝚺ᴬ₁-Function₂ (henkinFormula (V := V) L) := by
  have : 𝚺ᴬ₁.Definable fun v : Fin 3 → V ↦
      ((IsFormula L (v 1) ∧ ∃ p < v 1, v 1 = ^∃ p) ∧
          v 0 = imp L (v 1) (substs1 L ^&(v 2) (π₂ (v 1 - 1)))) ∨
        (¬(IsFormula L (v 1) ∧ ∃ p < v 1, v 1 = ^∃ p) ∧ v 0 = ^⊤) := by
    definability
  apply this.of_iff
  intro v
  by_cases h : IsFormula L (v 1) ∧ ∃ p < v 1, v 1 = ^∃ p <;> simp [henkinFormula, h]

instance henkinStep.definable : 𝚫ᴬ_[2]-Function₂ (henkinStep (V := V) S) := by
  have hD : 𝚺ᴬ₁.Definable fun v : Fin 3 → V ↦
      Derivable S (insert (neg L (henkinFormula L (v 1) (v 1 + v 2)))
        (insert (formulaOfCode L (v 1)) (v 2))) := by
    definability
  have hpos : 𝚺ᴬ₁.Definable fun v : Fin 3 → V ↦
      v 0 = insert (neg L (henkinFormula L (v 1) (v 1 + v 2)))
        (insert (neg L (formulaOfCode L (v 1))) (v 2)) := by
    definability
  have hneg : 𝚺ᴬ₁.Definable fun v : Fin 3 → V ↦
      v 0 = insert (neg L (henkinFormula L (v 1) (v 1 + v 2)))
        (insert (formulaOfCode L (v 1)) (v 2)) := by
    definability
  have hD₂ := hD.of_lt (Γ := 𝚫) (s := 2) (by simp)
  apply (HierarchySymbol.Definable.or (hD₂.and <| hpos.of_lt (by simp))
    (hD₂.notDelta.and <| hneg.of_lt (by simp))).of_iff
  intro v
  by_cases h : Derivable S (insert (neg L (henkinFormula L (v 1) (v 1 + v 2)))
    (insert (formulaOfCode L (v 1)) (v 2))) <;> simp [henkinStep, h]

end definability

/-- `y` is the sequence of the first `n + 1` contexts of the decision sequence of the Henkin
completion of `S`. -/
def IsHenkinSeq (n y : V) : Prop :=
  Seq y ∧ lh y = n + 1 ∧ znth y 0 = ∅ ∧ ∀ i < n, znth y (i + 1) = henkinStep S i (znth y i)

instance IsHenkinSeq.definable : 𝚫ᴬ_[2]-Relation (IsHenkinSeq (V := V) S) := by
  unfold IsHenkinSeq
  definability

private lemma exists_isHenkinSeq (n : V) : ∃ y, IsHenkinSeq S n y := by
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

/-- There is a $\Delta_2$-definable Henkin context. -/
theorem exists_isHenkinContext :
    ∃ c : V → V, IsHenkinContext S c ∧ 𝚫ᴬ_[2]-Function₁[V] c := by
  choose f hf using exists_isHenkinSeq (V := V) S
  have hzero : znth (f 0) 0 = ∅ := (hf 0).2.2.1
  have hsucc : ∀ n, znth (f (n + 1)) (n + 1) = henkinStep S n (znth (f n) n) := by
    intro n
    rw [(hf (n + 1)).2.2.2 n (lt_add_one n), (hf (n + 1)).znth_eq (hf n) le_self_add le_rfl]
  have hσ : 𝚺ᴬ_[2].Definable fun v : Fin 2 → V ↦
      ∃ y, IsHenkinSeq S (v 1) y ∧ v 0 = znth y (v 1) := by
    definability
  have hπ : 𝚷ᴬ_[2].Definable fun v : Fin 2 → V ↦
      ∀ y, IsHenkinSeq S (v 1) y → v 0 = znth y (v 1) := by
    definability
  have hdef : 𝚫ᴬ_[2]-Function₁[V] fun n ↦ znth (f n) n := by
    apply HierarchySymbol.Definable.of_sigma_of_pi
    · apply hσ.of_iff
      intro v
      constructor
      · intro h
        exact ⟨f (v 1), hf (v 1), h⟩
      · rintro ⟨y, hy, h⟩
        rw [h]
        exact hy.znth_eq (hf (v 1)) le_rfl le_rfl
    · apply hπ.of_iff
      intro v
      constructor
      · intro h y hy
        rw [h]
        exact (hf (v 1)).znth_eq hy le_rfl le_rfl
      · intro h
        exact h (f (v 1)) (hf (v 1))
  exact ⟨fun n ↦ znth (f n) n, ⟨hzero, hsucc⟩, hdef⟩

variable {S} in
lemma IsHenkinContext.unique {c c' : V → V} (hc : IsHenkinContext S c)
    (hc' : IsHenkinContext S c') (hdef : 𝚫ᴬ_[2]-Function₁[V] c)
    (hdef' : 𝚫ᴬ_[2]-Function₁[V] c') : c = c' := by
  have hP : 𝚫ᴬ_[2]-Predicate fun n : V ↦ c n = c' n :=
    HierarchySymbol.DefinableRel.comp HierarchySymbol.DefinableRel.eq hdef.of_delta
      hdef'.of_delta
  have hzero : c 0 = c' 0 := by rw [hc.1, hc'.1]
  have hsucc : ∀ n, c n = c' n → c (n + 1) = c' (n + 1) := by
    intro n ih
    rw [hc.2, hc'.2, ih]
  funext n
  exact InductionOnHierarchy.succ_induction_sigma 𝚫 2 hP hzero hsucc n

/-- The contexts of the decision sequence of the Henkin completion of `S`. -/
noncomputable def henkinContext : V → V := Classical.choose (exists_isHenkinContext (V := V) S)

lemma isHenkinContext_henkinContext : IsHenkinContext S (henkinContext S : V → V) :=
  (Classical.choose_spec (exists_isHenkinContext (V := V) S)).1

lemma henkinContext_definable : 𝚫ᴬ_[2]-Function₁[V] (henkinContext S) :=
  (Classical.choose_spec (exists_isHenkinContext (V := V) S)).2

/-- The Henkin set of `S`: the formulas decided positively along `henkinContext S`. -/
def HenkinSet (x : V) : Prop := HenkinMem S (henkinContext S) x

/-- The Henkin set is $\Delta_2$-definable.

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.25] -/
theorem henkinSet_definable : 𝚫ᴬ_[2]-Predicate[V] (HenkinSet S) := by
  have hmem : 𝚺ᴬ₁-Relation fun x c : V ↦
      IsFormula L x ∧ Derivable S (insert (neg L (henkinFormula L x (x + c))) (insert x c)) := by
    definability
  have hmem₂ : 𝚫ᴬ_[2]-Relation fun x c : V ↦
      IsFormula L x ∧ Derivable S (insert (neg L (henkinFormula L x (x + c))) (insert x c)) :=
    hmem.of_lt (by simp)
  have hc : 𝚺ᴬ_[2]-Function₁[V] henkinContext S := (henkinContext_definable S).of_delta
  exact hmem₂.comp (HierarchySymbol.DefinableFunction.var 0) hc

lemma HenkinSet.isFormula {x : V} (h : HenkinSet S x) : IsFormula L x := h.1

lemma HenkinSet.of_provable {φ : V} (hφ : IsFormula L φ) (h : Provable S φ) : HenkinSet S φ :=
  henkinMem_of_provable S (isHenkinContext_henkinContext S) (henkinContext_definable S) hφ h

lemma not_derivable_henkinContext (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (n : V) : ¬Derivable S (henkinContext S n) :=
  not_derivable_of_isHenkinContext S hS hcons (isHenkinContext_henkinContext S)
    (henkinContext_definable S) n

variable {S} (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

lemma HenkinSet.neg_iff {φ : V} (hφ : IsFormula L φ) :
    HenkinSet S (neg L φ) ↔ ¬HenkinSet S φ :=
  henkinMem_neg_iff S hS hcons (isHenkinContext_henkinContext S) (henkinContext_definable S) hφ

lemma HenkinSet.of_derivable {s ψ : V} (hψ : IsFormula L ψ)
    (hs : ∀ p ∈ s, HenkinSet S (neg L p)) (h : Derivable S (insert ψ s)) : HenkinSet S ψ :=
  henkinMem_of_derivable S hS hcons (isHenkinContext_henkinContext S) (henkinContext_definable S)
    hψ hs h

lemma HenkinSet.modus_ponens {α β : V} (hα : HenkinSet S α) (hαβ : HenkinSet S (imp L α β)) :
    HenkinSet S β :=
  henkinMem_modus_ponens S hS hcons (isHenkinContext_henkinContext S) (henkinContext_definable S)
    hα hαβ

lemma HenkinSet.exists_substs1 {α : V} (hα : IsSemiformula L 1 α) (h : HenkinSet S (^∃ α)) :
    ∃ u, HenkinSet S (substs1 L ^&u α) :=
  exists_henkinMem_substs1 S hS hcons (isHenkinContext_henkinContext S)
    (henkinContext_definable S) hα h

lemma HenkinSet.henkinFormula (n : V) :
    HenkinSet S (henkinFormula L n (n + henkinContext S n)) :=
  henkinMem_henkinFormula S hS hcons (isHenkinContext_henkinContext S)
    (henkinContext_definable S) n

end sequence

section explicit

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
private lemma IsHenkinSeq.znth_eq_henkinContext {n y : V} (hy : IsHenkinSeq S n y) :
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

private lemma eq_henkinContext_iff_exists {c n : V} :
    c = henkinContext S n ↔ ∃ y, IsHenkinSeq S n y ∧ c = znth y n := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := exists_isHenkinSeq S n
    exact ⟨y, hy, h.trans hy.znth_eq_henkinContext.symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy.znth_eq_henkinContext

private lemma eq_henkinContext_iff_forall {c n : V} :
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

end explicit

end FFL.FirstOrder.Arithmetic.Bootstrapping
