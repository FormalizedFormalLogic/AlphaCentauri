module

public import AlphaCentauri.Bootstrapping.Proof.Substitution
public import Foundation.FirstOrder.Incompleteness.Consistency

/-!
# Henkin completion inside $\mathsf{PA}$

Henkin's construction carried out in a model `V` of $\mathsf{PA}$: the Henkin formulas, the
contexts of the decision sequence, and the closure properties of the formulas decided positively.
The free variables `^&u` of internal formulas play the role of the Henkin constants.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
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

lemma not_derivable_insert_neg_henkinFormula (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
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

lemma IsHenkinContext.neg_henkinFormula_mem (hc : IsHenkinContext S c) (n : V) :
    neg L (henkinFormula L n (n + c n)) ∈ c (n + 1) := by
  rw [hc.2 n, henkinStep]
  simp

lemma IsHenkinContext.mem_succ_of_mem (hc : IsHenkinContext S c) {n x : V} (h : x ∈ c n) :
    x ∈ c (n + 1) := by
  rw [hc.2 n, henkinStep]
  simp [h]

lemma IsHenkinContext.mem_decision (hc : IsHenkinContext S c) (n : V) :
    (open Classical in
      if Derivable S (insert (neg L (henkinFormula L n (n + c n)))
        (insert (formulaOfCode L n) (c n))) then neg L (formulaOfCode L n)
      else formulaOfCode L n) ∈ c (n + 1) := by
  rw [hc.2 n, henkinStep]
  simp

lemma henkinMem_iff {n : V} (hn : IsFormula L n) :
    HenkinMem S c n ↔ Derivable S (insert (neg L (henkinFormula L n (n + c n)))
      (insert (formulaOfCode L n) (c n))) := by
  simp [HenkinMem, hn, formulaOfCode_of_isFormula hn]

lemma IsHenkinContext.neg_mem_of_henkinMem (hc : IsHenkinContext S c) {n : V}
    (h : HenkinMem S c n) : neg L n ∈ c (n + 1) := by
  have := hc.mem_decision n
  rwa [ite_eq_left ((henkinMem_iff h.isFormula).mp h), formulaOfCode_of_isFormula h.isFormula]
    at this

lemma IsHenkinContext.mem_of_not_henkinMem (hc : IsHenkinContext S c) {n : V}
    (hn : IsFormula L n) (h : ¬HenkinMem S c n) : n ∈ c (n + 1) := by
  have := hc.mem_decision n
  rwa [ite_eq_right (mt (henkinMem_iff hn).mpr h), formulaOfCode_of_isFormula hn] at this

lemma isFormulaSet_context (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) (n : V) :
    IsFormulaSet L (c n) := by
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

lemma IsHenkinContext.mem_of_le (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c)
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

lemma henkinMem_of_forall_mem (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
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

lemma exists_forall_mem_context (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c)
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

end FFL.FirstOrder.Arithmetic.Bootstrapping
