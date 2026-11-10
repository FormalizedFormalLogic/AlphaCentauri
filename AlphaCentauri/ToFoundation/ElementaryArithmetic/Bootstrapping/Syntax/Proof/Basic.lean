module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.Bootstrapping.Syntax.Formula.Functions
public import AlphaCentauri.ToFoundation.ElementaryArithmetic.Bootstrapping.Syntax.Theory
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic

/-!
# Derivations in models of $\mathsf{EA}$

The file `Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Proof/Basic.lean` on codes of
derivations, ported to models of $\mathsf{EA}$: sets of formulas `IsFormulaSet`, the shift
`setShift` of a set of formulas, the codes `axL`, …, `axm` of the inference rules, and the
predicates `Derivation T`, `DerivationOf T`, `Derivable T`, `Proof T` and `Provable T` for a
theory `T` whose axioms are locally $\Delta_0$ in the model. The formulas are Foundation's
`isFormulaSet`, `setShiftGraph`, `axLGraph`, …, `axmGraph`, `Derivation.blueprint`, `derivation`,
`derivationOf`, `derivable`, `proof` and `provable`; derivations form a strongly finite fixpoint,
with induction on locally $\Delta_0$ predicates.

- [HP98, §V.3]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]
  {L : Language} [L.Encodable] [L.LORDefinable]

variable (L) in
/-- The predicate that every element of `s` is the code of a formula. -/
def IsFormulaSet (s : V) : Prop := ∀ p ∈ s, IsFormula L p

namespace IsFormulaSet

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (isFormulaSet)

instance defined : 𝚫ᴬ₁-Predicate[V] IsFormulaSet L via isFormulaSet L := .mk
  ⟨by intro v; simp [isFormulaSet], by intro v; simp [isFormulaSet]; rfl⟩

instance definable : 𝚫ᴬ₁-Predicate[V] IsFormulaSet L := defined.to_definable

instance definable' {Γ : Polarity} {m : ℕ} : Γᴬ_[m + 1]-Predicate[V] IsFormulaSet L :=
  .of_deltaOne definable

@[simp] lemma empty : IsFormulaSet L (∅ : V) := fun p ↦ by simp

@[simp] lemma singleton {p : V} : IsFormulaSet L ({p} : V) ↔ IsFormula L p := by
  constructor
  · intro h; exact h p (by simp)
  · intro h p; simp only [mem_singleton_iff]
    rintro rfl; exact h

@[simp] lemma insert_iff {p s : V} :
    IsFormulaSet L (insert p s) ↔ IsFormula L p ∧ IsFormulaSet L s := by
  constructor
  · intro h; exact ⟨h p (by simp), fun q hq ↦ h q (by simp [hq])⟩
  · rintro ⟨hp, hs⟩ q; simp only [mem_bitInsert_iff]; rintro (rfl | hqs)
    · exact hp
    · exact hs q hqs

alias ⟨insert, _⟩ := insert_iff

@[simp] lemma union {s₁ s₂ : V} :
    IsFormulaSet L (s₁ ∪ s₂) ↔ IsFormulaSet L s₁ ∧ IsFormulaSet L s₂ :=
  ⟨fun h ↦ ⟨fun p hp ↦ h p (by simp [hp]), fun p hp ↦ h p (by simp [hp])⟩,
   fun h p hp ↦ by
    rcases mem_cup_iff.mp hp with (h₁ | h₂)
    · exact h.1 p h₁
    · exact h.2 p h₂⟩

end IsFormulaSet

lemma isFormulaSet_locallyDelta0 : LocallyDelta0Pred (IsFormulaSet (V := V) L) :=
  (LocallyDelta0.ball_lt_function (LocallyDelta0Function.var (0 : Fin 1)) <|
    (LocallyDelta0.mem (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 1)).imp <|
      isSemiformula_locallyDelta0.rel_comp₂ (LocallyDelta0Function.const 0)
        (LocallyDelta0Function.var 0)).of_iff fun _ ↦
    ⟨fun h x _ hx ↦ h x hx, fun h x hx ↦ h x (lt_of_mem hx) hx⟩

variable (L) in
lemma setShift_existsUnique (s : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ x ∈ s, y = shift L x := by
  obtain ⟨Y, hY⟩ := (shift_locallyDelta0 (V := V) (L := L)).bounded s
  have : LocallyDelta0Pred fun y ↦ ∃ x ∈ s, y = shift L x :=
    (LocallyDelta0.bexs_lt_function (LocallyDelta0Function.const s) <|
      (LocallyDelta0.mem (LocallyDelta0Function.var 0) (LocallyDelta0Function.const s)).and <|
        LocallyDelta0.eq (LocallyDelta0Function.var 1) <|
          shift_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)).of_iff fun v ↦
      ⟨fun ⟨x, hx, h⟩ ↦ ⟨x, lt_of_mem hx, hx, h⟩, fun ⟨x, _, hx, h⟩ ↦ ⟨x, hx, h⟩⟩
  apply this.finite_comprehension!
  use Y + 1
  rintro _ ⟨x, hx, rfl⟩
  exact lt_succ_iff_le.mpr <| hY ![x] fun _ ↦ by simpa using (lt_of_mem hx).le

variable (L) in
/-- The set of the shifts of the elements of `s`. -/
noncomputable def setShift (s : V) : V := Classical.choose! (setShift_existsUnique L s)

section setShift

lemma mem_setShift_iff {s y : V} : y ∈ setShift L s ↔ ∃ x ∈ s, y = shift L x :=
  Classical.choose!_spec (setShift_existsUnique L s) y

lemma IsFormulaSet.setShift {s : V} (h : IsFormulaSet L s) : IsFormulaSet L (setShift L s) := by
  simp only [IsFormulaSet, mem_setShift_iff, forall_exists_index, and_imp]
  rintro _ p hp rfl; exact (h p hp).shift

lemma shift_mem_setShift {p s : V} (h : p ∈ s) : shift L p ∈ setShift L s :=
  mem_setShift_iff.mpr ⟨p, h, rfl⟩

@[simp] lemma IsFormulaSet.setShift_iff {s : V} :
    IsFormulaSet L (Bootstrapping.setShift L s) ↔ IsFormulaSet L s :=
  ⟨by intro h p hp; simpa using h (shift L p) (shift_mem_setShift hp), IsFormulaSet.setShift⟩

@[simp] lemma mem_setShift_union {s t : V} :
    setShift L (s ∪ t) = setShift L s ∪ setShift L t := mem_ext <| by
  simp only [mem_setShift_iff, mem_cup_iff]; intro x
  constructor
  · rintro ⟨z, (hz | hz), rfl⟩
    · left; exact ⟨z, hz, rfl⟩
    · right; exact ⟨z, hz, rfl⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨z, Or.inl hz, rfl⟩
    · exact ⟨z, Or.inr hz, rfl⟩

@[simp] lemma mem_setShift_insert {x s : V} :
    setShift L (insert x s) = insert (shift L x) (setShift L s) := mem_ext <| by
  simp [mem_setShift_iff]

@[simp] lemma setShift_empty : setShift L (∅ : V) = ∅ := mem_ext <| by simp [mem_setShift_iff]

private lemma setShift_graph (t s : V) :
    t = setShift L s ↔ (∀ y ∈ t, ∃ x ∈ s, y = shift L x) ∧ (∀ x ∈ s, shift L x ∈ t) := by
  constructor
  · rintro rfl
    constructor
    · intro y hy; exact mem_setShift_iff.mp hy
    · intro x hx; exact mem_setShift_iff.mpr ⟨x, hx, rfl⟩
  · rintro ⟨h₁, h₂⟩
    apply mem_ext; intro y; constructor
    · intro hy; exact mem_setShift_iff.mpr (h₁ y hy)
    · intro hy
      rcases mem_setShift_iff.mp hy with ⟨x, hx, rfl⟩
      exact h₂ x hx

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (setShiftGraph) in
instance setShift.defined : 𝚺ᴬ₁-Function₁[V] setShift L via setShiftGraph L :=
  .mk fun v ↦ by simp [setShiftGraph, setShift_graph]

instance setShift.definable : 𝚺ᴬ₁-Function₁[V] setShift L := setShift.defined.to_definable

lemma setShift_locallyDelta0 : LocallyDelta0Function₁ (setShift (V := V) L) where
  graph := by
    have h₁ := LocallyDelta0.ball_lt_function (LocallyDelta0Function.var (V := V) (0 : Fin 2)) <|
      (LocallyDelta0.mem (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 1)).imp <|
        LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 2) <|
          (LocallyDelta0.mem (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 3)).and <|
            LocallyDelta0.eq (LocallyDelta0Function.var 1) <|
              (shift_locallyDelta0 (L := L)).comp₁ (LocallyDelta0Function.var 0)
    have h₂ := LocallyDelta0.ball_lt_function (LocallyDelta0Function.var (V := V) (1 : Fin 2)) <|
      (LocallyDelta0.mem (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 2)).imp <|
        LocallyDelta0.mem ((shift_locallyDelta0 (L := L)).comp₁ (LocallyDelta0Function.var 0))
          (LocallyDelta0Function.var 1)
    refine (h₁.and h₂).of_iff fun v ↦ (setShift_graph (v 0) (v 1)).trans ?_
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun y _ hy ↦ by obtain ⟨x, hx, h⟩ := h₁ y hy; exact ⟨x, lt_of_mem hx, hx, h⟩,
        fun x _ hx ↦ h₂ x hx⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun y hy ↦ by obtain ⟨x, _, hx, h⟩ := h₁ y (lt_of_mem hy) hy; exact ⟨x, hx, h⟩,
        fun x hx ↦ h₂ x (lt_of_mem hx) hx⟩
  bounded X := by
    obtain ⟨Y, hY⟩ := (shift_locallyDelta0 (V := V) (L := L)).bounded X
    use Exp.exp (Y + 1)
    intro v hv
    apply le_of_lt
    apply lt_exp_iff.mpr
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_setShift_iff.mp hy
    exact lt_succ_iff_le.mpr <| hY ![x] fun _ ↦ by
      simpa using le_trans (lt_of_mem hx).le (hv 0)

end setShift

section code

/-- The code of the derivation of `s` by the axiom `p, ¬p`. -/
noncomputable def axL (s p : V) : V := ⟪s, 0, p⟫ + 1

/-- The code of the derivation of `s` by the axiom `⊤`. -/
noncomputable def verumIntro (s : V) : V := ⟪s, 1, 0⟫ + 1

/-- The code of the derivation of `s` by the rule for `p ⋏ q` from `dp` and `dq`. -/
noncomputable def andIntro (s p q dp dq : V) : V := ⟪s, 2, p, q, dp, dq⟫ + 1

/-- The code of the derivation of `s` by the rule for `p ⋎ q` from `d`. -/
noncomputable def orIntro (s p q d : V) : V := ⟪s, 3, p, q, d⟫ + 1

/-- The code of the derivation of `s` by the rule for `∀ p` from `d`. -/
noncomputable def allIntro (s p d : V) : V := ⟪s, 4, p, d⟫ + 1

/-- The code of the derivation of `s` by the rule for `∃ p` with the witness `t` from `d`. -/
noncomputable def exsIntro (s p t d : V) : V := ⟪s, 5, p, t, d⟫ + 1

/-- The code of the derivation of `s` by weakening from `d`. -/
noncomputable def wkRule (s d : V) : V := ⟪s, 6, d⟫ + 1

/-- The code of the derivation of `s` by shifting the free variables of `d`. -/
noncomputable def shiftRule (s d : V) : V := ⟪s, 7, d⟫ + 1

/-- The code of the derivation of `s` by the cut on `p` from `d₁` and `d₂`. -/
noncomputable def cutRule (s p d₁ d₂ : V) : V := ⟪s, 8, p, d₁, d₂⟫ + 1

/-- The code of the derivation of `s` by the nonlogical axiom `p`. -/
noncomputable def axm (s p : V) : V := ⟪s, 9, p⟫ + 1

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (axLGraph verumIntroGraph andIntroGraph
  orIntroGraph allIntroGraph exsIntroGraph wkRuleGraph shiftRuleGraph cutRuleGraph axmGraph)

instance axL.defined : 𝚺ᴬ₀-Function₂[V] axL via axLGraph := .mk fun v ↦ by simp_all [axLGraph, axL]

instance axL.definable : 𝚺ᴬ₀-Function₂ (axL : V → V → V) := axL.defined.to_definable

instance verumIntro.defined : 𝚺ᴬ₀-Function₁[V] verumIntro via verumIntroGraph :=
  .mk fun v ↦ by simp_all [verumIntroGraph, verumIntro]

instance verumIntro.definable : 𝚺ᴬ₀-Function₁ (verumIntro : V → V) :=
  verumIntro.defined.to_definable

instance andIntro.defined :
    𝚺ᴬ₀-Function₅ (andIntro : V → V → V → V → V → V) via andIntroGraph :=
  .mk fun v ↦ by simp_all [andIntroGraph, andIntro]

instance andIntro.definable :
    𝚺ᴬ₀.DefinableFunction₅ (andIntro : V → V → V → V → V → V) :=
  andIntro.defined.to_definable

instance orIntro.defined : 𝚺ᴬ₀-Function₄ (orIntro : V → V → V → V → V) via orIntroGraph :=
  .mk fun v ↦ by simp_all [orIntroGraph, orIntro]

instance allIntro.defined : 𝚺ᴬ₀-Function₃ (allIntro : V → V → V → V) via allIntroGraph :=
  .mk fun v ↦ by simp_all [allIntroGraph, allIntro]

instance allIntro.definable : 𝚺ᴬ₀-Function₃ (allIntro : V → V → V → V) :=
  allIntro.defined.to_definable

instance exsIntro.defined : 𝚺ᴬ₀-Function₄ (exsIntro : V → V → V → V → V) via exsIntroGraph :=
  .mk fun v ↦ by simp_all [exsIntroGraph, numeral_eq_natCast, exsIntro]

instance exsIntro.definable : 𝚺ᴬ₀-Function₄ (exsIntro : V → V → V → V → V) :=
  exsIntro.defined.to_definable

instance wkRule.defined : 𝚺ᴬ₀-Function₂ (wkRule : V → V → V) via wkRuleGraph :=
  .mk fun v ↦ by simp_all [wkRuleGraph, numeral_eq_natCast, wkRule]

instance wkRule.definable : 𝚺ᴬ₀-Function₂ (wkRule : V → V → V) := wkRule.defined.to_definable

instance shiftRule.defined : 𝚺ᴬ₀-Function₂ (shiftRule : V → V → V) via shiftRuleGraph :=
  .mk fun v ↦ by simp_all [shiftRuleGraph, numeral_eq_natCast, shiftRule]

instance shiftRule.definable : 𝚺ᴬ₀-Function₂ (shiftRule : V → V → V) :=
  shiftRule.defined.to_definable

instance cutRule_defined : 𝚺ᴬ₀-Function₄ (cutRule : V → V → V → V → V) via cutRuleGraph :=
  .mk fun v ↦ by simp_all [cutRuleGraph, numeral_eq_natCast, cutRule]

instance cutRule_definable : 𝚺ᴬ₀-Function₄ (cutRule : V → V → V → V → V) :=
  cutRule_defined.to_definable

instance axm_defined : 𝚺ᴬ₀-Function₂ (axm : V → V → V) via axmGraph :=
  .mk fun v ↦ by simp_all [axmGraph, numeral_eq_natCast, axm]

instance (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₄ (orIntro : V → V → V → V → V) :=
  .of_zero orIntro.defined.to_definable

instance (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₂ (axm : V → V → V) :=
  .of_zero axm_defined.to_definable

@[simp] lemma seq_lt_axL (s p : V) : s < axL s p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma arity_lt_axL (s p : V) : p < axL s p :=
  le_iff_lt_succ.mp <| le_trans (by simp) <| le_pair_right _ _

@[simp] lemma seq_lt_verumIntro (s : V) : s < verumIntro s := le_iff_lt_succ.mp <| le_pair_left _ _

@[simp] lemma seq_lt_andIntro (s p q dp dq : V) : s < andIntro s p q dp dq :=
  le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_andIntro (s p q dp dq : V) : p < andIntro s p q dp dq :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _
@[simp] lemma q_lt_andIntro (s p q dp dq : V) : q < andIntro s p q dp dq :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma dp_lt_andIntro (s p q dp dq : V) : dp < andIntro s p q dp dq :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_trans (by simp) <| le_pair_right _ _) <|
    le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma dq_lt_andIntro (s p q dp dq : V) : dq < andIntro s p q dp dq :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_trans (by simp) <| le_pair_right _ _) <|
    le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_orIntro (s p q d : V) : s < orIntro s p q d :=
  le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_orIntro (s p q d : V) : p < orIntro s p q d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _
@[simp] lemma q_lt_orIntro (s p q d : V) : q < orIntro s p q d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d_lt_orIntro (s p q d : V) : d < orIntro s p q d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <|
    le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_allIntro (s p d : V) : s < allIntro s p d :=
  le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_allIntro (s p d : V) : p < allIntro s p d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _
@[simp] lemma s_lt_allIntro (s p d : V) : d < allIntro s p d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (by simp) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_exsIntro (s p t d : V) : s < exsIntro s p t d :=
  le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_exsIntro (s p t d : V) : p < exsIntro s p t d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _
@[simp] lemma t_lt_exsIntro (s p t d : V) : t < exsIntro s p t d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d_lt_exsIntro (s p t d : V) : d < exsIntro s p t d :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <|
    le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_wkRule (s d : V) : s < wkRule s d := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d_lt_wkRule (s d : V) : d < wkRule s d :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_shiftRule (s d : V) : s < shiftRule s d :=
  le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d_lt_shiftRule (s d : V) : d < shiftRule s d :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_cutRule (s p d₁ d₂ : V) : s < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_cutRule (s p d₁ d₂ : V) : p < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _
@[simp] lemma d₁_lt_cutRule (s p d₁ d₂ : V) : d₁ < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d₂_lt_cutRule (s p d₁ d₂ : V) : d₂ < cutRule s p d₁ d₂ :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <|
    le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_axm (s p : V) : s < axm s p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_axm (s p : V) : p < axm s p :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma fstIdx_axL (s p : V) : fstIdx (axL s p) = s := by simp [fstIdx, axL]
@[simp] lemma fstIdx_verumIntro (s : V) : fstIdx (verumIntro s) = s := by simp [fstIdx, verumIntro]
@[simp] lemma fstIdx_andIntro (s p q dp dq : V) : fstIdx (andIntro s p q dp dq) = s := by
  simp [fstIdx, andIntro]
@[simp] lemma fstIdx_orIntro (s p q dpq : V) : fstIdx (orIntro s p q dpq) = s := by
  simp [fstIdx, orIntro]
@[simp] lemma fstIdx_allIntro (s p d : V) : fstIdx (allIntro s p d) = s := by
  simp [fstIdx, allIntro]
@[simp] lemma fstIdx_exsIntro (s p t d : V) : fstIdx (exsIntro s p t d) = s := by
  simp [fstIdx, exsIntro]
@[simp] lemma fstIdx_wkRule (s d : V) : fstIdx (wkRule s d) = s := by simp [fstIdx, wkRule]
@[simp] lemma fstIdx_shiftRule (s d : V) : fstIdx (shiftRule s d) = s := by simp [fstIdx, shiftRule]
@[simp] lemma fstIdx_cutRule (s p d₁ d₂ : V) : fstIdx (cutRule s p d₁ d₂) = s := by
  simp [fstIdx, cutRule]
@[simp] lemma fstIdx_axm (s p : V) : fstIdx (axm s p) = s := by simp [fstIdx, axm]

end code

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
