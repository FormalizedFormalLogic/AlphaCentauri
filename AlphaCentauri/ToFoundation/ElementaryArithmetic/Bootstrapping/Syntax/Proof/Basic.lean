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

lemma fstIdx_locallyDelta0 : LocallyDelta0Function₁ (fstIdx : V → V) where
  graph := LocallyDelta0.of_definable fstIdx_definable
  bounded X := by
    use X
    intro v hv
    exact le_trans (fstIdx_le_self _) (hv 0)

variable {T U : Theory L} [T.Δ₁] [U.Δ₁]

namespace Derivation

noncomputable abbrev conseq (x : V) : V := π₁ x

variable (T) in
/-- The operator generating the codes of derivations from the axioms of `T`. -/
def Phi (C : Set V) (d : V) : Prop :=
  IsFormulaSet L (fstIdx d) ∧
  ( (∃ s p, d = axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
    (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
    (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧
      (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
    (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧
      fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
    (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧
      fstIdx dp = insert (free L p) (setShift L s) ∧ dp ∈ C) ∨
    (∃ s p t dp, d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧
      fstIdx dp = insert (substs1 L t p) s ∧ dp ∈ C) ∨
    (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
    (∃ s d', d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ d' ∈ C) ∨
    (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧
      (fstIdx d₁ = insert p s ∧ d₁ ∈ C) ∧ (fstIdx d₂ = insert (neg L p) s ∧ d₂ ∈ C)) ∨
    (∃ s p, d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) )

variable (T) in
private lemma phi_iff (C d : V) :
    Phi T {x | x ∈ C} d ↔
    IsFormulaSet L (fstIdx d) ∧
    ( (∃ s < d, ∃ p < d, d = axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
      (∃ s < d, d = verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧
          (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        d = allIntro s p dp ∧ ^∀ p ∈ s ∧ fstIdx dp = insert (free L p) (setShift L s) ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧
          fstIdx dp = insert (substs1 L t p) s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d,
        d = cutRule s p d₁ d₂ ∧
          (fstIdx d₁ = insert p s ∧ d₁ ∈ C) ∧ (fstIdx d₂ = insert (neg L p) s ∧ d₂ ∈ C)) ∨
      (∃ s < d, ∃ p < d,
        d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) ) := by
  constructor
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (⟨s, p, rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨s, p, q, dp, dq, rfl, h⟩ |
      ⟨s, p, q, dpq, rfl, h⟩ |
      ⟨s, p, dp, rfl, h⟩ | ⟨s, p, t, dp, rfl, h⟩ | ⟨s, d', rfl, h⟩ | ⟨s, d', rfl, h⟩ |
      ⟨s, p, d₁, d₂, rfl, h⟩ | ⟨s, p, rfl, h⟩)
    · disj 1; exact ⟨s, by simp, p, by simp, rfl, h⟩
    · disj 2; exact ⟨s, by simp, rfl, h⟩
    · disj 3; exact ⟨s, by simp, p, by simp, q, by simp, dp, by simp, dq, by simp, rfl, h⟩
    · disj 4; exact ⟨s, by simp, p, by simp, q, by simp, dpq, by simp, rfl, h⟩
    · disj 5; exact ⟨s, by simp, p, by simp, dp, by simp, rfl, h⟩
    · disj 6; exact ⟨s, by simp, p, by simp, t, by simp, dp, by simp, rfl, h⟩
    · disj 7; exact ⟨s, by simp, d', by simp, rfl, h⟩
    · disj 8; exact ⟨s, by simp, d', by simp, rfl, h⟩
    · disj 9; exact ⟨s, by simp, p, by simp, d₁, by simp, d₂, by simp, rfl, h⟩
    · disj 10; exact ⟨s, by simp, p, by simp, rfl, h⟩
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (⟨s, _, p, _, rfl, h⟩ | ⟨s, _, rfl, h⟩ |
      ⟨s, _, p, _, q, _, dp, _, dq, _, rfl, h⟩ |
      ⟨s, _, p, _, q, _, dpq, _, rfl, h⟩ |
      ⟨s, _, p, _, dp, _, rfl, h⟩ | ⟨s, _, p, _, t, _, dp, _, rfl, h⟩ | ⟨s, _, d', _, rfl, h⟩ |
      ⟨s, _, d', _, rfl, h⟩ | ⟨s, _, p, _, d₁, _, d₂, _, rfl, h⟩ | ⟨s, _, p, _, h⟩)
    · disj 1; exact ⟨s, p, rfl, h⟩
    · disj 2; exact ⟨s, rfl, h⟩
    · disj 3; exact ⟨s, p, q, dp, dq, rfl, h⟩
    · disj 4; exact ⟨s, p, q, dpq, rfl, h⟩
    · disj 5; exact ⟨s, p, dp, rfl, h⟩
    · disj 6; exact ⟨s, p, t, dp, rfl, h⟩
    · disj 7; exact ⟨s, d', rfl, h⟩
    · disj 8; exact ⟨s, d', rfl, h⟩
    · disj 9; exact ⟨s, p, d₁, d₂, rfl, h⟩
    · disj 10; exact ⟨s, p, h⟩

open LocallyDelta0 LocallyDelta0Function in
lemma phi_locallyDelta0 [LocallyDelta0Axioms T V] :
    LocallyDelta0 fun w : Fin 2 → V ↦ Phi T {x | x ∈ w 1} (w 0) := by
  have hv₀ := var (V := V) (0 : Fin 2)
  have hfs : LocallyDelta0 fun w : Fin 2 → V ↦ IsFormulaSet L (fstIdx (w 0)) :=
    isFormulaSet_locallyDelta0.pred_comp (fstIdx_locallyDelta0.comp₁ hv₀)
  have h₁ : LocallyDelta0 fun w : Fin 2 → V ↦
      ∃ s < w 0, ∃ p < w 0, w 0 = axL s p ∧ p ∈ s ∧ neg L p ∈ s := by
    have := bexs_lt_function hv₀ <| bexs_lt_function (var 1) <|
      (eq (var 2) (pairing.comp₂ (var 1) (pairing.comp₂ (const 0) (var 0))).add_one).and <|
      (mem (var 0) (var 1)).and <| mem ((neg_locallyDelta0 (L := L)).comp₁ (var 0)) (var 1)
    exact this
  have h₂ : LocallyDelta0 fun w : Fin 2 → V ↦ ∃ s < w 0, w 0 = verumIntro s ∧ ^⊤ ∈ s := by
    have := bexs_lt_function hv₀ <|
      (eq (var 1) (pairing.comp₂ (var 0) (pairing.comp₂ (const 1) (const 0))).add_one).and <|
      mem (const (^⊤ : V)) (var 0)
    exact this
  have h₃ : LocallyDelta0 fun w : Fin 2 → V ↦
      ∃ s < w 0, ∃ p < w 0, ∃ q < w 0, ∃ dp < w 0, ∃ dq < w 0,
        w 0 = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧
          (fstIdx dp = insert p s ∧ dp ∈ w 1) ∧ (fstIdx dq = insert q s ∧ dq ∈ w 1) := by
    have := bexs_lt_function hv₀ <| bexs_lt_function (var 1) <| bexs_lt_function (var 2) <|
      bexs_lt_function (var 3) <| bexs_lt_function (var 4) <|
      (eq (var 5) (pairing.comp₂ (var 4) <| pairing.comp₂ (const 2) <| pairing.comp₂ (var 3) <|
        pairing.comp₂ (var 2) <| pairing.comp₂ (var 1) (var 0)).add_one).and <|
      (mem (qqAnd_locallyDelta0.comp₂ (var 3) (var 2)) (var 4)).and <|
      ((eq (fstIdx_locallyDelta0.comp₁ (var 1)) (insert.comp₂ (var 3) (var 4))).and
        (mem (var 1) (var 6))).and <|
      (eq (fstIdx_locallyDelta0.comp₁ (var 0)) (insert.comp₂ (var 2) (var 4))).and
        (mem (var 0) (var 6))
    exact this
  have h₄ : LocallyDelta0 fun w : Fin 2 → V ↦
      ∃ s < w 0, ∃ p < w 0, ∃ q < w 0, ∃ dpq < w 0,
        w 0 = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧
          dpq ∈ w 1 := by
    have := bexs_lt_function hv₀ <| bexs_lt_function (var 1) <| bexs_lt_function (var 2) <|
      bexs_lt_function (var 3) <|
      (eq (var 4) (pairing.comp₂ (var 3) <| pairing.comp₂ (const 3) <| pairing.comp₂ (var 2) <|
        pairing.comp₂ (var 1) (var 0)).add_one).and <|
      (mem (qqOr_locallyDelta0.comp₂ (var 2) (var 1)) (var 3)).and <|
      (eq (fstIdx_locallyDelta0.comp₁ (var 0))
        (insert.comp₂ (var 2) (insert.comp₂ (var 1) (var 3)))).and (mem (var 0) (var 5))
    exact this
  have h₅ : LocallyDelta0 fun w : Fin 2 → V ↦
      ∃ s < w 0, ∃ p < w 0, ∃ dp < w 0,
        w 0 = allIntro s p dp ∧ ^∀ p ∈ s ∧ fstIdx dp = insert (free L p) (setShift L s) ∧
          dp ∈ w 1 := by
    have := bexs_lt_function hv₀ <| bexs_lt_function (var 1) <| bexs_lt_function (var 2) <|
      (eq (var 3) (pairing.comp₂ (var 2) <| pairing.comp₂ (const 4) <|
        pairing.comp₂ (var 1) (var 0)).add_one).and <|
      (mem (qqAll_locallyDelta0.comp₁ (var 1)) (var 2)).and <|
      (eq (fstIdx_locallyDelta0.comp₁ (var 0)) <|
        insert.comp₂ ((free_locallyDelta0 (L := L)).comp₁ (var 1))
          ((setShift_locallyDelta0 (L := L)).comp₁ (var 2))).and <|
      mem (var 0) (var 4)
    exact this
  have h₆ : LocallyDelta0 fun w : Fin 2 → V ↦
      ∃ s < w 0, ∃ p < w 0, ∃ t < w 0, ∃ dp < w 0,
        w 0 = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧
          fstIdx dp = insert (substs1 L t p) s ∧ dp ∈ w 1 := by
    have := bexs_lt_function hv₀ <| bexs_lt_function (var 1) <| bexs_lt_function (var 2) <|
      bexs_lt_function (var 3) <|
      (eq (var 4) (pairing.comp₂ (var 3) <| pairing.comp₂ (const 5) <| pairing.comp₂ (var 2) <|
        pairing.comp₂ (var 1) (var 0)).add_one).and <|
      (mem (qqExs_locallyDelta0.comp₁ (var 2)) (var 3)).and <|
      ((isSemiterm_locallyDelta0 (L := L)).rel_comp₂ (const 0) (var 1)).and <|
      (eq (fstIdx_locallyDelta0.comp₁ (var 0)) <|
        insert.comp₂ ((substs1_locallyDelta0 (L := L)).comp₂ (var 1) (var 2)) (var 3)).and <|
      mem (var 0) (var 5)
    exact this
  have h₇ : LocallyDelta0 fun w : Fin 2 → V ↦
      ∃ s < w 0, ∃ d' < w 0, w 0 = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ w 1 := by
    have hsub := of_definable (R := fun w : Fin 2 → V ↦ w 0 ⊆ w 1) (by definability)
    have := bexs_lt_function hv₀ <| bexs_lt_function (var 1) <|
      (eq (var 2) (pairing.comp₂ (var 1) (pairing.comp₂ (const 6) (var 0))).add_one).and <|
      (hsub.comp₂ (fstIdx_locallyDelta0.comp₁ (var 0)) (var 1)).and (mem (var 0) (var 3))
    exact this
  have h₈ : LocallyDelta0 fun w : Fin 2 → V ↦
      ∃ s < w 0, ∃ d' < w 0, w 0 = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ d' ∈ w 1 := by
    have := bexs_lt_function hv₀ <| bexs_lt_function (var 1) <|
      (eq (var 2) (pairing.comp₂ (var 1) (pairing.comp₂ (const 7) (var 0))).add_one).and <|
      (eq (var 1) ((setShift_locallyDelta0 (L := L)).comp₁ <|
        fstIdx_locallyDelta0.comp₁ (var 0))).and <|
      mem (var 0) (var 3)
    exact this
  have h₉ : LocallyDelta0 fun w : Fin 2 → V ↦
      ∃ s < w 0, ∃ p < w 0, ∃ d₁ < w 0, ∃ d₂ < w 0,
        w 0 = cutRule s p d₁ d₂ ∧ (fstIdx d₁ = insert p s ∧ d₁ ∈ w 1) ∧
          (fstIdx d₂ = insert (neg L p) s ∧ d₂ ∈ w 1) := by
    have := bexs_lt_function hv₀ <| bexs_lt_function (var 1) <| bexs_lt_function (var 2) <|
      bexs_lt_function (var 3) <|
      (eq (var 4) (pairing.comp₂ (var 3) <| pairing.comp₂ (const 8) <| pairing.comp₂ (var 2) <|
        pairing.comp₂ (var 1) (var 0)).add_one).and <|
      ((eq (fstIdx_locallyDelta0.comp₁ (var 1)) (insert.comp₂ (var 2) (var 3))).and
        (mem (var 1) (var 5))).and <|
      (eq (fstIdx_locallyDelta0.comp₁ (var 0)) <|
        insert.comp₂ ((neg_locallyDelta0 (L := L)).comp₁ (var 2)) (var 3)).and <|
      mem (var 0) (var 5)
    exact this
  have h₁₀ : LocallyDelta0 fun w : Fin 2 → V ↦
      ∃ s < w 0, ∃ p < w 0, w 0 = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class := by
    have := bexs_lt_function hv₀ <| bexs_lt_function (var 1) <|
      (eq (var 2) (pairing.comp₂ (var 1) (pairing.comp₂ (const 9) (var 0))).add_one).and <|
      (mem (var 0) (var 1)).and <|
      (LocallyDelta0Axioms.locallyDelta0 (T := T) (V := V)).pred_comp (var 0)
    exact this
  exact (hfs.and <| h₁.or <| h₂.or <| h₃.or <| h₄.or <| h₅.or <| h₆.or <| h₇.or <| h₈.or <|
    h₉.or h₁₀).of_iff fun w ↦ phi_iff T (w 1) (w 0)

variable [LocallyDelta0Axioms T V]

variable (T) in
open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Derivation (blueprint) in
/-- The construction of the codes of derivations from the axioms of `T`. -/
def construction : Fixpoint.Construction V (blueprint T) where
  Φ := fun _ ↦ Phi T
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, (LocallyDelta0Axioms.properOn (T := T) (V := V)).iff',
        Bounding.HierarchySymbol.Semiformula.val_sigma]
    · intro v
      simp [phi_iff, blueprint, Theory.Δ₁Class, Bounding.HierarchySymbol.Semiformula.val_sigma]
  monotone := by
    rintro C C' hC _ d ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (h | h | ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC⟩, ⟨hq, hqC⟩⟩ |
      ⟨s, p, q, dpq, rfl, hpq, h, hdC⟩ |
      ⟨s, p, dp, rfl, hp, h, hdC⟩ | ⟨s, p, t, dp, rfl, hp, ht, h, hdC⟩ |
      ⟨s, d', rfl, ss, hdC⟩ | ⟨s, d', rfl, ss, hdC⟩ | ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C⟩, ⟨h₂, hd₂C⟩⟩ |
      ⟨s, p, h⟩)
    · disj 1; exact h
    · disj 2; exact h
    · disj 3; exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hC hpC⟩, ⟨hq, hC hqC⟩⟩
    · disj 4; exact ⟨s, p, q, dpq, rfl, hpq, h, hC hdC⟩
    · disj 5; exact ⟨s, p, dp, rfl, hp, h, hC hdC⟩
    · disj 6; exact ⟨s, p, t, dp, rfl, hp, ht, h, hC hdC⟩
    · disj 7; exact ⟨s, d', rfl, ss, hC hdC⟩
    · disj 8; exact ⟨s, d', rfl, ss, hC hdC⟩
    · disj 9; exact ⟨s, p, d₁, d₂, rfl, ⟨h₁, hC hd₁C⟩, ⟨h₂, hC hd₂C⟩⟩
    · disj 10; exact ⟨s, p, h⟩
  Φ_locallyDelta0 := phi_locallyDelta0

instance : (construction T).StrongFinite V where
  strong_finite := by
    rintro C _ d ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (h | h | ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC⟩, ⟨hq, hqC⟩⟩ |
      ⟨s, p, q, dpq, rfl, hpq, h, hdC⟩ |
      ⟨s, p, dp, rfl, hp, h, hdC⟩ | ⟨s, p, t, dp, rfl, hp, ht, h, hdC⟩ |
      ⟨s, d', rfl, ss, hdC⟩ | ⟨s, d', rfl, ss, hdC⟩ | ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C⟩, ⟨h₂, hd₂C⟩⟩ |
      ⟨s, p, h⟩)
    · disj 1; exact h
    · disj 2; exact h
    · disj 3; exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC, by simp⟩, ⟨hq, hqC, by simp⟩⟩
    · disj 4; exact ⟨s, p, q, dpq, rfl, hpq, h, hdC, by simp⟩
    · disj 5; exact ⟨s, p, dp, rfl, hp, h, hdC, by simp⟩
    · disj 6; exact ⟨s, p, t, dp, rfl, hp, ht, h, hdC, by simp⟩
    · disj 7; exact ⟨s, d', rfl, ss, hdC, by simp⟩
    · disj 8; exact ⟨s, d', rfl, ss, hdC, by simp⟩
    · disj 9; exact ⟨s, p, d₁, d₂, rfl, ⟨h₁, hd₁C, by simp⟩, ⟨h₂, hd₂C, by simp⟩⟩
    · disj 10; exact ⟨s, p, h⟩

end Derivation

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
