module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.Bootstrapping.Syntax.Theory
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping.Syntax.Formula.Hierarchy
public import AlphaCentauri.ToFoundation.ElementaryArithmetic.Bootstrapping.Syntax.Term.Typed
public import Foundation.FirstOrder.Incompleteness.Definability

/-!
# The induction schemata recognised on codes in models of $\mathsf{EA}$

The part of `Foundation/FirstOrder/Incompleteness/Definability.lean` on recognising the induction
schema on codes, ported to models of $\mathsf{EA}$: the code `indBodyVal` of the induction
instance of a formula, and the predicate `InductionR S` of codes of the universal closures of
induction instances of formulas satisfying `S`, defined by Foundation's `chInd`. In each model of
$\mathsf{EA}$ the axioms of `𝗣𝗔⁻`, of the induction schemata over `ℬ[<, ℒₒᵣ].Hierarchy Γ s` and
`ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s`, and hence of `𝗜𝗡𝗗 Γ s`, `𝗜𝗡𝗗⁺ Γ s` and `𝗘𝗔`, form a locally
$\Delta_0$ set (`LocallyDelta0Axioms`).
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic

open _root_.FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping Bounding
open _root_.FFL.FirstOrder.Arithmetic (substCode indBodyValGraph chInd)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

section succInd

/-- The code of the induction instance `φ(0) → (∀ x, φ(x) → φ(x + 1)) → ∀ x, φ(x)` of the code
`k` of a formula `φ(x)`. -/
noncomputable def indBodyVal (k : V) : V :=
  imp ℒₒᵣ (subst ℒₒᵣ ↑(substCode (‘0’ : ArithmeticSemiterm ℕ 0)) k)
    (imp ℒₒᵣ (qqAll (imp ℒₒᵣ k (subst ℒₒᵣ ↑(substCode (‘#0 + 1’ : ArithmeticSemiterm ℕ 1)) k)))
      (qqAll k))

lemma le_indBodyVal (k : V) : k ≤ indBodyVal k :=
  (le_qqAll _).trans (lt_or_right _ _ |>.trans (lt_or_right _ _)).le

instance indBodyVal.defined : 𝚺ᴬ₁-Function₁ (indBodyVal : V → V) via indBodyValGraph :=
  .mk fun v ↦ by simp [indBodyValGraph, numeral_eq_natCast, indBodyVal]

lemma indBodyVal_locallyDelta0 : LocallyDelta0Function₁ (indBodyVal : V → V) := by
  have v1 : LocallyDelta0Function fun w : Fin 1 → V ↦ w 0 := LocallyDelta0Function.var 0
  have himp := imp_locallyDelta0 (V := V) (L := ℒₒᵣ)
  have hsubst := subst_locallyDelta0 (V := V) (L := ℒₒᵣ)
  exact himp.comp₂ (hsubst.comp₂ (LocallyDelta0Function.const _) v1)
    (himp.comp₂ (qqAll_locallyDelta0.comp₁ (himp.comp₂ v1
      (hsubst.comp₂ (LocallyDelta0Function.const _) v1))) (qqAll_locallyDelta0.comp₁ v1))

end succInd

section InductionR

/-- `InductionR S p` holds when `p` codes `∀¹* β` for a formula `β` without free variables such
that `β`, with its bound variables replaced by free ones, is the induction instance of a formula
whose code satisfies `S`. -/
def InductionR (S : V → Prop) (p : V) : Prop :=
  ∃ m ≤ p, ∃ b ≤ p,
    p = qqAlls b m ∧ IsUFormula ℒₒᵣ b ∧ shift ℒₒᵣ b = b ∧ bv ℒₒᵣ b = m
    ∧ ∃ K ≤ subst ℒₒᵣ (fvarVec m) b,
        IsSemiformula ℒₒᵣ 1 K ∧ S K ∧ subst ℒₒᵣ (fvarVec m) b = indBodyVal K

instance InductionR.defined {S : V → Prop} {cond : 𝚫ᴬ₁.Semisentence 1}
    [hcond : 𝚫ᴬ₁-Predicate[V] S via cond] :
    𝚫ᴬ₁-Predicate[V] (InductionR S : V → Prop) via chInd cond := .mk <| by
  constructor
  · intro v; simp [chInd, HierarchySymbol.Semiformula.val_sigma, eq_comm]
  · intro v
    simp [chInd, HierarchySymbol.Semiformula.val_sigma, InductionR, lt_succ_iff_le, eq_comm]

lemma InductionR.mono {S S' : V → Prop} (hS : ∀ K, S K → S' K) {p : V} (h : InductionR S p) :
    InductionR S' p := by
  obtain ⟨m, hm, b, hb, hp, hU, hsh, hbv, K, hK, hKs, hKS, hsub⟩ := h
  exact ⟨m, hm, b, hb, hp, hU, hsh, hbv, K, hK, hKs, hS K hKS, hsub⟩

lemma inductionR_locallyDelta0 {S : V → Prop} (hS : LocallyDelta0Pred S) :
    LocallyDelta0Pred (InductionR S) := by
  have v4 : ∀ i : Fin 4, LocallyDelta0Function fun w : Fin 4 → V ↦ w i :=
    LocallyDelta0Function.var
  have hsb : LocallyDelta0Function fun w : Fin 4 → V ↦ subst ℒₒᵣ (fvarVec (w 2)) (w 1) :=
    (subst_locallyDelta0 (L := ℒₒᵣ)).comp₂ (fvarVec_locallyDelta0.comp₁ (v4 2)) (v4 1)
  have hinner : LocallyDelta0 fun w : Fin 4 → V ↦
      IsSemiformula ℒₒᵣ 1 (w 0) ∧ S (w 0) ∧ subst ℒₒᵣ (fvarVec (w 2)) (w 1) = indBodyVal (w 0) :=
    ((isSemiformula_locallyDelta0 (L := ℒₒᵣ)).rel_comp₂ (LocallyDelta0Function.const 1)
      (v4 0)).and <|
      (hS.pred_comp (v4 0)).and (LocallyDelta0.eq hsb (indBodyVal_locallyDelta0.comp₁ (v4 0)))
  have hK := LocallyDelta0.bexs_le_function
    ((subst_locallyDelta0 (L := ℒₒᵣ)).comp₂
      (fvarVec_locallyDelta0.comp₁ (LocallyDelta0Function.var 1)) (LocallyDelta0Function.var 0))
    hinner
  have v3 : ∀ i : Fin 3, LocallyDelta0Function fun w : Fin 3 → V ↦ w i :=
    LocallyDelta0Function.var
  have hbody : LocallyDelta0 fun w : Fin 3 → V ↦
      w 2 = qqAlls (w 0) (w 1) ∧ IsUFormula ℒₒᵣ (w 0) ∧ shift ℒₒᵣ (w 0) = w 0 ∧
        bv ℒₒᵣ (w 0) = w 1 ∧ ∃ K ≤ subst ℒₒᵣ (fvarVec (w 1)) (w 0),
          IsSemiformula ℒₒᵣ 1 K ∧ S K ∧ subst ℒₒᵣ (fvarVec (w 1)) (w 0) = indBodyVal K :=
    (LocallyDelta0.eq (v3 2) (qqAlls_locallyDelta0.comp₂ (v3 0) (v3 1))).and <|
      ((isUFormula_locallyDelta0 (L := ℒₒᵣ)).pred_comp (v3 0)).and <|
        (LocallyDelta0.eq ((shift_locallyDelta0 (L := ℒₒᵣ)).comp₁ (v3 0)) (v3 0)).and <|
          (LocallyDelta0.eq ((bv_locallyDelta0 (L := ℒₒᵣ)).comp₁ (v3 0)) (v3 1)).and <|
            hK.of_iff fun w ↦ by simp
  exact (LocallyDelta0.bexs_le_function (LocallyDelta0Function.var 0)
    (LocallyDelta0.bexs_le_function (LocallyDelta0Function.var 1) hbody)).of_iff
      fun w ↦ by simp [InductionR]

end InductionR

section presentation

/-- A theory whose $\Delta_1$ formula is `chInd cond`, for a formula `cond` defining a locally
$\Delta_0$ predicate `S`, has locally $\Delta_0$ axioms. -/
lemma locallyDelta0Axioms_of_chInd {T : ArithmeticTheory} [T.Δ₁] {cond : 𝚫ᴬ₁.Semisentence 1}
    (hch : T.Δ₁ch = chInd cond) {S : V → Prop} [𝚫ᴬ₁-Predicate[V] S via cond]
    (hS : LocallyDelta0Pred S) : LocallyDelta0Axioms T V where
  properOn := hch ▸ (InductionR.defined (S := S)).proper
  locallyDelta0 := (inductionR_locallyDelta0 hS).of_iff fun v ↦ by
    simp [Theory.Δ₁Class, hch]

instance InductionScheme.locallyDelta0Axioms_hierarchy (Γ : Polarity) (s : ℕ) :
    LocallyDelta0Axioms (InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].Hierarchy Γ s)) V :=
  locallyDelta0Axioms_of_chInd rfl (isHierarchy_locallyDelta0 Γ s)

instance InductionScheme.locallyDelta0Axioms_prenexHierarchy (Γ : Polarity) (s : ℕ) :
    LocallyDelta0Axioms (InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s)) V :=
  locallyDelta0Axioms_of_chInd rfl (isPrenexHierarchy_locallyDelta0 Γ s)

instance : LocallyDelta0Axioms 𝗣𝗔⁻ V := LocallyDelta0Axioms.ofFinite _ _

example (Γ : Polarity) (s : ℕ) : LocallyDelta0Axioms (𝗜𝗡𝗗 Γ s) V := inferInstance

example : LocallyDelta0Axioms 𝗘𝗔 V := inferInstance

end presentation

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
