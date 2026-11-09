module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.FixedPoint
public import AlphaCentauri.ToFoundation.Syntax
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.PeanoMinus
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.EquationalTheory

@[expose] public section
/-!
# Internal provability: universal instantiation, modus ponens and induction

Generic facts about `Bootstrapping.Provable`: instantiating an internally-provable instance by
numerals of a universal formula at one more numeral, modus ponens for arbitrary (not necessarily
quoted) codes, and induction on a numeral of a formula whose base case and induction step are
provable.
-/

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section modus_ponens

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

/-- Modus ponens for internal provability of arbitrary codes, not necessarily quotes of standard
propositions. -/
theorem provable_of_provable_imp_of_provable {a b : V}
    (hab : Provable T (imp L a b)) (ha : Provable T a) : Provable T b := by
  have hab' : IsFormula L (imp L a b) := by simpa using hab.toDerivable.isFormulaSet
  have ha' : IsFormula L a := by simpa using ha.toDerivable.isFormulaSet
  have hb' : IsFormula L b := (IsSemiformula.imp.mp hab').2
  set φ : Formula V L := ⟨a, ha'⟩
  set ψ : Formula V L := ⟨b, hb'⟩
  have hφψ : T.internalize V ⊢ φ 🡒 ψ := tprovable_iff_provable.mpr (by simpa [φ, ψ] using hab)
  have hφ : T.internalize V ⊢ φ := tprovable_iff_provable.mpr (by simpa [φ] using ha)
  simpa [φ, ψ] using tprovable_iff_provable.mp (hφψ ⨀ hφ)

end modus_ponens

section specialize

open Bootstrapping.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁]

@[simp] lemma substNumerals_quote_of_isEmpty (σ : ArithmeticSentence) (v : Fin 0 → V) :
    substNumerals (⌜σ⌝ : V) v = ⌜σ⌝ := by
  simpa [Matrix.empty_eq] using substNumerals_app_quote (V := V) σ ![]

/-- Instantiating an internally-provable instance by numerals of `∀¹ φ` at one more numeral. -/
theorem provable_substNumerals_of_provable_substNumerals_all {m : ℕ}
    (φ : ArithmeticSemisentence (m + 1)) {v : Fin m → V}
    (h : Provable T (substNumerals (⌜∀¹ φ⌝ : V) v)) (x : V) :
    Provable T (substNumerals (⌜φ⌝ : V) (x :> v)) := by
  let w : V := matrixToVec fun i ↦ numeral (v i)
  have hw : IsSemitermVec ℒₒᵣ (m : V) 0 w :=
    SemitermVec.isSemitermVec (V := V) (L := ℒₒᵣ) (k := m) (n := 0) fun i ↦ 𝕹 (v i)
  have hφ : IsSemiformula ℒₒᵣ (m + 1 : V) (⌜φ⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) φ
  let ψ : Semiformula V ℒₒᵣ 1 :=
    ⟨subst ℒₒᵣ (qVec ℒₒᵣ w) ⌜φ⌝, by simpa using hφ.subst hw.qVec⟩
  have h₁ : T.internalize V ⊢ ∀¹ ψ :=
    tprovable_iff_provable.mpr (by simpa [ψ, w, substNumerals] using h)
  have h₂ := tprovable_iff_provable.mp (TProof.specialize! h₁ (𝕹 x))
  have e := substs1_subst_qVec hw hφ (t := numeral x) (by simp)
  simp only [substs1] at e
  simp only [Semiformula.val_substs, ψ, SemitermVec.val_succ] at h₂
  simpa [e, w, substNumerals, Matrix.vecHead, Matrix.vecTail, Function.comp_def] using h₂

/-- Instantiating an internally-provable universal closure at numerals. -/
theorem provable_substNumerals_of_provable_allClosure {k : ℕ} (φ : ArithmeticSemisentence k)
    (h : Provable T (⌜∀¹* φ⌝ : V)) (v : Fin k → V) : Provable T (substNumerals (⌜φ⌝ : V) v) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [← Matrix.cons_head_tail v]
    exact provable_substNumerals_of_provable_substNumerals_all φ (ih (∀¹ φ) h _) _

end specialize

section induction

open Bootstrapping.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

lemma substNumerals_eq_subst {k : ℕ} (φ : ArithmeticSemisentence k) (v : Fin k → V) :
    substNumerals (⌜φ⌝ : V) v =
      ((⌜φ⌝ : Semiformula V ℒₒᵣ k).subst fun i ↦ (𝕹 (v i) : Term V ℒₒᵣ)).val := by
  simp [substNumerals, Sentence.quote_eq]
  rfl

lemma typed_quote_rew_subst {k j : ℕ} (φ : ArithmeticSemisentence k)
    (w : Fin k → ArithmeticSemiterm Empty j) :
    (⌜Rew.subst w ▹ φ⌝ : Semiformula V ℒₒᵣ j) =
      (⌜φ⌝ : Semiformula V ℒₒᵣ k).subst fun i ↦ ⌜(Rew.emb (w i) : SyntacticSemiterm ℒₒᵣ j)⌝ := by
  simp [Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb]

/-- If `T` proves the base case `∀ p⃗, φ(0, p⃗)` and the induction step
`∀ x p⃗, φ(x, p⃗) 🡒 φ(x + 1, p⃗)`, then every instance of `φ` by numerals is internally provable. -/
theorem provable_substNumerals_of_provable_zero_of_provable_succ {m : ℕ}
    (φ : ArithmeticSemisentence (m + 1)) (h₀ : T ⊢ ∀¹* (Rew.subst (‘0’ :> fun i ↦ #i) ▹ φ))
    (hs : T ⊢ ∀¹* (φ 🡒 Rew.subst (‘#0 + 1’ :> fun i ↦ #i.succ) ▹ φ)) (x : V) (p : Fin m → V) :
    Provable T (substNumerals (⌜φ⌝ : V) (x :> p)) := by
  let Φ : Semiformula V ℒₒᵣ 1 :=
    (⌜φ⌝ : Semiformula V ℒₒᵣ (m + 1)).subst (Semiterm.bvar 0 :> fun i ↦ 𝕹 (p i))
  have hΦ (t : Term V ℒₒᵣ) :
      Φ.subst ![t] = (⌜φ⌝ : Semiformula V ℒₒᵣ (m + 1)).subst (t :> fun i ↦ 𝕹 (p i)) := by
    simp only [Φ, Semiformula.substs_substs]
    congr 1
    funext i
    cases i using Fin.cases <;> simp
  have hnum (y : V) : substNumeral Φ.val y = (Φ.subst ![(𝕹 y : Term V ℒₒᵣ)]).val := by
    simp [substNumeral]
  have key (y : V) : substNumerals (⌜φ⌝ : V) (y :> p) = substNumeral Φ.val y := by
    rw [substNumerals_eq_subst, hnum, hΦ]
    congr 2
    funext i
    cases i using Fin.cases <;> simp
  rw [key]
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    have h :=
      provable_substNumerals_of_provable_allClosure _ (internalize_provability (V := V) h₀) p
    rw [substNumerals_eq_subst, typed_quote_rew_subst, Semiformula.substs_substs] at h
    rw [hnum, hΦ]
    convert h using 3
    funext i
    cases i using Fin.cases <;> simp
  case succ y ih =>
    have h := provable_substNumerals_of_provable_allClosure _ (internalize_provability (V := V) hs)
      (y :> p)
    rw [substNumerals_eq_subst] at h
    have h₁ : T.internalize V ⊢ Φ.subst ![(𝕹 y : Term V ℒₒᵣ)] 🡒 Φ.subst ![𝕹 y + 𝕹 1] := by
      apply tprovable_iff_provable.mpr
      convert h using 2
      rw [hΦ, hΦ, LCWQIsoGödelQuote.imply, Semiformula.substs_imp, typed_quote_rew_subst,
        Semiformula.substs_substs]
      congr 2 <;> funext i <;> cases i using Fin.cases <;> simp
    have h₂ : T.internalize V ⊢ Φ.subst ![(𝕹 y : Term V ℒₒᵣ)] :=
      tprovable_iff_provable.mpr (by simpa [hnum] using ih)
    have h₃ := Arithmetic.replace T Φ (𝕹 y + 𝕹 1) (𝕹 (y + 1)) ⨀ Arithmetic.numeral_add T y 1 ⨀
      (h₁ ⨀ h₂)
    simpa [hnum] using tprovable_iff_provable.mp h₃

end induction

end FFL.FirstOrder.Arithmetic.Bootstrapping
