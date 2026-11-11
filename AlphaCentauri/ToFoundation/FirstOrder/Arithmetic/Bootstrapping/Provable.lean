module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D3
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.FixedPoint
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Hierarchy
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Equality
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.ProvableIff
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.QuantifierBlock
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.PeanoMinus
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.EquationalTheory

/-!
# Gaps in Foundation's `DerivabilityCondition`

Generic facts about `Bootstrapping.Provable`: instantiating an internally-provable instance by
numerals of a universal formula at one more numeral, modus ponens for arbitrary (not necessarily
quoted) codes, induction on a numeral of a formula whose base case and induction step are
provable, the internal provability of the numeral instances of a theorem of `𝗜𝚺₁` and of a
true $\Sigma_1$ formula, and the internal equivalence of `(∀¹ A) ⋎ (∀¹ B)` with
`∀¹ (∀u < #0 + 1, A u ⋎ ∀x < #0 + 1, B x)` for formulas without free variables. More generally,
the disjunction of two internal prenex $\Gamma_n$ sentences is internally equivalent to an internal
prenex $\Gamma_n$ sentence; this is stated as an axiom.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

open FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section modus_ponens

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

/-- Modus ponens for internal provability of arbitrary codes, not necessarily quotes of standard
propositions. -/
lemma provable_of_provable_imp_of_provable {a b : V}
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
lemma provable_substNumerals_of_provable_substNumerals_all {m : ℕ}
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
lemma provable_substNumerals_of_provable_allClosure {k : ℕ} (φ : ArithmeticSemisentence k)
    (h : Provable T (⌜∀¹* φ⌝ : V)) (v : Fin k → V) : Provable T (substNumerals (⌜φ⌝ : V) v) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [← Matrix.cons_head_tail v]
    exact provable_substNumerals_of_provable_substNumerals_all φ (ih (∀¹ φ) h _) _

variable [𝗜𝚺₁ ⪯ T]

/-- A theorem of `𝗜𝚺₁`, given by its truth in every model, is internally provable at every
vector of terms. -/
lemma tprovable_subst_of_models {k : ℕ} {φ : ArithmeticSemisentence k}
    (h : ∀ (W : Type) [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin k → W), W ⊧/e φ)
    (w : SemitermVec V ℒₒᵣ k 0) :
    T.internalize V ⊢ (⌜φ⌝ : Semiformula V ℒₒᵣ k).subst w :=
  tprovable_subst_of_allClosure T w <| internal_provable_of_outer_provable <|
    Entailment.WeakerThan.pbl <| complete 𝗜𝚺₁ _ fun W _ _ ↦ by simpa [models_iff] using h W

/-- A theorem of `𝗜𝚺₁`, given by its truth in every model, is internally provable at numerals. -/
lemma tprovable_subst_numeral_of_models {k : ℕ} {φ : ArithmeticSemisentence k}
    (h : ∀ (W : Type) [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin k → W), W ⊧/e φ)
    (w : Fin k → V) :
    T.internalize V ⊢ (⌜φ⌝ : Semiformula V ℒₒᵣ k).subst (fun i ↦ 𝕹 (w i)) :=
  tprovable_subst_of_allClosure T _ <| internal_provable_of_outer_provable <|
    Entailment.WeakerThan.pbl <| complete 𝗜𝚺₁ _ fun W _ _ ↦ by simpa [models_iff] using h W

/-- A $\Sigma_1$ formula true at `w` is internally provable at the numerals of `w`. -/
lemma tprovable_subst_numeral_of_sigma1 {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ) {w : Fin k → V} (h : V ⊧/w φ) :
    T.internalize V ⊢ (⌜φ⌝ : Semiformula V ℒₒᵣ k).subst (fun i ↦ 𝕹 (w i)) :=
  bold_sigma_one_complete T hφ h

end specialize

section induction

open Bootstrapping.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

lemma substNumerals_eq_subst {k : ℕ} (φ : ArithmeticSemisentence k) (v : Fin k → V) :
    substNumerals (⌜φ⌝ : V) v =
      ((⌜φ⌝ : Semiformula V ℒₒᵣ k).subst fun i ↦ (𝕹 (v i) : Term V ℒₒᵣ)).val := by
  simp [substNumerals, Sentence.quote_eq]
  rfl

lemma typed_quote_shift {n : ℕ} (σ : ArithmeticSemisentence n) :
    (⌜σ⌝ : Semiformula V ℒₒᵣ n).shift = ⌜σ⌝ := by
  ext;
  change shift ℒₒᵣ (⌜σ⌝ : V) = ⌜σ⌝;
  rw [Sentence.quote_def, ← Semiformula.quote_shift];
  simp [Rewriting.shift, Rewriting.emb, ← TransitiveRewriting.comp_app]

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

open FFL.Entailment Bootstrapping.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁]

/-- `∀¹ (∀u < #0 + 1, A u ⋎ ∀x < #0 + 1, B x)`. -/
noncomputable abbrev allBallOrBall (A B : Semiformula V ℒₒᵣ 1) : Formula V ℒₒᵣ :=
  ∀¹ ((A.subst ![Semiterm.bvar 0]).ball (Semiterm.bvar 0 + 𝕹 1) ⋎
    (B.subst ![Semiterm.bvar 0]).ball (Semiterm.bvar 0 + 𝕹 1))

lemma shift_allBallOrBall {A B : Semiformula V ℒₒᵣ 1} (hA : A.shift = A) (hB : B.shift = B) :
    (allBallOrBall A B).shift = allBallOrBall A B := by
  simp [Semiformula.shift_substs, hA, hB]

lemma tprovable_ball_imp (φ : Semiformula V ℒₒᵣ 1) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢ φ.ball t 🡒 Semiterm.notLessThan u t ⋎ φ.subst ![u] := by
  have := TProof.all_imp_subst (T := T)
    (Semiterm.notLessThan (Semiterm.bvar 0) t.bShift ⋎ φ) u;
  simpa [Semiformula.ball] using this

lemma tprovable_allBallOrBall_imp_subst (A B : Semiformula V ℒₒᵣ 1) (w : Term V ℒₒᵣ) :
    T.internalize V ⊢ allBallOrBall A B 🡒 A.ball (w + 𝕹 1) ⋎ B.ball (w + 𝕹 1) := by
  have := TProof.all_imp_subst (T := T)
    ((A.subst ![Semiterm.bvar 0]).ball (Semiterm.bvar 0 + 𝕹 1) ⋎
      (B.subst ![Semiterm.bvar 0]).ball (Semiterm.bvar 0 + 𝕹 1)) w;
  simpa [Semiformula.substs_substs, SemitermVec.q] using this

lemma tprovable_all_or_all_imp_allBallOrBall (A B : Semiformula V ℒₒᵣ 1) :
    T.internalize V ⊢ (∀¹ A) ⋎ (∀¹ B) 🡒 allBallOrBall A B := by
  have e (φ : Semiformula V ℒₒᵣ 1) :
      (((Semiterm.bvar 0 : Semiterm V ℒₒᵣ 1) <' Semiterm.fvar 0 + 𝕹 1) 🡒 φ) =
        (Semiterm.notLessThan (Semiterm.bvar 0 : Semiterm V ℒₒᵣ 1) (Semiterm.fvar 0 + 𝕹 1) ⋎
          φ) := by
    simp [Semiformula.imp_def];
  have hA := tprovable_all_imp_all (T := T)
    ((Semiterm.bvar 0 : Semiterm V ℒₒᵣ 1) <' Semiterm.fvar 0 + 𝕹 1) A.shift;
  have hB := tprovable_all_imp_all (T := T)
    ((Semiterm.bvar 0 : Semiterm V ℒₒᵣ 1) <' Semiterm.fvar 0 + 𝕹 1) B.shift;
  rw [e] at hA hB;
  apply TProof.generalize_imp;
  suffices T.internalize V ⊢ (∀¹ A.shift) ⋎ (∀¹ B.shift) 🡒
      (∀¹ (Semiterm.notLessThan (Semiterm.bvar 0) (Semiterm.fvar 0 + 𝕹 1) ⋎ A.shift)) ⋎
        (∀¹ (Semiterm.notLessThan (Semiterm.bvar 0) (Semiterm.fvar 0 + 𝕹 1) ⋎ B.shift)) by
    simpa [Semiformula.free, Semiformula.ball, Semiformula.shift_substs,
      Semiformula.substs_substs, SemitermVec.q] using this;
  cl_prover [hA, hB]

variable [𝗜𝚺₁ ⪯ T]

lemma tprovable_lt_add_add_one (t u : Term V ℒₒᵣ) : T.internalize V ⊢ t <' t + u + 𝕹 1 := by
  have h : T ⊢ (“∀ x y, x < x + y + 1” : ArithmeticSentence) :=
    complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦ by
      have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory hM;
      simpa [models_iff] using fun x y : M ↦ lt_succ_iff_le.mpr (le_self_add (a := x) (b := y));
  have h' : T.internalize V ⊢ ∀¹ ∀¹ ((Semiterm.bvar 1 : Semiterm V ℒₒᵣ 2) <'
      Semiterm.bvar 1 + Semiterm.bvar 0 + 𝕹 1) := by
    simpa using internal_provable_of_outer_provable (V := V) h;
  simpa using TProof.specialize₂! h' u t

lemma tprovable_lt_add_add_one' (t u : Term V ℒₒᵣ) : T.internalize V ⊢ u <' t + u + 𝕹 1 := by
  have h : T ⊢ (“∀ x y, y < x + y + 1” : ArithmeticSentence) :=
    complete.{0} T _ fun (M : Type) _ (hM : M↓[ℒₒᵣ] ⊧* T) ↦ by
      have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory hM;
      simpa [models_iff] using fun x y : M ↦ lt_add_self_add_one y x;
  have h' : T.internalize V ⊢ ∀¹ ∀¹ ((Semiterm.bvar 0 : Semiterm V ℒₒᵣ 2) <'
      Semiterm.bvar 1 + Semiterm.bvar 0 + 𝕹 1) := by
    simpa using internal_provable_of_outer_provable (V := V) h;
  simpa using TProof.specialize₂! h' u t

lemma tprovable_allBallOrBall_imp {A B : Semiformula V ℒₒᵣ 1} (hA : A.shift = A)
    (hB : B.shift = B) : T.internalize V ⊢ allBallOrBall A B 🡒 (∀¹ A) ⋎ (∀¹ B) := by
  have hHs := shift_allBallOrBall hA hB;
  have key : T.internalize V ⊢ ∃¹ (∼A) 🡒 allBallOrBall A B 🡒 ∀¹ B := by
    apply TProof.exs_imp_of_free;
    rw [Semiformula.shift_imp, hHs, Semiformula.shift_all, hB];
    suffices T.internalize V ⊢ (∼A).free ⋏ allBallOrBall A B 🡒 ∀¹ B by cl_prover [this];
    apply TProof.generalize_imp;
    suffices T.internalize V ⊢ ∼(A.subst ![Semiterm.fvar 1]) ⋏ allBallOrBall A B 🡒
        B.subst ![Semiterm.fvar 0] by
      simpa [Semiformula.free, Semiformula.shift_substs, hA, hB, hHs] using this;
    have h₁ := tprovable_allBallOrBall_imp_subst (T := T) A B
      (Semiterm.fvar 1 + Semiterm.fvar 0);
    have h₂ := tprovable_ball_imp (T := T) A
      (Semiterm.fvar 1 + Semiterm.fvar 0 + 𝕹 1) (Semiterm.fvar 1);
    have h₃ := tprovable_ball_imp (T := T) B
      (Semiterm.fvar 1 + Semiterm.fvar 0 + 𝕹 1) (Semiterm.fvar 0);
    have h₄ : T.internalize V ⊢ ∼(Semiterm.notLessThan (Semiterm.fvar 1)
        (Semiterm.fvar 1 + Semiterm.fvar 0 + 𝕹 1)) := by
      simpa using tprovable_lt_add_add_one (T := T) (Semiterm.fvar 1) (Semiterm.fvar 0);
    have h₅ : T.internalize V ⊢ ∼(Semiterm.notLessThan (Semiterm.fvar 0)
        (Semiterm.fvar 1 + Semiterm.fvar 0 + 𝕹 1)) := by
      simpa using tprovable_lt_add_add_one' (T := T) (Semiterm.fvar 1) (Semiterm.fvar 0);
    cl_prover [h₁, h₂, h₃, h₄, h₅];
  have key' : T.internalize V ⊢ ∼(∀¹ A) 🡒 allBallOrBall A B 🡒 ∀¹ B := by simpa using key;
  cl_prover [key']

/-- The disjunction of two internal prenex $\Gamma_n$ sentences is internally equivalent to an
internal prenex $\Gamma_n$ sentence. -/
axiom exists_isPrenexHierarchy_tprovable_or_iff {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {Γ : Polarity} {n : ℕ}
    {φ ψ : Formula V ℒₒᵣ} (hφs : φ.shift = φ) (hψs : ψ.shift = ψ)
    (hφ : IsPrenexHierarchy Γ n φ.val) (hψ : IsPrenexHierarchy Γ n ψ.val) :
    ∃ χ : Formula V ℒₒᵣ, χ.shift = χ ∧ IsPrenexHierarchy Γ n χ.val ∧
      T.internalize V ⊢ φ ⋎ ψ 🡘 χ

end Bootstrapping
end FFL.FirstOrder.Arithmetic
