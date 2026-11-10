module

public import AlphaCentauri.InterpretabilityLogic.Arithmetic.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.ProvabilityFormula
public import Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
# Arithmetical soundness of $\mathbf{ILM}$ for $\Pi_1$-conservativity

For a $\Delta_1$-axiomatized arithmetical theory $T$, `T.pi1Conservativity` reads
$\varphi \rhd \psi$ as "every prenex $\Pi_1$ sentence provable in $T + \psi$ is provable in
$T + \varphi$". Together with the standard provability predicate of $T$, it satisfies the
arithmetical forms of $\mathbf{J1}$–$\mathbf{J5}$ and $\mathbf{M}$ over $\mathsf{I}\Sigma_1$ once
$T$ contains $\mathsf{I}\Sigma_1$, so every theorem of $\mathbf{ILM}$ is provable in $T$ under
every realization.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping Bootstrapping.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁]

namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable (T) in
/-- For every internal prenex $\Pi_1$ sentence `x`, if `T` proves `b 🡒 x` then `T` proves
`a 🡒 x`. -/
def Pi1Conservative (a b : V) : Prop :=
  ∀ x, IsSemiformula ℒₒᵣ 0 x → shift ℒₒᵣ x = x → IsPrenexHierarchy 𝚷 1 x →
    Provable T (imp ℒₒᵣ b x) → Provable T (imp ℒₒᵣ a x)

variable {σ τ χ : ArithmeticSentence}

lemma pi1Conservative_quote_iff :
    Pi1Conservative T (⌜σ⌝ : V) ⌜τ⌝ ↔
      ∀ π : Formula V ℒₒᵣ, π.shift = π → IsPrenexHierarchy 𝚷 1 π.val →
      T.internalize V ⊢ ⌜τ⌝ 🡒 π → T.internalize V ⊢ ⌜σ⌝ 🡒 π := by
  constructor;
  · intro h π hs hπ hτ;
    apply tprovable_iff_provable.mpr;
    simpa [Sentence.quote_eq] using h π.val π.isSemiformula (by simpa using congrArg (·.val) hs) hπ
      (by simpa [Sentence.quote_eq] using tprovable_iff_provable.mp hτ);
  · intro h x hx hs hπ hτ;
    have := h ⟨x, hx⟩ (by ext; simpa using hs) hπ
      (tprovable_iff_provable.mpr <| by simpa [Sentence.quote_eq] using hτ);
    simpa [Sentence.quote_eq] using tprovable_iff_provable.mp this

lemma pi1Conservative_of_provable (h : Provable T (⌜σ 🡒 τ⌝ : V)) :
    Pi1Conservative T (⌜σ⌝ : V) ⌜τ⌝ := by
  apply pi1Conservative_quote_iff.mpr;
  intro π _ _ hτ;
  have hστ : T.internalize V ⊢ ⌜σ⌝ 🡒 ⌜τ⌝ := by
    simpa using (tprovable_tquote_iff_provable_quote_sentence (σ := σ 🡒 τ)).mpr h;
  exact C_trans hστ hτ

lemma Pi1Conservative.trans {a b c : V} (hab : Pi1Conservative T a b)
    (hbc : Pi1Conservative T b c) : Pi1Conservative T a c := by
  intro x hx hs hπ h;
  exact hab x hx hs hπ <| hbc x hx hs hπ h

lemma Pi1Conservative.or (hσ : Pi1Conservative T (⌜σ⌝ : V) ⌜χ⌝)
    (hτ : Pi1Conservative T (⌜τ⌝ : V) ⌜χ⌝) : Pi1Conservative T (⌜σ ⋎ τ⌝ : V) ⌜χ⌝ := by
  rw [pi1Conservative_quote_iff] at hσ hτ ⊢;
  intro π hs hπ h;
  have h₁ := hσ π hs hπ h;
  have h₂ := hτ π hs hπ h;
  have h₃ : T.internalize V ⊢ ⌜σ⌝ ⋎ ⌜τ⌝ 🡒 π := by cl_prover [h₁, h₂];
  simpa using h₃

lemma Pi1Conservative.consistent (h : Pi1Conservative T (⌜σ⌝ : V) ⌜τ⌝)
    (hτ : Provable T (⌜∼τ⌝ : V)) : Provable T (⌜∼σ⌝ : V) := by
  rw [pi1Conservative_quote_iff] at h;
  have h₁ : T.internalize V ⊢ ∼⌜τ⌝ := by
    simpa using (tprovable_tquote_iff_provable_quote_sentence (σ := ∼τ)).mpr hτ;
  have hbot : T.internalize V ⊢ (∀¹ (⊥ : Semiformula V ℒₒᵣ 1)) 🡒 ⊥ := by
    simpa using TProof.all_imp_subst (T := T) (⊥ : Semiformula V ℒₒᵣ 1) (Semiterm.fvar 0);
  have h₂ : T.internalize V ⊢ ⌜τ⌝ 🡒 ⊥ := by cl_prover [h₁];
  have h₃ := h (∀¹ ⊥) (by simp) (by simp [IsPrenexHierarchy]) (by
    apply TProof.generalize_imp;
    simpa [typed_quote_shift, Semiformula.free] using h₂);
  have h₄ : T.internalize V ⊢ ∼⌜σ⌝ := by cl_prover [h₃, hbot];
  simpa using (tprovable_tquote_iff_provable_quote_sentence (σ := ∼σ)).mp (by simpa using h₄)

lemma pi1Conservative_dia [𝗜𝚺₁ ⪯ T] :
    Pi1Conservative T (⌜∼provabilityPred T (∼σ)⌝ : V) ⌜σ⌝ := by
  apply pi1Conservative_quote_iff.mpr;
  intro π hs hπ h;
  have h₁ : T.internalize V ⊢ ∼π 🡒 ∼⌜σ⌝ := by cl_prover [h];
  have h₂ : T.internalize V ⊢ provabilityFormula T (∼π 🡒 ∼⌜σ⌝).val :=
    tprovable_provabilityFormula <| tprovable_iff_provable.mp h₁;
  have h₃ := tprovable_provabilityFormula_imp (T := T) (∼π) (∼⌜σ⌝);
  have h₄ := tprovable_imp_provabilityFormula_of_sigma1 (T := T) (∼π)
    (by simpa using hπ.neg π.isSemiformula.isUFormula) (by simp [hs]);
  have h₅ : T.internalize V ⊢ ∼provabilityFormula T (∼⌜σ⌝ : Formula V ℒₒᵣ).val 🡒 π := by
    cl_prover [h₂, h₃, h₄];
  simpa [Sentence.quote_eq] using h₅

lemma Pi1Conservative.and_provabilityPred [𝗜𝚺₁ ⪯ T] (h : Pi1Conservative T (⌜σ⌝ : V) ⌜τ⌝) :
    Pi1Conservative T (⌜σ ⋏ provabilityPred T χ⌝ : V) ⌜τ ⋏ provabilityPred T χ⌝ := by
  rw [pi1Conservative_quote_iff] at h ⊢;
  intro π hs hπ hτ;
  obtain ⟨θ, hθ, hθb⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp hπ;
  have hθs : IsSemiformula ℒₒᵣ ((1 : ℕ) : V) θ := by simpa [hθ] using π.isSemiformula;
  let B : Semiformula V ℒₒᵣ 1 := ⟨θ, hθs⟩;
  have hπB : π = ∀¹ B := by ext; simp [B, hθ];
  have hB : B.shift = B := by
    rw [hπB, Semiformula.shift_all] at hs;
    ext; simpa using congrArg (·.val) hs;
  obtain ⟨δ, hδ⟩ := ISigma1.exists_matrix_provable_of_sentence (σ := provabilityPred T χ) (by simp);
  let A : Semiformula V ℒₒᵣ 1 := ∼⌜δ.val⌝;
  have hA : A.shift = A := by simp [A, typed_quote_shift];
  have hAb : IsBounded A.val := by
    simpa [A, Sentence.quote_eq] using
      IsBounded.neg (by simp) <| (isBounded_quote_iff (V := V) δ.val).mpr δ.bounded;
  have hP : T.internalize V ⊢ provabilityFormula T ⌜χ⌝ 🡘 ∃¹ ⌜δ.val⌝ := by
    simpa using internal_provable_of_outer_provable (V := V) (Entailment.WeakerThan.pbl hδ :
      T ⊢ provabilityPred T χ 🡘 ∃¹ δ.val);
  have hnA : T.internalize V ⊢ ∼(∃¹ ⌜δ.val⌝) 🡒 ∀¹ A := by simp [A];
  have hAn : T.internalize V ⊢ ∀¹ A 🡒 ∼(∃¹ ⌜δ.val⌝) := by simp [A];
  have h₁ := tprovable_all_or_all_imp_allBallOrBall (T := T) A B;
  have h₂ := tprovable_allBallOrBall_imp (T := T) hA hB;
  have hτ' : T.internalize V ⊢ ⌜τ⌝ ⋏ provabilityFormula T ⌜χ⌝ 🡒 ∀¹ B := by
    simpa [hπB] using hτ;
  have h₃ := h (allBallOrBall A B) (shift_allBallOrBall hA hB)
    (isPrenexHierarchy_allBallOrBall hAb hθb) (by cl_prover [hP, hnA, h₁, hτ']);
  have h₄ : T.internalize V ⊢ ⌜σ⌝ ⋏ provabilityFormula T ⌜χ⌝ 🡒 ∀¹ B := by
    cl_prover [hP, hAn, h₂, h₃];
  simpa [hπB] using h₄

end Bootstrapping

variable (T) in
noncomputable def pi1ConservativeDef : ArithmeticSemisentence 2 :=
  “a b. ∀ x, !(isSemiformula ℒₒᵣ).sigma 0 x → !(shiftGraph ℒₒᵣ) x x →
    !(isPrenexHierarchy 𝚷 1).sigma x → ∀ y, !(impGraph ℒₒᵣ) y b x → ∀ z, !(impGraph ℒₒᵣ) z a x →
      !(provable T) y → !(provable T) z”

lemma eval_pi1ConservativeDef {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b : V) :
    V ⊧/![a, b] (pi1ConservativeDef T) ↔ Pi1Conservative T a b := by
  simp [pi1ConservativeDef, Pi1Conservative, eq_comm]

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.ArithmeticTheory

open Arithmetic

variable (T : ArithmeticTheory) [T.Δ₁]

/-- $\varphi \rhd \psi$ read as: every prenex $\Pi_1$ sentence provable in $T + \psi$ is provable
in $T + \varphi$.

- [HM90, Definition 3.1]
-/
noncomputable def pi1Conservativity :
    InterpretabilityLogic.Interpretability T.standardProvability where
  rhd σ τ := (pi1ConservativeDef T)/[⌜σ⌝, ⌜τ⌝]

variable {T}

@[simp] lemma models_pi1Conservativity_iff {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {σ τ : ArithmeticSentence} :
    V↓[ℒₒᵣ] ⊧ T.pi1Conservativity σ τ ↔ Bootstrapping.Pi1Conservative T (⌜σ⌝ : V) ⌜τ⌝ := by
  simp [pi1Conservativity, models_iff, eval_pi1ConservativeDef]

open Bootstrapping in
instance instPi1ConservativityIL [𝗜𝚺₁ ⪯ T] : T.pi1Conservativity.IL where
  J1 := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [standardProvability_def] using pi1Conservative_of_provable
  J2 := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa using Pi1Conservative.trans
  J3 {σ τ χ} := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have h := Pi1Conservative.or (T := T) (V := V) (σ := σ) (τ := τ) (χ := χ);
    simpa using h
  J4 := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [standardProvability_def] using fun h hσ hτ ↦ hσ <| Pi1Conservative.consistent h hτ
  J5 {σ} := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have h := pi1Conservative_dia (T := T) (V := V) (σ := σ);
    simpa [ProvabilityAbstraction.Provability.dia, standardProvability_def] using h

open Bootstrapping in
instance instPi1ConservativityM [𝗜𝚺₁ ⪯ T] : T.pi1Conservativity.M where
  axiomM {σ τ χ} := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have h := Pi1Conservative.and_provabilityPred (T := T) (V := V) (σ := σ) (τ := τ) (χ := χ);
    simpa [standardProvability_def] using h

end FFL.FirstOrder.ArithmeticTheory

namespace FFL.InterpretabilityLogic

open FirstOrder Arithmetic

variable {α : Type*} {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]
  {f : ProvabilityLogic.Realization α ℒₒᵣ} {A : Formula α}

/-- - [HM90, Definition 3.1] -/
theorem Logic.ILM.arithmetical_soundness_pi1Conservativity (h : 𝐈𝐋𝐌 ⊢ A) :
    T ⊢ A.interpret f T.standardProvability T.pi1Conservativity :=
  Entailment.WeakerThan.pbl <| Logic.ILM.arithmetical_soundness h

end FFL.InterpretabilityLogic
