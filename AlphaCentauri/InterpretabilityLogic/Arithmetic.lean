module

public import AlphaCentauri.InterpretabilityLogic.Logic
public import Foundation.ProvabilityLogic.Arithmetic.Interpret
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic
public import AlphaCentauri.Interpretability.InterpretationExistence
public import AlphaCentauri.ToFoundation.ProvabilityFormula
public import Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
# Arithmetical soundness of interpretability logics

An interpretability abstraction over a provability abstraction `𝔅` is a binary operator on
sentences. Interpreting `□` by `𝔅` and `▷` by the operator, every theorem of $\mathbf{IL}$ is
provable under every realization once the arithmetical forms of $\mathbf{J1}$–$\mathbf{J5}$ are,
and every theorem of $\mathbf{ILM}$ once the arithmetical form of $\mathbf{M}$ is as well.

For an arithmetical theory $T \supseteq \mathsf{PA}$ with $\Delta_1$ axioms, reading `□` as the
standard provability predicate of $T$ and `▷` as formalized relative interpretability over $T$
satisfies these forms, so every theorem of $\mathbf{IL}$ is provable in $T$ under every
realization. Reading `φ ▷ ψ` as "every prenex $\Pi_1$ sentence provable in $T + \psi$ is provable
in $T + \varphi$" satisfies them together with the arithmetical form of $\mathbf{M}$ over
$\mathsf{I}\Sigma_1$ once $T$ contains $\mathsf{I}\Sigma_1$, so every theorem of $\mathbf{ILM}$ is
provable in $T$ under every realization.

## References

- [Vis90, §6.1, §6.2.2.1]
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction

variable {α : Type*} {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}

/-- A binary operator on sentences, read as interpretability alongside the provability `𝔅`. -/
structure Interpretability (𝔅 : Provability T₀ T) where
  rhd : Sentence L → Sentence L → Sentence L

namespace Interpretability

variable {𝔅 : Provability T₀ T}

instance : CoeFun (Interpretability 𝔅) (fun _ ↦ Sentence L → Sentence L → Sentence L) := ⟨rhd⟩

variable (𝔍 : Interpretability 𝔅)

/-- $T_0$ proves the arithmetical forms of the axioms $\mathbf{J1}$–$\mathbf{J5}$ of
$\mathbf{IL}$. -/
class IL where
  J1 {σ τ : Sentence L} : T₀ ⊢ 𝔅 (σ 🡒 τ) 🡒 𝔍 σ τ
  J2 {σ τ χ : Sentence L} : T₀ ⊢ 𝔍 σ τ ⋏ 𝔍 τ χ 🡒 𝔍 σ χ
  J3 {σ τ χ : Sentence L} : T₀ ⊢ 𝔍 σ χ ⋏ 𝔍 τ χ 🡒 𝔍 (σ ⋎ τ) χ
  J4 {σ τ : Sentence L} : T₀ ⊢ 𝔍 σ τ 🡒 𝔅.dia σ 🡒 𝔅.dia τ
  J5 {σ : Sentence L} : T₀ ⊢ 𝔍 (𝔅.dia σ) σ
export IL (J1 J2 J3 J4 J5)

/-- $T_0$ proves the arithmetical form of the axiom $\mathbf{M}$. -/
class M where
  axiomM {σ τ χ : Sentence L} : T₀ ⊢ 𝔍 σ τ 🡒 𝔍 (σ ⋏ 𝔅 χ) (τ ⋏ 𝔅 χ)

variable {𝔍} [𝔍.IL] {σ σ' τ τ' χ : Sentence L}

lemma rhd_anti_left (h : T ⊢ σ' 🡒 σ) : T₀ ⊢ 𝔍 σ χ 🡒 𝔍 σ' χ := by
  have h₁ : T₀ ⊢ 𝔍 σ' σ := J1 ⨀ 𝔅.D1 h;
  have h₂ : T₀ ⊢ 𝔍 σ' σ ⋏ 𝔍 σ χ 🡒 𝔍 σ' χ := J2;
  cl_prover [h₁, h₂];

lemma rhd_mono_right (h : T ⊢ τ 🡒 τ') : T₀ ⊢ 𝔍 σ τ 🡒 𝔍 σ τ' := by
  have h₁ : T₀ ⊢ 𝔍 τ τ' := J1 ⨀ 𝔅.D1 h;
  have h₂ : T₀ ⊢ 𝔍 σ τ ⋏ 𝔍 τ τ' 🡒 𝔍 σ τ' := J2;
  cl_prover [h₁, h₂];

end Interpretability

namespace Formula

/-- The arithmetical interpretation of a formula, reading `□` as `𝔅` and `▷` as `𝔍`. -/
@[grind]
def interpret (f : ProvabilityLogic.Realization α L) (𝔅 : Provability T₀ T)
    (𝔍 : Interpretability 𝔅) : Formula α → Sentence L
  | #a    => f.val a
  | ⊥     => ⊥
  | A 🡒 B => A.interpret f 𝔅 𝔍 🡒 B.interpret f 𝔅 𝔍
  | □A    => 𝔅 (A.interpret f 𝔅 𝔍)
  | A ▷ B => 𝔍 (A.interpret f 𝔅 𝔍) (B.interpret f 𝔅 𝔍)

end Formula

open Interpretability Formula

variable [L.DecidableEq] [Diagonalization T₀] [T₀ ⪯ T]
  {𝔅 : Provability T₀ T} [𝔅.HBL] {𝔍 : Interpretability 𝔅} [𝔍.IL]
  {f : ProvabilityLogic.Realization α L} {𝔸 : Set (Formula α)} {A : Formula α}

theorem Logic.ofAxioms.arithmetical_soundness (h𝔸 : ∀ A ∈ 𝔸, T₀ ⊢ A.interpret f 𝔅 𝔍)
    (h : ofAxioms 𝔸 ⊢ A) : T₀ ⊢ A.interpret f 𝔅 𝔍 := by
  induction h with
  | axm hA => exact h𝔸 _ hA;
  | mdp _ _ ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | nec _ ih => exact 𝔅.D1 <| WeakerThan.pbl ih;
  | axiomK => exact 𝔅.D2;
  | axiomL => exact formalized_löb_theorem;
  | axiomJ1 => exact J1;
  | @axiomJ2 A B C =>
    dsimp only [interpret];
    generalize A.interpret f 𝔅 𝔍 = σ, B.interpret f 𝔅 𝔍 = τ, C.interpret f 𝔅 𝔍 = χ;
    have h : T₀ ⊢ 𝔍 σ τ ⋏ 𝔍 τ χ 🡒 𝔍 σ χ := J2;
    cl_prover [h];
  | @axiomJ3 A B C =>
    dsimp only [interpret];
    generalize A.interpret f 𝔅 𝔍 = σ, B.interpret f 𝔅 𝔍 = τ, C.interpret f 𝔅 𝔍 = χ;
    have h₁ : T₀ ⊢ 𝔍 σ χ ⋏ 𝔍 τ χ 🡒 𝔍 (σ ⋎ τ) χ := J3;
    have h₂ : T₀ ⊢ 𝔍 (σ ⋎ τ) χ 🡒 𝔍 ((σ 🡒 ⊥) 🡒 τ) χ :=
      Interpretability.rhd_anti_left <| by cl_prover;
    cl_prover [h₁, h₂];
  | @axiomJ4 A B =>
    dsimp only [interpret];
    generalize A.interpret f 𝔅 𝔍 = σ, B.interpret f 𝔅 𝔍 = τ;
    have h₁ : T₀ ⊢ 𝔍 σ τ 🡒 𝔅.dia σ 🡒 𝔅.dia τ := J4;
    have h₂ : T₀ ⊢ 𝔅 (∼σ) 🡒 𝔅 (σ 🡒 ⊥) := 𝔅.mono <| by cl_prover;
    have h₃ : T₀ ⊢ 𝔅 (τ 🡒 ⊥) 🡒 𝔅 (∼τ) := 𝔅.mono <| by cl_prover;
    cl_prover [h₁, h₂, h₃];
  | @axiomJ5 A =>
    dsimp only [interpret];
    generalize A.interpret f 𝔅 𝔍 = σ;
    have h₁ : T₀ ⊢ 𝔅 (∼σ) 🡒 𝔅 (σ 🡒 ⊥) := 𝔅.mono <| by cl_prover;
    have h₂ : T₀ ⊢ 𝔍 (𝔅.dia σ) σ 🡒 𝔍 (𝔅 (σ 🡒 ⊥) 🡒 ⊥) σ :=
      Interpretability.rhd_anti_left <| WeakerThan.pbl (𝓢 := T₀) <| by cl_prover [h₁];
    exact h₂ ⨀ J5;
  | _ => dsimp [interpret]; cl_prover;

theorem Logic.IL.arithmetical_soundness (h : 𝐈𝐋 ⊢ A) : T₀ ⊢ A.interpret f 𝔅 𝔍 :=
  Logic.ofAxioms.arithmetical_soundness (by simp) h

theorem Logic.ILM.arithmetical_soundness [𝔍.M] (h : 𝐈𝐋𝐌 ⊢ A) : T₀ ⊢ A.interpret f 𝔅 𝔍 := by
  apply Logic.ofAxioms.arithmetical_soundness _ h;
  rintro _ ⟨A, B, C, rfl⟩;
  dsimp only [interpret];
  generalize A.interpret f 𝔅 𝔍 = σ, B.interpret f 𝔅 𝔍 = τ, C.interpret f 𝔅 𝔍 = χ;
  have h₁ : T₀ ⊢ 𝔍 σ τ 🡒 𝔍 (σ ⋏ 𝔅 χ) (τ ⋏ 𝔅 χ) := M.axiomM;
  have h₂ : T₀ ⊢ 𝔍 (σ ⋏ 𝔅 χ) (τ ⋏ 𝔅 χ) 🡒 𝔍 ((σ 🡒 𝔅 χ 🡒 ⊥) 🡒 ⊥) (τ ⋏ 𝔅 χ) :=
    Interpretability.rhd_anti_left <| by cl_prover;
  have h₃ : T₀ ⊢ 𝔍 ((σ 🡒 𝔅 χ 🡒 ⊥) 🡒 ⊥) (τ ⋏ 𝔅 χ) 🡒
      𝔍 ((σ 🡒 𝔅 χ 🡒 ⊥) 🡒 ⊥) ((τ 🡒 𝔅 χ 🡒 ⊥) 🡒 ⊥) :=
    Interpretability.rhd_mono_right <| by cl_prover;
  cl_prover [h₁, h₂, h₃];

end

section

open FirstOrder FirstOrder.Arithmetic FirstOrder.ProvabilityAbstraction

variable (T : ArithmeticTheory) [T.Δ₁]

/-- Formalized relative interpretability over `T`, as an interpretability abstraction over the
standard provability predicate of `T`.

- [Vis90, §5.5]
-/
noncomputable def _root_.FFL.FirstOrder.ArithmeticTheory.interpretabilityAbstraction :
    Interpretability T.standardProvability :=
  ⟨T.interpretability⟩

variable [𝗣𝗔 ⪯ T] [Theory.Δ₁.Sentential T]

instance instILInterpretabilityAbstraction : T.interpretabilityAbstraction.IL where
  J1 := ArithmeticTheory.interpretability_of_provable
  J2 := ArithmeticTheory.interpretability_trans
  J3 := ArithmeticTheory.interpretability_or
  J4 := ArithmeticTheory.consistent_of_interpretability
  J5 := ArithmeticTheory.interpretability_consistency _

variable {T} {α : Type*} {f : ProvabilityLogic.Realization α ℒₒᵣ} {A : Formula α}

/-- Arithmetical soundness of $\mathbf{IL}$: every theorem of $\mathbf{IL}$ is provable in $T$
when `□` is read as provability in $T$ and `▷` as formalized relative interpretability over $T$.

- [Vis90, §6.1]
-/
theorem Logic.IL.arithmetical_soundness_interpretability (h : 𝐈𝐋 ⊢ A) :
    T ⊢ A.interpret f T.standardProvability T.interpretabilityAbstraction :=
  have : 𝗜𝚺₁ ⪯ T :=
    Entailment.WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ 𝗣𝗔) (inferInstance : 𝗣𝗔 ⪯ T)
  Entailment.WeakerThan.pbl (Logic.IL.arithmetical_soundness h)

end

end FFL.InterpretabilityLogic

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

end
