module

public import AlphaCentauri.Interpretability.Formalized
public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.ProvabilityFormula
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic
public import Foundation.ProvabilityLogic.Arithmetic.Interpret
public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import AlphaCentauri.InterpretabilityLogic.Arithmetic.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ISigma1.Prenex
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Prenex

/-!
# $\Gamma$-conservativity as an interpretability abstraction

Reading `φ ▷ ψ` as "every prenex $\Gamma_n$ sentence provable in $T + \psi$ is provable in
$T + \varphi$" for $\Gamma \in \{\Sigma, \Pi\}$ and $n \in \mathbb{N}$. Once $T$ contains
$\mathsf{I}\Sigma_1$, it satisfies the arithmetical forms of $\mathbf{J1}$–$\mathbf{J4}$ over
$\mathsf{I}\Sigma_1$, and for $\Gamma_n = \Pi_1$ also those of $\mathbf{J5}$ and $\mathbf{M}$.
If $T$ is moreover $\Sigma_1$-sound, the instance $\Diamond\Box\bot \rhd \Box\bot$ of
$\mathbf{J5}$ is not in the $\Gamma_n$-conservativity logic of $T$ for $\Sigma_{n + 1}$ and
$\Pi_{n + 2}$.

Conjoining a sentence $\chi$ to both sides preserves $\Gamma_n$-conservativity whenever
$\neg\chi$ is equivalent to a prenex $\Gamma_n$ sentence. Hence $T$ satisfies $\mathbf{M}$ for
$n \geq 2$, and, once it contains $\mathsf{B}\Sigma_2$, $\mathsf{Sa}$ for $\Sigma_n$ with $n \geq 2$
and $\Pi_n$ with $n \geq 3$, and $\mathsf{Sb}$ for $\Pi_n$ with $n \geq 2$ and $\Sigma_n$ with
$n \geq 3$.

## References

- [HM90, Definition 3.1]
- [Ign91, §1, Definition 2.8, Theorem 1, Theorem A.2]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping Bootstrapping.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁]

namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable (T) in
/-- For every internal prenex $\Gamma_n$ sentence `x`, if `T` proves `b 🡒 x` then `T` proves
`a 🡒 x`. -/
def Conservative (Γ : Polarity) (n : ℕ) (a b : V) : Prop :=
  ∀ x, IsSemiformula ℒₒᵣ 0 x → shift ℒₒᵣ x = x → IsPrenexHierarchy Γ n x →
    Provable T (imp ℒₒᵣ b x) → Provable T (imp ℒₒᵣ a x)

variable {Γ : Polarity} {n : ℕ} {σ τ χ : ArithmeticSentence}

lemma conservative_quote_iff :
    Conservative T Γ n (⌜σ⌝ : V) ⌜τ⌝ ↔
      ∀ π : Formula V ℒₒᵣ, π.shift = π → IsPrenexHierarchy Γ n π.val →
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

lemma conservative_of_provable (h : Provable T (⌜σ 🡒 τ⌝ : V)) :
    Conservative T Γ n (⌜σ⌝ : V) ⌜τ⌝ := by
  apply conservative_quote_iff.mpr;
  intro π _ _ hτ;
  have hστ : T.internalize V ⊢ ⌜σ⌝ 🡒 ⌜τ⌝ := by
    simpa using (tprovable_tquote_iff_provable_quote_sentence (σ := σ 🡒 τ)).mpr h;
  exact C_trans hστ hτ

lemma Conservative.trans {a b c : V} (hab : Conservative T Γ n a b)
    (hbc : Conservative T Γ n b c) : Conservative T Γ n a c := by
  intro x hx hs hπ h;
  exact hab x hx hs hπ <| hbc x hx hs hπ h

lemma Conservative.or (hσ : Conservative T Γ n (⌜σ⌝ : V) ⌜χ⌝)
    (hτ : Conservative T Γ n (⌜τ⌝ : V) ⌜χ⌝) : Conservative T Γ n (⌜σ ⋎ τ⌝ : V) ⌜χ⌝ := by
  rw [conservative_quote_iff] at hσ hτ ⊢;
  intro π hs hπ h;
  have h₁ := hσ π hs hπ h;
  have h₂ := hτ π hs hπ h;
  have h₃ : T.internalize V ⊢ ⌜σ⌝ ⋎ ⌜τ⌝ 🡒 π := by cl_prover [h₁, h₂];
  simpa using h₃

lemma Conservative.provable_imp (h : Conservative T Γ n (⌜σ⌝ : V) ⌜τ⌝)
    (hχ : ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n χ) (hτ : Provable T (⌜τ 🡒 χ⌝ : V)) :
    Provable T (⌜σ 🡒 χ⌝ : V) := by
  simpa [Sentence.quote_eq] using h ⌜χ⌝ (by simp) (by simp)
    ((isPrenexHierarchy_quote_iff χ).mpr hχ) (by simpa [Sentence.quote_eq] using hτ)

lemma conservative_dia_pi1 [𝗜𝚺₁ ⪯ T] :
    Conservative T 𝚷 1 (⌜∼provabilityPred T (∼σ)⌝ : V) ⌜σ⌝ := by
  apply conservative_quote_iff.mpr;
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

lemma Conservative.and_provabilityPred_pi1 [𝗜𝚺₁ ⪯ T] (h : Conservative T 𝚷 1 (⌜σ⌝ : V) ⌜τ⌝) :
    Conservative T 𝚷 1 (⌜σ ⋏ provabilityPred T χ⌝ : V) ⌜τ ⋏ provabilityPred T χ⌝ := by
  rw [conservative_quote_iff] at h ⊢;
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
    simpa using internal_provable_of_outer_provable (V := V) (WeakerThan.pbl hδ :
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

/-- If $\neg\chi$ is equivalent in `T` to a prenex $\Gamma_n$ sentence, conjoining `χ` to both
sides preserves $\Gamma_n$-conservativity. -/
lemma Conservative.and [𝗜𝚺₁ ⪯ T] {ψ : ArithmeticSentence}
    (hψ : ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n ψ) (hχψ : T ⊢ ∼χ 🡘 ψ)
    (h : Conservative T Γ n (⌜σ⌝ : V) ⌜τ⌝) : Conservative T Γ n (⌜σ ⋏ χ⌝ : V) ⌜τ ⋏ χ⌝ := by
  rw [conservative_quote_iff] at h ⊢;
  intro π hs hπ hτ;
  obtain ⟨θ, hθs, hθ, hθe⟩ := exists_isPrenexHierarchy_tprovable_or_iff (T := T)
    (φ := ⌜ψ⌝) (ψ := π) (by simp [typed_quote_shift]) hs
    (by simpa [Sentence.quote_eq] using (isPrenexHierarchy_quote_iff (V := V) ψ).mpr hψ) hπ;
  have hc : T.internalize V ⊢ ∼⌜χ⌝ 🡘 ⌜ψ⌝ := by
    simpa using internal_provable_of_outer_provable (V := V) hχψ;
  have hτ' : T.internalize V ⊢ ⌜τ⌝ ⋏ ⌜χ⌝ 🡒 π := by simpa using hτ;
  have h₁ := h θ hθs hθ (by cl_prover [hτ', hc, hθe]);
  have h₂ : T.internalize V ⊢ ⌜σ⌝ ⋏ ⌜χ⌝ 🡒 π := by cl_prover [h₁, hc, hθe];
  simpa using h₂

end Bootstrapping

variable (T Γ n) in
noncomputable def conservativeDef : ArithmeticSemisentence 2 :=
  “a b. ∀ x, !(isSemiformula ℒₒᵣ).sigma 0 x → !(shiftGraph ℒₒᵣ) x x →
    !(isPrenexHierarchy Γ n).sigma x → ∀ y, !(impGraph ℒₒᵣ) y b x → ∀ z, !(impGraph ℒₒᵣ) z a x →
      !(provable T) y → !(provable T) z”

lemma eval_conservativeDef {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Γ : Polarity) (n : ℕ) (a b : V) :
    V ⊧/![a, b] (conservativeDef T Γ n) ↔ Conservative T Γ n a b := by
  simp [conservativeDef, Conservative, eq_comm]

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.ArithmeticTheory

open Arithmetic

variable (T : ArithmeticTheory) [T.Δ₁] (Γ : Polarity) (n : ℕ)

/-- $\varphi \rhd \psi$ read as: every prenex $\Gamma_n$ sentence provable in $T + \psi$ is provable
in $T + \varphi$.

- [HM90, Definition 3.1]
-/
noncomputable def conservativity :
    InterpretabilityLogic.Interpretability T.standardProvability where
  rhd σ τ := (conservativeDef T Γ n)/[⌜σ⌝, ⌜τ⌝]

variable {T Γ n}

@[simp] lemma models_conservativity_iff {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {σ τ : ArithmeticSentence} :
    V↓[ℒₒᵣ] ⊧ (T.conservativity Γ n) σ τ ↔ Bootstrapping.Conservative T Γ n (⌜σ⌝ : V) ⌜τ⌝ := by
  simp [conservativity, models_iff, eval_conservativeDef]

lemma conservativity_imp_provable_imp {σ τ χ : ArithmeticSentence}
    (hχ : ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n χ) :
    𝗜𝚺₁ ⊢ (T.conservativity Γ n) σ τ ⋏ T.standardProvability (τ 🡒 χ) 🡒
      T.standardProvability (σ 🡒 χ) :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [standardProvability_def] using fun h hτ ↦ Bootstrapping.Conservative.provable_imp h hχ hτ

open Bootstrapping in
instance instConservativityCL [𝗜𝚺₁ ⪯ T] : (T.conservativity Γ n).CL where
  J1 := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [standardProvability_def] using conservative_of_provable
  J2 := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa using Conservative.trans
  J3 {σ τ χ} := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have h := Conservative.or (T := T) (Γ := Γ) (n := n) (V := V) (σ := σ) (τ := τ) (χ := χ);
    simpa using h
  J4 {σ τ} := by
    obtain ⟨χ, hχp, hχ⟩ := ISigma1.exists_prenexHierarchy_refutable Γ n;
    have h₁ := conservativity_imp_provable_imp (T := T) (σ := σ) (τ := τ) hχp;
    have h₂ : 𝗜𝚺₁ ⊢ T.standardProvability (∼τ) 🡒 T.standardProvability (τ 🡒 χ) :=
      T.standardProvability.mono <| by cl_prover;
    have h₃ : 𝗜𝚺₁ ⊢ T.standardProvability (σ 🡒 χ) 🡒 T.standardProvability (∼σ) :=
      T.standardProvability.mono <| by
        have : T ⊢ ∼χ := Entailment.WeakerThan.pbl hχ;
        cl_prover [this];
    simp only [ProvabilityAbstraction.Provability.dia];
    generalize (T.conservativity Γ n) σ τ = R at h₁ ⊢;
    generalize T.standardProvability (∼σ) = A at h₃ ⊢;
    generalize T.standardProvability (∼τ) = B at h₂ ⊢;
    generalize T.standardProvability (σ 🡒 χ) = C at h₁ h₃;
    generalize T.standardProvability (τ 🡒 χ) = D at h₁ h₂;
    cl_prover [h₁, h₂, h₃]

open Bootstrapping in
instance instConservativityPi1IL [𝗜𝚺₁ ⪯ T] : (T.conservativity 𝚷 1).IL where
  toCL := inferInstance
  J5 {σ} := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have h := conservative_dia_pi1 (T := T) (V := V) (σ := σ);
    simpa [ProvabilityAbstraction.Provability.dia, standardProvability_def] using h

open Bootstrapping in
instance instConservativityPi1M [𝗜𝚺₁ ⪯ T] : (T.conservativity 𝚷 1).M where
  axiomM {σ τ χ} := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have h := Conservative.and_provabilityPred_pi1 (T := T) (V := V) (σ := σ) (τ := τ) (χ := χ);
    simpa [standardProvability_def] using h

lemma hierarchy_conservativity {σ τ : ArithmeticSentence} :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 ((T.conservativity Γ n) σ τ) := by
  have h {k : ℕ} (φ : 𝚺-[ℬ[<, ℒₒᵣ], 1].Semisentence k) (Γ' : Polarity) :
      ℬ[<, ℒₒᵣ].Hierarchy Γ' 2 φ.val :=
    (Bounding.HierarchySymbol.Semiformula.hierarchy_sigma φ).strict_mono Γ' (by decide);
  simp [conservativity, conservativeDef, h]

open Bootstrapping in
/-- If $\neg\chi$ is a $\Gamma'_m$ sentence with $\Gamma'_m \subseteq \Gamma_n$, conjoining `χ` to
both sides preserves $\Gamma_n$-conservativity. -/
lemma conservativity_and [𝗜𝚺₁ ⪯ T] {Γ' : Polarity} {m : ℕ} [𝗕𝚺m ⪯ T]
    {σ τ χ : ArithmeticSentence} (hχ : ℬ[<, ℒₒᵣ].Hierarchy Γ' m (∼χ))
    (hn : Γ = Γ' ∧ m ≤ n ∨ m < n) :
    𝗜𝚺₁ ⊢ (T.conservativity Γ n) σ τ 🡒 (T.conservativity Γ n) (σ ⋏ χ) (τ ⋏ χ) := by
  obtain ⟨ψ, hψ, hχψ⟩ := exists_prenexHierarchy_provable_iff T hχ hn;
  exact complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa using Conservative.and (V := V) (σ := σ) (τ := τ) hψ hχψ

instance instConservativityM [𝗜𝚺₁ ⪯ T] : (T.conservativity Γ (n + 2)).M where
  axiomM {σ τ χ} := by
    have : 𝗕𝚺 1 ⪯ T := BSigma_weakerThan_ISigma.trans inferInstance;
    exact conservativity_and (Γ' := 𝚷) (m := 1) (by simp [standardProvability_def])
      (.inr (by omega))

section

variable [𝗕𝚺2 ⪯ T]

instance instConservativitySigmaSa : (T.conservativity 𝚺 (n + 2)).Sa where
  axiomSa {_ _ χ ψ} := by
    have : 𝗜𝚺₁ ⪯ T := ISigma_weakerThan_BSigma_succ.trans inferInstance;
    have h : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 2 (∼(T.conservativity 𝚺 (n + 2)) χ ψ) := by
      simpa using hierarchy_conservativity;
    exact conservativity_and h (.inl ⟨rfl, by omega⟩)

instance instConservativityPiSa : (T.conservativity 𝚷 (n + 3)).Sa where
  axiomSa {_ _ χ ψ} := by
    have : 𝗜𝚺₁ ⪯ T := ISigma_weakerThan_BSigma_succ.trans inferInstance;
    have h : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 2 (∼(T.conservativity 𝚷 (n + 3)) χ ψ) := by
      simpa using hierarchy_conservativity;
    exact conservativity_and h (.inr (by omega))

instance instConservativityPiSb : (T.conservativity 𝚷 (n + 2)).Sb where
  axiomSb {_ _ χ ψ} := by
    have : 𝗜𝚺₁ ⪯ T := ISigma_weakerThan_BSigma_succ.trans inferInstance;
    have h : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 (∼∼(T.conservativity 𝚷 (n + 2)) χ ψ) := by
      simpa using hierarchy_conservativity;
    exact conservativity_and h (.inl ⟨rfl, by omega⟩)

instance instConservativitySigmaSb : (T.conservativity 𝚺 (n + 3)).Sb where
  axiomSb {_ _ χ ψ} := by
    have : 𝗜𝚺₁ ⪯ T := ISigma_weakerThan_BSigma_succ.trans inferInstance;
    have h : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 (∼∼(T.conservativity 𝚺 (n + 3)) χ ψ) := by
      simpa using hierarchy_conservativity;
    exact conservativity_and h (.inr (by omega))

end

section

variable (T Γ n) {α : Type*}

/-- The $\Gamma_n$-conservativity logic of `T`: the formulas provable in `T` under every
realization, reading `□` as provability in `T` and `▷` as $\Gamma_n$-conservativity over `T`.

- [Ign91, Definition 2.8]
-/
def conservativityLogic : InterpretabilityLogic.Logic α :=
  { A | ∀ f : ProvabilityLogic.Realization α ℒₒᵣ,
    T ⊢ A.interpret f T.standardProvability (T.conservativity Γ n) }

end

section

open FFL.Entailment InterpretabilityLogic InterpretabilityLogic.Formula ProvabilityAbstraction

variable {α : Type*} [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

lemma conservativityLogic_unprovable_axiomJ5 (hn : Γ = 𝚺 ∧ 1 ≤ n ∨ 1 < n) :
    T.conservativityLogic Γ n (α := α) ⊬ Axioms.J5 (□⊥) := by
  obtain ⟨ψ, hψ, hP⟩ := exists_prenexHierarchy_provable_iff 𝗜𝚺₁ (Γ := Γ) (Γ' := 𝚺)
    (σ := T.standardProvability ⊥) (by simp [standardProvability_def]) hn;
  intro h;
  have h₀ : T ⊢ _ := h ⟨fun _ ↦ ⊥⟩;
  simp only [interpret] at h₀;
  generalize hD : T.standardProvability (T.standardProvability ⊥ 🡒 ⊥) 🡒 ⊥ = D at h₀;
  have hψP : T ⊢ ψ 🡒 T.standardProvability ⊥ :=
    WeakerThan.pbl (𝓢 := 𝗜𝚺₁) <| by cl_prover [hP];
  have h₁ : T ⊢ T.standardProvability (T.standardProvability ⊥ 🡒 ψ) :=
    WeakerThan.pbl <| T.standardProvability.D1 <|
      WeakerThan.pbl (𝓢 := 𝗜𝚺₁) <| by cl_prover [hP];
  have h₂ : T ⊢ (T.conservativity Γ n) D (T.standardProvability ⊥) ⋏
      T.standardProvability (T.standardProvability ⊥ 🡒 ψ) 🡒 T.standardProvability (D 🡒 ψ) :=
    WeakerThan.pbl <| conservativity_imp_provable_imp hψ;
  have h₃ : T ⊢ T.standardProvability (D 🡒 ψ) 🡒
      T.standardProvability (T.standardProvability (T.standardProvability ⊥ 🡒 ⊥) 🡒
        T.standardProvability ⊥) 🡒 T.standardProvability (T.standardProvability ⊥) := by
    have : T ⊢ (D 🡒 ψ) 🡒 (T.standardProvability (T.standardProvability ⊥ 🡒 ⊥) 🡒
        T.standardProvability ⊥) 🡒 T.standardProvability ⊥ := by
      subst hD; cl_prover [hψP];
    exact WeakerThan.pbl <|
      C_trans (T.standardProvability.mono this) T.standardProvability.D2;
  have h₄ : T ⊢ T.standardProvability (T.standardProvability (T.standardProvability ⊥ 🡒 ⊥) 🡒
      T.standardProvability ⊥) :=
    WeakerThan.pbl <| T.standardProvability.D1 <|
      WeakerThan.pbl formalized_löb_theorem;
  apply iIncon_unprovable_of_sigma1_sound (𝔅 := T.standardProvability) 2;
  simpa using h₃ ⨀ (h₂ ⨀ K_intro h₀ h₁) ⨀ h₄

/-- The instance $\Diamond\Box\bot \rhd \Box\bot$ of $\mathbf{J5}$ is not provable in
the $\Sigma_{n + 1}$-conservativity logic of a $\Sigma_1$-sound theory containing
$\mathsf{I}\Sigma_1$.

- [Ign91, §1]
-/
theorem conservativityLogic_sigma_unprovable_axiomJ5 :
    T.conservativityLogic 𝚺 (n + 1) (α := α) ⊬ Axioms.J5 (□⊥) :=
  conservativityLogic_unprovable_axiomJ5 <| .inl ⟨rfl, by omega⟩

/-- The instance $\Diamond\Box\bot \rhd \Box\bot$ of $\mathbf{J5}$ is not provable in
the $\Pi_{n + 2}$-conservativity logic of a $\Sigma_1$-sound theory containing
$\mathsf{I}\Sigma_1$.

- [Ign91, §1]
-/
theorem conservativityLogic_pi_unprovable_axiomJ5 :
    T.conservativityLogic 𝚷 (n + 2) (α := α) ⊬ Axioms.J5 (□⊥) :=
  conservativityLogic_unprovable_axiomJ5 <| .inr (by omega)

end

end FFL.FirstOrder.ArithmeticTheory

end
