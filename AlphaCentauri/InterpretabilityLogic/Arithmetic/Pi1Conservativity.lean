module

public import AlphaCentauri.InterpretabilityLogic.Arithmetic.Basic
public import AlphaCentauri.ToFoundation.ProvabilityFormula
public import Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
# Arithmetical soundness of $\mathbf{ILM}$ for $\Pi_1$-conservativity

For a $\Delta_1$-axiomatized arithmetical theory $T$, `T.pi1Conservativity` reads
$\varphi \rhd \psi$ as "every $\Pi_1$ sentence provable in $T + \psi$ is provable in
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
/-- Every internal $\Pi_1$ sentence `x` such that `b 🡒 x` is provable in `T` makes `a 🡒 x`
provable in `T`. -/
def Pi1Conservative (a b : V) : Prop :=
  ∀ x, IsSemiformula ℒₒᵣ 0 x → shift ℒₒᵣ x = x → IsPi 1 x →
    Provable T (imp ℒₒᵣ b x) → Provable T (imp ℒₒᵣ a x)

variable {σ τ χ : ArithmeticSentence}

lemma pi1Conservative_quote_iff :
    Pi1Conservative T (⌜σ⌝ : V) ⌜τ⌝ ↔ ∀ π : Formula V ℒₒᵣ, π.shift = π → IsPi 1 π.val →
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
  have h₂ := h ⊥ (by simp) (by simp) (by cl_prover [h₁]);
  have h₃ : T.internalize V ⊢ ∼⌜σ⌝ := by cl_prover [h₂];
  simpa using (tprovable_tquote_iff_provable_quote_sentence (σ := ∼σ)).mp (by simpa using h₃)

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

lemma Pi1Conservative.and_provabilityPred (h : Pi1Conservative T (⌜σ⌝ : V) ⌜τ⌝) :
    Pi1Conservative T (⌜σ ⋏ provabilityPred T χ⌝ : V) ⌜τ ⋏ provabilityPred T χ⌝ := by
  rw [pi1Conservative_quote_iff] at h ⊢;
  intro π hs hπ hτ;
  have hP : (⌜provabilityPred T χ⌝ : Formula V ℒₒᵣ) = provabilityFormula T ⌜χ⌝ := by simp;
  have hPs : (provabilityFormula T (⌜χ⌝ : V)).shift = provabilityFormula T ⌜χ⌝ := by
    rw [← hP]; ext; simpa [Sentence.quote_eq] using Sentence.shift_quote (V := V) (provabilityPred T χ);
  have hPσ : IsSigma 1 (provabilityFormula T (⌜χ⌝ : V)).val := by
    rw [← hP]; exact (isSigma_quote_iff (provabilityPred T χ)).mpr (by simp);
  have h₁ := h (provabilityFormula T ⌜χ⌝ 🡒 π) (by simp [hPs, hs]) (by
    simp only [Semiformula.val_imp, imp, IsHierarchy.or_iff];
    exact ⟨by simpa using hPσ.neg (by simp), hπ⟩) (by simp at hτ; cl_prover [hτ]);
  have h₂ : T.internalize V ⊢ ⌜σ⌝ ⋏ provabilityFormula T ⌜χ⌝ 🡒 π := by cl_prover [h₁];
  simpa using h₂

end Bootstrapping

end FFL.FirstOrder.Arithmetic
