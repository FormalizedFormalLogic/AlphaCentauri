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

end Bootstrapping

end FFL.FirstOrder.Arithmetic
