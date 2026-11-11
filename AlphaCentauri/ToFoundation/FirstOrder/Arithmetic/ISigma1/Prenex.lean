module

public import Foundation.FirstOrder.Arithmetic.ISigma1.Prenex

/-!
# Prenex sentences of a given level over $\mathsf{I}\Sigma_1$

Companion of Foundation's `Arithmetic/ISigma1/Prenex.lean`. Every prenex class contains a sentence
refutable in $\mathsf{I}\Sigma_1$, and every $\Sigma_1$ sentence is $\mathsf{I}\Sigma_1$-provably
equivalent to a prenex $\Sigma_n$ sentence for $n \geq 1$ and to a prenex $\Pi_n$ sentence for
$n \geq 2$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.ISigma1

variable {Γ : Polarity} {n : ℕ} {σ : ArithmeticSentence}

lemma exists_prenexHierarchy_refutable (Γ : Polarity) (n : ℕ) :
    ∃ χ : ArithmeticSentence, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n χ ∧ 𝗜𝚺₁ ⊢ ∼χ := by
  use (Bounding.Prenex.falsum : ℬ[<, ℒₒᵣ].Prenex Γ n Empty 0).val;
  and_intros;
  · exact Bounding.Prenex.val_prenexHierarchy;
  · apply complete;
    intro (V : Type) _ _;
    simp [models_iff, Bounding.Prenex.models_falsum]

lemma exists_prenexHierarchy_provable_iff (hσ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 σ)
    (hn : Γ = 𝚺 ∧ 1 ≤ n ∨ 1 < n) :
    ∃ ψ, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n ψ ∧ 𝗜𝚺₁ ⊢ σ 🡘 ψ := by
  obtain ⟨φ, hφ⟩ := hasPrenex hσ;
  obtain ⟨ψ, hψ, hφψ⟩ : ∃ ψ, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n ψ ∧
      ∀ (M : Type) [Tarski.Structure ℒₒᵣ M] [Nonempty M] (e : Fin 0 → M) (f : Empty → M),
        Semiformula.Eval e f φ.val ↔ Semiformula.Eval e f ψ := by
    rcases hn with ⟨rfl, hn⟩ | hn;
    · exact φ.val_prenexHierarchy.exists_eval_iff_of_le hn;
    · exact φ.val_prenexHierarchy.exists_eval_iff_of_lt Γ hn;
  use ψ;
  and_intros;
  · exact hψ;
  · apply complete;
    intro (V : Type) _ _;
    have := models_of_provable (M := V) inferInstance hφ;
    simpa [models_iff, hφψ, -Bounding.Prenex.val_sigmaInv] using this

end FFL.FirstOrder.Arithmetic.ISigma1

end
