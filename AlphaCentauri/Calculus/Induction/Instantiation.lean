module

public import AlphaCentauri.Calculus.Induction.Forcing
public import AlphaCentauri.ProvablyTotal.Basic

/-!
# Instantiating a block of universal quantifiers

Provability is defined for sentences, so a universally quantified sentence is instantiated at
terms with free variables at the level of derivations: the existential closure of a formula is
derivable from any instance of it, and dually the universal closure of a sentence entails every
instance of it. Cut against a proof of totality, that gives an anchored derivation of the graph
with the arguments as free variables.

- [Bus98A, Section 3.1.3]
-/

@[expose] public section

namespace FFL.FirstOrder

open Rewriting

namespace LK.Derivation

variable {L : Language} {Γ : LK.Sequent L}

/-- The existential closure is derivable from any instance of it. -/
def exsClosure : {k : ℕ} → (χ : Semiproposition L k) → (v : Fin k → SyntacticTerm L) →
    ⊢ᴸᴷ¹ Γ + ⦃χ ⇜ v⦄ → ⊢ᴸᴷ¹ Γ + ⦃∃¹* χ⦄
  | 0, _, _, d => d.cast (by simp)
  | _ + 1, χ, v, d =>
    exsClosure (∃¹ χ) (Matrix.vecTail v) <|
      (exs (Γ := Γ) (t := Matrix.vecHead v) (φ := (Rew.subst (Matrix.vecTail v)).q ▹ χ)
        (d.cast (by simp only [Rew.subst_q_app, Matrix.cons_head_tail]))).cast (by simp)

/-- The universal closure of a sentence entails every instance of it at terms with free
variables. -/
def specializeMany {k : ℕ} (χ : Semisentence L k) (v : Fin k → SyntacticTerm L) :
    ⊢ᴸᴷ¹ ⦃∼((∀¹* χ : Sentence L) : Proposition L), Rew.embSubsts v ▹ χ⦄ :=
  have e : (Rew.subst v).comp (Rew.emb : Rew L Empty k ℕ k) = Rew.embSubsts v := by
    ext x
    · simp [Rew.comp_app]
    · exact x.elim
  let d : ⊢ᴸᴷ¹ ⦃Rew.embSubsts v ▹ χ⦄ + ⦃(∼(emb χ : Semiproposition L k)) ⇜ v⦄ :=
    (eta (Rew.embSubsts v ▹ χ)).cast (by simp [← TransitiveRewriting.comp_app, e])
  (exsClosure _ v d).cast (by simp [add_comm])

end LK.Derivation

namespace Arithmetic.LKI.Canonical

open LK.Derivation

variable {k : ℕ} {φ : 𝚺₁.Semisentence (k + 1)}

/-- The graph of `φ` at the free variables `&0 … &(k-1)` is strict $\Sigma_1$. -/
lemma strictHierarchy_embSubsts_exs (hφ : StrictHierarchy 𝚺 1 φ.val) :
    StrictHierarchy 𝚺 1
      (Rew.embSubsts (fun i : Fin k ↦ (&i : ArithmeticTerm ℕ)) ▹ (∃¹ φ.val)) :=
  StrictHierarchy.rew _ hφ.exs

/-- A proof of totality in `𝗜 𝚺 1` becomes an anchored derivation of the graph of `φ` at the
free variables `&0 … &(k-1)`.

- [Bus98A, Section 3.1.3] -/
theorem nonempty_anchored_instance_of_provable_totality (h : 𝗜 𝚺 1 ⊢ totalitySentence φ) :
    ⊢ᴸᴷᴵ[StrictHierarchy 𝚺 1, fun ψ ↦ StrictHierarchy 𝚺 1 ψ ∨ StrictHierarchy 𝚷 1 ψ]
      ⦃Rew.embSubsts (fun i : Fin k ↦ (&i : ArithmeticTerm ℕ)) ▹ (∃¹ φ.val)⦄ := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp h
  have dcut : ⊢ᴸᴷ¹ ⦃Rew.embSubsts (fun i : Fin k ↦ (&i : ArithmeticTerm ℕ)) ▹ (∃¹ φ.val)⦄
      + ∼LK.Sequent.embed Δ :=
    (cut (φ := (totalitySentence φ : ArithmeticProposition)) (Γ := ∼LK.Sequent.embed Δ)
      (Δ := ⦃Rew.embSubsts (fun i : Fin k ↦ (&i : ArithmeticTerm ℕ)) ▹ (∃¹ φ.val)⦄)
      (d.cast (by simp [add_comm]))
      ((specializeMany (∃¹ φ.val) fun i ↦ &i).cast
        (by simp [totalitySentence, add_comm]))).cast (by simp [add_comm])
  exact nonempty_anchored_of_derivation (fun _ hη _ ↦ .inl (StrictHierarchy.rew _ hη))
    (fun τ hτ ↦ .inr (StrictHierarchy.rew _ (PeanoMinus.strictHierarchy τ hτ))) hΔ dcut

end Arithmetic.LKI.Canonical

end FFL.FirstOrder

end
