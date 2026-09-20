module

public import AlphaCentauri.Calculus.Induction.Forcing

/-!
# Instantiating a block of universal quantifiers

Provability is defined for sentences, so a universally quantified sentence is instantiated at
terms with free variables at the level of derivations: the existential closure of a formula is
derivable from any instance of it, and dually the universal closure of a sentence entails every
instance of it.

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

end FFL.FirstOrder

end
