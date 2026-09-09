module

public import AlphaCentauri.ProvablyTotal.Basic

/-!
# Parikh's theorem

A `𝚫₀` totality proved by `𝗜𝚺₀` is already provable in bounded form, so an `𝗜𝚺₀`-provably total
function with a `𝚫₀` graph is bounded by a term.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {k : ℕ}

/-- **Parikh's theorem**: a totality `𝗜𝚺₀` proves for a `𝚫₀` formula is provable with the
existential bounded by a term.
- [HP98, Theorem V.1.4]
- [Bus98A, Theorem 1.2.7.1] -/
axiom parikh (φ : ArithmeticSemisentence (k + 1)) (hφ : Hierarchy 𝚺 0 φ)
    (h : 𝗜𝚺₀ ⊢ ∀¹* ∃¹ φ) :
    ∃ t : ClosedSemiterm ℒₒᵣ k, 𝗜𝚺₀ ⊢ ∀¹* ∃¹[“#0 < !!(Rew.bShift t)”] φ

/-- An `𝗜𝚺₀`-provably total function with a `𝚫₀` graph is bounded by a term, hence grows at most
polynomially.
- [HP98, Theorem V.1.4]
- [Bus98A, Theorem 1.2.7.1] -/
axiom exists_term_bound_of_provablyTotal {f : (Fin k → ℕ) → ℕ} {φ : 𝚺₁.Semisentence (k + 1)}
    (hφ : Hierarchy 𝚺 0 φ.val) (h : 𝗜𝚺₀.ProvablyTotalVia f φ) :
    ∃ t : ClosedSemiterm ℒₒᵣ k, ∀ v, f v ≤ Semiterm.valb v t

end FFL.FirstOrder.Arithmetic
