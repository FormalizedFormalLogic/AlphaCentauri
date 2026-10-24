module

public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic

/-!
# Abstract provability: formalized consistency statements
-/

@[expose] public section

namespace FFL.FirstOrder.ProvabilityAbstraction

open FFL.Entailment Diagonalization Provability

variable
  {L : Language} [L.ReferenceableBy L] [L.DecidableEq]
  {T₀ T : Theory L} [Diagonalization T₀] [T₀ ⪯ T] (𝔅 : Provability T₀ T) [𝔅.HBL]

/-- $T_0$ proves that $\mathrm{Con}_{\mathfrak{B}}$ implies the unprovability of
$\mathrm{Con}_{\mathfrak{B}}$ in $\mathfrak{B}$.
- [HP98, Theorem III.2.21]
- [HP98, Corollary III.2.22] -/
theorem formalized_con_unprovable : T₀ ⊢ 𝔅.con 🡒 ∼𝔅 𝔅.con := by
  have h₁ : T₀ ⊢ gödel 𝔅 🡘 𝔅.con := gödel_iff_con
  have h₂ : T₀ ⊢ 𝔅.con 🡒 ∼𝔅 (gödel 𝔅) := formalized_unprovable_gödel
  have h₃ : T₀ ⊢ 𝔅 𝔅.con 🡒 𝔅 (gödel 𝔅) := mono' (K_right h₁)
  exact C_trans h₂ (contra h₃)

/-- $T_0$ proves that $\mathrm{Con}_{\mathfrak{B}}$ implies that $\neg\mathrm{Con}_{\mathfrak{B}}$
is not refutable in $\mathfrak{B}$.
- [HP98, Lemma III.4.9] -/
theorem formalized_con_unrefutable : T₀ ⊢ 𝔅.con 🡒 ∼𝔅 (∼𝔅.con 🡒 ⊥) := by
  have h₁ : T₀ ⊢ 𝔅 (∼𝔅.con 🡒 ⊥) 🡒 𝔅 𝔅.con := mono' <| by cl_prover
  exact C_trans (formalized_con_unprovable 𝔅) (contra h₁)

end FFL.FirstOrder.ProvabilityAbstraction
