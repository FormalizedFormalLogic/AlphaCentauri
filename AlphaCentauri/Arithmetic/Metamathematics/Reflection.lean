module

public import Foundation.FirstOrder.Incompleteness.Second
public import AlphaCentauri.Incompleteness.ProvabilityAbstraction.Reflection

@[expose] public section
/-!
# Local reflection principles for arithmetic theories

The arithmetic instantiation of `ProvabilityAbstraction.Provability.localReflectionOn` /
`localReflection` at the standard provability predicate `Theory.standardProvability`, together
with the restriction to a level `Γ n` of the arithmetical hierarchy, and the two theorems
relating `Rfn(T)` to `Con(T)`.

NOTE: the notation `𝗥𝗳𝗻 T` / `𝗥𝗳𝗻[Γ n] T` below, styled after Foundation's `𝗜𝗡𝗗 𝚺 n`, is proposed
here as a candidate for upstreaming into Foundation together with the abstract definitions in
`ProvabilityAbstraction.Provability`; it is not settled as final.

- [Lin97, §4.1, p. 52]
- [AB05, §4]
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment

/-- The local reflection schema `Rfn(T)` of an arithmetic theory `T`, via its standard
provability predicate.
- [Lin97, §4.1, p. 52]
- [AB05, §4] -/
abbrev _root_.LO.FirstOrder.Theory.localReflection (T : ArithmeticTheory) [T.Δ₁] : ArithmeticTheory :=
  T.standardProvability.localReflection

@[inherit_doc] notation "𝗥𝗳𝗻 " T:max => Theory.localReflection T

/-- The local reflection schema of `T` restricted to the `Γ n` sentences of the arithmetical
hierarchy, `Rfn_{Γ n}(T)`.
- [Lin97, §4.1, p. 52]
- [AB05, §4] -/
abbrev _root_.LO.FirstOrder.Theory.localReflectionOnHierarchy
    (T : ArithmeticTheory) [T.Δ₁] (Γ : Polarity) (n : ℕ) : ArithmeticTheory :=
  T.standardProvability.localReflectionOn (Hierarchy Γ n)

@[inherit_doc] notation "𝗥𝗳𝗻[" Γ:max n:max "] " T:max => Theory.localReflectionOnHierarchy T Γ n

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- `T` is strictly weaker than `T ∪ Rfn(T)` for consistent `T`: `Rfn(T)` proves `Con(T)`, which
`T` itself cannot prove by Gödel's second incompleteness theorem.
- [Lin97, §4.1, p. 52] -/
instance [Consistent T] : T ⪱ T ∪ 𝗥𝗳𝗻 T := sorry

/-- `Rfn_{Π₁}(T)` and `Con(T)` are equivalent over `T`.
- [Lin97, Exercise 4.1(b)(ii)]
- [AB05, Lemma 22(i)] -/
theorem localReflection_pi_one_equiv_con : T ∪ 𝗥𝗳𝗻[𝚷 1] T ≊ T ∪ T.Con := sorry

end LO.FirstOrder.Arithmetic
