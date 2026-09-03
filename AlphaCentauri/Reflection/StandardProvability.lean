module

public import Foundation.FirstOrder.Incompleteness.Second
public import AlphaCentauri.Reflection.ProvabilityAbstraction

@[expose] public section
/-!
# Local and uniform reflection principles for arithmetic theories

The arithmetic instantiation of `ProvabilityAbstraction.Provability.localReflectionOn` /
`localReflection` at the standard provability predicate `Theory.standardProvability`, together
with the restriction to a level `Γ n` of the arithmetical hierarchy, and the theorems relating
`Rfn(T)` to `Con(T)`.

The *uniform* reflection schema `RFN(T)` is added on top: unlike `Rfn(T)`, whose instances are
sentences, `RFN(T)`'s instances are universally quantified over a free variable, so a single
instance quantifies over all numerals at once. It is written with Foundation's `ssnum`/
`substNumeral` (the same numeral-substitution machinery `Bootstrapping.Arithmetic.diag` uses for
diagonalization) rather than with a truth predicate, exactly mirroring how `RFN` is stated in
[Lin97]/[AB05].

Also added: the finite-case unboundedness of local reflection instantiated at the standard
provability predicate, two consistency results for `T ∪ Rfn(T)`, the equivalence of
`RFN_{Σₙ}(T)` and `RFN_{Πₙ₊₁}(T)`, and the reduction of iterated consistency to iterated
provability of `⊥`.

NOTE: the notation `𝗥𝗳𝗻 T` / `𝗥𝗳𝗻[Γ n] T` / `𝗥𝗙𝗡[Γ n] T` below, styled after Foundation's
`𝗜𝗡𝗗 𝚺 n`, is proposed here as a candidate for upstreaming into Foundation together with the
abstract definitions in `ProvabilityAbstraction.Provability`; it is not settled as final.

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
@[instance] axiom strictlyWeakerThan_localReflection [Consistent T] : T ⪱ T ∪ 𝗥𝗳𝗻 T

/-- `Rfn_{Π₁}(T)` and `Con(T)` are equivalent over `T`.
- [Lin97, Exercise 4.1(b)(ii)]
- [AB05, Lemma 22(i)] -/
axiom localReflection_pi_one_equiv_con : T ∪ 𝗥𝗳𝗻[𝚷 1] T ≊ T ∪ T.Con

/-- `T ∪ Rfn(T)` is consistent whenever `T` is sound in the standard model.
- [Lin97, §4.1, p. 52]
- [AB05, §4.2] -/
@[instance] axiom consistent_localReflection_of_sound [ℕ↓[ℒₒᵣ] ⊧* T] :
    Entailment.Consistent (T ∪ 𝗥𝗳𝗻 T)

/-- `T ∪ Rfn(T)` is consistent whenever `T` is `Σ₁`-sound.
- [Lin97, §4.1, p. 52]
- [AB05, §4.2] -/
@[instance] axiom consistent_localReflection_of_sigma_one_sound [T.SoundOnHierarchy 𝚺 1] :
    Entailment.Consistent (T ∪ 𝗥𝗳𝗻 T)

/-- The uniform reflection schema `RFN_Γ(T)` of an arithmetic theory `T`: for every
one-free-variable formula `φ` satisfying `Γ`, the sentence `∀x (Pr_T(φ(ẋ)) → φ(x))`, where
`φ(ẋ)` — "the result of substituting the numeral of `x` for `φ`'s free variable" — is
formalized via Foundation's numeral-substitution predicate `ssnum`, exactly as
`Bootstrapping.Arithmetic.diag` uses it for diagonalization.
- [Lin97, §4.1, p. 52]
- [AB05, §4.2] -/
def _root_.LO.FirstOrder.Theory.uniformReflectionOn
    (T : ArithmeticTheory) [T.Δ₁] (Γ : ArithmeticSemisentence 1 → Prop) : ArithmeticTheory :=
  { ψ | ∃ φ : ArithmeticSemisentence 1, Γ φ ∧
      ψ = (“∀ x, ∀ y, !Bootstrapping.Arithmetic.ssnum y ↑(Encodable.encode φ) x →
        (!(T.standardProvability.prov) y → !φ x)” : ArithmeticSentence) }

/-- The uniform reflection schema of `T` restricted to the `Γ n` formulas of the arithmetical
hierarchy, `RFN_{Γ n}(T)`.
- [Lin97, §4.1, p. 52]
- [AB05, §4.2] -/
abbrev _root_.LO.FirstOrder.Theory.uniformReflectionOnHierarchy
    (T : ArithmeticTheory) [T.Δ₁] (Γ : Polarity) (n : ℕ) : ArithmeticTheory :=
  T.uniformReflectionOn (Hierarchy Γ n)

@[inherit_doc] notation "𝗥𝗙𝗡[" Γ:max n:max "] " T:max => Theory.uniformReflectionOnHierarchy T Γ n

/-- `RFN_{Σₙ}(T)` and `RFN_{Πₙ₊₁}(T)` are equivalent over `T`, for `n ≥ 1`.
- [AB05, Lemma 22(ii)] -/
axiom uniformReflectionOnHierarchy_sigma_equiv_pi_succ {n : ℕ} (hn : 1 ≤ n) :
    T ∪ 𝗥𝗙𝗡[𝚺 n] T ≊ T ∪ 𝗥𝗙𝗡[𝚷 (n + 1)] T

/-- `T` bundled with a witness of its own `Δ₁`-definability, after `n` rounds of adjoining its own
formalized consistency statement: the pair for `T₀ = T`, `Tₙ₊₁ = Tₙ ∪ Tₙ.Con`. Bundled with the
`Δ₁` witness because forming the next `.Con` needs it.
- [Lin97, §4, p. 55, the `Con(n, S)` tower]
- [AB05, §4.1, the `Tₙ` tower] -/
noncomputable def _root_.LO.FirstOrder.Theory.iterConSigma
    (T : ArithmeticTheory) [T.Δ₁] : ℕ → Σ' S : ArithmeticTheory, S.Δ₁
  | 0 => ⟨T, ‹_›⟩
  | n + 1 =>
    match T.iterConSigma n with
    | ⟨S, hS⟩ => letI := hS; ⟨S ∪ S.Con, inferInstance⟩

/-- The `n`-times iterated-consistency extension of `T`: `T₀ = T`, `Tₙ₊₁ = Tₙ ∪ Tₙ.Con`.
- [Lin97, §4, p. 55]
- [AB05, §4.1] -/
noncomputable def _root_.LO.FirstOrder.Theory.iterCon (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) :
    ArithmeticTheory := (T.iterConSigma n).1

noncomputable instance (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) : (T.iterCon n).Δ₁ :=
  (T.iterConSigma n).2

/-- Iterated consistency reduces to iterated provability of `⊥`: over `𝗜𝚺₁`, the formalized
consistency statement of the `n`-times iterated-consistency extension of `T` is equivalent to
`T`'s own provability predicate not proving `⊥` after `n + 1` applications.
- [Lin97, Lemma 4.2]
- [AB05, Lemma 21] -/
axiom provable_iterCon_iff_not_iterate_standardProvability_bot (n : ℕ) :
    𝗜𝚺₁ ⊢ (T.iterCon n).consistent.val 🡘 ∼(T.standardProvability^[n + 1] ⊥)

end LO.FirstOrder.Arithmetic
