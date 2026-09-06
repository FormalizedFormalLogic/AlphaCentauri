module

public import Foundation.FirstOrder.Incompleteness.Second
public import AlphaCentauri.Hierarchy.Prenex
public import AlphaCentauri.Reflection.ProvabilityAbstraction

@[expose] public section
/-!
# Local and uniform reflection principles for arithmetic theories

Local and uniform reflection schemas for arithmetic theories, together with consistency and
iteration results.

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

variable {T : ArithmeticTheory} [T.Δ₁]

/-- A consistent `T` is strictly weaker than `T ∪ Rfn(T)`.
- [Lin97, §4.1, p. 52] -/
@[instance] axiom strictlyWeakerThan_localReflection [Consistent T] : T ⪱ T ∪ 𝗥𝗳𝗻 T

/-- `Rfn_{𝚷-[1]}(T)` and `Con(T)` are equivalent over `T`.
- [Lin97, Exercise 4.1(b)(ii)]
- [AB05, Lemma 22(i)] -/
axiom localReflection_pi_one_equiv_con : T ∪ 𝗥𝗳𝗻[𝚷 1] T ≊ T ∪ T.Con

/-- `T ∪ Rfn(T)` is consistent whenever `T` is sound in the standard model.
- [Lin97, §4.1, p. 52]
- [AB05, §4.2] -/
@[instance] axiom consistent_localReflection_of_sound [ℕ↓[ℒₒᵣ] ⊧* T] :
    Consistent (T ∪ 𝗥𝗳𝗻 T)

/-- `T ∪ Rfn(T)` is consistent whenever `T` is `𝚺-[1]`-sound.
- [Lin97, §4.1, p. 52]
- [AB05, §4.2] -/
@[instance] axiom consistent_localReflection_of_sigma_one_sound [T.SoundOnHierarchy 𝚺 1] :
    Consistent (T ∪ 𝗥𝗳𝗻 T)

section
variable [𝗜𝚺₁ ⪯ T] {Γ : Polarity} {n : ℕ} {π : ArithmeticSentence}

/-- Unboundedness, for an extension by a single sentence: if `T ∪ {π}` for a `Γ n` sentence `π`
proves the local reflection schema of `T` on the dual class, then `T ∪ {π}` is inconsistent.
- [AB05, Theorem 23]
- [AB05, Remark 24]
- [Lin97, Theorem 4.1] -/
theorem inconsistent_of_localReflectionOnHierarchy_weakerThan_insert
    (hπ : Hierarchy Γ n π) (h : 𝗥𝗳𝗻[Γ.alt n] T ⪯ insert π T) : Inconsistent (insert π T) :=
  T.standardProvability.inconsistent_of_localReflectionOn_weakerThan_insert
    (fun _ hσ ↦ by simpa using hσ) hπ h

/-- Unboundedness, for an extension by a single sentence: a consistent `T ∪ {π}` with `π` a
`Γ n` sentence does not contain the local reflection schema of `T` on the dual class.
- [AB05, Theorem 23]
- [AB05, Remark 24]
- [Lin97, Theorem 4.1] -/
theorem not_localReflectionOnHierarchy_weakerThan_insert
    (hπ : Hierarchy Γ n π) [Consistent (insert π T)] : ¬𝗥𝗳𝗻[Γ.alt n] T ⪯ insert π T :=
  fun h ↦ (inconsistent_of_localReflectionOnHierarchy_weakerThan_insert hπ h).not_con
    inferInstance

/-- Unboundedness, for an extension by finitely many sentences: if `T ∪ U` for a finite set `U`
of `Γ n` sentences proves the local reflection schema of `T` on the dual class, then `T ∪ U` is
inconsistent.
- [AB05, Theorem 23]
- [AB05, Remark 24]
- [Lin97, Theorem 4.1] -/
theorem inconsistent_of_localReflectionOnHierarchy_weakerThan_union_of_finite
    {U : ArithmeticTheory} (hU : U.Finite) (hΓ : ∀ σ ∈ U, Hierarchy Γ n σ)
    (h : 𝗥𝗳𝗻[Γ.alt n] T ⪯ T ∪ U) : Inconsistent (T ∪ U) := by
  classical
  have hmem : ∀ σ, σ ∈ hU.toFinset.toList ↔ σ ∈ U := by simp
  have hconj : Hierarchy Γ n (⋀hU.toFinset.toList) :=
    Hierarchy.list_conj₂_iff.mpr fun σ hσ ↦ hΓ σ ((hmem σ).mp hσ)
  have hle : T ∪ U ⪯ insert (⋀hU.toFinset.toList) T := WeakerThan.ofAxm! <| by
    rintro φ (hφ | hφ)
    · exact by_axm (Set.mem_insert_of_mem _ hφ)
    · exact mdp (left_Conj₂_intro ((hmem φ).mpr hφ)) (by_axm (Set.mem_insert _ _))
  have hge : insert (⋀hU.toFinset.toList) T ⪯ T ∪ U := WeakerThan.ofAxm! <| by
    rintro φ (rfl | hφ)
    · exact Conj₂_iff_forall_provable.mpr fun ψ hψ ↦ by_axm (Or.inr ((hmem ψ).mp hψ))
    · exact by_axm (Or.inl hφ)
  exact (inconsistent_of_localReflectionOnHierarchy_weakerThan_insert hconj
    (h.trans hle)).of_ge hge

end

/-- The uniform reflection schema `RFN_Γ(T)` consists of
`∀x (Pr_T(φ(ẋ)) → φ(x))` for one-free-variable formulas `φ` satisfying `Γ`.
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

/-- `RFN_{𝚺-[n]}(T)` and `RFN_{𝚷-[n + 1]}(T)` are equivalent over `T`, for `n ≥ 1`.
- [AB05, Lemma 22(ii)] -/
axiom uniformReflectionOnHierarchy_sigma_equiv_pi_succ {n : ℕ} (hn : 1 ≤ n) :
    T ∪ 𝗥𝗙𝗡[𝚺 n] T ≊ T ∪ 𝗥𝗙𝗡[𝚷 (n + 1)] T

/-- The pair of the iterated-consistency theory `T₀ = T`, `Tₙ₊₁ = Tₙ ∪ Tₙ.Con` and its
`Δ₁`-definability witness.
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
