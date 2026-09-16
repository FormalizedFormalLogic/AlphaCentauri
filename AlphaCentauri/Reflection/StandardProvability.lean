module

public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import AlphaCentauri.Reflection.ProvabilityAbstraction

@[expose] public section
/-!
# Local reflection principles for arithmetic theories

Local reflection schemas for arithmetic theories, together with consistency and iteration
results.

- [Lin97, §4.1, p. 52]
- [AB05, §4]
-/

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment ProvabilityAbstraction

/-- The local reflection schema `Rfn(T)` of an arithmetic theory `T`, via its standard
provability predicate.
- [Lin97, §4.1, p. 52]
- [AB05, §4] -/
abbrev _root_.FFL.FirstOrder.Theory.localReflection (T : ArithmeticTheory) [T.Δ₁] :
    ArithmeticTheory :=
  T.standardProvability.localReflection

@[inherit_doc] notation "𝗥𝗳𝗻 " T:max => Theory.localReflection T

/-- The local reflection schema of `T` restricted to the sentences satisfying `Γ`, `Rfn_Γ(T)`.
- [Lin97, §4.1, p. 52]
- [AB05, §4] -/
abbrev _root_.FFL.FirstOrder.Theory.localReflectionOn
    (T : ArithmeticTheory) [T.Δ₁] (Γ : ArithmeticSentence → Prop) : ArithmeticTheory :=
  T.standardProvability.localReflectionOn Γ

@[inherit_doc] notation "𝗥𝗳𝗻[" Γ "] " T:max => Theory.localReflectionOn T Γ

variable {T : ArithmeticTheory} [T.Δ₁]

/-- A consistent `T` is strictly weaker than `T ∪ Rfn(T)`.
- [Lin97, §4.1, p. 52] -/
@[instance] theorem strictlyWeakerThan_localReflection [𝗜𝚺₁ ⪯ T] [Consistent T] :
    T ⪱ T ∪ 𝗥𝗳𝗻 T :=
  StrictlyWeakerThan.of_unprovable_provable (φ := T.consistent)
    (consistent_unprovable T)
    (Provability.con_of_localReflection _ trivial)

/-- The $\Pi_1$ local reflection principle and `Con(T)` are equivalent over `T`.
- [Lin97, Exercise 4.1(b)(ii)]
- [AB05, Lemma 22(i)] -/
theorem localReflection_Pi1_equiv_con [𝗜𝚺₁ ⪯ T] : T ∪ 𝗥𝗳𝗻[Hierarchy 𝚷 1] T ≊ T ∪ T.Con := by
  have : 𝗜𝚺₁ ⪯ T ∪ T.Con :=
    (inferInstance : 𝗜𝚺₁ ⪯ T).trans (WeakerThan.ofSubset Set.subset_union_left)
  refine Equiv.antisymm ⟨?_, ?_⟩
  · apply WeakerThan.ofAxm!
    rintro φ (hφ | ⟨σ, hσ, rfl⟩)
    · exact by_axm (Set.mem_union_left _ hφ)
    · have : T.standardProvability.FormalizedCompleteOn (∼σ) :=
        ⟨provable_sigma_one_complete (by simpa using hσ.neg)⟩
      have h₁ : T ∪ T.Con ⊢ T.standardProvability.con 🡒 (T.standardProvability σ 🡒 σ) :=
        WeakerThan.pbl (Provability.localReflection_of_con T.standardProvability)
      have h₂ : T ∪ T.Con ⊢ T.standardProvability.con :=
        by_axm (Set.mem_union_right _ rfl)
      cl_prover [h₁, h₂]
  · apply WeakerThan.ofAxm!
    rintro φ (hφ | rfl)
    · exact by_axm (Set.mem_union_left _ hφ)
    · exact Provability.con_of_localReflection _ (by simp)

/-- The standard model satisfies every local reflection instance of a theory it satisfies.
- [Lin97, §4.1, p. 52] -/
instance models_localReflectionOn {Γ : ArithmeticSentence → Prop} [ℕ↓[ℒₒᵣ] ⊧* T] :
    ℕ↓[ℒₒᵣ] ⊧* (T ∪ 𝗥𝗳𝗻[Γ] T) := by
  apply Semantics.modelsSet_iff.mpr
  rintro φ (hφ | ⟨σ, _, rfl⟩)
  · exact Semantics.modelsSet_iff.mp inferInstance hφ
  · have : ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ → ℕ↓[ℒₒᵣ] ⊧ σ := fun h ↦
      models_of_provable inferInstance (T.standardProvability.sound_on h)
    simpa using this

/-- `T ∪ Rfn(T)` is consistent whenever `T` is sound in the standard model.
- [Lin97, §4.1, p. 52]
- [AB05, §4.2] -/
@[instance] theorem consistent_localReflection_of_sound [ℕ↓[ℒₒᵣ] ⊧* T] :
    Consistent (T ∪ 𝗥𝗳𝗻 T) := Theory.consistent_of_satisfiable ⟨ℕ↓[ℒₒᵣ], inferInstance⟩

section Sigma1Sound

variable [T.SoundOnHierarchy 𝚺 1]

private lemma unprovable_disj {s : Finset ArithmeticSentence} (hs : ∀ σ ∈ s, T ⊬ σ) :
    T ⊬ (⩖ σ ∈ s, T.standardProvability σ) := by
  intro h
  obtain ⟨σ, hσ, hmod⟩ : ∃ σ ∈ s, ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ := by
    simpa using T.soundOnHierarchy 𝚺 1 h (by simp [standardProvability_def])
  exact hs σ hσ (T.standardProvability.sound_on hmod)

/-- `T ∪ Rfn(T)` is consistent whenever `T` is $\Sigma_1$-sound.
- [Lin97, §4.1, p. 52]
- [AB05, §4.2] -/
@[instance] theorem consistent_localReflection_of_Sigma1_sound :
    Consistent (T ∪ 𝗥𝗳𝗻 T) := by
  classical
  apply Entailment.consistent_compact.mpr
  intro F hF hFfin
  -- The instances of `Rfn(T)` in the finite part `F` come from a finite set `t` of sentences.
  obtain ⟨t, -, htfin, ht⟩ :=
    Set.Finite.exists_subset_finite_image_eq (s := Set.univ) (u := F \ T)
      (f := T.standardProvability.localReflectionSchema) ((by simpa using hFfin : F.Finite).sdiff)
      fun ψ hψ ↦ (AdjunctiveSet.subset_iff.mp hF ψ hψ.1).resolve_left hψ.2
  -- Adjoining `∼Pr(σ)` for those `σ ∈ t` that `T` does not prove proves every instance in `F`.
  set s : Finset ArithmeticSentence := htfin.toFinset.filter fun σ ↦ T ⊬ σ
  set D : ArithmeticSentence := ⩖ σ ∈ s, T.standardProvability σ
  have hcon : Consistent (adjoin (∼D) T) :=
    unprovable_iff_consistent_adjoin.mp (unprovable_disj fun σ hσ ↦ (Finset.mem_filter.mp hσ).2)
  refine hcon.of_le (WeakerThan.ofAxm! ?_)
  intro ψ hψ
  by_cases hψT : ψ ∈ T
  · exact by_axm (by simp [hψT])
  obtain ⟨σ, hσt, rfl⟩ : ψ ∈ T.standardProvability.localReflectionSchema '' t := ht ▸ ⟨hψ, hψT⟩
  by_cases hσ : T ⊢ σ
  · have h₁ : adjoin (∼D) T ⊢ σ := Axiomatized.to_adjoin hσ
    cl_prover [h₁]
  · have h₁ : adjoin (∼D) T ⊢ T.standardProvability σ 🡒 D :=
      right_Fdisj'_intro _ _ (Finset.mem_filter.mpr ⟨htfin.mem_toFinset.mpr hσt, hσ⟩)
    have h₂ : adjoin (∼D) T ⊢ ∼D := Axiomatized.adjoin! _ _
    cl_prover [h₁, h₂]

end Sigma1Sound

section
variable [𝗜𝚺₁ ⪯ T] {Γ : Polarity} {n : ℕ} {π : ArithmeticSentence}

/-- Unboundedness, for an extension by a single sentence: if `T ∪ {π}` for a `Γ n` sentence `π`
proves the local reflection schema of `T` on the dual class, then `T ∪ {π}` is inconsistent.
- [AB05, Theorem 23]
- [AB05, Remark 24]
- [Lin97, Theorem 4.1] -/
theorem inconsistent_of_localReflectionOn_weakerThan_insert
    (hπ : Hierarchy Γ n π) (h : 𝗥𝗳𝗻[Hierarchy Γ.alt n] T ⪯ insert π T) :
    Inconsistent (insert π T) :=
  T.standardProvability.inconsistent_of_localReflectionOn_weakerThan_insert
    (fun _ hσ ↦ by simpa using hσ) hπ h

/-- Unboundedness, for an extension by a single sentence: a consistent `T ∪ {π}` with `π` a
`Γ n` sentence does not contain the local reflection schema of `T` on the dual class.
- [AB05, Theorem 23]
- [AB05, Remark 24]
- [Lin97, Theorem 4.1] -/
theorem not_localReflectionOn_weakerThan_insert
    (hπ : Hierarchy Γ n π) [Consistent (insert π T)] : ¬𝗥𝗳𝗻[Hierarchy Γ.alt n] T ⪯ insert π T :=
  fun h ↦ (inconsistent_of_localReflectionOn_weakerThan_insert hπ h).not_con
    inferInstance

/-- Unboundedness, for an extension by finitely many sentences: if `T ∪ U` for a finite set `U`
of `Γ n` sentences proves the local reflection schema of `T` on the dual class, then `T ∪ U` is
inconsistent.
- [AB05, Theorem 23]
- [AB05, Remark 24]
- [Lin97, Theorem 4.1] -/
theorem inconsistent_of_localReflectionOn_weakerThan_union_of_finite
    {U : ArithmeticTheory} (hU : U.Finite) (hΓ : ∀ σ ∈ U, Hierarchy Γ n σ)
    (h : 𝗥𝗳𝗻[Hierarchy Γ.alt n] T ⪯ T ∪ U) : Inconsistent (T ∪ U) := by
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
  exact (inconsistent_of_localReflectionOn_weakerThan_insert hconj
    (h.trans hle)).of_ge hge

end

/-- The pair of the iterated-consistency theory `T₀ = T`, `Tₙ₊₁ = Tₙ ∪ Tₙ.Con` and its
$\Delta_1$-definability witness.
- [Lin97, §4, p. 55, the `Con(n, S)` tower]
- [AB05, §4.1, the `Tₙ` tower] -/
noncomputable def _root_.FFL.FirstOrder.Theory.iterConSigma
    (T : ArithmeticTheory) [T.Δ₁] : ℕ → Σ' S : ArithmeticTheory, S.Δ₁
  | 0 => ⟨T, ‹_›⟩
  | n + 1 =>
    match T.iterConSigma n with
    | ⟨S, hS⟩ => letI := hS; ⟨S ∪ S.Con, inferInstance⟩

/-- The `n`-times iterated-consistency extension of `T`: `T₀ = T`, `Tₙ₊₁ = Tₙ ∪ Tₙ.Con`.
- [Lin97, §4, p. 55]
- [AB05, §4.1] -/
noncomputable def _root_.FFL.FirstOrder.Theory.iterCon (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) :
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

end FFL.FirstOrder.Arithmetic
