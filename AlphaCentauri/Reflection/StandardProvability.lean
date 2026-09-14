module

public import Foundation.FirstOrder.Incompleteness.Second
public import AlphaCentauri.Hierarchy.StrictHierarchy
public import AlphaCentauri.Reflection.ProvabilityAbstraction
public import AlphaCentauri.Vorspiel.Adjoin

@[expose] public section
/-!
# Local and uniform reflection principles for arithmetic theories

Local and uniform reflection schemas for arithmetic theories, together with consistency and
iteration results.

- [Lin97, §4.1, p. 52]
- [AB05, §4]
-/

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment ProvabilityAbstraction

/-- The local reflection schema `Rfn(T)` of an arithmetic theory `T`, via its standard
provability predicate.
- [Lin97, §4.1, p. 52]
- [AB05, §4] -/
abbrev _root_.FFL.FirstOrder.Theory.localReflection (T : ArithmeticTheory) [T.Δ₁] : ArithmeticTheory :=
  T.standardProvability.localReflection

@[inherit_doc] notation "𝗥𝗳𝗻 " T:max => Theory.localReflection T

/-- The local reflection schema of `T` restricted to the `Γ n` sentences of the arithmetical
hierarchy, `Rfn_{Γ n}(T)`.
- [Lin97, §4.1, p. 52]
- [AB05, §4] -/
abbrev _root_.FFL.FirstOrder.Theory.localReflectionOnHierarchy
    (T : ArithmeticTheory) [T.Δ₁] (Γ : Polarity) (n : ℕ) : ArithmeticTheory :=
  T.standardProvability.localReflectionOn (Hierarchy Γ n)

@[inherit_doc] notation "𝗥𝗳𝗻[" Γ:max n:max "] " T:max => Theory.localReflectionOnHierarchy T Γ n

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
theorem localReflection_Pi1_equiv_con [𝗜𝚺₁ ⪯ T] : T ∪ 𝗥𝗳𝗻[𝚷 1] T ≊ T ∪ T.Con := by
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
    ℕ↓[ℒₒᵣ] ⊧* (T ∪ T.standardProvability.localReflectionOn Γ) := by
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

private lemma models_map_disj {g : ArithmeticSentence → ArithmeticSentence} :
    ∀ {l : List ArithmeticSentence},
      ℕ↓[ℒₒᵣ] ⊧ (l.map g).disj ↔ ∃ σ ∈ l, ℕ↓[ℒₒᵣ] ⊧ g σ
  | [] => by simp
  | _ :: l => by simp [models_map_disj (g := g) (l := l)]

private lemma hierarchy_map_disj {g : ArithmeticSentence → ArithmeticSentence}
    (hg : ∀ σ, Hierarchy 𝚺 1 (g σ)) :
    ∀ {l : List ArithmeticSentence}, Hierarchy 𝚺 1 (l.map g).disj
  | [] => by simp
  | _ :: l => by simp [hg, hierarchy_map_disj hg (l := l)]

/-- `T` proves no disjunction of provability statements for sentences it does not prove: the
disjunction is $\Sigma_1$ and false in the standard model. -/
private lemma unprovable_map_disj {l : List ArithmeticSentence} (hl : ∀ σ ∈ l, T ⊬ σ) :
    T ⊬ (l.map T.standardProvability).disj := by
  intro h
  obtain ⟨σ, hσ, hmod⟩ :=
    models_map_disj.mp
      (T.soundOnHierarchy 𝚺 1 h (hierarchy_map_disj (by intro _; simp [standardProvability_def])))
  exact hl σ hσ (T.standardProvability.sound_on hmod)

/-- `T ∪ Rfn(T)` is consistent whenever `T` is $\Sigma_1$-sound.
- [Lin97, §4.1, p. 52]
- [AB05, §4.2] -/
@[instance] theorem consistent_localReflection_of_Sigma1_sound :
    Consistent (T ∪ 𝗥𝗳𝗻 T) := by
  -- Adjoining `∼Pr(σ)` for every `σ` that `T` does not prove already proves `Rfn(T)`.
  set X : ArithmeticTheory := {ψ | ∃ σ, T ⊬ σ ∧ ψ = ∼(T.standardProvability σ)}
  have hTX : T ⪯ T ∪ X := WeakerThan.ofSubset Set.subset_union_left
  have hle : T ∪ 𝗥𝗳𝗻 T ⪯ T ∪ X := by
    apply WeakerThan.ofAxm!
    rintro φ (hφ | ⟨σ, -, rfl⟩)
    · exact by_axm (Set.mem_union_left _ hφ)
    · by_cases hσ : T ⊢ σ
      · have h₁ : T ∪ X ⊢ σ := WeakerThan.pbl hσ
        cl_prover [h₁]
      · have h₁ : T ∪ X ⊢ ∼(T.standardProvability σ) :=
          by_axm (Set.mem_union_right _ ⟨σ, hσ, rfl⟩)
        cl_prover [h₁]
  -- `T ∪ X` is consistent: each of its finite parts sits inside `T` with finitely many `∼Pr(σ)`
  -- adjoined, which `unprovable_map_disj` keeps consistent.
  have hcon : Consistent (T ∪ X) := by
    apply Entailment.consistent_compact.mpr
    intro F hsub hfin
    have hFfin : (F : Set ArithmeticSentence).Finite := by simpa using hfin
    classical
    have hmemX : ∀ ψ ∈ F \ T, ψ ∈ X := by
      intro ψ hψ
      rcases AdjunctiveSet.subset_iff.mp hsub ψ hψ.1 with h | h
      · exact absurd h hψ.2
      · exact h
    have hchoice : ∀ ψ : ArithmeticSentence,
        ∃ σ, ψ ∈ X → T ⊬ σ ∧ ψ = ∼(T.standardProvability σ) := by
      intro ψ
      by_cases h : ψ ∈ X
      · obtain ⟨σ, hσ⟩ := h
        exact ⟨σ, fun _ ↦ hσ⟩
      · exact ⟨⊥, fun h' ↦ absurd h' h⟩
    choose pick hpick using hchoice
    have hFT : (F \ T : Set ArithmeticSentence).Finite := hFfin.subset Set.sdiff_subset
    let l : List ArithmeticSentence := (hFT.toFinset.image pick).toList
    have hl : ∀ σ ∈ l, T ⊬ σ := by
      intro σ hσ
      simp only [l, Finset.mem_toList, Finset.mem_image, Set.Finite.mem_toFinset] at hσ
      obtain ⟨ψ, hψ, rfl⟩ := hσ
      exact (hpick ψ (hmemX ψ hψ)).1
    refine Entailment.Consistent.of_subset (consistent_adjoinNegs (unprovable_map_disj hl)) ?_
    intro ψ hψ
    by_cases h : ψ ∈ T
    · simp [h]
    · obtain ⟨-, he⟩ := hpick ψ (hmemX ψ ⟨hψ, h⟩)
      refine mem_adjoinNegs.mpr (Or.inl ⟨T.standardProvability (pick ψ), ?_, he⟩)
      simp only [l, List.mem_map, Finset.mem_toList, Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨pick ψ, ⟨ψ, ⟨hψ, h⟩, rfl⟩, rfl⟩
  exact hcon.of_le hle

end Sigma1Sound

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
def _root_.FFL.FirstOrder.Theory.uniformReflectionOn
    (T : ArithmeticTheory) [T.Δ₁] (Γ : ArithmeticSemisentence 1 → Prop) : ArithmeticTheory :=
  { ψ | ∃ φ : ArithmeticSemisentence 1, Γ φ ∧
      ψ = (“∀ x, ∀ y, !Bootstrapping.Arithmetic.ssnum y ↑(Encodable.encode φ) x →
        (!(T.standardProvability.prov) y → !φ x)” : ArithmeticSentence) }

/-- The uniform reflection schema of `T` restricted to the `Γ n` formulas of the arithmetical
hierarchy, `RFN_{Γ n}(T)`.
- [Lin97, §4.1, p. 52]
- [AB05, §4.2] -/
abbrev _root_.FFL.FirstOrder.Theory.uniformReflectionOnHierarchy
    (T : ArithmeticTheory) [T.Δ₁] (Γ : Polarity) (n : ℕ) : ArithmeticTheory :=
  T.uniformReflectionOn (Hierarchy Γ n)

@[inherit_doc] notation "𝗥𝗙𝗡[" Γ:max n:max "] " T:max => Theory.uniformReflectionOnHierarchy T Γ n

/-- `RFN_{𝚺-[n]}(T)` and `RFN_{𝚷-[n + 1]}(T)` are equivalent over `T`, for `n ≥ 1`.
- [AB05, Lemma 22(ii)] -/
axiom uniformReflectionOnHierarchy_sigma_equiv_pi_succ {n : ℕ} (hn : 1 ≤ n) :
    T ∪ 𝗥𝗙𝗡[𝚺 n] T ≊ T ∪ 𝗥𝗙𝗡[𝚷 (n + 1)] T

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
