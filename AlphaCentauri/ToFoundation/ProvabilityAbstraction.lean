module

public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Reflection
public import AlphaCentauri.ToFoundation.BooleanCombination

/-!
# Abstract provability: formalized consistency and Boolean combinations
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
theorem formalized_not_con_unrefutable : T₀ ⊢ 𝔅.con 🡒 ∼𝔅 (∼𝔅.con 🡒 ⊥) := by
  have h₁ : T₀ ⊢ 𝔅 (∼𝔅.con 🡒 ⊥) 🡒 𝔅 𝔅.con := mono' <| by cl_prover
  exact C_trans (formalized_con_unprovable 𝔅) (contra h₁)

section booleanCombination

variable {L : Language} {T₀ T : Theory L} {Γ : Sentence L → Prop}

/-- The conjunctions of clauses `∼C ⋎ D` with `C` and `D` in `Γ`. -/
private inductive ClauseConj (Γ : Sentence L → Prop) : Sentence L → Prop
  | clause {C D} : Γ C → Γ D → ClauseConj Γ (∼C ⋎ D)
  | and {φ ψ} : ClauseConj Γ φ → ClauseConj Γ ψ → ClauseConj Γ (φ ⋏ ψ)

variable
  (hand : ∀ σ τ, Γ σ → Γ τ → ∃ ρ, Γ ρ ∧ T₀ ⊢ ρ 🡘 σ ⋏ τ)
  (hor : ∀ σ τ, Γ σ → Γ τ → ∃ ρ, Γ ρ ∧ T₀ ⊢ ρ 🡘 σ ⋎ τ)
  (htop : ∃ ρ, Γ ρ ∧ T₀ ⊢ ρ) (hbot : ∃ ρ, Γ ρ ∧ T₀ ⊢ ∼ρ)

include hand hor in
private lemma ClauseConj.or_clause {C D : Sentence L} (hC : Γ C) (hD : Γ D) {φ : Sentence L}
    (hφ : ClauseConj Γ φ) : ∃ ψ, ClauseConj Γ ψ ∧ T₀ ⊢ ψ 🡘 φ ⋎ (∼C ⋎ D) := by
  induction hφ with
  | @clause C' D' hC' hD' =>
    obtain ⟨E, hE, hE'⟩ := hand C' C hC' hC
    obtain ⟨F, hF, hF'⟩ := hor D' D hD' hD
    exact ⟨∼E ⋎ F, .clause hE hF, by cl_prover [hE', hF']⟩
  | @and φ₁ φ₂ _ _ ih₁ ih₂ =>
    obtain ⟨ψ₁, h₁, e₁⟩ := ih₁
    obtain ⟨ψ₂, h₂, e₂⟩ := ih₂
    have e : T₀ ⊢ (φ₁ ⋎ (∼C ⋎ D)) ⋏ (φ₂ ⋎ (∼C ⋎ D)) 🡘 (φ₁ ⋏ φ₂) ⋎ (∼C ⋎ D) := by cl_prover
    exact ⟨ψ₁ ⋏ ψ₂, .and h₁ h₂, by cl_prover [e₁, e₂, e]⟩

include hand hor in
private lemma ClauseConj.or {φ ψ : Sentence L} (hφ : ClauseConj Γ φ) (hψ : ClauseConj Γ ψ) :
    ∃ χ, ClauseConj Γ χ ∧ T₀ ⊢ χ 🡘 φ ⋎ ψ := by
  induction hψ with
  | clause hC hD => exact ClauseConj.or_clause hand hor hC hD hφ
  | @and ψ₁ ψ₂ _ _ ih₁ ih₂ =>
    obtain ⟨χ₁, h₁, e₁⟩ := ih₁
    obtain ⟨χ₂, h₂, e₂⟩ := ih₂
    have e : T₀ ⊢ (φ ⋎ ψ₁) ⋏ (φ ⋎ ψ₂) 🡘 φ ⋎ (ψ₁ ⋏ ψ₂) := by cl_prover
    exact ⟨χ₁ ⋏ χ₂, .and h₁ h₂, by cl_prover [e₁, e₂, e]⟩

include hand hor htop hbot in
private lemma exists_clauseConj {φ : Sentence L} (hφ : BooleanCombination Γ φ) :
    ∃ ψ, ClauseConj Γ ψ ∧ T₀ ⊢ ψ 🡘 φ := by
  obtain ⟨t, ht, ht'⟩ := htop
  obtain ⟨b, hb, hb'⟩ := hbot
  induction hφ with
  | pos hC => exact ⟨_, .clause ht hC, by cl_prover [ht']⟩
  | neg hC => exact ⟨_, .clause hC hb, by cl_prover [hb']⟩
  | and _ _ ih₁ ih₂ =>
    obtain ⟨ψ₁, h₁, e₁⟩ := ih₁
    obtain ⟨ψ₂, h₂, e₂⟩ := ih₂
    exact ⟨ψ₁ ⋏ ψ₂, .and h₁ h₂, by cl_prover [e₁, e₂]⟩
  | or _ _ ih₁ ih₂ =>
    obtain ⟨ψ₁, h₁, e₁⟩ := ih₁
    obtain ⟨ψ₂, h₂, e₂⟩ := ih₂
    obtain ⟨χ, hχ, e⟩ := ClauseConj.or hand hor h₁ h₂
    exact ⟨χ, hχ, by cl_prover [e, e₁, e₂]⟩

variable [L.ReferenceableBy L] [T₀ ⪯ T] (𝔅 : Provability T₀ T) [𝔅.HBL2]

include hand hor htop hbot in
/-- Over local reflection for `Γ`, local reflection holds for every Boolean combination of `Γ`,
provided that `𝔅` is formalized complete on `Γ` and `Γ` is closed under `⋏` and `⋎` and contains
a provable and a refutable sentence, all up to provable equivalence in `T₀`.
- [Bek99, Lemma 4.3] -/
theorem provable_refl_of_booleanCombination
    (hc : ∀ σ, Γ σ → 𝔅.FormalizedCompleteOn σ) {φ : Sentence L}
    (hφ : BooleanCombination Γ φ) : T ∪ 𝔅.reflOn Γ ⊢ 𝔅.refl φ := by
  have : T₀ ⪯ T ∪ 𝔅.reflOn Γ := (inferInstance : T₀ ⪯ T).trans inferInstance
  have hext : ∀ {σ τ : Sentence L}, T₀ ⊢ σ 🡘 τ → T ∪ 𝔅.reflOn Γ ⊢ 𝔅.refl σ →
      T ∪ 𝔅.reflOn Γ ⊢ 𝔅.refl τ := fun {σ τ} h hσ ↦ by
    have h₁ : T ∪ 𝔅.reflOn Γ ⊢ 𝔅 τ 🡒 𝔅 σ :=
      WeakerThan.pbl (Provability.mono' (𝔅 := 𝔅) (K_right h))
    have h₂ : T ∪ 𝔅.reflOn Γ ⊢ σ 🡘 τ := WeakerThan.pbl h
    cl_prover [h₁, h₂, hσ]
  obtain ⟨ψ, hψ, e⟩ := exists_clauseConj hand hor htop hbot hφ
  apply hext e
  clear e
  induction hψ with
  | @clause C D hC hD =>
    have h₁ : T ∪ 𝔅.reflOn Γ ⊢ C 🡒 𝔅 C :=
      WeakerThan.pbl ((hc C hC).formalized_complete_on)
    have h₂ : T ∪ 𝔅.reflOn Γ ⊢ 𝔅 (∼C ⋎ D) 🡒 𝔅 C 🡒 𝔅 D :=
      WeakerThan.pbl (C_trans (Provability.mono' (𝔅 := 𝔅) (by cl_prover)) D2)
    have h₃ : T ∪ 𝔅.reflOn Γ ⊢ 𝔅.refl D :=
      Axiomatized.by_axm (Set.mem_union_right _ ((mem_localReflectionOn_iff 𝔅).mpr ⟨D, hD, rfl⟩))
    cl_prover [h₁, h₂, h₃]
  | @and φ ψ _ _ ih₁ ih₂ =>
    have h₁ : T ∪ 𝔅.reflOn Γ ⊢ 𝔅 (φ ⋏ ψ) 🡒 𝔅 φ :=
      WeakerThan.pbl (Provability.mono' (𝔅 := 𝔅) (by cl_prover))
    have h₂ : T ∪ 𝔅.reflOn Γ ⊢ 𝔅 (φ ⋏ ψ) 🡒 𝔅 ψ :=
      WeakerThan.pbl (Provability.mono' (𝔅 := 𝔅) (by cl_prover))
    cl_prover [h₁, h₂, ih₁, ih₂]

end booleanCombination

end FFL.FirstOrder.ProvabilityAbstraction
