module

public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy

/-!
# Prenex normal form

Every formula is equivalent, in every nonempty structure, to a prenex formula of either polarity
and of every large enough level.
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding

universe u

variable {L : Language} {ℬ : Bounding L} {ξ : Type*} {n : ℕ}

variable (ℬ) in
/-- `φ` is equivalent, in every nonempty structure, to a `ℬ`-prenex formula of either polarity and
of every large enough level. -/
private def HasPrenexNormalForm (φ : Semiformula L ξ n) : Prop :=
  ∃ s, ∀ Γ s', s ≤ s' → ∃ ψ, ℬ.PrenexHierarchy Γ s' ψ ∧
    ∀ (M : Type u) [Tarski.Structure L M] [Nonempty M] (e : Fin n → M) (f : ξ → M),
      Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ

namespace HasPrenexNormalForm

private lemma of_iff {φ ψ : Semiformula L ξ n} (h : HasPrenexNormalForm.{u} ℬ ψ)
    (H : ∀ (M : Type u) [Tarski.Structure L M] [Nonempty M] (e : Fin n → M) (f : ξ → M),
      Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ) :
    HasPrenexNormalForm.{u} ℬ φ := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, fun Γ s' hs' ↦ (hs Γ s' hs').imp fun _ hχ ↦
    ⟨hχ.1, fun M _ _ e f ↦ (H M e f).trans (hχ.2 M e f)⟩⟩

private lemma of_prenexHierarchy {Γ : Polarity} {s : ℕ} {φ : Semiformula L ξ n}
    (h : ℬ.PrenexHierarchy Γ s φ) : HasPrenexNormalForm.{u} ℬ φ :=
  ⟨s + 1, fun Γ' _ hs ↦ h.exists_eval_iff_of_lt Γ' hs⟩

private lemma of_closure {φ : Semiformula L ξ n} (h : ℬ.Closure φ) : HasPrenexNormalForm.{u} ℬ φ :=
  of_prenexHierarchy (Γ := 𝚺) (PrenexHierarchy.zero_iff_bounded.mpr h)

private lemma neg {φ : Semiformula L ξ n} (h : HasPrenexNormalForm.{u} ℬ φ) :
    HasPrenexNormalForm.{u} ℬ (∼φ) := by
  obtain ⟨s, hs⟩ := h
  use s
  intro Γ s' hs'
  obtain ⟨ψ, hψ, H⟩ := hs Γ.alt s' hs'
  exact ⟨∼ψ, by simpa using hψ.neg, fun M _ _ e f ↦ by simp [H M e f]⟩

private lemma all {φ : Semiformula L ξ (n + 1)} (h : HasPrenexNormalForm.{u} ℬ φ) :
    HasPrenexNormalForm.{u} ℬ (∀¹ φ) := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨ψ, hψ, H⟩ := hs 𝚺 s le_rfl
  exact (of_prenexHierarchy hψ.all).of_iff fun M _ _ e f ↦ by simp [H M]

private lemma exs {φ : Semiformula L ξ (n + 1)} (h : HasPrenexNormalForm.{u} ℬ φ) :
    HasPrenexNormalForm.{u} ℬ (∃¹ φ) := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨ψ, hψ, H⟩ := hs 𝚷 s le_rfl
  exact (of_prenexHierarchy hψ.exs).of_iff fun M _ _ e f ↦ by simp [H M]

private lemma and_of_prenexHierarchy : {Γ₁ Γ₂ : Polarity} → {s₁ s₂ n : ℕ} →
    {ψ₁ ψ₂ : Semiformula L ξ n} → ℬ.PrenexHierarchy Γ₁ s₁ ψ₁ → ℬ.PrenexHierarchy Γ₂ s₂ ψ₂ →
    HasPrenexNormalForm.{u} ℬ (ψ₁ ⋏ ψ₂)
  | _, _, 0, 0, _, _, _, h₁, h₂ =>
    of_closure <| .and (PrenexHierarchy.zero_iff_bounded.mp h₁)
      (PrenexHierarchy.zero_iff_bounded.mp h₂)
  | 𝚺, _, _ + 1, _, _, _, _, h₁, h₂ => by
    obtain ⟨χ, hχ, rfl⟩ := PrenexHierarchy.sigma_succ_iff.mp h₁
    exact (and_of_prenexHierarchy hχ (h₂.rew Rew.bShift)).exs.of_iff fun M _ _ e f ↦ by simp
  | 𝚷, _, _ + 1, _, _, _, _, h₁, h₂ => by
    obtain ⟨χ, hχ, rfl⟩ := PrenexHierarchy.pi_succ_iff.mp h₁
    exact (and_of_prenexHierarchy hχ (h₂.rew Rew.bShift)).all.of_iff fun M _ _ e f ↦ by
      simp [forall_and_right]
  | _, 𝚺, 0, _ + 1, _, _, _, h₁, h₂ => by
    obtain ⟨χ, hχ, rfl⟩ := PrenexHierarchy.sigma_succ_iff.mp h₂
    exact (and_of_prenexHierarchy (h₁.rew Rew.bShift) hχ).exs.of_iff fun M _ _ e f ↦ by simp
  | _, 𝚷, 0, _ + 1, _, _, _, h₁, h₂ => by
    obtain ⟨χ, hχ, rfl⟩ := PrenexHierarchy.pi_succ_iff.mp h₂
    exact (and_of_prenexHierarchy (h₁.rew Rew.bShift) hχ).all.of_iff fun M _ _ e f ↦ by
      simp [forall_and_left]
termination_by _ _ s₁ s₂ => s₁ + s₂

private lemma and {φ₁ φ₂ : Semiformula L ξ n} (h₁ : HasPrenexNormalForm.{u} ℬ φ₁)
    (h₂ : HasPrenexNormalForm.{u} ℬ φ₂) : HasPrenexNormalForm.{u} ℬ (φ₁ ⋏ φ₂) := by
  obtain ⟨s₁, hs₁⟩ := h₁
  obtain ⟨s₂, hs₂⟩ := h₂
  obtain ⟨ψ₁, hψ₁, H₁⟩ := hs₁ 𝚺 s₁ le_rfl
  obtain ⟨ψ₂, hψ₂, H₂⟩ := hs₂ 𝚺 s₂ le_rfl
  exact (and_of_prenexHierarchy hψ₁ hψ₂).of_iff fun M _ _ e f ↦ by simp [H₁ M, H₂ M]

end HasPrenexNormalForm

private lemma hasPrenexNormalForm (φ : Semiformula L ξ n) : HasPrenexNormalForm.{u} ℬ φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact .of_closure (.verum _)
  | hfalsum => exact .of_closure (.falsum _)
  | hrel r v => exact .of_closure (.rel r v)
  | hnrel r v => exact .of_closure (.nrel r v)
  | hand _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | hor _ _ ih₁ ih₂ => simpa using (ih₁.neg.and ih₂.neg).neg
  | hall _ ih => exact ih.all
  | hexs _ ih => exact ih.exs

variable (ℬ) in
/-- Every formula is equivalent, in every nonempty structure, to a `ℬ`-prenex formula of either
polarity and of every large enough level.
- [HP98, p. 8] -/
theorem exists_prenexHierarchy_eval_iff (φ : Semiformula L ξ n) :
    ∃ s, ∀ Γ s', s ≤ s' → ∃ ψ, ℬ.PrenexHierarchy Γ s' ψ ∧
      ∀ (M : Type u) [Tarski.Structure L M] [Nonempty M] (e : Fin n → M) (f : ξ → M),
        Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ :=
  hasPrenexNormalForm φ

end FFL.FirstOrder.Bounding
