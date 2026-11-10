module

public import AlphaCentauri.OmegaLogic.CutElimination.Elimination
public import AlphaCentauri.OmegaLogic.ExcludedMiddle.Sequent
public import AlphaCentauri.OmegaLogic.ExcludedMiddle.ValueCongruent
public import AlphaCentauri.OmegaLogic.OmegaCompleteness
public import AlphaCentauri.ToFoundation.FirstOrder.BinderNotation
public import AlphaCentauri.ToFoundation.FirstOrder.Fvar
public import AlphaCentauri.ToFoundation.FirstOrder.Rew
public import AlphaCentauri.ToFoundation.FirstOrder.Semiformula
public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.LK.Simplified

/-!
# Embedding `𝗣𝗔` into `Z_∞`

Every `𝗣𝗔` derivation embeds into `Z_∞` under a numeral assignment of its free variables, first
with bounded cut rank and then cut-free.

- [Tow20, Section 16]
- [Buc03, Section 5.5]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.OmegaLogic

variable {n : ℕ} {Γ : Sequent}

/-- The assignment sending each free variable `&x` to the numeral of `e x`.

- [Tow20, Section 16] -/
noncomputable def asg (e : ℕ → ℕ) : Rew ℒₒᵣ ℕ 0 ℕ 0 :=
  Rew.rewrite fun x => (↑(e x) : ArithmeticTerm ℕ)

/-- Closing after a shift re-indexes the assignment.

- [Tow20, Section 16] -/
lemma asg_comp_shift (e : ℕ → ℕ) : (asg e).comp Rew.shift = asg (e ∘ Nat.succ) := by
  ext x
  · exact x.elim0
  · simp [asg, Rew.comp_app]

lemma asg_image_shift (e : ℕ → ℕ) (Γ : Sequent) :
    (Γ.image Rewriting.shift).image (fun ψ => asg e ▹ ψ)
      = Γ.image (fun ψ => asg (e ∘ Nat.succ) ▹ ψ) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro ψ _
  change asg e ▹ (Rew.shift ▹ ψ) = asg (e ∘ Nat.succ) ▹ ψ
  rw [← TransitiveRewriting.comp_app, asg_comp_shift]

/-- Closing a freed variable with `m :>ₙ e` equals closing with `e` and substituting `m`.

- [Tow20, Section 16] -/
lemma asg_cons_free (m : ℕ) (e : ℕ → ℕ) (φ : ArithmeticSemiformula ℕ 1) :
    asg (m :>ₙ e) ▹ (Rewriting.free φ) = ((asg e).q ▹ φ)/[(↑m : ArithmeticTerm ℕ)] := by
  have h : (asg (m :>ₙ e)).comp Rew.free
      = (Rew.subst ![(↑m : ArithmeticTerm ℕ)]).comp (asg e).q := by
    ext x
    · refine Fin.cases ?_ (fun i => i.elim0) x
      simp [asg, Rew.comp_app]
    · simp [asg, Rew.comp_app]
  change asg (m :>ₙ e) ▹ (Rew.free ▹ φ) = Rew.subst ![(↑m : ArithmeticTerm ℕ)] ▹ ((asg e).q ▹ φ)
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, h]


namespace Provable

section ClosedWitness

variable {α : Ordinal.{0}} {c : ℕ}

/-- An arbitrary closed witness introduces an existential with cut rank at most `max c (ψ.qr + 1)`.

- [Tow20, Section 16] -/
lemma exI_closed (ψ : ArithmeticSemiformula ℕ 1) (s : ArithmeticTerm ℕ)
    (h : Z∞ ⊢[α, c] insert (ψ/[s]) Γ) :
    ∃ β, Z∞ ⊢[β, max c (ψ.qr + 1)] insert (∃¹ ψ) Γ := by
  set m := Semiterm.val (M := ℕ) ![] id s with hm
  have h₁ : Z∞ ⊢[α, max c (ψ.qr + 1)]
      insert (ψ/[s]) (insert (ψ/[(↑m : ArithmeticTerm ℕ)]) Γ) :=
    (h.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))).mono_cutRank
      (le_max_left _ _)
  obtain ⟨β, h₂⟩ := em_cong (↑m) s (by simp [hm]) ψ
    (Γ := insert (∼(ψ/[s])) (insert (ψ/[(↑m : ArithmeticTerm ℕ)]) Γ)) (by simp) (by simp)
  have hcut : ((ψ/[s]) : ArithmeticFormula ℕ).qr < max c (ψ.qr + 1) := by
    simp only [Semiformula.qr_substs]
    omega
  exact ⟨_, exI m (cut _ hcut h₁ (h₂.mono_cutRank (Nat.zero_le _)))⟩

end ClosedWitness

section Embedding

/-- Every `𝗣𝗔` derivation embeds into `Z_∞` under every numeral assignment of its free variables.

- [Tow20, Section 16]
- [Buc03, Section 5.5] -/
theorem of_derivation2 (d : 𝗣𝗔 ⟹₂ Γ) :
    ∃ c, ∀ e : ℕ → ℕ, ∃ α, Z∞ ⊢[α, c] (Γ.image fun φ => asg e ▹ φ) := by
  induction d with
  | closed Γ φ hp hn =>
    have h : ∀ e : ℕ → ℕ, ∼(asg e ▹ φ) ∈ Γ.image fun ψ => asg e ▹ ψ := fun e => by
      simpa using Finset.mem_image_of_mem (fun ψ => asg e ▹ ψ) hn
    exact ⟨0, fun e => ⟨_, lem (Finset.mem_image_of_mem _ hp) (h e)⟩⟩
  | axm φ hφ hΓ =>
    refine ⟨0, fun e => ⟨_, of_true ?_ (Finset.mem_image_of_mem _ hΓ)⟩⟩
    have hmod : (ℕ↓[ℒₒᵣ]) ⊧ φ := Semantics.modelsSet_iff.mp inferInstance hφ
    simp_all [LitTrue, asg, Semiformula.eval_emb, models_iff]
  | @verum Γ hΓ =>
    have h : ∀ e : ℕ → ℕ, (⊤ : ArithmeticFormula ℕ) ∈ Γ.image fun ψ => asg e ▹ ψ := fun e => by
      simpa using Finset.mem_image_of_mem (fun ψ => asg e ▹ ψ) hΓ
    exact ⟨0, fun e => ⟨0, verumR (h e)⟩⟩
  | @and Γ φ ψ hmem _ _ ih₁ ih₂ =>
    obtain ⟨c₁, ih₁⟩ := ih₁
    obtain ⟨c₂, ih₂⟩ := ih₂
    refine ⟨max c₁ c₂, ?_⟩
    intro e
    obtain ⟨α₁, h₁⟩ := ih₁ e
    obtain ⟨α₂, h₂⟩ := ih₂ e
    rw [Finset.image_insert] at h₁ h₂
    exact ⟨_, (andI (h₁.mono_cutRank (le_max_left _ _))
      (h₂.mono_cutRank (le_max_right _ _))).insert_absorb
      (by simpa using Finset.mem_image_of_mem (fun φ => asg e ▹ φ) hmem)⟩
  | @or Γ φ ψ hmem _ ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, ?_⟩
    intro e
    obtain ⟨α, h⟩ := ih e
    rw [Finset.image_insert, Finset.image_insert] at h
    exact ⟨_,
      h.orI.insert_absorb (by simpa using Finset.mem_image_of_mem (fun φ => asg e ▹ φ) hmem)⟩
  | @all Γ φ hmem _ ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, ?_⟩
    intro e
    have hfam : ∀ n : ℕ, ∃ α, Z∞ ⊢[α, c]
        insert (((asg e).q ▹ φ)/[(↑n : ArithmeticTerm ℕ)]) (Γ.image fun ψ => asg e ▹ ψ) := by
      intro n
      obtain ⟨α, h⟩ := ih (n :>ₙ e)
      rw [Finset.image_insert, asg_cons_free n e φ,
        asg_image_shift, show (n :>ₙ e) ∘ Nat.succ = e from rfl] at h
      exact ⟨α, h⟩
    choose βₓ hβ using hfam
    exact ⟨_, (allω hβ).insert_absorb
      (by simpa using Finset.mem_image_of_mem (fun ψ => asg e ▹ ψ) hmem)⟩
  | @exs Γ φ hmem t _ ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨max c (φ.qr + 1), ?_⟩
    intro e
    obtain ⟨α, h⟩ := ih e
    rw [Finset.image_insert, Rew.app_substs (asg e) φ t] at h
    obtain ⟨β, hβ⟩ := exI_closed ((asg e).q ▹ φ) (asg e t) h
    rw [show (((asg e).q ▹ φ).qr + 1) = (φ.qr + 1) by simp] at hβ
    exact ⟨_, hβ.insert_absorb (by simpa using Finset.mem_image_of_mem (fun ψ => asg e ▹ ψ) hmem)⟩
  | wk _ hsub ih =>
    obtain ⟨c, ih⟩ := ih
    exact ⟨c, fun e => (ih e).imp fun _ h => h.weakening (Finset.image_subset_image hsub)⟩
  | @shift Γ _ ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, ?_⟩
    intro e
    rw [asg_image_shift]
    exact ih (e ∘ Nat.succ)
  | @cut Γ φ _ _ ih₁ ih₂ =>
    obtain ⟨c₁, ih₁⟩ := ih₁
    obtain ⟨c₂, ih₂⟩ := ih₂
    refine ⟨max (φ.qr + 1) (max c₁ c₂), ?_⟩
    intro e
    obtain ⟨α₁, h₁⟩ := ih₁ e
    obtain ⟨α₂, h₂⟩ := ih₂ e
    rw [Finset.image_insert] at h₁ h₂
    rw [show (asg e ▹ (∼φ)) = ∼(asg e ▹ φ) by simp] at h₂
    exact ⟨_, cut (asg e ▹ φ) (by simp only [Semiformula.qr_rew]; omega)
      (h₁.mono_cutRank (by omega)) (h₂.mono_cutRank (by omega))⟩

/-- Every `𝗣𝗔` derivation embeds cut-free into `Z_∞` under a numeral assignment.

- [Tow20, Section 16] -/
theorem of_derivation2_cutFree (d : 𝗣𝗔 ⟹₂ Γ) (e : ℕ → ℕ) :
    ∃ α, Z∞ ⊢[α, 0] (Γ.image fun φ => asg e ▹ φ) := by
  obtain ⟨c, h⟩ := of_derivation2 d
  obtain ⟨α, hα⟩ := h e
  exact ⟨_, cut_elimination hα⟩

end Embedding

end Provable

end FFL.FirstOrder.Arithmetic.OmegaLogic
