module

public import AlphaCentauri.InterpretabilityLogic.Veltman.StepByStep

/-!
# Completeness of $\mathbf{ILW}^*$ with respect to Veltman models

The step-by-step construction in which every world added to remove a deficiency of `A ▷ B` also
promises `□∼A` yields a Veltman model satisfying the frame conditions of $\mathsf{W}$ and
$\mathsf{M}_0$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula Logic Logic.ofAxioms MaximalConsistentTheory

namespace Veltman.StepByStep

variable {α : Type*} [DecidableEq α] {𝔸 : Set (Formula α)}
  {Γ₀ : MaximalConsistentTheory (ofAxioms 𝔸)} {ε : Formula α → Set (Formula α)} {τ : ℕ → Job α}
  {Ω : Finset (Formula α)}

local notation "𝒩" => node Γ₀ ε τ

variable (hτ : ∀ n, (τ n).Mem Ω) (hε : ∀ A, □(∼A) ∈ ε A)

include hτ hε in
lemma exists_box_neg_mem_extra {n w s r : ℕ} {A : Formula α} (hk : (𝒩 n).kind = .deficiency w s A)
    (hr : (𝒩 n).mu w = r) : ∃ C ∈ Ω, □(∼C) ∈ (𝒩 n).extra w ∧ □(∼C) ∉ (𝒩 r).set := by
  induction n using Nat.strong_induction_on generalizing s r A with
  | _ n ih =>
  have hs := kind_spec (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  rw [hk] at hs;
  obtain ⟨-, hsn, hws, B, hτn, -, hA, -⟩ := hs;
  obtain ⟨-, -, hmu, -, hextra⟩ := fields_deficiency hk;
  rw [hmu, ite_eq_left rfl] at hr;
  rw [hextra, ite_eq_left rfl];
  by_cases hau : (𝒩 s).kind.anchor = w;
  · rcases hks : (𝒩 s).kind with _ | ⟨b, B'⟩ | ⟨b, s', A'⟩ <;> rw [hks] at hau <;>
      simp only [Kind.anchor] at hau;
    · simp at hau;
    · obtain rfl : b = w := WithBot.coe_injective hau;
      rw [(fields_problem hks).2.2.1, ite_eq_left rfl] at hr;
      simp at hr;
    · obtain rfl : b = w := WithBot.coe_injective hau;
      obtain ⟨C, hC, hCextra, hCr⟩ := ih s hsn hks hr;
      exact ⟨C, hC, .inl hCextra, hCr⟩;
  · have hrs : r ∈ (𝒩 s).pre :=
      (Finset.mem_filter.mp (Finset.mem_of_max ((mu_of_anchor_ne hau).symm.trans hr))).1;
    have hΩ : A ∈ Ω := by
      have := hτ n;
      rw [hτn] at this;
      exact this.1;
    refine ⟨A, hΩ, .inr (hε A), fun h ↦ ?_⟩;
    exact not_mem_of_neg_mem ((successor_of_mem_pre hrs).box_mem_of_box_mem h).1 hA

include hτ hε in
lemma boxedNeg_ssubset_of_reflTransGen {w x y z : ℕ} (hwx : w ∈ (𝒩 x).pre) (hxy : x ∈ (𝒩 y).pre)
    (hwz : w ∈ (𝒩 z).pre) (h : Relation.ReflTransGen (Step (Γ₀ := Γ₀) (ε := ε) (τ := τ) w) y z) :
    boxedNeg Γ₀ ε τ Ω x ⊂ boxedNeg Γ₀ ε τ Ω z := by
  classical
  obtain ⟨r, hr, hxr⟩ := exists_mu_of_reflTransGen hwx hxy h;
  have hsub {p q : ℕ} (hpq : p ∈ (𝒩 q).anc) : boxedNeg Γ₀ ε τ Ω p ⊆ boxedNeg Γ₀ ε τ Ω q := by
    intro C hC;
    obtain ⟨hC₁, hC₂⟩ := Finset.mem_filter.mp hC;
    exact Finset.mem_filter.mpr ⟨hC₁, box_mem_of_mem_anc hpq hC₂⟩;
  apply (hsub hxr).trans_ssubset;
  by_cases hau : (𝒩 z).kind.anchor = w;
  · rcases hk : (𝒩 z).kind with _ | ⟨b, B⟩ | ⟨b, s, A⟩ <;> rw [hk] at hau <;>
      simp only [Kind.anchor] at hau;
    · simp at hau;
    · obtain rfl : b = w := WithBot.coe_injective hau;
      rw [(fields_problem hk).2.2.1, ite_eq_left rfl] at hr;
      simp at hr;
    · obtain rfl : b = w := WithBot.coe_injective hau;
      obtain ⟨C, hC, hCextra, hCr⟩ := exists_box_neg_mem_extra hτ hε hk hr;
      refine (Finset.ssubset_iff_of_subset (hsub (mu_spec hwz hr).2)).mpr
        ⟨C, Finset.mem_filter.mpr ⟨hC, ?_⟩, fun hm ↦ hCr (Finset.mem_filter.mp hm).2⟩;
      apply (assuring_anchor_deficiency hk).subset;
      rw [(fields_deficiency hk).2.2.2.2, ite_eq_left rfl] at hCextra;
      rcases hCextra with hCextra | hCextra;
      · exact .inl (.inl (.inr hCextra));
      · exact .inr hCextra;
  · have hrz : r ∈ (𝒩 z).pre :=
      (Finset.mem_filter.mp (Finset.mem_of_max ((mu_of_anchor_ne hau).symm.trans hr))).1;
    exact boxedNeg_ssubset hτ hrz

include hτ hε in
lemma model_hasW : (model Γ₀ ε τ).HasW where
  cwf_rel_comp_s w := by
    classical
    have key (z : ℕ) (hwz : w ∈ (𝒩 z).pre) :
        Acc (flip (Relation.Comp (model Γ₀ ε τ).Rel ((model Γ₀ ε τ).S w))) z := by
      induction h : Ω.card - (boxedNeg Γ₀ ε τ Ω z).card using Nat.strong_induction_on
        generalizing z with
      | _ m ih =>
      constructor;
      rintro z' ⟨y, hzy, hyz'⟩;
      have h₁ := Finset.card_lt_card
        (boxedNeg_ssubset_of_reflTransGen hτ hε hwz hzy hyz'.2.1 hyz'.2.2);
      have h₂ : (boxedNeg Γ₀ ε τ Ω z').card ≤ Ω.card :=
        Finset.card_le_card (Finset.filter_subset _ Ω);
      exact ih _ (by omega) z' hyz'.2.1 rfl;
    constructor;
    intro x;
    constructor;
    rintro z ⟨y, -, hyz⟩;
    exact key z hyz.2.1

end Veltman.StepByStep

namespace Logic.ILWStar

open Veltman Veltman.StepByStep

variable {α : Type*} {A : Formula α}

/-- - [GJ08, Theorem 7.1] -/
theorem complete
    (h : ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsIL] → [M.HasW] → [M.HasM₀] → M ⊧ A) :
    𝐈𝐋𝐖* ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ₀, hΓ₀⟩ := exists_not_forces (ε := fun A ↦ {□(∼A)}) axiomM₀
    (fun h hAB hA ↦ h.exists_of_rhd_mem_of_axiomW axiomW hAB hA) hA;
  have hτ := enumJob_mem (bot_mem_jobFormulas (A := A));
  have := model_isIL (Γ₀ := Γ₀) (ε := fun A ↦ {□(∼A)}) hτ;
  have := model_hasW (Γ₀ := Γ₀) (ε := fun A ↦ {□(∼A)}) hτ fun _ ↦ Set.mem_singleton _;
  exact hΓ₀ (h _ 0)

end Logic.ILWStar

end FFL.InterpretabilityLogic

end
