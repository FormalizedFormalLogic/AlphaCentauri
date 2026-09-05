module

public import AlphaCentauri.OmegaLogic.Inversion
public import AlphaCentauri.Vorspiel.Ordinal

/-!
# Cut reduction for `Z_∞`

This file defines cut reducibility below `ω ^ θ` and proves it for each form of cut formula.

Neither [HP98] nor [Lin97] treats ω-logic; the presentation followed is [Tow20].
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.OmegaLogic

open scoped Ordinal

variable {θ α β : Ordinal.{0}} {c k : ℕ} {φ ψ : ArithmeticFormula ℕ}
  {φₓ : ArithmeticSemiformula ℕ 1} {Γ Δ : Sequent}

section Frame

/-! ### Moving an `insert` across an `erase`

Subset relations for moving insertion across erasure and union. -/

private lemma eraseIn (a e : ArithmeticFormula ℕ) (s : Sequent) :
    (insert a s).erase e ⊆ insert a (s.erase e) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  tauto

private lemma eraseOut {a e : ArithmeticFormula ℕ} (h : a ≠ e) (s : Sequent) :
    insert a (s.erase e) ⊆ (insert a s).erase e := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx <;> tauto

private lemma frameIn (a e : ArithmeticFormula ℕ) (s t : Sequent) :
    (insert a s).erase e ∪ t ⊆ insert a (s.erase e ∪ t) := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
  tauto

private lemma frameOut {a e : ArithmeticFormula ℕ} (h : a ≠ e) (s t : Sequent) :
    insert a (s.erase e ∪ t) ⊆ (insert a s).erase e ∪ t := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
  rcases hx with rfl | hx <;> tauto

end Frame

/-- A cut formula is reducible below `ω ^ θ` at rank `c` when cutting two bounded derivations on it
produces another derivation with the same bounds.

- [Tow20, Section 19.5] -/
def CutReducible (θ : Ordinal.{0}) (c : ℕ) (φ : ArithmeticFormula ℕ) : Prop :=
  ∀ {Γ : Sequent} {γ δ : Ordinal.{0}}, γ < ω ^ θ → δ < ω ^ θ →
    Z∞ ⊢[γ, c] insert φ Γ → Z∞ ⊢[δ, c] insert (∼φ) Γ → ∃ ε < ω ^ θ, Z∞ ⊢[ε, c] Γ

namespace CutReducible

lemma neg (h : CutReducible θ c φ) : CutReducible θ c (∼φ) := fun hγ hδ h₁ h₂ =>
  h hδ hγ (by simpa using h₂) h₁

end CutReducible

namespace Provable

/-- A formula of quantifier rank below `c` is cut-reducible at rank `c`.

- [Tow20, Section 19.5] -/
lemma cutReducible_of_qr_lt (hθ : 0 < θ) (h : φ.qr < c) : CutReducible θ c φ :=
  fun hγ hδ h₁ h₂ =>
    ⟨_, Ordinal.add_one_lt_omega0_opow hθ (max_lt hγ hδ), cut φ h h₁ h₂⟩

section Falsum

/-- Erases `⊥` from a cut-free derivation without increasing its height.

- [Tow20, Section 19.2] -/
private lemma remove_falsumAux (D : Derivation Γ) (hcr : D.cutRank ≤ (0 : ℕ∞)) (hmem : ⊥ ∈ Γ) :
    Z∞ ⊢[D.ordinalBound, 0] Γ.erase ⊥ := by
  induction D with
  | @axL Γ k r v hp hn => exact axL r v (by grind) (by grind)
  | @axTrue Γ k b r v ht hm =>
    refine axTrue b r v ht ?_
    cases b <;> · simp only [signedLit] at hm ⊢; grind
  | @verumR Γ h => exact verumR (by grind)
  | @weak Δ Γ D' hsub ih =>
    by_cases hd : (⊥ : ArithmeticFormula ℕ) ∈ Δ
    · exact (ih hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show Z∞ ⊢[D'.ordinalBound, 0] Δ from ⟨D', le_rfl, hcr⟩).weakening ?_
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
  | @andI Γ₁ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have h₀ : Z∞ ⊢[D₀.ordinalBound, 0] insert χ₀ (Γ₁.erase ⊥) :=
      (ih₀ ((le_max_left _ _).trans hcr) (by grind)).weakening (eraseIn χ₀ ⊥ Γ₁)
    have h₁ : Z∞ ⊢[D₁.ordinalBound, 0] insert χ₁ (Γ₁.erase ⊥) :=
      (ih₁ ((le_max_right _ _).trans hcr) (by grind)).weakening (eraseIn χ₁ ⊥ Γ₁)
    exact (andI h₀ h₁).weakening (eraseOut (by grind) Γ₁)
  | @orI Γ₁ χ₀ χ₁ D' ih =>
    have h : Z∞ ⊢[D'.ordinalBound, 0] insert χ₀ (insert χ₁ (Γ₁.erase ⊥)) :=
      (ih hcr (by grind)).weakening
        ((eraseIn χ₀ ⊥ _).trans (Finset.insert_subset_insert χ₀ (eraseIn χ₁ ⊥ Γ₁)))
    exact (orI h).weakening (eraseOut (by grind) Γ₁)
  | @allω Γ₁ χ Dₓ ih =>
    have h : ∀ n : ℕ, Z∞ ⊢[(Dₓ n).ordinalBound, 0]
        insert (χ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase ⊥) := fun n =>
      (ih n ((le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr) (by grind)).weakening
        (eraseIn _ ⊥ Γ₁)
    exact (allω h).weakening (eraseOut (by grind) Γ₁)
  | @exI Γ₁ χ n D' ih =>
    have h : Z∞ ⊢[D'.ordinalBound, 0] insert (χ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase ⊥) :=
      (ih hcr (by grind)).weakening (eraseIn _ ⊥ Γ₁)
    exact (exI n h).weakening (eraseOut (by grind) Γ₁)
  | @cut Γ₁ ξ D₁ D₂ ih₁ ih₂ => exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- Removes `⊥` from a cut-free sequent without increasing its height.

- [Tow20, Section 19.2] -/
lemma remove_falsum (h : Z∞ ⊢[α, 0] insert ⊥ Γ) : Z∞ ⊢[α, 0] Γ := by
  obtain ⟨D, ho, hcr⟩ := h
  refine ((remove_falsumAux D hcr (Finset.mem_insert_self _ _)).weakening ?_).mono_ordinalBound ho
  intro x hx
  simp only [Finset.mem_erase, Finset.mem_insert] at hx
  exact hx.2.resolve_left hx.1

lemma cutReducible_verum : CutReducible θ 0 (⊤ : ArithmeticFormula ℕ) :=
  fun _ hδ _ h₂ => ⟨_, hδ, remove_falsum (by simpa using h₂)⟩

lemma cutReducible_falsum : CutReducible θ 0 (⊥ : ArithmeticFormula ℕ) :=
  fun hγ _ h₁ _ => ⟨_, hγ, remove_falsum h₁⟩

end Falsum

section Atom

variable {k₀ : ℕ} {b₀ : Bool} {r₀ : (ℒₒᵣ).Rel k₀} {v₀ : Fin k₀ → ArithmeticTerm ℕ}

/-- Erases a false literal from a cut-free derivation without increasing its height.

- [Tow20, Section 19.2] -/
private lemma remove_false_litAux (hL : ¬LitTrue (signedLit b₀ r₀ v₀)) (D : Derivation Γ)
    (hcr : D.cutRank ≤ (0 : ℕ∞)) (hmem : signedLit b₀ r₀ v₀ ∈ Γ) :
    Z∞ ⊢[D.ordinalBound, 0] Γ.erase (signedLit b₀ r₀ v₀) := by
  have hne : ∀ χ : ArithmeticFormula ℕ, χ.complexity ≠ 0 → χ ≠ signedLit b₀ r₀ v₀ := fun χ h =>
    Semiformula.ne_of_ne_complexity (by cases b₀ <;> simp [signedLit, h])
  induction D with
  | @axL Γ k r v hp hn =>
    by_cases h₁ : signedLit b₀ r₀ v₀ = Semiformula.rel r v
    · refine axTrue false r v ?_ (Finset.mem_erase.mpr ⟨by rw [h₁]; simp [signedLit], hn⟩)
      show LitTrue (Semiformula.nrel r v)
      rw [← Semiformula.neg_rel, litTrue_neg]
      exact h₁ ▸ hL
    · by_cases h₂ : signedLit b₀ r₀ v₀ = Semiformula.nrel r v
      · refine axTrue true r v ?_ (Finset.mem_erase.mpr ⟨by rw [h₂]; simp [signedLit], hp⟩)
        show LitTrue (Semiformula.rel r v)
        by_contra hc
        exact (h₂ ▸ hL) (by rw [← Semiformula.neg_rel, litTrue_neg]; exact hc)
      · exact axL r v (Finset.mem_erase.mpr ⟨fun e => h₁ e.symm, hp⟩)
          (Finset.mem_erase.mpr ⟨fun e => h₂ e.symm, hn⟩)
  | @axTrue Γ k b r v ht hm =>
    exact axTrue b r v ht (Finset.mem_erase.mpr ⟨fun e => hL (e ▸ ht), hm⟩)
  | @verumR Γ h => exact verumR (Finset.mem_erase.mpr ⟨signedLit_ne_verum.symm, h⟩)
  | @weak Δ Γ D' hsub ih =>
    by_cases hd : signedLit b₀ r₀ v₀ ∈ Δ
    · exact (ih hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show Z∞ ⊢[D'.ordinalBound, 0] Δ from ⟨D', le_rfl, hcr⟩).weakening ?_
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
  | @andI Γ₁ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have hd : signedLit b₀ r₀ v₀ ∈ Γ₁ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hne _ (by simp) e.symm
    have h₀ := (ih₀ ((le_max_left _ _).trans hcr) (Finset.mem_insert_of_mem hd)).weakening
      (eraseIn χ₀ _ Γ₁)
    have h₁ := (ih₁ ((le_max_right _ _).trans hcr) (Finset.mem_insert_of_mem hd)).weakening
      (eraseIn χ₁ _ Γ₁)
    exact (andI h₀ h₁).weakening (eraseOut (hne _ (by simp)) Γ₁)
  | @orI Γ₁ χ₀ χ₁ D' ih =>
    have hd : signedLit b₀ r₀ v₀ ∈ Γ₁ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hne _ (by simp) e.symm
    have h := (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd))).weakening
      ((eraseIn χ₀ _ _).trans (Finset.insert_subset_insert χ₀ (eraseIn χ₁ _ Γ₁)))
    exact (orI h).weakening (eraseOut (hne _ (by simp)) Γ₁)
  | @allω Γ₁ χ Dₓ ih =>
    have hd : signedLit b₀ r₀ v₀ ∈ Γ₁ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hne _ (by simp) e.symm
    have h : ∀ n : ℕ, Z∞ ⊢[(Dₓ n).ordinalBound, 0]
        insert (χ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase (signedLit b₀ r₀ v₀)) := fun n =>
      (ih n ((le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr)
        (Finset.mem_insert_of_mem hd)).weakening (eraseIn _ _ Γ₁)
    exact (allω h).weakening (eraseOut (hne _ (by simp)) Γ₁)
  | @exI Γ₁ χ n D' ih =>
    have hd : signedLit b₀ r₀ v₀ ∈ Γ₁ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hne _ (by simp) e.symm
    have h := (ih hcr (Finset.mem_insert_of_mem hd)).weakening (eraseIn _ _ Γ₁)
    exact (exI n h).weakening (eraseOut (hne _ (by simp)) Γ₁)
  | @cut Γ₁ ξ D₁ D₂ ih₁ ih₂ => exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- Removes a false literal from a cut-free sequent without increasing its height.

- [Tow20, Section 19.2] -/
lemma remove_false_lit (hL : ¬LitTrue (signedLit b₀ r₀ v₀))
    (h : Z∞ ⊢[α, 0] insert (signedLit b₀ r₀ v₀) Γ) : Z∞ ⊢[α, 0] Γ := by
  obtain ⟨D, ho, hcr⟩ := h
  refine ((remove_false_litAux hL D hcr
    (Finset.mem_insert_self _ _)).weakening ?_).mono_ordinalBound ho
  intro x hx
  simp only [Finset.mem_erase, Finset.mem_insert] at hx
  exact hx.2.resolve_left hx.1

/-- Eliminates an atomic cut against a cut-free derivation with an explicit height bound.

- [Tow20, Section 19.2] -/
private lemma atom_cutAux (r : (ℒₒᵣ).Rel k) (v) (hNC : Z∞ ⊢[β, 0] insert (Semiformula.nrel r v) Γ)
    (D : Derivation Δ) (hcr : D.cutRank ≤ (0 : ℕ∞)) (hmem : (Semiformula.rel r v) ∈ Δ) :
    Z∞ ⊢[β + D.ordinalBound + 1, 0] (Δ.erase (Semiformula.rel r v) ∪ Γ) := by
  induction D with
  | @axL Δ k' r' v' hp hn =>
    have hnn : (Semiformula.nrel r' v' : ArithmeticFormula ℕ) ∈ Δ.erase (Semiformula.rel r v) :=
      Finset.mem_erase.mpr ⟨by simp, hn⟩
    by_cases hrel : (Semiformula.rel r' v' : ArithmeticFormula ℕ) = Semiformula.rel r v
    · have hnrv : (Semiformula.nrel r' v' : ArithmeticFormula ℕ) = Semiformula.nrel r v := by
        rw [← Semiformula.neg_rel r' v', hrel, Semiformula.neg_rel]
      refine (hNC.weakening ?_).mono_ordinalBound (le_self_add.trans (lt_add_one _).le)
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_union_left _ (hnrv ▸ hnn)
      · exact Finset.mem_union_right _ hx
    · exact (axL r' v' (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hrel, hp⟩))
        (Finset.mem_union_left _ hnn)).mono_ordinalBound zero_le
  | @axTrue Δ k' b' r' v' ht hm =>
    by_cases heq : (signedLit b' r' v' : ArithmeticFormula ℕ) = Semiformula.rel r v
    · have hfalse : ¬LitTrue (signedLit false r v) := by
        have : LitTrue (Semiformula.rel r v) := heq ▸ ht
        simpa [signedLit, ← Semiformula.neg_rel] using this
      have hrm := remove_false_lit hfalse
        (show Z∞ ⊢[β, 0] insert (signedLit false r v) Γ by simpa [signedLit] using hNC)
      exact (hrm.weakening Finset.subset_union_right).mono_ordinalBound
        (le_self_add.trans (lt_add_one _).le)
    · exact (axTrue b' r' v' ht (Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨heq, hm⟩))).mono_ordinalBound zero_le
  | @verumR Δ h =>
    exact (verumR (Finset.mem_union_left _
      (Finset.mem_erase.mpr ⟨by simp, h⟩))).mono_ordinalBound zero_le
  | @weak Δ' Δ D' hsub ih =>
    by_cases hd : (Semiformula.rel r v) ∈ Δ'
    · refine (ih hcr hd).weakening ?_
      intro x; simp only [Finset.mem_union, Finset.mem_erase]; grind
    · refine ((show Z∞ ⊢[D'.ordinalBound, 0] Δ' from ⟨D', le_rfl, hcr⟩).weakening
        ?_).mono_ordinalBound (le_add_self.trans (lt_add_one _).le)
      intro x hx
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
  | @andI Γ₁ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have h₀ := (ih₀ ((le_max_left _ _).trans hcr) (by grind)).weakening (frameIn χ₀ _ Γ₁ Γ)
    have h₁ := (ih₁ ((le_max_right _ _).trans hcr) (by grind)).weakening (frameIn χ₁ _ Γ₁ Γ)
    exact ((andI h₀ h₁).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.max_add_add_one_add_one_le β D₀.ordinalBound D₁.ordinalBound)
  | @orI Γ₁ χ₀ χ₁ D' ih =>
    have h := (ih hcr (by grind)).weakening
      ((frameIn χ₀ _ _ Γ).trans (Finset.insert_subset_insert χ₀ (frameIn χ₁ _ Γ₁ Γ)))
    exact ((orI h).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.add_add_one_add_one_le β D'.ordinalBound)
  | @allω Γ₁ χ Dₓ ih =>
    have h : ∀ n : ℕ, Z∞ ⊢[β + (Dₓ n).ordinalBound + 1, 0]
        insert (χ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase (Semiformula.rel r v) ∪ Γ) := fun n =>
      (ih n ((le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr) (by grind)).weakening
        (frameIn _ _ Γ₁ Γ)
    exact ((allω h).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.iSup_add_add_one_add_one_le β fun n => (Dₓ n).ordinalBound)
  | @exI Γ₁ χ n D' ih =>
    have h := (ih hcr (by grind)).weakening (frameIn _ _ Γ₁ Γ)
    exact ((exI n h).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.add_add_one_add_one_le β D'.ordinalBound)
  | @cut Γ₁ ξ D₁ D₂ ih₁ ih₂ => exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- Eliminates a cut on an atomic formula between cut-free derivations.

- [Tow20, Section 19.2] -/
lemma atom_cut (r : (ℒₒᵣ).Rel k) (v) (hC : Z∞ ⊢[α, 0] insert (Semiformula.rel r v) Γ)
    (hNC : Z∞ ⊢[β, 0] insert (Semiformula.nrel r v) Γ) : Z∞ ⊢[β + α + 1, 0] Γ := by
  obtain ⟨D, ho, hcr⟩ := hC
  refine ((atom_cutAux r v hNC D hcr (Finset.mem_insert_self _ _)).weakening ?_).mono_ordinalBound
    (by gcongr)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx
  tauto

/-- An atomic formula reduces at rank `0`.

- [Tow20, Section 19.2] -/
lemma cutReducible_rel (hθ : 0 < θ) (r : (ℒₒᵣ).Rel k) (v) :
    CutReducible θ 0 (Semiformula.rel r v) := fun hγ hδ h₁ h₂ =>
  ⟨_, Ordinal.add_one_lt_omega0_opow hθ (Ordinal.add_lt_omega0_opow hδ hγ),
    atom_cut r v h₁ (by simpa using h₂)⟩

/-- A negated atomic formula reduces at rank `0`.

- [Tow20, Section 19.2] -/
lemma cutReducible_nrel (hθ : 0 < θ) (r : (ℒₒᵣ).Rel k) (v) :
    CutReducible θ 0 (Semiformula.nrel r v) := fun hγ hδ h₁ h₂ =>
  ⟨_, Ordinal.add_one_lt_omega0_opow hθ (Ordinal.add_lt_omega0_opow hγ hδ),
    atom_cut r v (by simpa using h₂) h₁⟩

lemma cutReducible_of_complexity_zero (hθ : 0 < θ) (hc : φ.complexity = 0) :
    CutReducible θ c φ := by
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · cases φ using Semiformula.cases' with
    | hverum => exact cutReducible_verum
    | hfalsum => exact cutReducible_falsum
    | hrel r v => exact cutReducible_rel hθ r v
    | hnrel r v => exact cutReducible_nrel hθ r v
    | _ => simp at hc
  · refine cutReducible_of_qr_lt hθ ?_
    have : φ.qr = 0 := by cases φ using Semiformula.cases' <;> simp_all
    omega

end Atom

section Binary

/-- Reducibility of both conjuncts implies reducibility of their conjunction.

- [Tow20, Theorem 19.5] -/
lemma cut_reduce_and (hφ : CutReducible θ c φ) (hψ : CutReducible θ c ψ) :
    CutReducible θ c (φ ⋏ ψ) := by
  intro Γ γ δ hγ hδ hC hNC
  have hA : Z∞ ⊢[γ, c] insert φ Γ :=
    (hC.and_inv_left (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hB : Z∞ ⊢[γ, c] insert ψ Γ :=
    (hC.and_inv_right (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hNab : Z∞ ⊢[δ, c] insert (∼φ) (insert (∼ψ) Γ) :=
    ((show Z∞ ⊢[δ, c] insert (∼φ ⋎ ∼ψ) Γ by simpa using hNC).or_inv
      (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  obtain ⟨ε, hε, h⟩ := hφ hγ hδ (hA.weakening (by
    intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto)) hNab
  exact hψ hγ hε hB h

/-- Reducibility of both disjuncts implies reducibility of their disjunction.

- [Tow20, Theorem 19.5] -/
lemma cut_reduce_or (hφ : CutReducible θ c φ) (hψ : CutReducible θ c ψ) :
    CutReducible θ c (φ ⋎ ψ) := by
  intro Γ γ δ hγ hδ hC hNC
  exact cut_reduce_and hφ.neg hψ.neg hδ hγ (by simpa using hNC) (by simpa using hC)

end Binary

section Quantifier

/-- Eliminates a universal cut against a bounded derivation with an explicit height bound.

- [Tow20, Theorem 19.6] -/
private lemma cut_reduce_allAux (hqr : φₓ.qr < c)
    (fam : ∀ n : ℕ, Z∞ ⊢[α, c] insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ)
    (D : Derivation Δ) (hcr : D.cutRank ≤ (c : ℕ∞)) (hmem : (∃¹ ∼φₓ) ∈ Δ) :
    Z∞ ⊢[α + D.ordinalBound + 1, c] (Δ.erase (∃¹ ∼φₓ) ∪ Γ) := by
  induction D with
  | @axL Δ k r v hp hn =>
    exact (axL r v (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by grind, hp⟩))
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by grind, hn⟩))).mono
      zero_le (Nat.zero_le c)
  | @axTrue Δ k b r v ht hm =>
    refine (axTrue b r v ht (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hm⟩))).mono
      zero_le (Nat.zero_le c)
    cases b <;> · simp only [signedLit]; grind
  | @verumR Δ h =>
    exact (verumR (Finset.mem_union_left _
      (Finset.mem_erase.mpr ⟨by grind, h⟩))).mono zero_le (Nat.zero_le c)
  | @weak Δ' Δ D' hsub ih =>
    by_cases hd : (∃¹ ∼φₓ) ∈ Δ'
    · refine (ih hcr hd).weakening ?_
      intro x; simp only [Finset.mem_union, Finset.mem_erase]; grind
    · refine ((show Z∞ ⊢[D'.ordinalBound, c] Δ' from ⟨D', le_rfl, hcr⟩).weakening
        ?_).mono_ordinalBound (le_add_self.trans (lt_add_one _).le)
      intro x hx
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
  | @andI Γ₁ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have h₀ := (ih₀ ((le_max_left _ _).trans hcr) (by grind)).weakening (frameIn χ₀ _ Γ₁ Γ)
    have h₁ := (ih₁ ((le_max_right _ _).trans hcr) (by grind)).weakening (frameIn χ₁ _ Γ₁ Γ)
    exact ((andI h₀ h₁).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.max_add_add_one_add_one_le α D₀.ordinalBound D₁.ordinalBound)
  | @orI Γ₁ χ₀ χ₁ D' ih =>
    have h := (ih hcr (by grind)).weakening
      ((frameIn χ₀ _ _ Γ).trans (Finset.insert_subset_insert χ₀ (frameIn χ₁ _ Γ₁ Γ)))
    exact ((orI h).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.add_add_one_add_one_le α D'.ordinalBound)
  | @allω Γ₁ χ Dₓ ih =>
    have h : ∀ n : ℕ, Z∞ ⊢[α + (Dₓ n).ordinalBound + 1, c]
        insert (χ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase (∃¹ ∼φₓ) ∪ Γ) := fun n =>
      (ih n ((le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr) (by grind)).weakening
        (frameIn _ _ Γ₁ Γ)
    exact ((allω h).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.iSup_add_add_one_add_one_le α fun n => (Dₓ n).ordinalBound)
  | @exI Γ₁ χ n D' ih =>
    by_cases hhd : (∃¹ χ) = (∃¹ ∼φₓ)
    · obtain rfl := (Semiformula.exs_inj _ _).mp hhd
      rw [Finset.erase_insert_eq_erase]
      have hcut : ((φₓ/[(↑n : ArithmeticTerm ℕ)]) : ArithmeticFormula ℕ).qr < c := by
        simpa using hqr
      have hfam := (fam n).weakening (show insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ
          ⊆ insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase (∃¹ ∼φₓ) ∪ Γ) from by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
      by_cases hd : (∃¹ ∼φₓ) ∈ Γ₁
      · have hP : Z∞ ⊢[α + D'.ordinalBound + 1, c]
            insert (∼(φₓ/[(↑n : ArithmeticTerm ℕ)])) (Γ₁.erase (∃¹ ∼φₓ) ∪ Γ) := by
          refine (ih hcr (Finset.mem_insert_of_mem hd)).weakening ?_
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with ⟨hne, rfl | hx⟩ | hx
          · left; simp
          · exact Or.inr (Or.inl ⟨hne, hx⟩)
          · exact Or.inr (Or.inr hx)
        refine (cut _ hcut hfam hP).mono_ordinalBound ?_
        gcongr
        exact max_le le_self_add (le_of_eq (add_assoc α D'.ordinalBound 1))
      · have hP : Z∞ ⊢[D'.ordinalBound, c]
            insert (∼(φₓ/[(↑n : ArithmeticTerm ℕ)])) (Γ₁.erase (∃¹ ∼φₓ) ∪ Γ) := by
          refine (show Z∞ ⊢[D'.ordinalBound, c] insert ((∼φₓ)/[(↑n : ArithmeticTerm ℕ)]) Γ₁ from
            ⟨D', le_rfl, hcr⟩).weakening ?_
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · left; simp
          · exact Or.inr (Or.inl ⟨fun e => hd (e ▸ hx), hx⟩)
        refine (cut _ hcut hfam hP).mono_ordinalBound ?_
        gcongr
        exact max_le le_self_add ((lt_add_one _).le.trans le_add_self)
    · have h := (ih hcr (by grind)).weakening (frameIn _ _ Γ₁ Γ)
      exact ((exI n h).weakening (frameOut hhd Γ₁ Γ)).mono_ordinalBound
        (Ordinal.add_add_one_add_one_le α D'.ordinalBound)
  | @cut Γ₁ ξ D₁ D₂ ih₁ ih₂ =>
    have hcξ : ξ.qr < c := qr_lt_of_succ_le ((le_max_left _ _).trans hcr)
    have h₁ := (ih₁ ((le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr))
      (Finset.mem_insert_of_mem hmem)).weakening (frameIn ξ _ Γ₁ Γ)
    have h₂ := (ih₂ ((le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr))
      (Finset.mem_insert_of_mem hmem)).weakening (frameIn (∼ξ) _ Γ₁ Γ)
    exact (cut ξ hcξ h₁ h₂).mono_ordinalBound
      (Ordinal.max_add_add_one_add_one_le α D₁.ordinalBound D₂.ordinalBound)

/-- A universal formula of quantifier rank below `c` is cut-reducible at rank `c`.

- [Tow20, Theorem 19.6] -/
lemma cut_reduce_all (hθ : 0 < θ) (hqr : φₓ.qr < c) : CutReducible θ c (∀¹ φₓ) := by
  intro Γ γ δ hγ hδ hC hNC
  have fam : ∀ n : ℕ, Z∞ ⊢[γ, c] insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ := fun n =>
    (hC.all_inv (Finset.mem_insert_self _ _) n).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  obtain ⟨D, ho, hcr⟩ : Z∞ ⊢[δ, c] insert (∃¹ ∼φₓ) Γ := by simpa using hNC
  refine ⟨γ + δ + 1, Ordinal.add_one_lt_omega0_opow hθ (Ordinal.add_lt_omega0_opow hγ hδ), ?_⟩
  refine ((cut_reduce_allAux hqr fam D hcr
    (Finset.mem_insert_self _ _)).weakening ?_).mono_ordinalBound (by gcongr)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx
  tauto

end Quantifier

end Provable

end LO.FirstOrder.Arithmetic.OmegaLogic
