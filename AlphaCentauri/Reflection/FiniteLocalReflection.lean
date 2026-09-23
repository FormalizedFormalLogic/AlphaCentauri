module

public import AlphaCentauri.Reflection.ProvabilityAbstraction
public import AlphaCentauri.ToProvabilityLogic.Interpret
public import ProvabilityLogic.ProvabilityLogic.GL.Basic

@[expose] public section
/-!
# Collapsing finitely many local reflection instances

If `T` derives `σ` from finitely many local reflection instances `𝔅 τᵢ 🡒 τᵢ`, then it derives `σ`
from the instances at the sentences `ρ₀ := σ`, `ρᵢ₊₁ := ρᵢ ⋎ 𝔅 ρᵢ`, which depend on `σ` alone.
The argument is carried out in `GL` and transported by its arithmetical soundness.

- [Bek99, Lemma 4.2]
- [Bek99, Lemma 5.2]
-/

namespace FFL.FirstOrder.ProvabilityAbstraction.Provability

open FFL.Entailment

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T)

/-- `ρ₀ := σ`, `ρᵢ₊₁ := ρᵢ ⋎ 𝔅 ρᵢ`.
- [Bek99, Lemma 4.2] -/
def collapseSeq (σ : Sentence L) : ℕ → Sentence L
  | 0 => σ
  | i + 1 => collapseSeq σ i ⋎ 𝔅 (collapseSeq σ i)

end FFL.FirstOrder.ProvabilityAbstraction.Provability

namespace LogicGL.FiniteLocalReflection

open Model.World

variable {α : Type*}

/-- The modal counterpart of `collapseSeq`. -/
def seq (B : Formula α) : ℕ → Formula α
  | 0 => B
  | i + 1 => seq B i ⋎ □(seq B i)

variable {m : ℕ}

/-- `⋀ᵢ (□pᵢ 🡒 pᵢ) 🡒 q`, with `q` the atom `none` and `pᵢ` the atom `some i`. -/
def hyp (m : ℕ) : Formula (Option (Fin (m + 1))) :=
  FormulaList.conj (List.ofFn fun i : Fin (m + 1) ↦
    (Formula.atom (some i)).box 🡒 Formula.atom (some i)) 🡒 Formula.atom none

/-- The reflection instances at `seq q i`. -/
def reflection (m : ℕ) : Formula (Option (Fin (m + 1))) :=
  FormulaList.conj (List.ofFn fun i : Fin (m + 1) ↦
    (seq (Formula.atom none) i).box 🡒 seq (Formula.atom none) i)

section Kripke

variable {κ : Type*} [Nonempty κ] {M : Model κ (Option (Fin (m + 1)))} [M.IsFiniteGL]

omit [M.IsFiniteGL] in
lemma not_forces_seq_succ {x : M.World} {B : Formula _} {i : ℕ} :
    x ⊮[M] seq B (i + 1) ↔ x ⊮[M] seq B i ∧ ∃ y, x ≺ y ∧ y ⊮[M] seq B i := by
  grind [seq]

omit [M.IsFiniteGL] in
lemma not_forces_of_not_forces_seq {x : M.World} {B : Formula _} {i : ℕ}
    (h : x ⊮[M] seq B i) : x ⊮[M] B := by
  induction i with
  | zero => exact h
  | succ i ih => exact ih (not_forces_seq_succ.mp h).1

/-- The indices `i` such that some world above `x` or `x` itself refutes `pᵢ`. -/
noncomputable def refuted (x : M.World) : Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter fun i ↦ ∃ z, (z = x ∨ x ≺ z) ∧ z ⊮[M] Formula.atom (some i)

lemma card_refuted {w : M.World} (hw : ∀ x, x = w ∨ w ≺ x → x ⊩[M] hyp m) :
    ∀ k x, (x = w ∨ w ≺ x) → x ⊮[M] seq (Formula.atom none) k → k + 1 ≤ (refuted x).card := by
  classical
  have witness : ∀ x, (x = w ∨ w ≺ x) → x ⊮[M] Formula.atom none →
      ∃ i, x ⊩[M] □(Formula.atom (some i)) ∧ x ⊮[M] Formula.atom (some i) := by
    intro x hx hq
    rcases forces_imp.mp (hw x hx) with h | h
    · rw [NotForces, forces_lconj] at h
      push Not at h
      obtain ⟨A, hA, hxA⟩ := h
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
      exact ⟨i, by grind⟩
    · exact absurd h hq
  intro k
  induction k with
  | zero =>
    intro x hx hs
    obtain ⟨i, -, hi⟩ := witness x hx hs
    refine Finset.card_pos.mpr ⟨i, ?_⟩
    simp only [refuted, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, Or.inl rfl, hi⟩
  | succ k ih =>
    intro x hx hs
    obtain ⟨hk, y, hxy, hy⟩ := not_forces_seq_succ.mp hs
    have hrel : ∀ {a b c : M.World}, a ≺ b → (c = b ∨ b ≺ c) → a ≺ c := by
      rintro a b c hab (rfl | hbc)
      · exact hab
      · exact IsTrans.trans _ _ _ hab hbc
    have hy' : y = w ∨ w ≺ y :=
      hx.elim (fun h ↦ Or.inr (h ▸ hxy)) fun hwx ↦ Or.inr (hrel hwx (Or.inr hxy))
    obtain ⟨i, hbox, hi⟩ := witness x hx (not_forces_of_not_forces_seq hk)
    have hsub : refuted y ⊆ refuted x := by
      intro j
      simp only [refuted, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨z, hz, hzj⟩
      exact ⟨z, Or.inr (hrel hxy hz), hzj⟩
    have hnot : i ∉ refuted y := by
      simp only [refuted, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
      intro z hz hzi
      exact hzi <| forces_box.mp hbox z (hrel hxy hz)
    have hin : i ∈ refuted x := by
      simp only [refuted, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, Or.inl rfl, hi⟩
    have := ih y hy' hy
    calc k + 1 + 1 ≤ (refuted y).card + 1 := by omega
      _ = (insert i (refuted y)).card := (Finset.card_insert_of_notMem hnot).symm
      _ ≤ (refuted x).card := Finset.card_le_card (Finset.insert_subset hin hsub)

end Kripke

/-- The modal form of the collapse: `⊡hyp` and the reflection instances at `seq q i` give `q`. -/
theorem collapse_mem (m : ℕ) :
    (hyp m 🡒 □hyp m 🡒 reflection m 🡒 Formula.atom none) ∈ LogicGL := by
  classical
  rw [LogicGL.iff_forces]
  intro κ _ M _ w
  simp only [forces_imp]
  by_contra! hc
  obtain ⟨hH, hbH, hR, hq⟩ := hc
  have hw : ∀ x, x = w ∨ w ≺ x → x ⊩[M] hyp m := by
    rintro x (rfl | hx)
    · exact hH
    · exact forces_box.mp hbH x hx
  have hR' : ∀ i : Fin (m + 1),
      w ⊩[M] (seq (Formula.atom none) i).box 🡒 seq (Formula.atom none) i := by
    intro i
    exact forces_lconj.mp hR _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hs : ∀ k ≤ m + 1, w ⊮[M] seq (Formula.atom none) k := by
    intro k
    induction k with
    | zero => intro _; exact hq
    | succ k ih =>
      intro hk
      have hk' := ih (by omega)
      refine not_forces_seq_succ.mpr ⟨hk', ?_⟩
      have := hR' ⟨k, by omega⟩
      rw [forces_imp] at this
      by_contra! hc
      rcases this with h | h
      · exact h hc
      · exact hk' h
  have := card_refuted hw (m + 1) w (Or.inl rfl) (hs (m + 1) le_rfl)
  have := (refuted w).card_le_univ
  simp at this
  omega

end LogicGL.FiniteLocalReflection

namespace FFL.FirstOrder.ProvabilityAbstraction.Provability

open FFL.Entailment LogicGL.FiniteLocalReflection

variable {L : Language} [L.ReferenceableBy L] [L.DecidableEq] {T₀ T : Theory L}
  (𝔅 : Provability T₀ T) [T₀ ⪯ T]

omit [L.DecidableEq] in
private lemma pbl_ext [𝔅.HBL2] {σ τ : Sentence L} (h : T ⊢ σ 🡘 τ) : T ⊢ 𝔅 σ 🡘 𝔅 τ :=
  WeakerThan.pbl (𝔅.ext h)

section interpret

variable {α : Type*} {f : Realization α L}

variable [𝔅.HBL2]

lemma interpret_seq (B : _root_.Formula α) (i : ℕ) :
    T ⊢ (seq B i).interpret f 𝔅 🡘 𝔅.collapseSeq (B.interpret f 𝔅) i := by
  induction i with
  | zero => simp only [seq, collapseSeq]; cl_prover
  | succ i ih =>
    have hb := 𝔅.pbl_ext ih
    simp only [seq, collapseSeq, _root_.Formula.interpret]
    cl_prover [ih, hb]

end interpret

/-- If `T` derives `σ` from local reflection instances at `τ₀, …, τₘ`, then it derives `σ` from
those at `collapseSeq σ 0, …, collapseSeq σ m`.
- [Bek99, Lemma 4.2] -/
theorem collapse_localReflection [𝔅.HBL] [Diagonalization T₀] {m : ℕ} {σ : Sentence L}
    {τ : Fin (m + 1) → Sentence L} (h : T ⊢ (⩕ i, 𝔅.localReflectionSchema (τ i)) 🡒 σ) :
    T ⊢ (⩕ i : Fin (m + 1), 𝔅.localReflectionSchema (𝔅.collapseSeq σ i)) 🡒 σ := by
  classical
  let f : Realization (Option (Fin (m + 1))) L := ⟨fun o ↦ o.elim σ τ⟩
  have hH : T ⊢ (hyp m).interpret f 𝔅 := by
    have : T ⊢ (FormulaList.conj (List.ofFn fun i ↦
          (Formula.atom (some i)).box 🡒 Formula.atom (some i))).interpret f 𝔅 🡒
        ⩕ i, 𝔅.localReflectionSchema (τ i) :=
      right_Uconj_intro _ _ fun i ↦ Formula.interpret_conj_left (List.mem_ofFn.mpr ⟨i, rfl⟩)
    simp only [hyp, _root_.Formula.interpret] at this ⊢
    cl_prover [this, h]
  have hbox : T ⊢ 𝔅 ((hyp m).interpret f 𝔅) := WeakerThan.pbl (𝔅.D1 hH)
  have hG : T ⊢ (hyp m 🡒 □hyp m 🡒 reflection m 🡒 Formula.atom none).interpret f 𝔅 :=
    LogicGL.arithmetical_soundness' (collapse_mem m)
  have hR : T ⊢ (⩕ i : Fin (m + 1), 𝔅.localReflectionSchema (𝔅.collapseSeq σ i)) 🡒
      (reflection m).interpret f 𝔅 := by
    refine Formula.interpret_conj_right fun B hB ↦ ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
    have e := interpret_seq 𝔅 (f := f) (Formula.atom none) i
    have eb := 𝔅.pbl_ext e
    have l := left_Uconj_intro (𝓢 := T)
      (fun i : Fin (m + 1) ↦ 𝔅.localReflectionSchema (𝔅.collapseSeq σ i)) i
    simp only [_root_.Formula.interpret] at e eb l ⊢
    cl_prover [e, eb, l]
  simp only [_root_.Formula.interpret] at hG
  cl_prover [hH, hbox, hG, hR]

section iterate

variable [𝔅.HBL2]

private lemma bot_imp_succ_bot (n : ℕ) : T₀ ⊢ 𝔅^[n] ⊥ 🡒 𝔅^[n + 1] ⊥ := by
  induction n with
  | zero => simp only [Function.iterate_zero, id]; cl_prover
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply' (n := n + 1)]
    exact 𝔅.mono' ih

lemma iterate_bot_imp_iterate_bot {j k : ℕ} (h : j ≤ k) : T₀ ⊢ 𝔅^[j] ⊥ 🡒 𝔅^[k] ⊥ := by
  induction k, h using Nat.le_induction with
  | base => cl_prover
  | succ k _ ih => cl_prover [ih, 𝔅.bot_imp_succ_bot k]

lemma collapseSeq_bot (i : ℕ) : T ⊢ 𝔅.collapseSeq ⊥ i 🡘 𝔅^[i] ⊥ := by
  induction i with
  | zero => simp only [collapseSeq, Function.iterate_zero, id]; cl_prover
  | succ i ih =>
    have hb : T ⊢ 𝔅 (𝔅.collapseSeq ⊥ i) 🡘 𝔅^[i + 1] ⊥ := by
      rw [Function.iterate_succ_apply']; exact 𝔅.pbl_ext ih
    have hm : T ⊢ 𝔅^[i] ⊥ 🡒 𝔅^[i + 1] ⊥ := WeakerThan.pbl (𝔅.iterate_bot_imp_iterate_bot (by omega))
    simp only [collapseSeq]
    cl_prover [ih, hb, hm]

end iterate

/-- If `T` refutes finitely many local reflection instances `𝔅 τᵢ 🡒 τᵢ` (`i ≤ m`), then it proves
`𝔅^[m + 1] ⊥`.
- [Bek99, Lemma 4.2]
- [Bek99, Lemma 5.2] -/
theorem iterate_bot_of_refutable_localReflection [𝔅.HBL] [Diagonalization T₀] {m : ℕ}
    {τ : Fin (m + 1) → Sentence L} (h : T ⊢ ∼⩕ i, 𝔅.localReflectionSchema (τ i)) :
    T ⊢ 𝔅^[m + 1] ⊥ := by
  have hc := 𝔅.collapse_localReflection (σ := ⊥) (τ := τ) (by cl_prover [h])
  have hr : T ⊢ (∼𝔅^[m + 1] ⊥ : Sentence L) 🡒
      ⩕ i : Fin (m + 1), 𝔅.localReflectionSchema (𝔅.collapseSeq ⊥ i) :=
    right_Uconj_intro _ _ fun i ↦ by
      have e := 𝔅.collapseSeq_bot i
      have eb : T ⊢ 𝔅 (𝔅.collapseSeq ⊥ i) 🡘 𝔅^[i + 1] ⊥ := by
        rw [Function.iterate_succ_apply']; exact 𝔅.pbl_ext e
      have hm : T ⊢ 𝔅^[i + 1] ⊥ 🡒 𝔅^[m + 1] ⊥ :=
        WeakerThan.pbl (𝔅.iterate_bot_imp_iterate_bot (by have := i.isLt; omega))
      cl_prover [e, eb, hm]
  cl_prover [hc, hr]

end FFL.FirstOrder.ProvabilityAbstraction.Provability
