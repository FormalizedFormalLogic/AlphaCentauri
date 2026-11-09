module

public import AlphaCentauri.ToFoundation.BlockSequence

/-!
# The pigeonhole principle for coded injections

Over a model of $\mathsf{EA}$, a number coding a sequence of blocks of width $\|a\|$ cannot code an
injection of $\{0, \dots, x\}$ into $\{0, \dots, x - 1\}$ for $x \le a$.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

attribute [local instance] ElementaryArithmetic.models_ISigma0_union_Omega1

section

variable {a : V}

lemma pigeonhole_induction {I : V} (hI : ‖I‖ = a + 1) :
    ∀ x ≤ a, ∀ S < I ⨳ a, ¬((∀ j ≤ x, Nuon.ext a S j < x) ∧
      ∀ j ≤ x, ∀ j' ≤ x, Nuon.ext a S j = Nuon.ext a S j' → j = j') := by
  intro x
  induction x using ISigma0.succ_induction
  · definability
  case zero =>
    intro _ S _ h
    have := h.1 0 (by simp)
    simp at this
  case succ x IH =>
    intro hx S hS h
    obtain ⟨hlt, hinj⟩ := h
    have hle : ∀ m ≤ x, m ≤ x + 1 := fun m hm => le_trans hm le_self_add
    have hxa : x ≤ a := le_trans le_self_add hx
    have hxI : x + 1 < ‖I‖ := by rw [hI]; exact lt_succ_iff_le.mpr hx
    have hxx1 : ¬(x + 1 ≤ x) := not_le.mpr (lt_succ_iff_le.mpr le_rfl)
    by_cases hc : ∃ j ≤ x + 1, Nuon.ext a S j = x
    · obtain ⟨j, hjx, hej⟩ := hc
      have hjI : j < ‖I‖ := lt_of_le_of_lt hjx hxI
      obtain ⟨S', hS', e₁, -, e₃⟩ := exists_swap hS hjI hxI
      have hmx : ∀ m ≤ x, m ≠ j → Nuon.ext a S' m = Nuon.ext a S m := fun m hm hmj =>
        e₃ m (le_trans (hle m hm) (le_of_lt hxI)) hmj (fun h => hxx1 (h ▸ hm))
      have hlt' : ∀ m ≤ x, Nuon.ext a S' m < x := by
        intro m hm
        obtain h | hmj := eq_or_ne m j
        · have hne : Nuon.ext a S (x + 1) ≠ x := fun h' => by
            have hx1j : x + 1 = j := hinj (x + 1) le_rfl j hjx (h'.trans hej.symm)
            exact hxx1 (by rw [hx1j, ← h]; exact hm)
          rw [h, e₁]
          exact lt_of_le_of_ne (lt_succ_iff_le.mp (hlt (x + 1) le_rfl)) hne
        · rw [hmx m hm hmj]
          exact lt_of_le_of_ne (lt_succ_iff_le.mp (hlt m (hle m hm)))
            (fun h' => hmj (hinj m (hle m hm) j hjx (h'.trans hej.symm)))
      have hinj' : ∀ m ≤ x, ∀ m' ≤ x, Nuon.ext a S' m = Nuon.ext a S' m' → m = m' := by
        intro m hm m' hm' heq
        obtain h | hmj := eq_or_ne m j
        · obtain h' | hm'j := eq_or_ne m' j
          · exact h.trans h'.symm
          · rw [h, e₁, hmx m' hm' hm'j] at heq
            have hx1 : x + 1 = m' := hinj (x + 1) le_rfl m' (hle m' hm') heq
            exact absurd (by rw [hx1]; exact hm') hxx1
        · obtain h' | hm'j := eq_or_ne m' j
          · rw [h', e₁, hmx m hm hmj] at heq
            have hx1 : m = x + 1 := hinj m (hle m hm) (x + 1) le_rfl heq
            exact absurd (by rw [← hx1]; exact hm) hxx1
          · rw [hmx m hm hmj, hmx m' hm' hm'j] at heq
            exact hinj m (hle m hm) m' (hle m' hm') heq
      exact IH hxa S' hS' ⟨hlt', hinj'⟩
    · have hlt' : ∀ l ≤ x, Nuon.ext a S l < x := fun l hl => by
        have hne : Nuon.ext a S l ≠ x := fun h => hc ⟨l, hle l hl, h⟩
        exact lt_of_le_of_ne (lt_succ_iff_le.mp (hlt l (hle l hl))) hne
      exact IH hxa S hS ⟨hlt', fun l hl l' hl' heq => hinj l (hle l hl) l' (hle l' hl') heq⟩

/-- For $x \le a$, no block-coded sequence of width $\|a\|$ of length $x + 1$ has pairwise distinct
entries below $x$.
- [HP98, Theorem I.1.41(2)]
- [Sla04, Lemma 2.3]
-/
theorem no_coded_injection (a x S : V) (hx : x ≤ a)
    (hlt : ∀ j ≤ x, Nuon.ext a S j < x)
    (hinj : ∀ j ≤ x, ∀ j' ≤ x, Nuon.ext a S j = Nuon.ext a S j' → j = j') : False := by
  obtain ⟨I, hI⟩ := ElementaryArithmetic.exponential_total a
  have hIlen : ‖I‖ = a + 1 := hI.length_eq
  have hxI : x < ‖I‖ := by rw [hIlen]; exact lt_succ_iff_le.mpr hx
  have htr : ∀ j ≤ x, Nuon.ext a (S % (I ⨳ a)) j = Nuon.ext a S j := fun j hj =>
    ext_mod_smash (lt_of_le_of_lt hj hxI)
  exact pigeonhole_induction hIlen x hx (S % (I ⨳ a)) (mod_lt S (smash_pos I a))
    ⟨fun j hj => by rw [htr j hj]; exact hlt j hj,
     fun j hj j' hj' heq => hinj j hj j' hj' ((htr j hj).symm.trans (heq.trans (htr j' hj')))⟩

end

end

end FFL.FirstOrder.Arithmetic
