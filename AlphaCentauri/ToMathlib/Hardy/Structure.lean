module

public import AlphaCentauri.ToMathlib.Hardy.Basic

/-!
# Hardy hierarchy — structural laws

`hstep`, the intrinsic step invariant relating `hardy` at consecutive budgets, and the
additive decomposition of `hardy` along Cantor normal form addition and coefficient
multiplication.
-/

@[expose] public section

namespace ONote

open ONote Ordinal

/-! ### The Hardy step -/

/-- The fundamental sequence of a limit notation is everywhere nonzero. -/
lemma fundamentalSequence_ne_zero_of_limit {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (i : ℕ) : f i ≠ 0 := by
  induction o with
  | zero => simp [fundamentalSequence] at h
  | oadd a m b iha ihb =>
    rw [fundamentalSequence] at h
    split at h
    · injection h with h'; subst h'; exact (oadd_pos _ _ _).ne'
    · exact (Sum.inl_ne_inr h).elim
    · split at h <;>
        first
          | exact (Sum.inl_ne_inr h).elim
          | (injection h with h'; subst h'; simp only []; exact (oadd_pos _ _ _).ne')

/-- The Hardy step: passes through the limit stages of `o`'s fundamental-sequence descent and
stops after exactly one successor stage, at budget `n`. -/
def hstep : ONote → ℕ → ONote
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => fun _ => 0
    | Sum.inl (some a), _ => fun _ => a
    | Sum.inr f, h => fun n =>
      have : f n < o := (h.2.1 n).2.1
      hstep (f n) n
  termination_by o => o

private lemma hstep_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    hstep o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ONote)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => fun _ => 0
      | Sum.inl (some a), _ => fun _ => a
      | Sum.inr f, _ => fun n => hstep (f n) n := by
  subst x; rw [hstep]

lemma hstep_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) : hstep o = fun _ => a := by
  rw [hstep_def h]

lemma hstep_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    hstep o = fun n => hstep (f n) n := by
  rw [hstep_def h]

theorem hardy_hstep (o : ONote) (n : ℕ) (h : o ≠ 0) : hardy o n = hardy (hstep o n) (n + 1) := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · exact absurd (eq_zero_of_fundamentalSequence_none e) h
  · rw [hardy_succ o e, hstep_succ o e]
  · have hlt : f n < o := fundamentalSequence_lt_of_limit e n
    rw [hardy_limit o e, hstep_limit o e]
    exact hardy_hstep (f n) n (fundamentalSequence_ne_zero_of_limit e n)
termination_by o
decreasing_by exact hlt

/-! ### Peeling the tail -/

theorem hardy_oadd_tail (a : ONote) (m : ℕ+) (b : ONote) (n : ℕ) :
    hardy (oadd a m b) n = hardy (oadd a m 0) (hardy b n) := by
  rcases e : fundamentalSequence b with (_ | b') | f
  · have hb0 : b = 0 := eq_zero_of_fundamentalSequence_none e
    rw [hardy_zero' b e, hb0]; rfl
  · have hlt : b' < b := lt_of_fundamentalSequence_succ e
    have hfs : fundamentalSequence (oadd a m b) = Sum.inl (some (oadd a m b')) := by
      conv_lhs => rw [fundamentalSequence]; rw [e]
    rw [hardy_succ _ hfs, hardy_succ b e]
    exact hardy_oadd_tail a m b' (n + 1)
  · have hlt : f n < b := fundamentalSequence_lt_of_limit e n
    have hfs : fundamentalSequence (oadd a m b) = Sum.inr (fun i => oadd a m (f i)) := by
      conv_lhs => rw [fundamentalSequence]; rw [e]
    rw [hardy_limit _ hfs, hardy_limit b e]
    exact hardy_oadd_tail a m (f n) n
termination_by b
decreasing_by all_goals exact hlt

/-! ### Coefficient composition -/

theorem hardy_oadd_coeff_step (b : ONote) (hb : b ≠ 0) (k x : ℕ) :
    hardy (oadd b (k + 1).succPNat 0) x
      = hardy (oadd b k.succPNat 0) (hardy (oadd b 1 0) x) := by
  rcases e : fundamentalSequence b with (_ | b') | f
  · exact absurd (eq_zero_of_fundamentalSequence_none e) hb
  · have hfs : fundamentalSequence (oadd b (k + 1).succPNat 0)
        = Sum.inr (fun i => oadd b k.succPNat (oadd b' i.succPNat 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [e]; rfl
    rw [hardy_limit _ hfs]
    change hardy (oadd b k.succPNat (oadd b' x.succPNat 0)) x
        = hardy (oadd b k.succPNat 0) (hardy (oadd b 1 0) x)
    rw [hardy_oadd_tail b k.succPNat (oadd b' x.succPNat 0) x,
        hardy_limit (oadd b 1 0) (fundamentalSequence_omega_pow_succ e)]
  · have hfs : fundamentalSequence (oadd b (k + 1).succPNat 0)
        = Sum.inr (fun i => oadd b k.succPNat (oadd (f i) 1 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [e]; rfl
    rw [hardy_limit _ hfs]
    change hardy (oadd b k.succPNat (oadd (f x) 1 0)) x
        = hardy (oadd b k.succPNat 0) (hardy (oadd b 1 0) x)
    rw [hardy_oadd_tail b k.succPNat (oadd (f x) 1 0) x,
        hardy_limit (oadd b 1 0) (fundamentalSequence_omega_pow_limit e)]

/-- `oadd b k.succPNat 0` represents `ω^b · (k + 1)`. -/
theorem hardy_oadd_coeff (b : ONote) (hb : b ≠ 0) (k x : ℕ) :
    hardy (oadd b k.succPNat 0) x = (hardy (oadd b 1 0))^[k + 1] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [hardy_oadd_coeff_step b hb k x, ih (hardy (oadd b 1 0) x), ← Function.iterate_succ_apply]

/-- `oadd e p 0` represents `ω^e · p`. -/
lemma hardy_single_coeff (e : ONote) (he : e ≠ 0) (p : ℕ+) (x : ℕ) :
    hardy (oadd e p 0) x = (hardy (oadd e 1 0))^[(p : ℕ)] x := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k.succPNat := ⟨p.natPred, (PNat.succPNat_natPred p).symm⟩
  rw [hardy_oadd_coeff e he k x, Nat.succPNat_coe]

/-! ### The additive composition law

`H_{c+d}(x) = H_c(H_d(x))` when `d` lies strictly below `c`'s least exponent (non-absorbing CNF
concatenation).
-/

/-- The least (trailing) exponent of a notation's Cantor normal form (`0` for `0`). -/
def lastExp : ONote → ONote
  | 0 => 0
  | oadd e _ a => match a with
    | 0 => e
    | oadd _ _ _ => lastExp a

@[simp] theorem lastExp_zero : lastExp 0 = 0 := rfl
@[simp] theorem lastExp_oadd_zero (e n) : lastExp (oadd e n 0) = e := rfl

@[grind =]
lemma lastExp_oadd_ne {e : ONote} {n : ℕ+} {a : ONote} (h : a ≠ 0) :
    lastExp (oadd e n a) = lastExp a := by
  cases a with
  | zero => exact absurd rfl h
  | oadd e' n' a' => rfl

/-- `addAux` concatenates (no merge or absorption) when the right operand's leading exponent
is strictly below `e`. -/
private lemma addAux_concat {e : ONote} (he : e.NF) {n : ℕ+} {o : ONote} (ho : o.NF)
    (h : o = 0 ∨ ∀ e' n' a', o = oadd e' n' a' → e'.repr < e.repr) :
    addAux e n o = oadd e n o := by
  match o, ho, h with
  | 0, _, _ => rfl
  | oadd e' n' a', ho', h' =>
    have hlt : e'.repr < e.repr := by
      rcases h' with h0 | hf
      · exact absurd h0 (by simp)
      · exact hf e' n' a' rfl
    have hee' : ONote.cmp e e' = Ordering.gt :=
      (@ONote.cmp_compares e e' he ho'.fst).eq_gt.2 hlt
    simp only [addAux, hee']

/-- The least exponent of a nonzero notation lies below any bound it is `NFBelow`. -/
private lemma lastExp_repr_lt {o : ONote} {b : Ordinal} (hb : NFBelow o b) (h : o ≠ 0) :
    (lastExp o).repr < b := by
  induction o generalizing b with
  | zero => exact absurd rfl h
  | oadd e n a _ iha =>
    rcases eq_or_ne a 0 with ha | ha
    · subst ha; rw [lastExp_oadd_zero]; exact hb.lt
    · rw [lastExp_oadd_ne ha]
      exact lt_trans (iha hb.snd ha) hb.lt

/-- Convert an `NFBelow` fact into the leading-exponent bound `addAux_concat` consumes. -/
private lemma nfBelow_concat {o : ONote} {b : Ordinal} (h : NFBelow o b) :
    o = 0 ∨ ∀ e' n' a', o = oadd e' n' a' → e'.repr < b := by
  cases o with
  | zero => left; rfl
  | oadd e' n' a' => right; intro e'' n'' a'' heq; cases heq; exact h.lt

theorem hardy_add_comp (c : ONote) (hc : c.NF) (d : ONote) (hd : d.NF)
    (hcond : d = 0 ∨ d.repr < ω ^ (lastExp c).repr) (x : ℕ) :
    hardy (c + d) x = hardy c (hardy d x) := by
  induction c generalizing d x with
  | zero =>
    change hardy ((0 : ONote) + d) x = hardy (0 : ONote) (hardy d x)
    rw [ONote.zero_add, hardy_zero]; rfl
  | oadd e n a _ iha =>
    have := hc
    rcases eq_or_ne d 0 with hd0 | hd0
    · subst hd0
      have hadd : oadd e n a + 0 = oadd e n a :=
        repr_inj.mp (by rw [repr_add, repr_zero, add_zero])
      rw [hadd, hardy_zero]; rfl
    have he : e.NF := hc.fst
    have hba : NFBelow a e.repr := hc.snd'
    have ha : a.NF := ⟨⟨e.repr, hba⟩⟩
    have hle : (lastExp (oadd e n a)).repr ≤ e.repr := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · subst ha0; rw [lastExp_oadd_zero]
      · rw [lastExp_oadd_ne ha0]; exact le_of_lt (lastExp_repr_lt hba ha0)
    have hdlt_e : d.repr < ω ^ e.repr := by
      rcases hcond with h0 | hlt
      · exact absurd h0 hd0
      · exact lt_of_lt_of_le hlt (opow_le_opow_right omega0_pos hle)
    have hbd : NFBelow d e.repr := NF.below_of_lt' hdlt_e hd
    have hbad : NFBelow (a + d) e.repr := add_nfBelow hba hbd
    have hcc : addAux e n (a + d) = oadd e n (a + d) :=
      addAux_concat he (⟨⟨_, hbad⟩⟩) (nfBelow_concat hbad)
    rw [oadd_add, hcc, hardy_oadd_tail e n (a + d) x]
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0; rw [ONote.zero_add]
    · have ihcond : d = 0 ∨ d.repr < ω ^ (lastExp a).repr := by
        right
        rcases hcond with h0 | hlt
        · exact absurd h0 hd0
        · rwa [lastExp_oadd_ne ha0] at hlt
      rw [iha ha d hd ihcond x, hardy_oadd_tail e n a (hardy d x)]

end ONote
