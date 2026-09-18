module

public import AlphaCentauri.ToMathlib.ONote.FastGrowing

/-!
# The Hardy hierarchy `H_α`

The **Hardy hierarchy** `H_α : ℕ → ℕ` is the companion of the fast-growing hierarchy, sharing
its well-founded recursion on `ONote.fundamentalSequence`:
`H₀(n) = n`, `H_{α+1}(n) = H_α(n+1)`, `H_λ(n) = H_{λ[n]}(n)`. This file develops its growth
theory, `hstep` (the intrinsic step invariant relating `hardy` at consecutive budgets), the
additive decomposition of `hardy` along Cantor normal form addition and coefficient
multiplication, and a two-sided comparison against `fastGrowing`.
-/

@[expose] public section

namespace ONote

open ONote Ordinal

/-! ### Definition and values -/

section Basic

/-- The **Hardy hierarchy** `H_α : ℕ → ℕ` for ordinal notations `< ε₀`:
`H₀ = id`, `H_{α+1}(n) = H_α(n+1)`, `H_λ(n) = H_{λ[n]}(n)` (limit `λ`, via
`ONote.fundamentalSequence`). Same well-founded recursion as `ONote.fastGrowing`. -/
def hardy : ONote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => id
    | Sum.inl (some a), h =>
      have : a < o := by rw [lt_def, h.1]; exact Order.lt_succ _
      fun n => hardy a (n + 1)
    | Sum.inr f, h => fun n =>
      have : f n < o := (h.2.1 n).2.1
      hardy (f n) n
  termination_by o => o

private lemma eq_zero_of_fundamentalSequence_none
    {o : ONote} (e : fundamentalSequence o = Sum.inl none) :
    o = 0 := by
  have hp := fundamentalSequence_has_prop o; rw [e] at hp; exact hp

private lemma hardy_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    hardy o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => id
      | Sum.inl (some a), _ => fun n => hardy a (n + 1)
      | Sum.inr f, _ => fun n => hardy (f n) n := by
  subst x
  rw [hardy]

lemma hardy_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) : hardy o = id := by
  rw [hardy_def h]

lemma hardy_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    hardy o = fun n => hardy a (n + 1) := by
  rw [hardy_def h]

lemma hardy_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    hardy o = fun n => hardy (f n) n := by
  rw [hardy_def h]

@[simp]
lemma hardy_zero : hardy 0 = id :=
  hardy_zero' _ rfl

@[simp, grind =]
lemma hardy_one : hardy 1 = fun n => n + 1 := by
  rw [@hardy_succ 1 0 rfl]; funext n; rw [hardy_zero]; rfl

/-! ### Growth -/

theorem le_hardy (o : ONote) (n : ℕ) : n ≤ hardy o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e]; exact le_rfl
  · have hlt : a < o := lt_of_fundamentalSequence_succ e
    rw [hardy_succ o e]
    exact le_trans (Nat.le_succ n) (le_hardy a (n + 1))
  · have hlt : f n < o := fundamentalSequence_lt_of_limit e n
    rw [hardy_limit o e]
    exact le_hardy (f n) n
termination_by o
decreasing_by all_goals exact hlt

theorem hardy_le_of_reaches {x : ℕ} {b a : ONote} (h : Reaches x b a) :
    (∀ γ, Reaches x b γ → Monotone (hardy γ)) → hardy a x ≤ hardy b x := by
  induction h with
  | refl a => intro _; exact le_rfl
  | @succ b γ a hb _ ih =>
      intro hmono
      have hmγ : Monotone (hardy γ) := hmono γ (Reaches.succ hb (Reaches.refl γ))
      have iha : hardy a x ≤ hardy γ x := ih (fun δ hδ => hmono δ (Reaches.succ hb hδ))
      have heq : hardy b x = hardy γ (x + 1) := by rw [hardy_succ _ hb]
      rw [heq]; exact le_trans iha (hmγ (Nat.le_succ x))
  | @limit b a g hb _ ih =>
      intro hmono
      have ihg : hardy a x ≤ hardy (g x) x := ih (fun δ hδ => hmono δ (Reaches.limit hb hδ))
      have heq : hardy b x = hardy (g x) x := by rw [hardy_limit _ hb]
      rw [heq]; exact ihg

theorem hardy_monotone (o : ONote) : Monotone (hardy o) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e]; exact Nat.le_succ n
  · have hlt : a < o := lt_of_fundamentalSequence_succ e
    rw [hardy_succ o e]
    exact hardy_monotone a (Nat.le_succ (n + 1))
  · have hlt : f n < o := fundamentalSequence_lt_of_limit e n
    have hltn1 : f (n + 1) < o := fundamentalSequence_lt_of_limit e (n + 1)
    rw [hardy_limit o e]
    have mono_fn : Monotone (hardy (f n)) := hardy_monotone (f n)
    have step : hardy (f n) (n + 1) ≤ hardy (f (n + 1)) (n + 1) := by
      apply hardy_le_of_reaches (fastGrowing_bachmann_reach e n)
      intro γ hγ
      have hγo : γ < o := lt_of_le_of_lt (reaches_le hγ) hltn1
      exact hardy_monotone γ
    exact le_trans (mono_fn (Nat.le_succ n)) step
termination_by o
decreasing_by
  · exact hlt
  · exact hlt
  · exact hγo

theorem hardy_le_of_lt {x : ℕ} {a b : ONote} (ha : a.NF) (hb : b.NF)
    (hab : a < b) (hnorm : norm a ≤ x) : hardy a x ≤ hardy b x :=
  hardy_le_of_reaches (reaches_of_lt b hb a ha hab hnorm) (fun γ _ => hardy_monotone γ)

/-! ### Closed forms -/

@[simp, grind =]
lemma hardy_ofNat (k x : ℕ) : hardy (ofNat k) x = x + k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    simp only [hardy_succ _ (fundamentalSequence_ofNat_succ k)]
    rw [ih (x + 1)]; omega

/-- `oadd 1 1 0` represents `ω`. -/
lemma hardy_omega (n : ℕ) : hardy (oadd 1 1 0) n = 2 * n + 1 := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ofNat (i + 1)) := rfl
  have h1 : hardy (oadd 1 1 0) n = hardy (ofNat (n + 1)) n := by
    simp only [hardy_limit _ hfs]
  rw [h1, hardy_ofNat (n + 1) n]
  omega

end Basic

/-! ### The Hardy step -/

section Structure

/-- The fundamental sequence of a limit notation is everywhere nonzero. -/
private lemma fundamentalSequence_ne_zero_of_limit {o : ONote} {f : ℕ → ONote}
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

end Structure

/-! ### Comparison with the fast-growing hierarchy

Two-sided comparison of `hardy` at `ω`-powers against `fastGrowing`, up to the `ε₀`-tower
diagonal. Throughout, `oadd a 1 0` is the notation for `ω ^ a`. -/

section Comparison

instance : WellFoundedLT ONote := InvImage.wf repr Ordinal.lt_wf

theorem hardy_le_fastGrowing (o : ONote) (n : ℕ) (hn : 2 ≤ n) : hardy o n ≤ fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e, fastGrowing_zero' o e]; simp
  · have hlt : a < o := lt_of_fundamentalSequence_succ e
    rw [hardy_succ o e, fastGrowing_succ o e]
    have ih : hardy a (n + 1) ≤ fastGrowing a (n + 1) := hardy_le_fastGrowing a (n + 1) (by omega)
    have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
    have hmono : (fastGrowing a)^[2] n ≤ (fastGrowing a)^[n] n :=
      Function.monotone_iterate_of_id_le hexp hn n
    have h2it : (fastGrowing a)^[2] n = fastGrowing a (fastGrowing a n) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]; simp
    have hfn : n + 1 ≤ fastGrowing a n := lt_fastGrowing a (by omega)
    have hstep : fastGrowing a (n + 1) ≤ fastGrowing a (fastGrowing a n) :=
      fastGrowing_monotone a hfn
    calc hardy a (n + 1) ≤ fastGrowing a (n + 1) := ih
      _ ≤ fastGrowing a (fastGrowing a n) := hstep
      _ = (fastGrowing a)^[2] n := h2it.symm
      _ ≤ (fastGrowing a)^[n] n := hmono
  · have hlt : f n < o := fundamentalSequence_lt_of_limit e n
    rw [hardy_limit o e, fastGrowing_limit o e]
    exact hardy_le_fastGrowing (f n) n hn
termination_by o
decreasing_by all_goals exact hlt

/-! ### An arbitrary exponent

At arbitrary `a : ONote`, `H_{ω^a}(n) + 1 ≤ f_a(n+1)` unconditionally, tightening to a two-sided
bracket once the coefficient composition law is in place.
-/

private lemma hardy_omega_pow_coeff_comp (b : ONote) (k n : ℕ) :
    hardy (oadd b (Nat.succPNat (k + 1)) 0) n
      = hardy (oadd b (Nat.succPNat k) 0) (hardy (oadd b 1 0) n) := by
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    have e1 : oadd (0 : ONote) (Nat.succPNat (k + 1)) 0 = ofNat (k + 2) := (ofNat_succ (k + 1)).symm
    have e2 : oadd (0 : ONote) (Nat.succPNat k) 0 = ofNat (k + 1) := (ofNat_succ k).symm
    have e3 : oadd (0 : ONote) 1 0 = ofNat 1 := (ofNat_succ 0).symm
    rw [e1, e2, e3]
    simp only [hardy_ofNat]
    omega
  · exact hardy_oadd_coeff_step b hb k n

private lemma hardy_omega_pow_coeff_le {b : ONote}
    (hbase : ∀ n, hardy (oadd b 1 0) n + 1 ≤ fastGrowing b (n + 1)) (m n : ℕ) :
    hardy (oadd b (Nat.succPNat m) 0) n + 1 ≤ (fastGrowing b)^[m + 1] (n + 1) := by
  induction m generalizing n with
  | zero =>
      change hardy (oadd b 1 0) n + 1 ≤ fastGrowing b (n + 1)
      exact hbase n
  | succ m ih =>
      rw [hardy_omega_pow_coeff_comp b m n]
      have h2 : hardy (oadd b 1 0) n + 1 ≤ fastGrowing b (n + 1) := hbase n
      calc hardy (oadd b (Nat.succPNat m) 0) (hardy (oadd b 1 0) n) + 1
          ≤ (fastGrowing b)^[m + 1] (hardy (oadd b 1 0) n + 1) := ih _
        _ ≤ (fastGrowing b)^[m + 1] (fastGrowing b (n + 1)) :=
            (fastGrowing_monotone b).iterate (m + 1) h2
        _ = (fastGrowing b)^[m + 1 + 1] (n + 1) :=
            (Function.iterate_succ_apply (fastGrowing b) (m + 1) (n + 1)).symm

section
variable (a : ONote) (n : ℕ)

theorem hardy_omega_pow_add_one_le : hardy (oadd a 1 0) n + 1 ≤ fastGrowing a (n + 1) := by
  induction a using WellFoundedLT.induction generalizing n with
  | _ a ih =>
    rcases ha : fundamentalSequence a with (_ | b) | f
    · have h0 : a = 0 := eq_zero_of_fundamentalSequence_none ha
      subst h0
      have hfs1 : fundamentalSequence (oadd 0 1 0) = Sum.inl (some 0) := rfl
      rw [hardy_succ (oadd 0 1 0) hfs1, hardy_zero, fastGrowing_zero]
      simp only [id_eq]; omega
    · have hlt : b < a := lt_of_fundamentalSequence_succ ha
      have homega : fundamentalSequence (oadd a 1 0) = Sum.inr (fun i => oadd b i.succPNat 0) :=
        fundamentalSequence_omega_pow_succ ha
      rw [hardy_limit (oadd a 1 0) homega, fastGrowing_succ a ha]
      exact hardy_omega_pow_coeff_le (ih b hlt) n n
    · have hlim_h : fundamentalSequence (oadd a 1 0) = Sum.inr (fun i => oadd (f i) 1 0) :=
        fundamentalSequence_omega_pow_limit ha
      have hlt : f n < a := fundamentalSequence_lt_of_limit ha n
      rw [hardy_limit (oadd a 1 0) hlim_h, fastGrowing_limit a ha]
      calc hardy (oadd (f n) 1 0) n + 1
          ≤ fastGrowing (f n) (n + 1) := ih (f n) hlt n
        _ ≤ fastGrowing (f (n + 1)) (n + 1) :=
            fastGrowing_le_of_reaches (Nat.succ_le_succ (Nat.zero_le n))
              (fastGrowing_bachmann_reach ha n)

theorem hardy_omega_pow_lt_fastGrowing : hardy (oadd a 1 0) n < fastGrowing a (n + 1) := by
  have h := hardy_omega_pow_add_one_le a n
  omega

private lemma iterate_le_iterate_of_le {F g : ℕ → ℕ} (hFg : ∀ y, F y ≤ g y)
    (hg : Monotone g) (m x : ℕ) : F^[m] x ≤ g^[m] x := by
  induction m generalizing x with
  | zero => exact le_rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact le_trans (ih (F x)) (hg.iterate m (hFg x))

theorem fastGrowing_le_hardy_omega_pow : fastGrowing a n ≤ hardy (oadd a 1 0) n := by
  induction a using WellFoundedLT.induction generalizing n with
  | _ a ih =>
    rcases ha : fundamentalSequence a with (_ | b) | f
    · have h0 : a = 0 := eq_zero_of_fundamentalSequence_none ha
      subst h0
      have hfs1 : fundamentalSequence (oadd 0 1 0) = Sum.inl (some 0) := rfl
      rw [fastGrowing_zero, hardy_succ (oadd 0 1 0) hfs1, hardy_zero]
      simp only [id_eq]; omega
    · have hlt : b < a := lt_of_fundamentalSequence_succ ha
      have homega : fundamentalSequence (oadd a 1 0) = Sum.inr (fun i => oadd b i.succPNat 0) :=
        fundamentalSequence_omega_pow_succ ha
      rw [fastGrowing_succ a ha, hardy_limit (oadd a 1 0) homega]
      change (fastGrowing b)^[n] n ≤ hardy (oadd b n.succPNat 0) n
      rcases eq_or_ne b 0 with hb0 | hb0
      · subst hb0
        rw [fastGrowing_zero,
          show oadd (0 : ONote) n.succPNat 0 = ofNat (n + 1) from (ofNat_succ n).symm,
          hardy_ofNat, Nat.succ_iterate]
        omega
      · rw [hardy_oadd_coeff b hb0 n n]
        have hFg : ∀ y, fastGrowing b y ≤ hardy (oadd b 1 0) y := ih b hlt
        have hg : Monotone (hardy (oadd b 1 0)) := hardy_monotone _
        calc (fastGrowing b)^[n] n
            ≤ (hardy (oadd b 1 0))^[n] n := iterate_le_iterate_of_le hFg hg n n
          _ ≤ (hardy (oadd b 1 0))^[n + 1] n := by
              rw [Function.iterate_succ_apply']; exact le_hardy (oadd b 1 0) _
    · have hlim : fundamentalSequence (oadd a 1 0) = Sum.inr (fun i => oadd (f i) 1 0) :=
        fundamentalSequence_omega_pow_limit ha
      have hlt : f n < a := fundamentalSequence_lt_of_limit ha n
      rw [fastGrowing_limit a ha, hardy_limit (oadd a 1 0) hlim]
      exact ih (f n) hlt n

theorem hardy_omega_pow_bracket :
    fastGrowing a n ≤ hardy (oadd a 1 0) n ∧ hardy (oadd a 1 0) n < fastGrowing a (n + 1) :=
  ⟨fastGrowing_le_hardy_omega_pow a n, hardy_omega_pow_lt_fastGrowing a n⟩

end

theorem fastGrowing_iterate_le_hardy_coeff (a : ONote) (ha : a ≠ 0) (k n : ℕ) :
    (fastGrowing a)^[k + 1] n ≤ hardy (oadd a k.succPNat 0) n := by
  rw [hardy_oadd_coeff a ha k n]
  exact iterate_le_iterate_of_le (fastGrowing_le_hardy_omega_pow a) (hardy_monotone _) (k + 1) n

private lemma iterate_offset_le {g F : ℕ → ℕ} (hF : Monotone F) (h : ∀ y, g y + 1 ≤ F (y + 1))
    (m y : ℕ) : g^[m] y + 1 ≤ F^[m] (y + 1) := by
  induction m generalizing y with
  | zero => exact le_rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact le_trans (ih (g y)) (hF.iterate m (h y))

theorem hardy_coeff_add_one_le (a : ONote) (ha : a ≠ 0) (k n : ℕ) :
    hardy (oadd a k.succPNat 0) n + 1 ≤ (fastGrowing a)^[k + 1] (n + 1) := by
  rw [hardy_oadd_coeff a ha k n]
  exact iterate_offset_le (fastGrowing_monotone a) (hardy_omega_pow_add_one_le a) (k + 1) n

theorem hardy_omega_pow_coeff_bracket (a : ONote) (ha : a ≠ 0) (k n : ℕ) :
    (fastGrowing a)^[k + 1] n ≤ hardy (oadd a k.succPNat 0) n
      ∧ hardy (oadd a k.succPNat 0) n < (fastGrowing a)^[k + 1] (n + 1) :=
  ⟨fastGrowing_iterate_le_hardy_coeff a ha k n,
    Nat.lt_of_succ_le (hardy_coeff_add_one_le a ha k n)⟩

/-! ### The `ε₀`-diagonal capstone

`fastGrowingε₀ i = f_{tower i}(i)` and `tower (i+1) = ω^{tower i}`, so the `ω^a`-bracket at
`a = tower i`, argument `i`, pins the `ε₀`-diagonal against the Hardy function at the next
tower level. -/

theorem fastGrowingε₀_le_hardy_tower_succ (i : ℕ) : fastGrowingε₀ i ≤ hardy (tower (i + 1)) i := by
  have h : fastGrowing (tower i) i ≤ hardy (oadd (tower i) 1 0) i :=
    (hardy_omega_pow_bracket (tower i) i).1
  rw [← tower_succ] at h
  exact h

theorem hardy_tower_succ_lt_fastGrowing (i : ℕ) :
    hardy (tower (i + 1)) i < fastGrowing (tower i) (i + 1) := by
  have h := (hardy_omega_pow_bracket (tower i) i).2
  rw [← tower_succ] at h
  exact h

end Comparison

end ONote
