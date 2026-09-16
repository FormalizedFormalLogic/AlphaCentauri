module

public import Mathlib.SetTheory.Ordinal.Notation

/-!
# Fast-growing hierarchy over `ONote`

Monotonicity and expansiveness of `ONote.fastGrowing`, the structural `Reaches` descent
relation on fundamental sequences, and index monotonicity of the hierarchy along it.
-/

@[expose] public section

namespace ONote

open ONote Ordinal

variable {o a b : ONote} {f g : ℕ → ONote} {m n x : ℕ}

lemma lt_of_fundamentalSequence_succ (h : fundamentalSequence o = Sum.inl (some a)) : a < o := by
  have hp := fundamentalSequence_has_prop o
  rw [h] at hp
  rw [lt_def, hp.1]; exact Order.lt_succ _

lemma fundamentalSequence_lt_of_limit (h : fundamentalSequence o = Sum.inr g) (n : ℕ) :
    g n < o := by
  have hp := fundamentalSequence_has_prop o
  rw [h] at hp
  exact (hp.2.1 n).2.1

theorem le_fastGrowing (o : ONote) (n : ℕ) : n ≤ fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · -- `o = 0`: `fastGrowing o = Nat.succ`
    rw [fastGrowing_zero' o e]
    exact Nat.le_succ n
  · -- successor: `fastGrowing o n = (fastGrowing a)^[n] n`, `a < o`
    have hlt : a < o := lt_of_fundamentalSequence_succ e
    rw [fastGrowing_succ o e]
    exact Function.id_le_iterate_of_id_le (fun m => le_fastGrowing a m) n n
  · -- limit: `fastGrowing o n = fastGrowing (f n) n`, `f n < o`
    have hlt : f n < o := fundamentalSequence_lt_of_limit e n
    rw [fastGrowing_limit o e]
    exact le_fastGrowing (f n) n
termination_by o
decreasing_by all_goals exact hlt

lemma id_le_fastGrowing (o : ONote) : (id : ℕ → ℕ) ≤ fastGrowing o :=
  fun m => le_fastGrowing o m

theorem lt_fastGrowing (o : ONote) (hn : 1 ≤ n) : n < fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [fastGrowing_zero' o e]
    exact Nat.lt_succ_self n
  · have hlt : a < o := lt_of_fundamentalSequence_succ e
    rw [fastGrowing_succ o e]
    -- `n < f_a n = (f_a)^[1] n ≤ (f_a)^[n] n`
    have hstep : fastGrowing a n ≤ (fastGrowing a)^[n] n := by
      have hmono := Function.monotone_iterate_of_id_le (id_le_fastGrowing a) hn
      simpa using hmono n
    exact lt_of_lt_of_le (lt_fastGrowing a hn) hstep
  · have hlt : f n < o := fundamentalSequence_lt_of_limit e n
    rw [fastGrowing_limit o e]
    exact lt_fastGrowing (f n) hn
termination_by o
decreasing_by all_goals exact hlt

lemma fastGrowing_le_succ_index (h : fundamentalSequence o = Sum.inl (some a)) (hn : 1 ≤ n) :
    fastGrowing a n ≤ fastGrowing o n := by
  rw [fastGrowing_succ o h]
  simpa using (Function.monotone_iterate_of_id_le (id_le_fastGrowing a) hn) n

/-- `Reaches x p r`: from `p`, one can step down to `r` through `fundamentalSequence`,
taking a predecessor step at successor notations and an index-`x` step at limit notations. -/
inductive Reaches (x : ℕ) : ONote → ONote → Prop
  | refl (a : ONote) : Reaches x a a
  | succ {p q r : ONote} (h : fundamentalSequence p = Sum.inl (some q))
      (hr : Reaches x q r) : Reaches x p r
  | limit {p r : ONote} {g : ℕ → ONote} (h : fundamentalSequence p = Sum.inr g)
      (hr : Reaches x (g x) r) : Reaches x p r

lemma Reaches.trans {c : ONote} (h1 : Reaches x a b) (h2 : Reaches x b c) : Reaches x a c := by
  induction h1 with
  | refl a => exact h2
  | succ h _ ih => exact Reaches.succ h (ih h2)
  | limit h _ ih => exact Reaches.limit h (ih h2)

theorem fastGrowing_le_of_reaches {p r : ONote} (hx : 1 ≤ x) (h : Reaches x p r) :
    fastGrowing r x ≤ fastGrowing p x := by
  induction h with
  | refl a => exact le_rfl
  | succ hb _ ih => exact le_trans ih (fastGrowing_le_succ_index hb hx)
  | limit hb _ ih => rw [fastGrowing_limit _ hb]; exact ih

@[grind →]
lemma reaches_le {p r : ONote} (h : Reaches x p r) : r ≤ p := by
  induction h with
  | refl a => exact le_rfl
  | @succ p q r hb _ ih =>
      exact le_trans ih (lt_of_fundamentalSequence_succ hb).le
  | @limit p r g hb _ ih =>
      exact le_trans ih (fundamentalSequence_lt_of_limit hb x).le

/-! ### Structural Bachmann reachability

`fundamentalSequence`-level structural descent facts used to establish index monotonicity
of the fast-growing hierarchy. -/

-- `@[grind =]` fails to find patterns since `b'`/`h` don't occur in the LHS pattern;
-- `@[grind =>]` treats it as a forward implication instead.
@[grind =>]
lemma fundamentalSequence_oadd_succ {m : ℕ+} {b' : ONote}
    (h : fundamentalSequence b = Sum.inl (some b')) :
    fundamentalSequence (oadd a m b) = Sum.inl (some (oadd a m b')) := by
  conv_lhs => rw [fundamentalSequence]; rw [h]

-- `@[grind =]` fails (same reason as `fundamentalSequence_oadd_succ`); use `@[grind =>]`.
@[grind =>]
lemma fundamentalSequence_oadd_limit {m : ℕ+} {h : ℕ → ONote}
    (hb : fundamentalSequence b = Sum.inr h) :
    fundamentalSequence (oadd a m b) = Sum.inr (fun i => oadd a m (h i)) := by
  conv_lhs => rw [fundamentalSequence]; rw [hb]

-- `@[grind →]` fails to find a trigger pattern for the inductive `Reaches` hypothesis;
-- `@[grind =>]` works instead.
@[grind =>]
lemma Reaches.oadd_tail {m : ℕ+} {d' d : ONote} (h : Reaches x d' d) :
    Reaches x (oadd a m d') (oadd a m d) := by
  induction h with
  | refl c => exact Reaches.refl _
  | succ hb _ ih => exact Reaches.succ (fundamentalSequence_oadd_succ hb) ih
  | limit hb _ ih => exact Reaches.limit (fundamentalSequence_oadd_limit hb) ih

lemma reaches_zero (o : ONote) (x : ℕ) : Reaches x o 0 := by
  rcases e : fundamentalSequence o with (_ | a) | g
  · have ho : o = 0 := by have hp := fundamentalSequence_has_prop o; rw [e] at hp; exact hp
    rw [ho]; exact Reaches.refl 0
  · have hlt : a < o := lt_of_fundamentalSequence_succ e
    exact Reaches.succ e (reaches_zero a x)
  · have hlt : g x < o := fundamentalSequence_lt_of_limit e x
    exact Reaches.limit e (reaches_zero (g x) x)
termination_by o
decreasing_by all_goals exact hlt

/-- `ω^e·(j+2)` descends to `ω^e·(j+1)` with any budget. -/
lemma reaches_coeff_step (e : ONote) (j x : ℕ) :
    Reaches x (oadd e (j + 1).succPNat 0) (oadd e j.succPNat 0) := by
  rcases he : fundamentalSequence e with (_ | e') | p
  · have h0 : e = 0 := by have hp := fundamentalSequence_has_prop e; rw [he] at hp; exact hp
    subst h0
    refine Reaches.succ ?_ (Reaches.refl _)
    conv_lhs => rw [fundamentalSequence]
    rfl
  · have hlim : fundamentalSequence (oadd e (j + 1).succPNat 0)
        = Sum.inr (fun i => oadd e j.succPNat (oadd e' i.succPNat 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [he]; rfl
    exact Reaches.limit hlim (Reaches.oadd_tail (reaches_zero (oadd e' x.succPNat 0) x))
  · have hlim : fundamentalSequence (oadd e (j + 1).succPNat 0)
        = Sum.inr (fun i => oadd e j.succPNat (oadd (p i) 1 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [he]; rfl
    exact Reaches.limit hlim (Reaches.oadd_tail (reaches_zero (oadd (p x) 1 0) x))

/-- `ω^e·(j+1)` descends to `ω^e·1`. -/
lemma reaches_coeff_chain (e : ONote) (j x : ℕ) :
    Reaches x (oadd e j.succPNat 0) (oadd e (0 : ℕ).succPNat 0) := by
  induction j with
  | zero => exact Reaches.refl _
  | succ j ih => exact (reaches_coeff_step e j x).trans ih

/-- Fundamental sequence of `ω^{successor exponent}`. -/
-- `@[grind =]` fails (same reason as `fundamentalSequence_oadd_succ`); use `@[grind =>]`.
@[grind =>]
lemma fundamentalSequence_omega_pow_succ (he : fundamentalSequence o = Sum.inl (some a)) :
    fundamentalSequence (oadd o 1 0) = Sum.inr (fun i => oadd a i.succPNat 0) := by
  conv_lhs => rw [fundamentalSequence]
  rw [he]; rfl

/-- Fundamental sequence of `ω^{limit exponent}`. -/
-- `@[grind =]` fails (same reason as `fundamentalSequence_oadd_succ`); use `@[grind =>]`.
@[grind =>]
lemma fundamentalSequence_omega_pow_limit {q : ℕ → ONote}
    (he : fundamentalSequence o = Sum.inr q) :
    fundamentalSequence (oadd o 1 0) = Sum.inr (fun i => oadd (q i) 1 0) := by
  conv_lhs => rw [fundamentalSequence]
  rw [he]; rfl

/-- A structural reach on exponents lifts through `ω^·`. -/
lemma reaches_omega_pow_lift {p r : ONote} (h : Reaches x p r) :
    Reaches x (oadd p 1 0) (oadd r 1 0) := by
  induction h with
  | refl c => exact Reaches.refl _
  | @succ p q r hb _ ih =>
      refine Reaches.limit (fundamentalSequence_omega_pow_succ hb) ?_
      exact (reaches_coeff_chain q x x).trans ih
  | @limit p r g hb _ ih =>
      exact Reaches.limit (fundamentalSequence_omega_pow_limit hb) ih

@[simp, grind =]
lemma fundamentalSequence_ofNat_succ (k : ℕ) :
    fundamentalSequence (ofNat (k + 1)) = Sum.inl (some (ofNat k)) := by
  cases k with
  | zero => rfl
  | succ k' => rfl

lemma fastGrowing_succ_chain_mono
    (hchain : ∀ k, fundamentalSequence (g (k + 1)) = Sum.inl (some (g k)))
    (hmn : m ≤ n) (hx : 1 ≤ x) :
    fastGrowing (g m) x ≤ fastGrowing (g n) x := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact le_trans ih (fastGrowing_le_succ_index (hchain n) hx)

/-- The `ofNat` instance of `fastGrowing_succ_chain_mono`. -/
lemma fastGrowing_ofNat_mono (hmn : m ≤ n) (hx : 1 ≤ x) :
    fastGrowing (ofNat m) x ≤ fastGrowing (ofNat n) x :=
  fastGrowing_succ_chain_mono fundamentalSequence_ofNat_succ hmn hx

/-- **Bachmann reachability**: for a limit `o` with fundamental sequence `f`, `f (n + 1)`
reaches `f n` with budget `n + 1`. -/
theorem fastGrowing_bachmann_reach {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    Reaches (n + 1) (f (n + 1)) (f n) := by
  cases o with
  | zero => exact (Sum.inl_ne_inr h).elim
  | oadd a m b =>
    rcases hb : fundamentalSequence b with (_ | b') | hbf
    · -- b = 0 : leading-term cases
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0 : `oadd 0 m 0` is a successor → contradicts the limit hypothesis
        rcases hm : m.natPred with _ | k
        · rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inl_ne_inr h).elim
        · rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inl_ne_inr h).elim
      · -- a successor (predecessor a')
        rcases hm : m.natPred with _ | k
        · have hf : f = fun i => oadd a' i.succPNat 0 := by
            rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inr.inj h).symm
          rw [hf]; exact reaches_coeff_step a' n (n + 1)
        · have hf : f = fun i => oadd a k.succPNat (oadd a' i.succPNat 0) := by
            rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inr.inj h).symm
          rw [hf]; exact Reaches.oadd_tail (reaches_coeff_step a' n (n + 1))
      · -- a limit (fundamental sequence p) : the ω^{limit} residue, via exponent lifting
        rcases hm : m.natPred with _ | k
        · have hf : f = fun i => oadd (p i) 1 0 := by
            rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inr.inj h).symm
          rw [hf]; exact reaches_omega_pow_lift (fastGrowing_bachmann_reach ha n)
        · have hf : f = fun i => oadd a k.succPNat (oadd (p i) 1 0) := by
            rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inr.inj h).symm
          rw [hf]
          exact Reaches.oadd_tail (reaches_omega_pow_lift (fastGrowing_bachmann_reach ha n))
    · -- b a successor ⟹ `oadd a m b` is a successor → contradiction
      rw [fundamentalSequence_oadd_succ hb] at h; exact (Sum.inl_ne_inr h).elim
    · -- b a limit : descend the tail, recursing on b
      have hf : f = fun i => oadd a m (hbf i) := by
        rw [fundamentalSequence_oadd_limit hb] at h; exact (Sum.inr.inj h).symm
      rw [hf]; exact Reaches.oadd_tail (fastGrowing_bachmann_reach hb n)

lemma fastGrowing_fundSeq_step
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    fastGrowing (f n) (n + 1) ≤ fastGrowing (f (n + 1)) (n + 1) :=
  fastGrowing_le_of_reaches (Nat.succ_le_succ (Nat.zero_le n)) (fastGrowing_bachmann_reach h n)

lemma fastGrowing_le_succ (o : ONote) (n : ℕ) : fastGrowing o n ≤ fastGrowing o (n + 1) := by
  rcases e : fundamentalSequence o with (_ | a) | g
  · rw [fastGrowing_zero' o e]
    exact Nat.le_succ _
  · -- successor: `(f_a)^[n] n ≤ (f_a)^[n+1] (n+1)`
    have hlt : a < o := lt_of_fundamentalSequence_succ e
    rw [fastGrowing_succ o e]
    have hmono_a : Monotone (fastGrowing a) :=
      monotone_nat_of_le_succ fun k => fastGrowing_le_succ a k
    calc (fastGrowing a)^[n] n
        ≤ (fastGrowing a)^[n] (n + 1) := hmono_a.iterate n (Nat.le_succ n)
      _ ≤ (fastGrowing a)^[n + 1] (n + 1) := by
            rw [Function.iterate_succ_apply']
            exact le_fastGrowing a _
  · -- limit: `f_{g n}(n) ≤ f_{g (n+1)}(n+1)`
    have hlt : g n < o := fundamentalSequence_lt_of_limit e n
    rw [fastGrowing_limit o e]
    have hmono_gn : Monotone (fastGrowing (g n)) :=
      monotone_nat_of_le_succ fun k => fastGrowing_le_succ (g n) k
    calc fastGrowing (g n) n
        ≤ fastGrowing (g n) (n + 1) := hmono_gn (Nat.le_succ n)
      _ ≤ fastGrowing (g (n + 1)) (n + 1) := fastGrowing_fundSeq_step e n
termination_by o
decreasing_by all_goals exact hlt

theorem fastGrowing_monotone (o : ONote) : Monotone (fastGrowing o) :=
  monotone_nat_of_le_succ (fastGrowing_le_succ o)

end ONote
