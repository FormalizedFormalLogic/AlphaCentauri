module

public import Mathlib.SetTheory.Ordinal.Notation

/-!
# Fast-growing hierarchy over `ONote`

`ONote.fastGrowing` is monotone and expansive, and `Reaches` — descent along fundamental
sequences with a fixed budget — carries index monotonicity along it. The CNF norm `norm` bounds
the budget a descent needs, `osucc` is the notation successor, and `tower` is the diagonal
`0, 1, ω, ω^ω, …`, cofinal in `ε₀`. Along it `fastGrowingε₀` eventually dominates every fixed
level.
-/

@[expose] public section

namespace ONote

open ONote Ordinal

/-! ### Monotonicity, expansiveness, and structural descent -/

section Basic

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

@[grind =>]
lemma fundamentalSequence_oadd_succ {m : ℕ+} {b' : ONote}
    (h : fundamentalSequence b = Sum.inl (some b')) :
    fundamentalSequence (oadd a m b) = Sum.inl (some (oadd a m b')) := by
  conv_lhs => rw [fundamentalSequence]; rw [h]

@[grind =>]
lemma fundamentalSequence_oadd_limit {m : ℕ+} {h : ℕ → ONote}
    (hb : fundamentalSequence b = Sum.inr h) :
    fundamentalSequence (oadd a m b) = Sum.inr (fun i => oadd a m (h i)) := by
  conv_lhs => rw [fundamentalSequence]; rw [hb]

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
@[grind =>]
lemma fundamentalSequence_omega_pow_succ (he : fundamentalSequence o = Sum.inl (some a)) :
    fundamentalSequence (oadd o 1 0) = Sum.inr (fun i => oadd a i.succPNat 0) := by
  conv_lhs => rw [fundamentalSequence]
  rw [he]; rfl

/-- Fundamental sequence of `ω^{limit exponent}`. -/
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

end Basic

section Norm

variable {x : ℕ} {o a c d : ONote}

/-! ### The CNF norm

The budget condition for reachability: the standard fundamental-sequence descent of a
normal-form `o` reaches any smaller normal-form `d` once the budget is at least `d`'s CNF
norm (`reaches_of_lt`). -/

/-- **CNF norm** of a notation: the largest finite coefficient occurring in its Cantor normal
form, recursively through exponents and tails. -/
def norm : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (norm e) (max (n : ℕ) (norm a))

@[simp] theorem norm_zero : norm 0 = 0 := rfl

@[simp] theorem norm_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    norm (oadd e n a) = max (norm e) (max (n : ℕ) (norm a)) := rfl

private lemma repr_lt_opow_repr (o : ONote) (h : o.NF) : o.repr < ω ^ o.repr :=
  match o, h with
  | 0, _ => by simp
  | oadd e n a, h => by
      have hIH : e.repr < ω ^ e.repr := repr_lt_opow_repr e h.fst
      have hle : ω ^ e.repr ≤ (oadd e n a).repr := omega0_le_oadd e n a
      have helt : e.repr < (oadd e n a).repr := lt_of_lt_of_le hIH hle
      have hbelow : NFBelow (oadd e n a) (e.repr + 1) :=
        NFBelow.oadd h.fst h.snd' (Order.lt_succ _)
      have h1 : (oadd e n a).repr < ω ^ (e.repr + 1) := hbelow.repr_lt
      have h2 : ω ^ (e.repr + 1) ≤ ω ^ (oadd e n a).repr :=
        opow_le_opow_right omega0_pos (Order.succ_le_of_lt helt)
      exact lt_of_lt_of_le h1 h2

private lemma lt_oadd_cases {ea : ONote} {na : ℕ+} {ba e : ONote} {m : ℕ+} {b : ONote}
    (h1 : NF (oadd ea na ba)) (h2 : NF (oadd e m b)) (h : oadd ea na ba < oadd e m b) :
    ea < e ∨ (ea = e ∧ (na : ℕ) < (m : ℕ)) ∨ (ea = e ∧ na = m ∧ ba < b) := by
  rcases lt_trichotomy ea.repr e.repr with he | he | he
  · exact Or.inl (lt_def.2 he)
  · have heq : ea = e := (@repr_inj ea e h1.fst h2.fst).1 he
    subst heq
    rcases lt_trichotomy (na : ℕ) (m : ℕ) with hn | hn | hn
    · exact Or.inr (Or.inl ⟨rfl, hn⟩)
    · have hnm : na = m := PNat.coe_injective hn
      subst hnm
      rcases lt_trichotomy ba.repr b.repr with hb | hb | hb
      · exact Or.inr (Or.inr ⟨rfl, rfl, lt_def.2 hb⟩)
      · have hbeq : ba = b := (@repr_inj ba b h1.snd h2.snd).1 hb
        subst hbeq; exact absurd h (lt_irrefl _)
      · exact absurd (oadd_lt_oadd_3 (lt_def.2 hb)) (lt_asymm h)
    · exact absurd (oadd_lt_oadd_2 h2 hn) (lt_asymm h)
  · exact absurd (oadd_lt_oadd_1 h2 (lt_def.2 he)) (lt_asymm h)

private lemma lt_oadd_of_lead_le (hc : c.NF) {d : ONote} (hd : d.NF)
    (hlead : d.repr < ω ^ c.repr * ω) (hnorm : norm d ≤ x) :
    d < oadd c x.succPNat 0 := by
  cases d with
  | zero => exact oadd_pos _ _ _
  | oadd ed nd bd =>
    have hpow : ω ^ ed.repr ≤ (oadd ed nd bd).repr := omega0_le_oadd ed nd bd
    have h2 : (ω : Ordinal) ^ ed.repr < ω ^ c.repr * ω := lt_of_le_of_lt hpow hlead
    rw [← opow_succ] at h2
    have hed_le : ed.repr ≤ c.repr :=
      Order.lt_succ_iff.1 ((opow_lt_opow_iff_right one_lt_omega0).1 h2)
    rcases lt_or_eq_of_le hed_le with hlt | heq
    · exact oadd_lt_oadd_1 hd (lt_def.2 hlt)
    · have hedc : ed = c := (@repr_inj ed c hd.fst hc).1 heq
      subst hedc
      rw [norm_oadd] at hnorm
      have hnd : (nd : ℕ) ≤ x := (le_max_of_le_right (le_max_left _ _)).trans hnorm
      refine oadd_lt_oadd_2 hd ?_
      simpa [Nat.succPNat] using Nat.lt_succ_of_le hnd

private theorem lt_fundamentalSequence_of_norm_le (o : ONote) (ho : o.NF) (g : ℕ → ONote)
    (hg : fundamentalSequence o = Sum.inr g) (d : ONote) (hd : d.NF) (hdo : d < o)
    (hnorm : norm d ≤ x) : d < g x := by
  induction o generalizing g d with
  | zero => exact (Sum.inl_ne_inr hg).elim
  | oadd a m b iha ihb =>
    rcases hb : fundamentalSequence b with (_ | b') | hbf
    · -- b = 0 : leading-term cases
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0 : `oadd 0 m 0` is a successor → contradicts the limit `hg`
        rcases hm : m.natPred with _ | k
        · rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inl_ne_inr hg).elim
        · rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inl_ne_inr hg).elim
      · -- a a successor (predecessor `a'`)
        have hpa := fundamentalSequence_has_prop a; rw [ha] at hpa
        have ha'NF : a'.NF := hpa.2 ho.fst
        have harepr : a.repr = Order.succ a'.repr := hpa.1
        have hb0 : b = 0 := by have hpb := fundamentalSequence_has_prop b; rwa [hb] at hpb
        rcases hm : m.natPred with _ | k
        · -- L2 : `g = fun i => ω^a'·(i+1)`, `m = 1`
          have hg' : g = fun i => oadd a' i.succPNat 0 := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hm1 : m = 1 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          refine lt_oadd_of_lead_le ha'NF hd ?_ hnorm
          have hlt : d.repr < (oadd a m b).repr := lt_def.1 hdo
          rw [hb0, hm1] at hlt
          rw [show (oadd a 1 0).repr = ω ^ a.repr from by
            simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]] at hlt
          rw [harepr, opow_succ] at hlt
          exact hlt
        · -- L3 : `g = fun i => ω^a·(k+1) + ω^a'·(i+1)`, `m = k+2`
          have hg' : g = fun i => oadd a k.succPNat (oadd a' i.succPNat 0) := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hmval : (m : ℕ) = k + 2 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases d with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0] at hdo
            rcases lt_oadd_cases hd (hb0 ▸ ho) hdo with hlt | ⟨heq, hnlt⟩ | ⟨_, _, hbalt⟩
            · exact oadd_lt_oadd_1 hd hlt
            · rw [heq] at hd hnorm ⊢
              rw [hmval] at hnlt
              rcases Nat.lt_or_ge (na : ℕ) (k + 1) with hna | hna
              · exact oadd_lt_oadd_2 hd (by simpa [Nat.succPNat] using hna)
              · have hnak : (na : ℕ) = k + 1 := le_antisymm (by omega) hna
                have hnaP : na = k.succPNat :=
                  PNat.coe_injective (by simpa [Nat.succPNat] using hnak)
                subst hnaP
                refine oadd_lt_oadd_3 ?_
                refine lt_oadd_of_lead_le ha'NF hd.snd ?_ ?_
                · have hba : ba.repr < ω ^ a.repr := hd.snd'.repr_lt
                  rw [harepr, opow_succ] at hba; exact hba
                · rw [norm_oadd] at hnorm
                  exact (le_max_of_le_right (le_max_right _ _)).trans hnorm
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
      · -- a a limit (fundamental sequence `p`)
        have hb0 : b = 0 := by have hpb := fundamentalSequence_has_prop b; rwa [hb] at hpb
        rcases hm : m.natPred with _ | k
        · -- L4 : `g = fun i => ω^(a[i])`, `m = 1`
          have hg' : g = fun i => oadd (p i) 1 0 := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hm1 : m = 1 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases d with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0, hm1] at hdo
            rcases lt_oadd_cases hd ((hb0 ▸ hm1 ▸ ho : NF (oadd a 1 0))) hdo
              with hlt | ⟨rfl, hnlt⟩ | ⟨rfl, _, hbalt⟩
            · have hnorm_ea : norm ea ≤ x := by
                rw [norm_oadd] at hnorm; exact (le_max_left _ _).trans hnorm
              have hep : ea < p x := iha ho.fst p ha ea hd.fst hlt hnorm_ea
              exact oadd_lt_oadd_1 hd hep
            · simp only [PNat.one_coe] at hnlt; exact absurd hnlt (by have := na.pos; omega)
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
        · -- L5 : `g = fun i => ω^a·(k+1) + ω^(a[i])`, `m = k+2`
          have hg' : g = fun i => oadd a k.succPNat (oadd (p i) 1 0) := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hmval : (m : ℕ) = k + 2 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases d with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0] at hdo
            rcases lt_oadd_cases hd (hb0 ▸ ho) hdo with hlt | ⟨heq, hnlt⟩ | ⟨_, _, hbalt⟩
            · exact oadd_lt_oadd_1 hd hlt
            · rw [heq] at hd hnorm ⊢
              rw [hmval] at hnlt
              rcases Nat.lt_or_ge (na : ℕ) (k + 1) with hna | hna
              · exact oadd_lt_oadd_2 hd (by simpa [Nat.succPNat] using hna)
              · have hnak : (na : ℕ) = k + 1 := le_antisymm (by omega) hna
                have hnaP : na = k.succPNat :=
                  PNat.coe_injective (by simpa [Nat.succPNat] using hnak)
                subst hnaP
                refine oadd_lt_oadd_3 ?_
                cases ba with
                | zero => exact oadd_pos _ _ _
                | oadd eb nb bb =>
                  have heb : eb.repr < a.repr := by
                    have hbb : (oadd eb nb bb).repr < ω ^ a.repr := hd.snd'.repr_lt
                    have hle : ω ^ eb.repr ≤ (oadd eb nb bb).repr := omega0_le_oadd eb nb bb
                    exact (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hle hbb)
                  have hnorm_eb : norm eb ≤ x := by
                    rw [norm_oadd, norm_oadd] at hnorm
                    exact (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans hnorm
                  have hep : eb < p x := iha ho.fst p ha eb hd.snd.fst (lt_def.2 heb) hnorm_eb
                  exact oadd_lt_oadd_1 hd.snd hep
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
    · -- b a successor ⟹ `oadd a m b` is a successor → contradicts the limit `hg`
      rw [fundamentalSequence_oadd_succ hb] at hg; exact (Sum.inl_ne_inr hg).elim
    · -- L1 : b a limit, `g = fun i => oadd a m (b[i])` ; descend the tail
      have hg' : g = fun i => oadd a m (hbf i) := by
        rw [fundamentalSequence_oadd_limit hb] at hg; exact (Sum.inr.inj hg).symm
      rw [hg']
      cases d with
      | zero => exact oadd_pos _ _ _
      | oadd ea na ba =>
        rcases lt_oadd_cases hd ho hdo with hlt | ⟨rfl, hnlt⟩ | ⟨rfl, hnm, hbalt⟩
        · exact oadd_lt_oadd_1 hd hlt
        · exact oadd_lt_oadd_2 hd hnlt
        · subst hnm
          have hnorm_ba : norm ba ≤ x := by
            rw [norm_oadd] at hnorm; exact (le_max_of_le_right (le_max_right _ _)).trans hnorm
          exact oadd_lt_oadd_3 (ihb ho.snd hbf hb ba hd.snd hbalt hnorm_ba)

theorem reaches_of_lt (o : ONote) (ho : o.NF) (d : ONote) (hd : d.NF) (hdo : d < o)
    (hnorm : norm d ≤ x) : Reaches x o d := by
  rcases e : fundamentalSequence o with (_ | c) | g
  · exfalso
    have ho0 : o = 0 := by have hp := fundamentalSequence_has_prop o; rwa [e] at hp
    rw [ho0] at hdo
    have hr : d.repr < 0 := by rw [← repr_zero]; exact lt_def.1 hdo
    exact absurd hr not_lt_zero
  · have hp := fundamentalSequence_has_prop o; rw [e] at hp
    have hcNF : c.NF := hp.2 ho
    have hco : c < o := lt_def.2 (by rw [hp.1]; exact Order.lt_succ _)
    have hdr : d.repr ≤ c.repr := Order.lt_succ_iff.1 (by rw [← hp.1]; exact lt_def.1 hdo)
    rcases eq_or_lt_of_le hdr with heq | hlt
    · have hdc : d = c := (@repr_inj d c hd hcNF).1 heq
      subst hdc; exact Reaches.succ e (Reaches.refl _)
    · exact Reaches.succ e (reaches_of_lt c hcNF d hd (lt_def.2 hlt) hnorm)
  · have hp := fundamentalSequence_has_prop o; rw [e] at hp
    have hgxNF : (g x).NF := (hp.2.1 x).2.2 ho
    have hgxlt : g x < o := (hp.2.1 x).2.1
    have hdgx : d < g x := lt_fundamentalSequence_of_norm_le o ho g e d hd hdo hnorm
    exact Reaches.limit e (reaches_of_lt (g x) hgxNF d hd hdgx hnorm)
termination_by o
decreasing_by all_goals assumption

theorem fastGrowing_le_of_lt (hx : 1 ≤ x) (hd : d.NF) (ho : o.NF) (hdo : d < o)
    (hnorm : norm d ≤ x) : fastGrowing d x ≤ fastGrowing o x :=
  fastGrowing_le_of_reaches hx (reaches_of_lt o ho d hd hdo hnorm)

/-! ### The notation successor `osucc`

Structural fundamental-sequence descent, used to reach `osucc o` from a tower level with
budget `n` (for strict index domination). -/

private lemma tail_eq_zero_of_zero_exponent {n : ℕ+} {a : ONote} (h : (oadd 0 n a).NF) : a = 0 := by
  have hlt : a.repr < ω ^ (0 : ONote).repr := h.snd'.repr_lt
  rw [repr_zero, opow_zero] at hlt
  exact (@repr_inj a 0 h.snd NF.zero).1 (by rw [repr_zero]; exact Order.lt_one_iff.1 hlt)

/-- The **notation successor** `osucc o`: `repr (osucc o) = repr o + 1` and
`fundamentalSequence (osucc o) = inl (some o)` on normal forms. -/
def osucc : ONote → ONote
  | 0 => oadd 0 1 0
  | oadd 0 n _ => oadd 0 (n + 1) 0
  | oadd (oadd e' n' a') m b => oadd (oadd e' n' a') m (osucc b)

@[grind =]
lemma repr_osucc {o : ONote} (h : o.NF) : (osucc o).repr = o.repr + 1 :=
  match o, h with
  | 0, _ => by simp [osucc]
  | oadd 0 n a, h => by
      have ha0 := tail_eq_zero_of_zero_exponent h
      subst ha0
      change (oadd 0 (n + 1) 0).repr = (oadd 0 n 0).repr + 1
      simp only [ONote.repr, opow_zero, one_mul, add_zero, PNat.add_coe,
        PNat.one_coe, Nat.cast_add, Nat.cast_one]
  | oadd (oadd e' n' a') m b, h => by
      change (oadd (oadd e' n' a') m (osucc b)).repr = (oadd (oadd e' n' a') m b).repr + 1
      simp only [ONote.repr]
      rw [repr_osucc h.snd, ← add_assoc]

@[grind →]
lemma osucc_NF {o : ONote} (h : o.NF) : (osucc o).NF :=
  match o, h with
  | 0, _ => NF.oadd_zero 0 1
  | oadd 0 n _, _ => NF.oadd_zero 0 (n + 1)
  | oadd (oadd e' n' a') m b, h => by
      refine NF.oadd h.fst m (NF.below_of_lt' ?_ (osucc_NF h.snd))
      rw [repr_osucc h.snd, ← Order.succ_eq_add_one]
      have hElim : Order.IsSuccLimit (ω ^ (oadd e' n' a').repr) := by
        refine isSuccLimit_opow_left isSuccLimit_omega0 ?_
        have hpos : (0 : Ordinal) < (oadd e' n' a').repr := by
          rw [← repr_zero]; exact lt_def.1 (oadd_pos e' n' a')
        exact hpos.ne'
      exact hElim.succ_lt h.snd'.repr_lt

@[grind =]
lemma fundamentalSequence_osucc {o : ONote} (h : o.NF) :
    fundamentalSequence (osucc o) = Sum.inl (some o) :=
  match o, h with
  | 0, _ => rfl
  | oadd 0 n a, h => by
      have ha0 := tail_eq_zero_of_zero_exponent h
      subst ha0
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k.succPNat := ⟨n.natPred, (PNat.succPNat_natPred n).symm⟩
      rfl
  | oadd (oadd e' n' a') m b, h =>
      fundamentalSequence_oadd_succ (fundamentalSequence_osucc h.snd)

lemma norm_osucc_le {o : ONote} : norm (osucc o) ≤ norm o + 1 :=
  match o with
  | 0 => by simp [osucc, norm]
  | oadd 0 n _ => by
      simp only [osucc, norm_oadd, norm_zero, PNat.add_coe, PNat.one_coe]; omega
  | oadd (oadd e' n' a') m b => by
      have ih : norm (osucc b) ≤ norm b + 1 := norm_osucc_le
      simp only [osucc, norm_oadd]; omega

lemma fastGrowing_lt_succ_index (h : fundamentalSequence o = Sum.inl (some a)) {n : ℕ}
    (hn : 2 ≤ n) : fastGrowing a n < fastGrowing o n := by
  rw [fastGrowing_succ o h]
  have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
  have h1n : 1 ≤ n := le_trans one_le_two hn
  have hge : n ≤ fastGrowing a n := le_fastGrowing a n
  have hlt2 : fastGrowing a n < fastGrowing a (fastGrowing a n) :=
    lt_fastGrowing a (le_trans h1n hge)
  have hstep2 : (fastGrowing a)^[2] n ≤ (fastGrowing a)^[n] n :=
    Function.monotone_iterate_of_id_le hexp hn n
  have h2eq : (fastGrowing a)^[2] n = fastGrowing a (fastGrowing a n) := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
  calc fastGrowing a n < fastGrowing a (fastGrowing a n) := hlt2
    _ = (fastGrowing a)^[2] n := h2eq.symm
    _ ≤ (fastGrowing a)^[n] n := hstep2

/-! ### The diagonal tower

`tower 0 = 0` and `tower (i + 1) = ω ^ tower i`, cofinal in `ε₀`. -/

/-- The **diagonal tower**: `0, 1, ω, ω^ω, …`. -/
def tower (i : ℕ) : ONote := (fun a => oadd a 1 0)^[i] 0

@[simp] theorem tower_zero : tower 0 = 0 := rfl

lemma tower_succ (i : ℕ) : tower (i + 1) = oadd (tower i) 1 0 := by
  rw [tower, tower, Function.iterate_succ_apply']

lemma tower_NF (i : ℕ) : (tower i).NF :=
  match i with
  | 0 => by rw [tower_zero]; exact NF.zero
  | i + 1 => by rw [tower_succ]; have := tower_NF i; exact NF.oadd_zero _ _

private lemma tower_lt_succ (i : ℕ) : tower i < tower (i + 1) := by
  rw [tower_succ, lt_def]
  have hrepr : ((tower i).oadd 1 0).repr = ω ^ (tower i).repr := by
    simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]
  rw [hrepr]
  exact repr_lt_opow_repr _ (tower_NF i)

lemma tower_strictMono : StrictMono tower :=
  strictMono_nat_of_lt_succ tower_lt_succ

lemma repr_tower_succ (i : ℕ) : (tower (i + 1)).repr = ω ^ (tower i).repr := by
  rw [tower_succ]
  simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]

theorem tower_cofinal (o : ONote) (h : o.NF) : ∃ k, o < tower k :=
  match o, h with
  | 0, _ => ⟨1, by rw [lt_def]; simp [tower_succ]⟩
  | oadd e n a, h => by
      obtain ⟨j, hj⟩ := tower_cofinal e h.fst
      refine ⟨j + 1, ?_⟩
      rw [lt_def, repr_tower_succ]
      have hej : e.repr < (tower j).repr := (lt_def).mp hj
      have hbelow : NFBelow (oadd e n a) (e.repr + 1) :=
        NFBelow.oadd h.fst h.snd' (Order.lt_succ _)
      have h1 : (oadd e n a).repr < ω ^ (e.repr + 1) := hbelow.repr_lt
      have h2 : ω ^ (e.repr + 1) ≤ ω ^ (tower j).repr :=
        opow_le_opow_right omega0_pos (Order.succ_le_of_lt hej)
      exact lt_of_lt_of_le h1 h2

end Norm

/-! ### Domination by `fastGrowingε₀`

Every fixed level `fastGrowing o` is eventually strictly dominated by the diagonal
`fastGrowingε₀`. -/

private lemma fastGrowingε₀_eq (i : ℕ) : fastGrowingε₀ i = fastGrowing (tower i) i := rfl

theorem fastGrowing_lt_of_lt_tower {o : ONote} (ho : o.NF) (n : ℕ)
    (hn : norm o < n) (h2 : 2 ≤ n) (h : o < tower n) :
    fastGrowing o n < fastGrowing (tower n) n := by
  -- `tower n` is a limit ordinal for `n ≥ 2`: `repr (tower n) = ω^(repr (tower (n-1)))`
  -- with `tower (n-1) > 0`, so `ω^·` is a limit.
  have hlimit : Order.IsSuccLimit (tower n).repr := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [repr_tower_succ]
    refine isSuccLimit_opow_left isSuccLimit_omega0 ?_
    have hpos : (0 : ONote) < tower j :=
      tower_zero ▸ tower_strictMono (show (0 : ℕ) < j by omega)
    rw [← repr_zero]; exact (lt_def.1 hpos).ne'
  -- Reach the *successor* of `o`, then take one strict successor step.
  have hNF : (osucc o).NF := osucc_NF ho
  have hlt : osucc o < tower n := by
    rw [lt_def, repr_osucc ho, ← Order.succ_eq_add_one]
    exact hlimit.succ_lt (lt_def.1 h)
  have hnorm : norm (osucc o) ≤ n := le_trans norm_osucc_le (by omega)
  have hreach : Reaches n (tower n) (osucc o) :=
    reaches_of_lt (tower n) (tower_NF n) (osucc o) hNF hlt hnorm
  have hle : fastGrowing (osucc o) n ≤ fastGrowing (tower n) n :=
    fastGrowing_le_of_reaches (le_trans one_le_two h2) hreach
  have hstrict : fastGrowing o n < fastGrowing (osucc o) n :=
    fastGrowing_lt_succ_index (fundamentalSequence_osucc ho) h2
  exact lt_of_lt_of_le hstrict hle

theorem fastGrowing_lt_fastGrowingε₀ (o : ONote) (ho : o.NF) :
    ∃ N, ∀ n ≥ N, fastGrowing o n < fastGrowingε₀ n := by
  obtain ⟨k, hk⟩ := tower_cofinal o ho
  refine ⟨max (max k (norm o + 1)) 2, ?_⟩
  intro n hn
  simp only [ge_iff_le, max_le_iff] at hn
  obtain ⟨⟨hkn, hnormn⟩, h2n⟩ := hn
  have hlt : o < tower n := lt_of_lt_of_le hk (tower_strictMono.monotone hkn)
  rw [fastGrowingε₀_eq]
  exact fastGrowing_lt_of_lt_tower ho n (by omega) h2n hlt

end ONote
