module

public import AlphaCentauri.ToMathlib.FastGrowing.Basic

/-!
# `ONote` norm, successor, and tower

`norm`, the notation successor `osucc`, the diagonal tower `tower`, and the norm-budgeted
reachability facts these support in the fast-growing hierarchy.
-/

@[expose] public section

namespace ONote

open ONote Ordinal

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

-- No `grind` attribute: `@[grind =]` needs an equality conclusion (this is a `≤`), and
-- `@[grind →]` needs a propositional hypothesis (there is none here).
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

end ONote
