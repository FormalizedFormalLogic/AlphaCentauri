module

public import AlphaCentauri.ToMathlib.Hardy.Structure

/-!
# Hardy hierarchy vs. fast-growing hierarchy

Two-sided comparison of `hardy` at `ω`-powers against `fastGrowing`, up to the `ε₀`-tower
diagonal. Throughout, `oadd a 1 0` is the notation for `ω ^ a`.
-/

@[expose] public section

namespace ONote

open ONote Ordinal

instance : WellFoundedLT ONote := ⟨InvImage.wf repr Ordinal.lt_wf⟩

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

/-! ### Hardy vs. fast-growing at an arbitrary exponent

At arbitrary `a : ONote`, `H_{ω^a}(n) + 1 ≤ f_a(n+1)` unconditionally, tightening to a
two-sided bracket once the coefficient composition law is in place.
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

end ONote
