module

public import AlphaCentauri.ToMathlib.FastGrowing.Norm

/-!
# The Hardy hierarchy `H_α`

The **Hardy hierarchy** `H_α : ℕ → ℕ` is the companion of the fast-growing hierarchy, sharing
its well-founded recursion on `ONote.fundamentalSequence`:
`H₀(n) = n`, `H_{α+1}(n) = H_α(n+1)`, `H_λ(n) = H_{λ[n]}(n)`.
-/

@[expose] public section

namespace ONote

open ONote Ordinal

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

lemma eq_zero_of_fundamentalSequence_none {o : ONote} (e : fundamentalSequence o = Sum.inl none) :
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

/-! ### Growth theory of the Hardy hierarchy -/

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

end ONote
