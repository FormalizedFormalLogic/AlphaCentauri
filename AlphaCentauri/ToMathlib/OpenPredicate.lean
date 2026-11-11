module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Open predicates, open induction and the least number principle

`IsPolynomial` and `IsOpen` describe the polynomial functions and the open (quantifier-free)
predicates on a commutative ring `R` with parameters in `R`. `OpenInduction R` is induction over
the non-negative elements for open predicates. `LeastNumberPrinciple R` is the
least number principle for the predicates `∃ ys : Fin n → R, (∀ j, |ys j| < B) ∧ Φ (x, ys)`
with `Φ` open, over the non-negative `x`. In a discretely ordered ring satisfying
`LeastNumberPrinciple`, division with remainder is available.
-/

@[expose] public section

namespace OpenPredicate

variable {R : Type*} [CommRing R] {V W : Type*}

/-- Polynomial functions of the variables `V`, with coefficients in `R`. -/
inductive IsPolynomial : ((V → R) → R) → Prop
  | var (i : V) : IsPolynomial fun w => w i
  | const (c : R) : IsPolynomial fun _ => c
  | add {f g : (V → R) → R} : IsPolynomial f → IsPolynomial g → IsPolynomial fun w => f w + g w
  | mul {f g : (V → R) → R} : IsPolynomial f → IsPolynomial g → IsPolynomial fun w => f w * g w
  | neg {f : (V → R) → R} : IsPolynomial f → IsPolynomial fun w => -f w

/-- Open (quantifier-free) predicates in the variables `V`, with parameters in `R`. -/
inductive IsOpen [LT R] : ((V → R) → Prop) → Prop
  | eq {f g : (V → R) → R} : IsPolynomial f → IsPolynomial g → IsOpen fun w => f w = g w
  | lt {f g : (V → R) → R} : IsPolynomial f → IsPolynomial g → IsOpen fun w => f w < g w
  | not {P : (V → R) → Prop} : IsOpen P → IsOpen fun w => ¬P w
  | and {P Q : (V → R) → Prop} : IsOpen P → IsOpen Q → IsOpen fun w => P w ∧ Q w
  | or {P Q : (V → R) → Prop} : IsOpen P → IsOpen Q → IsOpen fun w => P w ∨ Q w

variable {f g : (V → R) → R} {P Q : (V → R) → Prop}

namespace IsPolynomial

lemma sub (hf : IsPolynomial f) (hg : IsPolynomial g) : IsPolynomial fun w => f w - g w := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma pow (hf : IsPolynomial f) (n : ℕ) : IsPolynomial fun w => f w ^ n := by
  induction n with
  | zero => simpa using IsPolynomial.const (V := V) (1 : R)
  | succ n ih => simpa [pow_succ] using ih.mul hf

lemma of_eq (hf : IsPolynomial f) (e : ∀ w, f w = g w) : IsPolynomial g := funext e ▸ hf

/-- Renaming the variables. -/
lemma comp (hf : IsPolynomial f) (σ : V → W) : IsPolynomial fun w : W → R => f (w ∘ σ) := by
  induction hf <;> constructor <;> assumption

end IsPolynomial

variable [LinearOrder R]

/-- The predicate `∃ ys : Fin n → R, (∀ j, |ys j| < B) ∧ Φ (x, ys)`, the variable `0` of `Φ` being
`x` and the variable `j.succ` being `ys j`. -/
def BoundedExists {n : ℕ} (B : R) (Φ : (Fin (n + 1) → R) → Prop) (x : R) : Prop :=
  ∃ ys : Fin n → R, (∀ j, |ys j| < B) ∧ Φ (Fin.cons x ys)

variable (R) in
/-- The least number principle for bounded existential open predicates, over the non-negative
elements. -/
def LeastNumberPrinciple : Prop :=
  ∀ (n : ℕ) (Φ : (Fin (n + 1) → R) → Prop), IsOpen Φ → ∀ (B x₀ : R), 0 ≤ x₀ → BoundedExists B Φ x₀ →
    ∃ x, 0 ≤ x ∧ BoundedExists B Φ x ∧ ∀ y, 0 ≤ y → y < x → ¬BoundedExists B Φ y

variable (R) in
/-- A discretely ordered ring: there is nothing strictly between `0` and `1`. -/
class DiscretelyOrdered : Prop where
  one_le_of_pos : ∀ x : R, 0 < x → 1 ≤ x

variable (R) in
/-- Open induction: induction over the non-negative elements for open predicates with parameters
in `R`.
- [BO96, §1]
- [GG17, §2.1] -/
def OpenInduction : Prop :=
  ∀ P : (Fin 1 → R) → Prop, IsOpen P → P ![0] → (∀ x, 0 ≤ x → P ![x] → P ![x + 1]) →
    ∀ x, 0 ≤ x → P ![x]

namespace IsOpen

lemma of_iff (hP : IsOpen P) (e : ∀ w, P w ↔ Q w) : IsOpen Q := funext (propext <| e ·) ▸ hP

lemma le (hf : IsPolynomial f) (hg : IsPolynomial g) : IsOpen fun w => f w ≤ g w :=
  (IsOpen.lt hg hf).not.of_iff fun _ => not_lt

lemma abs_lt [IsStrictOrderedRing R] (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsOpen fun w => |f w| < g w :=
  ((IsOpen.lt hg.neg hf).and (IsOpen.lt hf hg)).of_iff fun _ => _root_.abs_lt.symm

lemma forall_fin {n : ℕ} {P : Fin n → (V → R) → Prop} (h : ∀ j, IsOpen (P j)) :
    IsOpen fun w => ∀ j, P j w := by
  induction n with
  | zero => exact (IsOpen.eq (.const 0) (.const 0)).of_iff fun _ => iff_of_true rfl (·.elim0)
  | succ n ih =>
    exact ((h 0).and (ih fun j => h j.succ)).of_iff fun w =>
      (Fin.forall_fin_succ (P := fun j => P j w)).symm

/-- Renaming the variables. -/
lemma comp (hP : IsOpen P) (σ : V → W) : IsOpen fun w : W → R => P (w ∘ σ) := by
  induction hP <;> constructor <;> first | assumption | exact IsPolynomial.comp ‹_› σ

end IsOpen

/-- One step of `is_open`; further rules are added with `macro_rules`. -/
syntax "is_open_step" : tactic

macro_rules
  | `(tactic| is_open_step) => `(tactic| first
    | assumption | apply IsPolynomial.const | apply IsPolynomial.var | apply IsPolynomial.sub
    | apply IsPolynomial.add | apply IsPolynomial.mul | apply IsPolynomial.neg
    | apply IsPolynomial.pow | apply IsOpen.abs_lt | apply IsOpen.le | apply IsOpen.lt
    | apply IsOpen.eq | (apply IsOpen.forall_fin; intro) | apply IsOpen.and | apply IsOpen.or
    | apply IsOpen.not | exact IsOpen.comp ‹_› _)

/-- Proves `IsOpen P` and `IsPolynomial f` by decomposing `P` and `f` syntactically. -/
macro "is_open" : tactic => `(tactic| repeat' is_open_step)

variable [IsStrictOrderedRing R] [DiscretelyOrdered R] (hL : LeastNumberPrinciple R)

include hL

lemma exists_ediv (a b : R) (hb : 0 < b) : ∃ q r, a = q * b + r ∧ 0 ≤ r ∧ r < b := by
  have hb1 := DiscretelyOrdered.one_le_of_pos _ hb
  have ha : 0 ≤ a + |a| * b := by nlinarith [neg_abs_le a, abs_nonneg a]
  have hB (x : R) : BoundedExists 0 (fun w : Fin 1 → R => a + |a| * b < (w 0 + 1) * b) x ↔
      a + |a| * b < (x + 1) * b := by
    simp [BoundedExists]
  obtain ⟨q, hq0, hq, hmin⟩ := hL 0 _ (by is_open) 0 _ ha ((hB _).2 (by nlinarith))
  have hle : q * b ≤ a + |a| * b := by
    rcases hq0.eq_or_lt with rfl | h
    · simpa using ha
    · have := hmin (q - 1) (by linarith [DiscretelyOrdered.one_le_of_pos _ h]) (by linarith)
      simpa [hB] using this
  use q - |a|, a + |a| * b - q * b
  exact ⟨by ring, by linarith, by linarith [(hB q).1 hq]⟩

/-- Division with a remainder of at most half the divisor in absolute value. -/
lemma exists_round (u n : R) (hn : 0 < n) : ∃ q r, u = q * n + r ∧ 2 * |r| ≤ n := by
  obtain ⟨q, r, h, hr0, hr⟩ := exists_ediv hL (2 * u + n) (2 * n) (by linarith)
  use q, u - q * n
  exact ⟨by ring, by rcases abs_cases (u - q * n) with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith⟩

end OpenPredicate
