module

public import AlphaCentauri.ToMathlib.NumberTheory.EisensteinInteger.Basic
public import AlphaCentauri.ToMathlib.OpenPredicate

/-!
# Eisenstein-valued polynomial functions

`IsEisensteinPolynomial F` says that the real and imaginary parts of an Eisenstein-valued function
`F` are polynomial functions. The equality of two such functions is an open predicate.
-/

@[expose] public section

open QuadraticAlgebra OpenPredicate

namespace EisensteinInteger

variable {R : Type*} [CommRing R] {V : Type*} {a b c z : EisensteinInteger R}
  {F G : (V → R) → EisensteinInteger R}

/-- Eisenstein-valued functions that are polynomial in the real and imaginary parts. -/
def IsEisensteinPolynomial (F : (V → R) → EisensteinInteger R) : Prop :=
  IsPolynomial (fun w => (F w).re) ∧ IsPolynomial (fun w => (F w).im)

namespace IsEisensteinPolynomial

lemma mk {f g : (V → R) → R} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsEisensteinPolynomial fun w => (⟨f w, g w⟩ : EisensteinInteger R) := ⟨hf, hg⟩

lemma const (z : EisensteinInteger R) : IsEisensteinPolynomial (V := V) fun _ => z :=
  ⟨IsPolynomial.const _, IsPolynomial.const _⟩

lemma add (hF : IsEisensteinPolynomial F) (hG : IsEisensteinPolynomial G) :
    IsEisensteinPolynomial fun w => F w + G w := ⟨hF.1.add hG.1, hF.2.add hG.2⟩

lemma neg (hF : IsEisensteinPolynomial F) : IsEisensteinPolynomial fun w => -F w :=
  ⟨hF.1.neg, hF.2.neg⟩

lemma sub (hF : IsEisensteinPolynomial F) (hG : IsEisensteinPolynomial G) :
    IsEisensteinPolynomial fun w => F w - G w := ⟨hF.1.sub hG.1, hF.2.sub hG.2⟩

lemma mul (hF : IsEisensteinPolynomial F) (hG : IsEisensteinPolynomial G) :
    IsEisensteinPolynomial fun w => F w * G w :=
  ⟨((hF.1.mul hG.1).add ((IsPolynomial.const (-1)).mul (hF.2.mul hG.2))).of_eq fun _ => by simp,
    (((hF.1.mul hG.2).add (hF.2.mul hG.1)).add ((IsPolynomial.const (-1)).mul
      (hF.2.mul hG.2))).of_eq fun _ => by simp⟩

lemma pow (hF : IsEisensteinPolynomial F) (n : ℕ) : IsEisensteinPolynomial fun w => F w ^ n := by
  induction n with
  | zero => simpa using IsEisensteinPolynomial.const (V := V) (1 : EisensteinInteger R)
  | succ n ih => simpa [pow_succ] using ih.mul hF

lemma norm (hF : IsEisensteinPolynomial F) :
    IsPolynomial fun w => EisensteinInteger.norm (F w) :=
  (((hF.1.pow 2).sub (hF.1.mul hF.2)).add (hF.2.pow 2)).of_eq fun _ => (norm_eq _).symm

end IsEisensteinPolynomial

variable [LinearOrder R]

lemma IsEisensteinPolynomial.isOpen_eq (hF : IsEisensteinPolynomial F)
    (hG : IsEisensteinPolynomial G) : IsOpen fun w => F w = G w :=
  ((IsOpen.eq hF.1 hG.1).and (IsOpen.eq hF.2 hG.2)).of_iff fun _ =>
    ⟨fun h => QuadraticAlgebra.ext h.1 h.2, fun h => ⟨congrArg _ h, congrArg _ h⟩⟩

macro_rules
  | `(tactic| is_open_step) => `(tactic| first
    | apply IsEisensteinPolynomial.isOpen_eq | apply IsEisensteinPolynomial.norm
    | apply IsEisensteinPolynomial.const | apply IsEisensteinPolynomial.mk
    | apply IsEisensteinPolynomial.sub | apply IsEisensteinPolynomial.add
    | apply IsEisensteinPolynomial.mul | apply IsEisensteinPolynomial.neg
    | apply IsEisensteinPolynomial.pow)

end EisensteinInteger
