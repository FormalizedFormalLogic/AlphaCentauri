module

public import AlphaCentauri.ToMathlib.OpenPredicate
public import AlphaCentauri.ToMathlib.OpenPredicate.Induction
public import Foundation.FirstOrder.Arithmetic.Basic

/-!
# Open formulas over an ordered ring

Over a commutative ordered ring `R` regarded as an `ℒₒᵣ`-structure, the open `ℒₒᵣ`-formulas define
open predicates. Conversely, every open predicate on `R` is defined by an open formula whose
parameters range over any `M → R` whose differences cover `R`.
-/

@[expose] public section

open FFL FirstOrder Semiterm Polynomial

namespace OpenPredicate

variable {R : Type*} [CommRing R] [LinearOrder R] {ξ : Type*} {n : ℕ}

lemma isPolynomial_val (ε : ξ → R) (t : ArithmeticSemiterm ξ n) :
    IsPolynomial fun w : Fin n → R ↦ t.val w ε := by
  induction t with
  | bvar x => exact .var x
  | fvar x => exact .const (ε x)
  | func f v ih =>
    cases f
    · exact (IsPolynomial.const 0).of_eq fun _ ↦ rfl
    · exact (IsPolynomial.const 1).of_eq fun _ ↦ rfl
    · exact ((ih 0).add (ih 1)).of_eq fun _ ↦ rfl
    · exact ((ih 0).mul (ih 1)).of_eq fun _ ↦ rfl

lemma isOpen_eval (ε : ξ → R) {φ : ArithmeticSemiformula ξ n} (hφ : φ.Open) :
    IsOpen fun w : Fin n → R ↦ φ.Eval w ε := by
  induction φ using Semiformula.rec' with
  | hverum => exact (IsOpen.eq (.const 0) (.const 0)).of_iff fun _ ↦ by simp
  | hfalsum => exact (IsOpen.eq (.const 0) (.const 0)).not.of_iff fun _ ↦ by simp
  | hrel r v =>
    cases r <;> have h₀ := isPolynomial_val ε (v 0) <;> have h₁ := isPolynomial_val ε (v 1)
    exacts [(IsOpen.eq h₀ h₁).of_iff fun _ ↦ Iff.rfl, (IsOpen.lt h₀ h₁).of_iff fun _ ↦ Iff.rfl]
  | hnrel r v =>
    cases r <;> have h₀ := isPolynomial_val ε (v 0) <;> have h₁ := isPolynomial_val ε (v 1)
    exacts [(IsOpen.eq h₀ h₁).not.of_iff fun _ ↦ Iff.rfl,
      (IsOpen.lt h₀ h₁).not.of_iff fun _ ↦ Iff.rfl]
  | hand φ ψ ihφ ihψ => simp at hφ; simpa using (ihφ hφ.1).and (ihψ hφ.2)
  | hor φ ψ ihφ ihψ => simp at hφ; simpa using (ihφ hφ.1).or (ihψ hφ.2)
  | hall => simp at hφ
  | hexs => simp at hφ

variable {M : Type*} {ι : M → R} (hι : ∀ x : R, ∃ a b, ι a - ι b = x)
include hι

/-- A polynomial over `R` is a difference of two `ℒₒᵣ`-terms with parameters in `M`. -/
lemma exists_val_sub_val_eq {f : (Fin n → R) → R} (hf : IsPolynomial f) :
    ∃ tp tn : ArithmeticSemiterm M n, ∀ e, tp.val e ι - tn.val e ι = f e := by
  induction hf with
  | var i =>
    use #i, ‘0’
    intro e
    simp
  | const c =>
    obtain ⟨a, b, rfl⟩ := hι c
    use &a, &b
    intro e
    simp
  | add _ _ ih₁ ih₂ =>
    obtain ⟨p₁, n₁, h₁⟩ := ih₁
    obtain ⟨p₂, n₂, h₂⟩ := ih₂
    use ‘!!p₁ + !!p₂’, ‘!!n₁ + !!n₂’
    intro e
    simp [← h₁, ← h₂]
    ring
  | mul _ _ ih₁ ih₂ =>
    obtain ⟨p₁, n₁, h₁⟩ := ih₁
    obtain ⟨p₂, n₂, h₂⟩ := ih₂
    use ‘!!p₁ * !!p₂ + !!n₁ * !!n₂’, ‘!!p₁ * !!n₂ + !!n₁ * !!p₂’
    intro e
    simp [← h₁, ← h₂]
    ring
  | neg _ ih =>
    obtain ⟨p, m, h⟩ := ih
    use m, p
    intro e
    simp [← h]

lemma exists_open_eval_iff [IsStrictOrderedRing R] {P : (Fin n → R) → Prop} (hP : IsOpen P) :
    ∃ θ : ArithmeticSemiformula M n, θ.Open ∧ ∀ e, θ.Eval e ι ↔ P e := by
  induction hP with
  | eq hf hg =>
    obtain ⟨p₁, n₁, h₁⟩ := exists_val_sub_val_eq hι hf
    obtain ⟨p₂, n₂, h₂⟩ := exists_val_sub_val_eq hι hg
    use “!!p₁ + !!n₂ = !!p₂ + !!n₁”
    simp [← h₁, ← h₂, sub_eq_sub_iff_add_eq_add]
  | lt hf hg =>
    obtain ⟨p₁, n₁, h₁⟩ := exists_val_sub_val_eq hι hf
    obtain ⟨p₂, n₂, h₂⟩ := exists_val_sub_val_eq hι hg
    use “!!p₁ + !!n₂ < !!p₂ + !!n₁”
    simp [← h₁, ← h₂, sub_lt_sub_iff]
  | not _ ih =>
    obtain ⟨θ, hθ, h⟩ := ih
    use ∼θ
    simp [hθ, h]
  | and _ _ ih₁ ih₂ =>
    obtain ⟨θ₁, hθ₁, h₁⟩ := ih₁
    obtain ⟨θ₂, hθ₂, h₂⟩ := ih₂
    use θ₁ ⋏ θ₂
    simp [hθ₁, hθ₂, h₁, h₂]
  | or _ _ ih₁ ih₂ =>
    obtain ⟨θ₁, hθ₁, h₁⟩ := ih₁
    obtain ⟨θ₂, hθ₂, h₂⟩ := ih₂
    use θ₁ ⋎ θ₂
    simp [hθ₁, hθ₂, h₁, h₂]

end OpenPredicate
