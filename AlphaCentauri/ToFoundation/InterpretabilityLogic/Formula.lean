module

public import Foundation.Logic.LogicSymbol

/-!
# Formulas of interpretability logic

Modal formulas extended by the binary interpretability connective `▷`.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

inductive Formula (α : Type*) where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  | rhd    : Formula α → Formula α → Formula α
  deriving DecidableEq

namespace Formula

variable {α : Type*} {A B : Formula α}

scoped[FFL.InterpretabilityLogic] prefix:max "#" => Formula.atom

abbrev neg (A : Formula α) : Formula α := imp A falsum

abbrev verum : Formula α := imp falsum falsum

abbrev or (A B : Formula α) : Formula α := imp (neg A) B

abbrev and (A B : Formula α) : Formula α := neg (imp A (neg B))

abbrev dia (A : Formula α) : Formula α := neg (box (neg A))

instance : LogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or

instance : LogicalNeutral (Formula α) where
  top := verum
  bot := falsum

instance : Box (Formula α) := ⟨box⟩

instance : Dia (Formula α) := ⟨dia⟩

instance : Rhd (Formula α) := ⟨rhd⟩

instance : ŁukasiewiczAbbrev (Formula α) where
  neg := rfl
  top := rfl
  or := rfl
  and := rfl

@[simp, grind =] lemma imp_inj {A₁ A₂ B₁ B₂ : Formula α} : A₁ 🡒 A₂ = B₁ 🡒 B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ :=
  Iff.of_eq <| imp.injEq _ _ _ _

@[simp, grind =] lemma box_inj : □A = □B ↔ A = B := Iff.of_eq <| box.injEq _ _

@[simp, grind =] lemma rhd_inj {A₁ A₂ B₁ B₂ : Formula α} : A₁ ▷ A₂ = B₁ ▷ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ :=
  Iff.of_eq <| rhd.injEq _ _ _ _

@[elab_as_elim, induction_eliminator]
def rec' {C : Formula α → Sort*}
    (atom : ∀ a, C (#a))
    (falsum : C ⊥)
    (imp : ∀ A B, C A → C B → C (A 🡒 B))
    (box : ∀ A, C A → C (□A))
    (rhd : ∀ A B, C A → C B → C (A ▷ B)) :
    (A : Formula α) → C A
  | #a => atom a
  | .falsum => falsum
  | .imp A B => imp A B (rec' atom falsum imp box rhd A) (rec' atom falsum imp box rhd B)
  | .box A => box A (rec' atom falsum imp box rhd A)
  | .rhd A B => rhd A B (rec' atom falsum imp box rhd A) (rec' atom falsum imp box rhd B)

@[elab_as_elim, cases_eliminator]
def cases' {C : Formula α → Sort*}
    (atom : ∀ a, C (#a))
    (falsum : C ⊥)
    (imp : ∀ A B, C (A 🡒 B))
    (box : ∀ A, C (□A))
    (rhd : ∀ A B, C (A ▷ B)) :
    (A : Formula α) → C A
  | #a => atom a
  | .falsum => falsum
  | .imp A B => imp A B
  | .box A => box A
  | .rhd A B => rhd A B

end Formula

end FFL.InterpretabilityLogic

end
