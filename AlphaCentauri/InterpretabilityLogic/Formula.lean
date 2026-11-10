module

public import Foundation.Logic.LogicSymbol
public import Mathlib.Data.Finset.Basic

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

/-! ### Subformulas -/

section

variable {α : Type*} [DecidableEq α]

namespace Formula

def subformulas : Formula α → Finset (Formula α)
  | #a    => {#a}
  | ⊥     => {⊥}
  | A 🡒 B => insert (A 🡒 B) (A.subformulas ∪ B.subformulas)
  | □A    => insert (□A) A.subformulas
  | A ▷ B => insert (A ▷ B) (A.subformulas ∪ B.subformulas)

variable {A B : Formula α}

@[simp] lemma mem_subformulas_self : A ∈ A.subformulas := by
  cases A <;> simp [subformulas];

lemma subformulas_subset_of_mem (h : B ∈ A.subformulas) : B.subformulas ⊆ A.subformulas := by
  induction A with
  | atom a => simp_all [subformulas];
  | falsum => simp_all [subformulas];
  | imp A₁ A₂ ih₁ ih₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with rfl | h | h;
    · rfl;
    · exact (ih₁ h).trans <| fun x hx ↦ by simp [subformulas, hx];
    · exact (ih₂ h).trans <| fun x hx ↦ by simp [subformulas, hx];
  | box A ih =>
    simp only [subformulas, Finset.mem_insert] at h;
    rcases h with rfl | h;
    · rfl;
    · exact (ih h).trans <| fun x hx ↦ by simp [subformulas, hx];
  | rhd A₁ A₂ ih₁ ih₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with rfl | h | h;
    · rfl;
    · exact (ih₁ h).trans <| fun x hx ↦ by simp [subformulas, hx];
    · exact (ih₂ h).trans <| fun x hx ↦ by simp [subformulas, hx];

end Formula

end

end FFL.InterpretabilityLogic

end
