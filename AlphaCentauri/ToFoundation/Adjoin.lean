module

public import Foundation.FirstOrder.LK.Basic
public import Foundation.Meta.ClProver

/-!
# Adjoining the negations of a list of sentences

Adjoining `∼φ` for every `φ` in a list is, as far as provability goes, the same as weakening the
goal by the disjunction of the list.
-/

@[expose] public section

namespace FFL.Entailment

open FFL.FirstOrder

variable {L : Language} [L.DecidableEq] {T : Theory L}

/-- The theory obtained by adjoining `∼φ` for every `φ` in `l`. -/
def adjoinNegs (T : Theory L) : List (Sentence L) → Theory L
  | [] => T
  | φ :: l => adjoin (∼φ) (adjoinNegs T l)

omit [L.DecidableEq] in
@[simp] lemma adjoinNegs_nil : adjoinNegs T [] = T := rfl

omit [L.DecidableEq] in
@[simp] lemma adjoinNegs_cons {φ : Sentence L} {l : List (Sentence L)} :
    adjoinNegs T (φ :: l) = adjoin (∼φ) (adjoinNegs T l) := rfl

/-- Proving `χ` from `T` with the negations of `l` adjoined is proving `l.disj ⋎ χ` from `T`. -/
lemma provable_adjoinNegs_iff :
    ∀ (l : List (Sentence L)) (χ : Sentence L), adjoinNegs T l ⊢ χ ↔ T ⊢ l.disj ⋎ χ
  | [], χ => by
    simp only [adjoinNegs_nil, List.disj]
    constructor
    · intro h; cl_prover [h]
    · intro h; cl_prover [h]
  | φ :: l, χ => by
    rw [adjoinNegs_cons, deduction_iff, provable_adjoinNegs_iff l, List.disj]
    constructor
    · intro h; cl_prover [h]
    · intro h; cl_prover [h]

omit [L.DecidableEq] in
/-- Membership in `adjoinNegs T l`. -/
@[simp] lemma mem_adjoinNegs {ψ : Sentence L} :
    ∀ {l : List (Sentence L)}, ψ ∈ adjoinNegs T l ↔ (∃ φ ∈ l, ψ = ∼φ) ∨ ψ ∈ T
  | [] => by simp
  | φ :: l => by simp [mem_adjoinNegs (l := l), or_assoc]

/-- Adjoining the negations of `l` keeps the theory consistent as long as it does not prove the
disjunction of `l`. -/
lemma consistent_adjoinNegs {l : List (Sentence L)} (h : T ⊬ l.disj) :
    Consistent (adjoinNegs T l) := by
  apply consistent_iff_unprovable_bot.mpr
  intro hb
  exact h (by have := (provable_adjoinNegs_iff l ⊥).mp hb; cl_prover [this])

end FFL.Entailment
