module

public import AlphaCentauri.Bootstrapping.Delta0
public import AlphaCentauri.Bootstrapping.TermVal

/-!
# Partial satisfaction tables

This module defines `PSatZero`, the partial satisfaction table for an internally coded `Δ₀`
formula under an assignment, proves it is `𝚫₁`, and proves that a table for a fixed root is
unique.

- [HP98, Definition I.1.71(1)]
- [HP98, Lemma I.1.72(1), (2)]
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Arithmetic (qqEQ qqNEQ qqLT qqNLT)

section coding

-- Unfolding these coding operations to their underlying pairs, together with the default simp
-- set (numeral facts, `pair_ext_iff`), is exactly what is needed to tell two differently-shaped
-- coded formulas apart when reading `spec` off at a node. Scoped to this section, since
-- unconditionally unfolding these constructors defeats the ordinary simp set on coded formulas.
attribute [local simp] qqAnd qqOr qqVerum qqFalsum qqRel qqNRel qqBall qqAll qqBex qqExs
  Arithmetic.qqEQ Arithmetic.qqNEQ Arithmetic.qqLT Arithmetic.qqNLT

/-! ## Coding injectivity facts for the bounded quantifiers -/

/-- The bounded universal coding operation is injective in both arguments.
- This is a routine coding fact; no separate source theorem. -/
@[simp] lemma qqBall_inj {u₁ q₁ u₂ q₂ : V} : qqBall u₁ q₁ = qqBall u₂ q₂ ↔ u₁ = u₂ ∧ q₁ = q₂ := by
  simp [qqBall, Arithmetic.qqNLT, qqNRel, adjoin_inj]

/-- The bounded existential coding operation is injective in both arguments.
- This is a routine coding fact; no separate source theorem. -/
@[simp] lemma qqBex_inj {u₁ q₁ u₂ q₂ : V} : qqBex u₁ q₁ = qqBex u₂ q₂ ↔ u₁ = u₂ ∧ q₁ = q₂ := by
  simp [qqBex, Arithmetic.qqLT, qqRel, adjoin_inj]

/-- The coded equality atom is injective in both arguments.
- This is a routine coding fact; no separate source theorem. -/
@[simp] lemma qqEQ_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^= u₁ = t₂ ^= u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Arithmetic.qqEQ, qqRel, adjoin_inj]

/-- The coded inequality atom is injective in both arguments.
- This is a routine coding fact; no separate source theorem. -/
@[simp] lemma qqNEQ_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^≠ u₁ = t₂ ^≠ u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Arithmetic.qqNEQ, qqNRel, adjoin_inj]

/-- The coded less-than atom is injective in both arguments.
- This is a routine coding fact; no separate source theorem. -/
@[simp] lemma qqLT_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^< u₁ = t₂ ^< u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Arithmetic.qqLT, qqRel, adjoin_inj]

/-- The coded not-less-than atom is injective in both arguments.
- This is a routine coding fact; no separate source theorem. -/
@[simp] lemma qqNLT_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^≮ u₁ = t₂ ^≮ u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Arithmetic.qqNLT, qqNRel, adjoin_inj]

/-- The relation index of coded equality, read off in `V`.
- This is a routine coding fact; no separate source theorem. -/
@[simp] lemma coe_eqIndex_eq : (Arithmetic.eqIndex : V) = 0 := rfl

/-- The relation index of coded less-than, read off in `V`.
- This is a routine coding fact; no separate source theorem. -/
@[simp] lemma coe_ltIndex_eq : (Arithmetic.ltIndex : V) = 1 := by simp [Arithmetic.ltIndex]; rfl

/-- The two relation indices of `ℒₒᵣ` are distinct.
- This is a routine coding fact; no separate source theorem. -/
lemma eqIndex_ne_ltIndex : (Arithmetic.eqIndex : V) ≠ (Arithmetic.ltIndex : V) := by simp

/-! ## The partial satisfaction table -/

/-- `PSatZero q z e` says that `q` is a partial satisfaction table for the `Δ₀` formula `z`
under assignment `e`: `q` is a finite mapping whose domain is the downward closure of the root
`⟪z, e⟫` under immediate subformulas (extending the assignment by `x ∷ e'` when entering a
bounded quantifier), and which carries `0`/`1` values obeying Tarski's clauses at every node of
its domain.

- [HP98, Definition I.1.71(1)] -/
structure PSatZero (q z e : V) : Prop where
  /-- `q` is a finite mapping. -/
  isMapping : IsMapping q
  /-- The root belongs to the domain. -/
  mem_dom_root : ⟪z, e⟫ ∈ domain q
  /-- At every node of the domain, `q` obeys the Tarski clause for that node's outermost
  constructor, and (for the compound constructors) the node's immediate children also belong
  to the domain. -/
  spec : ∀ z' e', ⟪z', e'⟫ ∈ domain q →
    (z' = ^⊤ ∧ ⟪⟪z', e'⟫, 1⟫ ∈ q) ∨
    (z' = ^⊥ ∧ ⟪⟪z', e'⟫, 0⟫ ∈ q) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z' = t ^= u ∧
      (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ termVal e' t = termVal e' u) ∧
      (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ termVal e' t ≠ termVal e' u)) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z' = t ^≠ u ∧
      (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ termVal e' t ≠ termVal e' u) ∧
      (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ termVal e' t = termVal e' u)) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z' = t ^< u ∧
      (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ termVal e' t < termVal e' u) ∧
      (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ ¬termVal e' t < termVal e' u)) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z' = t ^≮ u ∧
      (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ ¬termVal e' t < termVal e' u) ∧
      (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ termVal e' t < termVal e' u)) ∨
    (∃ p₁ p₂, z' = p₁ ^⋏ p₂ ∧ ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q ∧
      (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 1⟫ ∈ q) ∧
      (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 0⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 0⟫ ∈ q)) ∨
    (∃ p₁ p₂, z' = p₁ ^⋎ p₂ ∧ ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q ∧
      (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 1⟫ ∈ q) ∧
      (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 0⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 0⟫ ∈ q)) ∨
    (∃ u p, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ z' = qqBall u p ∧
      (∀ x < termVal (0 ∷ e') u, ⟪p, x ∷ e'⟫ ∈ domain q) ∧
      (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q) ∧
      (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 0⟫ ∈ q)) ∨
    (∃ u p, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ z' = qqBex u p ∧
      (∀ x < termVal (0 ∷ e') u, ⟪p, x ∷ e'⟫ ∈ domain q) ∧
      (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q) ∧
      (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 0⟫ ∈ q))
  /-- Every node of the domain other than the root has an immediate parent in the domain: the
  domain is exactly the downward closure of the root, not merely a superset of it. -/
  minimal : ∀ n ∈ domain q, n = ⟪z, e⟫ ∨
    (∃ p₁ p₂ e', ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
    (∃ p₁ p₂ e', ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
    (∃ u p e', ⟪qqBall u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫) ∨
    (∃ u p e', ⟪qqBex u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫)


namespace PSatZero

variable {q q₁ q₂ z z₁ z₂ e e₁ e₂ z' e' t u p p₁ p₂ : V}

/-! ## Reading `spec` off at a node of known shape

`spec` is a ten-way disjunction over the outermost coding constructor of the node. Each lemma
below selects the disjunct matching a node of known shape and returns all of its content: that
the immediate children belong to the domain, and how the values `1` and `0` at the node are
determined. -/

/-- Case analysis of `spec` at a node known to be the coded truth constant.
- [HP98, Definition I.1.71(1)] -/
lemma val_verum (h : PSatZero q z e) (hn : ⟪(^⊤ : V), e'⟫ ∈ domain q) :
    ⟪⟪(^⊤ : V), e'⟫, 1⟫ ∈ q := by
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  on_goal 1 => exact hv
  all_goals simp at he

/-- Case analysis of `spec` at a node known to be the coded falsehood constant.
- [HP98, Definition I.1.71(1)] -/
lemma val_falsum (h : PSatZero q z e) (hn : ⟪(^⊥ : V), e'⟫ ∈ domain q) :
    ⟪⟪(^⊥ : V), e'⟫, 0⟫ ∈ q := by
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  on_goal 2 => exact hv
  all_goals simp at he

/-- The Tarski clauses for a coded equality atom, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma spec_eq (h : PSatZero q z e) (hn : ⟪t ^= u, e'⟫ ∈ domain q) :
    (⟪⟪t ^= u, e'⟫, 1⟫ ∈ q ↔ termVal e' t = termVal e' u) ∧
    (⟪⟪t ^= u, e'⟫, 0⟫ ∈ q ↔ termVal e' t ≠ termVal e' u) := by
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  on_goal 3 => obtain ⟨rfl, rfl⟩ := qqEQ_inj.mp he; exact ⟨hA, hB⟩
  all_goals simp at he

/-- The Tarski clauses for a coded inequality atom, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma spec_neq (h : PSatZero q z e) (hn : ⟪t ^≠ u, e'⟫ ∈ domain q) :
    (⟪⟪t ^≠ u, e'⟫, 1⟫ ∈ q ↔ termVal e' t ≠ termVal e' u) ∧
    (⟪⟪t ^≠ u, e'⟫, 0⟫ ∈ q ↔ termVal e' t = termVal e' u) := by
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  on_goal 4 => obtain ⟨rfl, rfl⟩ := qqNEQ_inj.mp he; exact ⟨hA, hB⟩
  all_goals simp at he

/-- The Tarski clauses for a coded less-than atom, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma spec_lt (h : PSatZero q z e) (hn : ⟪t ^< u, e'⟫ ∈ domain q) :
    (⟪⟪t ^< u, e'⟫, 1⟫ ∈ q ↔ termVal e' t < termVal e' u) ∧
    (⟪⟪t ^< u, e'⟫, 0⟫ ∈ q ↔ ¬termVal e' t < termVal e' u) := by
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  on_goal 5 => obtain ⟨rfl, rfl⟩ := qqLT_inj.mp he; exact ⟨hA, hB⟩
  all_goals simp at he

/-- The Tarski clauses for a coded not-less-than atom, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma spec_nlt (h : PSatZero q z e) (hn : ⟪t ^≮ u, e'⟫ ∈ domain q) :
    (⟪⟪t ^≮ u, e'⟫, 1⟫ ∈ q ↔ ¬termVal e' t < termVal e' u) ∧
    (⟪⟪t ^≮ u, e'⟫, 0⟫ ∈ q ↔ termVal e' t < termVal e' u) := by
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  on_goal 6 => obtain ⟨rfl, rfl⟩ := qqNLT_inj.mp he; exact ⟨hA, hB⟩
  all_goals simp at he

/-- The Tarski clauses for a coded conjunction, at a node of the domain, together with
membership of its immediate subformulas in the domain.
- [HP98, Definition I.1.71(1)] -/
lemma spec_and (h : PSatZero q z e) (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q ∧
    (⟪⟪p₁ ^⋏ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪p₁ ^⋏ p₂, e'⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 0⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 0⟫ ∈ q) := by
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  on_goal 7 => obtain ⟨rfl, rfl⟩ := (qqAnd_inj _ _ _ _).mp he; exact ⟨hd, hd', hA, hB⟩
  all_goals simp at he

/-- The Tarski clauses for a coded disjunction, at a node of the domain, together with
membership of its immediate subformulas in the domain.
- [HP98, Definition I.1.71(1)] -/
lemma spec_or (h : PSatZero q z e) (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q ∧
    (⟪⟪p₁ ^⋎ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪p₁ ^⋎ p₂, e'⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 0⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 0⟫ ∈ q) := by
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  on_goal 8 => obtain ⟨rfl, rfl⟩ := (qqOr_inj _ _ _ _).mp he; exact ⟨hd, hd', hA, hB⟩
  all_goals simp at he

/-- The Tarski clauses for a coded bounded universal, at a node of the domain, together with
membership of its body in the domain under every extended assignment.
- [HP98, Definition I.1.71(1)] -/
lemma spec_ball (h : PSatZero q z e) (hn : ⟪qqBall u p, e'⟫ ∈ domain q) :
    (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧
    (∀ x < termVal (0 ∷ e') u, ⟪p, x ∷ e'⟫ ∈ domain q) ∧
    (⟪⟪qqBall u p, e'⟫, 1⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪qqBall u p, e'⟫, 0⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 0⟫ ∈ q) := by
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  on_goal 9 => obtain ⟨rfl, rfl⟩ := qqBall_inj.mp he; exact ⟨ht, hd, hA, hB⟩
  all_goals simp at he

/-- The Tarski clauses for a coded bounded existential, at a node of the domain, together with
membership of its body in the domain under every extended assignment.
- [HP98, Definition I.1.71(1)] -/
lemma spec_bex (h : PSatZero q z e) (hn : ⟪qqBex u p, e'⟫ ∈ domain q) :
    (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧
    (∀ x < termVal (0 ∷ e') u, ⟪p, x ∷ e'⟫ ∈ domain q) ∧
    (⟪⟪qqBex u p, e'⟫, 1⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪qqBex u p, e'⟫, 0⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 0⟫ ∈ q) := by
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  on_goal 10 => obtain ⟨rfl, rfl⟩ := qqBex_inj.mp he; exact ⟨ht, hd, hA, hB⟩
  all_goals simp at he

/-! ## The Tarski clauses in the form the satisfaction predicate uses -/

/-- Satisfaction of a coded equality atom, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_eq (h : PSatZero q z e) (hn : ⟪t ^= u, e'⟫ ∈ domain q) :
    ⟪⟪t ^= u, e'⟫, 1⟫ ∈ q ↔ termVal e' t = termVal e' u := (h.spec_eq hn).1

/-- Satisfaction of a coded inequality atom, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_neq (h : PSatZero q z e) (hn : ⟪t ^≠ u, e'⟫ ∈ domain q) :
    ⟪⟪t ^≠ u, e'⟫, 1⟫ ∈ q ↔ termVal e' t ≠ termVal e' u := (h.spec_neq hn).1

/-- Satisfaction of a coded less-than atom, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_lt (h : PSatZero q z e) (hn : ⟪t ^< u, e'⟫ ∈ domain q) :
    ⟪⟪t ^< u, e'⟫, 1⟫ ∈ q ↔ termVal e' t < termVal e' u := (h.spec_lt hn).1

/-- Satisfaction of a coded not-less-than atom, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_nlt (h : PSatZero q z e) (hn : ⟪t ^≮ u, e'⟫ ∈ domain q) :
    ⟪⟪t ^≮ u, e'⟫, 1⟫ ∈ q ↔ ¬termVal e' t < termVal e' u := (h.spec_nlt hn).1

/-- Immediate subformulas of a coded conjunction in the domain also belong to the domain.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_and (h : PSatZero q z e) (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q :=
  ⟨(h.spec_and hn).1, (h.spec_and hn).2.1⟩

/-- The Tarski clause for conjunction, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_and (h : PSatZero q z e) (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪⟪p₁ ^⋏ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 1⟫ ∈ q := (h.spec_and hn).2.2.1

/-- Immediate subformulas of a coded disjunction in the domain also belong to the domain.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_or (h : PSatZero q z e) (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q :=
  ⟨(h.spec_or hn).1, (h.spec_or hn).2.1⟩

/-- The Tarski clause for disjunction, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_or (h : PSatZero q z e) (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪⟪p₁ ^⋎ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 1⟫ ∈ q := (h.spec_or hn).2.2.1

/-- Immediate subformulas of a coded bounded universal in the domain also belong to the domain,
under the extended assignment.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_ball (h : PSatZero q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) {x : V} (hx : x < termVal e' t) :
    ⟪p, x ∷ e'⟫ ∈ domain q :=
  (h.spec_ball hn).2.1 x (by rwa [termVal_termBShift ht])

/-- The Tarski clause for the bounded universal, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_ball (h : PSatZero q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) :
    ⟪⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫, 1⟫ ∈ q ↔ ∀ x < termVal e' t, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q := by
  have := (h.spec_ball hn).2.2.1
  rwa [termVal_termBShift ht] at this

/-- Immediate subformulas of a coded bounded existential in the domain also belong to the
domain, under the extended assignment.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_bex (h : PSatZero q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) {x : V} (hx : x < termVal e' t) :
    ⟪p, x ∷ e'⟫ ∈ domain q :=
  (h.spec_bex hn).2.1 x (by rwa [termVal_termBShift ht])

/-- The Tarski clause for the bounded existential, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_bex (h : PSatZero q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) :
    ⟪⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫, 1⟫ ∈ q ↔ ∃ x < termVal e' t, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q := by
  have := (h.spec_bex hn).2.2.1
  rwa [termVal_termBShift ht] at this

end PSatZero

end coding

namespace PSatZero

variable {q q₁ q₂ z z₁ z₂ e e₁ e₂ p : V}

/-! ## Uniqueness -/

/-- A node of the domain of a finite mapping is smaller than the mapping. -/
private lemma lt_of_mem_domain {n q : V} (h : n ∈ domain q) : n < q := by
  obtain ⟨y, hy⟩ := mem_domain_iff.mp h
  exact lt_of_mem_dom hy

/-- A table takes at most one value at each node, so `0` and `1` cannot both occur. -/
lemma val_one_ne_zero (h : PSatZero q z e) {n : V} (h1 : ⟪n, 1⟫ ∈ q) (h0 : ⟪n, 0⟫ ∈ q) : False := by
  simpa using h.isMapping.uniq h1 h0

/-- Every node of the domain carries the value `1` or the value `0`.
- [HP98, Definition I.1.71(1)] -/
lemma val_zero_or_one (h : PSatZero q z e) :
    ∀ p e', ⟪p, e'⟫ ∈ domain q → ⟪⟪p, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p, e'⟫, 0⟫ ∈ q := by
  refine ISigma1.pi1_order_induction
    (P := fun p ↦ ∀ e', ⟪p, e'⟫ ∈ domain q → ⟪⟪p, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p, e'⟫, 0⟫ ∈ q)
    (by definability) ?_
  intro p ih e' hn
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  · exact Or.inl hv
  · exact Or.inr hv
  · by_cases h' : termVal e' a = termVal e' b
    · exact Or.inl (hA.mpr h')
    · exact Or.inr (hB.mpr h')
  · by_cases h' : termVal e' a = termVal e' b
    · exact Or.inr (hB.mpr h')
    · exact Or.inl (hA.mpr h')
  · by_cases h' : termVal e' a < termVal e' b
    · exact Or.inl (hA.mpr h')
    · exact Or.inr (hB.mpr h')
  · by_cases h' : termVal e' a < termVal e' b
    · exact Or.inr (hB.mpr h')
    · exact Or.inl (hA.mpr h')
  · subst he
    rcases ih a (by simp) e' hd with h1 | h1
    · rcases ih b (by simp) e' hd' with h2 | h2
      · exact Or.inl (hA.mpr ⟨h1, h2⟩)
      · exact Or.inr (hB.mpr (Or.inr h2))
    · exact Or.inr (hB.mpr (Or.inl h1))
  · subst he
    rcases ih a (by simp) e' hd with h1 | h1
    · exact Or.inl (hA.mpr (Or.inl h1))
    · rcases ih b (by simp) e' hd' with h2 | h2
      · exact Or.inl (hA.mpr (Or.inr h2))
      · exact Or.inr (hB.mpr ⟨h1, h2⟩)
  · subst he
    by_cases hall : ∀ x < termVal (0 ∷ e') a, ⟪⟪b, x ∷ e'⟫, 1⟫ ∈ q
    · exact Or.inl (hA.mpr hall)
    · push Not at hall
      obtain ⟨x, hx, hx1⟩ := hall
      rcases ih b (by simp) (x ∷ e') (hd x hx) with h' | h'
      · exact absurd h' hx1
      · exact Or.inr (hB.mpr ⟨x, hx, h'⟩)
  · subst he
    by_cases hall : ∀ x < termVal (0 ∷ e') a, ⟪⟪b, x ∷ e'⟫, 0⟫ ∈ q
    · exact Or.inr (hB.mpr hall)
    · push Not at hall
      obtain ⟨x, hx, hx0⟩ := hall
      rcases ih b (by simp) (x ∷ e') (hd x hx) with h' | h'
      · exact Or.inl (hA.mpr ⟨x, hx, h'⟩)
      · exact absurd h' hx0

/-- Two tables agree at every node that belongs to both domains: this is the agreement half of
uniqueness, and it does not require the two tables to have the same root.
- [HP98, Lemma I.1.72(2)] -/
lemma agree (h₁ : PSatZero q₁ z₁ e₁) (h₂ : PSatZero q₂ z₂ e₂) :
    ∀ p e', ⟪p, e'⟫ ∈ domain q₁ → ⟪p, e'⟫ ∈ domain q₂ →
      (⟪⟪p, e'⟫, 1⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 1⟫ ∈ q₂) ∧
      (⟪⟪p, e'⟫, 0⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 0⟫ ∈ q₂) := by
  refine ISigma1.pi1_order_induction
    (P := fun p ↦ ∀ e', ⟪p, e'⟫ ∈ domain q₁ → ⟪p, e'⟫ ∈ domain q₂ →
      (⟪⟪p, e'⟫, 1⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 1⟫ ∈ q₂) ∧
      (⟪⟪p, e'⟫, 0⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 0⟫ ∈ q₂))
    (by definability) ?_
  intro p ih e' hn₁ hn₂
  rcases h₁.spec _ e' hn₁ with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  · subst he
    have hv₂ := h₂.val_verum hn₂
    exact ⟨iff_of_true hv hv₂, iff_of_false (h₁.val_one_ne_zero hv) (h₂.val_one_ne_zero hv₂)⟩
  · subst he
    have hv₂ := h₂.val_falsum hn₂
    exact ⟨iff_of_false (fun hc ↦ h₁.val_one_ne_zero hc hv) (fun hc ↦ h₂.val_one_ne_zero hc hv₂),
      iff_of_true hv hv₂⟩
  · subst he
    obtain ⟨hA₂, hB₂⟩ := h₂.spec_eq hn₂
    exact ⟨hA.trans hA₂.symm, hB.trans hB₂.symm⟩
  · subst he
    obtain ⟨hA₂, hB₂⟩ := h₂.spec_neq hn₂
    exact ⟨hA.trans hA₂.symm, hB.trans hB₂.symm⟩
  · subst he
    obtain ⟨hA₂, hB₂⟩ := h₂.spec_lt hn₂
    exact ⟨hA.trans hA₂.symm, hB.trans hB₂.symm⟩
  · subst he
    obtain ⟨hA₂, hB₂⟩ := h₂.spec_nlt hn₂
    exact ⟨hA.trans hA₂.symm, hB.trans hB₂.symm⟩
  · subst he
    obtain ⟨hd₂, hd₂', hA₂, hB₂⟩ := h₂.spec_and hn₂
    obtain ⟨i1, i0⟩ := ih a (by simp) e' hd hd₂
    obtain ⟨j1, j0⟩ := ih b (by simp) e' hd' hd₂'
    exact ⟨by rw [hA, hA₂, i1, j1], by rw [hB, hB₂, i0, j0]⟩
  · subst he
    obtain ⟨hd₂, hd₂', hA₂, hB₂⟩ := h₂.spec_or hn₂
    obtain ⟨i1, i0⟩ := ih a (by simp) e' hd hd₂
    obtain ⟨j1, j0⟩ := ih b (by simp) e' hd' hd₂'
    exact ⟨by rw [hA, hA₂, i1, j1], by rw [hB, hB₂, i0, j0]⟩
  · subst he
    obtain ⟨ht₂, hd₂, hA₂, hB₂⟩ := h₂.spec_ball hn₂
    have key : ∀ x < termVal (0 ∷ e') a,
        (⟪⟪b, x ∷ e'⟫, 1⟫ ∈ q₁ ↔ ⟪⟪b, x ∷ e'⟫, 1⟫ ∈ q₂) ∧
        (⟪⟪b, x ∷ e'⟫, 0⟫ ∈ q₁ ↔ ⟪⟪b, x ∷ e'⟫, 0⟫ ∈ q₂) :=
      fun x hx ↦ ih b (by simp) (x ∷ e') (hd x hx) (hd₂ x hx)
    refine ⟨?_, ?_⟩
    · rw [hA, hA₂]
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦ (key x hx).1
    · rw [hB, hB₂]
      exact exists_congr fun x ↦ and_congr_right fun hx ↦ (key x hx).2
  · subst he
    obtain ⟨ht₂, hd₂, hA₂, hB₂⟩ := h₂.spec_bex hn₂
    have key : ∀ x < termVal (0 ∷ e') a,
        (⟪⟪b, x ∷ e'⟫, 1⟫ ∈ q₁ ↔ ⟪⟪b, x ∷ e'⟫, 1⟫ ∈ q₂) ∧
        (⟪⟪b, x ∷ e'⟫, 0⟫ ∈ q₁ ↔ ⟪⟪b, x ∷ e'⟫, 0⟫ ∈ q₂) :=
      fun x hx ↦ ih b (by simp) (x ∷ e') (hd x hx) (hd₂ x hx)
    refine ⟨?_, ?_⟩
    · rw [hA, hA₂]
      exact exists_congr fun x ↦ and_congr_right fun hx ↦ (key x hx).1
    · rw [hB, hB₂]
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦ (key x hx).2

/-- Two tables for the same root have the same domain.
- [HP98, Lemma I.1.72(2)] -/
lemma dom_subset (h₁ : PSatZero q₁ z e) (h₂ : PSatZero q₂ z e) :
    ∀ n ∈ domain q₁, n ∈ domain q₂ := by
  have key : ∀ k n, n ∈ domain q₁ → q₁ ≤ π₁ n + k → n ∈ domain q₂ := by
    refine ISigma1.pi1_succ_induction
      (P := fun k ↦ ∀ n, n ∈ domain q₁ → q₁ ≤ π₁ n + k → n ∈ domain q₂)
      (by definability) ?_ ?_
    · intro n hn hle
      exact absurd (by simpa using hle)
        (not_le.mpr (lt_of_le_of_lt (pi₁_le_self n) (lt_of_mem_domain hn)))
    · intro k IH n hn hle
      have up : ∀ m, m ∈ domain q₁ → π₁ n < π₁ m → m ∈ domain q₂ := by
        intro m hm hlt
        refine IH m hm ?_
        calc q₁ ≤ π₁ n + (k + 1) := hle
          _ = π₁ n + 1 + k := by simp [add_assoc, add_comm]
          _ ≤ π₁ m + k := add_le_add (lt_iff_succ_le.mp hlt) le_rfl
      rcases h₁.minimal n hn with rfl | ⟨a, b, e'', hm, hc⟩ | ⟨a, b, e'', hm, hc⟩ |
        ⟨u, r, e'', hm, x, hx, rfl⟩ | ⟨u, r, e'', hm, x, hx, rfl⟩
      · exact h₂.mem_dom_root
      · rcases hc with rfl | rfl
        · exact (h₂.spec_and (up _ hm (by simp))).1
        · exact (h₂.spec_and (up _ hm (by simp))).2.1
      · rcases hc with rfl | rfl
        · exact (h₂.spec_or (up _ hm (by simp))).1
        · exact (h₂.spec_or (up _ hm (by simp))).2.1
      · exact (h₂.spec_ball (up _ hm (by simp))).2.1 x hx
      · exact (h₂.spec_bex (up _ hm (by simp))).2.1 x hx
  exact fun n hn ↦ key q₁ n hn le_add_self

/-- A partial satisfaction table for a fixed formula and assignment is unique.
- [HP98, Lemma I.1.72(2)] -/
theorem uniq (h₁ : PSatZero q₁ z e) (h₂ : PSatZero q₂ z e) : q₁ = q₂ := by
  have sub : ∀ {r₁ r₂ : V}, PSatZero r₁ z e → PSatZero r₂ z e → ∀ x, x ∈ r₁ → x ∈ r₂ := by
    intro r₁ r₂ k₁ k₂ x hx
    have hx' : ⟪π₁ x, π₂ x⟫ ∈ r₁ := by rwa [pair_unpair]
    have hn₁ : ⟪π₁ (π₁ x), π₂ (π₁ x)⟫ ∈ domain r₁ := by
      rw [pair_unpair]; exact mem_domain_of_pair_mem hx'
    have hn₂ : ⟪π₁ (π₁ x), π₂ (π₁ x)⟫ ∈ domain r₂ := by
      rw [pair_unpair]; exact k₁.dom_subset k₂ _ (mem_domain_of_pair_mem hx')
    obtain ⟨i1, i0⟩ := k₁.agree k₂ (π₁ (π₁ x)) (π₂ (π₁ x)) hn₁ hn₂
    rw [pair_unpair] at i1 i0
    rcases k₁.val_zero_or_one (π₁ (π₁ x)) (π₂ (π₁ x)) hn₁ with h' | h' <;> rw [pair_unpair] at h'
    · have hv : π₂ x = 1 := k₁.isMapping.uniq hx' h'
      have hxe : x = ⟪π₁ x, 1⟫ := by rw [← hv, pair_unpair]
      rw [hxe]; exact i1.mp h'
    · have hv : π₂ x = 0 := k₁.isMapping.uniq hx' h'
      have hxe : x = ⟪π₁ x, 0⟫ := by rw [← hv, pair_unpair]
      rw [hxe]; exact i0.mp h'
  exact mem_ext fun i ↦ ⟨sub h₁ h₂ i, sub h₂ h₁ i⟩

end PSatZero

end LO.FirstOrder.Arithmetic.Bootstrapping
