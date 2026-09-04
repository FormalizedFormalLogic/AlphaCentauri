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

-- Unfolding these coding operations to their underlying pairs, together with the default simp
-- set (numeral facts, `pair_ext_iff`), is exactly what is needed throughout this file to tell
-- two differently-shaped coded formulas apart. Local to this file, since unconditionally
-- unfolding these constructors is not desirable elsewhere.
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
    (∃ t p e' x, ⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q ∧ x < termVal e' t ∧
      n = ⟪p, x ∷ e'⟫) ∨
    (∃ t p e' x, ⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q ∧ x < termVal e' t ∧
      n = ⟪p, x ∷ e'⟫)

namespace PSatZero

variable {q z e z' e' t u p p₁ p₂ : V}

/-- Case analysis of `spec` at a node known to be the coded truth constant. -/
lemma val_verum (h : PSatZero q z e) (hn : ⟪(^⊤ : V), e'⟫ ∈ domain q) :
    ⟪⟪(^⊤ : V), e'⟫, 1⟫ ∈ q := by
  rcases h.spec _ e' hn with ⟨-, hv⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, heq, -⟩ | ⟨_, _, heq, -⟩
    | ⟨_, _, _, heq, -⟩ | ⟨_, _, _, heq, -⟩
  · exact hv
  all_goals simp at heq

/-- Case analysis of `spec` at a node known to be the coded falsehood constant. -/
lemma val_falsum (h : PSatZero q z e) (hn : ⟪(^⊥ : V), e'⟫ ∈ domain q) :
    ⟪⟪(^⊥ : V), e'⟫, 0⟫ ∈ q := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨-, hv⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, heq, -⟩ | ⟨_, _, heq, -⟩
    | ⟨_, _, _, heq, -⟩ | ⟨_, _, _, heq, -⟩
  · simp at heq
  · exact hv
  all_goals simp at heq

/-- Case analysis of `spec` at a node known to be a coded equality atom. -/
lemma val_eq (h : PSatZero q z e) (_ht : IsUTerm ℒₒᵣ t) (_hu : IsUTerm ℒₒᵣ u)
    (hn : ⟪t ^= u, e'⟫ ∈ domain q) :
    ⟪⟪t ^= u, e'⟫, 1⟫ ∈ q ↔ termVal e' t = termVal e' u := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨t', u', ht', hu', heq, hiff, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, heq, -⟩
    | ⟨_, _, heq, -⟩ | ⟨_, _, _, heq, -⟩ | ⟨_, _, _, heq, -⟩
  · simp at heq
  · simp at heq
  · obtain ⟨rfl, rfl⟩ := qqEQ_inj.mp heq
    exact hiff
  all_goals simp at heq

/-- Case analysis of `spec` at a node known to be a coded inequality atom. -/
lemma val_neq (h : PSatZero q z e) (_ht : IsUTerm ℒₒᵣ t) (_hu : IsUTerm ℒₒᵣ u)
    (hn : ⟪t ^≠ u, e'⟫ ∈ domain q) :
    ⟪⟪t ^≠ u, e'⟫, 1⟫ ∈ q ↔ termVal e' t ≠ termVal e' u := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨t', u', ht', hu', heq, hiff, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, heq, -⟩ | ⟨_, _, heq, -⟩ | ⟨_, _, _, heq, -⟩ | ⟨_, _, _, heq, -⟩
  · simp at heq
  · simp at heq
  · simp at heq
  · obtain ⟨rfl, rfl⟩ := qqNEQ_inj.mp heq
    exact hiff
  all_goals simp at heq

/-- Case analysis of `spec` at a node known to be a coded less-than atom. -/
lemma val_lt (h : PSatZero q z e) (_ht : IsUTerm ℒₒᵣ t) (_hu : IsUTerm ℒₒᵣ u)
    (hn : ⟪t ^< u, e'⟫ ∈ domain q) :
    ⟪⟪t ^< u, e'⟫, 1⟫ ∈ q ↔ termVal e' t < termVal e' u := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨t', u', ht', hu', heq, hiff, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, heq, -⟩ | ⟨_, _, heq, -⟩
    | ⟨_, _, _, heq, -⟩ | ⟨_, _, _, heq, -⟩
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · obtain ⟨rfl, rfl⟩ := qqLT_inj.mp heq
    exact hiff
  all_goals simp at heq

/-- Case analysis of `spec` at a node known to be a coded not-less-than atom. -/
lemma val_nlt (h : PSatZero q z e) (_ht : IsUTerm ℒₒᵣ t) (_hu : IsUTerm ℒₒᵣ u)
    (hn : ⟪t ^≮ u, e'⟫ ∈ domain q) :
    ⟪⟪t ^≮ u, e'⟫, 1⟫ ∈ q ↔ ¬termVal e' t < termVal e' u := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨t', u', ht', hu', heq, hiff, -⟩ | ⟨_, _, heq, -⟩ | ⟨_, _, heq, -⟩
    | ⟨_, _, _, heq, -⟩ | ⟨_, _, _, heq, -⟩
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · obtain ⟨rfl, rfl⟩ := qqNLT_inj.mp heq
    exact hiff
  all_goals simp at heq

/-- Immediate subformulas of a coded conjunction in the domain also belong to the domain.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_and (h : PSatZero q z e) (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨p₁', p₂', heq, hd1, hd2, -⟩ | ⟨_, _, heq, -⟩ | ⟨_, _, _, heq, -⟩ | ⟨_, _, _, heq, -⟩
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · obtain ⟨rfl, rfl⟩ := (qqAnd_inj p₁ p₂ p₁' p₂').mp heq
    exact ⟨hd1, hd2⟩
  · simp at heq
  · simp at heq
  · simp at heq

/-- The Tarski clause for conjunction, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_and (h : PSatZero q z e) (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪⟪p₁ ^⋏ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 1⟫ ∈ q := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨p₁', p₂', heq, hd1, hd2, hiff, -⟩ | ⟨_, _, heq, -⟩ | ⟨_, _, _, heq, -⟩ | ⟨_, _, _, heq, -⟩
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · obtain ⟨rfl, rfl⟩ := (qqAnd_inj p₁ p₂ p₁' p₂').mp heq
    exact hiff
  · simp at heq
  · simp at heq
  · simp at heq

/-- Immediate subformulas of a coded disjunction in the domain also belong to the domain.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_or (h : PSatZero q z e) (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, heq, -⟩
    | ⟨p₁', p₂', heq, hd1, hd2, -⟩ | ⟨_, _, _, heq, -⟩ | ⟨_, _, _, heq, -⟩
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · obtain ⟨rfl, rfl⟩ := (qqOr_inj p₁ p₂ p₁' p₂').mp heq
    exact ⟨hd1, hd2⟩
  · simp at heq
  · simp at heq

/-- The Tarski clause for disjunction, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_or (h : PSatZero q z e) (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪⟪p₁ ^⋎ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 1⟫ ∈ q := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, heq, -⟩
    | ⟨p₁', p₂', heq, hd1, hd2, hiff, -⟩ | ⟨_, _, _, heq, -⟩ | ⟨_, _, _, heq, -⟩
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · obtain ⟨rfl, rfl⟩ := (qqOr_inj p₁ p₂ p₁' p₂').mp heq
    exact hiff
  · simp at heq
  · simp at heq

/-- Immediate subformulas of a coded bounded universal in the domain also belong to the domain,
under the extended assignment.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_ball (h : PSatZero q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) {x : V} (hx : x < termVal e' t) :
    ⟪p, x ∷ e'⟫ ∈ domain q := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, heq, -⟩ | ⟨_, _, heq, -⟩
    | ⟨u', p', -, heq, hd, -⟩ | ⟨_, _, _, heq, -⟩
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · obtain ⟨hu, rfl⟩ := qqBall_inj.mp heq
    rw [← hu, termVal_termBShift ht] at hd
    exact hd x hx
  · simp at heq

/-- The Tarski clause for the bounded universal, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_ball (h : PSatZero q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) :
    ⟪⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫, 1⟫ ∈ q ↔ ∀ x < termVal e' t, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, heq, -⟩ | ⟨_, _, heq, -⟩
    | ⟨u', p', -, heq, hd, hiff, -⟩ | ⟨_, _, _, heq, -⟩
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · obtain ⟨hu, rfl⟩ := qqBall_inj.mp heq
    rw [← hu, termVal_termBShift ht] at hiff
    exact hiff
  · simp at heq

/-- Immediate subformulas of a coded bounded existential in the domain also belong to the
domain, under the extended assignment.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_bex (h : PSatZero q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) {x : V} (hx : x < termVal e' t) :
    ⟪p, x ∷ e'⟫ ∈ domain q := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, heq, -⟩ | ⟨_, _, heq, -⟩
    | ⟨_, _, _, heq, -⟩ | ⟨u', p', -, heq, hd, -⟩
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · obtain ⟨hu, rfl⟩ := qqBex_inj.mp heq
    rw [← hu, termVal_termBShift ht] at hd
    exact hd x hx

/-- The Tarski clause for the bounded existential, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_bex (h : PSatZero q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) :
    ⟪⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫, 1⟫ ∈ q ↔ ∃ x < termVal e' t, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q := by
  rcases h.spec _ e' hn with ⟨heq, -⟩ | ⟨heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩
    | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, _, _, heq, -⟩ | ⟨_, _, heq, -⟩ | ⟨_, _, heq, -⟩
    | ⟨_, _, _, heq, -⟩ | ⟨u', p', -, heq, hd, hiff, -⟩
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · simp at heq
  · obtain ⟨hu, rfl⟩ := qqBex_inj.mp heq
    rw [← hu, termVal_termBShift ht] at hiff
    exact hiff

/-- A table for a root restricts to a table for any node in its domain: some sub-mapping of `q`
is itself a partial satisfaction table rooted at that node.
- [HP98, Definition I.1.71(1)] -/
axiom restriction (h : PSatZero q z e) {z' e' : V} (hn : ⟪z', e'⟫ ∈ domain q) :
    ∃ q', PSatZero q' z' e' ∧ q' ⊆ q

end PSatZero

end LO.FirstOrder.Arithmetic.Bootstrapping
