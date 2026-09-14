module

public import AlphaCentauri.Bootstrapping.Bounded
public import AlphaCentauri.Bootstrapping.TermVal
public import Foundation.FirstOrder.Arithmetic.HFS.Superexp
import Mathlib.Tactic.Ring

/-!
# Satisfaction for $\Delta_0$ formulas

This module defines the satisfaction predicate for internally coded $\Delta_0$ formulas and proves
Tarski's satisfaction conditions for it. It is built in three steps.

`BoundedSatisfactionTable q z e` is the satisfaction table for the code `z` under the assignment
`e`: a finite mapping which obeys a Tarski clause at every node of its domain. It is $\Delta_1$,
and a table for a fixed root is unique. `BoundedSatisfactionTable.agree` is the form uniqueness
takes for tables with different roots: two tables give the same value at every node common to
their domains. This is what reads a Tarski condition off the table of a subformula, so no
separate restriction operation is needed.

Every well-formed internally $\Delta_0$ code has such a table under every assignment. The
statement `∀ e, ∃ q, BoundedSatisfactionTable q z e` is $\Pi_2$, so `𝗜𝚺₁` cannot induct on it
directly; following [HP98, Lemma I.1.72(3)], the induction is carried out on a bounded form of
the statement instead. Where the source bounds the table uniformly by a polynomial in the code
and in an assignment bound, this development bounds it by

  `tableBound z e = iterExp (4 * z + 3 * e + 31) (8 * z + 24)`,

an exponential tower whose height decreases along the induction. The tower replaces the source's
polynomial because the domain here is the downward closure of the root rather than a uniform
rectangle `(< p) × (< r)`: entering a bounded quantifier pushes a value `x < termVal e t` onto
the assignment, and `termVal_le_poly` bounds that value only exponentially. Since the number of
nested quantifiers is bounded by the code `z`, the height `8 * z + 24` suffices; `iterExp` is
$\Sigma_1$ and total in `𝗜𝚺₁`, so the bound is available.

`BoundedSatisfaction z e` then says that some table rooted at `⟪z, e⟫` gives it the value `1`;
uniqueness turns this $\Sigma_1$ statement into a $\Delta_1$ one.

- [HP98, Theorem I.1.70]
- [HP98, Definition I.1.71]
- [HP98, Lemma I.1.72]
- [HP98, Lemma I.1.73]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section table

open Arithmetic (qqEQ qqNEQ qqLT qqNLT qqEQ_defined qqNEQ_defined qqLT_defined qqNLT_defined)

/-! ## Bounds on the nodes of a finite mapping -/

lemma lt_of_mem_domain {n q : V} (h : n ∈ domain q) : n < q := by
  obtain ⟨y, hy⟩ := mem_domain_iff.mp h
  exact lt_of_mem_dom hy

lemma fst_lt_of_mem_domain {p e q : V} (h : ⟪p, e⟫ ∈ domain q) : p < q :=
  lt_of_le_of_lt (le_pair_left p e) (lt_of_mem_domain h)

lemma snd_lt_of_mem_domain {p e q : V} (h : ⟪p, e⟫ ∈ domain q) : e < q :=
  lt_of_le_of_lt (le_pair_right p e) (lt_of_mem_domain h)

section coding

-- Unfolding these coding operations to their underlying pairs, together with the default simp
-- set (numeral facts, `pair_ext_iff`), is exactly what is needed to tell two differently-shaped
-- coded formulas apart when reading `spec` off at a node. Scoped to this section, since
-- unconditionally unfolding these constructors defeats the ordinary simp set on coded formulas.
attribute [local simp] qqAnd qqOr qqVerum qqFalsum qqRel qqNRel qqBall qqAll qqBex qqExs
  qqEQ qqNEQ qqLT qqNLT

/-! ## Coding injectivity facts for the bounded quantifiers -/

@[simp] lemma qqBall_inj {u₁ q₁ u₂ q₂ : V} : qqBall u₁ q₁ = qqBall u₂ q₂ ↔ u₁ = u₂ ∧ q₁ = q₂ := by
  simp [qqBall, qqNLT, qqNRel, adjoin_inj]

@[simp] lemma qqBex_inj {u₁ q₁ u₂ q₂ : V} : qqBex u₁ q₁ = qqBex u₂ q₂ ↔ u₁ = u₂ ∧ q₁ = q₂ := by
  simp [qqBex, qqLT, qqRel, adjoin_inj]

@[simp] lemma qqEQ_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^= u₁ = t₂ ^= u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [qqEQ, qqRel, adjoin_inj]

@[simp] lemma qqNEQ_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^≠ u₁ = t₂ ^≠ u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [qqNEQ, qqNRel, adjoin_inj]

@[simp] lemma qqLT_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^< u₁ = t₂ ^< u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [qqLT, qqRel, adjoin_inj]

@[simp] lemma qqNLT_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^≮ u₁ = t₂ ^≮ u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [qqNLT, qqNRel, adjoin_inj]

@[simp] lemma coe_eqIndex_eq : (Arithmetic.eqIndex : V) = 0 := rfl

@[simp] lemma coe_ltIndex_eq : (Arithmetic.ltIndex : V) = 1 := by simp [Arithmetic.ltIndex]; rfl

lemma eqIndex_ne_ltIndex : (Arithmetic.eqIndex : V) ≠ (Arithmetic.ltIndex : V) := by simp

/-! ## The partial satisfaction table -/

/-- `BoundedSatisfactionTable q z e` says that `q` is a finite Tarski satisfaction table rooted at
`⟪z, e⟫`.

- [HP98, Definition I.1.71(1)] -/
structure BoundedSatisfactionTable (q z e : V) : Prop where
  /-- `q` is a finite mapping. -/
  isMapping : IsMapping q
  /-- The root belongs to the domain. -/
  mem_dom_root : ⟪z, e⟫ ∈ domain q
  /-- Each domain node obeys its Tarski clause and has its immediate children in the domain. -/
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
  /-- Every nonroot domain node has an immediate parent in the domain. -/
  minimal : ∀ n ∈ domain q, n = ⟪z, e⟫ ∨
    (∃ p₁ p₂ e', ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
    (∃ p₁ p₂ e', ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
    (∃ u p e', ⟪qqBall u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫) ∨
    (∃ u p e', ⟪qqBex u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫)


namespace BoundedSatisfactionTable

variable {q z e z' e' t u p p₁ p₂ : V}

/-! ## Reading `spec` off at a node of known shape

`spec` is a ten-way disjunction over the outermost coding constructor of the node. Each lemma
below specializes it to a node of known shape: membership of the immediate children in the
domain, and how the values `1` and `0` at the node are determined. -/

/-- The Tarski clause for the truth constant, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_verum (h : BoundedSatisfactionTable q z e) (hn : ⟪(^⊤ : V), e'⟫ ∈ domain q) :
    ⟪⟪(^⊤ : V), e'⟫, 1⟫ ∈ q := by
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩
  on_goal 1 => exact hv
  all_goals simp at he

/-- The Tarski clause for the falsehood constant, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_falsum (h : BoundedSatisfactionTable q z e) (hn : ⟪(^⊥ : V), e'⟫ ∈ domain q) :
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
lemma spec_eq (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^= u, e'⟫ ∈ domain q) :
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
lemma spec_neq (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^≠ u, e'⟫ ∈ domain q) :
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
lemma spec_lt (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^< u, e'⟫ ∈ domain q) :
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
lemma spec_nlt (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^≮ u, e'⟫ ∈ domain q) :
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

/-- The Tarski and child-domain clauses for a coded conjunction.
- [HP98, Definition I.1.71(1)] -/
lemma spec_and (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
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

/-- The Tarski and child-domain clauses for a coded disjunction.
- [HP98, Definition I.1.71(1)] -/
lemma spec_or (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
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

/-- The Tarski and child-domain clauses for a coded bounded universal.
- [HP98, Definition I.1.71(1)] -/
lemma spec_ball (h : BoundedSatisfactionTable q z e) (hn : ⟪qqBall u p, e'⟫ ∈ domain q) :
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

/-- The Tarski and child-domain clauses for a coded bounded existential.
- [HP98, Definition I.1.71(1)] -/
lemma spec_bex (h : BoundedSatisfactionTable q z e) (hn : ⟪qqBex u p, e'⟫ ∈ domain q) :
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
lemma val_eq (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^= u, e'⟫ ∈ domain q) :
    ⟪⟪t ^= u, e'⟫, 1⟫ ∈ q ↔ termVal e' t = termVal e' u := (h.spec_eq hn).1

/-- Satisfaction of a coded inequality atom, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_neq (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^≠ u, e'⟫ ∈ domain q) :
    ⟪⟪t ^≠ u, e'⟫, 1⟫ ∈ q ↔ termVal e' t ≠ termVal e' u := (h.spec_neq hn).1

/-- Satisfaction of a coded less-than atom, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_lt (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^< u, e'⟫ ∈ domain q) :
    ⟪⟪t ^< u, e'⟫, 1⟫ ∈ q ↔ termVal e' t < termVal e' u := (h.spec_lt hn).1

/-- Satisfaction of a coded not-less-than atom, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_nlt (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^≮ u, e'⟫ ∈ domain q) :
    ⟪⟪t ^≮ u, e'⟫, 1⟫ ∈ q ↔ ¬termVal e' t < termVal e' u := (h.spec_nlt hn).1

/-- Immediate subformulas of a coded conjunction in the domain also belong to the domain.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_and (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q :=
  ⟨(h.spec_and hn).1, (h.spec_and hn).2.1⟩

/-- The Tarski clause for conjunction, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_and (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪⟪p₁ ^⋏ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 1⟫ ∈ q := (h.spec_and hn).2.2.1

/-- Immediate subformulas of a coded disjunction in the domain also belong to the domain.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_or (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q :=
  ⟨(h.spec_or hn).1, (h.spec_or hn).2.1⟩

/-- The Tarski clause for disjunction, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_or (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪⟪p₁ ^⋎ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 1⟫ ∈ q := (h.spec_or hn).2.2.1

/-- Immediate subformulas of a coded bounded universal in the domain also belong to the domain,
under the extended assignment.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_ball (h : BoundedSatisfactionTable q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) {x : V} (hx : x < termVal e' t) :
    ⟪p, x ∷ e'⟫ ∈ domain q :=
  (h.spec_ball hn).2.1 x (by rwa [termVal_termBShift ht])

/-- The Tarski clause for the bounded universal, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_ball (h : BoundedSatisfactionTable q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) :
    ⟪⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫, 1⟫ ∈ q ↔ ∀ x < termVal e' t, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q := by
  have := (h.spec_ball hn).2.2.1
  rwa [termVal_termBShift ht] at this

/-- Immediate subformulas of a coded bounded existential in the domain also belong to the
domain, under the extended assignment.
- [HP98, Definition I.1.71(1)] -/
lemma mem_dom_bex (h : BoundedSatisfactionTable q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) {x : V} (hx : x < termVal e' t) :
    ⟪p, x ∷ e'⟫ ∈ domain q :=
  (h.spec_bex hn).2.1 x (by rwa [termVal_termBShift ht])

/-- The Tarski clause for the bounded existential, at a node of the domain.
- [HP98, Definition I.1.71(1)] -/
lemma val_bex (h : BoundedSatisfactionTable q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) :
    ⟪⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫, 1⟫ ∈ q ↔ ∃ x < termVal e' t, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q := by
  have := (h.spec_bex hn).2.2.1
  rwa [termVal_termBShift ht] at this

end BoundedSatisfactionTable

end coding

namespace BoundedSatisfactionTable

variable {q q₁ q₂ z z₁ z₂ e e₁ e₂ p : V}

/-! ## Uniqueness -/

/-- A table takes at most one value at each node, so `0` and `1` cannot both occur.
- [HP98, Definition I.1.71(1)] -/
lemma val_one_ne_zero (h : BoundedSatisfactionTable q z e) {n : V} (h1 : ⟪n, 1⟫ ∈ q) (h0 : ⟪n,
  0⟫ ∈ q) : False := by
  simpa using h.isMapping.uniq h1 h0

/-- Every node of the domain carries the value `1` or the value `0`.
- [HP98, Definition I.1.71(1)] -/
lemma val_zero_or_one (h : BoundedSatisfactionTable q z e) :
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

/-- Two tables agree at every node common to their domains.
- [HP98, Lemma I.1.72(2)] -/
lemma agree (h₁ : BoundedSatisfactionTable q₁ z₁ e₁) (h₂ : BoundedSatisfactionTable q₂ z₂ e₂) :
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

/-- Every node of a table is a node of any other table with the same root: the domain of a table
is determined by its root.
- [HP98, Lemma I.1.72(2)] -/
lemma dom_subset (h₁ : BoundedSatisfactionTable q₁ z e) (h₂ : BoundedSatisfactionTable q₂ z e) :
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
theorem uniq (h₁ : BoundedSatisfactionTable q₁ z e) (h₂ : BoundedSatisfactionTable q₂ z e) :
    q₁ = q₂ := by
  have sub : ∀ {r₁ r₂ : V}, BoundedSatisfactionTable r₁ z e → BoundedSatisfactionTable r₂ z e →
    ∀ x, x ∈ r₁ → x ∈ r₂ := by
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

end BoundedSatisfactionTable

/-! ## $\Delta_1$-definability

The predicate is spelled out clause by clause: each clause of `BoundedSatisfactionTable.spec` and of
`BoundedSatisfactionTable.minimal` gets a `Prop` with every quantifier bounded and a defining
formula, and
`boundedSatisfactionTable` is their assembly. Where a clause mentions `termVal`, whose graph is
$\Sigma_1$ but not
$\Sigma_0$, the value is hoisted out of the clause by an existential on the $\Sigma_1$ side and by a
universal on the $\Pi_1$ side, which leaves the clause itself $\Sigma_0$. -/

namespace BoundedSatisfactionTableF

/-! ### Nodes and values as $\Sigma_0$ relations -/

/-- Defining formula for `n ∈ domain q`.
- [HP98, Lemma I.1.72(1)] -/
def inDomDef : 𝚺₀.Semisentence 2 := .mkSigma “q n. ∃ v < q, :⟪n, v⟫:∈ q”

/-- `inDomDef` defines membership in the domain of a finite mapping.
- [HP98, Lemma I.1.72(1)] -/
instance inDom_defined : 𝚺₀-Relation (fun q n : V ↦ n ∈ domain q) via inDomDef := .mk fun v ↦ by
  suffices (∃ y < v 0, ⟪v 1, y⟫ ∈ v 0) ↔ v 1 ∈ domain (v 0) by simpa [inDomDef]
  rw [mem_domain_iff]
  exact ⟨fun ⟨y, _, h⟩ ↦ ⟨y, h⟩, fun ⟨y, h⟩ ↦ ⟨y, lt_of_mem_rng h, h⟩⟩

/-- Defining formula for `⟪⟪p, e⟫, v⟫ ∈ q`: the table `q` gives the node `⟪p, e⟫` the value
`v`.
- [HP98, Lemma I.1.72(1)] -/
def nodeValDef : 𝚺₀.Semisentence 4 := .mkSigma
  “q p e v. ∃ n <⁺ (p + e + 1)², !pairDef n p e ∧ :⟪n, v⟫:∈ q”

/-- `nodeValDef` defines the value of a table at a node.
- [HP98, Lemma I.1.72(1)] -/
instance nodeVal_defined :
    𝚺₀-Relation₄ (fun q p e v : V ↦ ⟪⟪p, e⟫, v⟫ ∈ q) via nodeValDef := .mk fun v ↦ by
  simp [nodeValDef]

/-- Defining formula for `⟪p, e⟫ ∈ domain q`.
- [HP98, Lemma I.1.72(1)] -/
def nodeDomDef : 𝚺₀.Semisentence 3 := .mkSigma “q p e. ∃ v < q, !nodeValDef q p e v”

/-- `nodeDomDef` defines membership of a node in a table.
- [HP98, Lemma I.1.72(1)] -/
instance nodeDom_defined :
    𝚺₀-Relation₃ (fun q p e : V ↦ ⟪p, e⟫ ∈ domain q) via nodeDomDef := .mk fun v ↦ by
  suffices (∃ y < v 0, ⟪⟪v 1, v 2⟫, y⟫ ∈ v 0) ↔ ⟪v 1, v 2⟫ ∈ domain (v 0) by
    simpa [nodeDomDef, nodeVal_defined.df]
  rw [mem_domain_iff]
  exact ⟨fun ⟨y, _, h⟩ ↦ ⟨y, h⟩, fun ⟨y, h⟩ ↦ ⟨y, lt_of_mem_rng h, h⟩⟩

/-- Defining formula for `⟪⟪p, x ∷ e⟫, v⟫ ∈ q`.
- [HP98, Lemma I.1.72(1)] -/
def childValDef : 𝚺₀.Semisentence 5 := .mkSigma
  “q p x e v. ∃ xe <⁺ (x + e + 1)² + 1, !adjoinDef xe x e ∧ !nodeValDef q p xe v”

/-- `childValDef` defines the value of a table at a node under an extended assignment.
- [HP98, Lemma I.1.72(1)] -/
instance childVal_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦ ⟪⟪v 1, v 2 ∷ v 3⟫, v 4⟫ ∈ v 0) childValDef :=
  .mk fun v ↦ by simp [childValDef, nodeVal_defined.df, adjoin_def]

/-- Defining formula for `⟪p, x ∷ e⟫ ∈ domain q`.
- [HP98, Lemma I.1.72(1)] -/
def childDomDef : 𝚺₀.Semisentence 4 := .mkSigma
  “q p x e. ∃ xe <⁺ (x + e + 1)² + 1, !adjoinDef xe x e ∧ !nodeDomDef q p xe”

/-- `childDomDef` defines membership of a node under an extended assignment.
- [HP98, Lemma I.1.72(1)] -/
instance childDom_defined :
    𝚺₀-Relation₄ (fun q p x e : V ↦ ⟪p, x ∷ e⟫ ∈ domain q) via childDomDef := .mk fun v ↦ by
  simp [childDomDef, nodeDom_defined.df, adjoin_def]

/-- Defining formula for `n = ⟪p, x ∷ e⟫`.
- [HP98, Lemma I.1.72(1)] -/
def childPairDef : 𝚺₀.Semisentence 4 := .mkSigma
  “n p x e. ∃ xe <⁺ (x + e + 1)² + 1, !adjoinDef xe x e ∧ !pairDef n p xe”

/-- `childPairDef` defines the code of a node under an extended assignment.
- [HP98, Lemma I.1.72(1)] -/
instance childPair_defined :
    𝚺₀-Relation₄ (fun n p x e : V ↦ n = ⟪p, x ∷ e⟫) via childPairDef := .mk fun v ↦ by
  simp [childPairDef, adjoin_def]

/-! ### The ten Tarski clauses -/

/-- The clause of `BoundedSatisfactionTable.spec` at a node whose code is the truth constant.
- [HP98, Lemma I.1.72(1)] -/
def SpecVerum (q z e : V) : Prop := z = ^⊤ ∧ ⟪⟪z, e⟫, 1⟫ ∈ q

/-- Defining formula for `SpecVerum`.
- [HP98, Lemma I.1.72(1)] -/
def specVerumDef : 𝚺₀.Semisentence 3 := .mkSigma “q z e. !qqVerumDef z ∧ !nodeValDef q z e 1”

/-- `specVerumDef` defines `SpecVerum`.
- [HP98, Lemma I.1.72(1)] -/
instance specVerum_defined : 𝚺₀-Relation₃ (SpecVerum : V → V → V → Prop) via specVerumDef :=
  .mk fun v ↦ by simp [specVerumDef, SpecVerum, nodeVal_defined.df]

/-- The clause of `BoundedSatisfactionTable.spec` at a node whose code is the falsehood constant.
- [HP98, Lemma I.1.72(1)] -/
def SpecFalsum (q z e : V) : Prop := z = ^⊥ ∧ ⟪⟪z, e⟫, 0⟫ ∈ q

/-- Defining formula for `SpecFalsum`.
- [HP98, Lemma I.1.72(1)] -/
def specFalsumDef : 𝚺₀.Semisentence 3 := .mkSigma “q z e. !qqFalsumDef z ∧ !nodeValDef q z e 0”

/-- `specFalsumDef` defines `SpecFalsum`.
- [HP98, Lemma I.1.72(1)] -/
instance specFalsum_defined : 𝚺₀-Relation₃ (SpecFalsum : V → V → V → Prop) via specFalsumDef :=
  .mk fun v ↦ by simp [specFalsumDef, SpecFalsum, nodeVal_defined.df]

/-- The clause of `BoundedSatisfactionTable.spec` at a node whose code is an equality atom.
- [HP98, Lemma I.1.72(1)] -/
def SpecEq (q z e : V) : Prop :=
  ∃ t < z, ∃ u < z, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^= u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ termVal e t = termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ termVal e t ≠ termVal e u)

/-- Defining formula for the values of `SpecEq` once the two term values are known.
- [HP98, Lemma I.1.72(1)] -/
def eqMatrixDef : 𝚺₀.Semisentence 5 := .mkSigma
  “q z e a b. (!nodeValDef q z e 1 ↔ a = b) ∧ (!nodeValDef q z e 0 ↔ a ≠ b)”

/-- `eqMatrixDef` defines the values of `SpecEq` at given term values.
- [HP98, Lemma I.1.72(1)] -/
instance eqMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ v 3 = v 4) ∧ (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ v 3 ≠ v 4)) eqMatrixDef :=
  .mk fun v ↦ by simp [eqMatrixDef, nodeVal_defined.df]

/-- Defining formula for `SpecEq`.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def specEqDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ t < z, ∃ u < z,
    !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u ∧ !qqEQDef z t u ∧
    ∃ a, !termValGraph a e t ∧ ∃ b, !termValGraph b e u ∧ !eqMatrixDef q z e a b”)
  (.mkPi “q z e. ∃ t < z, ∃ u < z,
    !(isUTerm ℒₒᵣ).pi t ∧ !(isUTerm ℒₒᵣ).pi u ∧ (∀ z', !qqEQDef z' t u → z = z') ∧
    ∀ a, !termValGraph a e t → ∀ b, !termValGraph b e u → !eqMatrixDef q z e a b”)

/-- `specEqDef` defines `SpecEq`.
- [HP98, Lemma I.1.72(1)] -/
instance specEq_defined : 𝚫₁-Relation₃ (SpecEq : V → V → V → Prop) via specEqDef := .mk <| by
  constructor
  · intro v
    simp [specEqDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (qqEQ_defined (V := V)).df, eqMatrix_defined.df]
  · intro v
    simp [specEqDef, HierarchySymbol.Semiformula.val_sigma, SpecEq, (termVal.defined (V := V)).df,
      (qqEQ_defined (V := V)).df, eqMatrix_defined.df]

/-- The clause of `BoundedSatisfactionTable.spec` at a node whose code is an inequality atom.
- [HP98, Lemma I.1.72(1)] -/
def SpecNeq (q z e : V) : Prop :=
  ∃ t < z, ∃ u < z, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^≠ u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ termVal e t ≠ termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ termVal e t = termVal e u)

/-- Defining formula for the values of `SpecNeq` once the two term values are known.
- [HP98, Lemma I.1.72(1)] -/
def neqMatrixDef : 𝚺₀.Semisentence 5 := .mkSigma
  “q z e a b. (!nodeValDef q z e 1 ↔ a ≠ b) ∧ (!nodeValDef q z e 0 ↔ a = b)”

/-- `neqMatrixDef` defines the values of `SpecNeq` at given term values.
- [HP98, Lemma I.1.72(1)] -/
instance neqMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ v 3 ≠ v 4) ∧ (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ v 3 = v 4)) neqMatrixDef :=
  .mk fun v ↦ by simp [neqMatrixDef, nodeVal_defined.df]

/-- Defining formula for `SpecNeq`.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def specNeqDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ t < z, ∃ u < z,
    !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u ∧ !qqNEQDef z t u ∧
    ∃ a, !termValGraph a e t ∧ ∃ b, !termValGraph b e u ∧ !neqMatrixDef q z e a b”)
  (.mkPi “q z e. ∃ t < z, ∃ u < z,
    !(isUTerm ℒₒᵣ).pi t ∧ !(isUTerm ℒₒᵣ).pi u ∧ (∀ z', !qqNEQDef z' t u → z = z') ∧
    ∀ a, !termValGraph a e t → ∀ b, !termValGraph b e u → !neqMatrixDef q z e a b”)

/-- `specNeqDef` defines `SpecNeq`.
- [HP98, Lemma I.1.72(1)] -/
instance specNeq_defined : 𝚫₁-Relation₃ (SpecNeq : V → V → V → Prop) via specNeqDef := .mk <| by
  constructor
  · intro v
    simp [specNeqDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (qqNEQ_defined (V := V)).df, neqMatrix_defined.df]
  · intro v
    simp [specNeqDef, HierarchySymbol.Semiformula.val_sigma, SpecNeq, (termVal.defined (V := V)).df,
      (qqNEQ_defined (V := V)).df, neqMatrix_defined.df]

/-- The clause of `BoundedSatisfactionTable.spec` at a node whose code is a less-than atom.
- [HP98, Lemma I.1.72(1)] -/
def SpecLt (q z e : V) : Prop :=
  ∃ t < z, ∃ u < z, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^< u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ termVal e t < termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ¬termVal e t < termVal e u)

/-- Defining formula for the values of `SpecLt` once the two term values are known.
- [HP98, Lemma I.1.72(1)] -/
def ltMatrixDef : 𝚺₀.Semisentence 5 := .mkSigma
  “q z e a b. (!nodeValDef q z e 1 ↔ a < b) ∧ (!nodeValDef q z e 0 ↔ ¬a < b)”

/-- `ltMatrixDef` defines the values of `SpecLt` at given term values.
- [HP98, Lemma I.1.72(1)] -/
instance ltMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ v 3 < v 4) ∧ (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ ¬v 3 < v 4)) ltMatrixDef :=
  .mk fun v ↦ by simp [ltMatrixDef, nodeVal_defined.df]

/-- Defining formula for `SpecLt`.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def specLtDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ t < z, ∃ u < z,
    !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u ∧ !qqLTDef z t u ∧
    ∃ a, !termValGraph a e t ∧ ∃ b, !termValGraph b e u ∧ !ltMatrixDef q z e a b”)
  (.mkPi “q z e. ∃ t < z, ∃ u < z,
    !(isUTerm ℒₒᵣ).pi t ∧ !(isUTerm ℒₒᵣ).pi u ∧ (∀ z', !qqLTDef z' t u → z = z') ∧
    ∀ a, !termValGraph a e t → ∀ b, !termValGraph b e u → !ltMatrixDef q z e a b”)

/-- `specLtDef` defines `SpecLt`.
- [HP98, Lemma I.1.72(1)] -/
instance specLt_defined : 𝚫₁-Relation₃ (SpecLt : V → V → V → Prop) via specLtDef := .mk <| by
  constructor
  · intro v
    simp [specLtDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (qqLT_defined (V := V)).df, ltMatrix_defined.df]
  · intro v
    simp [specLtDef, HierarchySymbol.Semiformula.val_sigma, SpecLt, (termVal.defined (V := V)).df,
      (qqLT_defined (V := V)).df, ltMatrix_defined.df]

/-- The clause of `BoundedSatisfactionTable.spec` at a node whose code is a not-less-than atom.
- [HP98, Lemma I.1.72(1)] -/
def SpecNlt (q z e : V) : Prop :=
  ∃ t < z, ∃ u < z, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^≮ u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ¬termVal e t < termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ termVal e t < termVal e u)

/-- Defining formula for the values of `SpecNlt` once the two term values are known.
- [HP98, Lemma I.1.72(1)] -/
def nltMatrixDef : 𝚺₀.Semisentence 5 := .mkSigma
  “q z e a b. (!nodeValDef q z e 1 ↔ ¬a < b) ∧ (!nodeValDef q z e 0 ↔ a < b)”

/-- `nltMatrixDef` defines the values of `SpecNlt` at given term values.
- [HP98, Lemma I.1.72(1)] -/
instance nltMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ ¬v 3 < v 4) ∧ (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ v 3 < v 4)) nltMatrixDef :=
  .mk fun v ↦ by simp [nltMatrixDef, nodeVal_defined.df]

/-- Defining formula for `SpecNlt`.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def specNltDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ t < z, ∃ u < z,
    !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u ∧ !qqNLTDef z t u ∧
    ∃ a, !termValGraph a e t ∧ ∃ b, !termValGraph b e u ∧ !nltMatrixDef q z e a b”)
  (.mkPi “q z e. ∃ t < z, ∃ u < z,
    !(isUTerm ℒₒᵣ).pi t ∧ !(isUTerm ℒₒᵣ).pi u ∧ (∀ z', !qqNLTDef z' t u → z = z') ∧
    ∀ a, !termValGraph a e t → ∀ b, !termValGraph b e u → !nltMatrixDef q z e a b”)

/-- `specNltDef` defines `SpecNlt`.
- [HP98, Lemma I.1.72(1)] -/
instance specNlt_defined : 𝚫₁-Relation₃ (SpecNlt : V → V → V → Prop) via specNltDef := .mk <| by
  constructor
  · intro v
    simp [specNltDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (qqNLT_defined (V := V)).df, nltMatrix_defined.df]
  · intro v
    simp [specNltDef, HierarchySymbol.Semiformula.val_sigma, SpecNlt, (termVal.defined (V := V)).df,
      (qqNLT_defined (V := V)).df, nltMatrix_defined.df]

/-- The clause of `BoundedSatisfactionTable.spec` at a node whose code is a conjunction.
- [HP98, Lemma I.1.72(1)] -/
def SpecAnd (q z e : V) : Prop :=
  ∃ p₁ < z, ∃ p₂ < z, z = p₁ ^⋏ p₂ ∧ ⟪p₁, e⟫ ∈ domain q ∧ ⟪p₂, e⟫ ∈ domain q ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 0⟫ ∈ q ∨ ⟪⟪p₂, e⟫, 0⟫ ∈ q)

/-- Defining formula for `SpecAnd`.
- [HP98, Lemma I.1.72(1)] -/
def specAndDef : 𝚺₀.Semisentence 3 := .mkSigma
  “q z e. ∃ p₁ < z, ∃ p₂ < z, !qqAndDef z p₁ p₂ ∧ !nodeDomDef q p₁ e ∧ !nodeDomDef q p₂ e ∧
    (!nodeValDef q z e 1 ↔ !nodeValDef q p₁ e 1 ∧ !nodeValDef q p₂ e 1) ∧
    (!nodeValDef q z e 0 ↔ !nodeValDef q p₁ e 0 ∨ !nodeValDef q p₂ e 0)”

/-- `specAndDef` defines `SpecAnd`.
- [HP98, Lemma I.1.72(1)] -/
instance specAnd_defined : 𝚺₀-Relation₃ (SpecAnd : V → V → V → Prop) via specAndDef :=
  .mk fun v ↦ by simp [specAndDef, SpecAnd, nodeVal_defined.df, nodeDom_defined.df]

/-- The clause of `BoundedSatisfactionTable.spec` at a node whose code is a disjunction.
- [HP98, Lemma I.1.72(1)] -/
def SpecOr (q z e : V) : Prop :=
  ∃ p₁ < z, ∃ p₂ < z, z = p₁ ^⋎ p₂ ∧ ⟪p₁, e⟫ ∈ domain q ∧ ⟪p₂, e⟫ ∈ domain q ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 0⟫ ∈ q ∧ ⟪⟪p₂, e⟫, 0⟫ ∈ q)

/-- Defining formula for `SpecOr`.
- [HP98, Lemma I.1.72(1)] -/
def specOrDef : 𝚺₀.Semisentence 3 := .mkSigma
  “q z e. ∃ p₁ < z, ∃ p₂ < z, !qqOrDef z p₁ p₂ ∧ !nodeDomDef q p₁ e ∧ !nodeDomDef q p₂ e ∧
    (!nodeValDef q z e 1 ↔ !nodeValDef q p₁ e 1 ∨ !nodeValDef q p₂ e 1) ∧
    (!nodeValDef q z e 0 ↔ !nodeValDef q p₁ e 0 ∧ !nodeValDef q p₂ e 0)”

/-- `specOrDef` defines `SpecOr`.
- [HP98, Lemma I.1.72(1)] -/
instance specOr_defined : 𝚺₀-Relation₃ (SpecOr : V → V → V → Prop) via specOrDef :=
  .mk fun v ↦ by simp [specOrDef, SpecOr, nodeVal_defined.df, nodeDom_defined.df]

/-- The clause of `BoundedSatisfactionTable.spec` at a node whose code is a bounded universal.
- [HP98, Lemma I.1.72(1)] -/
def SpecBall (q z e : V) : Prop :=
  ∃ u < z, ∃ p < z, (∃ t ≤ u, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ z = qqBall u p ∧
    (∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain q) ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 0⟫ ∈ q)

/-- Defining formula for the values of `SpecBall` once the bound is known.
- [HP98, Lemma I.1.72(1)] -/
def ballMatrixDef : 𝚺₀.Semisentence 5 := .mkSigma
  “q z e p b. (∀ x < b, !childDomDef q p x e) ∧
    (!nodeValDef q z e 1 ↔ ∀ x < b, !childValDef q p x e 1) ∧
    (!nodeValDef q z e 0 ↔ ∃ x < b, !childValDef q p x e 0)”

/-- `ballMatrixDef` defines the values of `SpecBall` at a given bound.
- [HP98, Lemma I.1.72(1)] -/
instance ballMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦
      (∀ x < v 4, ⟪v 3, x ∷ v 2⟫ ∈ domain (v 0)) ∧
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ ∀ x < v 4, ⟪⟪v 3, x ∷ v 2⟫, 1⟫ ∈ v 0) ∧
      (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ ∃ x < v 4, ⟪⟪v 3, x ∷ v 2⟫, 0⟫ ∈ v 0)) ballMatrixDef :=
  .mk fun v ↦ by
    simp [ballMatrixDef, nodeVal_defined.df, childVal_defined.df, childDom_defined.df]

/-- Defining formula for `SpecBall`.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def specBallDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ u < z, ∃ p < z,
    (∃ t <⁺ u, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ !qqBallDef z u p ∧
    ∃ e0, !adjoinDef e0 0 e ∧ ∃ b, !termValGraph b e0 u ∧ !ballMatrixDef q z e p b”)
  (.mkPi “q z e. ∃ u < z, ∃ p < z,
    (∃ t <⁺ u, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧
    (∀ z', !qqBallDef z' u p → z = z') ∧
    ∀ e0, !adjoinDef e0 0 e → ∀ b, !termValGraph b e0 u → !ballMatrixDef q z e p b”)

/-- `specBallDef` defines `SpecBall`.
- [HP98, Lemma I.1.72(1)] -/
instance specBall_defined : 𝚫₁-Relation₃ (SpecBall : V → V → V → Prop) via specBallDef :=
  .mk <| by
  constructor
  · intro v
    simp [specBallDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBall_defined (V := V)).df,
      ballMatrix_defined.df, adjoin_def]
  · intro v
    simp [specBallDef, HierarchySymbol.Semiformula.val_sigma, SpecBall,
      (termVal.defined (V := V)).df, (termBShift.defined (L := ℒₒᵣ) (V := V)).df,
      (qqBall_defined (V := V)).df, ballMatrix_defined.df, adjoin_def]

/-- The clause of `BoundedSatisfactionTable.spec` at a node whose code is a bounded existential.
- [HP98, Lemma I.1.72(1)] -/
def SpecBex (q z e : V) : Prop :=
  ∃ u < z, ∃ p < z, (∃ t ≤ u, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ z = qqBex u p ∧
    (∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain q) ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 0⟫ ∈ q)

/-- Defining formula for the values of `SpecBex` once the bound is known.
- [HP98, Lemma I.1.72(1)] -/
def bexMatrixDef : 𝚺₀.Semisentence 5 := .mkSigma
  “q z e p b. (∀ x < b, !childDomDef q p x e) ∧
    (!nodeValDef q z e 1 ↔ ∃ x < b, !childValDef q p x e 1) ∧
    (!nodeValDef q z e 0 ↔ ∀ x < b, !childValDef q p x e 0)”

/-- `bexMatrixDef` defines the values of `SpecBex` at a given bound.
- [HP98, Lemma I.1.72(1)] -/
instance bexMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦
      (∀ x < v 4, ⟪v 3, x ∷ v 2⟫ ∈ domain (v 0)) ∧
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ ∃ x < v 4, ⟪⟪v 3, x ∷ v 2⟫, 1⟫ ∈ v 0) ∧
      (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ ∀ x < v 4, ⟪⟪v 3, x ∷ v 2⟫, 0⟫ ∈ v 0)) bexMatrixDef :=
  .mk fun v ↦ by
    simp [bexMatrixDef, nodeVal_defined.df, childVal_defined.df, childDom_defined.df]

/-- Defining formula for `SpecBex`.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def specBexDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ u < z, ∃ p < z,
    (∃ t <⁺ u, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ !qqBexDef z u p ∧
    ∃ e0, !adjoinDef e0 0 e ∧ ∃ b, !termValGraph b e0 u ∧ !bexMatrixDef q z e p b”)
  (.mkPi “q z e. ∃ u < z, ∃ p < z,
    (∃ t <⁺ u, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧
    (∀ z', !qqBexDef z' u p → z = z') ∧
    ∀ e0, !adjoinDef e0 0 e → ∀ b, !termValGraph b e0 u → !bexMatrixDef q z e p b”)

/-- `specBexDef` defines `SpecBex`.
- [HP98, Lemma I.1.72(1)] -/
instance specBex_defined : 𝚫₁-Relation₃ (SpecBex : V → V → V → Prop) via specBexDef :=
  .mk <| by
  constructor
  · intro v
    simp [specBexDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBex_defined (V := V)).df,
      bexMatrix_defined.df, adjoin_def]
  · intro v
    simp [specBexDef, HierarchySymbol.Semiformula.val_sigma, SpecBex,
      (termVal.defined (V := V)).df, (termBShift.defined (L := ℒₒᵣ) (V := V)).df,
      (qqBex_defined (V := V)).df, bexMatrix_defined.df, adjoin_def]


/-! ### The clause of `BoundedSatisfactionTable.spec`, assembled -/

/-- The clause `BoundedSatisfactionTable.spec` imposes at the node `⟪z, e⟫` of the domain of `q`.
- [HP98, Lemma I.1.72(1)] -/
def SpecAt (q z e : V) : Prop :=
  SpecVerum q z e ∨ SpecFalsum q z e ∨ SpecEq q z e ∨ SpecNeq q z e ∨ SpecLt q z e ∨
    SpecNlt q z e ∨ SpecAnd q z e ∨ SpecOr q z e ∨ SpecBall q z e ∨ SpecBex q z e

/-- Defining formula for `SpecAt`.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def specDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. !specVerumDef q z e ∨ !specFalsumDef q z e ∨ !specEqDef.sigma q z e ∨
    !specNeqDef.sigma q z e ∨ !specLtDef.sigma q z e ∨ !specNltDef.sigma q z e ∨
    !specAndDef q z e ∨ !specOrDef q z e ∨ !specBallDef.sigma q z e ∨ !specBexDef.sigma q z e”)
  (.mkPi “q z e. !specVerumDef q z e ∨ !specFalsumDef q z e ∨ !specEqDef.pi q z e ∨
    !specNeqDef.pi q z e ∨ !specLtDef.pi q z e ∨ !specNltDef.pi q z e ∨
    !specAndDef q z e ∨ !specOrDef q z e ∨ !specBallDef.pi q z e ∨ !specBexDef.pi q z e”)

/-- `specDef` defines `SpecAt`.
- [HP98, Lemma I.1.72(1)] -/
instance specAt_defined : 𝚫₁-Relation₃ (SpecAt : V → V → V → Prop) via specDef := .mk <| by
  constructor
  · intro v; simp [specDef, HierarchySymbol.Semiformula.val_sigma]
  · intro v; simp [specDef, HierarchySymbol.Semiformula.val_sigma, SpecAt]

/-! ### The clause of `BoundedSatisfactionTable.minimal` -/

/-- A node of the domain that is an immediate subformula of a coded conjunction in it.
- [HP98, Lemma I.1.72(1)] -/
def MinAnd (q n : V) : Prop :=
  ∃ c < q, ∃ p₁ < c, ∃ p₂ < c, ∃ e < q, c = p₁ ^⋏ p₂ ∧ ⟪c, e⟫ ∈ domain q ∧
    (n = ⟪p₁, e⟫ ∨ n = ⟪p₂, e⟫)

/-- Defining formula for `MinAnd`.
- [HP98, Lemma I.1.72(1)] -/
def minAndDef : 𝚺₀.Semisentence 2 := .mkSigma
  “q n. ∃ c < q, ∃ p₁ < c, ∃ p₂ < c, ∃ e < q, !qqAndDef c p₁ p₂ ∧ !nodeDomDef q c e ∧
    (!pairDef n p₁ e ∨ !pairDef n p₂ e)”

/-- `minAndDef` defines `MinAnd`.
- [HP98, Lemma I.1.72(1)] -/
instance minAnd_defined : 𝚺₀-Relation (MinAnd : V → V → Prop) via minAndDef := .mk fun v ↦ by
  simp [minAndDef, MinAnd, nodeDom_defined.df]

/-- A node of the domain that is an immediate subformula of a coded disjunction in it.
- [HP98, Lemma I.1.72(1)] -/
def MinOr (q n : V) : Prop :=
  ∃ c < q, ∃ p₁ < c, ∃ p₂ < c, ∃ e < q, c = p₁ ^⋎ p₂ ∧ ⟪c, e⟫ ∈ domain q ∧
    (n = ⟪p₁, e⟫ ∨ n = ⟪p₂, e⟫)

/-- Defining formula for `MinOr`.
- [HP98, Lemma I.1.72(1)] -/
def minOrDef : 𝚺₀.Semisentence 2 := .mkSigma
  “q n. ∃ c < q, ∃ p₁ < c, ∃ p₂ < c, ∃ e < q, !qqOrDef c p₁ p₂ ∧ !nodeDomDef q c e ∧
    (!pairDef n p₁ e ∨ !pairDef n p₂ e)”

/-- `minOrDef` defines `MinOr`.
- [HP98, Lemma I.1.72(1)] -/
instance minOr_defined : 𝚺₀-Relation (MinOr : V → V → Prop) via minOrDef := .mk fun v ↦ by
  simp [minOrDef, MinOr, nodeDom_defined.df]

/-- `∃ x < b, n = ⟪p, x ∷ e⟫`.
- [HP98, Lemma I.1.72(1)] -/
def minChildDef : 𝚺₀.Semisentence 4 := .mkSigma “n p e b. ∃ x < b, !childPairDef n p x e”

/-- `minChildDef` defines the codes of the nodes below a bounded quantifier.
- [HP98, Lemma I.1.72(1)] -/
instance minChild_defined :
    𝚺₀-Relation₄ (fun n p e b : V ↦ ∃ x < b, n = ⟪p, x ∷ e⟫) via minChildDef := .mk fun v ↦ by
  simp [minChildDef, childPair_defined.df]

/-- A node of the domain reached by entering a coded bounded universal in it.
- [HP98, Lemma I.1.72(1)] -/
def MinBall (q n : V) : Prop :=
  ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, c = qqBall u p ∧ ⟪c, e⟫ ∈ domain q ∧
    ∃ x < termVal (0 ∷ e) u, n = ⟪p, x ∷ e⟫

/-- Defining formula for `MinBall`.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def minBallDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “q n. ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, !qqBallDef c u p ∧ !nodeDomDef q c e ∧
    ∃ e0, !adjoinDef e0 0 e ∧ ∃ b, !termValGraph b e0 u ∧ !minChildDef n p e b”)
  (.mkPi “q n. ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, (∀ c', !qqBallDef c' u p → c = c') ∧
    !nodeDomDef q c e ∧
    ∀ e0, !adjoinDef e0 0 e → ∀ b, !termValGraph b e0 u → !minChildDef n p e b”)

/-- `minBallDef` defines `MinBall`.
- [HP98, Lemma I.1.72(1)] -/
instance minBall_defined : 𝚫₁-Relation (MinBall : V → V → Prop) via minBallDef := .mk <| by
  constructor
  · intro v
    simp [minBallDef, (termVal.defined (V := V)).df,
      (qqBall_defined (V := V)).df, nodeDom_defined.df, minChild_defined.df, adjoin_def]
  · intro v
    simp [minBallDef, MinBall,
      (termVal.defined (V := V)).df, (qqBall_defined (V := V)).df, nodeDom_defined.df,
      minChild_defined.df, adjoin_def]

/-- A node of the domain reached by entering a coded bounded existential in it.
- [HP98, Lemma I.1.72(1)] -/
def MinBex (q n : V) : Prop :=
  ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, c = qqBex u p ∧ ⟪c, e⟫ ∈ domain q ∧
    ∃ x < termVal (0 ∷ e) u, n = ⟪p, x ∷ e⟫

/-- Defining formula for `MinBex`.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def minBexDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “q n. ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, !qqBexDef c u p ∧ !nodeDomDef q c e ∧
    ∃ e0, !adjoinDef e0 0 e ∧ ∃ b, !termValGraph b e0 u ∧ !minChildDef n p e b”)
  (.mkPi “q n. ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, (∀ c', !qqBexDef c' u p → c = c') ∧
    !nodeDomDef q c e ∧
    ∀ e0, !adjoinDef e0 0 e → ∀ b, !termValGraph b e0 u → !minChildDef n p e b”)

/-- `minBexDef` defines `MinBex`.
- [HP98, Lemma I.1.72(1)] -/
instance minBex_defined : 𝚫₁-Relation (MinBex : V → V → Prop) via minBexDef := .mk <| by
  constructor
  · intro v
    simp [minBexDef, (termVal.defined (V := V)).df,
      (qqBex_defined (V := V)).df, nodeDom_defined.df, minChild_defined.df, adjoin_def]
  · intro v
    simp [minBexDef, MinBex,
      (termVal.defined (V := V)).df, (qqBex_defined (V := V)).df, nodeDom_defined.df,
      minChild_defined.df, adjoin_def]

/-- The clause `BoundedSatisfactionTable.minimal` imposes at the node `n` of the domain of `q`.
- [HP98, Lemma I.1.72(1)] -/
def MinimalAt (q z e n : V) : Prop :=
  n = ⟪z, e⟫ ∨ MinAnd q n ∨ MinOr q n ∨ MinBall q n ∨ MinBex q n

/-- Defining formula for `MinimalAt`.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def minimalDef : 𝚫₁.Semisentence 4 := .mkDelta
  (.mkSigma “q z e n. !pairDef n z e ∨ !minAndDef q n ∨ !minOrDef q n ∨ !minBallDef.sigma q n ∨
    !minBexDef.sigma q n”)
  (.mkPi “q z e n. !pairDef n z e ∨ !minAndDef q n ∨ !minOrDef q n ∨ !minBallDef.pi q n ∨
    !minBexDef.pi q n”)

/-- `minimalDef` defines `MinimalAt`.
- [HP98, Lemma I.1.72(1)] -/
instance minimalAt_defined :
    𝚫₁-Relation₄ (MinimalAt : V → V → V → V → Prop) via minimalDef := .mk <| by
  constructor
  · intro v; simp [minimalDef, HierarchySymbol.Semiformula.val_sigma]
  · intro v; simp [minimalDef, HierarchySymbol.Semiformula.val_sigma, MinimalAt]

/-! ### Assembling the definition -/

/-- The definition of `BoundedSatisfactionTable`, with every quantifier bounded by the table.
- [HP98, Lemma I.1.72(1)] -/
lemma boundedSatisfactionTable_iff {q z e : V} : BoundedSatisfactionTable q z e ↔
    IsMapping q ∧ ⟪z, e⟫ ∈ domain q ∧
    (∀ z' < q, ∀ e' < q, ⟪z', e'⟫ ∈ domain q → SpecAt q z' e') ∧
    (∀ n < q, n ∈ domain q → MinimalAt q z e n) := by
  constructor
  · rintro ⟨hm, hr, hs, hmin⟩
    refine ⟨hm, hr, ?_, ?_⟩
    · intro z' _ e' _ hd
      rcases hs z' e' hd with
        h | h | ⟨t, u, ht, hu, rfl, h⟩ | ⟨t, u, ht, hu, rfl, h⟩ | ⟨t, u, ht, hu, rfl, h⟩ |
        ⟨t, u, ht, hu, rfl, h⟩ | ⟨p₁, p₂, rfl, h⟩ | ⟨p₁, p₂, rfl, h⟩ |
        ⟨u, p, ⟨t, ht, rfl⟩, rfl, h⟩ | ⟨u, p, ⟨t, ht, rfl⟩, rfl, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨p₁, by simp, p₂, by simp, rfl, h⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨p₁, by simp, p₂, by simp, rfl, h⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨termBShift ℒₒᵣ t, by simp, p, by simp, ⟨t, le_termBShift ht, ht, rfl⟩, rfl, h⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨termBShift ℒₒᵣ t, by simp, p, by simp, ⟨t, le_termBShift ht, ht, rfl⟩, rfl, h⟩))))))))
    · intro n _ hn
      rcases hmin n hn with h | ⟨p₁, p₂, e', hd, hc⟩ | ⟨p₁, p₂, e', hd, hc⟩ |
        ⟨u, p, e', hd, hx⟩ | ⟨u, p, e', hd, hx⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨p₁ ^⋏ p₂, fst_lt_of_mem_domain hd, p₁, by simp, p₂, by simp,
          e', snd_lt_of_mem_domain hd, rfl, hd, hc⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨p₁ ^⋎ p₂, fst_lt_of_mem_domain hd, p₁, by simp, p₂, by simp,
          e', snd_lt_of_mem_domain hd, rfl, hd, hc⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨qqBall u p, fst_lt_of_mem_domain hd, u, by simp,
          p, by simp, e', snd_lt_of_mem_domain hd, rfl, hd, hx⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨qqBex u p, fst_lt_of_mem_domain hd, u, by simp,
          p, by simp, e', snd_lt_of_mem_domain hd, rfl, hd, hx⟩)))
  · rintro ⟨hm, hr, hs, hmin⟩
    refine ⟨hm, hr, ?_, ?_⟩
    · intro z' e' hd
      rcases hs z' (fst_lt_of_mem_domain hd) e' (snd_lt_of_mem_domain hd) hd with
        h | h | ⟨t, -, u, -, h⟩ | ⟨t, -, u, -, h⟩ | ⟨t, -, u, -, h⟩ | ⟨t, -, u, -, h⟩ |
        ⟨p₁, -, p₂, -, h⟩ | ⟨p₁, -, p₂, -, h⟩ | ⟨u, -, p, -, ⟨t, -, ht⟩, h⟩ |
        ⟨u, -, p, -, ⟨t, -, ht⟩, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨t, u, h⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, u, h⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, u, h⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, u, h⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, h⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, h⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨u, p, ⟨t, ht⟩, h⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨u, p, ⟨t, ht⟩, h⟩))))))))
    · intro n hn
      rcases hmin n (lt_of_mem_domain hn) hn with h | ⟨c, -, p₁, -, p₂, -, e', -, rfl, hd, hc⟩ |
        ⟨c, -, p₁, -, p₂, -, e', -, rfl, hd, hc⟩ | ⟨c, -, u, -, p, -, e', -, rfl, hd, hx⟩ |
        ⟨c, -, u, -, p, -, e', -, rfl, hd, hx⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨p₁, p₂, e', hd, hc⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨p₁, p₂, e', hd, hc⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u, p, e', hd, hx⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨u, p, e', hd, hx⟩)))

end BoundedSatisfactionTableF

section defining

open BoundedSatisfactionTableF

/-- The $\Delta_1$ formula defining satisfaction tables.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def boundedSatisfactionTable : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. !isMappingDef q ∧ !nodeDomDef q z e ∧
    (∀ z' < q, ∀ e' < q, !nodeDomDef q z' e' → !specDef.sigma q z' e') ∧
    (∀ n < q, !inDomDef q n → !minimalDef.sigma q z e n)”)
  (.mkPi “q z e. !isMappingDef q ∧ !nodeDomDef q z e ∧
    (∀ z' < q, ∀ e' < q, !nodeDomDef q z' e' → !specDef.pi q z' e') ∧
    (∀ n < q, !inDomDef q n → !minimalDef.pi q z e n)”)

/-- The formula `boundedSatisfactionTable` defines satisfaction tables.
- [HP98, Lemma I.1.72(1)] -/
instance BoundedSatisfactionTable.defined :
    𝚫₁-Relation₃ (BoundedSatisfactionTable : V → V → V → Prop) via boundedSatisfactionTable :=
  .mk <| by
    constructor
    · intro v
      simp [boundedSatisfactionTable, HierarchySymbol.Semiformula.val_sigma,
        nodeDom_defined.df, inDom_defined.df]
    · intro v
      simp [boundedSatisfactionTable, HierarchySymbol.Semiformula.val_sigma,
        boundedSatisfactionTable_iff, nodeDom_defined.df, inDom_defined.df]

/-- Satisfaction tables form a $\Delta_1$-definable relation.
- [HP98, Lemma I.1.72(1)] -/
instance BoundedSatisfactionTable.definable :
    𝚫₁-Relation₃ (BoundedSatisfactionTable : V → V → V → Prop) :=
  BoundedSatisfactionTable.defined.to_definable

end defining

end table

/-! ## Elementary exponential bounds -/

lemma mul_le_exp_add (a b : V) : a * b ≤ Exp.exp (a + b) :=
  calc a * b ≤ Exp.exp a * Exp.exp b :=
        mul_le_mul (le_of_lt (lt_exp a)) (le_of_lt (lt_exp b)) (by simp) (by simp)
    _ = Exp.exp (a + b) := (exp_add a b).symm

lemma exp_add_le (a c : V) : Exp.exp a + c ≤ Exp.exp (a + c + 1) := by
  have h1 : c + 2 ≤ Exp.exp (c + 1) := by
    have : c + 1 + 1 ≤ Exp.exp (c + 1) := succ_le_iff_lt.mpr (lt_exp (c + 1))
    simpa [add_assoc, one_add_one_eq_two] using this
  have h2 : (1 : V) ≤ Exp.exp a := by
    have := succ_le_iff_lt.mpr (exp_pos a)
    simp
  have hc : c ≤ Exp.exp a * c := le_mul_of_one_le_left (by simp) h2
  have he : Exp.exp a ≤ Exp.exp a * 2 := le_mul_of_one_le_right (by simp) (by simp)
  calc Exp.exp a + c
      ≤ Exp.exp a * 2 + Exp.exp a * c := add_le_add he hc
    _ = Exp.exp a * (c + 2) := by rw [mul_add]; simp [add_comm]
    _ ≤ Exp.exp a * Exp.exp (c + 1) := mul_le_mul le_rfl h1 (by simp) (by simp)
    _ = Exp.exp (a + c + 1) := by rw [← exp_add]; simp [add_assoc]

lemma pair_le_exp (a b : V) : ⟪a, b⟫ ≤ Exp.exp (2 * a + 2 * b + 2) :=
  calc ⟪a, b⟫ ≤ (a + b + 1) ^ 2 := pair_polybound a b
    _ = (a + b + 1) * (a + b + 1) := by ring
    _ ≤ Exp.exp ((a + b + 1) + (a + b + 1)) := mul_le_exp_add _ _
    _ = Exp.exp (2 * a + 2 * b + 2) := by ring_nf

lemma adjoin_le_exp (a v : V) : a ∷ v ≤ Exp.exp (2 * a + 2 * v + 3) := by
  have h1 : (1 : V) ≤ Exp.exp (2 * a + 2 * v + 2) := by simp
  calc a ∷ v = ⟪a, v⟫ + 1 := adjoin_def a v
    _ ≤ Exp.exp (2 * a + 2 * v + 2) + 1 := add_le_add (pair_le_exp a v) le_rfl
    _ ≤ 2 * Exp.exp (2 * a + 2 * v + 2) := by simp [two_mul]
    _ = Exp.exp (2 * a + 2 * v + 3) := by
        rw [show 2 * a + 2 * v + 3 = (2 * a + 2 * v + 2) + 1 from by ring, exp_succ]

lemma listMax_le_self (v : V) : listMax v ≤ v := by
  refine adjoin_induction 𝚷 (P := fun v ↦ listMax v ≤ v) (by definability) (by simp) ?_ v
  intro x v ih
  simp only [listMax_adjoin, max_le_iff]
  exact ⟨le_of_lt (lt_adjoin x v), le_trans ih (le_of_lt (lt_adjoin' x v))⟩

/-! ## The iterated exponential -/

lemma le_iterExp (x n : V) : x ≤ iterExp x n := by
  refine ISigma1.sigma1_succ_induction (P := fun n ↦ x ≤ iterExp x n) (by definability)
    (by simp) ?_ n
  intro n ih
  calc x ≤ iterExp x n := ih
    _ ≤ Exp.exp (iterExp x n) := le_of_lt (lt_exp _)
    _ = iterExp x (n + 1) := (iterExp_succ x n).symm

lemma iterExp_le_iterExp_left {x y : V} (h : x ≤ y) (n : V) : iterExp x n ≤ iterExp y n := by
  refine ISigma1.sigma1_succ_induction (P := fun n ↦ iterExp x n ≤ iterExp y n) (by definability)
    (by simpa using h) ?_ n
  intro n ih
  simpa using exp_monotone_le.mpr ih

lemma iterExp_add (x m n : V) : iterExp x (m + n) = iterExp (iterExp x m) n := by
  refine ISigma1.sigma1_succ_induction (P := fun n ↦ iterExp x (m + n) = iterExp (iterExp x m) n)
    (by definability) (by simp) ?_ n
  intro n ih
  rw [show m + (n + 1) = (m + n) + 1 from by ring, iterExp_succ, ih, iterExp_succ]

lemma iterExp_le_iterExp_right (x : V) {m n : V} (h : m ≤ n) : iterExp x m ≤ iterExp x n := by
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp h
  rw [iterExp_add]
  exact le_iterExp _ k

lemma iterExp_lt_iterExp_succ (x n : V) : iterExp x n < iterExp x (n + 1) := by
  simp

lemma iterExp_lt_of_lt (x : V) {m n : V} (h : m < n) : iterExp x m < iterExp x n :=
  lt_of_lt_of_le (iterExp_lt_iterExp_succ x m) (iterExp_le_iterExp_right x (lt_iff_succ_le.mp h))

lemma two_mul_le_exp {a : V} (h : 2 ≤ a) : 2 * a ≤ Exp.exp a := by
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp h
  have h4 : Exp.exp (2 + c : V) = 4 * Exp.exp c := by
    rw [show (2 : V) + c = c + 1 + 1 from by ring, exp_succ, exp_succ]; ring
  have hc : c + 1 ≤ Exp.exp c := succ_le_iff_lt.mpr (lt_exp c)
  calc 2 * (2 + c) = 4 + 2 * c := by ring
    _ ≤ (4 + 2 * c) + 2 * c := le_self_add
    _ = 4 * (c + 1) := by ring
    _ ≤ 4 * Exp.exp c := mul_le_mul le_rfl hc (by simp) (by simp)
    _ = Exp.exp (2 + c) := h4.symm

@[simp] lemma iterExp_one (x : V) : iterExp x 1 = Exp.exp x := by
  rw [show (1 : V) = 0 + 1 from by ring, iterExp_succ, iterExp_zero]

lemma iterExp_two (x : V) : iterExp x 2 = Exp.exp (Exp.exp x) := by
  rw [show (2 : V) = 1 + 1 from by ring, iterExp_succ, iterExp_one]

lemma iterExp_three (x : V) : iterExp x 3 = Exp.exp (Exp.exp (Exp.exp x)) := by
  rw [show (3 : V) = 2 + 1 from by ring, iterExp_succ, iterExp_two]

lemma iterExp_four (x : V) : iterExp x 4 = Exp.exp (Exp.exp (Exp.exp (Exp.exp x))) := by
  rw [show (4 : V) = 3 + 1 from by ring, iterExp_succ, iterExp_three]

/-! ## The bound on a partial satisfaction table -/

/-- The exponent from which the bound on a table for `z` under `e` is built.
- [HP98, Lemma I.1.72(3)] -/
def tableExp (z e : V) : V := 4 * z + 3 * e + 31

/-- `tableBound z e` bounds every partial satisfaction table for `z` under `e`.
- [HP98, Lemma I.1.72(3)] -/
noncomputable def tableBound (z e : V) : V := iterExp (tableExp z e) (8 * z + 24)

/-- The exponent is monotone in the formula code.
- [HP98, Lemma I.1.72(3)] -/
lemma tableExp_mono {p z e : V} (h : p ≤ z) : tableExp p e ≤ tableExp z e :=
  add_le_add (add_le_add (mul_le_mul le_rfl h (by simp) (by simp)) le_rfl) le_rfl

/-- Every node of the table for `z` under `e` is bounded by two exponential steps.
- [HP98, Lemma I.1.72(3)] -/
lemma node_le_iterExp {z e v : V} (hv : v ≤ 1) : ⟪⟪z, e⟫, v⟫ ≤ iterExp (tableExp z e) 2 := by
  have h1 : (2 : V) * ⟪z, e⟫ + 2 * v + 2 ≤ Exp.exp (2 * z + 2 * e + 3) + 4 := by
    calc (2 : V) * ⟪z, e⟫ + 2 * v + 2
        ≤ 2 * Exp.exp (2 * z + 2 * e + 2) + 2 * 1 + 2 :=
          add_le_add (add_le_add (mul_le_mul le_rfl (pair_le_exp z e) (by simp) (by simp))
            (mul_le_mul le_rfl hv (by simp) (by simp))) le_rfl
      _ = Exp.exp (2 * z + 2 * e + 2 + 1) + 4 := by rw [← exp_succ]; ring
      _ = Exp.exp (2 * z + 2 * e + 3) + 4 := by
          rw [show 2 * z + 2 * e + 2 + 1 = 2 * z + 2 * e + 3 from by ring]
  have h2 : Exp.exp (2 * z + 2 * e + 3) + 4 ≤ Exp.exp (2 * z + 2 * e + 8) := by
    calc Exp.exp (2 * z + 2 * e + 3) + 4 ≤ Exp.exp (2 * z + 2 * e + 3 + 4 + 1) := exp_add_le _ _
      _ = Exp.exp (2 * z + 2 * e + 8) := by
          rw [show 2 * z + 2 * e + 3 + 4 + 1 = 2 * z + 2 * e + 8 from by ring]
  have h3 : 2 * z + 2 * e + 8 ≤ tableExp z e := by
    calc 2 * z + 2 * e + 8 ≤ (2 * z + 2 * e + 8) + (2 * z + e + 23) := le_self_add
      _ = tableExp z e := by simp only [tableExp]; ring
  calc ⟪⟪z, e⟫, v⟫ ≤ Exp.exp (2 * ⟪z, e⟫ + 2 * v + 2) := pair_le_exp _ _
    _ ≤ Exp.exp (Exp.exp (2 * z + 2 * e + 8)) := exp_monotone_le.mpr (le_trans h1 h2)
    _ ≤ Exp.exp (Exp.exp (tableExp z e)) := exp_monotone_le.mpr (exp_monotone_le.mpr h3)
    _ = iterExp (tableExp z e) 2 := (iterExp_two _).symm

/-- Entering a bounded quantifier costs four exponential steps in the exponent.
- [HP98, Lemma I.1.72(3)] -/
lemma tableExp_step {z p u x e : V} (hp : p < z) (hu : u < z) (hx : x < termVal (0 ∷ e) u) :
    tableExp p (x ∷ e) ≤ iterExp (tableExp z e) 4 := by
  have hxE : x ≤ Exp.exp ((e + 2) * (z + 1)) := by
    have h2 : listMax (0 ∷ e) ≤ e := by simpa using listMax_le_self e
    have h3 : (listMax (0 ∷ e) + 2) * (u + 1) ≤ (e + 2) * (z + 1) :=
      mul_le_mul (add_le_add h2 le_rfl) (add_le_add (le_of_lt hu) le_rfl) (by simp) (by simp)
    exact le_of_lt (lt_of_lt_of_le hx
      (le_trans (termVal_le_poly _ _) (exp_monotone_le.mpr h3)))
  have hb : 3 * (x ∷ e) ≤ Exp.exp (2 * x + 2 * e + 5) := by
    calc 3 * (x ∷ e) ≤ 3 * Exp.exp (2 * x + 2 * e + 3) :=
          mul_le_mul le_rfl (adjoin_le_exp x e) (by simp) (by simp)
      _ ≤ 3 * Exp.exp (2 * x + 2 * e + 3) + Exp.exp (2 * x + 2 * e + 3) := le_self_add
      _ = 4 * Exp.exp (2 * x + 2 * e + 3) := by ring
      _ = Exp.exp (2 * x + 2 * e + 5) := by
          rw [show 2 * x + 2 * e + 5 = (2 * x + 2 * e + 3) + 1 + 1 from by ring, exp_succ, exp_succ]
          ring
  have step1 : tableExp p (x ∷ e) ≤ Exp.exp (2 * x + 2 * e + 4 * z + 37) := by
    have hpz : 4 * p ≤ 4 * z := mul_le_mul le_rfl (le_of_lt hp) (by simp) (by simp)
    calc tableExp p (x ∷ e) = 4 * p + 3 * (x ∷ e) + 31 := rfl
      _ ≤ 4 * z + Exp.exp (2 * x + 2 * e + 5) + 31 := add_le_add (add_le_add hpz hb) le_rfl
      _ = Exp.exp (2 * x + 2 * e + 5) + (4 * z + 31) := by ring
      _ ≤ Exp.exp (2 * x + 2 * e + 5 + (4 * z + 31) + 1) := exp_add_le _ _
      _ = Exp.exp (2 * x + 2 * e + 4 * z + 37) := by
          rw [show 2 * x + 2 * e + 5 + (4 * z + 31) + 1 = 2 * x + 2 * e + 4 * z + 37 from by ring]
  have step2 : 2 * x + 2 * e + 4 * z + 37 ≤ Exp.exp ((e + 2) * (z + 1) + 2 * e + 4 * z + 39) := by
    have h2x : 2 * x ≤ Exp.exp ((e + 2) * (z + 1) + 1) := by
      calc 2 * x ≤ 2 * Exp.exp ((e + 2) * (z + 1)) := mul_le_mul le_rfl hxE (by simp) (by simp)
        _ = Exp.exp ((e + 2) * (z + 1) + 1) := (exp_succ _).symm
    calc 2 * x + 2 * e + 4 * z + 37
        ≤ Exp.exp ((e + 2) * (z + 1) + 1) + 2 * e + 4 * z + 37 :=
          add_le_add (add_le_add (add_le_add h2x le_rfl) le_rfl) le_rfl
      _ = Exp.exp ((e + 2) * (z + 1) + 1) + (2 * e + 4 * z + 37) := by ring
      _ ≤ Exp.exp ((e + 2) * (z + 1) + 1 + (2 * e + 4 * z + 37) + 1) := exp_add_le _ _
      _ = Exp.exp ((e + 2) * (z + 1) + 2 * e + 4 * z + 39) := by
          rw [show (e + 2) * (z + 1) + 1 + (2 * e + 4 * z + 37) + 1
            = (e + 2) * (z + 1) + 2 * e + 4 * z + 39 from by ring]
  have step3 : (e + 2) * (z + 1) + 2 * e + 4 * z + 39 ≤ Exp.exp (5 * z + 3 * e + 43) := by
    have hEE : (e + 2) * (z + 1) ≤ Exp.exp (z + e + 3) := by
      calc (e + 2) * (z + 1) ≤ Exp.exp ((e + 2) + (z + 1)) := mul_le_exp_add _ _
        _ = Exp.exp (z + e + 3) := by rw [show (e + 2) + (z + 1) = z + e + 3 from by ring]
    calc (e + 2) * (z + 1) + 2 * e + 4 * z + 39
        ≤ Exp.exp (z + e + 3) + 2 * e + 4 * z + 39 :=
          add_le_add (add_le_add (add_le_add hEE le_rfl) le_rfl) le_rfl
      _ = Exp.exp (z + e + 3) + (2 * e + 4 * z + 39) := by ring
      _ ≤ Exp.exp (z + e + 3 + (2 * e + 4 * z + 39) + 1) := exp_add_le _ _
      _ = Exp.exp (5 * z + 3 * e + 43) := by
          rw [show z + e + 3 + (2 * e + 4 * z + 39) + 1 = 5 * z + 3 * e + 43 from by ring]
  have step4 : 5 * z + 3 * e + 43 ≤ Exp.exp (tableExp z e) := by
    have h2 : (2 : V) ≤ tableExp z e := by
      calc (2 : V) ≤ 2 + (4 * z + 3 * e + 29) := le_self_add
        _ = tableExp z e := by simp only [tableExp]; ring
    calc 5 * z + 3 * e + 43 ≤ (5 * z + 3 * e + 43) + (3 * z + 3 * e + 19) := le_self_add
      _ = 2 * tableExp z e := by simp only [tableExp]; ring
      _ ≤ Exp.exp (tableExp z e) := two_mul_le_exp h2
  calc tableExp p (x ∷ e) ≤ Exp.exp (2 * x + 2 * e + 4 * z + 37) := step1
    _ ≤ Exp.exp (Exp.exp ((e + 2) * (z + 1) + 2 * e + 4 * z + 39)) := exp_monotone_le.mpr step2
    _ ≤ Exp.exp (Exp.exp (Exp.exp (5 * z + 3 * e + 43))) :=
        exp_monotone_le.mpr (exp_monotone_le.mpr step3)
    _ ≤ Exp.exp (Exp.exp (Exp.exp (Exp.exp (tableExp z e)))) :=
        exp_monotone_le.mpr (exp_monotone_le.mpr (exp_monotone_le.mpr step4))
    _ = iterExp (tableExp z e) 4 := (iterExp_four _).symm

/-! ## Atomic codes over `ℒₒᵣ` -/

lemma uformula_rel_cases {k r w : V} (h : IsUFormula ℒₒᵣ (^rel k r w)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r w = t ^= u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r w = t ^< u) := by
  obtain ⟨hkr, hw⟩ := IsUFormula.rel.mp h
  rcases Arithmetic.isRel_iff_LOR.mp hkr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨t, u, ht, hu, rfl⟩ := IsUTermVec.two_iff.mp hw
    exact Or.inl ⟨t, u, ht, hu, rfl⟩
  · obtain ⟨t, u, ht, hu, rfl⟩ := IsUTermVec.two_iff.mp hw
    exact Or.inr ⟨t, u, ht, hu, rfl⟩

lemma uformula_nrel_cases {k r w : V} (h : IsUFormula ℒₒᵣ (^nrel k r w)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r w = t ^≠ u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r w = t ^≮ u) := by
  obtain ⟨hkr, hw⟩ := IsUFormula.nrel.mp h
  rcases Arithmetic.isRel_iff_LOR.mp hkr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨t, u, ht, hu, rfl⟩ := IsUTermVec.two_iff.mp hw
    exact Or.inl ⟨t, u, ht, hu, rfl⟩
  · obtain ⟨t, u, ht, hu, rfl⟩ := IsUTermVec.two_iff.mp hw
    exact Or.inr ⟨t, u, ht, hu, rfl⟩

/-! ## The clauses of a table as standalone predicates -/

namespace BoundedSatisfactionTable

variable {q q₁ q₂ Q z e z' e' n p p₁ p₂ u t v : V}

/-- The clause that `BoundedSatisfactionTable.spec` imposes at the node `⟪z', e'⟫` of the domain of
`q`.
- [HP98, Definition I.1.71(1)] -/
def Spec (q z' e' : V) : Prop :=
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

/-- The clause that `BoundedSatisfactionTable.minimal` imposes at a node of the domain other than
the root.
- [HP98, Definition I.1.71(1)] -/
def MinChild (q n : V) : Prop :=
  (∃ p₁ p₂ e', ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
  (∃ p₁ p₂ e', ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
  (∃ u p e', ⟪qqBall u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫) ∨
  (∃ u p e', ⟪qqBex u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫)

/-- Reading the `spec` field of a table as the standalone clause `Spec`.
- [HP98, Definition I.1.71(1)] -/
lemma spec' (h : BoundedSatisfactionTable q z e) (hn : ⟪z',
  e'⟫ ∈ domain q) : Spec q z' e' := h.spec z' e' hn

/-- Reading the `minimal` field of a table as the standalone clause `MinChild`.
- [HP98, Definition I.1.71(1)] -/
lemma minimal' (h : BoundedSatisfactionTable q z e) (hn : n ∈ domain q) : n = ⟪z, e⟫ ∨
  MinChild q n :=
  h.minimal n hn

/-- The domain clause is inherited by any larger domain.
- [HP98, Definition I.1.71(1)] -/
lemma MinChild.mono (hsub : ∀ m ∈ domain q, m ∈ domain Q) (h : MinChild q n) : MinChild Q n := by
  rcases h with ⟨a, b, e'', hd, hc⟩ | ⟨a, b, e'', hd, hc⟩ | ⟨a, b, e'', hd, hx⟩ |
    ⟨a, b, e'', hd, hx⟩
  · exact Or.inl ⟨a, b, e'', hsub _ hd, hc⟩
  · exact Or.inr (Or.inl ⟨a, b, e'', hsub _ hd, hc⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, b, e'', hsub _ hd, hx⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a, b, e'', hsub _ hd, hx⟩))

lemma val_iff_of_subset (hQ : IsMapping Q) (hsub : q ⊆ Q) (hn : n ∈ domain q) :
    ⟪n, v⟫ ∈ Q ↔ ⟪n, v⟫ ∈ q := by
  obtain ⟨w, hw⟩ := mem_domain_iff.mp hn
  exact ⟨fun h ↦ by rw [hQ.uniq h (hsub hw)]; exact hw, fun h ↦ hsub h⟩

/-- The Tarski clause at a node survives passing to a larger mapping.
- [HP98, Definition I.1.71(1)] -/
lemma Spec.mono (hQ : IsMapping Q) (hsub : q ⊆ Q) (hd : ⟪z', e'⟫ ∈ domain q) (h : Spec q z' e') :
    Spec Q z' e' := by
  have dom : ∀ m ∈ domain q, m ∈ domain Q := fun m hm ↦ domain_subset_domain_of_subset hsub hm
  have root : ∀ w : V, ⟪⟪z', e'⟫, w⟫ ∈ Q ↔ ⟪⟪z', e'⟫, w⟫ ∈ q :=
    fun w ↦ val_iff_of_subset hQ hsub hd
  rcases h with ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hc, hc', hA, hB⟩ | ⟨a, b, he, hc, hc', hA, hB⟩ |
    ⟨a, b, ht, he, hc, hA, hB⟩ | ⟨a, b, ht, he, hc, hA, hB⟩
  · exact Or.inl ⟨he, hsub hv⟩
  · exact Or.inr <| Or.inl ⟨he, hsub hv⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨a, b, ha, hb, he, (root 1).trans hA, (root 0).trans hB⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨a, b, ha, hb, he, (root 1).trans hA, (root 0).trans hB⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨a, b, ha, hb, he, (root 1).trans hA, (root 0).trans hB⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨a, b, ha, hb, he, (root 1).trans hA, (root 0).trans hB⟩
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨a, b, he, dom _ hc, dom _ hc', ?_, ?_⟩
    · rw [root 1, hA, val_iff_of_subset hQ hsub hc, val_iff_of_subset hQ hsub hc']
    · rw [root 0, hB, val_iff_of_subset hQ hsub hc, val_iff_of_subset hQ hsub hc']
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨a, b, he, dom _ hc, dom _ hc', ?_, ?_⟩
    · rw [root 1, hA, val_iff_of_subset hQ hsub hc, val_iff_of_subset hQ hsub hc']
    · rw [root 0, hB, val_iff_of_subset hQ hsub hc, val_iff_of_subset hQ hsub hc']
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨a, b, ht, he, fun x hx ↦ dom _ (hc x hx), ?_, ?_⟩
    · rw [root 1, hA]
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
        (val_iff_of_subset hQ hsub (hc x hx)).symm
    · rw [root 0, hB]
      exact exists_congr fun x ↦ and_congr_right fun hx ↦
        (val_iff_of_subset hQ hsub (hc x hx)).symm
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨a, b, ht, he, fun x hx ↦ dom _ (hc x hx), ?_, ?_⟩
    · rw [root 1, hA]
      exact exists_congr fun x ↦ and_congr_right fun hx ↦
        (val_iff_of_subset hQ hsub (hc x hx)).symm
    · rw [root 0, hB]
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
        (val_iff_of_subset hQ hsub (hc x hx)).symm

/-! ## Gluing tables together -/

variable {z₁ z₂ e₁ e₂ : V}

/-- Two tables assign the same value to any node common to both.
- [HP98, Lemma I.1.72(2)] -/
lemma val_agree (h₁ : BoundedSatisfactionTable q₁ z₁ e₁)
  (h₂ : BoundedSatisfactionTable q₂ z₂ e₂) {y₁ y₂ : V}
    (hn₁ : ⟪n, y₁⟫ ∈ q₁) (hn₂ : ⟪n, y₂⟫ ∈ q₂) : y₁ = y₂ := by
  have hd₁ : ⟪π₁ n, π₂ n⟫ ∈ domain q₁ := by rw [pair_unpair]; exact mem_domain_of_pair_mem hn₁
  have hd₂ : ⟪π₁ n, π₂ n⟫ ∈ domain q₂ := by rw [pair_unpair]; exact mem_domain_of_pair_mem hn₂
  obtain ⟨i1, i0⟩ := h₁.agree h₂ (π₁ n) (π₂ n) hd₁ hd₂
  rw [pair_unpair] at i1 i0
  rcases h₁.val_zero_or_one (π₁ n) (π₂ n) hd₁ with h' | h' <;> rw [pair_unpair] at h'
  · rw [h₁.isMapping.uniq hn₁ h', h₂.isMapping.uniq hn₂ (i1.mp h')]
  · rw [h₁.isMapping.uniq hn₁ h', h₂.isMapping.uniq hn₂ (i0.mp h')]

/-- The union of two tables is again a mapping: they agree wherever both are defined.
- [HP98, Lemma I.1.72(3)] -/
lemma isMapping_union (h₁ : BoundedSatisfactionTable q₁ z₁ e₁)
  (h₂ : BoundedSatisfactionTable q₂ z₂ e₂) :
    IsMapping (q₁ ∪ q₂) := by
  intro x hx
  obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
  refine ⟨y, hy, fun y' hy' ↦ ?_⟩
  rcases mem_cup_iff.mp hy with h | h <;> rcases mem_cup_iff.mp hy' with h' | h'
  · exact h₁.isMapping.uniq h' h
  · exact h₁.val_agree h₂ h h' |>.symm
  · exact h₂.val_agree h₁ h h' |>.symm
  · exact h₂.isMapping.uniq h' h

/-- Every node of a table has a formula code bounded by the root's.
- [HP98, Definition I.1.71(1)] -/
lemma fst_le_of_mem_domain (h : BoundedSatisfactionTable q z e) : ∀ n ∈ domain q, π₁ n ≤ z := by
  have key : ∀ k n, n ∈ domain q → q ≤ π₁ n + k → π₁ n ≤ z := by
    refine ISigma1.pi1_succ_induction
      (P := fun k ↦ ∀ n, n ∈ domain q → q ≤ π₁ n + k → π₁ n ≤ z) (by definability) ?_ ?_
    · intro n hn hle
      exact absurd (by simpa using hle)
        (not_le.mpr (lt_of_le_of_lt (pi₁_le_self n) (lt_of_mem_domain hn)))
    · intro k IH n hn hle
      have up : ∀ m, m ∈ domain q → π₁ n < π₁ m → π₁ m ≤ z := by
        intro m hm hlt
        refine IH m hm ?_
        calc q ≤ π₁ n + (k + 1) := hle
          _ = π₁ n + 1 + k := by ring
          _ ≤ π₁ m + k := add_le_add (lt_iff_succ_le.mp hlt) le_rfl
      rcases h.minimal n hn with rfl | ⟨a, b, e'', hm, hc⟩ | ⟨a, b, e'', hm, hc⟩ |
        ⟨w, r, e'', hm, x, hx, rfl⟩ | ⟨w, r, e'', hm, x, hx, rfl⟩
      · simp
      · rcases hc with rfl | rfl
        · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp))
        · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp))
      · rcases hc with rfl | rfl
        · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp))
        · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp))
      · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp))
      · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp))
  exact fun n hn ↦ key q n hn le_add_self

/-- A table for a proper subformula does not contain the root node.
- [HP98, Definition I.1.71(1)] -/
lemma root_not_mem_domain (h : BoundedSatisfactionTable q p e₁) (hlt : p < z) : ⟪z,
  e⟫ ∉ domain q := by
  intro hc
  have : π₁ (⟪z, e⟫ : V) ≤ p := h.fst_le_of_mem_domain _ hc
  simp only [pi₁_pair] at this
  exact absurd (lt_of_le_of_lt this hlt) (lt_irrefl z)

/-! ## Building tables -/

/-- The one-node table for a node whose Tarski clause mentions no children.
- [HP98, Lemma I.1.72(3)] -/
lemma of_atom (h : Spec ({⟪⟪z, e⟫, v⟫} : V) z e) : BoundedSatisfactionTable ({⟪⟪z, e⟫,
  v⟫} : V) z e := by
  refine ⟨IsMapping.singleton _ _, by simp, ?_, ?_⟩
  · intro z' e' hn
    obtain ⟨rfl, rfl⟩ : z' = z ∧ e' = e := by simpa using hn
    exact h
  · intro n hn
    exact Or.inl (by simpa using hn)

/-- Existence of a table for a conjunction from bounded tables for its conjuncts.
- [HP98, Lemma I.1.72(3)] -/
lemma of_and {N : V} (h₁ : BoundedSatisfactionTable q₁ p₁ e) (h₂ : BoundedSatisfactionTable q₂ p₂ e)
    (hn₁ : ∀ w ∈ q₁, w < N) (hn₂ : ∀ w ∈ q₂, w < N)
    (hr1 : ⟪⟪p₁ ^⋏ p₂, e⟫, 1⟫ < N) (hr0 : ⟪⟪p₁ ^⋏ p₂, e⟫, 0⟫ < N) :
    ∃ Q, BoundedSatisfactionTable Q (p₁ ^⋏ p₂) e ∧ ∀ w ∈ Q, w < N := by
  obtain ⟨v, hv, hv1, hv0⟩ :
      ∃ v : V, (v = 0 ∨ v = 1) ∧ (v = 1 ↔ ⟪⟪p₁, e⟫, 1⟫ ∈ q₁ ∧ ⟪⟪p₂, e⟫, 1⟫ ∈ q₂) ∧
        (v = 0 ↔ ⟪⟪p₁, e⟫, 0⟫ ∈ q₁ ∨ ⟪⟪p₂, e⟫, 0⟫ ∈ q₂) := by
    by_cases h : ⟪⟪p₁, e⟫, 1⟫ ∈ q₁ ∧ ⟪⟪p₂, e⟫, 1⟫ ∈ q₂
    · refine ⟨1, Or.inr rfl, iff_of_true rfl h, ?_⟩
      refine iff_of_false (by simp) ?_
      rintro (h0 | h0)
      · exact h₁.val_one_ne_zero h.1 h0
      · exact h₂.val_one_ne_zero h.2 h0
    · refine ⟨0, Or.inl rfl, iff_of_false (by simp) h, iff_of_true rfl ?_⟩
      by_cases h1 : ⟪⟪p₁, e⟫, 1⟫ ∈ q₁
      · have : ⟪⟪p₂, e⟫, 1⟫ ∉ q₂ := fun hc ↦ h ⟨h1, hc⟩
        rcases h₂.val_zero_or_one p₂ e h₂.mem_dom_root with hc | hc
        · exact absurd hc this
        · exact Or.inr hc
      · rcases h₁.val_zero_or_one p₁ e h₁.mem_dom_root with hc | hc
        · exact absurd hc h1
        · exact Or.inl hc
  refine ⟨insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂), ?_, ?_⟩
  · have hnr : ⟪p₁ ^⋏ p₂, e⟫ ∉ domain (q₁ ∪ q₂) := by
      rw [domain_union]
      intro hc
      rcases mem_cup_iff.mp hc with h | h
      · exact h₁.root_not_mem_domain (by simp) h
      · exact h₂.root_not_mem_domain (by simp) h
    have hmU : IsMapping (q₁ ∪ q₂) := h₁.isMapping_union h₂
    have hmQ : IsMapping (insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂)) := hmU.insert hnr
    have hs₁ : q₁ ⊆ insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
      subset_trans (union_succ_union_left q₁ q₂) (susbset_insert _ _)
    have hs₂ : q₂ ⊆ insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
      subset_trans (union_succ_union_right q₁ q₂) (susbset_insert _ _)
    have hroot : ∀ w : V, ⟪⟪p₁ ^⋏ p₂, e⟫, w⟫ ∈ insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂) ↔ w = v := by
      intro w
      constructor
      · intro h
        rcases (by simpa using h : ⟪⟪p₁ ^⋏ p₂, e⟫, w⟫ = ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ ∨
            ⟪⟪p₁ ^⋏ p₂, e⟫, w⟫ ∈ q₁ ∪ q₂) with h | h
        · exact (pair_ext_iff.mp h).2
        · exact absurd (mem_domain_of_pair_mem h) hnr
      · rintro rfl; simp
    refine ⟨hmQ, by simp, ?_, ?_⟩
    · intro z' e' hn
      rcases (by simpa [domain_union] using hn : ⟪z', e'⟫ = ⟪p₁ ^⋏ p₂, e⟫ ∨
          ⟪z', e'⟫ ∈ domain q₁ ∨ ⟪z', e'⟫ ∈ domain q₂) with h | h | h
      · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨p₁, p₂, rfl, domain_subset_domain_of_subset hs₁ h₁.mem_dom_root,
            domain_subset_domain_of_subset hs₂ h₂.mem_dom_root, ?_, ?_⟩
        · rw [hroot 1, val_iff_of_subset hmQ hs₁ h₁.mem_dom_root,
            val_iff_of_subset hmQ hs₂ h₂.mem_dom_root]
          exact eq_comm.trans hv1
        · rw [hroot 0, val_iff_of_subset hmQ hs₁ h₁.mem_dom_root,
            val_iff_of_subset hmQ hs₂ h₂.mem_dom_root]
          exact eq_comm.trans hv0
      · exact (h₁.spec' h).mono hmQ hs₁ h
      · exact (h₂.spec' h).mono hmQ hs₂ h
    · intro n hn
      rcases (by simpa [domain_union] using hn : n = ⟪p₁ ^⋏ p₂, e⟫ ∨
          n ∈ domain q₁ ∨ n ∈ domain q₂) with h | h | h
      · exact Or.inl h
      · rcases h₁.minimal' h with rfl | hm
        · exact Or.inr <| Or.inl ⟨p₁, p₂, e, by simp, Or.inl rfl⟩
        · exact Or.inr (hm.mono (fun m hm ↦ domain_subset_domain_of_subset hs₁ hm))
      · rcases h₂.minimal' h with rfl | hm
        · exact Or.inr <| Or.inl ⟨p₁, p₂, e, by simp, Or.inr rfl⟩
        · exact Or.inr (hm.mono (fun m hm ↦ domain_subset_domain_of_subset hs₂ hm))
  · intro w hw
    rcases (by simpa using hw : w = ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ ∨ w ∈ q₁ ∨ w ∈ q₂) with rfl | h | h
    · rcases hv with rfl | rfl
      · exact hr0
      · exact hr1
    · exact hn₁ _ h
    · exact hn₂ _ h

/-- Existence of a table for a disjunction from bounded tables for its disjuncts.
- [HP98, Lemma I.1.72(3)] -/
lemma of_or {N : V} (h₁ : BoundedSatisfactionTable q₁ p₁ e) (h₂ : BoundedSatisfactionTable q₂ p₂ e)
    (hn₁ : ∀ w ∈ q₁, w < N) (hn₂ : ∀ w ∈ q₂, w < N)
    (hr1 : ⟪⟪p₁ ^⋎ p₂, e⟫, 1⟫ < N) (hr0 : ⟪⟪p₁ ^⋎ p₂, e⟫, 0⟫ < N) :
    ∃ Q, BoundedSatisfactionTable Q (p₁ ^⋎ p₂) e ∧ ∀ w ∈ Q, w < N := by
  obtain ⟨v, hv, hv1, hv0⟩ :
      ∃ v : V, (v = 0 ∨ v = 1) ∧ (v = 1 ↔ ⟪⟪p₁, e⟫, 1⟫ ∈ q₁ ∨ ⟪⟪p₂, e⟫, 1⟫ ∈ q₂) ∧
        (v = 0 ↔ ⟪⟪p₁, e⟫, 0⟫ ∈ q₁ ∧ ⟪⟪p₂, e⟫, 0⟫ ∈ q₂) := by
    by_cases h : ⟪⟪p₁, e⟫, 1⟫ ∈ q₁ ∨ ⟪⟪p₂, e⟫, 1⟫ ∈ q₂
    · refine ⟨1, Or.inr rfl, iff_of_true rfl h, iff_of_false (by simp) ?_⟩
      rintro ⟨h0₁, h0₂⟩
      rcases h with h | h
      · exact h₁.val_one_ne_zero h h0₁
      · exact h₂.val_one_ne_zero h h0₂
    · refine ⟨0, Or.inl rfl, iff_of_false (by simp) h, iff_of_true rfl ⟨?_, ?_⟩⟩
      · rcases h₁.val_zero_or_one p₁ e h₁.mem_dom_root with hc | hc
        · exact absurd (Or.inl hc) h
        · exact hc
      · rcases h₂.val_zero_or_one p₂ e h₂.mem_dom_root with hc | hc
        · exact absurd (Or.inr hc) h
        · exact hc
  refine ⟨insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂), ?_, ?_⟩
  · have hnr : ⟪p₁ ^⋎ p₂, e⟫ ∉ domain (q₁ ∪ q₂) := by
      rw [domain_union]
      intro hc
      rcases mem_cup_iff.mp hc with h | h
      · exact h₁.root_not_mem_domain (by simp) h
      · exact h₂.root_not_mem_domain (by simp) h
    have hmU : IsMapping (q₁ ∪ q₂) := h₁.isMapping_union h₂
    have hmQ : IsMapping (insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂)) := hmU.insert hnr
    have hs₁ : q₁ ⊆ insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
      subset_trans (union_succ_union_left q₁ q₂) (susbset_insert _ _)
    have hs₂ : q₂ ⊆ insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
      subset_trans (union_succ_union_right q₁ q₂) (susbset_insert _ _)
    have hroot : ∀ w : V, ⟪⟪p₁ ^⋎ p₂, e⟫, w⟫ ∈ insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂) ↔ w = v := by
      intro w
      constructor
      · intro h
        rcases (by simpa using h : ⟪⟪p₁ ^⋎ p₂, e⟫, w⟫ = ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ ∨
            ⟪⟪p₁ ^⋎ p₂, e⟫, w⟫ ∈ q₁ ∪ q₂) with h | h
        · exact (pair_ext_iff.mp h).2
        · exact absurd (mem_domain_of_pair_mem h) hnr
      · rintro rfl; simp
    refine ⟨hmQ, by simp, ?_, ?_⟩
    · intro z' e' hn
      rcases (by simpa [domain_union] using hn : ⟪z', e'⟫ = ⟪p₁ ^⋎ p₂, e⟫ ∨
          ⟪z', e'⟫ ∈ domain q₁ ∨ ⟪z', e'⟫ ∈ domain q₂) with h | h | h
      · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨p₁, p₂, rfl, domain_subset_domain_of_subset hs₁ h₁.mem_dom_root,
            domain_subset_domain_of_subset hs₂ h₂.mem_dom_root, ?_, ?_⟩
        · rw [hroot 1, val_iff_of_subset hmQ hs₁ h₁.mem_dom_root,
            val_iff_of_subset hmQ hs₂ h₂.mem_dom_root]
          exact eq_comm.trans hv1
        · rw [hroot 0, val_iff_of_subset hmQ hs₁ h₁.mem_dom_root,
            val_iff_of_subset hmQ hs₂ h₂.mem_dom_root]
          exact eq_comm.trans hv0
      · exact (h₁.spec' h).mono hmQ hs₁ h
      · exact (h₂.spec' h).mono hmQ hs₂ h
    · intro n hn
      rcases (by simpa [domain_union] using hn : n = ⟪p₁ ^⋎ p₂, e⟫ ∨
          n ∈ domain q₁ ∨ n ∈ domain q₂) with h | h | h
      · exact Or.inl h
      · rcases h₁.minimal' h with rfl | hm
        · exact Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, e, by simp, Or.inl rfl⟩
        · exact Or.inr (hm.mono (fun m hm ↦ domain_subset_domain_of_subset hs₁ hm))
      · rcases h₂.minimal' h with rfl | hm
        · exact Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, e, by simp, Or.inr rfl⟩
        · exact Or.inr (hm.mono (fun m hm ↦ domain_subset_domain_of_subset hs₂ hm))
  · intro w hw
    rcases (by simpa using hw : w = ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ ∨ w ∈ q₁ ∨ w ∈ q₂) with rfl | h | h
    · rcases hv with rfl | rfl
      · exact hr0
      · exact hr1
    · exact hn₁ _ h
    · exact hn₂ _ h

/-- A single mapping contains bounded partial satisfaction tables for every body instance.
- [HP98, Lemma I.1.72(3)] -/
lemma exists_family_union {p e X N : V}
    (H : ∀ x < X, ∃ q, BoundedSatisfactionTable q p (x ∷ e) ∧ ∀ w ∈ q, w < N) :
    ∃ W : V, IsMapping W ∧ (∀ w ∈ W, w < N) ∧
      (∀ n ∈ domain W, ∃ x < X, ∃ r, BoundedSatisfactionTable r p (x ∷ e) ∧ r ⊆ W ∧ n ∈ domain r) ∧
      (∀ x < X, ∃ r, BoundedSatisfactionTable r p (x ∷ e) ∧ r ⊆ W) := by
  obtain ⟨f, hfm, hfd, hfr⟩ :
      ∃ f, IsMapping f ∧ domain f = under X ∧
        ∀ x r : V, ⟪x, r⟫ ∈ f → BoundedSatisfactionTable r p (x ∷ e) ∧ ∀ w ∈ r, w < N :=
    sigmaOne_skolem (R := fun x r : V ↦ BoundedSatisfactionTable r p (x ∷ e) ∧ ∀ w ∈ r, w < N)
      (by definability) (fun x hx ↦ H x (by simpa using hx))
  obtain ⟨W, hW⟩ : ∃ W : V, ∀ w : V, w ∈ W ↔ ∃ x < f, ∃ r < f, ⟪x, r⟫ ∈ f ∧ w ∈ r :=
    (finite_comprehension₁! (Γ := 𝚺) (by definability)
      ⟨f, by rintro i ⟨x, -, r, hrf, -, hir⟩; exact lt_trans (lt_of_mem hir) hrf⟩).exists
  have hsub : ∀ x r : V, ⟪x, r⟫ ∈ f → r ⊆ W := by
    intro x r hxr w hw
    have hlt : ⟪x, r⟫ < f := lt_of_mem hxr
    exact (hW w).mpr ⟨x, lt_of_le_of_lt (le_pair_left x r) hlt, r,
      lt_of_le_of_lt (le_pair_right x r) hlt, hxr, hw⟩
  have hmem : ∀ w ∈ W, ∃ x r : V, ⟪x, r⟫ ∈ f ∧ w ∈ r := by
    intro w hw
    obtain ⟨x, -, r, -, hxr, hwr⟩ := (hW w).mp hw
    exact ⟨x, r, hxr, hwr⟩
  have hxlt : ∀ x r : V, ⟪x, r⟫ ∈ f → x < X := by
    intro x r hxr
    have hx : x ∈ domain f := mem_domain_of_pair_mem hxr
    rw [hfd] at hx
    simpa using hx
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hn
    refine ⟨y, hy, fun y' hy' ↦ ?_⟩
    obtain ⟨x, r, hxr, hyr⟩ := hmem _ hy
    obtain ⟨x', r', hxr', hyr'⟩ := hmem _ hy'
    exact (hfr x' r' hxr').1.val_agree (hfr x r hxr).1 hyr' hyr
  · intro w hw
    obtain ⟨x, r, hxr, hwr⟩ := hmem w hw
    exact (hfr x r hxr).2 w hwr
  · intro n hn
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hn
    obtain ⟨x, r, hxr, hyr⟩ := hmem _ hy
    exact ⟨x, hxlt x r hxr, r, (hfr x r hxr).1, hsub x r hxr, mem_domain_of_pair_mem hyr⟩
  · intro x hx
    obtain ⟨r, hr⟩ := mem_domain_iff.mp (show x ∈ domain f by rw [hfd]; simpa using hx)
    exact ⟨r, (hfr x r hr).1, hsub x r hr⟩

/-- Existence of a table for a bounded universal from bounded tables for its body instances.
- [HP98, Lemma I.1.72(3)] -/
lemma of_ball {N : V} (hu : ∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) (hp : p < qqBall u p)
    (hr1 : ⟪⟪qqBall u p, e⟫, 1⟫ < N) (hr0 : ⟪⟪qqBall u p, e⟫, 0⟫ < N)
    (H : ∀ x < termVal (0 ∷ e) u, ∃ q, BoundedSatisfactionTable q p (x ∷ e) ∧ ∀ w ∈ q, w < N) :
    ∃ Q, BoundedSatisfactionTable Q (qqBall u p) e ∧ ∀ w ∈ Q, w < N := by
  obtain ⟨W, hmW, hWN, hWdom, hWfam⟩ := exists_family_union H
  have hchild : ∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain W := by
    intro x hx
    obtain ⟨r, hr, hrsub⟩ := hWfam x hx
    exact domain_subset_domain_of_subset hrsub hr.mem_dom_root
  have hval : ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W ∨ ⟪⟪p, x ∷ e⟫, 0⟫ ∈ W := by
    intro x hx
    obtain ⟨r, hr, hrsub⟩ := hWfam x hx
    rcases hr.val_zero_or_one p (x ∷ e) hr.mem_dom_root with h | h
    · exact Or.inl (hrsub h)
    · exact Or.inr (hrsub h)
  have hnotin : ⟪qqBall u p, e⟫ ∉ domain W := by
    intro hc
    obtain ⟨x, -, r, hr, -, hn⟩ := hWdom _ hc
    exact hr.root_not_mem_domain hp hn
  obtain ⟨v, hv, hv1, hv0⟩ : ∃ v : V, (v = 0 ∨ v = 1) ∧
      (v = 1 ↔ ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W) ∧
      (v = 0 ↔ ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 0⟫ ∈ W) := by
    by_cases h : ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W
    · refine ⟨1, Or.inr rfl, iff_of_true rfl h, iff_of_false (by simp) ?_⟩
      rintro ⟨x, hx, h0⟩
      exact absurd (hmW.uniq (h x hx) h0) (by simp)
    · refine ⟨0, Or.inl rfl, iff_of_false (by simp) h, iff_of_true rfl ?_⟩
      push Not at h
      obtain ⟨x, hx, h1⟩ := h
      rcases hval x hx with hc | hc
      · exact absurd hc h1
      · exact ⟨x, hx, hc⟩
  refine ⟨insert ⟪⟪qqBall u p, e⟫, v⟫ W, ?_, ?_⟩
  · have hmQ : IsMapping (insert ⟪⟪qqBall u p, e⟫, v⟫ W) := hmW.insert hnotin
    have hsW : W ⊆ insert ⟪⟪qqBall u p, e⟫, v⟫ W := susbset_insert _ _
    have hroot : ∀ w : V, ⟪⟪qqBall u p, e⟫, w⟫ ∈ insert ⟪⟪qqBall u p, e⟫, v⟫ W ↔ w = v := by
      intro w
      constructor
      · intro h
        rcases (by simpa using h : ⟪⟪qqBall u p, e⟫, w⟫ = ⟪⟪qqBall u p, e⟫, v⟫ ∨
            ⟪⟪qqBall u p, e⟫, w⟫ ∈ W) with h | h
        · exact (pair_ext_iff.mp h).2
        · exact absurd (mem_domain_of_pair_mem h) hnotin
      · rintro rfl; simp
    refine ⟨hmQ, by simp, ?_, ?_⟩
    · intro z' e' hn
      rcases (by simpa using hn : ⟪z', e'⟫ = ⟪qqBall u p, e⟫ ∨ ⟪z', e'⟫ ∈ domain W) with h | h
      · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inl ⟨u, p, hu, rfl,
            fun x hx ↦ domain_subset_domain_of_subset hsW (hchild x hx), ?_, ?_⟩
        · rw [hroot 1]
          refine (eq_comm.trans hv1).trans (forall_congr' fun x ↦ imp_congr_right fun hx ↦ ?_)
          exact (val_iff_of_subset hmQ hsW (hchild x hx)).symm
        · rw [hroot 0]
          refine (eq_comm.trans hv0).trans (exists_congr fun x ↦ and_congr_right fun hx ↦ ?_)
          exact (val_iff_of_subset hmQ hsW (hchild x hx)).symm
      · obtain ⟨x, -, r, hr, hrsub, hnd⟩ := hWdom _ h
        exact (hr.spec' hnd).mono hmQ (subset_trans hrsub hsW) hnd
    · intro n hn
      rcases (by simpa using hn : n = ⟪qqBall u p, e⟫ ∨ n ∈ domain W) with h | h
      · exact Or.inl h
      · obtain ⟨x, hx, r, hr, hrsub, hnd⟩ := hWdom _ h
        rcases hr.minimal' hnd with rfl | hm
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨u, p, e, by simp, x, hx, rfl⟩
        · exact Or.inr (hm.mono
            (fun m hm ↦ domain_subset_domain_of_subset (subset_trans hrsub hsW) hm))
  · intro w hw
    rcases (by simpa using hw : w = ⟪⟪qqBall u p, e⟫, v⟫ ∨ w ∈ W) with rfl | h
    · rcases hv with rfl | rfl
      · exact hr0
      · exact hr1
    · exact hWN _ h

/-- Existence of a table for a bounded existential from bounded tables for its body instances.
- [HP98, Lemma I.1.72(3)] -/
lemma of_bex {N : V} (hu : ∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) (hp : p < qqBex u p)
    (hr1 : ⟪⟪qqBex u p, e⟫, 1⟫ < N) (hr0 : ⟪⟪qqBex u p, e⟫, 0⟫ < N)
    (H : ∀ x < termVal (0 ∷ e) u, ∃ q, BoundedSatisfactionTable q p (x ∷ e) ∧ ∀ w ∈ q, w < N) :
    ∃ Q, BoundedSatisfactionTable Q (qqBex u p) e ∧ ∀ w ∈ Q, w < N := by
  obtain ⟨W, hmW, hWN, hWdom, hWfam⟩ := exists_family_union H
  have hchild : ∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain W := by
    intro x hx
    obtain ⟨r, hr, hrsub⟩ := hWfam x hx
    exact domain_subset_domain_of_subset hrsub hr.mem_dom_root
  have hval : ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W ∨ ⟪⟪p, x ∷ e⟫, 0⟫ ∈ W := by
    intro x hx
    obtain ⟨r, hr, hrsub⟩ := hWfam x hx
    rcases hr.val_zero_or_one p (x ∷ e) hr.mem_dom_root with h | h
    · exact Or.inl (hrsub h)
    · exact Or.inr (hrsub h)
  have hnotin : ⟪qqBex u p, e⟫ ∉ domain W := by
    intro hc
    obtain ⟨x, -, r, hr, -, hn⟩ := hWdom _ hc
    exact hr.root_not_mem_domain hp hn
  obtain ⟨v, hv, hv1, hv0⟩ : ∃ v : V, (v = 0 ∨ v = 1) ∧
      (v = 1 ↔ ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W) ∧
      (v = 0 ↔ ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 0⟫ ∈ W) := by
    by_cases h : ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W
    · refine ⟨1, Or.inr rfl, iff_of_true rfl h, iff_of_false (by simp) ?_⟩
      intro hall
      obtain ⟨x, hx, h1⟩ := h
      exact absurd (hmW.uniq h1 (hall x hx)) (by simp)
    · refine ⟨0, Or.inl rfl, iff_of_false (by simp) h, iff_of_true rfl ?_⟩
      intro x hx
      rcases hval x hx with hc | hc
      · exact absurd ⟨x, hx, hc⟩ h
      · exact hc
  refine ⟨insert ⟪⟪qqBex u p, e⟫, v⟫ W, ?_, ?_⟩
  · have hmQ : IsMapping (insert ⟪⟪qqBex u p, e⟫, v⟫ W) := hmW.insert hnotin
    have hsW : W ⊆ insert ⟪⟪qqBex u p, e⟫, v⟫ W := susbset_insert _ _
    have hroot : ∀ w : V, ⟪⟪qqBex u p, e⟫, w⟫ ∈ insert ⟪⟪qqBex u p, e⟫, v⟫ W ↔ w = v := by
      intro w
      constructor
      · intro h
        rcases (by simpa using h : ⟪⟪qqBex u p, e⟫, w⟫ = ⟪⟪qqBex u p, e⟫, v⟫ ∨
            ⟪⟪qqBex u p, e⟫, w⟫ ∈ W) with h | h
        · exact (pair_ext_iff.mp h).2
        · exact absurd (mem_domain_of_pair_mem h) hnotin
      · rintro rfl; simp
    refine ⟨hmQ, by simp, ?_, ?_⟩
    · intro z' e' hn
      rcases (by simpa using hn : ⟪z', e'⟫ = ⟪qqBex u p, e⟫ ∨ ⟪z', e'⟫ ∈ domain W) with h | h
      · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr ⟨u, p, hu, rfl,
            fun x hx ↦ domain_subset_domain_of_subset hsW (hchild x hx), ?_, ?_⟩
        · rw [hroot 1]
          refine (eq_comm.trans hv1).trans (exists_congr fun x ↦ and_congr_right fun hx ↦ ?_)
          exact (val_iff_of_subset hmQ hsW (hchild x hx)).symm
        · rw [hroot 0]
          refine (eq_comm.trans hv0).trans (forall_congr' fun x ↦ imp_congr_right fun hx ↦ ?_)
          exact (val_iff_of_subset hmQ hsW (hchild x hx)).symm
      · obtain ⟨x, -, r, hr, hrsub, hnd⟩ := hWdom _ h
        exact (hr.spec' hnd).mono hmQ (subset_trans hrsub hsW) hnd
    · intro n hn
      rcases (by simpa using hn : n = ⟪qqBex u p, e⟫ ∨ n ∈ domain W) with h | h
      · exact Or.inl h
      · obtain ⟨x, hx, r, hr, hrsub, hnd⟩ := hWdom _ h
        rcases hr.minimal' hnd with rfl | hm
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨u, p, e, by simp, x, hx, rfl⟩
        · exact Or.inr (hm.mono
            (fun m hm ↦ domain_subset_domain_of_subset (subset_trans hrsub hsW) hm))
  · intro w hw
    rcases (by simpa using hw : w = ⟪⟪qqBex u p, e⟫, v⟫ ∨ w ∈ W) with rfl | h
    · rcases hv with rfl | rfl
      · exact hr0
      · exact hr1
    · exact hWN _ h

/-! ## Bound bookkeeping -/

/-- A one-node table is within the bound.
- [HP98, Lemma I.1.72(3)] -/
lemma singleton_le_tableBound {z e v : V} (hv : v ≤ 1) :
    ({⟪⟪z, e⟫, v⟫} : V) ≤ tableBound z e := by
  rw [singleton_def]
  calc Exp.exp ⟪⟪z, e⟫, v⟫ ≤ Exp.exp (iterExp (tableExp z e) 2) :=
        exp_monotone_le.mpr (node_le_iterExp hv)
    _ = iterExp (tableExp z e) 3 := by rw [show (3 : V) = 2 + 1 from by ring, iterExp_succ]
    _ ≤ tableBound z e := by
        rw [tableBound, show 8 * z + 24 = 3 + (8 * z + 21) from by ring, iterExp_add]
        exact le_iterExp _ _

/-- A root node lies below the designated iterated-exponential bound.
- [HP98, Lemma I.1.72(3)] -/
lemma node_lt_step {z e v : V} (hv : v ≤ 1) :
    ⟪⟪z, e⟫, v⟫ < iterExp (tableExp z e) (8 * z + 21) := by
  calc ⟪⟪z, e⟫, v⟫ ≤ iterExp (tableExp z e) 2 := node_le_iterExp hv
    _ < iterExp (tableExp z e) 3 := iterExp_lt_of_lt _ (by
        rw [show (3 : V) = 2 + 1 from by ring]; simp)
    _ ≤ iterExp (tableExp z e) (8 * z + 21) := by
        rw [show 8 * z + 21 = 3 + (8 * z + 18) from by ring, iterExp_add]
        exact le_iterExp _ _

/-- One exponential above the working bound is still within the bound.
- [HP98, Lemma I.1.72(3)] -/
lemma exp_step_le_tableBound (z e : V) :
    Exp.exp (iterExp (tableExp z e) (8 * z + 21)) ≤ tableBound z e :=
  calc Exp.exp (iterExp (tableExp z e) (8 * z + 21))
      = iterExp (tableExp z e) (8 * z + 21 + 1) := (iterExp_succ _ _).symm
    _ ≤ iterExp (tableExp z e) (8 * z + 24) := iterExp_le_iterExp_right _ (by
        calc 8 * z + 21 + 1 = 8 * z + 22 := by ring
          _ ≤ 8 * z + 22 + 2 := le_self_add
          _ = 8 * z + 24 := by ring)
    _ = tableBound z e := rfl

/-- The bound for an immediate subformula lies below the working bound.
- [HP98, Lemma I.1.72(3)] -/
lemma tableBound_le_step {p z e : V} (h : p < z) :
    tableBound p e ≤ iterExp (tableExp z e) (8 * z + 21) := by
  have h1 : p + 1 ≤ z := lt_iff_succ_le.mp h
  calc tableBound p e = iterExp (tableExp p e) (8 * p + 24) := rfl
    _ ≤ iterExp (tableExp z e) (8 * p + 24) :=
        iterExp_le_iterExp_left (tableExp_mono (le_of_lt h)) _
    _ ≤ iterExp (tableExp z e) (8 * z + 21) := by
        refine iterExp_le_iterExp_right _ ?_
        calc 8 * p + 24 = 8 * (p + 1) + 16 := by ring
          _ ≤ 8 * z + 16 := add_le_add (mul_le_mul le_rfl h1 (by simp) (by simp)) le_rfl
          _ ≤ 8 * z + 16 + 5 := le_self_add
          _ = 8 * z + 21 := by ring

/-- The bound for the body of a bounded quantifier lies below the working bound.
- [HP98, Lemma I.1.72(3)] -/
lemma tableBound_le_step_quant {p z u x e : V} (hp : p < z) (hu : u < z)
    (hx : x < termVal (0 ∷ e) u) :
    tableBound p (x ∷ e) ≤ iterExp (tableExp z e) (8 * z + 21) := by
  have h1 : p + 1 ≤ z := lt_iff_succ_le.mp hp
  calc tableBound p (x ∷ e) = iterExp (tableExp p (x ∷ e)) (8 * p + 24) := rfl
    _ ≤ iterExp (iterExp (tableExp z e) 4) (8 * p + 24) :=
        iterExp_le_iterExp_left (tableExp_step hp hu hx) _
    _ = iterExp (tableExp z e) (4 + (8 * p + 24)) := (iterExp_add _ _ _).symm
    _ ≤ iterExp (tableExp z e) (8 * z + 21) := by
        refine iterExp_le_iterExp_right _ ?_
        calc 4 + (8 * p + 24) = 8 * (p + 1) + 20 := by ring
          _ ≤ 8 * z + 20 := add_le_add (mul_le_mul le_rfl h1 (by simp) (by simp)) le_rfl
          _ ≤ 8 * z + 20 + 1 := le_self_add
          _ = 8 * z + 21 := by ring

/-! ## The atomic cases -/

/-- The one-node table for a well-formed atomic code.
- [HP98, Lemma I.1.72(3)] -/
lemma exists_atom_table {z e : V} (hz' : IsUFormula ℒₒᵣ z)
    (h : z = ^⊤ ∨ z = ^⊥ ∨ (∃ k r w, z = ^rel k r w) ∨ (∃ k r w, z = ^nrel k r w)) :
    ∃ v : V, v ≤ 1 ∧ BoundedSatisfactionTable ({⟪⟪z, e⟫, v⟫} : V) z e := by
  rcases h with rfl | rfl | ⟨k, r, w, rfl⟩ | ⟨k, r, w, rfl⟩
  · exact ⟨1, le_rfl, of_atom (Or.inl ⟨rfl, by simp⟩)⟩
  · exact ⟨0, by simp, of_atom (Or.inr <| Or.inl ⟨rfl, by simp⟩)⟩
  · rcases uformula_rel_cases hz' with ⟨t, u, ht, hu, hzz⟩ | ⟨t, u, ht, hu, hzz⟩
    · rw [hzz]
      by_cases hc : termVal e t = termVal e u
      · exact ⟨1, le_rfl, of_atom (Or.inr <| Or.inr <| Or.inl
          ⟨t, u, ht, hu, rfl, by simp [hc], by simp [hc]⟩)⟩
      · exact ⟨0, by simp, of_atom (Or.inr <| Or.inr <| Or.inl
          ⟨t, u, ht, hu, rfl, by simp [hc], by simp [hc]⟩)⟩
    · rw [hzz]
      by_cases hc : termVal e t < termVal e u
      · exact ⟨1, le_rfl, of_atom (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨t, u, ht, hu, rfl, by simp [hc], by simp [hc]⟩)⟩
      · exact ⟨0, by simp, of_atom (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨t, u, ht, hu, rfl, by simp [hc], by simp [hc]⟩)⟩
  · rcases uformula_nrel_cases hz' with ⟨t, u, ht, hu, hzz⟩ | ⟨t, u, ht, hu, hzz⟩
    · rw [hzz]
      by_cases hc : termVal e t = termVal e u
      · exact ⟨0, by simp, of_atom (Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨t, u, ht, hu, rfl, by simp [hc], by simp [hc]⟩)⟩
      · exact ⟨1, le_rfl, of_atom (Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨t, u, ht, hu, rfl, by simp [hc], by simp [hc]⟩)⟩
    · rw [hzz]
      by_cases hc : termVal e t < termVal e u
      · exact ⟨0, by simp, of_atom (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨t, u, ht, hu, rfl, by simp [hc], by simp [hc]⟩)⟩
      · exact ⟨1, le_rfl, of_atom (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨t, u, ht, hu, rfl, by simp [hc], by simp [hc]⟩)⟩

end BoundedSatisfactionTable

/-! ## Existence -/

/-- Every well-formed internally $\Delta_0$ formula has a partial satisfaction table under every
assignment.
- [HP98, Lemma I.1.72(3)] -/
theorem BoundedSatisfactionTable.exists {z e : V} (hz : IsBounded z) (hz' : IsUFormula ℒₒᵣ z) :
    ∃ q, BoundedSatisfactionTable q z e := by
  suffices H : ∀ z, IsBounded z →
      ∀ e b, b = tableBound z e → IsUFormula ℒₒᵣ z → ∃ q ≤ b, BoundedSatisfactionTable q z e by
    obtain ⟨q, -, hq⟩ := H z hz e (tableBound z e) rfl hz'
    exact ⟨q, hq⟩
  refine IsBounded.induction 𝚷
    (P := fun z ↦ ∀ e b, b = tableBound z e → IsUFormula ℒₒᵣ z → ∃ q ≤ b,
      BoundedSatisfactionTable q z e)
    (by simp only [tableBound, tableExp]; definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro e b hb hu
    subst hb
    obtain ⟨v, hv, hq⟩ := BoundedSatisfactionTable.exists_atom_table (e := e) hu (Or.inl rfl)
    exact ⟨_, BoundedSatisfactionTable.singleton_le_tableBound hv, hq⟩
  · intro e b hb hu
    subst hb
    obtain ⟨v, hv,
      hq⟩ := BoundedSatisfactionTable.exists_atom_table (e := e) hu (Or.inr <| Or.inl rfl)
    exact ⟨_, BoundedSatisfactionTable.singleton_le_tableBound hv, hq⟩
  · intro k r w e b hb hu
    subst hb
    obtain ⟨v, hv, hq⟩ :=
      BoundedSatisfactionTable.exists_atom_table (e := e) hu (Or.inr <| Or.inr <| Or.inl ⟨k, r, w,
        rfl⟩)
    exact ⟨_, BoundedSatisfactionTable.singleton_le_tableBound hv, hq⟩
  · intro k r w e b hb hu
    subst hb
    obtain ⟨v, hv, hq⟩ :=
      BoundedSatisfactionTable.exists_atom_table (e := e) hu (Or.inr <| Or.inr <| Or.inr ⟨k, r, w,
        rfl⟩)
    exact ⟨_, BoundedSatisfactionTable.singleton_le_tableBound hv, hq⟩
  · intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ e b hb hu
    subst hb
    obtain ⟨hu₁, hu₂⟩ : IsUFormula ℒₒᵣ p₁ ∧ IsUFormula ℒₒᵣ p₂ := by simpa using hu
    obtain ⟨q₁, hb₁, hq₁⟩ := ih₁ e _ rfl hu₁
    obtain ⟨q₂, hb₂, hq₂⟩ := ih₂ e _ rfl hu₂
    obtain ⟨Q, hQ, hQN⟩ := hq₁.of_and hq₂
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₁ (BoundedSatisfactionTable.tableBound_le_step (by simp))))
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₂ (BoundedSatisfactionTable.tableBound_le_step (by simp))))
      (BoundedSatisfactionTable.node_lt_step le_rfl)
        (BoundedSatisfactionTable.node_lt_step (by simp))
    refine ⟨Q, ?_, hQ⟩
    calc Q ≤ Exp.exp (iterExp (tableExp (p₁ ^⋏ p₂) e) (8 * (p₁ ^⋏ p₂) + 21)) :=
          le_of_lt (lt_exp_iff.mpr hQN)
      _ ≤ tableBound (p₁ ^⋏ p₂) e := BoundedSatisfactionTable.exp_step_le_tableBound _ _
  · intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ e b hb hu
    subst hb
    obtain ⟨hu₁, hu₂⟩ : IsUFormula ℒₒᵣ p₁ ∧ IsUFormula ℒₒᵣ p₂ := by simpa using hu
    obtain ⟨q₁, hb₁, hq₁⟩ := ih₁ e _ rfl hu₁
    obtain ⟨q₂, hb₂, hq₂⟩ := ih₂ e _ rfl hu₂
    obtain ⟨Q, hQ, hQN⟩ := hq₁.of_or hq₂
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₁ (BoundedSatisfactionTable.tableBound_le_step (by simp))))
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₂ (BoundedSatisfactionTable.tableBound_le_step (by simp))))
      (BoundedSatisfactionTable.node_lt_step le_rfl)
        (BoundedSatisfactionTable.node_lt_step (by simp))
    refine ⟨Q, ?_, hQ⟩
    calc Q ≤ Exp.exp (iterExp (tableExp (p₁ ^⋎ p₂) e) (8 * (p₁ ^⋎ p₂) + 21)) :=
          le_of_lt (lt_exp_iff.mpr hQN)
      _ ≤ tableBound (p₁ ^⋎ p₂) e := BoundedSatisfactionTable.exp_step_le_tableBound _ _
  · intro t p ht hp ih e b hb hu
    subst hb
    have hup : IsUFormula ℒₒᵣ p := by
      have h := hu
      simp only [qqBall, IsUFormula.all, IsUFormula.or] at h
      exact h.2
    obtain ⟨Q, hQ, hQN⟩ := BoundedSatisfactionTable.of_ball (e := e) ⟨t, ht, rfl⟩ (by simp)
      (BoundedSatisfactionTable.node_lt_step le_rfl)
        (BoundedSatisfactionTable.node_lt_step (by simp)) (fun x hx ↦ by
        obtain ⟨q, hqb, hq⟩ := ih (x ∷ e) _ rfl hup
        exact ⟨q, hq, fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
          (le_trans hqb
            (BoundedSatisfactionTable.tableBound_le_step_quant (by simp) (by simp) hx))⟩)
    refine ⟨Q, ?_, hQ⟩
    calc Q ≤ Exp.exp (iterExp (tableExp (qqBall (termBShift ℒₒᵣ t) p) e)
              (8 * qqBall (termBShift ℒₒᵣ t) p + 21)) := le_of_lt (lt_exp_iff.mpr hQN)
      _ ≤ tableBound
        (qqBall (termBShift ℒₒᵣ t) p) e := BoundedSatisfactionTable.exp_step_le_tableBound _ _
  · intro t p ht hp ih e b hb hu
    subst hb
    have hup : IsUFormula ℒₒᵣ p := by
      have h := hu
      simp only [qqBex, IsUFormula.ex, IsUFormula.and] at h
      exact h.2
    obtain ⟨Q, hQ, hQN⟩ := BoundedSatisfactionTable.of_bex (e := e) ⟨t, ht, rfl⟩ (by simp)
      (BoundedSatisfactionTable.node_lt_step le_rfl)
        (BoundedSatisfactionTable.node_lt_step (by simp)) (fun x hx ↦ by
        obtain ⟨q, hqb, hq⟩ := ih (x ∷ e) _ rfl hup
        exact ⟨q, hq, fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
          (le_trans hqb
            (BoundedSatisfactionTable.tableBound_le_step_quant (by simp) (by simp) hx))⟩)
    refine ⟨Q, ?_, hQ⟩
    calc Q ≤ Exp.exp (iterExp (tableExp (qqBex (termBShift ℒₒᵣ t) p) e)
              (8 * qqBex (termBShift ℒₒᵣ t) p + 21)) := le_of_lt (lt_exp_iff.mpr hQN)
      _ ≤ tableBound
        (qqBex (termBShift ℒₒᵣ t) p) e := BoundedSatisfactionTable.exp_step_le_tableBound _ _

@[simp] lemma isRel_two_zero : (ℒₒᵣ).IsRel (2 : V) 0 := by
  simpa using Arithmetic.LOR_rel_eqIndex (V := V)

@[simp] lemma isRel_two_one : (ℒₒᵣ).IsRel (2 : V) 1 := by
  simpa using Arithmetic.LOR_rel_ltIndex (V := V)

/-- A $\Delta_0$ code beginning with the bounded existential constructor has a $\Delta_0$ body.
- [HP98, Lemma I.1.68(2)] -/
lemma IsBounded.of_qqBex {u p : V} (h : IsBounded (qqBex u p)) : IsBounded p := by
  obtain ⟨u', q', -, hq', heq⟩ :=
    IsBounded.of_ex (p := (Arithmetic.qqLT (qqBvar 0) u) ^⋏ p) h
  obtain ⟨-, rfl⟩ := (qqAnd_inj _ _ _ _).mp heq
  exact hq'

lemma coe_quote_eq : (⌜(Language.Eq.eq : (ℒₒᵣ).Rel 2)⌝ : V) = 0 := coe_eqIndex_eq

lemma coe_quote_lt : (⌜(Language.LT.lt : (ℒₒᵣ).Rel 2)⌝ : V) = 1 := coe_ltIndex_eq

/-- A well-formed positive atom of `ℒₒᵣ` is a coded equality or a coded less-than.
- [HP98, 1.64] -/
lemma rel_cases {k r v : V} (h : IsUFormula ℒₒᵣ (^rel k r v)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r v = t ^= u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r v = t ^< u) := by
  obtain ⟨hr, hv⟩ := IsUFormula.rel.mp h
  rcases Arithmetic.isRel_iff_LOR.mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv
  · exact Or.inl ⟨a, b, ha, hb, by rw [Arithmetic.qqEQ, coe_quote_eq, coe_eqIndex_eq]⟩
  · exact Or.inr ⟨a, b, ha, hb, by rw [Arithmetic.qqLT, coe_quote_lt, coe_ltIndex_eq]⟩

/-- A well-formed negative atom of `ℒₒᵣ` is a coded inequality or a coded not-less-than.
- [HP98, 1.64] -/
lemma nrel_cases {k r v : V} (h : IsUFormula ℒₒᵣ (^nrel k r v)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r v = t ^≠ u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r v = t ^≮ u) := by
  obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp h
  rcases Arithmetic.isRel_iff_LOR.mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv
  · exact Or.inl ⟨a, b, ha, hb, by rw [Arithmetic.qqNEQ, coe_quote_eq, coe_eqIndex_eq]⟩
  · exact Or.inr ⟨a, b, ha, hb, by rw [Arithmetic.qqNLT, coe_quote_lt, coe_ltIndex_eq]⟩

/-! ## Substitution and the coded quantifiers -/

lemma isSemiterm_of_termBShift {n t : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t)) : IsSemiterm ℒₒᵣ n t :=
  (IsSemiterm.def (L := ℒₒᵣ)).mpr
    ⟨ht, (termBV_termBShift_le (L := ℒₒᵣ) ht n).mp ((IsSemiterm.def (L := ℒₒᵣ)).mp h).2⟩

lemma isSemiformula_qqBall {n t p : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiformula ℒₒᵣ n (qqBall (termBShift ℒₒᵣ t) p)) :
    IsSemiterm ℒₒᵣ n t ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
  have h' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
    simpa [qqBall, Arithmetic.qqNLT] using h
  exact ⟨isSemiterm_of_termBShift ht h'.1, h'.2⟩

lemma isSemiformula_qqBex {n t p : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiformula ℒₒᵣ n (qqBex (termBShift ℒₒᵣ t) p)) :
    IsSemiterm ℒₒᵣ n t ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
  have h' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
    simpa [qqBex, Arithmetic.qqLT] using h
  exact ⟨isSemiterm_of_termBShift ht h'.1, h'.2⟩

/-- Substitution distributes over the coded equality atom.
- [HP98, 1.64(4)] -/
lemma substs_qqEQ {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^= u)
      = (termSubst ℒₒᵣ w t) ^= (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqEQ, ht, hu]

/-- Substitution distributes over the coded inequality atom.
- [HP98, 1.64(4)] -/
lemma substs_qqNEQ {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^≠ u)
      = (termSubst ℒₒᵣ w t) ^≠ (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqNEQ, ht, hu]

/-- Substitution distributes over the coded less-than atom.
- [HP98, 1.64(4)] -/
lemma substs_qqLT {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^< u)
      = (termSubst ℒₒᵣ w t) ^< (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqLT, ht, hu]

/-- Substitution distributes over the coded not-less-than atom.
- [HP98, 1.64(4)] -/
lemma substs_qqNLT {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^≮ u)
      = (termSubst ℒₒᵣ w t) ^≮ (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqNLT, ht, hu]

/-- Substitution commutes with the bounded universal coding operation.
- [HP98, 1.64(4)] -/
lemma substs_qqBall {n m w t p : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t)
    (hp : IsUFormula ℒₒᵣ p) :
    Bootstrapping.subst ℒₒᵣ w (qqBall (termBShift ℒₒᵣ t) p)
      = qqBall (termBShift ℒₒᵣ (termSubst ℒₒᵣ w t)) (Bootstrapping.subst ℒₒᵣ (qVec ℒₒᵣ w) p) := by
  have hbt : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) := ht.isUTerm.termBShift
  have hlt : IsUFormula ℒₒᵣ ((qqBvar 0 : V) ^≮ termBShift ℒₒᵣ t) := by
    simp [Arithmetic.qqNLT, hbt]
  rw [show qqBall (termBShift ℒₒᵣ t) p = ^∀ (((qqBvar 0 : V) ^≮ termBShift ℒₒᵣ t) ^⋎ p) from rfl,
    substs_all (by simp [hlt, hp]), substs_or hlt hp, substs_qqNLT (by simp) hbt,
    substs_qVec_bShift ht hw]
  simp [qVec, qqBall]

/-- Substitution commutes with the bounded existential coding operation.
- [HP98, 1.64(4)] -/
lemma substs_qqBex {n m w t p : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t)
    (hp : IsUFormula ℒₒᵣ p) :
    Bootstrapping.subst ℒₒᵣ w (qqBex (termBShift ℒₒᵣ t) p)
      = qqBex (termBShift ℒₒᵣ (termSubst ℒₒᵣ w t)) (Bootstrapping.subst ℒₒᵣ (qVec ℒₒᵣ w) p) := by
  have hbt : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) := ht.isUTerm.termBShift
  have hlt : IsUFormula ℒₒᵣ ((qqBvar 0 : V) ^< termBShift ℒₒᵣ t) := by
    simp [Arithmetic.qqLT, hbt]
  rw [show qqBex (termBShift ℒₒᵣ t) p = ^∃ (((qqBvar 0 : V) ^< termBShift ℒₒᵣ t) ^⋏ p) from rfl,
    substs_ex (by simp [hlt, hp]), substs_and hlt hp, substs_qqLT (by simp) hbt,
    substs_qVec_bShift ht hw]
  simp [qVec, qqBex]

/-- Evaluating the vector that enters a quantifier extends the evaluated substitution.
- [HP98, 1.64(5)] -/
lemma termValVec_qVec {n m w e x : V} (hw : IsSemitermVec ℒₒᵣ n m w) :
    termValVec (x ∷ e) (n + 1) (qVec ℒₒᵣ w) = x ∷ termValVec e n w := by
  have hq : IsUTermVec ℒₒᵣ (n + 1) (qVec ℒₒᵣ w) := hw.qVec.isUTerm
  apply nth_ext' (n + 1) (by simp [hq]) (by simp [len_termValVec hw.isUTerm])
  intro i hi
  rw [nth_termValVec hq hi]
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · simp [qVec]
  · have hj : j < n := by simpa using hi
    have hnth : (qVec ℒₒᵣ w).[j + 1] = termBShift ℒₒᵣ w.[j] := by
      rw [qVec, hw.lh]
      simp [nth_termBShiftVec hw.isUTerm hj]
    rw [hnth, termVal_termBShift (hw.isUTerm.nth hj) x e]
    simp [nth_termValVec hw.isUTerm hj]

/-- $\Delta_0$ shape is preserved by substitution.
- [HP98, Lemma I.1.68(2)] -/
lemma IsBounded.subst {n m w p : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (h : IsBounded p) :
    IsBounded (Bootstrapping.subst ℒₒᵣ w p) := by
  have H : ∀ p : V, IsBounded p → ∀ n m w, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
      IsBounded (Bootstrapping.subst ℒₒᵣ w p) := by
    apply IsBounded.induction 𝚷
      (P := fun p ↦ ∀ n m w, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
        IsBounded (Bootstrapping.subst ℒₒᵣ w p))
    · definability
    · intro n m w _ _; simp
    · intro n m w _ _; simp
    · intro k r v n m w _ hp
      obtain ⟨hr, hv⟩ := IsUFormula.rel.mp hp.isUFormula
      simp [hr, hv]
    · intro k r v n m w _ hp
      obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp hp.isUFormula
      simp [hr, hv]
    · intro p q _ _ ihp ihq n m w hw hpq
      obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq
      rw [substs_and hp.isUFormula hq.isUFormula]
      exact IsBounded.and_iff.mpr ⟨ihp n m w hw hp, ihq n m w hw hq⟩
    · intro p q _ _ ihp ihq n m w hw hpq
      obtain ⟨hp, hq⟩ := IsSemiformula.or.mp hpq
      rw [substs_or hp.isUFormula hq.isUFormula]
      exact IsBounded.or_iff.mpr ⟨ihp n m w hw hp, ihq n m w hw hq⟩
    · intro t q ht _ ih n m w hw hpq
      obtain ⟨ht', hq⟩ := isSemiformula_qqBall ht hpq
      rw [substs_qqBall hw ht' hq.isUFormula]
      exact IsBounded.ball (hw.termSubst ht').isUTerm
        (ih (n + 1) (m + 1) (qVec ℒₒᵣ w) hw.qVec hq)
    · intro t q ht _ ih n m w hw hpq
      obtain ⟨ht', hq⟩ := isSemiformula_qqBex ht hpq
      rw [substs_qqBex hw ht' hq.isUFormula]
      exact IsBounded.bex (hw.termSubst ht').isUTerm
        (ih (n + 1) (m + 1) (qVec ℒₒᵣ w) hw.qVec hq)
  exact H p h n m w hw hp

/-- `BoundedSatisfaction z e` says that `z` is an internally coded $\Delta_0$ formula satisfied by
`e`.
- [HP98, Definition I.1.71(2)] -/
structure BoundedSatisfaction (z e : V) : Prop where
  /-- The satisfied code is that of a bounded formula. -/
  isBounded : IsBounded z
  /-- The satisfied code is that of a formula. -/
  isUFormula : IsUFormula ℒₒᵣ z
  /-- Some satisfaction table rooted at `⟪z, e⟫` gives it the value `1`. -/
  exists_table : ∃ q, BoundedSatisfactionTable q z e ∧ ⟪⟪z, e⟫, 1⟫ ∈ q

namespace BoundedSatisfaction

variable {z e : V}

/-! ## Reading satisfaction off a table -/

/-- Satisfaction at a node of a table is the value the table takes there.
- [HP98, Lemma I.1.72(2)] -/
lemma iff_mem {r z e p e' : V} (hr : BoundedSatisfactionTable r z e) (hn : ⟪p, e'⟫ ∈ domain r)
    (hp : IsBounded p) (hp' : IsUFormula ℒₒᵣ p) :
    BoundedSatisfaction p e' ↔ ⟪⟪p, e'⟫, 1⟫ ∈ r := by
  constructor
  · rintro ⟨-, -, s, hs, h1⟩
    exact (hs.agree hr p e' hs.mem_dom_root hn).1.mp h1
  · intro h1
    obtain ⟨s, hs⟩ := BoundedSatisfactionTable.exists hp hp'
    exact ⟨hp, hp', s, hs, (hr.agree hs p e' hn hs.mem_dom_root).1.mp h1⟩

/-- Satisfaction of the root of a table is the value the table takes at the root.
- [HP98, Lemma I.1.72(2)] -/
lemma iff_val {r : V} (hz : IsBounded z) (hz' : IsUFormula ℒₒᵣ z)
  (hr : BoundedSatisfactionTable r z e) :
    BoundedSatisfaction z e ↔ ⟪⟪z, e⟫, 1⟫ ∈ r := iff_mem hr hr.mem_dom_root hz hz'

/-- Existential and universal table characterizations of $\Delta_0$ satisfaction agree.
- [HP98, Lemma I.1.73(1)] -/
lemma exists_iff_forall (hz : IsBounded z) (hz' : IsUFormula ℒₒᵣ z) :
    (∃ r, BoundedSatisfactionTable r z e ∧ ⟪⟪z, e⟫, 1⟫ ∈ r) ↔ ∀ r, BoundedSatisfactionTable r z e →
      ⟪⟪z, e⟫, 1⟫ ∈ r := by
  constructor
  · rintro ⟨s, hs, h1⟩ r hr
    exact (hs.agree hr z e hs.mem_dom_root hr.mem_dom_root).1.mp h1
  · intro h
    obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hz hz'
    exact ⟨r, hr, h r hr⟩

/-- The $\Pi_1$ form of satisfaction.
- [HP98, Lemma I.1.73(1)] -/
lemma iff_forall {z e : V} :
    BoundedSatisfaction z e ↔
      (IsBounded z ∧ IsUFormula ℒₒᵣ z) ∧ ∀ r, BoundedSatisfactionTable r z e → ⟪⟪z, e⟫, 1⟫ ∈ r := by
  constructor
  · rintro ⟨hz, hz', h⟩
    exact ⟨⟨hz, hz'⟩, (exists_iff_forall hz hz').mp h⟩
  · rintro ⟨⟨hz, hz'⟩, h⟩
    exact ⟨hz, hz', (exists_iff_forall hz hz').mpr h⟩

/-- The existential table characterization of $\Delta_0$ satisfaction. -/
lemma iff_exists {z e : V} :
    BoundedSatisfaction z e ↔
      (IsBounded z ∧ IsUFormula ℒₒᵣ z) ∧ ∃ r, BoundedSatisfactionTable r z e ∧ ⟪⟪z, e⟫, 1⟫ ∈ r :=
  ⟨fun h ↦ ⟨⟨h.isBounded, h.isUFormula⟩, h.exists_table⟩, fun ⟨⟨hz, hz'⟩, h⟩ ↦ ⟨hz, hz', h⟩⟩

end BoundedSatisfaction

/-- The $\Delta_1$ formula defining satisfaction for internally coded $\Delta_0$ formulas.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
noncomputable def boundedSatisfaction : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “z e. (!isBounded.sigma z ∧ !(isUFormula ℒₒᵣ).sigma z) ∧
    ∃ q, !boundedSatisfactionTable.sigma q z e ∧ !BoundedSatisfactionTableF.nodeValDef q z e 1”)
  (.mkPi “z e. (!isBounded.pi z ∧ !(isUFormula ℒₒᵣ).pi z) ∧
    ∀ q, !boundedSatisfactionTable.sigma q z e → !BoundedSatisfactionTableF.nodeValDef q z e 1”)

/-- The formula `boundedSatisfaction` defines `BoundedSatisfaction`.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
instance BoundedSatisfaction.defined : 𝚫₁-Relation (BoundedSatisfaction : V → V →
  Prop) via boundedSatisfaction := .mk <| by
  constructor
  · intro v
    suffices IsBounded (v 0) → IsUFormula ℒₒᵣ (v 0) →
        ((∃ r, BoundedSatisfactionTable r (v 0) (v 1) ∧ ⟪⟪v 0, v 1⟫, 1⟫ ∈ r) ↔
          ∀ r, BoundedSatisfactionTable r (v 0) (v 1) → ⟪⟪v 0, v 1⟫, 1⟫ ∈ r) by
      simpa [boundedSatisfaction, HierarchySymbol.Semiformula.val_sigma,
        (IsBounded.defined (V := V)).df, (IsUFormula.defined (V := V) (L := ℒₒᵣ)).df,
        (BoundedSatisfactionTable.defined (V := V)).df,
          BoundedSatisfactionTableF.nodeVal_defined.df] using this
    exact fun hz hz' ↦ BoundedSatisfaction.exists_iff_forall hz hz'
  · intro v
    simp [boundedSatisfaction, HierarchySymbol.Semiformula.val_sigma,
      BoundedSatisfaction.iff_exists,
      (IsBounded.defined (V := V)).df, (IsUFormula.defined (V := V) (L := ℒₒᵣ)).df,
      (BoundedSatisfactionTable.defined (V := V)).df, BoundedSatisfactionTableF.nodeVal_defined.df]

/-- Satisfaction for internally coded $\Delta_0$ formulas is $\Delta_1$-definable.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
instance BoundedSatisfaction.definable : 𝚫₁-Relation (BoundedSatisfaction : V → V → Prop) :=
  BoundedSatisfaction.defined.to_definable


/-! ## Tarski conditions -/

namespace BoundedSatisfaction

/-- Satisfaction implies that its formula code belongs to the $\Delta_0$ domain.
- [HP98, Theorem I.1.70(i)] -/
lemma dom {z e : V} (h : BoundedSatisfaction z e) : IsBounded z ∧ IsUFormula ℒₒᵣ z :=
  ⟨h.isBounded, h.isUFormula⟩

/-- The coded truth constant is satisfied.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma verum (e : V) : BoundedSatisfaction (^⊤ : V) e := by
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists (z := (^⊤ : V)) (e := e) (by simp) (by simp)
  exact ⟨by simp, by simp, r, hr, hr.val_verum hr.mem_dom_root⟩

/-- The coded falsehood constant is not satisfied.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma falsum (e : V) : ¬BoundedSatisfaction (^⊥ : V) e := by
  rintro ⟨-, -, r, hr, h1⟩
  exact hr.val_one_ne_zero h1 (hr.val_falsum hr.mem_dom_root)

section
variable {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u)
include ht hu

/-- Satisfaction of coded equality agrees with equality of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma eq_iff : BoundedSatisfaction (t ^= u) e ↔ termVal e t = termVal e u := by
  have hd : IsBounded (t ^= u) := by simp [Arithmetic.qqEQ]
  have hf : IsUFormula ℒₒᵣ (t ^= u) := by simp [Arithmetic.qqEQ, ht, hu]
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_eq hr.mem_dom_root

/-- Satisfaction of coded inequality agrees with inequality of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma neq_iff : BoundedSatisfaction (t ^≠ u) e ↔ termVal e t ≠ termVal e u := by
  have hd : IsBounded (t ^≠ u) := by simp [Arithmetic.qqNEQ]
  have hf : IsUFormula ℒₒᵣ (t ^≠ u) := by simp [Arithmetic.qqNEQ, ht, hu]
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_neq hr.mem_dom_root

/-- Satisfaction of coded less-than agrees with comparison of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma lt_iff : BoundedSatisfaction (t ^< u) e ↔ termVal e t < termVal e u := by
  have hd : IsBounded (t ^< u) := by simp [Arithmetic.qqLT]
  have hf : IsUFormula ℒₒᵣ (t ^< u) := by simp [Arithmetic.qqLT, ht, hu]
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_lt hr.mem_dom_root

/-- Satisfaction of coded negated less-than agrees with failure of comparison.
- [HP98, Theorem I.1.70(ii)] -/
lemma nlt_iff : BoundedSatisfaction (t ^≮ u) e ↔ ¬(termVal e t < termVal e u) := by
  have hd : IsBounded (t ^≮ u : V) := by simp [Arithmetic.qqNLT]
  have hf : IsUFormula ℒₒᵣ (t ^≮ u : V) := by simp [Arithmetic.qqNLT, ht, hu]
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_nlt hr.mem_dom_root

end

/-- Satisfaction commutes with coded conjunction.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma and_iff {p q e : V} :
    BoundedSatisfaction (p ^⋏ q) e ↔ BoundedSatisfaction p e ∧ BoundedSatisfaction q e := by
  constructor
  · rintro ⟨hd, hf, r, hr, h1⟩
    obtain ⟨hdp, hdq⟩ := IsBounded.and_iff.mp hd
    obtain ⟨hfp, hfq⟩ := IsUFormula.and.mp hf
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_and hr.mem_dom_root
    obtain ⟨v₁, v₂⟩ := (hr.val_and hr.mem_dom_root).mp h1
    exact ⟨(iff_mem hr hn₁ hdp hfp).mpr v₁, (iff_mem hr hn₂ hdq hfq).mpr v₂⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨hdp, hfp⟩ := h₁.dom
    obtain ⟨hdq, hfq⟩ := h₂.dom
    have hd : IsBounded (p ^⋏ q) := IsBounded.and_iff.mpr ⟨hdp, hdq⟩
    have hf : IsUFormula ℒₒᵣ (p ^⋏ q) := by simp [hfp, hfq]
    obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_and hr.mem_dom_root
    exact (iff_val hd hf hr).mpr ((hr.val_and hr.mem_dom_root).mpr
      ⟨(iff_mem hr hn₁ hdp hfp).mp h₁, (iff_mem hr hn₂ hdq hfq).mp h₂⟩)

/-- Satisfaction commutes with coded disjunction of well-formed formulas.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma or_iff {p q e : V} (hdp : IsBounded p) (hfp : IsUFormula ℒₒᵣ p)
    (hdq : IsBounded q) (hfq : IsUFormula ℒₒᵣ q) :
    BoundedSatisfaction (p ^⋎ q) e ↔ BoundedSatisfaction p e ∨ BoundedSatisfaction q e := by
  constructor
  · rintro ⟨-, -, r, hr, h1⟩
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_or hr.mem_dom_root
    rcases (hr.val_or hr.mem_dom_root).mp h1 with v | v
    · exact Or.inl ((iff_mem hr hn₁ hdp hfp).mpr v)
    · exact Or.inr ((iff_mem hr hn₂ hdq hfq).mpr v)
  · intro h
    have hd : IsBounded (p ^⋎ q) := IsBounded.or_iff.mpr ⟨hdp, hdq⟩
    have hf : IsUFormula ℒₒᵣ (p ^⋎ q) := by simp [hfp, hfq]
    obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_or hr.mem_dom_root
    refine (iff_val hd hf hr).mpr ((hr.val_or hr.mem_dom_root).mpr ?_)
    rcases h with h | h
    · exact Or.inl ((iff_mem hr hn₁ hdp hfp).mp h)
    · exact Or.inr ((iff_mem hr hn₂ hdq hfq).mp h)

section
variable {t q e : V} (ht : IsUTerm ℒₒᵣ t)
include ht

/-- Satisfaction of a bounded universal is bounded universal satisfaction of its body.
- [HP98, Theorem I.1.70(iv)] -/
lemma ball_iff (hq : IsBounded q) (hq' : IsUFormula ℒₒᵣ q) :
    BoundedSatisfaction (qqBall (termBShift ℒₒᵣ t) q) e ↔ ∀ x < termVal e t,
      BoundedSatisfaction q (x ∷ e) := by
  have hd : IsBounded (qqBall (termBShift ℒₒᵣ t) q) := IsBounded.ball ht hq
  have hf : IsUFormula ℒₒᵣ (qqBall (termBShift ℒₒᵣ t) q) := by
    simp [qqBall, Arithmetic.qqNLT, ht.termBShift, hq']
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf
  rw [iff_val hd hf hr, hr.val_ball ht hr.mem_dom_root]
  exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
    (iff_mem hr (hr.mem_dom_ball ht hr.mem_dom_root hx) hq hq').symm

/-- Satisfaction of a bounded existential is bounded existential satisfaction of its body.
- [HP98, Theorem I.1.70(iv)] -/
lemma bex_iff : BoundedSatisfaction (qqBex (termBShift ℒₒᵣ t) q) e ↔ ∃ x < termVal e t,
  BoundedSatisfaction q (x ∷ e) := by
  constructor
  · rintro ⟨hd, hf, r, hr, h1⟩
    have hq : IsBounded q := hd.of_qqBex
    have hq' : IsUFormula ℒₒᵣ q := by
      simpa [qqBex, Arithmetic.qqLT, ht.termBShift] using hf
    obtain ⟨x, hx, v⟩ := (hr.val_bex ht hr.mem_dom_root).mp h1
    exact ⟨x, hx, (iff_mem hr (hr.mem_dom_bex ht hr.mem_dom_root hx) hq hq').mpr v⟩
  · rintro ⟨x, hx, hsat⟩
    obtain ⟨hq, hq'⟩ := hsat.dom
    have hd : IsBounded (qqBex (termBShift ℒₒᵣ t) q) := IsBounded.bex ht hq
    have hf : IsUFormula ℒₒᵣ (qqBex (termBShift ℒₒᵣ t) q) := by
      simp [qqBex, Arithmetic.qqLT, ht.termBShift, hq']
    obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf
    refine (iff_val hd hf hr).mpr ((hr.val_bex ht hr.mem_dom_root).mpr ⟨x, hx, ?_⟩)
    exact (iff_mem hr (hr.mem_dom_bex ht hr.mem_dom_root hx) hq hq').mp hsat

end

/-- Satisfaction commutes with coded negation on $\Delta_0$ formulas.
- [HP98, Theorem I.1.70(iii)] -/
lemma neg_iff {p e : V} (hp : IsBounded p) (hp' : IsUFormula ℒₒᵣ p) :
    BoundedSatisfaction (neg ℒₒᵣ p) e ↔ ¬BoundedSatisfaction p e := by
  have H : ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p →
      ∀ e, (BoundedSatisfaction (neg ℒₒᵣ p) e ↔ ¬BoundedSatisfaction p e) := by
    apply IsBounded.induction 𝚷
      (P := fun p ↦ IsUFormula ℒₒᵣ p → ∀ e, (BoundedSatisfaction (neg ℒₒᵣ p) e ↔
        ¬BoundedSatisfaction p e))
    · definability
    · intro _ e; simp
    · intro _ e; simp
    · intro k r v h e
      rcases rel_cases h with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩
      · rw [heq, Arithmetic.neg_eq ht hu, neq_iff ht hu, eq_iff ht hu]
      · rw [heq, Arithmetic.neg_lt ht hu, nlt_iff ht hu, lt_iff ht hu]
    · intro k r v h e
      rcases nrel_cases h with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩
      · rw [heq, Arithmetic.neg_neq ht hu, eq_iff ht hu, neq_iff ht hu]; simp
      · rw [heq, Arithmetic.neg_nlt ht hu, lt_iff ht hu, nlt_iff ht hu]; simp
    · intro p q hdp hdq ihp ihq h e
      obtain ⟨hfp, hfq⟩ := IsUFormula.and.mp h
      rw [neg_and hfp hfq,
        or_iff (IsBounded.neg hfp hdp) hfp.neg (IsBounded.neg hfq hdq) hfq.neg,
        ihp hfp e, ihq hfq e, and_iff]
      tauto
    · intro p q hdp hdq ihp ihq h e
      obtain ⟨hfp, hfq⟩ := IsUFormula.or.mp h
      rw [neg_or hfp hfq, and_iff, ihp hfp e, ihq hfq e, or_iff hdp hfp hdq hfq]
      tauto
    · intro t q ht hdq ih h e
      obtain ⟨-, hfq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBall, Arithmetic.qqNLT] using h
      rw [neg_qqBall ht.termBShift hfq, bex_iff ht, ball_iff ht hdq hfq]
      constructor
      · rintro ⟨x, hx, hnx⟩ hall
        exact (ih hfq (x ∷ e)).mp hnx (hall x hx)
      · intro hn
        by_contra hc
        exact hn fun x hx ↦ by
          by_contra hnx
          exact hc ⟨x, hx, (ih hfq (x ∷ e)).mpr hnx⟩
    · intro t q ht hdq ih h e
      obtain ⟨-, hfq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBex, Arithmetic.qqLT] using h
      rw [neg_qqBex ht.termBShift hfq,
        ball_iff ht (IsBounded.neg hfq hdq) hfq.neg, bex_iff ht]
      constructor
      · rintro hall ⟨x, hx, hx'⟩
        exact (ih hfq (x ∷ e)).mp (hall x hx) hx'
      · intro hn x hx
        exact (ih hfq (x ∷ e)).mpr fun hc ↦ hn ⟨x, hx, hc⟩
  exact H p hp hp' e

/-- Satisfaction commutes with substitution of a coded vector of terms.
- [HP98, 1.64(4)]
- [HP98, Theorem I.1.70] -/
lemma subst {n m w p e : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (hp' : IsBounded p) :
    BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w p) e ↔
      BoundedSatisfaction p (termValVec e n w) := by
  have H : ∀ p : V, IsBounded p → ∀ n m w e, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
      (BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w p) e ↔
        BoundedSatisfaction p (termValVec e n w)) := by
    apply IsBounded.induction 𝚷
      (P := fun p ↦ ∀ n m w e, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
        (BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w p) e ↔
          BoundedSatisfaction p (termValVec e n w)))
    · definability
    · intro n m w e _ _; simp
    · intro n m w e _ _; simp
    · intro k r v n m w e hw hp
      rcases rel_cases hp.isUFormula with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩
      · rw [heq] at hp ⊢
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqEQ] using hp
        rw [substs_qqEQ ht hu,
          eq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm, eq_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus]
      · rw [heq] at hp ⊢
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqLT] using hp
        rw [substs_qqLT ht hu,
          lt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm, lt_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus]
    · intro k r v n m w e hw hp
      rcases nrel_cases hp.isUFormula with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩
      · rw [heq] at hp ⊢
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqNEQ] using hp
        rw [substs_qqNEQ ht hu,
          neq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm, neq_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus]
      · rw [heq] at hp ⊢
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqNLT] using hp
        rw [substs_qqNLT ht hu,
          nlt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm, nlt_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus]
    · intro p q _ _ ihp ihq n m w e hw hpq
      obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq
      rw [substs_and hp.isUFormula hq.isUFormula, and_iff, and_iff,
        ihp n m w e hw hp, ihq n m w e hw hq]
    · intro p q hdp hdq ihp ihq n m w e hw hpq
      obtain ⟨hp, hq⟩ := IsSemiformula.or.mp hpq
      rw [substs_or hp.isUFormula hq.isUFormula,
        or_iff (IsBounded.subst hw hp hdp) (hp.subst hw).isUFormula
          (IsBounded.subst hw hq hdq) (hq.subst hw).isUFormula,
        or_iff hdp hp.isUFormula hdq hq.isUFormula,
        ihp n m w e hw hp, ihq n m w e hw hq]
    · intro t q ht hdq ih n m w e hw hpq
      obtain ⟨hts, hq⟩ := isSemiformula_qqBall ht hpq
      rw [substs_qqBall hw hts hq.isUFormula,
        ball_iff (hw.termSubst hts).isUTerm (IsBounded.subst hw.qVec hq hdq)
          (hq.subst hw.qVec).isUFormula,
        ball_iff ht hdq hq.isUFormula, termVal_termSubst hw hts]
      refine forall_congr' fun x ↦ imp_congr_right fun _ ↦ ?_
      rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw]
    · intro t q ht hdq ih n m w e hw hpq
      obtain ⟨hts, hq⟩ := isSemiformula_qqBex ht hpq
      rw [substs_qqBex hw hts hq.isUFormula, bex_iff (hw.termSubst hts).isUTerm,
        bex_iff ht, termVal_termSubst hw hts]
      refine exists_congr fun x ↦ and_congr_right fun _ ↦ ?_
      rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw]
  exact H p hp' n m w e hw hp

end BoundedSatisfaction

end FFL.FirstOrder.Arithmetic.Bootstrapping
