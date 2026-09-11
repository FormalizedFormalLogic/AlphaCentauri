module

public import AlphaCentauri.Bootstrapping.Delta0
public import AlphaCentauri.Bootstrapping.TermVal

/-!
# Partial satisfaction tables

This module defines `PSatZero`, the partial satisfaction table for an internally coded $\Delta_0$
formula under an assignment, proves it is $\Delta_1$, and proves that a table for a fixed root is
unique. `PSatZero.agree` is the form uniqueness takes for tables with different roots: two
tables give the same value at every node common to their domains. This is what reads a Tarski
condition off the table of a subformula, so no separate restriction operation is needed.

- [HP98, Definition I.1.71(1)]
- [HP98, Lemma I.1.72(1), (2)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

/-- `PSatZero q z e` says that `q` is a finite Tarski satisfaction table rooted at `⟪z, e⟫`.

- [HP98, Definition I.1.71(1)] -/
structure PSatZero (q z e : V) : Prop where
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


namespace PSatZero

variable {q z e z' e' t u p p₁ p₂ : V}

/-! ## Reading `spec` off at a node of known shape

`spec` is a ten-way disjunction over the outermost coding constructor of the node. Each lemma
below specializes it to a node of known shape: membership of the immediate children in the
domain, and how the values `1` and `0` at the node are determined. -/

/-- The Tarski clause for the truth constant, at a node of the domain.
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

/-- The Tarski clause for the falsehood constant, at a node of the domain.
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

/-- The Tarski and child-domain clauses for a coded conjunction.
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

/-- The Tarski and child-domain clauses for a coded disjunction.
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

/-- The Tarski and child-domain clauses for a coded bounded universal.
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

/-- The Tarski and child-domain clauses for a coded bounded existential.
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

/-- A table takes at most one value at each node, so `0` and `1` cannot both occur.
- [HP98, Definition I.1.71(1)] -/
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

/-- Two tables agree at every node common to their domains.
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

/-- Every node of a table is a node of any other table with the same root: the domain of a table
is determined by its root.
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

/-! ## $\Delta_1$-definability

The predicate is spelled out clause by clause: each clause of `PSatZero.spec` and of
`PSatZero.minimal` gets a `Prop` with every quantifier bounded and a defining formula, and
`pSatZero` is their assembly. Where a clause mentions `termVal`, whose graph is $\Sigma_1$ but not
$\Sigma_0$, the value is hoisted out of the clause by an existential on the $\Sigma_1$ side and by a
universal on the $\Pi_1$ side, which leaves the clause itself $\Sigma_0$. -/

namespace PSatZeroF

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

/-- The clause of `PSatZero.spec` at a node whose code is the truth constant.
- [HP98, Lemma I.1.72(1)] -/
def SpecVerum (q z e : V) : Prop := z = ^⊤ ∧ ⟪⟪z, e⟫, 1⟫ ∈ q

/-- Defining formula for `SpecVerum`.
- [HP98, Lemma I.1.72(1)] -/
def specVerumDef : 𝚺₀.Semisentence 3 := .mkSigma “q z e. !qqVerumDef z ∧ !nodeValDef q z e 1”

/-- `specVerumDef` defines `SpecVerum`.
- [HP98, Lemma I.1.72(1)] -/
instance specVerum_defined : 𝚺₀-Relation₃ (SpecVerum : V → V → V → Prop) via specVerumDef :=
  .mk fun v ↦ by simp [specVerumDef, SpecVerum, nodeVal_defined.df]

/-- The clause of `PSatZero.spec` at a node whose code is the falsehood constant.
- [HP98, Lemma I.1.72(1)] -/
def SpecFalsum (q z e : V) : Prop := z = ^⊥ ∧ ⟪⟪z, e⟫, 0⟫ ∈ q

/-- Defining formula for `SpecFalsum`.
- [HP98, Lemma I.1.72(1)] -/
def specFalsumDef : 𝚺₀.Semisentence 3 := .mkSigma “q z e. !qqFalsumDef z ∧ !nodeValDef q z e 0”

/-- `specFalsumDef` defines `SpecFalsum`.
- [HP98, Lemma I.1.72(1)] -/
instance specFalsum_defined : 𝚺₀-Relation₃ (SpecFalsum : V → V → V → Prop) via specFalsumDef :=
  .mk fun v ↦ by simp [specFalsumDef, SpecFalsum, nodeVal_defined.df]

/-- The clause of `PSatZero.spec` at a node whose code is an equality atom.
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

/-- The clause of `PSatZero.spec` at a node whose code is an inequality atom.
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

/-- The clause of `PSatZero.spec` at a node whose code is a less-than atom.
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

/-- The clause of `PSatZero.spec` at a node whose code is a not-less-than atom.
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

/-- The clause of `PSatZero.spec` at a node whose code is a conjunction.
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

/-- The clause of `PSatZero.spec` at a node whose code is a disjunction.
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

/-- The clause of `PSatZero.spec` at a node whose code is a bounded universal.
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

/-- The clause of `PSatZero.spec` at a node whose code is a bounded existential.
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


/-! ### The clause of `PSatZero.spec`, assembled -/

/-- The clause `PSatZero.spec` imposes at the node `⟪z, e⟫` of the domain of `q`.
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

/-! ### The clause of `PSatZero.minimal` -/

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

/-- The clause `PSatZero.minimal` imposes at the node `n` of the domain of `q`.
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

/-- The definition of `PSatZero`, with every quantifier bounded by the table.
- [HP98, Lemma I.1.72(1)] -/
lemma psatZero_iff {q z e : V} : PSatZero q z e ↔
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

end PSatZeroF

/-- The $\Delta_1$ formula defining partial satisfaction tables.
- [HP98, Lemma I.1.72(1)] -/
noncomputable def pSatZero : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. !isMappingDef q ∧ !PSatZeroF.nodeDomDef q z e ∧
    (∀ z' < q, ∀ e' < q, !PSatZeroF.nodeDomDef q z' e' → !PSatZeroF.specDef.sigma q z' e') ∧
    (∀ n < q, !PSatZeroF.inDomDef q n → !PSatZeroF.minimalDef.sigma q z e n)”)
  (.mkPi “q z e. !isMappingDef q ∧ !PSatZeroF.nodeDomDef q z e ∧
    (∀ z' < q, ∀ e' < q, !PSatZeroF.nodeDomDef q z' e' → !PSatZeroF.specDef.pi q z' e') ∧
    (∀ n < q, !PSatZeroF.inDomDef q n → !PSatZeroF.minimalDef.pi q z e n)”)

/-- The formula `pSatZero` defines partial satisfaction tables.
- [HP98, Lemma I.1.72(1)] -/
instance PSatZero.defined : 𝚫₁-Relation₃ (PSatZero : V → V → V → Prop) via pSatZero := .mk <| by
  constructor
  · intro v
    simp [pSatZero, HierarchySymbol.Semiformula.val_sigma, PSatZeroF.nodeDom_defined.df,
      PSatZeroF.inDom_defined.df]
  · intro v
    simp [pSatZero, HierarchySymbol.Semiformula.val_sigma, PSatZeroF.psatZero_iff,
      PSatZeroF.nodeDom_defined.df, PSatZeroF.inDom_defined.df]

/-- Partial satisfaction tables form a $\Delta_1$-definable relation.
- [HP98, Lemma I.1.72(1)] -/
instance PSatZero.definable : 𝚫₁-Relation₃ (PSatZero : V → V → V → Prop) :=
  PSatZero.defined.to_definable

end FFL.FirstOrder.Arithmetic.Bootstrapping
