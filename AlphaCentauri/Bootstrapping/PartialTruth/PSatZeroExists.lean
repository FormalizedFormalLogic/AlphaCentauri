module

public import AlphaCentauri.Bootstrapping.PartialTruth.PSatZero
public import Foundation.FirstOrder.Arithmetic.HFS.Superexp
import Mathlib.Tactic.Ring

/-!
# Existence of partial satisfaction tables

Every well-formed internally `Δ₀` formula has a partial satisfaction table under every
assignment. The statement `∀ e, ∃ q, PSatZero q z e` is `Π₂`, so `𝗜𝚺₁` cannot induct on it
directly; following [HP98, Lemma I.1.72(3)], the induction is carried out on a bounded form of
the statement instead. Where the source bounds the table uniformly by a polynomial in the code
and in an assignment bound, this development bounds it by

  `tableBound z e = iterExp (4 * z + 3 * e + 31) (8 * z + 24)`,

an exponential tower whose height decreases along the induction. The tower replaces the source's
polynomial because the domain here is the downward closure of the root rather than a uniform
rectangle `(< p) × (< r)`: entering a bounded quantifier pushes a value `x < termVal e t` onto
the assignment, and `termVal_le_poly` bounds that value only exponentially. Since the number of
nested quantifiers is bounded by the code `z`, the height `8 * z + 24` suffices; `iterExp` is
`𝚺₁` and total in `𝗜𝚺₁`, so the bound is available.

- [HP98, Lemma I.1.72(3)]
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

namespace PSatZero

variable {q q₁ q₂ Q z e z' e' n p p₁ p₂ u t v : V}

/-- The clause that `PSatZero.spec` imposes at the node `⟪z', e'⟫` of the domain of `q`.
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

/-- The clause that `PSatZero.minimal` imposes at a node of the domain other than the root.
- [HP98, Definition I.1.71(1)] -/
def MinChild (q n : V) : Prop :=
  (∃ p₁ p₂ e', ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
  (∃ p₁ p₂ e', ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
  (∃ u p e', ⟪qqBall u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫) ∨
  (∃ u p e', ⟪qqBex u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫)

/-- Reading the `spec` field of a table as the standalone clause `Spec`.
- [HP98, Definition I.1.71(1)] -/
lemma spec' (h : PSatZero q z e) (hn : ⟪z', e'⟫ ∈ domain q) : Spec q z' e' := h.spec z' e' hn

/-- Reading the `minimal` field of a table as the standalone clause `MinChild`.
- [HP98, Definition I.1.71(1)] -/
lemma minimal' (h : PSatZero q z e) (hn : n ∈ domain q) : n = ⟪z, e⟫ ∨ MinChild q n :=
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
lemma val_agree (h₁ : PSatZero q₁ z₁ e₁) (h₂ : PSatZero q₂ z₂ e₂) {y₁ y₂ : V}
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
lemma isMapping_union (h₁ : PSatZero q₁ z₁ e₁) (h₂ : PSatZero q₂ z₂ e₂) :
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
lemma fst_le_of_mem_domain (h : PSatZero q z e) : ∀ n ∈ domain q, π₁ n ≤ z := by
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
lemma root_not_mem_domain (h : PSatZero q p e₁) (hlt : p < z) : ⟪z, e⟫ ∉ domain q := by
  intro hc
  have : π₁ (⟪z, e⟫ : V) ≤ p := h.fst_le_of_mem_domain _ hc
  simp only [pi₁_pair] at this
  exact absurd (lt_of_le_of_lt this hlt) (lt_irrefl z)

/-! ## Building tables -/

/-- The one-node table for a node whose Tarski clause mentions no children.
- [HP98, Lemma I.1.72(3)] -/
lemma of_atom (h : Spec ({⟪⟪z, e⟫, v⟫} : V) z e) : PSatZero ({⟪⟪z, e⟫, v⟫} : V) z e := by
  refine ⟨IsMapping.singleton _ _, by simp, ?_, ?_⟩
  · intro z' e' hn
    obtain ⟨rfl, rfl⟩ : z' = z ∧ e' = e := by simpa using hn
    exact h
  · intro n hn
    exact Or.inl (by simpa using hn)

/-- Existence of a table for a conjunction from bounded tables for its conjuncts.
- [HP98, Lemma I.1.72(3)] -/
lemma of_and {N : V} (h₁ : PSatZero q₁ p₁ e) (h₂ : PSatZero q₂ p₂ e)
    (hn₁ : ∀ w ∈ q₁, w < N) (hn₂ : ∀ w ∈ q₂, w < N)
    (hr1 : ⟪⟪p₁ ^⋏ p₂, e⟫, 1⟫ < N) (hr0 : ⟪⟪p₁ ^⋏ p₂, e⟫, 0⟫ < N) :
    ∃ Q, PSatZero Q (p₁ ^⋏ p₂) e ∧ ∀ w ∈ Q, w < N := by
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
lemma of_or {N : V} (h₁ : PSatZero q₁ p₁ e) (h₂ : PSatZero q₂ p₂ e)
    (hn₁ : ∀ w ∈ q₁, w < N) (hn₂ : ∀ w ∈ q₂, w < N)
    (hr1 : ⟪⟪p₁ ^⋎ p₂, e⟫, 1⟫ < N) (hr0 : ⟪⟪p₁ ^⋎ p₂, e⟫, 0⟫ < N) :
    ∃ Q, PSatZero Q (p₁ ^⋎ p₂) e ∧ ∀ w ∈ Q, w < N := by
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
    (H : ∀ x < X, ∃ q, PSatZero q p (x ∷ e) ∧ ∀ w ∈ q, w < N) :
    ∃ W : V, IsMapping W ∧ (∀ w ∈ W, w < N) ∧
      (∀ n ∈ domain W, ∃ x < X, ∃ r, PSatZero r p (x ∷ e) ∧ r ⊆ W ∧ n ∈ domain r) ∧
      (∀ x < X, ∃ r, PSatZero r p (x ∷ e) ∧ r ⊆ W) := by
  obtain ⟨f, hfm, hfd, hfr⟩ :
      ∃ f, IsMapping f ∧ domain f = under X ∧
        ∀ x r : V, ⟪x, r⟫ ∈ f → PSatZero r p (x ∷ e) ∧ ∀ w ∈ r, w < N :=
    sigmaOne_skolem (R := fun x r : V ↦ PSatZero r p (x ∷ e) ∧ ∀ w ∈ r, w < N)
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
    (H : ∀ x < termVal (0 ∷ e) u, ∃ q, PSatZero q p (x ∷ e) ∧ ∀ w ∈ q, w < N) :
    ∃ Q, PSatZero Q (qqBall u p) e ∧ ∀ w ∈ Q, w < N := by
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
    (H : ∀ x < termVal (0 ∷ e) u, ∃ q, PSatZero q p (x ∷ e) ∧ ∀ w ∈ q, w < N) :
    ∃ Q, PSatZero Q (qqBex u p) e ∧ ∀ w ∈ Q, w < N := by
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
    ∃ v : V, v ≤ 1 ∧ PSatZero ({⟪⟪z, e⟫, v⟫} : V) z e := by
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

end PSatZero

/-! ## Existence -/

/-- Every well-formed internally `Δ₀` formula has a partial satisfaction table under every
assignment.
- [HP98, Lemma I.1.72(3)] -/
theorem PSatZero.exists {z e : V} (hz : IsDelta0 z) (hz' : IsUFormula ℒₒᵣ z) :
    ∃ q, PSatZero q z e := by
  suffices H : ∀ z, IsDelta0 z →
      ∀ e b, b = tableBound z e → IsUFormula ℒₒᵣ z → ∃ q ≤ b, PSatZero q z e by
    obtain ⟨q, -, hq⟩ := H z hz e (tableBound z e) rfl hz'
    exact ⟨q, hq⟩
  refine IsDelta0.induction 𝚷
    (P := fun z ↦ ∀ e b, b = tableBound z e → IsUFormula ℒₒᵣ z → ∃ q ≤ b, PSatZero q z e)
    (by simp only [tableBound, tableExp]; definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro e b hb hu
    subst hb
    obtain ⟨v, hv, hq⟩ := PSatZero.exists_atom_table (e := e) hu (Or.inl rfl)
    exact ⟨_, PSatZero.singleton_le_tableBound hv, hq⟩
  · intro e b hb hu
    subst hb
    obtain ⟨v, hv, hq⟩ := PSatZero.exists_atom_table (e := e) hu (Or.inr <| Or.inl rfl)
    exact ⟨_, PSatZero.singleton_le_tableBound hv, hq⟩
  · intro k r w e b hb hu
    subst hb
    obtain ⟨v, hv, hq⟩ :=
      PSatZero.exists_atom_table (e := e) hu (Or.inr <| Or.inr <| Or.inl ⟨k, r, w, rfl⟩)
    exact ⟨_, PSatZero.singleton_le_tableBound hv, hq⟩
  · intro k r w e b hb hu
    subst hb
    obtain ⟨v, hv, hq⟩ :=
      PSatZero.exists_atom_table (e := e) hu (Or.inr <| Or.inr <| Or.inr ⟨k, r, w, rfl⟩)
    exact ⟨_, PSatZero.singleton_le_tableBound hv, hq⟩
  · intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ e b hb hu
    subst hb
    obtain ⟨hu₁, hu₂⟩ : IsUFormula ℒₒᵣ p₁ ∧ IsUFormula ℒₒᵣ p₂ := by simpa using hu
    obtain ⟨q₁, hb₁, hq₁⟩ := ih₁ e _ rfl hu₁
    obtain ⟨q₂, hb₂, hq₂⟩ := ih₂ e _ rfl hu₂
    obtain ⟨Q, hQ, hQN⟩ := hq₁.of_and hq₂
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₁ (PSatZero.tableBound_le_step (by simp))))
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₂ (PSatZero.tableBound_le_step (by simp))))
      (PSatZero.node_lt_step le_rfl) (PSatZero.node_lt_step (by simp))
    refine ⟨Q, ?_, hQ⟩
    calc Q ≤ Exp.exp (iterExp (tableExp (p₁ ^⋏ p₂) e) (8 * (p₁ ^⋏ p₂) + 21)) :=
          le_of_lt (lt_exp_iff.mpr hQN)
      _ ≤ tableBound (p₁ ^⋏ p₂) e := PSatZero.exp_step_le_tableBound _ _
  · intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ e b hb hu
    subst hb
    obtain ⟨hu₁, hu₂⟩ : IsUFormula ℒₒᵣ p₁ ∧ IsUFormula ℒₒᵣ p₂ := by simpa using hu
    obtain ⟨q₁, hb₁, hq₁⟩ := ih₁ e _ rfl hu₁
    obtain ⟨q₂, hb₂, hq₂⟩ := ih₂ e _ rfl hu₂
    obtain ⟨Q, hQ, hQN⟩ := hq₁.of_or hq₂
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₁ (PSatZero.tableBound_le_step (by simp))))
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₂ (PSatZero.tableBound_le_step (by simp))))
      (PSatZero.node_lt_step le_rfl) (PSatZero.node_lt_step (by simp))
    refine ⟨Q, ?_, hQ⟩
    calc Q ≤ Exp.exp (iterExp (tableExp (p₁ ^⋎ p₂) e) (8 * (p₁ ^⋎ p₂) + 21)) :=
          le_of_lt (lt_exp_iff.mpr hQN)
      _ ≤ tableBound (p₁ ^⋎ p₂) e := PSatZero.exp_step_le_tableBound _ _
  · intro t p ht hp ih e b hb hu
    subst hb
    have hup : IsUFormula ℒₒᵣ p := by
      have h := hu
      simp only [qqBall, IsUFormula.all, IsUFormula.or] at h
      exact h.2
    obtain ⟨Q, hQ, hQN⟩ := PSatZero.of_ball (e := e) ⟨t, ht, rfl⟩ (by simp)
      (PSatZero.node_lt_step le_rfl) (PSatZero.node_lt_step (by simp)) (fun x hx ↦ by
        obtain ⟨q, hqb, hq⟩ := ih (x ∷ e) _ rfl hup
        exact ⟨q, hq, fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
          (le_trans hqb (PSatZero.tableBound_le_step_quant (by simp) (by simp) hx))⟩)
    refine ⟨Q, ?_, hQ⟩
    calc Q ≤ Exp.exp (iterExp (tableExp (qqBall (termBShift ℒₒᵣ t) p) e)
              (8 * qqBall (termBShift ℒₒᵣ t) p + 21)) := le_of_lt (lt_exp_iff.mpr hQN)
      _ ≤ tableBound (qqBall (termBShift ℒₒᵣ t) p) e := PSatZero.exp_step_le_tableBound _ _
  · intro t p ht hp ih e b hb hu
    subst hb
    have hup : IsUFormula ℒₒᵣ p := by
      have h := hu
      simp only [qqBex, IsUFormula.ex, IsUFormula.and] at h
      exact h.2
    obtain ⟨Q, hQ, hQN⟩ := PSatZero.of_bex (e := e) ⟨t, ht, rfl⟩ (by simp)
      (PSatZero.node_lt_step le_rfl) (PSatZero.node_lt_step (by simp)) (fun x hx ↦ by
        obtain ⟨q, hqb, hq⟩ := ih (x ∷ e) _ rfl hup
        exact ⟨q, hq, fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
          (le_trans hqb (PSatZero.tableBound_le_step_quant (by simp) (by simp) hx))⟩)
    refine ⟨Q, ?_, hQ⟩
    calc Q ≤ Exp.exp (iterExp (tableExp (qqBex (termBShift ℒₒᵣ t) p) e)
              (8 * qqBex (termBShift ℒₒᵣ t) p + 21)) := le_of_lt (lt_exp_iff.mpr hQN)
      _ ≤ tableBound (qqBex (termBShift ℒₒᵣ t) p) e := PSatZero.exp_step_le_tableBound _ _

end LO.FirstOrder.Arithmetic.Bootstrapping
