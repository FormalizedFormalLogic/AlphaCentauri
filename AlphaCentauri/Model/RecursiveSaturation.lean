module

public import AlphaCentauri.Model.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Type
public import Foundation.FirstOrder.Arithmetic.Exponential.Bit
public import Foundation.Vorspiel.Computability

/-! # Standard systems and recursive saturation

The standard system of a model of `𝗜𝚺₁` is the family of subsets of `ℕ` coded by its elements
under Ackermann's membership.

A set of arithmetic formulas is recursive when the set of its codes is. A model of arithmetic is
$\Sigma_n$-recursively saturated when it realizes every recursive $\Sigma_n$ type over it with
finitely many parameters, and recursively saturated when it realizes every recursive type over it
with finitely many parameters.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-! ## The standard system -/

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The set of standard natural numbers coded by `a` under Ackermann's membership.
- [Kay91, Exercise 11.4(a)] -/
def codedSet (a : V) : Set ℕ := {n | (n : V) ∈ a}

@[simp] lemma mem_codedSet {a : V} {n : ℕ} : n ∈ codedSet a ↔ (n : V) ∈ a := Iff.rfl

variable (V) in
/-- The standard system: the subsets of `ℕ` coded by some element of `V`.
- [Kay91, §11.1]
- [Kay91, Exercise 11.4(a)] -/
def standardSystem : Set (Set ℕ) := Set.range (codedSet (V := V))

lemma mem_standardSystem_of_finite {S : Set ℕ} (hS : S.Finite) : S ∈ standardSystem V := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    use ∅
    ext
    simp
  | @insert n S _ _ ih =>
    obtain ⟨a, rfl⟩ := ih
    use insert (n : V) a
    ext
    simp

/-- The standard system of `ℕ` is the family of finite subsets of `ℕ`.
- [Kay91, Exercise 11.1] -/
lemma standardSystem_nat : standardSystem ℕ = {S | S.Finite} := by
  ext S
  constructor
  · rintro ⟨a, rfl⟩
    apply (Set.finite_lt_nat a).subset
    intro n hn
    exact lt_of_mem (by simpa using hn)
  · apply mem_standardSystem_of_finite

section

variable {M N : Type*} [ORingStructure M] [ORingStructure N] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
  (e : M ⊆ₑ N)

namespace EndExtension

@[simp] lemma emb_natCast (n : ℕ) : e n = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.cast_succ, ih]

@[simp] lemma emb_mem_emb_iff {i a : M} : e i ∈ e a ↔ i ∈ a := by
  simpa using (Bounding.HierarchySymbol.Defined.sigmaZero_absolute e.emb
    (bit_defined (V := M)) (bit_defined (V := N)) ![i, a]).symm

@[simp] lemma codedSet_emb (a : M) : codedSet (e a) = codedSet a := by
  ext n
  simpa using e.emb_mem_emb_iff (i := (n : M)) (a := a)

end EndExtension

include e in
/-- The standard system of a model of `𝗜𝚺₁` is contained in that of an end extension which
again models `𝗜𝚺₁`.
- [Kay91, Chapter 12, p. 159] -/
lemma standardSystem_subset_of_endExtension : standardSystem M ⊆ standardSystem N := by
  rintro _ ⟨a, rfl⟩
  use e a
  exact e.codedSet_emb a

end

end

/-! ## Recursive saturation -/

/-- The set of codes of the formulas of `Φ` is recursive.
- [Kay91, §11.2] -/
def _root_.FFL.FirstOrder.Type.IsRecursive {ξ : Type*} [Encodable ξ] {k : ℕ}
    (Φ : FirstOrder.Type ℒₒᵣ ξ k) : Prop :=
  ComputablePred (· ∈ Encodable.encode '' Φ)

open scoped FFL.FirstOrder.Bounding

/-- Every finitely satisfied recursive $\Sigma_n$ type over `M` with finitely many parameters is
realized in `M`.
- [Kay91, §11.2] -/
def SigmaRecursivelySaturated (n : ℕ) (M : Type*) [ORingStructure M] : Prop :=
  ∀ (k m : ℕ) (Φ : FirstOrder.Type ℒₒᵣ (Fin m) k) (b : Fin m → M),
    (∀ φ ∈ Φ, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n φ) → Φ.IsRecursive → Φ.FinitelySatisfied M b →
      Φ.Realized M b

/-- Every finitely satisfied recursive type over `M` with finitely many parameters is realized in
`M`.
- [Kay91, §11.2] -/
def RecursivelySaturated (M : Type*) [ORingStructure M] : Prop :=
  ∀ (k m : ℕ) (Φ : FirstOrder.Type ℒₒᵣ (Fin m) k) (b : Fin m → M),
    Φ.IsRecursive → Φ.FinitelySatisfied M b → Φ.Realized M b

end FFL.FirstOrder.Arithmetic
