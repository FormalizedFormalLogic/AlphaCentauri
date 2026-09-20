module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# The pigeonhole schemata `𝗣𝗛𝗣` and `𝗪𝗣𝗛𝗣`

The pigeonhole axiom for `φ` says that `φ` defines no injection of $a + 1$ into $a$; the weak
pigeonhole axiom widens the domain to $a^2$, and is what Paris, Wilkie and Woods prove for
$\Delta_0$ formulas, over $\mathsf{I}\Delta_0 + \Omega_1$. Whether $\mathsf{I}\Delta_0$ proves the
$\Delta_0$ pigeonhole principle is open.

A formula is read here as a multivalued function, as in [PWW88, Problem 2]: the hypothesis asks
only that every element of the domain has a value, not that it has exactly one. [HP98, I.2.20]
states the principle instead for a map of $a$ onto $a + 1$.

- [HP98, §I.2(b)]
- [PWW88, Problems 1 and 2]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

section axioms

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

/-- `φ` defines an injection of `a` into `b`: every `x < a` has a value `y < b`, and no `y < b` is
a value of two of them.
- [PWW88, Problem 2] -/
def definesInjection {ξ} (φ : Semiformula L ξ 2) : Semiformula L ξ 2 :=
  “a b. (∀ x < a, ∃ y < b, !φ x y) ∧ ∀ x < a, ∀ x' < a, ∀ y < b, !φ x y ∧ !φ x' y → x = x'”

/-- The pigeonhole axiom for `φ`: `φ` defines no injection of `a + 1` into `a`.
- [HP98, I.2.20]
- [PWW88, Problem 2] -/
def pigeonholeAxiom {ξ} (φ : Semiformula L ξ 2) : Formula L ξ :=
  “∀ a, ¬!(definesInjection φ) (a + 1) a”

/-- The weak pigeonhole axiom for `φ`: `φ` defines no injection of `a * a` into `a`, for `1 < a`.
- [PWW88, Theorem 1] -/
def weakPigeonholeAxiom {ξ} (φ : Semiformula L ξ 2) : Formula L ξ :=
  “∀ a, 1 < a → ¬!(definesInjection φ) (a * a) a”

/-- The pigeonhole scheme for the class `Γ` of `ArithmeticSemiformula ℕ 2`.
- [HP98, I.2.22] -/
def PigeonholeScheme (Γ : ArithmeticSemiformula ℕ 2 → Prop) : ArithmeticTheory :=
  { σ | ∃ φ : ArithmeticSemiformula ℕ 2, Γ φ ∧ σ = .univCl (pigeonholeAxiom φ) }

/-- The weak pigeonhole scheme for the class `Γ` of `ArithmeticSemiformula ℕ 2`.
- [PWW88, Theorem 1] -/
def WeakPigeonholeScheme (Γ : ArithmeticSemiformula ℕ 2 → Prop) : ArithmeticTheory :=
  { σ | ∃ φ : ArithmeticSemiformula ℕ 2, Γ φ ∧ σ = .univCl (weakPigeonholeAxiom φ) }

/-- `𝗣𝗛𝗣 Γ n` is `𝗜𝚺₀` together with the pigeonhole scheme for `Hierarchy Γ n`.
- [HP98, I.2.22] -/
abbrev PigeonholeOnHierarchy (Γ : Polarity) (n : ℕ) : ArithmeticTheory :=
  𝗜𝚺₀ ∪ PigeonholeScheme (Arithmetic.Hierarchy Γ n)

prefix:max "𝗣𝗛𝗣 " => PigeonholeOnHierarchy

/-- `𝗪𝗣𝗛𝗣 Γ n` is `𝗜𝚺₀` together with the weak pigeonhole scheme for `Hierarchy Γ n`.
- [PWW88, Theorem 1] -/
abbrev WeakPigeonholeOnHierarchy (Γ : Polarity) (n : ℕ) : ArithmeticTheory :=
  𝗜𝚺₀ ∪ WeakPigeonholeScheme (Arithmetic.Hierarchy Γ n)

prefix:max "𝗪𝗣𝗛𝗣 " => WeakPigeonholeOnHierarchy

variable {C C' : ArithmeticSemiformula ℕ 2 → Prop}

lemma PigeonholeScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 2}, C φ → C' φ) :
    PigeonholeScheme C ⊆ PigeonholeScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma mem_PigeonholeScheme_of_mem {φ : ArithmeticSemiformula ℕ 2} (hφ : C φ) :
    .univCl (pigeonholeAxiom φ) ∈ PigeonholeScheme C := ⟨φ, hφ, rfl⟩

lemma WeakPigeonholeScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 2}, C φ → C' φ) :
    WeakPigeonholeScheme C ⊆ WeakPigeonholeScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma mem_WeakPigeonholeScheme_of_mem {φ : ArithmeticSemiformula ℕ 2} (hφ : C φ) :
    .univCl (weakPigeonholeAxiom φ) ∈ WeakPigeonholeScheme C := ⟨φ, hφ, rfl⟩

variable {Γ : Polarity}

lemma PigeonholeOnHierarchy_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝗣𝗛𝗣 Γ s₁ ⊆ 𝗣𝗛𝗣 Γ s₂ :=
  Set.union_subset_union_right _ (PigeonholeScheme_subset (fun H ↦ H.mono h))

lemma PigeonholeOnHierarchy_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝗣𝗛𝗣 Γ s₁ ⪯ 𝗣𝗛𝗣 Γ s₂ :=
  WeakerThan.ofSubset (PigeonholeOnHierarchy_subset_mono h)

lemma WeakPigeonholeOnHierarchy_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝗪𝗣𝗛𝗣 Γ s₁ ⊆ 𝗪𝗣𝗛𝗣 Γ s₂ :=
  Set.union_subset_union_right _ (WeakPigeonholeScheme_subset (fun H ↦ H.mono h))

lemma WeakPigeonholeOnHierarchy_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) :
    𝗪𝗣𝗛𝗣 Γ s₁ ⪯ 𝗪𝗣𝗛𝗣 Γ s₂ :=
  WeakerThan.ofSubset (WeakPigeonholeOnHierarchy_subset_mono h)

instance (Γ : Polarity) (n : ℕ) : 𝗜𝚺₀ ⪯ 𝗣𝗛𝗣 Γ n := WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (n : ℕ) : 𝗜𝚺₀ ⪯ 𝗪𝗣𝗛𝗣 Γ n := WeakerThan.ofSubset Set.subset_union_left

end axioms

section models

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- The reading of the pigeonhole axiom in a model of `𝗣𝗔⁻`.
- [PWW88, Problem 2] -/
lemma models_pigeonholeAxiom_iff (φ : ArithmeticSemiformula ℕ 2) :
    V↓[ℒₒᵣ] ⊧ (.univCl (pigeonholeAxiom φ) : ArithmeticSentence) ↔
      ∀ f : ℕ → V, ∀ a : V, (∀ x < a + 1, ∃ y < a, φ.Eval ![x, y] f) →
        ∃ x < a + 1, ∃ x' < a + 1, ∃ y < a,
          x ≠ x' ∧ φ.Eval ![x, y] f ∧ φ.Eval ![x', y] f := by
  simp [models_iff, Semiformula.eval_univCl, pigeonholeAxiom, definesInjection,
    Semiformula.eval_ballLT, Semiformula.eval_bexsLT, Semiformula.eval_substs,
    or_iff_not_imp_left, and_comm, and_left_comm]

/-- The reading of the weak pigeonhole axiom in a model of `𝗣𝗔⁻`.
- [PWW88, Theorem 1] -/
lemma models_weakPigeonholeAxiom_iff (φ : ArithmeticSemiformula ℕ 2) :
    V↓[ℒₒᵣ] ⊧ (.univCl (weakPigeonholeAxiom φ) : ArithmeticSentence) ↔
      ∀ f : ℕ → V, ∀ a : V, 1 < a → (∀ x < a * a, ∃ y < a, φ.Eval ![x, y] f) →
        ∃ x < a * a, ∃ x' < a * a, ∃ y < a,
          x ≠ x' ∧ φ.Eval ![x, y] f ∧ φ.Eval ![x', y] f := by
  simp [models_iff, Semiformula.eval_univCl, weakPigeonholeAxiom, definesInjection,
    Semiformula.eval_ballLT, Semiformula.eval_bexsLT, Semiformula.eval_substs,
    or_iff_not_imp_left, and_comm, and_left_comm]

end models

section standardModel

instance models_PigeonholeOnHierarchy (Γ : Polarity) (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗣𝗛𝗣 Γ n := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, -, rfl⟩
  apply models_pigeonholeAxiom_iff _ |>.mpr
  intro f a h
  choose! g hlt hφ using h
  obtain ⟨x, hx, x', hx', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (a + 1)) (t := Finset.range a)
      (by simp) (f := g) fun x hx ↦ Finset.mem_range.mpr (hlt x (Finset.mem_range.mp hx))
  rw [Finset.mem_range] at hx hx'
  exact ⟨x, hx, x', hx', g x, hlt x hx, hne, hφ x hx, heq ▸ hφ x' hx'⟩

instance models_WeakPigeonholeOnHierarchy (Γ : Polarity) (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗪𝗣𝗛𝗣 Γ n := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, -, rfl⟩
  apply models_weakPigeonholeAxiom_iff _ |>.mpr
  intro f a ha h
  choose! g hlt hφ using h
  obtain ⟨x, hx, x', hx', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (a * a))
      (t := Finset.range a) (by simpa using Nat.lt_mul_self_iff.mpr ha)
      (f := g) fun x hx ↦ Finset.mem_range.mpr (hlt x (Finset.mem_range.mp hx))
  rw [Finset.mem_range] at hx hx'
  exact ⟨x, hx, x', hx', g x, hlt x hx, hne, hφ x hx, heq ▸ hφ x' hx'⟩

instance (Γ : Polarity) (n : ℕ) : Consistent (𝗣𝗛𝗣 Γ n) := (𝗣𝗛𝗣 Γ n).consistent_of_sound (Eq ⊥) rfl

instance (Γ : Polarity) (n : ℕ) : Consistent (𝗪𝗣𝗛𝗣 Γ n) :=
  (𝗪𝗣𝗛𝗣 Γ n).consistent_of_sound (Eq ⊥) rfl

end standardModel

end FFL.FirstOrder.Arithmetic
