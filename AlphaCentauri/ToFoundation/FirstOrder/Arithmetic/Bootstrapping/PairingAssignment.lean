module

public import Foundation.FirstOrder.Arithmetic.HFS.Vec

/-!
# Gaps in Foundation's `HFS.Vec`: polynomial pairing and decoding of lists

A polynomial pairing `ppair x b = (x + b)² + b + 1` and the decoding `dec` of iterated `ppair`s
into lists (`∷`).
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ppair (x b : V) : V := (x + b) * (x + b) + b + 1

lemma ppair_lt_ppair {x b x' b' : V} (h : x + b < x' + b') : ppair x b < ppair x' b' := by
  have h1 : x + b + 1 ≤ x' + b' := lt_iff_succ_le.mp h
  have h2 : (x + b + 1) * (x + b + 1) ≤ (x' + b') * (x' + b') := mul_self_le_mul_self (by simp) h1
  unfold ppair
  have : b ≤ x + b := le_add_self
  have h3 : (x + b) * (x + b) + b + 1 ≤ (x + b + 1) * (x + b + 1) := by
    calc (x + b) * (x + b) + b + 1 ≤ (x + b) * (x + b) + (x + b) + 1 := by gcongr
      _ ≤ _ := by
        have : (x + b + 1) * (x + b + 1) = (x + b) * (x + b) + (x + b) + (x + b + 1) := by grind
        rw [this]; gcongr; exact le_add_self
  have : (x' + b') * (x' + b') < (x' + b') * (x' + b') + b' + 1 := by
    rw [add_assoc]; exact lt_add_of_pos_right _ (by simp)
  exact lt_of_le_of_lt (h3.trans h2) this

private lemma ppair_eq_imp {x b x' b' : V} (h : ppair x b = ppair x' b') : x = x' ∧ b = b' := by
  rcases lt_trichotomy (x + b) (x' + b') with (hl | he | hg)
  · exact absurd h (ppair_lt_ppair hl).ne
  · have : b = b' := by
      unfold ppair at h
      rw [he] at h
      simpa using h
    subst this
    exact ⟨by simpa using he, rfl⟩
  · exact absurd h (ppair_lt_ppair hg).ne'

@[simp] lemma ppair_inj {x b x' b' : V} : ppair x b = ppair x' b' ↔ x = x' ∧ b = b' := by
  constructor
  · exact ppair_eq_imp
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] lemma lt_ppair_right (x b : V) : b < ppair x b := by
  unfold ppair
  exact lt_succ_iff_le.mpr le_add_self

@[simp] lemma lt_ppair_left (x b : V) : x < ppair x b := by
  unfold ppair
  rcases eq_zero_or_pos (x + b) with (h | h)
  · have : x = 0 := (add_eq_zero_iff_of_nonneg zero_le zero_le |>.mp h).1
    simp [this]
  · have h1 : x + b ≤ (x + b) * (x + b) := le_mul_of_one_le_left zero_le (pos_iff_one_le.mp h)
    have h2 : x ≤ x + b := le_self_add
    exact lt_succ_iff_le.mpr (le_add_right (h2.trans h1))

@[simp] lemma ppair_ne_zero (x b : V) : ppair x b ≠ 0 := by simp [ppair]

def _root_.FFL.FirstOrder.Arithmetic.ppairDef : 𝚺ᴬ₀.Semisentence 3 :=
  .mkSigma “y x b. y = (x + b) * (x + b) + b + 1”

instance ppair_defined : 𝚺ᴬ₀-Function₂ (ppair : V → V → V) via ppairDef := .mk fun v ↦ by
  simp [ppairDef, ppair]

instance ppair_definable : 𝚺ᴬ₀-Function₂ (ppair : V → V → V) := ppair_defined.to_definable

instance ppair_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₂ (ppair : V → V → V) := ppair_definable.of_zero

def IsPPair (a : V) : Prop := ∃ x ≤ a, ∃ b ≤ a, a = ppair x b

lemma isPPair_ppair (x b : V) : IsPPair (ppair x b) :=
  ⟨x, (lt_ppair_left x b).le, b, (lt_ppair_right x b).le, rfl⟩

lemma isPPair_iff {a : V} : IsPPair a ↔ ∃ x b, a = ppair x b :=
  ⟨fun ⟨x, _, b, _, h⟩ ↦ ⟨x, b, h⟩, fun ⟨x, b, h⟩ ↦ h ▸ isPPair_ppair x b⟩

def _root_.FFL.FirstOrder.Arithmetic.isPPairDef : 𝚺ᴬ₀.Semisentence 1 :=
  .mkSigma “a. ∃ x <⁺ a, ∃ b <⁺ a, !ppairDef a x b”

instance isPPair_defined : 𝚺ᴬ₀-Predicate (IsPPair : V → Prop) via isPPairDef := .mk fun v ↦ by
  simp [isPPairDef, IsPPair]

instance isPPair_definable : 𝚺ᴬ₀-Predicate (IsPPair : V → Prop) := isPPair_defined.to_definable

instance isPPair_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Predicate (IsPPair : V → Prop) := isPPair_definable.of_zero

namespace Dec

def Phi (C : Set V) (pr : V) : Prop :=
  (∃ a, pr = ⟪a, 0⟫ ∧ ¬IsPPair a) ∨ (∃ x b s, pr = ⟪ppair x b, x ∷ s⟫ ∧ ⟪b, s⟫ ∈ C)

private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
    (∃ a ≤ pr, pr = ⟪a, 0⟫ ∧ ¬IsPPair a) ∨
    (∃ x ≤ pr, ∃ b ≤ pr, ∃ s ≤ pr, ∃ pb ≤ pr, pb = ppair x b ∧ ∃ xs ≤ pr, xs = x ∷ s ∧
      pr = ⟪pb, xs⟫ ∧ ∃ bs < C, bs = ⟪b, s⟫ ∧ bs ∈ C) := by
  constructor
  · rintro (⟨a, rfl, h⟩ | ⟨x, b, s, rfl, hC⟩)
    · left; exact ⟨a, by simp, rfl, h⟩
    · have hpb : ppair x b ≤ ⟪ppair x b, x ∷ s⟫ := le_pair_left _ _
      have hxs : x ∷ s ≤ ⟪ppair x b, x ∷ s⟫ := le_pair_right _ _
      right
      exact ⟨x, (lt_ppair_left x b).le.trans hpb, b, (lt_ppair_right x b).le.trans hpb,
        s, (lt_adjoin' x s).le.trans hxs, ppair x b, hpb, rfl, x ∷ s, hxs, rfl, rfl,
        _, lt_of_mem hC, rfl, hC⟩
  · rintro (⟨a, _, rfl, h⟩ | ⟨x, _, b, _, s, _, pb, _, rfl, xs, _, rfl, rfl, bs, _, rfl, hC⟩)
    · left; exact ⟨a, rfl, h⟩
    · right; exact ⟨x, b, s, rfl, hC⟩

def blueprint : Fixpoint.Blueprint 0 where
  core := .ofZero
    (.mkSigma “pr C.
    (∃ a <⁺ pr, !pairDef pr a 0 ∧ ¬!isPPairDef a) ∨
    (∃ x <⁺ pr, ∃ b <⁺ pr, ∃ s <⁺ pr, ∃ pb <⁺ pr, !ppairDef pb x b ∧ ∃ xs <⁺ pr, !adjoinDef xs x s ∧
      !pairDef pr pb xs ∧ ∃ bs < C, !pairDef bs b s ∧ bs ∈ C)”
    (by simp))
    _

def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .of_zero <| .mk fun v ↦ by simp [phi_iff]
  monotone := by
    rintro C C' hC _ x (h | ⟨x, b, s, rfl, h⟩)
    · left; exact h
    · right; exact ⟨x, b, s, rfl, hC h⟩

instance : construction.Finite V where
  finite := by
    rintro C v pr (h | ⟨x, b, s, rfl, h⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨⟪b, s⟫ + 1, Or.inr ⟨x, b, s, rfl, h, by simp⟩⟩

def Graph : V → Prop := construction.Fixpoint ![]

def graphDef : 𝚺ᴬ₁.Semisentence 1 := blueprint.fixpointDef

instance graph_defined : 𝚺ᴬ₁-Predicate (Graph : V → Prop) via graphDef :=
  construction.fixpoint_defined

instance graph_definable : 𝚺ᴬ₁-Predicate (Graph : V → Prop) := graph_defined.to_definable

lemma graph_case {pr : V} :
    Graph pr ↔
    (∃ a, pr = ⟪a, 0⟫ ∧ ¬IsPPair a) ∨ (∃ x b s, pr = ⟪ppair x b, x ∷ s⟫ ∧ Graph ⟪b, s⟫) :=
  construction.case

lemma graph_of_not_isPPair {a s : V} (h : ¬IsPPair a) : Graph ⟪a, s⟫ ↔ s = 0 := by
  constructor
  · intro hg
    rcases graph_case.mp hg with (⟨a', h', _⟩ | ⟨x, b, s', h', _⟩)
    · simpa using (show a = a' ∧ s = 0 by simpa using h').2
    · exact absurd ((show a = ppair x b ∧ s = x ∷ s' by simpa using h').1 ▸ isPPair_ppair x b) h
  · rintro rfl; exact graph_case.mpr <| Or.inl ⟨a, rfl, h⟩

lemma graph_ppair {x b s : V} : Graph ⟪ppair x b, s⟫ ↔ ∃ s', s = x ∷ s' ∧ Graph ⟪b, s'⟫ := by
  constructor
  · intro hg
    rcases graph_case.mp hg with (⟨a, h, hn⟩ | ⟨x', b', s', h, hs⟩)
    · exact absurd ((show ppair x b = a ∧ s = 0 by simpa using h).1 ▸ isPPair_ppair x b) hn
    · rcases show ppair x b = ppair x' b' ∧ s = x' ∷ s' by simpa using h with ⟨h1, rfl⟩
      rcases ppair_inj.mp h1 with ⟨rfl, rfl⟩
      exact ⟨s', rfl, hs⟩
  · rintro ⟨s', rfl, hs⟩
    exact graph_case.mpr <| Or.inr ⟨x, b, s', rfl, hs⟩

lemma graph_exists (a : V) : ∃ s, Graph ⟪a, s⟫ := by
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a ih =>
    by_cases ha : IsPPair a
    · rcases isPPair_iff.mp ha with ⟨x, b, rfl⟩
      rcases ih b (lt_ppair_right x b) with ⟨s, hs⟩
      exact ⟨x ∷ s, graph_ppair.mpr ⟨s, rfl, hs⟩⟩
    · exact ⟨0, (graph_of_not_isPPair ha).mpr rfl⟩

lemma graph_unique {a s₁ s₂ : V} : Graph ⟪a, s₁⟫ → Graph ⟪a, s₂⟫ → s₁ = s₂ := by
  induction a using ISigma1.pi1_order_induction generalizing s₁ s₂
  · definability
  case ind a ih =>
    intro h₁ h₂
    by_cases ha : IsPPair a
    · rcases isPPair_iff.mp ha with ⟨x, b, rfl⟩
      rcases graph_ppair.mp h₁ with ⟨t₁, rfl, ht₁⟩
      rcases graph_ppair.mp h₂ with ⟨t₂, rfl, ht₂⟩
      rw [ih b (lt_ppair_right x b) ht₁ ht₂]
    · rw [(graph_of_not_isPPair ha).mp h₁, (graph_of_not_isPPair ha).mp h₂]

lemma graph_existsUnique (a : V) : ∃! s, Graph ⟪a, s⟫ := by
  rcases graph_exists a with ⟨s, hs⟩
  exact ExistsUnique.intro s hs (fun t ht ↦ graph_unique ht hs)

end Dec

open Dec

noncomputable def dec (a : V) : V := Classical.choose! (graph_existsUnique a)

lemma dec_graph (a : V) : Graph ⟪a, dec a⟫ := Classical.choose!_spec (graph_existsUnique a)

lemma dec_eq_of_graph {a s : V} (h : Graph ⟪a, s⟫) : dec a = s :=
  graph_unique (dec_graph a) h

@[simp] lemma dec_ppair (x b : V) : dec (ppair x b) = x ∷ dec b :=
  dec_eq_of_graph (graph_ppair.mpr ⟨dec b, rfl, dec_graph b⟩)

lemma dec_of_not_isPPair {a : V} (h : ¬IsPPair a) : dec a = 0 :=
  dec_eq_of_graph ((graph_of_not_isPPair h).mpr rfl)

@[simp] lemma dec_zero : dec (0 : V) = 0 :=
  dec_of_not_isPPair fun h ↦ by
    rcases isPPair_iff.mp h with ⟨x, b, h⟩
    exact ppair_ne_zero x b h.symm

def _root_.FFL.FirstOrder.Arithmetic.decGraph : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “y a. ∃ pr, !pairDef pr a y ∧ !Dec.graphDef pr”

set_option linter.flexible false in
instance dec_defined : 𝚺ᴬ₁-Function₁ (dec : V → V) via decGraph := .mk fun v ↦ by
  simp [decGraph]
  constructor
  · intro h; simp [dec_eq_of_graph h]
  · intro h; rw [h]; exact dec_graph _

instance dec_definable : 𝚺ᴬ₁-Function₁ (dec : V → V) := dec_defined.to_definable

instance dec_definable' {Γ : Polarity} {m : ℕ} : Γᴬ_[m + 1]-Function₁ (dec : V → V) :=
  dec_definable.of_sigmaOne

end Bootstrapping
end FFL.FirstOrder.Arithmetic
