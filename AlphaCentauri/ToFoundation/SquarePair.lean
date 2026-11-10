module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Lists coded by a polynomial pairing

The pairing $(a, s) \mapsto (a + s)^2 + a + 1$ is injective and given by an arithmetical term, so
iterating it codes a list of the values of finitely many terms by the value of a single term. The
entries of such a list are read off by the projections of the pairing.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The polynomial pairing $(a + s)^2 + a + 1$. -/
def squarePair (a s : V) : V := (a + s) * (a + s) + a + 1

section pairing

lemma squarePair_le_succ_mul_succ (a s : V) :
    squarePair a s ≤ (a + s + 1) * (a + s + 1) := by
  have h : (a + s + 1) * (a + s + 1) = (a + s) * (a + s) + (a + s) + (a + s) + 1 := by grind
  rw [h, squarePair]
  apply (add_le_add_iff_right 1).mpr
  calc (a + s) * (a + s) + a ≤ (a + s) * (a + s) + (a + s) :=
        (add_le_add_iff_left _).mpr le_self_add
    _ ≤ (a + s) * (a + s) + (a + s) + (a + s) := le_self_add

lemma mul_self_lt_squarePair (a s : V) : (a + s) * (a + s) < squarePair a s := by
  rw [squarePair]
  exact lt_of_le_of_lt le_self_add (lt_add_one _)

lemma squarePair_injective {a s b t : V} (h : squarePair a s = squarePair b t) :
    a = b ∧ s = t := by
  have key : ∀ {a s b t : V}, a + s < b + t → squarePair a s < squarePair b t := by
    intro a s b t hlt
    calc squarePair a s ≤ (a + s + 1) * (a + s + 1) := squarePair_le_succ_mul_succ a s
      _ ≤ (b + t) * (b + t) := by
        have h₁ : a + s + 1 ≤ b + t := lt_iff_succ_le.mp hlt
        exact mul_le_mul' h₁ h₁
      _ < squarePair b t := mul_self_lt_squarePair b t
  have hp : a + s = b + t := by
    rcases lt_trichotomy (a + s) (b + t) with hlt | heq | hgt
    · exact absurd h (key hlt).ne
    · exact heq
    · exact absurd h (key hgt).ne'
  have ha : a = b := by
    have h₁ : (a + s) * (a + s) + a + 1 = (a + s) * (a + s) + b + 1 := by
      simpa [squarePair, hp] using h
    exact add_left_cancel (add_right_cancel h₁)
  subst ha
  exact ⟨rfl, add_left_cancel hp⟩

@[simp] lemma squarePair_inj {a s b t : V} : squarePair a s = squarePair b t ↔ a = b ∧ s = t :=
  ⟨squarePair_injective, by rintro ⟨rfl, rfl⟩; rfl⟩

lemma le_squarePair_left (a s : V) : a ≤ squarePair a s := by
  rw [squarePair]
  exact le_trans le_add_self (le_self_add (b := 1))

lemma le_squarePair_right (a s : V) : s ≤ squarePair a s := by
  rcases eq_zero_or_pos s with rfl | hs
  · simp
  · calc s ≤ a + s := le_add_self
      _ ≤ (a + s) * (a + s) :=
        le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (lt_of_lt_of_le hs le_add_self))
      _ ≤ squarePair a s := by rw [squarePair]; exact le_trans le_self_add le_self_add

end pairing

section projections

lemma exists_unique_squarePairFst (x : V) :
    ∃! a, (∃ s, x = squarePair a s) ∨ ((∀ b s, x ≠ squarePair b s) ∧ a = 0) := by
  by_cases h : ∃ b s, x = squarePair b s
  · obtain ⟨b, s, rfl⟩ := h
    refine ⟨b, Or.inl ⟨s, rfl⟩, ?_⟩
    rintro a (⟨t, ht⟩ | ⟨hn, -⟩)
    · exact (squarePair_injective ht).1.symm
    · exact absurd rfl (hn b s)
  · push Not at h
    refine ⟨0, Or.inr ⟨h, rfl⟩, ?_⟩
    rintro a (⟨t, ht⟩ | ⟨-, rfl⟩)
    · exact absurd ht (h a t)
    · rfl

lemma exists_unique_squarePairSnd (x : V) :
    ∃! s, (∃ a, x = squarePair a s) ∨ ((∀ b t, x ≠ squarePair b t) ∧ s = 0) := by
  by_cases h : ∃ b t, x = squarePair b t
  · obtain ⟨b, t, rfl⟩ := h
    refine ⟨t, Or.inl ⟨b, rfl⟩, ?_⟩
    rintro s (⟨a, ha⟩ | ⟨hn, -⟩)
    · exact (squarePair_injective ha).2.symm
    · exact absurd rfl (hn b t)
  · push Not at h
    refine ⟨0, Or.inr ⟨h, rfl⟩, ?_⟩
    rintro s (⟨a, ha⟩ | ⟨-, rfl⟩)
    · exact absurd ha (h a s)
    · rfl

/-- The first projection of `squarePair`, and `0` off its range. -/
noncomputable def squarePairFst (x : V) : V := Classical.choose! (exists_unique_squarePairFst x)

/-- The second projection of `squarePair`, and `0` off its range. -/
noncomputable def squarePairSnd (x : V) : V := Classical.choose! (exists_unique_squarePairSnd x)

@[simp] lemma squarePairFst_squarePair (a s : V) : squarePairFst (squarePair a s) = a :=
  (exists_unique_squarePairFst (squarePair a s)).unique
    (Classical.choose!_spec (exists_unique_squarePairFst (squarePair a s))) (Or.inl ⟨s, rfl⟩)

@[simp] lemma squarePairSnd_squarePair (a s : V) : squarePairSnd (squarePair a s) = s :=
  (exists_unique_squarePairSnd (squarePair a s)).unique
    (Classical.choose!_spec (exists_unique_squarePairSnd (squarePair a s))) (Or.inl ⟨a, rfl⟩)

lemma squarePairFst_eq_iff {x y : V} :
    y = squarePairFst x ↔
      (∃ s ≤ x, x = squarePair y s) ∨ ((∀ b ≤ x, ∀ s ≤ x, x ≠ squarePair b s) ∧ y = 0) := by
  have e : (∃ s ≤ x, x = squarePair y s) ∨ ((∀ b ≤ x, ∀ s ≤ x, x ≠ squarePair b s) ∧ y = 0) ↔
      (∃ s, x = squarePair y s) ∨ ((∀ b s, x ≠ squarePair b s) ∧ y = 0) := by
    constructor
    · rintro (⟨s, -, hs⟩ | ⟨hn, rfl⟩)
      · exact Or.inl ⟨s, hs⟩
      · refine Or.inr ⟨fun b s hbs ↦ ?_, rfl⟩
        exact hn b (hbs ▸ le_squarePair_left b s) s (hbs ▸ le_squarePair_right b s) hbs
    · rintro (⟨s, rfl⟩ | ⟨hn, rfl⟩)
      · exact Or.inl ⟨s, le_squarePair_right y s, rfl⟩
      · exact Or.inr ⟨fun b _ s _ ↦ hn b s, rfl⟩
  rw [e]
  exact Classical.choose!_eq_iff_right (exists_unique_squarePairFst x)

lemma squarePairSnd_eq_iff {x y : V} :
    y = squarePairSnd x ↔
      (∃ a ≤ x, x = squarePair a y) ∨ ((∀ b ≤ x, ∀ t ≤ x, x ≠ squarePair b t) ∧ y = 0) := by
  have e : (∃ a ≤ x, x = squarePair a y) ∨ ((∀ b ≤ x, ∀ t ≤ x, x ≠ squarePair b t) ∧ y = 0) ↔
      (∃ a, x = squarePair a y) ∨ ((∀ b t, x ≠ squarePair b t) ∧ y = 0) := by
    constructor
    · rintro (⟨a, -, ha⟩ | ⟨hn, rfl⟩)
      · exact Or.inl ⟨a, ha⟩
      · refine Or.inr ⟨fun b t hbt ↦ ?_, rfl⟩
        exact hn b (hbt ▸ le_squarePair_left b t) t (hbt ▸ le_squarePair_right b t) hbt
    · rintro (⟨a, rfl⟩ | ⟨hn, rfl⟩)
      · exact Or.inl ⟨a, le_squarePair_left a y, rfl⟩
      · exact Or.inr ⟨fun b _ t _ ↦ hn b t, rfl⟩
  rw [e]
  exact Classical.choose!_eq_iff_right (exists_unique_squarePairSnd x)

def squarePairFstGraph : 𝚺ᴬ₀.Semisentence 2 := .mkSigma
  “y x. (∃ s <⁺ x, x = (y + s) * (y + s) + y + 1) ∨
    ((∀ b <⁺ x, ∀ s <⁺ x, x ≠ (b + s) * (b + s) + b + 1) ∧ y = 0)”

def squarePairSndGraph : 𝚺ᴬ₀.Semisentence 2 := .mkSigma
  “y x. (∃ a <⁺ x, x = (a + y) * (a + y) + a + 1) ∨
    ((∀ b <⁺ x, ∀ t <⁺ x, x ≠ (b + t) * (b + t) + b + 1) ∧ y = 0)”

instance squarePairFst.defined : 𝚺ᴬ₀-Function₁ (squarePairFst : V → V) via squarePairFstGraph :=
  .mk fun v ↦ by simp [squarePairFstGraph, squarePairFst_eq_iff, squarePair]

instance squarePairSnd.defined : 𝚺ᴬ₀-Function₁ (squarePairSnd : V → V) via squarePairSndGraph :=
  .mk fun v ↦ by simp [squarePairSndGraph, squarePairSnd_eq_iff, squarePair]

instance squarePairFst.definable : 𝚺ᴬ₀-Function₁ (squarePairFst : V → V) :=
  squarePairFst.defined.to_definable

instance squarePairSnd.definable : 𝚺ᴬ₀-Function₁ (squarePairSnd : V → V) :=
  squarePairSnd.defined.to_definable

instance squarePairFst.definable' {Γ : SigmaPiDelta} {m : ℕ} :
    Γᴬ_[m]-Function₁ (squarePairFst : V → V) := squarePairFst.definable.of_zero

instance squarePairSnd.definable' {Γ : SigmaPiDelta} {m : ℕ} :
    Γᴬ_[m]-Function₁ (squarePairSnd : V → V) := squarePairSnd.definable.of_zero

end projections

section entries

namespace SquarePairTail

def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y s. y = s”
  succ := .mkSigma “y ih k s. !squarePairSndGraph y ih”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ squarePairSnd ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end SquarePairTail

/-- The list `s` with its first `i` entries removed. -/
noncomputable def squarePairTail (s i : V) : V := SquarePairTail.construction.result ![s] i

/-- The `i`-th entry of the list `s`. -/
noncomputable def squarePairNth (s i : V) : V := squarePairFst (squarePairTail s i)

@[simp] lemma squarePairTail_zero (s : V) : squarePairTail s 0 = s := by
  simp [squarePairTail, SquarePairTail.construction]

lemma squarePairTail_succ (s i : V) :
    squarePairTail s (i + 1) = squarePairSnd (squarePairTail s i) := by
  simp [squarePairTail, SquarePairTail.construction]

def squarePairTailGraph : 𝚺ᴬ₁.Semisentence 3 :=
  SquarePairTail.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

def squarePairNthGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y s i. ∃ t, !squarePairTailGraph t s i ∧ !squarePairFstGraph y t”

instance squarePairTail.defined : 𝚺ᴬ₁-Function₂ (squarePairTail : V → V → V) via
    squarePairTailGraph := .mk fun v ↦ by
  simp [SquarePairTail.construction.result_defined_iff, squarePairTailGraph]; rfl

instance squarePairTail.definable : 𝚺ᴬ₁-Function₂ (squarePairTail : V → V → V) :=
  squarePairTail.defined.to_definable

instance squarePairNth.defined : 𝚺ᴬ₁-Function₂ (squarePairNth : V → V → V) via
    squarePairNthGraph := .mk fun v ↦ by
  simp [squarePairNthGraph, squarePairNth]

instance squarePairNth.definable : 𝚺ᴬ₁-Function₂ (squarePairNth : V → V → V) :=
  squarePairNth.defined.to_definable

lemma squarePairTail_succ' (s i : V) :
    squarePairTail s (i + 1) = squarePairTail (squarePairSnd s) i := by
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using squarePairTail_succ s 0
  case succ i ih => rw [squarePairTail_succ, ih, squarePairTail_succ]

@[simp] lemma squarePairNth_squarePair_zero (a s : V) : squarePairNth (squarePair a s) 0 = a := by
  simp [squarePairNth]

@[simp] lemma squarePairNth_squarePair_succ (a s i : V) :
    squarePairNth (squarePair a s) (i + 1) = squarePairNth s i := by
  simp [squarePairNth, squarePairTail_succ']

end entries

end FFL.FirstOrder.Arithmetic
