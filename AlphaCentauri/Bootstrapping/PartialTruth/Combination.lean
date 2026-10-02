module

public import AlphaCentauri.Bootstrapping.PartialTruth.Assignment

/-!
# Truth for combinations of prenex formulas

For standard `k` and `D`, `IsReadable k D` is the $\Delta_1$ class of internal formulas consisting
of the prenex formulas with a $\Delta_0$ matrix and at most `k` quantifiers, their combinations by
`^⋏` and `^⋎` of depth at most `D`, the universal quantifications of such combinations, and the
prenex $\Pi_{k+1}$ formulas with a $\Delta_0$ matrix. `ReadableSatisfaction k D p f` says that
`p` belongs to this class and is true when its free variables take the values `f`; it is
$\Pi_{k+1}$, satisfies the Tarski conditions, and does not depend on how a formula is read when it
falls into several of the clauses above.

## References

- [HP98, Definition I.1.74, Theorem I.1.75]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Arithmetic (numeral)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The class -/

section isReadable

variable (k : ℕ)

/-- The prenex classes read directly: at most `k` quantifiers of either polarity, or `k + 1`
quantifiers beginning with a universal one. -/
def IsAtomLevel (Γ : Polarity) (s : ℕ) : Prop := s ≤ k ∨ Γ = 𝚷 ∧ s = k + 1

/-- `p` is a prenex formula with a $\Delta_0$ matrix and at most `k` quantifiers. -/
def IsPrenexAtMost (p : V) : Prop := ∃ Γ, ∃ s ≤ k, IsPrenexHierarchy Γ s p

/-- `p` is a prenex formula with a $\Delta_0$ matrix whose class is read directly. -/
def IsPrenexAtom (p : V) : Prop := ∃ Γ s, IsAtomLevel k Γ s ∧ IsPrenexHierarchy Γ s p

/-- `p` is built from formulas of `IsPrenexAtMost k` by `^⋏` and `^⋎`, nested at most `D` deep. -/
def IsCombination : ℕ → V → Prop
  | 0 => IsPrenexAtMost k
  | D + 1 => fun p ↦ IsCombination D p ∨
      (∃ p₁ < p, ∃ p₂ < p, p = p₁ ^⋏ p₂ ∧ IsCombination D p₁ ∧ IsCombination D p₂) ∨
      (∃ p₁ < p, ∃ p₂ < p, p = p₁ ^⋎ p₂ ∧ IsCombination D p₁ ∧ IsCombination D p₂)

/-- The class of formulas read by `ReadableSatisfaction k D`. -/
def IsReadable (D : ℕ) (p : V) : Prop :=
  IsCombination k D p ∨ (∃ q < p, p = ^∀ q ∧ IsCombination k D q) ∨
    IsPrenexHierarchy 𝚷 (k + 1) p

end isReadable

section structure_

variable {k D : ℕ} {Γ : Polarity} {s : ℕ} {p q θ : V}

lemma IsAtomLevel.of_le (h : s ≤ k) : IsAtomLevel k Γ s := Or.inl h

lemma IsPrenexAtMost.isPrenexAtom (h : IsPrenexAtMost k p) : IsPrenexAtom k p := by
  obtain ⟨Γ, s, hs, h⟩ := h
  exact ⟨Γ, s, .of_le hs, h⟩

lemma IsPrenexAtMost.of_isBounded (h : IsBounded p) : IsPrenexAtMost k p := ⟨𝚺, 0, by simp, h⟩

lemma isPrenexAtom_iff :
    IsPrenexAtom k p ↔ IsPrenexAtMost k p ∨ IsPrenexHierarchy 𝚷 (k + 1) p := by
  constructor
  · rintro ⟨Γ, s, hs | ⟨rfl, rfl⟩, h⟩
    · exact Or.inl ⟨Γ, s, hs, h⟩
    · exact Or.inr h
  · rintro (h | h)
    · exact h.isPrenexAtom
    · exact ⟨𝚷, k + 1, Or.inr ⟨rfl, rfl⟩, h⟩

lemma IsPrenexAtom.exists_qqToPrenex (h : IsPrenexAtom k p) :
    ∃ Γ s θ, IsAtomLevel k Γ s ∧ p = qqToPrenex Γ s θ ∧ IsBounded θ := by
  obtain ⟨Γ, s, hs, h⟩ := h
  obtain ⟨θ, rfl, hθ⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp h
  exact ⟨Γ, s, θ, hs, rfl, hθ⟩

lemma IsPrenexAtom.of_qqToPrenex (hs : IsAtomLevel k Γ s) (hθ : IsBounded θ) :
    IsPrenexAtom k (qqToPrenex Γ s θ) :=
  ⟨Γ, s, hs, isPrenexHierarchy_iff_exists_qqToPrenex.mpr ⟨θ, rfl, hθ⟩⟩

lemma IsPrenexAtMost.of_qqToPrenex (hs : s ≤ k) (hθ : IsBounded θ) :
    IsPrenexAtMost k (qqToPrenex Γ s θ) :=
  ⟨Γ, s, hs, isPrenexHierarchy_iff_exists_qqToPrenex.mpr ⟨θ, rfl, hθ⟩⟩

lemma qqToPrenex_eq_and (h : qqToPrenex Γ s θ = p ^⋏ q) : s = 0 := by
  rcases s with _ | s
  · rfl
  · cases Γ <;> simp [qqExs, qqAll, qqAnd] at h

lemma qqToPrenex_eq_or (h : qqToPrenex Γ s θ = p ^⋎ q) : s = 0 := by
  rcases s with _ | s
  · rfl
  · cases Γ <;> simp [qqExs, qqAll, qqOr] at h

lemma IsPrenexAtom.isBounded_of_and (h : IsPrenexAtom k (p ^⋏ q)) : IsBounded (p ^⋏ q) := by
  obtain ⟨Γ, s, θ, -, he, hθ⟩ := h.exists_qqToPrenex
  obtain rfl := qqToPrenex_eq_and he.symm
  simpa [he] using hθ

lemma IsPrenexAtom.isBounded_of_or (h : IsPrenexAtom k (p ^⋎ q)) : IsBounded (p ^⋎ q) := by
  obtain ⟨Γ, s, θ, -, he, hθ⟩ := h.exists_qqToPrenex
  obtain rfl := qqToPrenex_eq_or he.symm
  simpa [he] using hθ

/-- A prenex atom beginning with `^∀` is the universal quantification of a prenex formula with at
most `k` quantifiers. -/
lemma IsPrenexAtom.exists_of_all (h : IsPrenexAtom k (^∀ p)) :
    ∃ s θ, s ≤ k ∧ p = qqToPrenex 𝚺 s θ ∧ IsBounded θ := by
  obtain ⟨Γ, s, θ, hs, he, hθ⟩ := h.exists_qqToPrenex
  rcases s with _ | s
  · have hb : IsBounded (^∀ p) := by
      rw [he]
      simpa using hθ
    obtain ⟨_, q, -, hq, rfl⟩ := IsBounded.of_all hb
    exact ⟨0, _, by simp, rfl, IsBounded.or_iff.mpr ⟨by simp [Arithmetic.qqNLT], hq⟩⟩
  · cases Γ
    · simp [qqExs, qqAll] at he
    · change ^∀ p = ^∀ (qqToPrenex 𝚺 s θ) at he
      exact ⟨s, θ, by rcases hs with hs | ⟨-, hs⟩ <;> omega, (qqAll_inj _ _).mp he, hθ⟩

lemma IsPrenexAtom.exists_of_exs (h : IsPrenexAtom k (^∃ p)) :
    ∃ s θ, s ≤ k ∧ p = qqToPrenex 𝚷 s θ ∧ IsBounded θ := by
  obtain ⟨Γ, s, θ, hs, he, hθ⟩ := h.exists_qqToPrenex
  rcases s with _ | s
  · have hb : IsBounded (^∃ p) := by
      rw [he]
      simpa using hθ
    obtain ⟨_, q, -, hq, rfl⟩ := IsBounded.of_ex hb
    exact ⟨0, _, by simp, rfl, IsBounded.and_iff.mpr ⟨by simp [Arithmetic.qqLT], hq⟩⟩
  · rcases Γ
    · change ^∃ p = ^∃ (qqToPrenex 𝚷 s θ) at he
      exact ⟨s, θ, by rcases hs with hs | ⟨h, -⟩ <;> simp_all; omega, (qqExs_inj _ _).mp he, hθ⟩
    · simp [qqExs, qqAll] at he

lemma IsPrenexAtMost.of_all (h : IsPrenexAtom k (^∀ p)) : IsPrenexAtMost k p := by
  obtain ⟨s, θ, hs, rfl, hθ⟩ := h.exists_of_all
  exact .of_qqToPrenex hs hθ

lemma IsPrenexAtMost.of_exs (h : IsPrenexAtom k (^∃ p)) : IsPrenexAtMost k p := by
  obtain ⟨s, θ, hs, rfl, hθ⟩ := h.exists_of_exs
  exact .of_qqToPrenex hs hθ

lemma IsPrenexAtMost.of_and (h : IsPrenexAtom k (p ^⋏ q)) :
    IsPrenexAtMost k p ∧ IsPrenexAtMost k q :=
  have h' := IsBounded.and_iff.mp h.isBounded_of_and
  ⟨.of_isBounded h'.1, .of_isBounded h'.2⟩

lemma IsPrenexAtMost.of_or (h : IsPrenexAtom k (p ^⋎ q)) :
    IsPrenexAtMost k p ∧ IsPrenexAtMost k q :=
  have h' := IsBounded.or_iff.mp h.isBounded_of_or
  ⟨.of_isBounded h'.1, .of_isBounded h'.2⟩

lemma IsCombination.succ (h : IsCombination k D p) : IsCombination k (D + 1) p := Or.inl h

lemma IsCombination.mono {D' : ℕ} (h : IsCombination k D p) (hD : D ≤ D') :
    IsCombination k D' p := by
  induction hD with
  | refl => exact h
  | step _ ih => exact ih.succ

lemma IsCombination.of_isPrenexAtMost (h : IsPrenexAtMost k p) : IsCombination k D p :=
  IsCombination.mono (D := 0) h (Nat.zero_le D)

lemma IsCombination.and (hp : IsCombination k D p) (hq : IsCombination k D q) :
    IsCombination k (D + 1) (p ^⋏ q) :=
  Or.inr <| Or.inl ⟨p, by simp, q, by simp, rfl, hp, hq⟩

lemma IsCombination.or (hp : IsCombination k D p) (hq : IsCombination k D q) :
    IsCombination k (D + 1) (p ^⋎ q) :=
  Or.inr <| Or.inr ⟨p, by simp, q, by simp, rfl, hp, hq⟩

/-- A combination is a prenex formula with at most `k` quantifiers, or a conjunction or a
disjunction of combinations of smaller depth. -/
lemma IsCombination.cases (h : IsCombination k D p) :
    IsPrenexAtMost k p ∨ ∃ D', D = D' + 1 ∧
      ((∃ p₁ p₂, p = p₁ ^⋏ p₂ ∧ IsCombination k D' p₁ ∧ IsCombination k D' p₂) ∨
        (∃ p₁ p₂, p = p₁ ^⋎ p₂ ∧ IsCombination k D' p₁ ∧ IsCombination k D' p₂)) := by
  induction D generalizing p with
  | zero => exact Or.inl h
  | succ D ih =>
    rcases h with h | ⟨p₁, -, p₂, -, rfl, h₁, h₂⟩ | ⟨p₁, -, p₂, -, rfl, h₁, h₂⟩
    · rcases ih h with h | ⟨D', rfl, ⟨p₁, p₂, rfl, h₁, h₂⟩ | ⟨p₁, p₂, rfl, h₁, h₂⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨D' + 1, rfl, Or.inl ⟨p₁, p₂, rfl, h₁.succ, h₂.succ⟩⟩
      · exact Or.inr ⟨D' + 1, rfl, Or.inr ⟨p₁, p₂, rfl, h₁.succ, h₂.succ⟩⟩
    · exact Or.inr ⟨D, rfl, Or.inl ⟨p₁, p₂, rfl, h₁, h₂⟩⟩
    · exact Or.inr ⟨D, rfl, Or.inr ⟨p₁, p₂, rfl, h₁, h₂⟩⟩

lemma IsCombination.of_and (h : IsCombination k D (p ^⋏ q)) :
    IsCombination k D p ∧ IsCombination k D q := by
  rcases h.cases with h | ⟨D, rfl, ⟨p₁, p₂, he, h₁, h₂⟩ | ⟨p₁, p₂, he, -, -⟩⟩
  · exact ⟨.of_isPrenexAtMost (IsPrenexAtMost.of_and h.isPrenexAtom).1,
      .of_isPrenexAtMost (IsPrenexAtMost.of_and h.isPrenexAtom).2⟩
  · obtain ⟨rfl, rfl⟩ := (qqAnd_inj _ _ _ _).mp he
    exact ⟨h₁.succ, h₂.succ⟩
  · simp [qqAnd, qqOr] at he

lemma IsCombination.of_or (h : IsCombination k D (p ^⋎ q)) :
    IsCombination k D p ∧ IsCombination k D q := by
  rcases h.cases with h | ⟨D, rfl, ⟨p₁, p₂, he, -, -⟩ | ⟨p₁, p₂, he, h₁, h₂⟩⟩
  · exact ⟨.of_isPrenexAtMost (IsPrenexAtMost.of_or h.isPrenexAtom).1,
      .of_isPrenexAtMost (IsPrenexAtMost.of_or h.isPrenexAtom).2⟩
  · simp [qqAnd, qqOr] at he
  · obtain ⟨rfl, rfl⟩ := (qqOr_inj _ _ _ _).mp he
    exact ⟨h₁.succ, h₂.succ⟩

lemma IsCombination.isPrenexAtMost_of_all (h : IsCombination k D (^∀ p)) :
    IsPrenexAtMost k (^∀ p) := by
  rcases h.cases with h | ⟨D, rfl, ⟨p₁, p₂, he, -, -⟩ | ⟨p₁, p₂, he, -, -⟩⟩
  · exact h
  · simp [qqAll, qqAnd] at he
  · simp [qqAll, qqOr] at he

lemma IsCombination.isPrenexAtMost_of_exs (h : IsCombination k D (^∃ p)) :
    IsPrenexAtMost k (^∃ p) := by
  rcases h.cases with h | ⟨D, rfl, ⟨p₁, p₂, he, -, -⟩ | ⟨p₁, p₂, he, -, -⟩⟩
  · exact h
  · simp [qqExs, qqAnd] at he
  · simp [qqExs, qqOr] at he

/-- Combinations are closed under an operation that preserves prenex formulas with at most `k`
quantifiers and sends conjunctions and disjunctions to conjunctions or disjunctions of the images
of their components. -/
lemma IsCombination.map {P : V → Prop} {F : V → V}
    (hatom : ∀ p, P p → IsPrenexAtMost k p → IsPrenexAtMost k (F p))
    (hand : ∀ p q, P (p ^⋏ q) → P p ∧ P q ∧
      (F (p ^⋏ q) = F p ^⋏ F q ∨ F (p ^⋏ q) = F p ^⋎ F q))
    (hor : ∀ p q, P (p ^⋎ q) → P p ∧ P q ∧
      (F (p ^⋎ q) = F p ^⋏ F q ∨ F (p ^⋎ q) = F p ^⋎ F q))
    (hp : P p) (h : IsCombination k D p) : IsCombination k D (F p) := by
  induction D generalizing p with
  | zero => exact hatom p hp h
  | succ D ih =>
    rcases h with h | ⟨p₁, -, p₂, -, rfl, h₁, h₂⟩ | ⟨p₁, -, p₂, -, rfl, h₁, h₂⟩
    · exact (ih hp h).succ
    · obtain ⟨hp₁, hp₂, he | he⟩ := hand p₁ p₂ hp <;> rw [he]
      · exact (ih hp₁ h₁).and (ih hp₂ h₂)
      · exact (ih hp₁ h₁).or (ih hp₂ h₂)
    · obtain ⟨hp₁, hp₂, he | he⟩ := hor p₁ p₂ hp <;> rw [he]
      · exact (ih hp₁ h₁).and (ih hp₂ h₂)
      · exact (ih hp₁ h₁).or (ih hp₂ h₂)

lemma IsReadable.of_isCombination (h : IsCombination k D p) : IsReadable k D p := Or.inl h

lemma IsReadable.of_isPrenexAtom (h : IsPrenexAtom k p) : IsReadable k D p :=
  (isPrenexAtom_iff.mp h).elim (fun h ↦ .of_isCombination (.of_isPrenexAtMost h))
    fun h ↦ Or.inr (Or.inr h)

lemma IsReadable.all (h : IsCombination k D p) : IsReadable k D (^∀ p) :=
  Or.inr <| Or.inl ⟨p, by simp, rfl, h⟩

@[simp] lemma IsReadable.verum : IsReadable k D (^⊤ : V) :=
  .of_isCombination <| .of_isPrenexAtMost <| .of_isBounded <| by simp

lemma IsReadable.isCombination_of_and (h : IsReadable k D (p ^⋏ q)) :
    IsCombination k D (p ^⋏ q) := by
  rcases h with h | ⟨_, _, he, _⟩ | h
  · exact h
  · simp [qqAll, qqAnd] at he
  · obtain ⟨θ, he, -⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp h
    exact absurd (qqToPrenex_eq_and he.symm) (by simp)

lemma IsReadable.isCombination_of_or (h : IsReadable k D (p ^⋎ q)) :
    IsCombination k D (p ^⋎ q) := by
  rcases h with h | ⟨_, _, he, _⟩ | h
  · exact h
  · simp [qqAll, qqOr] at he
  · obtain ⟨θ, he, -⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp h
    exact absurd (qqToPrenex_eq_or he.symm) (by simp)

lemma IsReadable.of_and (h : IsReadable k D (p ^⋏ q)) : IsReadable k D p ∧ IsReadable k D q :=
  have h' := h.isCombination_of_and.of_and
  ⟨.of_isCombination h'.1, .of_isCombination h'.2⟩

lemma IsReadable.of_or (h : IsReadable k D (p ^⋎ q)) : IsReadable k D p ∧ IsReadable k D q :=
  have h' := h.isCombination_of_or.of_or
  ⟨.of_isCombination h'.1, .of_isCombination h'.2⟩

lemma IsReadable.isCombination_of_all (h : IsReadable k D (^∀ p)) : IsCombination k D p := by
  rcases h with h | ⟨q, -, he, hq⟩ | h
  · exact .of_isPrenexAtMost (.of_all h.isPrenexAtMost_of_all.isPrenexAtom)
  · obtain rfl := (qqAll_inj _ _).mp he
    exact hq
  · exact .of_isPrenexAtMost (.of_all (isPrenexAtom_iff.mpr (Or.inr h)))

lemma IsReadable.isPrenexAtom_of_exs (h : IsReadable k D (^∃ p)) : IsPrenexAtom k (^∃ p) := by
  rcases h with h | ⟨_, _, he, _⟩ | h
  · exact h.isPrenexAtMost_of_exs.isPrenexAtom
  · simp [qqAll, qqExs] at he
  · obtain ⟨θ, he, -⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp h
    change ^∃ p = ^∀ (qqToPrenex 𝚺 k θ) at he
    simp [qqAll, qqExs] at he

end structure_

/-! ### Closure under syntactic operations -/

section closure

variable {k D : ℕ} {p : V}

/-- `IsReadable k D` is closed under an operation that preserves the prenex classes and commutes
with `^⋏`, `^⋎` and `^∀`. -/
lemma IsReadable.map {P : V → Prop} {F : V → V}
    (hprenex : ∀ Γ s p, P p → IsPrenexHierarchy Γ s p → IsPrenexHierarchy Γ s (F p))
    (hand : ∀ p q, P (p ^⋏ q) → P p ∧ P q ∧ F (p ^⋏ q) = F p ^⋏ F q)
    (hor : ∀ p q, P (p ^⋎ q) → P p ∧ P q ∧ F (p ^⋎ q) = F p ^⋎ F q)
    (hall : ∀ p, P (^∀ p) → P p ∧ F (^∀ p) = ^∀ (F p))
    (hp : P p) (h : IsReadable k D p) : IsReadable k D (F p) := by
  have hatom : ∀ p, P p → IsPrenexAtMost k p → IsPrenexAtMost k (F p) := by
    rintro p hp ⟨Γ, s, hs, h⟩
    exact ⟨Γ, s, hs, hprenex Γ s p hp h⟩
  have hand' : ∀ p q, P (p ^⋏ q) → P p ∧ P q ∧
      (F (p ^⋏ q) = F p ^⋏ F q ∨ F (p ^⋏ q) = F p ^⋎ F q) := by
    intro p q h
    obtain ⟨hp, hq, he⟩ := hand p q h
    exact ⟨hp, hq, Or.inl he⟩
  have hor' : ∀ p q, P (p ^⋎ q) → P p ∧ P q ∧
      (F (p ^⋎ q) = F p ^⋏ F q ∨ F (p ^⋎ q) = F p ^⋎ F q) := by
    intro p q h
    obtain ⟨hp, hq, he⟩ := hor p q h
    exact ⟨hp, hq, Or.inr he⟩
  rcases h with h | ⟨q, -, rfl, hq⟩ | h
  · exact .of_isCombination (IsCombination.map hatom hand' hor' hp h)
  · obtain ⟨hq', he⟩ := hall q hp
    rw [he]
    exact .all (IsCombination.map hatom hand' hor' hq' hq)
  · exact Or.inr <| Or.inr <| hprenex 𝚷 (k + 1) p hp h

lemma IsCombination.neg (hp : IsUFormula ℒₒᵣ p) (h : IsCombination k D p) :
    IsCombination k D (neg ℒₒᵣ p) := by
  refine IsCombination.map (P := IsUFormula ℒₒᵣ) ?_ ?_ ?_ hp h
  · rintro p hp ⟨Γ, s, hs, h⟩
    exact ⟨Γ.alt, s, hs, h.neg hp⟩
  · intro p q h
    obtain ⟨hp, hq⟩ := IsUFormula.and.mp h
    exact ⟨hp, hq, Or.inr (neg_and hp hq)⟩
  · intro p q h
    obtain ⟨hp, hq⟩ := IsUFormula.or.mp h
    exact ⟨hp, hq, Or.inl (neg_or hp hq)⟩

lemma IsCombination.subst {n m w : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (h : IsCombination k D p) :
    IsCombination k D (subst ℒₒᵣ w p) := by
  refine IsCombination.map (P := IsSemiformula ℒₒᵣ n) ?_ ?_ ?_ hp h
  · rintro p hp ⟨Γ, s, hs, h⟩
    exact ⟨Γ, s, hs, h.subst hw hp⟩
  · intro p q h
    obtain ⟨hp, hq⟩ := IsSemiformula.and.mp h
    exact ⟨hp, hq, Or.inl (substs_and hp.isUFormula hq.isUFormula)⟩
  · intro p q h
    obtain ⟨hp, hq⟩ := IsSemiformula.or.mp h
    exact ⟨hp, hq, Or.inr (substs_or hp.isUFormula hq.isUFormula)⟩

/-- `IsReadable k D` is closed under an operation on formulas that preserves the prenex classes
and commutes with the connectives and quantifiers. -/
lemma IsReadable.map_uformula {F : V → V}
    (hprenex : ∀ Γ s p, IsUFormula ℒₒᵣ p → IsPrenexHierarchy Γ s p → IsPrenexHierarchy Γ s (F p))
    (hand : ∀ p q, IsUFormula ℒₒᵣ p → IsUFormula ℒₒᵣ q → F (p ^⋏ q) = F p ^⋏ F q)
    (hor : ∀ p q, IsUFormula ℒₒᵣ p → IsUFormula ℒₒᵣ q → F (p ^⋎ q) = F p ^⋎ F q)
    (hall : ∀ p, IsUFormula ℒₒᵣ p → F (^∀ p) = ^∀ (F p))
    (hp : IsUFormula ℒₒᵣ p) (h : IsReadable k D p) : IsReadable k D (F p) := by
  refine IsReadable.map (P := IsUFormula ℒₒᵣ) hprenex ?_ ?_ ?_ hp h
  · intro p q h
    obtain ⟨hp, hq⟩ := IsUFormula.and.mp h
    exact ⟨hp, hq, hand p q hp hq⟩
  · intro p q h
    obtain ⟨hp, hq⟩ := IsUFormula.or.mp h
    exact ⟨hp, hq, hor p q hp hq⟩
  · intro p h
    have hp : IsUFormula ℒₒᵣ p := IsUFormula.all.mp h
    exact ⟨hp, hall p hp⟩

lemma IsReadable.shift (hp : IsUFormula ℒₒᵣ p) (h : IsReadable k D p) :
    IsReadable k D (shift ℒₒᵣ p) :=
  IsReadable.map_uformula (fun _ _ _ hp h ↦ h.shift hp) (fun _ _ ↦ shift_and)
    (fun _ _ ↦ shift_or) (fun _ ↦ shift_all) hp h

lemma IsReadable.fvUnshift (hp : IsUFormula ℒₒᵣ p) (h : IsReadable k D p) :
    IsReadable k D (fvUnshift p) :=
  IsReadable.map_uformula (fun _ _ _ hp h ↦ h.fvUnshift hp) (fun _ _ ↦ fvUnshift_and)
    (fun _ _ ↦ fvUnshift_or) (fun _ ↦ fvUnshift_all) hp h

@[simp] lemma IsReadable.shift_iff (hp : IsUFormula ℒₒᵣ p) :
    IsReadable k D (Bootstrapping.shift ℒₒᵣ p) ↔ IsReadable k D p :=
  ⟨fun h ↦ by simpa [fvUnshift_shift hp] using h.fvUnshift hp.shift, IsReadable.shift hp⟩

lemma IsReadable.fvAssign {f : V} (hp : IsUFormula ℒₒᵣ p) (h : IsReadable k D p) :
    IsReadable k D (fvAssign f p) :=
  IsReadable.map_uformula (fun _ _ _ hp h ↦ h.fvAssign hp) (fun _ _ ↦ fvAssign_and)
    (fun _ _ ↦ fvAssign_or) (fun _ ↦ fvAssign_all) hp h

lemma IsReadable.fvSubst {w : V} (hw : IsSemitermVec ℒₒᵣ (len w) 0 w)
    (hp : IsUFormula ℒₒᵣ p) (h : IsReadable k D p) : IsReadable k D (fvSubst ℒₒᵣ w p) :=
  IsReadable.map_uformula (fun _ _ _ hp h ↦ h.fvSubst hw hp) (fun _ _ ↦ fvSubst_and)
    (fun _ _ ↦ fvSubst_or) (fun _ ↦ fvSubst_all) hp h

lemma IsReadable.substs1_of_all {m t : V} (ht : IsSemiterm ℒₒᵣ m t)
    (hp : IsSemiformula ℒₒᵣ 1 p) (h : IsReadable k D (^∀ p)) :
    IsReadable k D (substs1 ℒₒᵣ t p) :=
  .of_isCombination <| h.isCombination_of_all.subst (m := m) (by simp [ht]) hp

lemma IsReadable.substs1_of_exs {m t : V} (ht : IsSemiterm ℒₒᵣ m t)
    (hp : IsSemiformula ℒₒᵣ 1 p) (h : IsReadable k D (^∃ p)) :
    IsReadable k D (substs1 ℒₒᵣ t p) :=
  .of_isCombination <| (IsCombination.of_isPrenexAtMost (.of_exs h.isPrenexAtom_of_exs)).subst
    (m := m) (by simp [ht]) hp

lemma IsReadable.free (hp : IsSemiformula ℒₒᵣ 1 p) (h : IsReadable k D (^∀ p)) :
    IsReadable k D (free ℒₒᵣ p) := by
  have hs : IsReadable k D (^∀ (Bootstrapping.shift ℒₒᵣ p)) := by
    simpa [shift_all hp.isUFormula] using h.shift (by simpa using hp.isUFormula)
  exact hs.substs1_of_all (m := 0) (by simp) hp.shift

end closure

/-! ### Definability of the class -/

section definability

open FFL.FirstOrder.Bounding.HierarchySymbol

variable {k : ℕ}

lemma exists_polarity_iff {P : Polarity → Prop} : (∃ Γ, P Γ) ↔ P 𝚺 ∨ P 𝚷 :=
  ⟨fun ⟨Γ, h⟩ ↦ by rcases Γ <;> simp_all, fun h ↦ h.elim (⟨𝚺, ·⟩) (⟨𝚷, ·⟩)⟩

lemma forall_polarity_iff {P : Polarity → Prop} : (∀ Γ, P Γ) ↔ P 𝚺 ∧ P 𝚷 :=
  ⟨fun h ↦ ⟨h 𝚺, h 𝚷⟩, fun h Γ ↦ by rcases Γ <;> simp_all⟩

instance IsPrenexAtMost.definable : 𝚫ᴬ₁-Predicate (IsPrenexAtMost k : V → Prop) := by
  have h : ∀ Γ : Polarity,
      𝚫ᴬ₁-Predicate fun p : V ↦ ∃ s : Fin (k + 1), IsPrenexHierarchy Γ s p :=
    fun Γ ↦ Definable.fintype_exs fun s ↦ IsPrenexHierarchy.definable Γ s
  refine ((h 𝚺).or (h 𝚷)).of_iff fun v ↦ ?_
  simp only [IsPrenexAtMost, exists_polarity_iff]
  exact or_congr ⟨fun ⟨s, hs, h⟩ ↦ ⟨⟨s, by omega⟩, h⟩, fun ⟨s, h⟩ ↦ ⟨s, by omega, h⟩⟩
    ⟨fun ⟨s, hs, h⟩ ↦ ⟨⟨s, by omega⟩, h⟩, fun ⟨s, h⟩ ↦ ⟨s, by omega, h⟩⟩

instance IsPrenexAtom.definable : 𝚫ᴬ₁-Predicate (IsPrenexAtom k : V → Prop) :=
  (IsPrenexAtMost.definable.or (IsPrenexHierarchy.definable 𝚷 (k + 1))).of_iff
    fun _ ↦ isPrenexAtom_iff

instance IsCombination.definable : (D : ℕ) → 𝚫ᴬ₁-Predicate (IsCombination k D : V → Prop)
  | 0 => IsPrenexAtMost.definable
  | D + 1 => by
    have := IsCombination.definable D
    have : 𝚫ᴬ₁-Predicate fun p : V ↦ IsCombination k D p ∨
        (∃ p₁ < p, ∃ p₂ < p, p = p₁ ^⋏ p₂ ∧ IsCombination k D p₁ ∧ IsCombination k D p₂) ∨
        (∃ p₁ < p, ∃ p₂ < p, p = p₁ ^⋎ p₂ ∧ IsCombination k D p₁ ∧ IsCombination k D p₂) := by
      definability
    exact this.of_iff fun _ ↦ Iff.rfl

instance IsReadable.definable (D : ℕ) : 𝚫ᴬ₁-Predicate (IsReadable k D : V → Prop) := by
  have : 𝚫ᴬ₁-Predicate fun p : V ↦ IsCombination k D p ∨
      (∃ q < p, p = ^∀ q ∧ IsCombination k D q) ∨ IsPrenexHierarchy 𝚷 (k + 1) p := by
    definability
  exact this.of_iff fun _ ↦ Iff.rfl

end definability

end FFL.FirstOrder.Arithmetic.Bootstrapping
