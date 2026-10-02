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

- [HP98, Theorem I.1.75]
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
  apply IsCombination.map (P := IsUFormula ℒₒᵣ) (hp := hp) (h := h)
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
  apply IsCombination.map (P := IsSemiformula ℒₒᵣ n) (hp := hp) (h := h)
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
  apply IsReadable.map (P := IsUFormula ℒₒᵣ) hprenex (hp := hp) (h := h)
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
    IsReadable k D (Bootstrapping.shift ℒₒᵣ p) ↔ IsReadable k D p := by
  constructor
  · intro h
    simpa [fvUnshift_shift hp] using h.fvUnshift hp.shift
  · exact IsReadable.shift hp

lemma IsReadable.fvAssign {f : V} (hp : IsUFormula ℒₒᵣ p) (h : IsReadable k D p) :
    IsReadable k D (fvAssign f p) :=
  IsReadable.map_uformula (fun _ _ _ hp h ↦ h.fvAssign hp) (fun _ _ ↦ fvAssign_and)
    (fun _ _ ↦ fvAssign_or) (fun _ ↦ fvAssign_all) hp h

lemma IsReadable.fvSubst {w : V} (hw : IsSemitermVec ℒₒᵣ (len w) 0 w)
    (hp : IsUFormula ℒₒᵣ p) (h : IsReadable k D p) : IsReadable k D (fvSubst ℒₒᵣ w p) :=
  IsReadable.map_uformula (fun _ _ _ hp h ↦ h.fvSubst hw hp) (fun _ _ ↦ fvSubst_and)
    (fun _ _ ↦ fvSubst_or) (fun _ ↦ fvSubst_all) hp h

lemma IsReadable.subst {n m w : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (h : IsReadable k D p) : IsReadable k D (subst ℒₒᵣ w p) := by
  rcases h with h | ⟨q, -, rfl, hq⟩ | h
  · exact .of_isCombination (h.subst hw hp)
  · have hq' : IsSemiformula ℒₒᵣ (n + 1) q := by simpa using hp
    rw [substs_all hq'.isUFormula]
    exact .all (hq.subst hw.qVec hq')
  · exact Or.inr <| Or.inr <| h.subst hw hp

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

private lemma exists_polarity_iff {P : Polarity → Prop} : (∃ Γ, P Γ) ↔ P 𝚺 ∨ P 𝚷 := by
  constructor
  · rintro ⟨Γ, h⟩
    rcases Γ <;> simp_all
  · rintro (h | h)
    · exact ⟨𝚺, h⟩
    · exact ⟨𝚷, h⟩

instance IsPrenexAtMost.definable : 𝚫ᴬ₁-Predicate (IsPrenexAtMost k : V → Prop) := by
  have h (Γ : Polarity) :
      𝚫ᴬ₁-Predicate fun p : V ↦ ∃ s : Fin (k + 1), IsPrenexHierarchy Γ s p :=
    Definable.fintype_exs fun s ↦ IsPrenexHierarchy.definable Γ s
  have e (Γ : Polarity) (p : V) :
      (∃ s ≤ k, IsPrenexHierarchy Γ s p) ↔ ∃ s : Fin (k + 1), IsPrenexHierarchy Γ s p := by
    constructor
    · rintro ⟨s, hs, h⟩
      exact ⟨⟨s, by omega⟩, h⟩
    · rintro ⟨s, h⟩
      exact ⟨s, by omega, h⟩
  apply ((h 𝚺).or (h 𝚷)).of_iff
  intro v
  simp only [IsPrenexAtMost, exists_polarity_iff, e]

instance IsPrenexAtMost.definable' (Γ : SigmaPiDelta) (m : ℕ) :
    Γᴬ-[m + 1]-Predicate (IsPrenexAtMost k : V → Prop) :=
  IsPrenexAtMost.definable.of_deltaOne

instance IsPrenexAtom.definable : 𝚫ᴬ₁-Predicate (IsPrenexAtom k : V → Prop) :=
  (IsPrenexAtMost.definable.or (IsPrenexHierarchy.definable 𝚷 (k + 1))).of_iff
    fun _ ↦ isPrenexAtom_iff

instance IsPrenexAtom.definable' (Γ : SigmaPiDelta) (m : ℕ) :
    Γᴬ-[m + 1]-Predicate (IsPrenexAtom k : V → Prop) :=
  IsPrenexAtom.definable.of_deltaOne

instance IsCombination.definable : (D : ℕ) → 𝚫ᴬ₁-Predicate (IsCombination k D : V → Prop)
  | 0 => IsPrenexAtMost.definable
  | D + 1 => by
    have := IsCombination.definable D
    have : 𝚫ᴬ₁-Predicate fun p : V ↦ IsCombination k D p ∨
        (∃ p₁ < p, ∃ p₂ < p, p = p₁ ^⋏ p₂ ∧ IsCombination k D p₁ ∧ IsCombination k D p₂) ∨
        (∃ p₁ < p, ∃ p₂ < p, p = p₁ ^⋎ p₂ ∧ IsCombination k D p₁ ∧ IsCombination k D p₂) := by
      definability
    exact this.of_iff fun _ ↦ Iff.rfl

instance IsCombination.definable' (D : ℕ) (Γ : SigmaPiDelta) (m : ℕ) :
    Γᴬ-[m + 1]-Predicate (IsCombination k D : V → Prop) :=
  (IsCombination.definable D).of_deltaOne

instance IsReadable.definable (D : ℕ) : 𝚫ᴬ₁-Predicate (IsReadable k D : V → Prop) := by
  have : 𝚫ᴬ₁-Predicate fun p : V ↦ IsCombination k D p ∨
      (∃ q < p, p = ^∀ q ∧ IsCombination k D q) ∨ IsPrenexHierarchy 𝚷 (k + 1) p := by
    definability
  exact this.of_iff fun _ ↦ Iff.rfl

instance IsReadable.definable' (D : ℕ) (Γ : SigmaPiDelta) (m : ℕ) :
    Γᴬ-[m + 1]-Predicate (IsReadable k D : V → Prop) :=
  (IsReadable.definable D).of_deltaOne

end definability

/-! ## Truth -/

section truth

variable (k : ℕ)

/-- `q` is true when read as `qqToPrenex Γ s θ` with a $\Delta_0$ matrix `θ`. -/
def PrenexReading (Γ : Polarity) (s : ℕ) (q : V) : Prop :=
  ∀ θ ≤ q, q = qqToPrenex Γ s θ → IsBounded θ → HierarchicalSatisfaction Γ s θ 0

/-- `q` is true when read as a prenex formula of any class read directly. -/
def AtomReading (q : V) : Prop := ∀ Γ s, IsAtomLevel k Γ s → PrenexReading Γ s q

/-- The truth of a combination of depth at most `D`, computed by its truth table from the
prenex formulas it is built from. -/
def CombinationReading : ℕ → V → Prop
  | 0 => AtomReading k
  | D + 1 => fun q ↦ (IsPrenexAtom k q → AtomReading k q) ∧
      (¬IsPrenexAtom k q → ∀ q₁ < q, ∀ q₂ < q, q = q₁ ^⋏ q₂ →
        CombinationReading D q₁ ∧ CombinationReading D q₂) ∧
      (¬IsPrenexAtom k q → ∀ q₁ < q, ∀ q₂ < q, q = q₁ ^⋎ q₂ →
        CombinationReading D q₁ ∨ CombinationReading D q₂)

/-- `q` belongs to `IsReadable k D` and is true, its free variables being read as `0`. -/
def ReadableTruth (D : ℕ) (q : V) : Prop :=
  IsReadable k D q ∧ CombinationReading k D q ∧
    (¬IsPrenexAtom k q → ∀ χ < q, q = ^∀ χ →
      ∀ x, CombinationReading k D (substs1 ℒₒᵣ (numeral x) χ))

/-- `p`, with its free variables `^&i` valued by `f.[i]`, belongs to `IsReadable k D` and is
true. -/
def ReadableSatisfaction (D : ℕ) (p f : V) : Prop := ReadableTruth k D (fvAssign f p)

end truth

section reading

variable {k D : ℕ} {Γ : Polarity} {s : ℕ} {q θ : V}

lemma PrenexReading.iff (heq : q = qqToPrenex Γ s θ) (hθ : IsBounded θ) :
    PrenexReading Γ s q ↔ HierarchicalSatisfaction Γ s θ 0 := by
  subst heq
  constructor
  · intro h
    exact h θ le_qqToPrenex rfl hθ
  · intro h θ' _ he _
    obtain rfl := qqToPrenex_inj.mp he.symm
    exact h

lemma AtomReading.of_not_isPrenexAtom (ha : ¬IsPrenexAtom k q) : AtomReading k q := by
  intro Γ s hs θ _ he hθ
  exact absurd (he ▸ IsPrenexAtom.of_qqToPrenex hs hθ) ha

lemma AtomReading.iff (ha : IsPrenexAtom k q) (heq : q = qqToPrenex Γ s θ) (hθ : IsBounded θ)
    (hq : IsUFormula ℒₒᵣ q) : AtomReading k q ↔ HierarchicalSatisfaction Γ s θ 0 := by
  have hθ' : IsUFormula ℒₒᵣ θ := isUFormula_qqToPrenex.mp (heq ▸ hq)
  obtain ⟨Γ', s', θ', hs', heq', hθ''⟩ := ha.exists_qqToPrenex
  constructor
  · intro h
    exact (HierarchicalSatisfaction.iff_of_qqToPrenex_eq (heq'.symm.trans heq) hθ'' hθ
      (isUFormula_qqToPrenex.mp (heq' ▸ hq))).mp ((PrenexReading.iff heq' hθ'').mp (h Γ' s' hs'))
  · intro h Γ'' s'' _ θ'' _ he hb
    exact (HierarchicalSatisfaction.iff_of_qqToPrenex_eq (heq.symm.trans he) hθ hb hθ').mp h

lemma AtomReading.neg (ha : IsPrenexAtom k q) (hna : IsPrenexAtom k (neg ℒₒᵣ q))
    (hq : IsUFormula ℒₒᵣ q) : AtomReading k (neg ℒₒᵣ q) ↔ ¬AtomReading k q := by
  obtain ⟨Γ, s, θ, -, rfl, hθ⟩ := ha.exists_qqToPrenex
  have hθ' : IsUFormula ℒₒᵣ θ := isUFormula_qqToPrenex.mp hq
  rw [AtomReading.iff ha rfl hθ hq, AtomReading.iff hna (neg_qqToPrenex hθ') (hθ.neg hθ') hq.neg,
    HierarchicalSatisfaction.neg_iff hθ hθ']

/-- An instance of a prenex formula with at most `k` quantifiers by a closed term is read with the
value of the term. -/
lemma AtomReading.substs1_iff {t : V} (hs : s ≤ k) (hθ : IsBounded θ)
    (hχ : IsSemiformula ℒₒᵣ 1 (qqToPrenex Γ s θ)) (ht : IsSemiterm ℒₒᵣ 0 t) :
    IsPrenexAtom k (substs1 ℒₒᵣ t (qqToPrenex Γ s θ)) ∧
      (AtomReading k (substs1 ℒₒᵣ t (qqToPrenex Γ s θ)) ↔
        HierarchicalSatisfaction Γ s θ (termVal 0 t ∷ 0)) := by
  have hθs : IsSemiformula ℒₒᵣ (1 + s : V) θ := isSemiformula_qqToPrenex.mp hχ
  have hw : IsSemitermVec ℒₒᵣ 1 0 (?[t] : V) := by simp [ht]
  have he : substs1 ℒₒᵣ t (qqToPrenex Γ s θ) =
      qqToPrenex Γ s (subst ℒₒᵣ ((qVec ℒₒᵣ)^[s] ?[t]) θ) :=
    subst_qqToPrenex hθs.isUFormula
  have hb : IsBounded (subst ℒₒᵣ ((qVec ℒₒᵣ)^[s] ?[t]) θ) := hθ.subst (hw.iterate_qVec s) hθs
  have ha : IsPrenexAtom k (substs1 ℒₒᵣ t (qqToPrenex Γ s θ)) :=
    he ▸ IsPrenexAtom.of_qqToPrenex (.of_le hs) hb
  refine ⟨ha, ?_⟩
  rw [AtomReading.iff ha he hb (hχ.substs1 ht).isUFormula, HierarchicalSatisfaction.subst hw hθs hθ,
    termValVec_cons₁ ht.isUTerm]

lemma CombinationReading.iff_atomReading (ha : IsPrenexAtom k q) :
    CombinationReading k D q ↔ AtomReading k q := by
  cases D with
  | zero => rfl
  | succ D => simp [CombinationReading, ha]

lemma CombinationReading.of_not_isPrenexAtom_all {χ : V} (ha : ¬IsPrenexAtom k (^∀ χ)) :
    CombinationReading k D (^∀ χ) := by
  cases D with
  | zero => exact AtomReading.of_not_isPrenexAtom ha
  | succ D =>
    and_intros
    · intro h
      exact absurd h ha
    all_goals
      intro _ q₁ _ q₂ _ he
      simp [qqAll, qqAnd, qqOr] at he

lemma CombinationReading.and_iff {q₁ q₂ : V} (hq₁ : IsUFormula ℒₒᵣ q₁) (hq₂ : IsUFormula ℒₒᵣ q₂) :
    CombinationReading k (D + 1) (q₁ ^⋏ q₂) ↔
      CombinationReading k D q₁ ∧ CombinationReading k D q₂ := by
  by_cases ha : IsPrenexAtom k (q₁ ^⋏ q₂)
  · have hb := ha.isBounded_of_and
    obtain ⟨hb₁, hb₂⟩ := IsBounded.and_iff.mp hb
    rw [iff_atomReading ha, iff_atomReading (IsPrenexAtMost.of_isBounded hb₁).isPrenexAtom,
      iff_atomReading (IsPrenexAtMost.of_isBounded hb₂).isPrenexAtom,
      AtomReading.iff (Γ := 𝚺) (s := 0) (θ := q₁ ^⋏ q₂) ha rfl hb (by simp [hq₁, hq₂]),
      AtomReading.iff (Γ := 𝚺) (s := 0) (θ := q₁) (IsPrenexAtMost.of_isBounded hb₁).isPrenexAtom
        rfl hb₁ hq₁,
      AtomReading.iff (Γ := 𝚺) (s := 0) (θ := q₂) (IsPrenexAtMost.of_isBounded hb₂).isPrenexAtom
        rfl hb₂ hq₂]
    simp only [HierarchicalSatisfaction.zero_iff, BoundedSatisfaction.and_iff]
  · simp only [CombinationReading, ha, IsEmpty.forall_iff, not_false_eq_true, forall_const,
      true_and]
    constructor
    · rintro ⟨h, -⟩
      exact h q₁ (by simp) q₂ (by simp) rfl
    · intro h
      constructor
      · rintro q₁' - q₂' - he
        obtain ⟨rfl, rfl⟩ := (qqAnd_inj _ _ _ _).mp he
        exact h
      · rintro q₁' - q₂' - he
        simp [qqAnd, qqOr] at he

lemma CombinationReading.or_iff {q₁ q₂ : V} (hq₁ : IsUFormula ℒₒᵣ q₁) (hq₂ : IsUFormula ℒₒᵣ q₂) :
    CombinationReading k (D + 1) (q₁ ^⋎ q₂) ↔
      CombinationReading k D q₁ ∨ CombinationReading k D q₂ := by
  by_cases ha : IsPrenexAtom k (q₁ ^⋎ q₂)
  · have hb := ha.isBounded_of_or
    obtain ⟨hb₁, hb₂⟩ := IsBounded.or_iff.mp hb
    rw [iff_atomReading ha, iff_atomReading (IsPrenexAtMost.of_isBounded hb₁).isPrenexAtom,
      iff_atomReading (IsPrenexAtMost.of_isBounded hb₂).isPrenexAtom,
      AtomReading.iff (Γ := 𝚺) (s := 0) (θ := q₁ ^⋎ q₂) ha rfl hb (by simp [hq₁, hq₂]),
      AtomReading.iff (Γ := 𝚺) (s := 0) (θ := q₁) (IsPrenexAtMost.of_isBounded hb₁).isPrenexAtom
        rfl hb₁ hq₁,
      AtomReading.iff (Γ := 𝚺) (s := 0) (θ := q₂) (IsPrenexAtMost.of_isBounded hb₂).isPrenexAtom
        rfl hb₂ hq₂]
    simp only [HierarchicalSatisfaction.zero_iff, BoundedSatisfaction.or_iff hb₁ hq₁ hb₂ hq₂]
  · simp only [CombinationReading, ha, IsEmpty.forall_iff, not_false_eq_true, forall_const,
      true_and]
    constructor
    · rintro ⟨-, h⟩
      exact h q₁ (by simp) q₂ (by simp) rfl
    · intro h
      constructor
      · rintro q₁' - q₂' - he
        simp [qqAnd, qqOr] at he
      · rintro q₁' - q₂' - he
        obtain ⟨rfl, rfl⟩ := (qqOr_inj _ _ _ _).mp he
        exact h

lemma CombinationReading.succ_iff (h : IsCombination k D q) (hq : IsUFormula ℒₒᵣ q) :
    CombinationReading k (D + 1) q ↔ CombinationReading k D q := by
  induction D generalizing q with
  | zero => exact iff_atomReading (IsPrenexAtMost.isPrenexAtom h)
  | succ D ih =>
    rcases h.cases with h | ⟨D', hD, ⟨q₁, q₂, rfl, h₁, h₂⟩ | ⟨q₁, q₂, rfl, h₁, h₂⟩⟩
    · rw [iff_atomReading h.isPrenexAtom, iff_atomReading h.isPrenexAtom]
    · obtain rfl : D' = D := by omega
      obtain ⟨hq₁, hq₂⟩ := IsUFormula.and.mp hq
      rw [and_iff hq₁ hq₂, and_iff hq₁ hq₂, ih h₁ hq₁, ih h₂ hq₂]
    · obtain rfl : D' = D := by omega
      obtain ⟨hq₁, hq₂⟩ := IsUFormula.or.mp hq
      rw [or_iff hq₁ hq₂, or_iff hq₁ hq₂, ih h₁ hq₁, ih h₂ hq₂]

lemma CombinationReading.le_iff {D' : ℕ} (h : IsCombination k D q) (hq : IsUFormula ℒₒᵣ q)
    (hD : D ≤ D') : CombinationReading k D' q ↔ CombinationReading k D q := by
  induction hD with
  | refl => rfl
  | step hD ih => exact (succ_iff (h.mono hD) hq).trans ih

lemma CombinationReading.neg (h : IsCombination k D q) (hq : IsUFormula ℒₒᵣ q) :
    CombinationReading k D (neg ℒₒᵣ q) ↔ ¬CombinationReading k D q := by
  induction D generalizing q with
  | zero =>
    have ha : IsPrenexAtMost k q := h
    rw [iff_atomReading ha.isPrenexAtom,
      iff_atomReading (h.neg hq : IsPrenexAtMost k (neg ℒₒᵣ q)).isPrenexAtom,
      AtomReading.neg ha.isPrenexAtom (h.neg hq : IsPrenexAtMost k (neg ℒₒᵣ q)).isPrenexAtom hq]
  | succ D ih =>
    rcases h.cases with ha | ⟨D', hD, ⟨q₁, q₂, rfl, h₁, h₂⟩ | ⟨q₁, q₂, rfl, h₁, h₂⟩⟩
    · have hna : IsPrenexAtMost k (neg ℒₒᵣ q) :=
        IsCombination.neg (D := 0) hq ha
      rw [iff_atomReading ha.isPrenexAtom, iff_atomReading hna.isPrenexAtom,
        AtomReading.neg ha.isPrenexAtom hna.isPrenexAtom hq]
    · obtain rfl : D' = D := by omega
      obtain ⟨hq₁, hq₂⟩ := IsUFormula.and.mp hq
      rw [neg_and hq₁ hq₂, or_iff hq₁.neg hq₂.neg, and_iff hq₁ hq₂, ih h₁ hq₁, ih h₂ hq₂]
      tauto
    · obtain rfl : D' = D := by omega
      obtain ⟨hq₁, hq₂⟩ := IsUFormula.or.mp hq
      rw [neg_or hq₁ hq₂, and_iff hq₁.neg hq₂.neg, or_iff hq₁ hq₂, ih h₁ hq₁, ih h₂ hq₂]
      tauto

end reading

/-! ### The Tarski conditions for closed formulas -/

section readableTruth

variable {k D : ℕ} {q χ : V}

lemma ReadableTruth.iff_atomReading (ha : IsPrenexAtom k q) :
    ReadableTruth k D q ↔ AtomReading k q := by
  simp [ReadableTruth, IsReadable.of_isPrenexAtom ha, CombinationReading.iff_atomReading ha, ha]

lemma ReadableTruth.iff_combinationReading (h : IsCombination k D q) :
    ReadableTruth k D q ↔ CombinationReading k D q := by
  constructor
  · intro h'
    exact h'.2.1
  · intro h'
    refine ⟨.of_isCombination h, h', ?_⟩
    rintro ha χ - rfl
    exact absurd h.isPrenexAtMost_of_all.isPrenexAtom ha

@[simp] lemma ReadableTruth.verum : ReadableTruth k D (^⊤ : V) := by
  have ha : IsPrenexAtom k (^⊤ : V) := (IsPrenexAtMost.of_isBounded (by simp)).isPrenexAtom
  rw [iff_atomReading ha, AtomReading.iff (Γ := 𝚺) (s := 0) (θ := ^⊤) ha rfl (by simp) (by simp)]
  simp

lemma ReadableTruth.and_iff {q₁ q₂ : V} (h : IsReadable k D (q₁ ^⋏ q₂))
    (hq₁ : IsUFormula ℒₒᵣ q₁) (hq₂ : IsUFormula ℒₒᵣ q₂) :
    ReadableTruth k D (q₁ ^⋏ q₂) ↔ ReadableTruth k D q₁ ∧ ReadableTruth k D q₂ := by
  have hc := h.isCombination_of_and
  rcases hc.cases with ha | ⟨D, rfl, ⟨p₁, p₂, he, h₁, h₂⟩ | ⟨p₁, p₂, he, -, -⟩⟩
  · obtain ⟨ha₁, ha₂⟩ := IsPrenexAtMost.of_and ha.isPrenexAtom
    rw [iff_atomReading ha.isPrenexAtom, iff_atomReading ha₁.isPrenexAtom,
      iff_atomReading ha₂.isPrenexAtom,
      ← CombinationReading.iff_atomReading (D := 1) ha.isPrenexAtom,
      CombinationReading.and_iff hq₁ hq₂]
    rfl
  · obtain ⟨rfl, rfl⟩ := (qqAnd_inj _ _ _ _).mp he
    rw [iff_combinationReading hc, iff_combinationReading h₁.succ, iff_combinationReading h₂.succ,
      CombinationReading.and_iff hq₁ hq₂, CombinationReading.succ_iff h₁ hq₁,
      CombinationReading.succ_iff h₂ hq₂]
  · simp [qqAnd, qqOr] at he

lemma ReadableTruth.or_iff {q₁ q₂ : V} (h : IsReadable k D (q₁ ^⋎ q₂))
    (hq₁ : IsUFormula ℒₒᵣ q₁) (hq₂ : IsUFormula ℒₒᵣ q₂) :
    ReadableTruth k D (q₁ ^⋎ q₂) ↔ ReadableTruth k D q₁ ∨ ReadableTruth k D q₂ := by
  have hc := h.isCombination_of_or
  rcases hc.cases with ha | ⟨D, rfl, ⟨p₁, p₂, he, -, -⟩ | ⟨p₁, p₂, he, h₁, h₂⟩⟩
  · obtain ⟨ha₁, ha₂⟩ := IsPrenexAtMost.of_or ha.isPrenexAtom
    rw [iff_atomReading ha.isPrenexAtom, iff_atomReading ha₁.isPrenexAtom,
      iff_atomReading ha₂.isPrenexAtom,
      ← CombinationReading.iff_atomReading (D := 1) ha.isPrenexAtom,
      CombinationReading.or_iff hq₁ hq₂]
    rfl
  · simp [qqAnd, qqOr] at he
  · obtain ⟨rfl, rfl⟩ := (qqOr_inj _ _ _ _).mp he
    rw [iff_combinationReading hc, iff_combinationReading h₁.succ, iff_combinationReading h₂.succ,
      CombinationReading.or_iff hq₁ hq₂, CombinationReading.succ_iff h₁ hq₁,
      CombinationReading.succ_iff h₂ hq₂]

lemma ReadableTruth.all_iff (h : IsReadable k D (^∀ χ)) (hχ : IsSemiformula ℒₒᵣ 1 χ) :
    ReadableTruth k D (^∀ χ) ↔ ∀ x, ReadableTruth k D (substs1 ℒₒᵣ (numeral x) χ) := by
  by_cases ha : IsPrenexAtom k (^∀ χ)
  · obtain ⟨s, θ, hs, rfl, hθ⟩ := ha.exists_of_all
    rw [iff_atomReading ha,
      AtomReading.iff (Γ := 𝚷) (s := s + 1) ha rfl hθ (by simpa using hχ.isUFormula)]
    apply forall_congr'
    intro x
    obtain ⟨ha', hr⟩ := AtomReading.substs1_iff hs hθ hχ (Arithmetic.numeral_semiterm 0 x)
    rw [iff_atomReading ha', hr, termVal_numeral]
  · have hc := h.isCombination_of_all
    have hc' (x : V) : IsCombination k D (substs1 ℒₒᵣ (numeral x) χ) :=
      hc.subst (m := 0) (by simp) hχ
    have e : ReadableTruth k D (^∀ χ) ↔
        ∀ x, CombinationReading k D (substs1 ℒₒᵣ (numeral x) χ) := by
      constructor
      · intro h' x
        exact h'.2.2 ha χ (by simp) rfl x
      · intro h'
        refine ⟨h, CombinationReading.of_not_isPrenexAtom_all ha, ?_⟩
        rintro - χ' - he
        obtain rfl := (qqAll_inj _ _).mp he
        exact h'
    rw [e]
    apply forall_congr'
    intro x
    exact (iff_combinationReading (hc' x)).symm

lemma ReadableTruth.exs_iff (h : IsReadable k D (^∃ χ)) (hχ : IsSemiformula ℒₒᵣ 1 χ) :
    ReadableTruth k D (^∃ χ) ↔ ∃ x, ReadableTruth k D (substs1 ℒₒᵣ (numeral x) χ) := by
  have ha := h.isPrenexAtom_of_exs
  obtain ⟨s, θ, hs, rfl, hθ⟩ := ha.exists_of_exs
  rw [iff_atomReading ha,
    AtomReading.iff (Γ := 𝚺) (s := s + 1) ha rfl hθ (by simpa using hχ.isUFormula)]
  apply exists_congr
  intro x
  obtain ⟨ha', hr⟩ := AtomReading.substs1_iff hs hθ hχ (Arithmetic.numeral_semiterm 0 x)
  rw [iff_atomReading ha', hr, termVal_numeral]

lemma ReadableTruth.substs1_iff {t : V} (h : IsReadable k D (^∃ χ)) (hχ : IsSemiformula ℒₒᵣ 1 χ)
    (ht : IsSemiterm ℒₒᵣ 0 t) :
    ReadableTruth k D (substs1 ℒₒᵣ t χ) ↔
      ReadableTruth k D (substs1 ℒₒᵣ (numeral (termVal 0 t)) χ) := by
  obtain ⟨s, θ, hs, rfl, hθ⟩ := h.isPrenexAtom_of_exs.exists_of_exs
  obtain ⟨ha, hr⟩ := AtomReading.substs1_iff hs hθ hχ ht
  obtain ⟨ha', hr'⟩ :=
    AtomReading.substs1_iff hs hθ hχ (Arithmetic.numeral_semiterm 0 (termVal 0 t))
  rw [iff_atomReading ha, iff_atomReading ha', hr, hr', termVal_numeral]

lemma ReadableTruth.exs_of_substs1 {t : V} (h : IsReadable k D (^∃ χ))
    (hχ : IsSemiformula ℒₒᵣ 1 χ) (ht : IsSemiterm ℒₒᵣ 0 t)
    (ht' : ReadableTruth k D (substs1 ℒₒᵣ t χ)) : ReadableTruth k D (^∃ χ) :=
  (exs_iff h hχ).mpr ⟨termVal 0 t, (substs1_iff h hχ ht).mp ht'⟩

/-- A prenex atom whose negation is readable has a negation that is a prenex atom. -/
lemma IsReadable.isPrenexAtom_neg (ha : IsPrenexAtom k q) (hn : IsReadable k D (neg ℒₒᵣ q))
    (hq : IsUFormula ℒₒᵣ q) : IsPrenexAtom k (neg ℒₒᵣ q) := by
  obtain ⟨Γ, s, θ, hs, rfl, hθ⟩ := ha.exists_qqToPrenex
  have hθ' : IsUFormula ℒₒᵣ θ := isUFormula_qqToPrenex.mp hq
  rw [neg_qqToPrenex hθ'] at hn ⊢
  rcases hs with hs | ⟨rfl, rfl⟩
  · exact IsPrenexAtom.of_qqToPrenex (.of_le hs) (hθ.neg hθ')
  · exact hn.isPrenexAtom_of_exs

lemma ReadableTruth.neg_iff (h : IsReadable k D q) (hn : IsReadable k D (neg ℒₒᵣ q))
    (hq : IsUFormula ℒₒᵣ q) : ReadableTruth k D (neg ℒₒᵣ q) ↔ ¬ReadableTruth k D q := by
  by_cases ha : IsPrenexAtom k q
  · have hna := hn.isPrenexAtom_neg ha hq
    rw [iff_atomReading ha, iff_atomReading hna, AtomReading.neg ha hna hq]
  · by_cases hna : IsPrenexAtom k (neg ℒₒᵣ q)
    · have h' : IsReadable k D (neg ℒₒᵣ (neg ℒₒᵣ q)) := by rwa [IsUFormula.neg_neg hq]
      have := IsReadable.isPrenexAtom_neg hna h' hq.neg
      rw [IsUFormula.neg_neg hq] at this
      exact absurd this ha
    · have hc : IsCombination k D q := by
        rcases h with h | ⟨χ, -, rfl, -⟩ | h
        · exact h
        · have hχ : IsUFormula ℒₒᵣ χ := IsUFormula.all.mp hq
          rw [neg_all hχ] at hn hna
          exact absurd hn.isPrenexAtom_of_exs hna
        · exact absurd (isPrenexAtom_iff.mpr (Or.inr h)) ha
      rw [iff_combinationReading hc, iff_combinationReading (hc.neg hq),
        CombinationReading.neg hc hq]

end readableTruth

/-! ### Definability of truth -/

section truthDefinability

open FFL.FirstOrder.Bounding.HierarchySymbol

variable {k : ℕ} {Γ : Polarity} {s : ℕ}

lemma HierarchicalSatisfaction.definable_of_isAtomLevel (hs : IsAtomLevel k Γ s) :
    𝚷ᴬ-[k + 1]-Relation (HierarchicalSatisfaction Γ s : V → V → Prop) := by
  rcases s with _ | s
  · have : 𝚫ᴬ₁-Relation (HierarchicalSatisfaction Γ 0 : V → V → Prop) := by
      apply BoundedSatisfaction.definable.of_iff
      intro v
      simp
    exact this.of_deltaOne
  · rcases Γ with _ | _
    · have hs : s + 1 ≤ k := by rcases hs with hs | ⟨h, -⟩ <;> simp_all
      exact (HierarchicalSatisfaction.sigma_definable (s + 1)).of_lt (by simp; omega)
    · rcases hs with hs | ⟨-, hs⟩
      · exact (HierarchicalSatisfaction.pi_definable (s + 1)).of_lt (by simp; omega)
      · obtain rfl : s = k := by omega
        exact HierarchicalSatisfaction.pi_definable (s + 1)

lemma PrenexReading.definable (hs : IsAtomLevel k Γ s) :
    𝚷ᴬ-[k + 1]-Predicate (PrenexReading Γ s : V → Prop) := by
  have := HierarchicalSatisfaction.definable_of_isAtomLevel (V := V) hs
  have : 𝚺ᴬ-[k + 1]-Predicate (IsBounded : V → Prop) := IsBounded.definable.of_deltaOne
  have : 𝚺ᴬ-[k + 1]-Function₁ (qqToPrenex Γ s : V → V) :=
    Definable.of_zero (qqToPrenex_defined Γ s).to_definable
  have : 𝚷ᴬ-[k + 1]-Predicate fun q : V ↦ ∀ θ ≤ q, q = qqToPrenex Γ s θ → IsBounded θ →
      HierarchicalSatisfaction Γ s θ 0 := by
    definability
  exact this.of_iff fun _ ↦ Iff.rfl

instance AtomReading.definable : 𝚷ᴬ-[k + 1]-Predicate (AtomReading k : V → Prop) := by
  have h (Γ : Polarity) (s : Fin (k + 2)) :
      𝚷ᴬ-[k + 1]-Predicate fun q : V ↦ IsAtomLevel k Γ s → PrenexReading Γ s q := by
    by_cases hs : IsAtomLevel k Γ s
    · apply (PrenexReading.definable hs).of_iff
      simp [hs]
    · apply (Definable.const (P := True)).of_iff
      simp [hs]
  have : 𝚷ᴬ-[k + 1]-Predicate fun q : V ↦ ∀ s : Fin (k + 2),
      (IsAtomLevel k 𝚺 s → PrenexReading 𝚺 s q) ∧ (IsAtomLevel k 𝚷 s → PrenexReading 𝚷 s q) :=
    Definable.fintype_all fun s ↦ (h 𝚺 s).and (h 𝚷 s)
  apply this.of_iff
  intro v
  constructor
  · intro H s
    exact ⟨H 𝚺 s, H 𝚷 s⟩
  · intro H Γ s hs
    have hs' : s < k + 2 := by rcases hs with hs | ⟨-, hs⟩ <;> omega
    rcases Γ with _ | _
    · exact (H ⟨s, hs'⟩).1 hs
    · exact (H ⟨s, hs'⟩).2 hs

instance CombinationReading.definable :
    (D : ℕ) → 𝚷ᴬ-[k + 1]-Predicate (CombinationReading k D : V → Prop)
  | 0 => AtomReading.definable
  | D + 1 => by
    have := CombinationReading.definable D
    have : 𝚷ᴬ-[k + 1]-Predicate fun q : V ↦ (IsPrenexAtom k q → AtomReading k q) ∧
        (¬IsPrenexAtom k q → ∀ q₁ < q, ∀ q₂ < q, q = q₁ ^⋏ q₂ →
          CombinationReading k D q₁ ∧ CombinationReading k D q₂) ∧
        (¬IsPrenexAtom k q → ∀ q₁ < q, ∀ q₂ < q, q = q₁ ^⋎ q₂ →
          CombinationReading k D q₁ ∨ CombinationReading k D q₂) := by
      definability
    exact this.of_iff fun _ ↦ Iff.rfl

instance ReadableTruth.definable (D : ℕ) :
    𝚷ᴬ-[k + 1]-Predicate (ReadableTruth k D : V → Prop) := by
  have : 𝚷ᴬ-[k + 1]-Predicate fun q : V ↦ IsReadable k D q ∧ CombinationReading k D q ∧
      (¬IsPrenexAtom k q → ∀ χ < q, q = ^∀ χ →
        ∀ x, CombinationReading k D (substs1 ℒₒᵣ (numeral x) χ)) := by
    definability
  exact this.of_iff fun _ ↦ Iff.rfl

instance ReadableSatisfaction.definable (D : ℕ) :
    𝚷ᴬ-[k + 1]-Relation (ReadableSatisfaction k D : V → V → Prop) := by
  have : 𝚷ᴬ-[k + 1]-Relation fun p f : V ↦ ReadableTruth k D (fvAssign f p) := by
    definability
  exact this.of_iff fun _ ↦ Iff.rfl

end truthDefinability

/-! ### The Tarski conditions -/

section readableSatisfaction

variable {k D : ℕ} {p q f : V}

lemma ReadableSatisfaction.isReadable (h : ReadableSatisfaction k D p f) :
    IsReadable k D (fvAssign f p) := h.1

@[simp] lemma ReadableSatisfaction.verum : ReadableSatisfaction k D (^⊤ : V) f := by
  simp [ReadableSatisfaction]

lemma ReadableSatisfaction.and_iff (h : IsReadable k D (p ^⋏ q)) (hp : IsUFormula ℒₒᵣ p)
    (hq : IsUFormula ℒₒᵣ q) :
    ReadableSatisfaction k D (p ^⋏ q) f ↔
      ReadableSatisfaction k D p f ∧ ReadableSatisfaction k D q f := by
  have h' := h.fvAssign (f := f) (by simp [hp, hq])
  rw [fvAssign_and hp hq] at h'
  rw [ReadableSatisfaction, fvAssign_and hp hq]
  exact ReadableTruth.and_iff h' hp.fvAssign hq.fvAssign

lemma ReadableSatisfaction.or_iff (h : IsReadable k D (p ^⋎ q)) (hp : IsUFormula ℒₒᵣ p)
    (hq : IsUFormula ℒₒᵣ q) :
    ReadableSatisfaction k D (p ^⋎ q) f ↔
      ReadableSatisfaction k D p f ∨ ReadableSatisfaction k D q f := by
  have h' := h.fvAssign (f := f) (by simp [hp, hq])
  rw [fvAssign_or hp hq] at h'
  rw [ReadableSatisfaction, fvAssign_or hp hq]
  exact ReadableTruth.or_iff h' hp.fvAssign hq.fvAssign

lemma ReadableSatisfaction.all_iff (h : IsReadable k D (^∀ p)) (hp : IsSemiformula ℒₒᵣ 1 p) :
    ReadableSatisfaction k D (^∀ p) f ↔ ∀ x, ReadableSatisfaction k D (free ℒₒᵣ p) (x ∷ f) := by
  have h' := h.fvAssign (f := f) (by simpa using hp.isUFormula)
  rw [fvAssign_all hp.isUFormula] at h'
  simp only [ReadableSatisfaction, fvAssign_all hp.isUFormula, fvAssign_free hp]
  exact ReadableTruth.all_iff h' hp.fvAssign

lemma ReadableSatisfaction.exs_iff (h : IsReadable k D (^∃ p)) (hp : IsSemiformula ℒₒᵣ 1 p) :
    ReadableSatisfaction k D (^∃ p) f ↔ ∃ x, ReadableSatisfaction k D (free ℒₒᵣ p) (x ∷ f) := by
  have h' := h.fvAssign (f := f) (by simpa using hp.isUFormula)
  rw [fvAssign_exs hp.isUFormula] at h'
  simp only [ReadableSatisfaction, fvAssign_exs hp.isUFormula, fvAssign_free hp]
  exact ReadableTruth.exs_iff h' hp.fvAssign

lemma ReadableSatisfaction.exs_of_substs1 {t : V} (h : IsReadable k D (^∃ p))
    (hp : IsSemiformula ℒₒᵣ 1 p) (ht : IsSemiterm ℒₒᵣ 0 t)
    (ht' : ReadableSatisfaction k D (substs1 ℒₒᵣ t p) f) : ReadableSatisfaction k D (^∃ p) f := by
  have h' := h.fvAssign (f := f) (by simpa using hp.isUFormula)
  rw [fvAssign_exs hp.isUFormula] at h'
  rw [ReadableSatisfaction, fvAssign_substs1 ht hp] at ht'
  rw [ReadableSatisfaction, fvAssign_exs hp.isUFormula]
  exact ReadableTruth.exs_of_substs1 h' hp.fvAssign ht.termFvAssign ht'

lemma ReadableSatisfaction.qqToPrenex_iff {Γ : Polarity} {s : ℕ} {θ : V}
    (hs : IsAtomLevel k Γ s) (hθ : IsBounded θ) (hθ' : IsUFormula ℒₒᵣ θ) :
    ReadableSatisfaction k D (qqToPrenex Γ s θ) f ↔
      HierarchicalSatisfaction Γ s (fvAssign f θ) 0 := by
  have hb := hθ.fvAssign (f := f) hθ'
  have ha := IsPrenexAtom.of_qqToPrenex (k := k) hs hb
  rw [ReadableSatisfaction, fvAssign_qqToPrenex hθ', ReadableTruth.iff_atomReading ha,
    AtomReading.iff ha rfl hb (by simpa using hθ'.fvAssign)]

lemma ReadableSatisfaction.isBounded_iff (h : IsBounded p) (hp : IsUFormula ℒₒᵣ p) :
    ReadableSatisfaction k D p f ↔ BoundedSatisfaction (fvAssign f p) 0 := by
  simpa using qqToPrenex_iff (D := D) (f := f) (Γ := 𝚺) (s := 0) (.of_le (Nat.zero_le k)) h hp

@[simp] lemma ReadableSatisfaction.shift_iff {b : V} :
    ReadableSatisfaction k D (shift ℒₒᵣ p) (b ∷ f) ↔ ReadableSatisfaction k D p f := by
  by_cases hp : IsUFormula ℒₒᵣ p
  · rw [ReadableSatisfaction, fvAssign_shift hp, ReadableSatisfaction]
  · rw [ReadableSatisfaction, shift_not_uformula hp, ReadableSatisfaction,
      fvAssign_not_uformula hp, fvAssign_not_uformula (by simp)]

lemma ReadableSatisfaction.congr {g : V} (h : ∀ i, f.[i] = g.[i]) :
    ReadableSatisfaction k D p f ↔ ReadableSatisfaction k D p g := by
  rw [ReadableSatisfaction, ReadableSatisfaction, fvAssign_congr h]

lemma ReadableSatisfaction.neg_iff (h : IsReadable k D p) (hn : IsReadable k D (neg ℒₒᵣ p))
    (hp : IsUFormula ℒₒᵣ p) :
    ReadableSatisfaction k D (neg ℒₒᵣ p) f ↔ ¬ReadableSatisfaction k D p f := by
  have hn' := hn.fvAssign (f := f) hp.neg
  rw [fvAssign_neg hp] at hn'
  rw [ReadableSatisfaction, ReadableSatisfaction, fvAssign_neg hp]
  exact ReadableTruth.neg_iff (h.fvAssign hp) hn' hp.fvAssign

end readableSatisfaction

/-! ### Formulas of the meta level -/

section quote

variable {k D : ℕ} {Γ : Polarity} {s n : ℕ}

/-- An instance of a prenex formula `qqToPrenex Γ s θ` with a $\Delta_0$ matrix, read directly, by
closed terms is true exactly when the matrix is satisfied by the values of the terms.
- [HP98, Theorem I.1.75] -/
theorem ReadableTruth.subst_qqToPrenex_iff {n θ u : V} (hs : IsAtomLevel k Γ s)
    (hθ : IsSemiformula ℒₒᵣ (n + s) θ) (hb : IsBounded θ) (hu : IsSemitermVec ℒₒᵣ n 0 u) :
    ReadableTruth k D (subst ℒₒᵣ u (qqToPrenex Γ s θ)) ↔
      HierarchicalSatisfaction Γ s θ (termValVec 0 n u) := by
  have he : subst ℒₒᵣ u (qqToPrenex Γ s θ) =
      qqToPrenex Γ s (subst ℒₒᵣ ((qVec ℒₒᵣ)^[s] u) θ) := subst_qqToPrenex hθ.isUFormula
  have hb' := hb.subst (hu.iterate_qVec s) hθ
  have hφ : IsSemiformula ℒₒᵣ n (qqToPrenex Γ s θ) := isSemiformula_qqToPrenex.mpr hθ
  have ha : IsPrenexAtom k (subst ℒₒᵣ u (qqToPrenex Γ s θ)) :=
    he ▸ IsPrenexAtom.of_qqToPrenex hs hb'
  rw [iff_atomReading ha, AtomReading.iff ha he hb' (hφ.subst hu).isUFormula,
    HierarchicalSatisfaction.subst hu hθ hb]

/-- An instance of a standard prenex formula by closed terms is true exactly when the formula
holds of the values of the terms.
- [HP98, Theorem I.1.75] -/
theorem ReadableTruth.subst_quote_iff (hs : IsAtomLevel k Γ s)
    (φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty n) {w : V} (hw : IsSemitermVec ℒₒᵣ (n : V) 0 w) :
    ReadableTruth k D (subst ℒₒᵣ w ⌜φ.val⌝) ↔ V ⊧/(fun i ↦ termVal 0 w.[i]) φ.val := by
  have hb : IsBounded (⌜φ.matrix.val⌝ : V) := (isBounded_quote_iff _).mpr φ.matrix.bounded
  have hf : IsSemiformula ℒₒᵣ (n + s : V) ⌜φ.matrix.val⌝ := by
    simpa using Sentence.quote_isSemiformula (V := V) φ.matrix.val
  have hφ : IsSemiformula ℒₒᵣ (n : V) ⌜φ.val⌝ := by simp
  have he : subst ℒₒᵣ w ⌜φ.val⌝ =
      qqToPrenex Γ s (subst ℒₒᵣ ((qVec ℒₒᵣ)^[s] w) ⌜φ.matrix.val⌝) := by
    rw [Bounding.Prenex.val, quote_toPrenex, subst_qqToPrenex hf.isUFormula]
  have hb' := hb.subst (hw.iterate_qVec s) hf
  have ha : IsPrenexAtom k (subst ℒₒᵣ w ⌜φ.val⌝) := by
    rw [he]
    exact IsPrenexAtom.of_qqToPrenex hs hb'
  have hv : termValVec 0 (n : V) w = matrixToVec fun i : Fin n ↦ termVal 0 w.[((i : ℕ) : V)] := by
    apply nth_ext' (n : V) (by simp [hw.isUTerm]) (by simp)
    intro i hi
    rw [nth_termValVec hw.isUTerm hi]
    obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hi
    have hj : j < n := by exact_mod_cast hi
    simpa using (matrixToVec_nth (fun i : Fin n ↦ termVal 0 w.[((i : ℕ) : V)]) ⟨j, hj⟩).symm
  rw [iff_atomReading ha, AtomReading.iff ha he hb' (hφ.subst hw).isUFormula,
    HierarchicalSatisfaction.subst hw hf hb, hv, hierarchicalSatisfaction_quote_iff]

/-- An instance of a standard prenex formula by terms is true under an assignment exactly when the
formula holds of the values of the terms.
- [HP98, Theorem I.1.75] -/
theorem ReadableSatisfaction.subst_quote_iff (hs : IsAtomLevel k Γ s)
    (φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty n) {w : V} (hw : IsSemitermVec ℒₒᵣ (n : V) 0 w) (f : V) :
    ReadableSatisfaction k D (subst ℒₒᵣ w ⌜φ.val⌝) f ↔
      V ⊧/(fun i ↦ termVal 0 (termFvAssign f w.[i])) φ.val := by
  have hf : IsSemiformula ℒₒᵣ (n : V) ⌜φ.val⌝ := by simp
  rw [ReadableSatisfaction, fvAssign_subst hw hf, fvAssign_quote,
    ReadableTruth.subst_quote_iff hs φ hw.termFvAssignVec]
  have e : (fun i : Fin n ↦ termVal 0 (termFvAssignVec (n : V) f w).[((i : ℕ) : V)]) =
      fun i : Fin n ↦ termVal 0 (termFvAssign f w.[((i : ℕ) : V)]) := by
    funext i
    rw [nth_termFvAssignVec hw.isUTerm (by exact_mod_cast i.isLt)]
  rw [e]

end quote

end FFL.FirstOrder.Arithmetic.Bootstrapping
