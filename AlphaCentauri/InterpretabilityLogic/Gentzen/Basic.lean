module

public import AlphaCentauri.InterpretabilityLogic.Sequent

/-!
# A sequent calculus for $\mathbf{IL}$

A cut-free sequent calculus for $\mathbf{IL}$ in the language with a primitive `□`. Its modal rules
are those of $\mathbf{GIL}$, with `A ▷ ⊥` written `□∼A`, the boxes on the left treated as in the
calculus of $\mathbf{GL}$, and a rule for `□` on the right.

## References

- [HSS25a]
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace IL

variable {α : Type*} [DecidableEq α]

/-- The first components of a list of pairs of formulas. -/
def antecedents (l : List (Formula α × Formula α)) : FormulaFinset α := (l.map Prod.fst).toFinset

/-- The formulas `A ▷ B` for the pairs `(A, B)` of a list. -/
def rhdFormulas (l : List (Formula α × Formula α)) : FormulaFinset α :=
  (l.map fun p ↦ p.1 ▷ p.2).toFinset

/-- The sequent `D, □∼D, Γ, □Γ, □∼N ⟹ N`. -/
def witness (Γ N : FormulaFinset α) (D : Formula α) : Sequent α :=
  insert D (insert (□(∼D)) (Γ ∪ Γ.box ∪ N.boxNeg)) ⟹ N

@[simp, grind =] lemma antecedents_nil : antecedents ([] : List (Formula α × Formula α)) = ∅ := rfl

@[simp, grind =] lemma antecedents_cons {p : Formula α × Formula α} {l} :
    antecedents (p :: l) = insert p.1 (antecedents l) := by simp [antecedents]

@[simp, grind =] lemma mem_antecedents {l : List (Formula α × Formula α)} {A : Formula α} :
    A ∈ antecedents l ↔ ∃ B, (A, B) ∈ l := by simp [antecedents]

@[simp, grind =] lemma rhdFormulas_nil : rhdFormulas ([] : List (Formula α × Formula α)) = ∅ := rfl

@[simp, grind =] lemma rhdFormulas_cons {p : Formula α × Formula α} {l} :
    rhdFormulas (p :: l) = insert (p.1 ▷ p.2) (rhdFormulas l) := by simp [rhdFormulas]

@[simp, grind =] lemma mem_rhdFormulas {l : List (Formula α × Formula α)} {C : Formula α} :
    C ∈ rhdFormulas l ↔ ∃ A B, (A, B) ∈ l ∧ C = A ▷ B := by
  simp [rhdFormulas, eq_comm]

/-- The cut-free sequent calculus for $\mathbf{IL}$: the rules `rhd` and `box` take, for a list
`l` of pairs `(C, D)` of the formulas `C ▷ D` on the left, one premise for each pair and one for the
formula on the right, the premise of a pair mentioning the antecedents of the pairs after it.

- [HSS25a, Definition 3.1]
-/
inductive Gentzen : Sequent α → Prop
  | axm (A) : Gentzen ({A} ⟹ {A})
  | botL : Gentzen ({⊥} ⟹ ∅)
  | wkL {Γ Γ' Δ} : Gentzen (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → Gentzen (Γ' ⟹ Δ)
  | wkR {Γ Δ Δ'} : Gentzen (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → Gentzen (Γ ⟹ Δ')
  | impL {Γ Δ A B} :
    Gentzen (Γ ⟹ insert A Δ) → Gentzen (insert B Γ ⟹ Δ) → Gentzen (insert (A 🡒 B) Γ ⟹ Δ)
  | impR {Γ Δ A B} : Gentzen (insert A Γ ⟹ insert B Δ) → Gentzen (Γ ⟹ insert (A 🡒 B) Δ)
  | rhd {Γ : FormulaFinset α} {l : List (Formula α × Formula α)} {A B : Formula α} :
    (∀ l₁ p l₂, l = l₁ ++ p :: l₂ → Gentzen (witness Γ (insert B (antecedents l₂)) p.2)) →
    Gentzen (witness Γ (insert B (antecedents l)) A) →
    Gentzen (Γ.box ∪ rhdFormulas l ⟹ {A ▷ B})
  | box {Γ : FormulaFinset α} {l : List (Formula α × Formula α)} {B : Formula α} :
    (∀ l₁ p l₂, l = l₁ ++ p :: l₂ → Gentzen (witness Γ (antecedents l₂) p.2)) →
    Gentzen (insert (□B) (Γ ∪ Γ.box ∪ (antecedents l).boxNeg) ⟹ insert B (antecedents l)) →
    Gentzen (Γ.box ∪ rhdFormulas l ⟹ {□B})

@[inherit_doc] notation:45 "⊢ᴳ[𝐈𝐋] " S:50 => Gentzen S

notation:45 "⊬ᴳ[𝐈𝐋] " S:50 => ¬Gentzen S

namespace Gentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α} {S : Sequent α}

lemma union (A) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᴳ[𝐈𝐋] Γ ⟹ Δ :=
  wkR (wkL (axm A) (by simpa)) (by simpa)

lemma union' (A) (hΓ : A ∈ S.ant) (hΔ : A ∈ S.suc) : ⊢ᴳ[𝐈𝐋] S := union A hΓ hΔ

lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᴳ[𝐈𝐋] Γ ⟹ Δ := wkR (wkL botL (by simpa)) (by simp)

lemma wk (h : ⊢ᴳ[𝐈𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[𝐈𝐋] Γ' ⟹ Δ' := wkR (wkL h hΓ) hΔ

lemma negL (h : ⊢ᴳ[𝐈𝐋] Γ ⟹ insert A Δ) : ⊢ᴳ[𝐈𝐋] insert (∼A) Γ ⟹ Δ :=
  impL h (botL_mem (Finset.mem_insert_self _ _))

lemma negR (h : ⊢ᴳ[𝐈𝐋] insert A Γ ⟹ Δ) : ⊢ᴳ[𝐈𝐋] Γ ⟹ insert (∼A) Δ := impR (wkR h)

lemma isImpClosed : Sequent.IsImpClosed (Gentzen (α := α)) :=
  ⟨fun h₁ h₂ ↦ union' _ h₁ h₂, impL, impR⟩

end Gentzen

end IL

end FFL.InterpretabilityLogic

end
