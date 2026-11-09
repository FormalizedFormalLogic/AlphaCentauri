module

public import Foundation.FirstOrder.Arithmetic.Prenex
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-!
# Boolean combinations of prenex formulas over open induction

In models of `𝗜𝗢𝗽𝗲𝗻`, pairing merges two adjacent quantifiers of the same kind into one. Hence a
conjunction or a disjunction of two prenex formulas of the same polarity and level, and the
existential quantification of a prenex $\Sigma_{s + 1}$ formula, are equivalent to a prenex formula
of that polarity and level. Unlike `Bounding.Prenex.and`, this needs no collection.
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding.Prenex

open Arithmetic

variable {ξ : Type*}

/-- `φ` with its first two free variables replaced by the two components of a single one. -/
def contract : {Γ : Polarity} → {s n : ℕ} →
    ℬ[<, ℒₒᵣ].Prenex Γ s ξ (n + 2) → ℬ[<, ℒₒᵣ].Prenex Γ s ξ (n + 1)
  | Γ, 0, n, φ =>
    bexs ‘#0 + 1’ <| bexs ‘#1 + 1’ <|
      (⟨⟨Rew.embSubsts ![#2, #1, #0] ▹ pairDef.val,
        (Hierarchy.zero_iff_bounded.mp pairDef.sigma_prop).rew _⟩⟩ : ℬ[<, ℒₒᵣ].Prenex Γ 0 ξ (n + 3)) ⋏
        φ.rew (Rew.subst (#1 :> #0 :> fun i ↦ #i.succ.succ.succ))
  | 𝚺, _ + 1, _, φ =>
    ((contract (φ.sigmaInv.rew (Rew.subst (#2 :> #0 :> #1 :> fun i ↦ #i.succ.succ.succ)))).rew
      (Rew.subst (#1 :> #0 :> fun i ↦ #i.succ.succ))).sigma
  | 𝚷, _ + 1, _, φ =>
    ((contract (φ.piInv.rew (Rew.subst (#2 :> #0 :> #1 :> fun i ↦ #i.succ.succ.succ)))).rew
      (Rew.subst (#1 :> #0 :> fun i ↦ #i.succ.succ))).pi

/-- The conjunction of two prenex formulas of the same polarity and level, with the two
existential quantifiers at each $\Sigma$ level merged by pairing. -/
def pairAnd : {Γ : Polarity} → {s n : ℕ} →
    ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n
  | _, 0, _, φ, ψ => φ ⋏ ψ
  | 𝚺, _ + 1, _, φ, ψ =>
    (contract (pairAnd (φ.sigmaInv.rew (Rew.subst (#0 :> fun i ↦ #i.succ.succ)))
      (ψ.sigmaInv.rew (Rew.subst (#1 :> fun i ↦ #i.succ.succ))))).sigma
  | 𝚷, _ + 1, _, φ, ψ => (pairAnd φ.piInv ψ.piInv).pi

/-- The disjunction of two prenex formulas of the same polarity and level, with the two
universal quantifiers at each $\Pi$ level merged by pairing. -/
def pairOr : {Γ : Polarity} → {s n : ℕ} →
    ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n
  | _, 0, _, φ, ψ => φ ⋎ ψ
  | 𝚺, _ + 1, _, φ, ψ => (pairOr φ.sigmaInv ψ.sigmaInv).sigma
  | 𝚷, _ + 1, _, φ, ψ =>
    (contract (pairOr (φ.piInv.rew (Rew.subst (#0 :> fun i ↦ #i.succ.succ)))
      (ψ.piInv.rew (Rew.subst (#1 :> fun i ↦ #i.succ.succ))))).pi

/-- The existential quantification of a prenex $\Sigma_{s + 1}$ formula, with its two outermost
existential quantifiers merged by pairing. -/
def pairExs {s n : ℕ} (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (n + 1)) : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ n :=
  (contract φ.sigmaInv).sigma

section eval

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] {f : ξ → V}

lemma eval_contract {Γ : Polarity} {s n : ℕ} (φ : ℬ[<, ℒₒᵣ].Prenex Γ s ξ (n + 2)) (z : V)
    (e : Fin n → V) :
    Semiformula.Eval (z :> e) f (contract φ).val ↔
      Semiformula.Eval (π₁ z :> π₂ z :> e) f φ.val := by
  induction s generalizing Γ n with
  | zero =>
    have h (a b : V) : (fun i ↦ Semiterm.val (b :> a :> z :> e) f
        ((#1 :> #0 :> fun i ↦ #i.succ.succ.succ : Fin (n + 2) → ArithmeticSemiterm ξ (n + 3)) i)) =
        a :> b :> e :=
      funext <| Fin.cases (by simp) <| Fin.cases (by simp) (by simp)
    simp [contract, Prenex.val, Arithmetic.lt_succ_iff_le]
    simp only [Prenex.rew, Rew.qpow_zero, Bounding.Semiformula.val_rew, Semiformula.eval_rew,
      Function.comp_def, Rew.subst_bvar, Rew.subst_fvar, Semiterm.val_fvar, h]
    constructor
    · rintro ⟨a, -, b, -, rfl, hφ⟩
      simpa using hφ
    · intro hφ
      exact ⟨π₁ z, pi₁_le_self z, π₂ z, pi₂_le_self z, by simp, hφ⟩
  | succ s ih =>
    have h₁ (u : V) : (fun i ↦ Semiterm.val (u :> z :> e) f
        ((#1 :> #0 :> fun i ↦ #i.succ.succ : Fin (n + 2) → ArithmeticSemiterm ξ (n + 2)) i)) =
        z :> u :> e :=
      funext <| Fin.cases (by simp) <| Fin.cases (by simp) (by simp)
    have h₂ (u : V) : (fun i ↦ Semiterm.val (π₁ z :> π₂ z :> u :> e) f
        ((#2 :> #0 :> #1 :> fun i ↦ #i.succ.succ.succ :
          Fin (n + 3) → ArithmeticSemiterm ξ (n + 3)) i)) = u :> π₁ z :> π₂ z :> e :=
      funext <| Fin.cases (by simp) <| Fin.cases (by simp) <| Fin.cases (by simp) (by simp)
    rcases Γ with _ | _
    · simp only [contract, models_sigma, val_rew, Semiformula.eval_rew, Function.comp_def,
        Rew.subst_bvar, Rew.subst_fvar, Semiterm.val_fvar, h₁, ih, h₂, ← models_sigmaInv]
    · simp only [contract, models_pi, val_rew, Semiformula.eval_rew, Function.comp_def,
        Rew.subst_bvar, Rew.subst_fvar, Semiterm.val_fvar, h₁, ih, h₂, ← models_piInv]

lemma eval_pairAnd {Γ : Polarity} {s n : ℕ} (φ ψ : ℬ[<, ℒₒᵣ].Prenex Γ s ξ n) (e : Fin n → V) :
    Semiformula.Eval e f (pairAnd φ ψ).val ↔
      Semiformula.Eval e f φ.val ∧ Semiformula.Eval e f ψ.val := by
  induction s generalizing Γ n with
  | zero => simp [pairAnd, Prenex.val]
  | succ s ih =>
    rcases Γ with _ | _
    · have h₁ (a b : V) : (fun i ↦ Semiterm.val (a :> b :> e) f
          ((#0 :> fun i ↦ #i.succ.succ : Fin (n + 1) → ArithmeticSemiterm ξ (n + 2)) i)) =
          a :> e :=
        funext <| Fin.cases (by simp) (by simp)
      have h₂ (a b : V) : (fun i ↦ Semiterm.val (a :> b :> e) f
          ((#1 :> fun i ↦ #i.succ.succ : Fin (n + 1) → ArithmeticSemiterm ξ (n + 2)) i)) =
          b :> e :=
        funext <| Fin.cases (by simp) (by simp)
      simp only [pairAnd, models_sigma, eval_contract, ih, val_rew, Semiformula.eval_rew,
        Function.comp_def, Rew.subst_bvar, Rew.subst_fvar, Semiterm.val_fvar, h₁, h₂,
        models_sigmaInv φ, models_sigmaInv ψ]
      constructor
      · rintro ⟨z, ha, hb⟩
        exact ⟨⟨_, ha⟩, ⟨_, hb⟩⟩
      · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        exact ⟨⟪a, b⟫, by simpa using ha, by simpa using hb⟩
    · simp only [pairAnd, models_pi, ih, models_piInv φ, models_piInv ψ, forall_and]

lemma eval_pairOr {Γ : Polarity} {s n : ℕ} (φ ψ : ℬ[<, ℒₒᵣ].Prenex Γ s ξ n) (e : Fin n → V) :
    Semiformula.Eval e f (pairOr φ ψ).val ↔
      Semiformula.Eval e f φ.val ∨ Semiformula.Eval e f ψ.val := by
  induction s generalizing Γ n with
  | zero => simp [pairOr, Prenex.val]
  | succ s ih =>
    rcases Γ with _ | _
    · simp only [pairOr, models_sigma, ih, models_sigmaInv φ, models_sigmaInv ψ, exists_or]
    · have h₁ (a b : V) : (fun i ↦ Semiterm.val (a :> b :> e) f
          ((#0 :> fun i ↦ #i.succ.succ : Fin (n + 1) → ArithmeticSemiterm ξ (n + 2)) i)) =
          a :> e :=
        funext <| Fin.cases (by simp) (by simp)
      have h₂ (a b : V) : (fun i ↦ Semiterm.val (a :> b :> e) f
          ((#1 :> fun i ↦ #i.succ.succ : Fin (n + 1) → ArithmeticSemiterm ξ (n + 2)) i)) =
          b :> e :=
        funext <| Fin.cases (by simp) (by simp)
      simp only [pairOr, models_pi, eval_contract, ih, val_rew, Semiformula.eval_rew,
        Function.comp_def, Rew.subst_bvar, Rew.subst_fvar, Semiterm.val_fvar, h₁, h₂,
        models_piInv φ, models_piInv ψ]
      constructor
      · intro h
        by_contra! hn
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hn
        rcases h ⟪a, b⟫ with h | h
        · exact ha (by simpa using h)
        · exact hb (by simpa using h)
      · rintro (h | h) z
        · exact Or.inl <| h _
        · exact Or.inr <| h _

lemma eval_pairExs {s n : ℕ} (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (n + 1)) (e : Fin n → V) :
    Semiformula.Eval e f (pairExs φ).val ↔ ∃ x, Semiformula.Eval (x :> e) f φ.val := by
  simp only [pairExs, models_sigma, eval_contract, models_sigmaInv φ]
  constructor
  · rintro ⟨z, h⟩
    exact ⟨_, _, h⟩
  · rintro ⟨x, y, h⟩
    exact ⟨⟪y, x⟫, by simpa using h⟩

end eval

end FFL.FirstOrder.Bounding.Prenex
