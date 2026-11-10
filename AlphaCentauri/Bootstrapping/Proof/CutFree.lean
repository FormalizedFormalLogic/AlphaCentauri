module

public import Foundation.Vorspiel.Tactic.Disj
public import AlphaCentauri.ToFoundation.Coding
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Coding

/-!
# Internal cut-free derivations

This module defines the cut-free fragment of Foundation's internal one-sided calculus.  It is a
separate least fixpoint so that cut-freeness remains a $\Delta_1$ property in every model of `𝗜𝚺₁`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

namespace CutFreeDerivation

variable (T)

/-- The one-step unfolding of cut-free derivability: `d` is a coded axiom leaf, a
`⊤`-introduction, an and/or/all/exists-introduction whose immediate subderivation(s) lie in
`C`, a weakening or shift of a derivation in `C`, or a `T`-axiom leaf — the clauses of Foundation's
`Derivation.Phi` with the cut clause omitted. -/
def Phi (C : Set V) (d : V) : Prop :=
  IsFormulaSet L (fstIdx d) ∧
  ( (∃ s p, d = axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
    (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
    (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧
      (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
    (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧
      fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
    (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧
      fstIdx dp = insert (free L p) (setShift L s) ∧ dp ∈ C) ∨
    (∃ s p t dp, d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧
      fstIdx dp = insert (substs1 L t p) s ∧ dp ∈ C) ∨
    (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
    (∃ s d', d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ d' ∈ C) ∨
    (∃ s p, d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) )

/-- A restatement of `Phi` in which each existential over `C` is bounded by `d`. -/
private lemma phi_iff (C d : V) :
    Phi T {x | x ∈ C} d ↔
    IsFormulaSet L (fstIdx d) ∧
    ( (∃ s < d, ∃ p < d, d = axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
      (∃ s < d, d = verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧
        (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        d = allIntro s p dp ∧ ^∀ p ∈ s ∧
        fstIdx dp = insert (free L p) (setShift L s) ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧
        fstIdx dp = insert (substs1 L t p) s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d, d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d, d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) ) := by
  constructor
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (⟨s, p, rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨s, p, q, dp, dq, rfl, h⟩ |
      ⟨s, p, q, dpq, rfl, h⟩ | ⟨s, p, dp, rfl, h⟩ | ⟨s, p, t, dp, rfl, h⟩ |
      ⟨s, d', rfl, h⟩ | ⟨s, d', rfl, h⟩ | ⟨s, p, rfl, h⟩)
    · left; exact ⟨s, by simp, p, by simp, rfl, h⟩
    · right; left; exact ⟨s, by simp, rfl, h⟩
    · right; right; left
      exact ⟨s, by simp, p, by simp, q, by simp, dp, by simp, dq, by simp, rfl, h⟩
    · right; right; right; left
      exact ⟨s, by simp, p, by simp, q, by simp, dpq, by simp, rfl, h⟩
    · right; right; right; right; left
      exact ⟨s, by simp, p, by simp, dp, by simp, rfl, h⟩
    · right; right; right; right; right; left
      exact ⟨s, by simp, p, by simp, t, by simp, dp, by simp, rfl, h⟩
    · right; right; right; right; right; right; left
      exact ⟨s, by simp, d', by simp, rfl, h⟩
    · right; right; right; right; right; right; right; left
      exact ⟨s, by simp, d', by simp, rfl, h⟩
    · right; right; right; right; right; right; right; right
      exact ⟨s, by simp, p, by simp, rfl, h⟩
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (⟨s, _, p, _, rfl, h⟩ | ⟨s, _, rfl, h⟩ |
      ⟨s, _, p, _, q, _, dp, _, dq, _, rfl, h⟩ | ⟨s, _, p, _, q, _, dpq, _, rfl, h⟩ |
      ⟨s, _, p, _, dp, _, rfl, h⟩ | ⟨s, _, p, _, t, _, dp, _, rfl, h⟩ |
      ⟨s, _, d', _, rfl, h⟩ | ⟨s, _, d', _, rfl, h⟩ | ⟨s, _, p, _, h⟩)
    · left; exact ⟨s, p, rfl, h⟩
    · right; left; exact ⟨s, rfl, h⟩
    · right; right; left; exact ⟨s, p, q, dp, dq, rfl, h⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, h⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, h⟩
    · right; right; right; right; right; left; exact ⟨s, p, t, dp, rfl, h⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, h⟩
    · right; right; right; right; right; right; right; left; exact ⟨s, d', rfl, h⟩
    · right; right; right; right; right; right; right; right; exact ⟨s, p, h⟩

/-- The $\Delta_1$ fixpoint blueprint of `Phi`. -/
noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “d C.
    (∃ fst, !fstIdxDef fst d ∧ !(isFormulaSet L).sigma fst) ∧
    ( (∃ s < d, ∃ p < d, !axLGraph d s p ∧ p ∈ s ∧ ∃ np, !(negGraph L) np p ∧ np ∈ s) ∨
      (∃ s < d, !verumIntroGraph d s ∧ ∃ vrm, !qqVerumDef vrm ∧ vrm ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        !andIntroGraph d s p q dp dq ∧ (∃ and, !qqAndDef and p q ∧ and ∈ s) ∧
          (∃ c, !fstIdxDef c dp ∧ !insertDef c p s ∧ dp ∈ C) ∧
          (∃ c, !fstIdxDef c dq ∧ !insertDef c q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        !orIntroGraph d s p q dpq ∧ (∃ or, !qqOrDef or p q ∧ or ∈ s) ∧
        ∃ c, !fstIdxDef c dpq ∧ ∃ c', !insertDef c' q s ∧ !insertDef c p c' ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        !allIntroGraph d s p dp ∧ (∃ all, !qqAllDef all p ∧ all ∈ s) ∧
        ∃ c, !fstIdxDef c dp ∧ ∃ fp, !(freeGraph L) fp p ∧ ∃ ss, !(setShiftGraph L) ss s ∧
        !insertDef c fp ss ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        !exsIntroGraph d s p t dp ∧ (∃ ex, !qqExsDef ex p ∧ ex ∈ s) ∧
        !(isSemiterm L).sigma 0 t ∧ ∃ c, !fstIdxDef c dp ∧ ∃ pt, !(substs1Graph L) pt t p ∧
        !insertDef c pt s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !wkRuleGraph d s d' ∧ ∃ c, !fstIdxDef c d' ∧ !bitSubsetDef c s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !shiftRuleGraph d s d' ∧ ∃ c, !fstIdxDef c d' ∧ !(setShiftGraph L) s c ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, !axmGraph d s p ∧ p ∈ s ∧ !T.Δ₁ch.sigma p) )”)
  (.mkPi “d C.
    (∀ fst, !fstIdxDef fst d → !(isFormulaSet L).pi fst) ∧
    ( (∃ s < d, ∃ p < d, !axLGraph d s p ∧ p ∈ s ∧ ∀ np, !(negGraph L) np p → np ∈ s) ∨
      (∃ s < d, !verumIntroGraph d s ∧ ∀ vrm, !qqVerumDef vrm → vrm ∈ s) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d,
        !andIntroGraph d s p q dp dq ∧ (∀ and, !qqAndDef and p q → and ∈ s) ∧
          (∀ c, !fstIdxDef c dp → !insertDef c p s ∧ dp ∈ C) ∧
          (∀ c, !fstIdxDef c dq → !insertDef c q s ∧ dq ∈ C)) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dpq < d,
        !orIntroGraph d s p q dpq ∧ (∀ or, !qqOrDef or p q → or ∈ s) ∧
        ∀ c, !fstIdxDef c dpq → ∀ c', !insertDef c' q s → !insertDef c p c' ∧ dpq ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ dp < d,
        !allIntroGraph d s p dp ∧ (∀ all, !qqAllDef all p → all ∈ s) ∧
        ∀ c, !fstIdxDef c dp → ∀ fp, !(freeGraph L) fp p → ∀ ss, !(setShiftGraph L) ss s →
          !insertDef c fp ss ∧ dp ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ dp < d,
        !exsIntroGraph d s p t dp ∧ (∀ ex, !qqExsDef ex p → ex ∈ s) ∧
        !(isSemiterm L).pi 0 t ∧
        ∀ c, !fstIdxDef c dp → ∀ pt, !(substs1Graph L) pt t p → !insertDef c pt s ∧ dp ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !wkRuleGraph d s d' ∧ ∀ c, !fstIdxDef c d' → !bitSubsetDef c s ∧ d' ∈ C) ∨
      (∃ s < d, ∃ d' < d,
        !shiftRuleGraph d s d' ∧ ∀ c, !fstIdxDef c d' → ∀ ss, !(setShiftGraph L) ss c →
          s = ss ∧ d' ∈ C) ∨
      (∃ s < d, ∃ p < d, !axmGraph d s p ∧ p ∈ s ∧ !T.Δ₁ch.pi p) )”)⟩

/-- `Phi` is $\Delta_1$-defined by `blueprint`. -/
lemma Phi_definable :
    𝚫ᴬ₁.Defined (fun v : Fin 2 → V ↦ Phi T {x | x ∈ v 1} (v 0)) (blueprint T).core := .mk <| by
  constructor
  · intro v; simp [blueprint]
  · intro v; simp [phi_iff, blueprint]

/-- The fixpoint construction realizing `blueprint`, whose least fixpoint is `CutFreeDerivation`. -/
def construction : Fixpoint.Construction V (blueprint T) where
  Φ := fun _ ↦ Phi T
  defined := Phi_definable _
  monotone := by
    rintro C C' hC _ d ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (h | h | ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC⟩, ⟨hq, hqC⟩⟩ |
      ⟨s, p, q, dpq, rfl, hpq, h, hdC⟩ | ⟨s, p, dp, rfl, hp, h, hdC⟩ |
      ⟨s, p, t, dp, rfl, hp, ht, h, hdC⟩ | ⟨s, d', rfl, ss, hdC⟩ |
      ⟨s, d', rfl, ss, hdC⟩ | ⟨s, p, h⟩)
    · left; exact h
    · right; left; exact h
    · right; right; left
      exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hC hpC⟩, ⟨hq, hC hqC⟩⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, hpq, h, hC hdC⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, hp, h, hC hdC⟩
    · right; right; right; right; right; left; exact ⟨s, p, t, dp, rfl, hp, ht, h, hC hdC⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hC hdC⟩
    · right; right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hC hdC⟩
    · right; right; right; right; right; right; right; right; exact ⟨s, p, h⟩

instance : (construction T).StrongFinite V where
  strong_finite := by
    rintro C _ d ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with (h | h | ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC⟩, ⟨hq, hqC⟩⟩ |
      ⟨s, p, q, dpq, rfl, hpq, h, hdC⟩ | ⟨s, p, dp, rfl, hp, h, hdC⟩ |
      ⟨s, p, t, dp, rfl, hp, ht, h, hdC⟩ | ⟨s, d', rfl, ss, hdC⟩ |
      ⟨s, d', rfl, ss, hdC⟩ | ⟨s, p, h⟩)
    · left; exact h
    · right; left; exact h
    · right; right; left
      exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hpC, by simp⟩, ⟨hq, hqC, by simp⟩⟩
    · right; right; right; left; exact ⟨s, p, q, dpq, rfl, hpq, h, hdC, by simp⟩
    · right; right; right; right; left; exact ⟨s, p, dp, rfl, hp, h, hdC, by simp⟩
    · right; right; right; right; right; left
      exact ⟨s, p, t, dp, rfl, hp, ht, h, hdC, by simp⟩
    · right; right; right; right; right; right; left; exact ⟨s, d', rfl, ss, hdC, by simp⟩
    · right; right; right; right; right; right; right; left
      exact ⟨s, d', rfl, ss, hdC, by simp⟩
    · right; right; right; right; right; right; right; right; exact ⟨s, p, h⟩

end CutFreeDerivation

/-- `CutFreeDerivation T d`: `d` codes a derivation of the cut-free fragment of the internal
one-sided (Tait-style) sequent calculus over the theory `T`, i.e. a derivation using none of the
cut rule.
- [Bus98, Ch. I §2.4] -/
def CutFreeDerivation (T : Theory L) [T.Δ₁] (d : V) : Prop :=
  (CutFreeDerivation.construction T).Fixpoint ![] d

/-- `CutFreeDerivationOf T d s`: `d` codes a cut-free derivation of `T` whose end-sequent is `s`. -/
def CutFreeDerivationOf (T : Theory L) [T.Δ₁] (d s : V) : Prop :=
  fstIdx d = s ∧ CutFreeDerivation T d

/-- `CutFreeDerivable T s`: the sequent `s` has some cut-free derivation over `T`. -/
def CutFreeDerivable (T : Theory L) [T.Δ₁] (s : V) : Prop := ∃ d, CutFreeDerivationOf T d s

/-- The $\Delta_1$ semisentence defining `CutFreeDerivation`. -/
noncomputable def cutFreeDerivation (T : Theory L) [T.Δ₁] : 𝚫ᴬ₁.Semisentence 1 :=
  (CutFreeDerivation.blueprint T).fixpointDefΔ₁

/-- The $\Delta_1$ semisentence defining `CutFreeDerivationOf`. -/
noncomputable def cutFreeDerivationOf (T : Theory L) [T.Δ₁] : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  (.mkSigma “d s. !fstIdxDef s d ∧ !(cutFreeDerivation T).sigma d”)
  (.mkPi “d s. !fstIdxDef s d ∧ !(cutFreeDerivation T).pi d”)

/-- The $\Sigma_1$ semisentence defining `CutFreeDerivable`. -/
noncomputable def cutFreeDerivable (T : Theory L) [T.Δ₁] : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “Γ. ∃ d, !(cutFreeDerivationOf T).sigma d Γ”

section

variable {Γ : SigmaPiDelta} {m : ℕ}

instance CutFreeDerivation.defined :
    𝚫ᴬ₁-Predicate[V] CutFreeDerivation T via cutFreeDerivation T :=
  (CutFreeDerivation.construction T).fixpoint_definedΔ₁

instance CutFreeDerivation.definable : 𝚫ᴬ₁-Predicate[V] CutFreeDerivation T :=
  CutFreeDerivation.defined.to_definable

instance CutFreeDerivation.definable' : Γᴬ_[m + 1]-Predicate[V] CutFreeDerivation T :=
  CutFreeDerivation.definable.of_deltaOne

instance CutFreeDerivationOf.defined :
    𝚫ᴬ₁-Relation[V] CutFreeDerivationOf T via cutFreeDerivationOf T := .mk
  ⟨by intro v; simp [cutFreeDerivationOf],
   by intro v; simp [cutFreeDerivationOf, eq_comm (b := fstIdx (v 0))]; rfl⟩

instance CutFreeDerivationOf.definable : 𝚫ᴬ₁-Relation[V] CutFreeDerivationOf T :=
  CutFreeDerivationOf.defined.to_definable

instance CutFreeDerivationOf.definable' : Γᴬ_[m + 1]-Relation[V] CutFreeDerivationOf T :=
  CutFreeDerivationOf.definable.of_deltaOne

instance CutFreeDerivable.defined :
    𝚺ᴬ₁-Predicate[V] CutFreeDerivable T via cutFreeDerivable T := .mk fun v ↦ by
  simp [cutFreeDerivable, CutFreeDerivable]

instance CutFreeDerivable.definable : 𝚺ᴬ₁-Predicate[V] CutFreeDerivable T :=
  CutFreeDerivable.defined.to_definable

instance CutFreeDerivable.definable' : 𝚺ᴬ_[0 + 1]-Predicate[V] CutFreeDerivable T :=
  CutFreeDerivable.definable

end

namespace CutFreeDerivation

/-- `CutFreeDerivation T d` unfolds one step: `d` is one of the cut-free rule applications (axiom
leaf, `⊤`-introduction, and/or/all/exists-introduction, weakening, shift, or a `T`-axiom leaf),
with its immediate subderivation(s) again cut-free. -/
lemma case_iff {d : V} :
    CutFreeDerivation T d ↔
    IsFormulaSet L (fstIdx d) ∧
    ( (∃ s p, d = axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
      (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧
        CutFreeDerivationOf T dp (insert p s) ∧ CutFreeDerivationOf T dq (insert q s)) ∨
      (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧
        CutFreeDerivationOf T dpq (insert p (insert q s))) ∨
      (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧
        CutFreeDerivationOf T dp (insert (free L p) (setShift L s))) ∨
      (∃ s p t dp, d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧
        CutFreeDerivationOf T dp (insert (substs1 L t p) s)) ∨
      (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ CutFreeDerivation T d') ∨
      (∃ s d', d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ CutFreeDerivation T d') ∨
      (∃ s p, d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) ) :=
  (construction T).case

alias ⟨case, _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.CutFreeDerivation.mk⟩ := case_iff

/-- Structural induction on cut-free derivations: to prove `P` for every `CutFreeDerivation T d`,
it suffices to prove it for each rule of the cut-free calculus (axiom leaf, `⊤`-introduction,
and/or/all/exists-introduction, weakening, shift, `T`-axiom leaf), assuming `P` for the
immediate subderivation(s).
- [Bus98, Ch. I §2.4] -/
lemma induction1 (Γ : Polarity) {P : V → Prop} (hP : Γᴬ_[1]-Predicate P)
    {d} (hd : CutFreeDerivation T d)
    (hAxL : ∀ s, IsFormulaSet L s → ∀ p ∈ s, neg L p ∈ s → P (axL s p))
    (hVerumIntro : ∀ s, IsFormulaSet L s → ^⊤ ∈ s → P (verumIntro s))
    (hAnd : ∀ s, IsFormulaSet L s → ∀ p q dp dq, p ^⋏ q ∈ s →
      CutFreeDerivationOf T dp (insert p s) → CutFreeDerivationOf T dq (insert q s) →
      P dp → P dq → P (andIntro s p q dp dq))
    (hOr : ∀ s, IsFormulaSet L s → ∀ p q d, p ^⋎ q ∈ s →
      CutFreeDerivationOf T d (insert p (insert q s)) → P d → P (orIntro s p q d))
    (hAll : ∀ s, IsFormulaSet L s → ∀ p d, ^∀ p ∈ s →
      CutFreeDerivationOf T d (insert (free L p) (setShift L s)) → P d → P (allIntro s p d))
    (hExs : ∀ s, IsFormulaSet L s → ∀ p t d, ^∃ p ∈ s → IsTerm L t →
      CutFreeDerivationOf T d (insert (substs1 L t p) s) → P d → P (exsIntro s p t d))
    (hWk : ∀ s, IsFormulaSet L s → ∀ d, fstIdx d ⊆ s → CutFreeDerivation T d →
      P d → P (wkRule s d))
    (hShift : ∀ s, IsFormulaSet L s → ∀ d, s = setShift L (fstIdx d) → CutFreeDerivation T d →
      P d → P (shiftRule s d))
    (hRoot : ∀ s, IsFormulaSet L s → ∀ p, p ∈ s → p ∈ T.Δ₁Class → P (axm s p)) : P d :=
  (construction T).induction (v := ![]) hP (by
    intro C ih d hd
    rcases hd with ⟨hds,
      (⟨s, p, rfl, hps, hnps⟩ | ⟨s, rfl, hs⟩ |
        ⟨s, p, q, dp, dq, rfl, hpq, h₁, h₂⟩ | ⟨s, p, q, d, rfl, hpq, h⟩ |
        ⟨s, p, d, rfl, hp, h, hC⟩ | ⟨s, p, t, d, rfl, hp, ht, h, hC⟩ |
        ⟨s, d, rfl, h, hC⟩ | ⟨s, d, rfl, h, hC⟩ | ⟨s, p, rfl, hs, hT⟩)⟩
    · exact hAxL s (by simpa using hds) p hps hnps
    · exact hVerumIntro s (by simpa using hds) hs
    · exact hAnd s (by simpa using hds) p q dp dq hpq
        ⟨h₁.1, (ih dp h₁.2).1⟩ ⟨h₂.1, (ih dq h₂.2).1⟩ (ih dp h₁.2).2 (ih dq h₂.2).2
    · exact hOr s (by simpa using hds) p q d hpq ⟨h.1, (ih d h.2).1⟩ (ih d h.2).2
    · exact hAll s (by simpa using hds) p d hp ⟨h, (ih d hC).1⟩ (ih d hC).2
    · exact hExs s (by simpa using hds) p t d hp ht ⟨h, (ih d hC).1⟩ (ih d hC).2
    · exact hWk s (by simpa using hds) d h (ih d hC).1 (ih d hC).2
    · exact hShift s (by simpa using hds) d h (ih d hC).1 (ih d hC).2
    · exact hRoot s (by simpa using hds) p hs hT) d hd

/-- The end-sequent of a cut-free derivation is a coded formula set. -/
lemma isFormulaSet {d : V} (h : CutFreeDerivation T d) : IsFormulaSet L (fstIdx d) := h.case.1

/-- The sequent of a `CutFreeDerivationOf` witness is a coded formula set. -/
lemma _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.CutFreeDerivationOf.isFormulaSet {d s : V}
    (h : CutFreeDerivationOf T d s) : IsFormulaSet L s := by
  simpa [h.1] using h.2.case.1

/-- An axiom leaf `axL s p` is a cut-free derivation of `s` whenever `s` contains both `p` and its
negation. -/
lemma axL {s p : V} (hs : IsFormulaSet L s) (h : p ∈ s) (hn : neg L p ∈ s) :
    CutFreeDerivation T (axL s p) :=
  CutFreeDerivation.mk ⟨by simpa using hs, Or.inl ⟨s, p, rfl, h, hn⟩⟩

/-- A `⊤`-introduction leaf `verumIntro s` is a cut-free derivation of `s` whenever `s` contains
`⊤`. -/
lemma verumIntro {s : V} (hs : IsFormulaSet L s) (h : ^⊤ ∈ s) :
    CutFreeDerivation T (verumIntro s) :=
  CutFreeDerivation.mk ⟨by simpa using hs, by disj 2; exact ⟨s, rfl, h⟩⟩

/-- An and-introduction `andIntro s p q dp dq` is a cut-free derivation of `s` whenever `s`
contains `p ^⋏ q` and `dp`, `dq` cut-free derive `s` extended by `p`, respectively `q`. -/
lemma andIntro {s p q dp dq : V} (h : p ^⋏ q ∈ s)
    (hdp : CutFreeDerivationOf T dp (insert p s)) (hdq : CutFreeDerivationOf T dq (insert q s)) :
    CutFreeDerivation T (andIntro s p q dp dq) :=
  CutFreeDerivation.mk
    ⟨by simp only [fstIdx_andIntro]; intro r hr; exact hdp.isFormulaSet r (by simp [hr]),
      by disj 3; exact ⟨s, p, q, dp, dq, rfl, h, hdp, hdq⟩⟩

/-- An or-introduction `orIntro s p q dpq` is a cut-free derivation of `s` whenever `s` contains
`p ^⋎ q` and `dpq` cut-free derives `s` extended by both `p` and `q`. -/
lemma orIntro {s p q dpq : V} (h : p ^⋎ q ∈ s)
    (hdpq : CutFreeDerivationOf T dpq (insert p (insert q s))) :
    CutFreeDerivation T (orIntro s p q dpq) :=
  CutFreeDerivation.mk
    ⟨by simp only [fstIdx_orIntro]; intro r hr; exact hdpq.isFormulaSet r (by simp [hr]),
      by disj 4; exact ⟨s, p, q, dpq, rfl, h, hdpq⟩⟩

/-- An all-introduction `allIntro s p dp` is a cut-free derivation of `s` whenever `s` contains
`^∀ p` and `dp` cut-free derives the shifted sequent extended by the free instance of `p`. -/
lemma allIntro {s p dp : V} (h : ^∀ p ∈ s)
    (hdp : CutFreeDerivationOf T dp (insert (free L p) (setShift L s))) :
    CutFreeDerivation T (allIntro s p dp) :=
  CutFreeDerivation.mk
    ⟨by simp only [fstIdx_allIntro]; intro q hq
        simpa using hdp.isFormulaSet (shift L q) (by simp [shift_mem_setShift hq]),
      by disj 5; exact ⟨s, p, dp, rfl, h, hdp⟩⟩

/-- An exists-introduction `exsIntro s p t dp` is a cut-free derivation of `s` whenever `s`
contains `^∃ p`, `t` is a term, and `dp` cut-free derives `s` extended by the instance of `p` at
`t`. -/
lemma exsIntro {s p t dp : V} (h : ^∃ p ∈ s) (ht : IsTerm L t)
    (hdp : CutFreeDerivationOf T dp (insert (substs1 L t p) s)) :
    CutFreeDerivation T (exsIntro s p t dp) :=
  CutFreeDerivation.mk
    ⟨by simp only [fstIdx_exsIntro]; intro q hq; exact hdp.isFormulaSet q (by simp [hq]),
      by disj 6; exact ⟨s, p, t, dp, rfl, h, ht, hdp⟩⟩

/-- A weakening `wkRule s d` is a cut-free derivation of `s` whenever `d` cut-free derives some
subset `s'` of `s`. -/
lemma wkRule {s s' d : V} (hs : IsFormulaSet L s) (h : s' ⊆ s)
    (hd : CutFreeDerivationOf T d s') : CutFreeDerivation T (wkRule s d) :=
  CutFreeDerivation.mk
    ⟨by simpa using hs,
      by disj 7; exact ⟨s, d, rfl, by simp [hd.1, h], hd.2⟩⟩

/-- A shift `shiftRule (setShift L s) d` is a cut-free derivation of the shifted sequent whenever
`d` cut-free derives `s`. -/
lemma shiftRule {s d : V} (hd : CutFreeDerivationOf T d s) :
    CutFreeDerivation T (shiftRule (setShift L s) d) :=
  CutFreeDerivation.mk
    ⟨by simp [hd.isFormulaSet],
      by disj 8; exact ⟨setShift L s, d, rfl, by simp [hd.1], hd.2⟩⟩

/-- An axiom-set leaf `axm s p` is a cut-free derivation of `s` whenever `s` contains `p` and `p`
is (the code of) an axiom of `T`. -/
lemma axm {s p : V} (hs : IsFormulaSet L s) (hp : p ∈ s) (hT : p ∈ T.Δ₁Class) :
    CutFreeDerivation T (axm s p) :=
  CutFreeDerivation.mk
    ⟨by simpa using hs,
      by disj 9; exact ⟨s, p, rfl, hp, hT⟩⟩

variable {U : Theory L} [U.Δ₁]

/-- Cut-free derivability is monotone in the theory: enlarging the set of $\Delta_1$-axioms
preserves cut-free derivations. -/
lemma of_ss (h : T.Δ₁Class (V := V) ⊆ U.Δ₁Class) {d : V} :
    CutFreeDerivation T d → CutFreeDerivation U d := by
  intro hd
  apply CutFreeDerivation.induction1 𝚺 ?_ hd
  · intro s hs p hp hn
    exact CutFreeDerivation.axL hs hp hn
  · intro s hs hv
    exact CutFreeDerivation.verumIntro hs hv
  · intro s _ p q dp dq hpq hdp hdq ihp ihq
    exact CutFreeDerivation.andIntro hpq ⟨hdp.1, ihp⟩ ⟨hdq.1, ihq⟩
  · intro s _ p q d hpq hd ih
    exact CutFreeDerivation.orIntro hpq ⟨hd.1, ih⟩
  · intro s _ p d hp hd ih
    exact CutFreeDerivation.allIntro hp ⟨hd.1, ih⟩
  · intro s _ p t d hp ht hd ih
    exact CutFreeDerivation.exsIntro hp ht ⟨hd.1, ih⟩
  · intro s hs d hsd _ ih
    exact CutFreeDerivation.wkRule hs hsd ⟨rfl, ih⟩
  · rintro _ _ d rfl _ ih
    exact CutFreeDerivation.shiftRule ⟨rfl, ih⟩
  · intro s hs p hp hT
    exact CutFreeDerivation.axm hs hp (h hT)
  · definability

/-- Every cut-free derivation is in particular a derivation of Foundation's full calculus, which
additionally allows the cut rule. -/
lemma toDerivation {d : V} : CutFreeDerivation T d → Derivation T d := by
  intro hd
  apply CutFreeDerivation.induction1 𝚺 ?_ hd
  · intro s hs p hp hn; exact Derivation.axL hs hp hn
  · intro s hs hv; exact Derivation.verumIntro hs hv
  · intro s _ p q dp dq hpq hdp hdq ihp ihq
    exact Derivation.andIntro hpq ⟨hdp.1, ihp⟩ ⟨hdq.1, ihq⟩
  · intro s _ p q d hpq hd ih; exact Derivation.orIntro hpq ⟨hd.1, ih⟩
  · intro s _ p d hp hd ih; exact Derivation.allIntro hp ⟨hd.1, ih⟩
  · intro s _ p t d hp ht hd ih; exact Derivation.exsIntro hp ht ⟨hd.1, ih⟩
  · intro s hs d h _ ih; exact Derivation.wkRule hs h ⟨rfl, ih⟩
  · rintro s _ d rfl _ ih; exact Derivation.shiftRule ⟨rfl, ih⟩
  · intro s hs p hps hpT; exact Derivation.axm hs hps hpT
  · definability

end CutFreeDerivation

namespace CutFreeDerivable

/-- A cut-free-derivable sequent is a coded formula set. -/
lemma isFormulaSet {s : V} (h : CutFreeDerivable T s) : IsFormulaSet L s := by
  rcases h with ⟨d, hd⟩
  exact hd.isFormulaSet

/-- Cut-free derivability is closed under weakening. -/
lemma wk {s s' : V} (hs : IsFormulaSet L s) (h : s' ⊆ s) (hd : CutFreeDerivable T s') :
    CutFreeDerivable T s := by
  obtain ⟨d, hd⟩ := hd
  exact ⟨_, by simp, CutFreeDerivation.wkRule hs h hd⟩

lemma em {s : V} (hs : IsFormulaSet L s) (p : V) (h : p ∈ s) (hn : neg L p ∈ s) :
    CutFreeDerivable T s :=
  ⟨_, by simp, CutFreeDerivation.axL hs h hn⟩

lemma verum {s : V} (hs : IsFormulaSet L s) (h : ^⊤ ∈ s) : CutFreeDerivable T s :=
  ⟨_, by simp, CutFreeDerivation.verumIntro hs h⟩

lemma and_m {s p q : V} (h : p ^⋏ q ∈ s) (hp : CutFreeDerivable T (insert p s))
    (hq : CutFreeDerivable T (insert q s)) : CutFreeDerivable T s := by
  obtain ⟨dp, hdp⟩ := hp
  obtain ⟨dq, hdq⟩ := hq
  exact ⟨_, by simp, CutFreeDerivation.andIntro h hdp hdq⟩

lemma or_m {s p q : V} (h : p ^⋎ q ∈ s) (hpq : CutFreeDerivable T (insert p (insert q s))) :
    CutFreeDerivable T s := by
  obtain ⟨d, hd⟩ := hpq
  exact ⟨_, by simp, CutFreeDerivation.orIntro h hd⟩

lemma all_m {s p : V} (h : ^∀ p ∈ s)
    (hp : CutFreeDerivable T (insert (free L p) (setShift L s))) : CutFreeDerivable T s := by
  obtain ⟨d, hd⟩ := hp
  exact ⟨_, by simp, CutFreeDerivation.allIntro h hd⟩

lemma ex_m {s p t : V} (h : ^∃ p ∈ s) (ht : IsTerm L t)
    (hp : CutFreeDerivable T (insert (substs1 L t p) s)) : CutFreeDerivable T s := by
  obtain ⟨d, hd⟩ := hp
  exact ⟨_, by simp, CutFreeDerivation.exsIntro h ht hd⟩

lemma shift_m {s : V} (hd : CutFreeDerivable T s) : CutFreeDerivable T (setShift L s) := by
  obtain ⟨d, hd⟩ := hd
  exact ⟨_, by simp, CutFreeDerivation.shiftRule hd⟩

/-- A cut-free-derivable sequent is derivable in Foundation's full calculus. -/
lemma toDerivable {s : V} : CutFreeDerivable T s → Derivable T s := by
  rintro ⟨d, hd⟩
  exact ⟨d, hd.1, hd.2.toDerivation⟩

end CutFreeDerivable

end FFL.FirstOrder.Arithmetic.Bootstrapping
