module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding

/-!
# Internal cut-free derivations

This module defines the cut-free fragment of Foundation's internal one-sided calculus.  It is a
separate least fixpoint so that cut-freeness remains a `Δ₁` property in every model of `𝗜𝚺₁`.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

namespace CutFreeDerivation

variable (T)

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

lemma Phi_definable :
    𝚫₁.Defined (fun v : Fin 2 → V ↦ Phi T {x | x ∈ v 1} (v 0)) (blueprint T).core := .mk <| by
  constructor
  · intro v; simp [blueprint]
  · intro v; simp [phi_iff, blueprint]

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

def CutFreeDerivation (T : Theory L) [T.Δ₁] (d : V) : Prop :=
  (CutFreeDerivation.construction T).Fixpoint ![] d

def CutFreeDerivationOf (T : Theory L) [T.Δ₁] (d s : V) : Prop :=
  fstIdx d = s ∧ CutFreeDerivation T d

def CutFreeDerivable (T : Theory L) [T.Δ₁] (s : V) : Prop := ∃ d, CutFreeDerivationOf T d s

noncomputable def cutFreeDerivation (T : Theory L) [T.Δ₁] : 𝚫₁.Semisentence 1 :=
  (CutFreeDerivation.blueprint T).fixpointDefΔ₁

noncomputable def cutFreeDerivationOf (T : Theory L) [T.Δ₁] : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d s. !fstIdxDef s d ∧ !(cutFreeDerivation T).sigma d”)
  (.mkPi “d s. !fstIdxDef s d ∧ !(cutFreeDerivation T).pi d”)

noncomputable def cutFreeDerivable (T : Theory L) [T.Δ₁] : 𝚺₁.Semisentence 1 := .mkSigma
  “Γ. ∃ d, !(cutFreeDerivationOf T).sigma d Γ”

section

instance CutFreeDerivation.defined :
    𝚫₁-Predicate[V] CutFreeDerivation T via cutFreeDerivation T :=
  (CutFreeDerivation.construction T).fixpoint_definedΔ₁

instance CutFreeDerivation.definable : 𝚫₁-Predicate[V] CutFreeDerivation T :=
  CutFreeDerivation.defined.to_definable

instance CutFreeDerivation.definable' : Γ-[m + 1]-Predicate[V] CutFreeDerivation T :=
  CutFreeDerivation.definable.of_deltaOne

instance CutFreeDerivationOf.defined :
    𝚫₁-Relation[V] CutFreeDerivationOf T via cutFreeDerivationOf T := .mk
  ⟨by intro v; simp [cutFreeDerivationOf],
   by intro v; simp [cutFreeDerivationOf, eq_comm (b := fstIdx (v 0))]; rfl⟩

instance CutFreeDerivationOf.definable : 𝚫₁-Relation[V] CutFreeDerivationOf T :=
  CutFreeDerivationOf.defined.to_definable

instance CutFreeDerivationOf.definable' : Γ-[m + 1]-Relation[V] CutFreeDerivationOf T :=
  CutFreeDerivationOf.definable.of_deltaOne

instance CutFreeDerivable.defined :
    𝚺₁-Predicate[V] CutFreeDerivable T via cutFreeDerivable T := .mk fun v ↦ by
  simp [cutFreeDerivable, CutFreeDerivable]

instance CutFreeDerivable.definable : 𝚺₁-Predicate[V] CutFreeDerivable T :=
  CutFreeDerivable.defined.to_definable

instance CutFreeDerivable.definable' : 𝚺-[0 + 1]-Predicate[V] CutFreeDerivable T :=
  CutFreeDerivable.definable

end

namespace CutFreeDerivation

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

alias ⟨case, _root_.LO.FirstOrder.Arithmetic.Bootstrapping.CutFreeDerivation.mk⟩ := case_iff

lemma induction1 (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
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

lemma isFormulaSet {d : V} (h : CutFreeDerivation T d) : IsFormulaSet L (fstIdx d) := h.case.1

lemma _root_.LO.FirstOrder.Arithmetic.Bootstrapping.CutFreeDerivationOf.isFormulaSet {d s : V}
    (h : CutFreeDerivationOf T d s) : IsFormulaSet L s := by
  simpa [h.1] using h.2.case.1

lemma axL {s p : V} (hs : IsFormulaSet L s) (h : p ∈ s) (hn : neg L p ∈ s) :
    CutFreeDerivation T (axL s p) :=
  CutFreeDerivation.mk ⟨by simpa using hs, Or.inl ⟨s, p, rfl, h, hn⟩⟩

lemma verumIntro {s : V} (hs : IsFormulaSet L s) (h : ^⊤ ∈ s) :
    CutFreeDerivation T (verumIntro s) :=
  CutFreeDerivation.mk ⟨by simpa using hs, Or.inr <| Or.inl ⟨s, rfl, h⟩⟩

lemma andIntro {s p q dp dq : V} (h : p ^⋏ q ∈ s)
    (hdp : CutFreeDerivationOf T dp (insert p s)) (hdq : CutFreeDerivationOf T dq (insert q s)) :
    CutFreeDerivation T (andIntro s p q dp dq) :=
  CutFreeDerivation.mk
    ⟨by simp only [fstIdx_andIntro]; intro r hr; exact hdp.isFormulaSet r (by simp [hr]),
      Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dp, dq, rfl, h, hdp, hdq⟩⟩

lemma orIntro {s p q dpq : V} (h : p ^⋎ q ∈ s)
    (hdpq : CutFreeDerivationOf T dpq (insert p (insert q s))) :
    CutFreeDerivation T (orIntro s p q dpq) :=
  CutFreeDerivation.mk
    ⟨by simp only [fstIdx_orIntro]; intro r hr; exact hdpq.isFormulaSet r (by simp [hr]),
      Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dpq, rfl, h, hdpq⟩⟩

lemma allIntro {s p dp : V} (h : ^∀ p ∈ s)
    (hdp : CutFreeDerivationOf T dp (insert (free L p) (setShift L s))) :
    CutFreeDerivation T (allIntro s p dp) :=
  CutFreeDerivation.mk
    ⟨by simp only [fstIdx_allIntro]; intro q hq
        simpa using hdp.isFormulaSet (shift L q) (by simp [shift_mem_setShift hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, dp, rfl, h, hdp⟩⟩

lemma exsIntro {s p t dp : V} (h : ^∃ p ∈ s) (ht : IsTerm L t)
    (hdp : CutFreeDerivationOf T dp (insert (substs1 L t p) s)) :
    CutFreeDerivation T (exsIntro s p t dp) :=
  CutFreeDerivation.mk
    ⟨by simp only [fstIdx_exsIntro]; intro q hq; exact hdp.isFormulaSet q (by simp [hq]),
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, t, dp, rfl, h, ht, hdp⟩⟩

lemma wkRule {s s' d : V} (hs : IsFormulaSet L s) (h : s' ⊆ s)
    (hd : CutFreeDerivationOf T d s') : CutFreeDerivation T (wkRule s d) :=
  CutFreeDerivation.mk
    ⟨by simpa using hs,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨s, d, rfl, by simp [hd.1, h], hd.2⟩⟩

lemma shiftRule {s d : V} (hd : CutFreeDerivationOf T d s) :
    CutFreeDerivation T (shiftRule (setShift L s) d) :=
  CutFreeDerivation.mk
    ⟨by simp [hd.isFormulaSet],
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨setShift L s, d, rfl, by simp [hd.1], hd.2⟩⟩

lemma axm {s p : V} (hs : IsFormulaSet L s) (hp : p ∈ s) (hT : p ∈ T.Δ₁Class) :
    CutFreeDerivation T (axm s p) :=
  CutFreeDerivation.mk
    ⟨by simpa using hs,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
        ⟨s, p, rfl, hp, hT⟩⟩

variable {U : Theory L} [U.Δ₁]

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

lemma isFormulaSet {s : V} (h : CutFreeDerivable T s) : IsFormulaSet L s := by
  rcases h with ⟨d, hd⟩
  exact hd.isFormulaSet

lemma toDerivable {s : V} : CutFreeDerivable T s → Derivable T s := by
  rintro ⟨d, hd⟩
  exact ⟨d, hd.1, hd.2.toDerivation⟩

end CutFreeDerivable

namespace Derivation

lemma mem_deltaClass_ofList_iff (l : List (Sentence L)) (p : V) :
    p ∈ @Theory.Δ₁Class V _ L _ _ {p | p ∈ l} (Theory.Δ₁.ofList l) ↔
      ∃ σ ∈ l, p = (⌜σ⌝ : V) := by
  induction l with
  | nil =>
    change False ↔ ∃ σ ∈ ([] : List (Sentence L)), p = (⌜σ⌝ : V)
    simp
  | cons σ l ih =>
    change V ⊧/![p] (((Theory.Δ₁.singleton σ).add
      (Theory.Δ₁.ofList l)).ch).val ↔
      ∃ τ ∈ σ :: l, p = (⌜τ⌝ : V)
    change V ⊧/![p] (((Theory.Δ₁.singleton σ).ch ⋎
      (Theory.Δ₁.ofList l).ch).val) ↔
      ∃ τ ∈ σ :: l, p = (⌜τ⌝ : V)
    simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or,
      LogicalConnective.Prop.or_eq]
    rw [Theory.Δ₁.singleton_toTDef_ch_val]
    have ih' : V ⊧/![p] (Theory.Δ₁.ofList l).ch.val ↔
        ∃ τ ∈ l, p = (⌜τ⌝ : V) := ih
    rw [ih']
    simp [Sentence.quote_eq_encode, numeral_eq_natCast]

theorem deductionAux {a d : V} (ha : IsFormulaSet L a) (hsa : setShift L a = a)
    (hax : ∀ p, p ∈ T.Δ₁Class → neg L p ∈ a) (hd : Derivation T d) :
    ∃ d', Derivation (∅ : Theory L) d' ∧ fstIdx d' = fstIdx d ∪ a := by
  have insert_union (x s : V) : insert x s ∪ a = insert x (s ∪ a) := by
    apply mem_ext
    intro z
    simp only [mem_cup_iff, mem_bitInsert_iff]
    tauto
  apply Derivation.induction1 SigmaSymbol.sigma (P := fun d ↦
      ∃ d', Derivation (∅ : Theory L) d' ∧ fstIdx d' = fstIdx d ∪ a) (by definability) hd
  · intro s hs p hp hnp
    exact ⟨Bootstrapping.axL (s ∪ a) p,
      Derivation.axL (by simp [hs, ha]) (by simp [hp]) (by simp [hnp]), by simp⟩
  · intro s hs hv
    exact ⟨Bootstrapping.verumIntro (s ∪ a),
      Derivation.verumIntro (by simp [hs, ha]) (by simp [hv]), by simp⟩
  · intro s _ p q dp dq hpq hdp hdq ihp ihq
    obtain ⟨dp', hdp', edp⟩ := ihp
    obtain ⟨dq', hdq', edq⟩ := ihq
    refine ⟨Bootstrapping.andIntro (s ∪ a) p q dp' dq',
      Derivation.andIntro (by simp [hpq]) ?_ ?_, by simp⟩
    · exact ⟨by rw [edp, hdp.1, insert_union], hdp'⟩
    · exact ⟨by rw [edq, hdq.1, insert_union], hdq'⟩
  · intro s _ p q dp hpq hdp ih
    obtain ⟨dp', hdp', edp⟩ := ih
    refine ⟨Bootstrapping.orIntro (s ∪ a) p q dp',
      Derivation.orIntro (by simp [hpq]) ?_, by simp⟩
    exact ⟨by rw [edp, hdp.1, insert_union, insert_union], hdp'⟩
  · intro s _ p dp hp hdp ih
    obtain ⟨dp', hdp', edp⟩ := ih
    refine ⟨Bootstrapping.allIntro (s ∪ a) p dp',
      Derivation.allIntro (by simp [hp]) ?_, by simp⟩
    exact ⟨by rw [edp, hdp.1, insert_union, mem_setShift_union, hsa], hdp'⟩
  · intro s _ p t dp hp ht hdp ih
    obtain ⟨dp', hdp', edp⟩ := ih
    refine ⟨Bootstrapping.exsIntro (s ∪ a) p t dp',
      Derivation.exsIntro (by simp [hp]) ht ?_, by simp⟩
    exact ⟨by rw [edp, hdp.1, insert_union], hdp'⟩
  · intro s hs d hsd _ ih
    obtain ⟨d', hd', ed⟩ := ih
    have hsub : fstIdx d' ⊆ s ∪ a := by
      rw [ed]
      intro p hp
      rcases mem_cup_iff.mp hp with hp | hp
      · exact mem_cup_iff.mpr (Or.inl (hsd hp))
      · exact mem_cup_iff.mpr (Or.inr hp)
    exact ⟨Bootstrapping.wkRule (s ∪ a) d',
      Derivation.wkRule (by simp [hs, ha]) hsub ⟨rfl, hd'⟩,
      by simp⟩
  · rintro _ _ d rfl _ ih
    obtain ⟨d', hd', ed⟩ := ih
    refine ⟨Bootstrapping.shiftRule (setShift L (fstIdx d ∪ a)) d', ?_, ?_⟩
    · exact Derivation.shiftRule ⟨ed, hd'⟩
    · simp [mem_setShift_union, hsa]
  · intro s _ p d₁ d₂ hd₁ hd₂ ih₁ ih₂
    obtain ⟨d₁', hd₁', ed₁⟩ := ih₁
    obtain ⟨d₂', hd₂', ed₂⟩ := ih₂
    refine ⟨Bootstrapping.cutRule (s ∪ a) p d₁' d₂', Derivation.cutRule ?_ ?_, by simp⟩
    · exact ⟨by rw [ed₁, hd₁.1, insert_union], hd₁'⟩
    · exact ⟨by rw [ed₂, hd₂.1, insert_union], hd₂'⟩
  · intro s hs p hp hT
    exact ⟨Bootstrapping.axL (s ∪ a) p,
      Derivation.axL (by simp [hs, ha]) (by simp [hp])
      (by simp [hax p hT]), by simp⟩

section Deduction

variable [L.DecidableEq]

/-- The finite sequent consisting of the negations of the listed axioms.
- [HP98, Section I.4(a)] -/
noncomputable def negatedAxioms (l : List (Sentence L)) : Finset (Proposition L) :=
  l.toFinset.image fun σ : Sentence L ↦ ∼(↑σ : Proposition L)

/-- The finite sequent consisting of the negations of the axioms in a finite set.
- [HP98, Section I.4(a)] -/
noncomputable def negatedAxiomsFinset (F : Finset (Sentence L)) : Finset (Proposition L) :=
  F.image fun σ : Sentence L ↦ ∼(↑σ : Proposition L)

/-- The internal deduction transform replaces every axiom leaf by an excluded-middle leaf and
adjoins the negations of the finite list of axioms to every sequent.
- [HP98, Section I.4(a)] -/
theorem deduction (l : List (Sentence L)) {d : V} :
    let _ : Theory.Δ₁ {p | p ∈ l} := Theory.Δ₁.ofList l
    Derivation {p | p ∈ l} d →
      ∃ d', Derivation (∅ : Theory L) d' ∧
        fstIdx d' = fstIdx d ∪ (⌜negatedAxioms l⌝ : V) := by
  let _ : Theory.Δ₁ {p | p ∈ l} := Theory.Δ₁.ofList l
  dsimp only
  intro hd
  apply deductionAux (T := {p | p ∈ l}) (a := (⌜negatedAxioms l⌝ : V))
  · exact Derivation2.formulaSet_quote_finset _
  · rw [Derivation2.setShift_quote]
    congr 1
    ext p
    have hshift (σ : Sentence L) :
        Rewriting.shift (↑σ : Proposition L) = (↑σ : Proposition L) := by simp
    simp [negatedAxioms, hshift]
  · intro p hp
    rw [mem_deltaClass_ofList_iff l p] at hp
    obtain ⟨σ, hσ, rfl⟩ := hp
    have hneg : neg L (⌜σ⌝ : V) = (⌜∼(↑σ : Proposition L)⌝ : V) := by
      exact congrArg (fun q : Bootstrapping.Formula V L ↦ q.val)
        (Semiformula.typedQuote_neg (V := V) (↑σ : Proposition L)).symm
    rw [hneg]
    exact (Derivation2.Sequent.mem_quote_iff (V := V)).mpr
      (show ∼(↑σ : Proposition L) ∈ negatedAxioms l by simp [negatedAxioms, hσ])
  · exact hd

/-- The internal deduction transform for a finite set of axioms.  The explicit `ofList`
presentation is definitionally the same classifier as the corresponding finite theory, while
avoiding proof-dependent reduction through `Set.Finite.toFinset`.
- [HP98, Section I.4(a)] -/
theorem deductionFinset (F : Finset (Sentence L)) {d : V} :
    let _ : Theory.Δ₁ {p | p ∈ F} :=
      (Theory.Δ₁.ofList F.toList).ofEq (by ext; simp)
    Derivation {p | p ∈ F} d →
      ∃ d', Derivation (∅ : Theory L) d' ∧
        fstIdx d' = fstIdx d ∪ (⌜negatedAxiomsFinset F⌝ : V) := by
  let _ : Theory.Δ₁ {p | p ∈ F} :=
    (Theory.Δ₁.ofList F.toList).ofEq (by ext; simp)
  dsimp only
  intro hd
  simpa [negatedAxiomsFinset, negatedAxioms] using
    (deduction (V := V) F.toList hd)

/-- Provability from a finite list of axioms yields a pure derivation after adjoining their
negations to the end sequent.
- [HP98, Section I.4(a)] -/
theorem provable_deduction (l : List (Sentence L)) {p : V} :
    let _ : Theory.Δ₁ {q | q ∈ l} := Theory.Δ₁.ofList l
    Provable {q | q ∈ l} p →
      Derivable (∅ : Theory L) (insert p (⌜negatedAxioms l⌝ : V)) := by
  let _ : Theory.Δ₁ {q | q ∈ l} := Theory.Δ₁.ofList l
  dsimp only
  rintro ⟨d, hd⟩
  obtain ⟨d', hd', heq⟩ := deduction l hd.2
  have heq' : fstIdx d' = insert p (⌜negatedAxioms l⌝ : V) := by
    rw [heq, hd.1]
    apply mem_ext
    intro x
    simp only [mem_cup_iff, mem_singleton_iff, mem_bitInsert_iff]
  exact ⟨d', heq', hd'⟩

/-- Provability from a finite set of axioms yields a pure derivation after adjoining their
negations to the end sequent.
- [HP98, Section I.4(a)] -/
theorem provable_deductionFinset (F : Finset (Sentence L)) {p : V} :
    let _ : Theory.Δ₁ {q | q ∈ F} :=
      (Theory.Δ₁.ofList F.toList).ofEq (by ext; simp)
    Provable {q | q ∈ F} p →
      Derivable (∅ : Theory L) (insert p (⌜negatedAxiomsFinset F⌝ : V)) := by
  let _ : Theory.Δ₁ {q | q ∈ F} :=
    (Theory.Δ₁.ofList F.toList).ofEq (by ext; simp)
  dsimp only
  intro hp
  simpa [negatedAxiomsFinset, negatedAxioms] using
    (provable_deduction (V := V) F.toList hp)

end Deduction

end Derivation

end LO.FirstOrder.Arithmetic.Bootstrapping
