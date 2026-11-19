module

public import AlphaCentauri.ToFoundation.FirstOrder.ConstantExtension
public import Foundation.FirstOrder.LK.Completeness.CounterModel

/-! # Types

A type over a structure `M` is a set of formulas in the free variables $\bar x$, with parameters
from `M`, that is finitely satisfied in `M`. The variables $\bar x$ are the bound variables of the
formulas, and the parameters are their free variables, read in `M` by a valuation.

A type over a theory `T` is a set $\Phi(\bar x)$ of formulas such that $T + \Phi(\bar c)$ is
consistent for new constants $\bar c$. A type over a theory is one realized in some model of the
theory, and a type over `M` with parameters $\bar b$ is a type over the theory of $(M, \bar b)$.
-/

@[expose] public section

namespace FFL.FirstOrder

open Semiformula

/-- A set of formulas of `L` in `k` variables with parameters indexed by `ξ`: the shape of a
$k$-type.
- [Kay91, §8.1] -/
abbrev Semitype (L : Language) (ξ : Type*) (k : ℕ) := Set (Semiformula L ξ k)

variable {L : Language} {M : Type*} [Tarski.Structure L M] {ξ : Type*} {k : ℕ}
  {Φ Ψ : Semitype L ξ k} {b : ξ → M}

/-- The tuple `a` realizes `Φ` with the parameters read as `b`.
- [Kay91, §8.1] -/
def RealizedBy (Φ : Semitype L ξ k) (b : ξ → M) (a : Fin k → M) : Prop :=
  ∀ φ ∈ Φ, φ.Eval a b

variable (M) in
/-- `Φ` is realized in `M` with the parameters read as `b`.
- [Kay91, §8.1] -/
def Realized (Φ : Semitype L ξ k) (b : ξ → M) : Prop :=
  ∃ a : Fin k → M, RealizedBy Φ b a

variable (M) in
/-- Every finite subset of `Φ` is realized in `M` with the parameters read as `b`.
- [Kay91, §11.2] -/
def FinitelySatisfied (Φ : Semitype L ξ k) (b : ξ → M) : Prop :=
  ∀ s : Finset (Semiformula L ξ k), ↑s ⊆ Φ → Realized M (↑s : Semitype L ξ k) b

/-- `Φ` decides every formula in `M` with the parameters read as `b`: some finite subset of `Φ`
implies the formula or its negation.
- [Kay91, §11.2] -/
def IsCompleteType (Φ : Semitype L ξ k) (b : ξ → M) : Prop :=
  ∀ φ : Semiformula L ξ k, ∃ s : Finset (Semiformula L ξ k), ↑s ⊆ Φ ∧
    ((∀ a, RealizedBy (↑s : Semitype L ξ k) b a → φ.Eval a b) ∨
      ∀ a, RealizedBy (↑s : Semitype L ξ k) b a → ¬φ.Eval a b)

lemma RealizedBy.mono {a : Fin k → M} (h : RealizedBy Φ b a) (hΨΦ : Ψ ⊆ Φ) : RealizedBy Ψ b a :=
  fun φ hφ ↦ h φ (hΨΦ hφ)

lemma Realized.mono (h : Realized M Φ b) (hΨΦ : Ψ ⊆ Φ) : Realized M Ψ b :=
  h.imp fun _ ha ↦ ha.mono hΨΦ

lemma Realized.finitelySatisfied (h : Realized M Φ b) : FinitelySatisfied M Φ b :=
  fun _ hs ↦ h.mono hs

section theory

open Entailment

universe u

variable {L : Language.{u}} {k : ℕ}

/-- `T + Φ(c̄)`: `T` together with the formulas of `Φ`, their variables filled by new constants.
- [Kay91, §8.1] -/
def Theory.addType (T : Theory L) (Φ : Semitype L Empty k) :
    Theory (L.add (Language.constant (Fin k))) :=
  T.lMap (Language.Hom.add₁ L (Language.constant (Fin k))) ∪ lift '' Φ

/-- `Φ` is a type over `T`: `T + Φ(c̄)` is consistent.
- [Kay91, §8.1] -/
def IsTypeOver (T : Theory L) (Φ : Semitype L Empty k) : Prop :=
  Consistent (T.addType Φ)

/-- `Φ` is a complete type over `T`: `T + Φ(c̄)` is consistent and complete.
- [Kay91, §8.1] -/
def IsCompleteTypeOver (T : Theory L) (Φ : Semitype L Empty k) : Prop :=
  IsTypeOver T Φ ∧ Entailment.Complete (T.addType Φ)

/-- `Φ` is a principal type over `T`: some `ψ` with `T + Φ(c̄) ⊢ ψ(c̄)` implies every formula of `Φ`
over `T`.
- [Kay91, §8.1] -/
def IsPrincipalTypeOver (T : Theory L) (Φ : Semitype L Empty k) : Prop :=
  ∃ ψ : Semisentence L k, T.addType Φ ⊢ lift ψ ∧ ∀ φ ∈ Φ, T ⊢ ∀¹* (ψ 🡒 φ)

/-- A type over `T` is realized in some model of `T`, and a set of formulas realized in a model of
`T` is a type over `T`.
- [Kay91, §8.1] -/
theorem isTypeOver_iff_exists_realized {T : Theory L} {Φ : Semitype L Empty k} :
    IsTypeOver T Φ ↔ ∃ N : Tarski.Struc.{u} L, N ⊧* T ∧ Realized N Φ Empty.elim := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := Theory.satisfiable_iff_consistent.{u, u}.mpr h
    use N.reduct
    and_intros
    · apply Semantics.modelsSet_iff.mpr
      intro σ hσ
      exact (N.models_lMap_iff σ).mp <| Semantics.modelsSet_iff.mp hN <| Or.inl ⟨σ, hσ, rfl⟩
    · use N.cstVal
      intro φ hφ
      exact (N.models_lift_iff φ).mp <| Semantics.modelsSet_iff.mp hN <| Or.inr ⟨φ, hφ, rfl⟩
  · rintro ⟨N, hN, a, ha⟩
    apply Theory.consistent_of_satisfiable
    use strucOfTuple N a
    apply Semantics.modelsSet_iff.mpr
    rintro σ (hσ | ⟨φ, hφ, rfl⟩)
    · exact Semantics.modelsSet_iff.mp (strucOfTuple_models_lMap_image N a hN) hσ
    · exact (strucOfTuple_models_lift_iff N a φ).mpr <| ha φ hφ

/-- A set of formulas with parameters `b` is finitely satisfied in `M` if and only if, with the
parameters read as constants, it is a type over the theory of `(M, b)`.
- [Kay91, §11.2] -/
theorem isTypeOver_theory_iff_finitelySatisfied {ι : Type*} {M : Type*} [Nonempty M]
    [Tarski.Structure L M] {Φ : Semitype L ι k} {b : ι → M} :
    IsTypeOver (Semantics.theory (strucOfTuple M b)) (liftParameters '' Φ) ↔
      FinitelySatisfied M Φ b := by
  constructor
  · intro h s hs
    obtain ⟨N, hN, a, ha⟩ := isTypeOver_iff_exists_realized.mp h
    let σ : Sentence (L.add (Language.constant ι)) := ∃¹* ⋀(s.toList.map liftParameters)
    have hσ : ∼σ ∉ Semantics.theory (strucOfTuple M b) := by
      intro hσ
      have : Semiformula.Eval (s := N.struc) ![] Empty.elim (∼σ) := Semantics.modelsSet_iff.mp hN hσ
      simp only [σ, LogicalConnective.HomClass.map_neg, eval_exsClosure] at this
      apply this
      use a
      simpa using fun φ hφ ↦ ha (liftParameters φ) ⟨φ, hs hφ, rfl⟩
    by_contra hM
    apply hσ
    change Semiformula.Eval (s := structureOfTuple M b) ![] Empty.elim (∼σ)
    simp only [σ, LogicalConnective.HomClass.map_neg, eval_exsClosure]
    rintro ⟨a, ha⟩
    apply hM
    use a
    intro φ hφ
    have := List.map_conj₂_prop.mp ha (liftParameters φ) <|
      List.mem_map.mpr ⟨φ, by simpa using hφ, rfl⟩
    simpa using this
  · intro h
    apply consistent_compact.mpr
    intro F hF hfin
    let A : Theory ((L.add (Language.constant ι)).add (Language.constant (Fin k))) :=
      Theory.lMap (Language.Hom.add₁ (L.add (Language.constant ι)) (Language.constant (Fin k)))
        (Semantics.theory (strucOfTuple M b))
    obtain ⟨t, htΦ, htfin, ht⟩ := Set.exists_subset_image_finite_and
      (f := lift ∘ liftParameters) (s := Φ) (p := fun u ↦ F ⊆ A ∪ u) |>.mp <| by
        use F \ A
        and_intros
        · intro σ ⟨hσF, hσA⟩
          rcases hF hσF with hσ | hσ
          · exact absurd hσ hσA
          · simpa [Set.image_image] using hσ
        · exact Set.Finite.sdiff hfin
        · intro σ hσ
          by_cases hσA : σ ∈ A
          · exact Or.inl hσA
          · exact Or.inr ⟨hσ, hσA⟩
    obtain ⟨a, ha⟩ := h htfin.toFinset (by simpa using htΦ)
    let _ : Tarski.Structure (L.add (Language.constant ι)) M := structureOfTuple M b
    apply Theory.consistent_of_satisfiable
    use strucOfTuple M a
    apply Semantics.modelsSet_iff.mpr
    intro σ hσ
    rcases ht hσ with hσ | ⟨φ, hφ, rfl⟩
    · exact Semantics.modelsSet_iff.mp (strucOfTuple_models_lMap_image
        (T := Semantics.theory (strucOfTuple M b)) M a ⟨fun _ h ↦ h⟩) hσ
    · apply (strucOfTuple_models_lift_iff M a (liftParameters φ)).mpr
      simpa using ha φ (by simpa using hφ)

end theory

end FFL.FirstOrder
