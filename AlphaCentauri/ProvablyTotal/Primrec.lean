module

public import AlphaCentauri.ProvablyTotal.Basic
public import AlphaCentauri.Vorspiel.Primrec
public import AlphaCentauri.Vorspiel.Vector
public import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
# Primitive recursive functions are `𝗜𝚺₁`-provably functional

Every primitive recursive function is `𝗜𝚺₁`-provably functional, hence provably total, in
Mathlib's `Nat.Primrec'` and `Primrec` forms.
-/

@[expose] public section

namespace FFL.FirstOrder

open Arithmetic HierarchySymbol

variable {k n : ℕ}

namespace Arithmetic

variable {V : Type*} [ORingStructure V]

private lemma definedFunction_zero :
    𝚺₁.DefinedFunction (fun _ : Fin 0 → V ↦ 0) (.mkSigma “y. y = 0”) := .mk fun _ ↦ by simp

private lemma definedFunction_succ :
    𝚺₁.DefinedFunction (fun v : Fin 1 → V ↦ v 0 + 1) (.mkSigma “y x. y = x + 1”) :=
  .mk fun _ ↦ by simp

private lemma definedFunction_get (i : Fin k) :
    𝚺₁.DefinedFunction (fun v : Fin k → V ↦ v i)
      ((.mkSigma “y x. y = x” : 𝚺₁.Semisentence 2).rew (Rew.subst ![#0, #i.succ])) :=
  .mk fun _ ↦ by simp

/-- The blueprint of the primitive recursion whose base and step are given by the graphs `ψ` and
`χ`, the arguments of `χ` being the recursion variable, the previous value, and the parameters.
- [HP98, Lemma I.1.55] -/
private def precBlueprint (ψ : 𝚺₁.Semisentence (n + 1)) (χ : 𝚺₁.Semisentence (n + 3)) :
    PR.Blueprint n where
  zero := ψ
  succ := χ.rew (Rew.subst (#0 :> #2 :> #1 :> (#·.succ.succ.succ)))

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {ψ : 𝚺₁.Semisentence (n + 1)} {χ : 𝚺₁.Semisentence (n + 3)}

/-- The primitive recursion built inside a model of `𝗜𝚺₁` from the functions defined by `ψ` and
`χ`.
- [HP98, Lemma I.1.55] -/
private def precConstruction {f : (Fin n → V) → V} {g : (Fin (n + 2) → V) → V}
    (hf : 𝚺₁.DefinedFunction f ψ) (hg : 𝚺₁.DefinedFunction g χ) :
    PR.Construction V (precBlueprint ψ χ) where
  zero := f
  succ := fun v i z ↦ g (i :> z :> v)
  zero_defined := hf
  succ_defined := .mk fun v ↦ by
    simp [precBlueprint, Semiformula.eval_rew, Empty.eq_elim, hg.iff, Matrix.comp_vecCons']

private lemma result_precConstruction {f : (Fin n → ℕ) → ℕ} {g : (Fin (n + 2) → ℕ) → ℕ}
    (hf : 𝚺₁.DefinedFunction (V := ℕ) f ψ) (hg : 𝚺₁.DefinedFunction (V := ℕ) g χ)
    (v : Fin n → ℕ) (u : ℕ) :
    (precConstruction hf hg).result v u = u.rec (f v) fun y ih ↦ g (y :> ih :> v) := by
  induction u with
  | zero => simp [precConstruction]
  | succ u ih => rw [PR.Construction.result_succ, ih]; rfl

end Arithmetic

namespace ArithmeticTheory.ProvablyFunctionalVia

variable {T : ArithmeticTheory}

section
variable {f g : (Fin k → ℕ) → ℕ} {φ : 𝚺₁.Semisentence (k + 1)}

private lemma of_eq (hf : T.ProvablyFunctionalVia f φ) (h : ∀ v, f v = g v) :
    T.ProvablyFunctionalVia g φ :=
  ⟨⟨DefinedFunction.of_eq h hf.defined, hf.total⟩, hf.functional⟩

end

section
variable [𝗘𝗤 ℒₒᵣ ⪯ T]

private lemma zero : T.ProvablyFunctionalVia (fun _ : Fin 0 → ℕ ↦ 0) (.mkSigma “y. y = 0”) :=
  of_models definedFunction_zero fun _ _ _ ↦ ⟨_, definedFunction_zero⟩

private lemma succ :
    T.ProvablyFunctionalVia (fun v : Fin 1 → ℕ ↦ v 0 + 1) (.mkSigma “y x. y = x + 1”) :=
  of_models definedFunction_succ fun _ _ _ ↦ ⟨_, definedFunction_succ⟩

private lemma get (i : Fin k) :
    T.ProvablyFunctionalVia (fun v : Fin k → ℕ ↦ v i)
      ((.mkSigma “y x. y = x” : 𝚺₁.Semisentence 2).rew (Rew.subst ![#0, #i.succ])) :=
  of_models (definedFunction_get i) fun _ _ _ ↦ ⟨_, definedFunction_get i⟩

section comp
variable {l : ℕ} {g : (Fin l → ℕ) → ℕ} {h : Fin l → (Fin k → ℕ) → ℕ}
  {ψ : 𝚺₁.Semisentence (l + 1)} {χ : Fin l → 𝚺₁.Semisentence (k + 1)}

private lemma comp (hg : T.ProvablyFunctionalVia g ψ)
    (hh : ∀ i, T.ProvablyFunctionalVia (h i) (χ i)) :
    T.ProvablyFunctionalVia (fun v ↦ g fun i ↦ h i v) (compGraph ψ χ) := by
  refine of_models (definedFunction_compGraph hg.defined fun i ↦ (hh i).defined) fun V _ _ ↦ ?_
  obtain ⟨G, hG⟩ := hg.models V
  choose H hH using fun i ↦ (hh i).models V
  exact ⟨_, definedFunction_compGraph hG hH⟩

end comp

section prec
variable {f : (Fin n → ℕ) → ℕ} {g : (Fin (n + 2) → ℕ) → ℕ}
  {ψ : 𝚺₁.Semisentence (n + 1)} {χ : 𝚺₁.Semisentence (n + 3)}

private lemma prec [𝗜𝚺₁ ⪯ T] (hf : T.ProvablyFunctionalVia f ψ)
    (hg : T.ProvablyFunctionalVia g χ) :
    T.ProvablyFunctionalVia
      (fun v : Fin (n + 1) → ℕ ↦ (v 0).rec (f (v ·.succ)) fun y ih ↦ g (y :> ih :> (v ·.succ)))
      (precBlueprint ψ χ).resultDef := by
  refine of_models (DefinedFunction.of_eq
    (fun v ↦ result_precConstruction hf.defined hg.defined _ _)
    (precConstruction hf.defined hg.defined).result_defined) fun V _ _ ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
  obtain ⟨F, hF⟩ := hf.models V
  obtain ⟨G, hG⟩ := hg.models V
  exact ⟨_, (precConstruction hF hG).result_defined⟩

end prec

end

end ArithmeticTheory.ProvablyFunctionalVia

namespace Arithmetic

open ArithmeticTheory

open ProvablyFunctionalVia in
/-- Every primitive recursive function, in Mathlib's `List.Vector` form `Nat.Primrec'`, is
`𝗜𝚺₁`-provably functional.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
theorem provablyFunctional_of_primrec' {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    𝗜𝚺₁.ProvablyFunctional (fun v ↦ f (.ofFn v)) := by
  induction hf with
  | zero => exact (zero.of_eq (by simp)).toProvablyFunctional
  | succ => exact (succ.of_eq (by simp)).toProvablyFunctional
  | get i => exact ((get i).of_eq (by simp)).toProvablyFunctional
  | comp g _ _ ihf ihg =>
    obtain ⟨ψ, hψ⟩ := ihf
    choose χ hχ using ihg
    exact ((hψ.comp hχ).of_eq (by simp)).toProvablyFunctional
  | prec _ _ ihf ihg =>
    obtain ⟨ψ, hψ⟩ := ihf
    obtain ⟨χ, hχ⟩ := ihg
    exact ((hψ.prec hχ).of_eq (by simp)).toProvablyFunctional

/-- Every primitive recursive function, in Mathlib's curried form `Primrec`, is `𝗜𝚺₁`-provably
functional.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
theorem provablyFunctional_of_primrec {f : List.Vector ℕ k → ℕ} (hf : Primrec f) :
    𝗜𝚺₁.ProvablyFunctional (fun v ↦ f (.ofFn v)) :=
  provablyFunctional_of_primrec' (Nat.Primrec'.prim_iff.mpr hf)

/-- Every primitive recursive function, in Mathlib's `List.Vector` form `Nat.Primrec'`, is
`𝗜𝚺₁`-provably total.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
lemma provablyTotal_of_primrec' {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) :=
  (provablyFunctional_of_primrec' hf).toProvablyTotal

/-- Every primitive recursive function, in Mathlib's curried form `Primrec`, is `𝗜𝚺₁`-provably
total.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
lemma provablyTotal_of_primrec {f : List.Vector ℕ k → ℕ} (hf : Primrec f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) :=
  (provablyFunctional_of_primrec hf).toProvablyTotal

end Arithmetic

end FFL.FirstOrder
