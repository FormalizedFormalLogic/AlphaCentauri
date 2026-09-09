module

public import AlphaCentauri.ProvablyTotal.Basic
public import AlphaCentauri.Vorspiel.Primrec
public import AlphaCentauri.Vorspiel.Vector
public import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
# Primitive recursive functions are `𝗜𝚺₁`-provably total

Every primitive recursive function is `𝗜𝚺₁`-provably total, in Mathlib's `Nat.Primrec'` and
`Primrec` forms.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {k n : ℕ}

section graph

/-- The graph `y = 0` of the constant zero. -/
private def zeroGraph : 𝚺₁.Semisentence 1 := .mkSigma “y. y = 0”

/-- The graph `y = x + 1` of the successor. -/
private def succGraph : 𝚺₁.Semisentence 2 := .mkSigma “y x. y = x + 1”

/-- The graph `y = xᵢ` of the `i`-th projection. -/
private def getGraph (i : Fin k) : 𝚺₁.Semisentence (k + 1) :=
  (.mkSigma “y x. y = x” : 𝚺₁.Semisentence 2).rew (Rew.subst ![#0, #i.succ])

/-- The blueprint of the primitive recursion whose base and step are given by the graphs `ψ` and
`χ`, the arguments of `χ` being the recursion variable, the previous value, and the parameters.
- [HP98, Lemma I.1.55] -/
private def precBlueprint (ψ : 𝚺₁.Semisentence (n + 1)) (χ : 𝚺₁.Semisentence (n + 3)) :
    PR.Blueprint n where
  zero := ψ
  succ := χ.rew (Rew.subst (#0 :> #2 :> #1 :> (#·.succ.succ.succ)))

variable {V : Type*} [ORingStructure V]

private lemma definedFunction_zeroGraph :
    𝚺₁.DefinedFunction (fun _ : Fin 0 → V ↦ (0 : V)) zeroGraph := .mk fun v ↦ by simp [zeroGraph]

private lemma definedFunction_succGraph :
    𝚺₁.DefinedFunction (fun v : Fin 1 → V ↦ v 0 + 1) succGraph := .mk fun v ↦ by simp [succGraph]

private lemma definedFunction_getGraph (i : Fin k) :
    𝚺₁.DefinedFunction (fun v : Fin k → V ↦ v i) (getGraph i) := .mk fun v ↦ by simp [getGraph]

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

end graph

/-- `f` has a `𝚺₁` graph which defines `f` over `ℕ` and defines a function in every model of
`𝗜𝚺₁`.
- [HP98, Definition I.1.51] -/
private def ProvablyFunctional (f : (Fin k → ℕ) → ℕ) : Prop :=
  ∃ φ : 𝚺₁.Semisentence (k + 1), 𝚺₁.DefinedFunction (V := ℕ) f φ ∧
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], ∃ F : (Fin k → V) → V,
      𝚺₁.DefinedFunction F φ

namespace ProvablyFunctional

open ArithmeticTheory HierarchySymbol

variable {f g : (Fin k → ℕ) → ℕ}

private lemma of_eq (h : ∀ v, f v = g v) (hf : ProvablyFunctional f) : ProvablyFunctional g :=
  have ⟨φ, hφ, hV⟩ := hf
  ⟨φ, DefinedFunction.of_eq h hφ, hV⟩

private lemma to_provablyTotal (hf : ProvablyFunctional f) : 𝗜𝚺₁.ProvablyTotal f :=
  have ⟨φ, hφ, hV⟩ := hf
  ⟨φ, ProvablyTotalVia.of_models hφ fun V _ _ v ↦
    have ⟨F, hF⟩ := hV V
    ⟨F v, by simp [hF.iff]⟩⟩

private lemma zero : ProvablyFunctional (fun _ : Fin 0 → ℕ ↦ 0) :=
  ⟨zeroGraph, definedFunction_zeroGraph, fun _ _ _ ↦ ⟨_, definedFunction_zeroGraph⟩⟩

private lemma succ : ProvablyFunctional (fun v : Fin 1 → ℕ ↦ v 0 + 1) :=
  ⟨succGraph, definedFunction_succGraph, fun _ _ _ ↦ ⟨_, definedFunction_succGraph⟩⟩

private lemma get (i : Fin k) : ProvablyFunctional (fun v : Fin k → ℕ ↦ v i) :=
  ⟨getGraph i, definedFunction_getGraph i, fun _ _ _ ↦ ⟨_, definedFunction_getGraph i⟩⟩

private lemma comp {l : ℕ} {f : (Fin l → ℕ) → ℕ} {g : Fin l → (Fin k → ℕ) → ℕ}
    (hf : ProvablyFunctional f) (hg : ∀ i, ProvablyFunctional (g i)) :
    ProvablyFunctional fun v ↦ f fun i ↦ g i v := by
  obtain ⟨ψ, hψ, hψ'⟩ := hf
  choose χ hχ hχ' using hg
  refine ⟨compGraph ψ χ, definedFunction_compGraph hψ hχ, fun V _ _ ↦ ?_⟩
  obtain ⟨F, hF⟩ := hψ' V
  choose G hG using fun i ↦ hχ' i V
  exact ⟨_, definedFunction_compGraph hF hG⟩

private lemma prec {f : (Fin n → ℕ) → ℕ} {g : (Fin (n + 2) → ℕ) → ℕ}
    (hf : ProvablyFunctional f) (hg : ProvablyFunctional g) :
    ProvablyFunctional fun v : Fin (n + 1) → ℕ ↦
      (v 0).rec (f (v ·.succ)) fun y ih ↦ g (y :> ih :> (v ·.succ)) := by
  obtain ⟨ψ, hψ, hψ'⟩ := hf
  obtain ⟨χ, hχ, hχ'⟩ := hg
  refine ⟨(precBlueprint ψ χ).resultDef, ?_, fun V _ _ ↦ ?_⟩
  · exact DefinedFunction.of_eq (fun v ↦ result_precConstruction hψ hχ _ _)
      (precConstruction hψ hχ).result_defined
  · obtain ⟨F, hF⟩ := hψ' V
    obtain ⟨G, hG⟩ := hχ' V
    exact ⟨_, (precConstruction hF hG).result_defined⟩

private lemma of_primrec' {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    ProvablyFunctional fun v ↦ f (.ofFn v) := by
  induction hf with
  | zero => exact of_eq (by simp) zero
  | succ => exact of_eq (by simp) succ
  | get i => exact of_eq (by simp) (get i)
  | comp g _ _ ihf ihg => exact of_eq (by simp) (comp ihf ihg)
  | prec _ _ ihf ihg => exact of_eq (by simp) (prec ihf ihg)

end ProvablyFunctional

/-- Every primitive recursive function, in Mathlib's `List.Vector` form `Nat.Primrec'`, is
`𝗜𝚺₁`-provably total.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
theorem provablyTotal_of_primrec' {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) :=
  (ProvablyFunctional.of_primrec' hf).to_provablyTotal

/-- Every primitive recursive function, in Mathlib's curried form `Primrec`, is `𝗜𝚺₁`-provably
total.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
theorem provablyTotal_of_primrec {f : List.Vector ℕ k → ℕ} (hf : Primrec f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) :=
  provablyTotal_of_primrec' (Nat.Primrec'.prim_iff.mpr hf)

end FFL.FirstOrder.Arithmetic
