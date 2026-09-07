module

public import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness

/-!
# Casting true `𝚺₁`/`𝚺₀`/`𝚫₁` facts about standard numbers into a model of `𝗣𝗔⁻`
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- A `𝚺₁` fact about standard numbers is inherited by every model of `𝗣𝗔⁻`.
- [HP98, Theorem I.1.6] -/
lemma sigma_one_cast {m : ℕ} (σ : 𝚺₁.Semisentence m) {u : Fin m → ℕ}
    (h : ℕ ⊧/u σ.val) : V ⊧/(fun i ↦ (u i : V)) σ.val := by
  simpa [Function.comp_def] using sigmaOne_upward_absolute V σ u h

/-- The `𝚫₁` form of `sigma_one_cast`, reading the `𝚺₁` half of the definition.
- [HP98, Theorem I.1.6] -/
lemma delta_one_cast {m : ℕ} (σ : 𝚫₁.Semisentence m) {u : Fin m → ℕ}
    (h : ℕ ⊧/u σ.val) : V ⊧/(fun i ↦ (u i : V)) σ.val := by
  have h' : ℕ ⊧/u σ.sigma.val := by rwa [HierarchySymbol.Semiformula.val_sigma]
  have := sigma_one_cast (V := V) σ.sigma h'
  rwa [HierarchySymbol.Semiformula.val_sigma] at this

/-- `sigma_one_cast` at one argument.
- [HP98, Theorem I.1.6] -/
lemma cast_sigma₁ (σ : 𝚺₁.Semisentence 1) {a : ℕ} (h : ℕ ⊧/![a] σ.val) :
    V ⊧/![(a : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using sigma_one_cast (V := V) σ h

/-- `sigma_one_cast` at two arguments.
- [HP98, Theorem I.1.6] -/
lemma cast_sigma₂ (σ : 𝚺₁.Semisentence 2) {a b : ℕ} (h : ℕ ⊧/![a, b] σ.val) :
    V ⊧/![(a : V), (b : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using sigma_one_cast (V := V) σ h

/-- `sigma_one_cast` at three arguments.
- [HP98, Theorem I.1.6] -/
lemma cast_sigma₃ (σ : 𝚺₁.Semisentence 3) {a b c : ℕ} (h : ℕ ⊧/![a, b, c] σ.val) :
    V ⊧/![(a : V), (b : V), (c : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using sigma_one_cast (V := V) σ h

/-- `𝚺₀` cast at one argument.
- [HP98, Theorem I.1.6] -/
lemma cast_sigmaZero₁ (σ : 𝚺₀.Semisentence 1) {a : ℕ} (h : ℕ ⊧/![a] σ.val) :
    V ⊧/![(a : V)] σ.val := by
  simpa [Function.comp_def, Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using (shigmaZero_absolute V σ ![a]).mp h

/-- `𝚺₀` cast at two arguments.
- [HP98, Theorem I.1.6] -/
lemma cast_sigmaZero₂ (σ : 𝚺₀.Semisentence 2) {a b : ℕ} (h : ℕ ⊧/![a, b] σ.val) :
    V ⊧/![(a : V), (b : V)] σ.val := by
  simpa [Function.comp_def, Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using (shigmaZero_absolute V σ ![a, b]).mp h

/-- `𝚺₀` cast at three arguments.
- [HP98, Theorem I.1.6] -/
lemma cast_sigmaZero₃ (σ : 𝚺₀.Semisentence 3) {a b c : ℕ} (h : ℕ ⊧/![a, b, c] σ.val) :
    V ⊧/![(a : V), (b : V), (c : V)] σ.val := by
  simpa [Function.comp_def, Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using (shigmaZero_absolute V σ ![a, b, c]).mp h

/-- `delta_one_cast` at one argument.
- [HP98, Theorem I.1.6] -/
lemma cast_delta₁ (σ : 𝚫₁.Semisentence 1) {a : ℕ} (h : ℕ ⊧/![a] σ.val) :
    V ⊧/![(a : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using delta_one_cast (V := V) σ h

end FFL.FirstOrder.Arithmetic
