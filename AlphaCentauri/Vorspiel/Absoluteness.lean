module

public import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness

/-!
# Casting true $\Sigma_1$/$\Sigma_0$/$\Delta_1$ facts about standard numbers into a model of `𝗣𝗔⁻`
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- A $\Sigma_1$ fact about standard numbers is inherited by every model of `𝗣𝗔⁻`.
- [HP98, Theorem I.1.6] -/
lemma Sigma1_cast {m : ℕ} (σ : 𝚺₁.Semisentence m) {u : Fin m → ℕ}
    (h : ℕ ⊧/u σ.val) : V ⊧/(fun i ↦ (u i : V)) σ.val := by
  simpa [Function.comp_def] using sigmaOne_upward_absolute V σ u h

/-- The $\Delta_1$ form of `Sigma1_cast`, reading the $\Sigma_1$ half of the definition.
- [HP98, Theorem I.1.6] -/
lemma Delta1_cast {m : ℕ} (σ : 𝚫₁.Semisentence m) {u : Fin m → ℕ}
    (h : ℕ ⊧/u σ.val) : V ⊧/(fun i ↦ (u i : V)) σ.val := by
  have h' : ℕ ⊧/u σ.sigma.val := by rwa [HierarchySymbol.Semiformula.val_sigma]
  have := Sigma1_cast (V := V) σ.sigma h'
  rwa [HierarchySymbol.Semiformula.val_sigma] at this

/-- `Sigma1_cast` at one argument.
- [HP98, Theorem I.1.6] -/
lemma Sigma1_cast₁ (σ : 𝚺₁.Semisentence 1) {a : ℕ} (h : ℕ ⊧/![a] σ.val) :
    V ⊧/![(a : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using Sigma1_cast (V := V) σ h

/-- `Sigma1_cast` at two arguments.
- [HP98, Theorem I.1.6] -/
lemma Sigma1_cast₂ (σ : 𝚺₁.Semisentence 2) {a b : ℕ} (h : ℕ ⊧/![a, b] σ.val) :
    V ⊧/![(a : V), (b : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using Sigma1_cast (V := V) σ h

/-- `Sigma1_cast` at three arguments.
- [HP98, Theorem I.1.6] -/
lemma Sigma1_cast₃ (σ : 𝚺₁.Semisentence 3) {a b c : ℕ} (h : ℕ ⊧/![a, b, c] σ.val) :
    V ⊧/![(a : V), (b : V), (c : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using Sigma1_cast (V := V) σ h

/-- $\Sigma_0$ cast at one argument.
- [HP98, Theorem I.1.6] -/
lemma Sigma0_cast₁ (σ : 𝚺₀.Semisentence 1) {a : ℕ} (h : ℕ ⊧/![a] σ.val) :
    V ⊧/![(a : V)] σ.val := by
  simpa [Function.comp_def, Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using (shigmaZero_absolute V σ ![a]).mp h

/-- $\Sigma_0$ cast at two arguments.
- [HP98, Theorem I.1.6] -/
lemma Sigma0_cast₂ (σ : 𝚺₀.Semisentence 2) {a b : ℕ} (h : ℕ ⊧/![a, b] σ.val) :
    V ⊧/![(a : V), (b : V)] σ.val := by
  simpa [Function.comp_def, Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using (shigmaZero_absolute V σ ![a, b]).mp h

/-- $\Sigma_0$ cast at three arguments.
- [HP98, Theorem I.1.6] -/
lemma Sigma0_cast₃ (σ : 𝚺₀.Semisentence 3) {a b c : ℕ} (h : ℕ ⊧/![a, b, c] σ.val) :
    V ⊧/![(a : V), (b : V), (c : V)] σ.val := by
  simpa [Function.comp_def, Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using (shigmaZero_absolute V σ ![a, b, c]).mp h

/-- `Delta1_cast` at one argument.
- [HP98, Theorem I.1.6] -/
lemma Delta1_cast₁ (σ : 𝚫₁.Semisentence 1) {a : ℕ} (h : ℕ ⊧/![a] σ.val) :
    V ⊧/![(a : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using Delta1_cast (V := V) σ h

end FFL.FirstOrder.Arithmetic
