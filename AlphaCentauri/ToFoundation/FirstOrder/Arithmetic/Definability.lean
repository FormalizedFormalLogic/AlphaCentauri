module

public import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness
public import Foundation.FirstOrder.Arithmetic.Definability.PrenexDefinable
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.Vorspiel.Computability.Primrec
public import AlphaCentauri.ToMathlib.Computability.Primrec.Basic
public import AlphaCentauri.Hierarchy.Bounded
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Absoluteness, prenex definability and primitive recursion of $\Delta_0$ truth

Supplements `Foundation.FirstOrder.Arithmetic.Definability`: casting true
$\Sigma_1$/$\Sigma_0$/$\Delta_1$ facts about standard numbers into a model of `𝗣𝗔⁻`, prenex
$\Sigma_1$ definability of existentially quantified relations, and primitive recursiveness of the
truth of $\Delta_0$ formulas.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

section Absoluteness

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- A $\Sigma_1$ fact about standard numbers is inherited by every model of `𝗣𝗔⁻`.
- [HP98, Theorem I.1.6] -/
lemma Sigma1_cast {m : ℕ} (σ : 𝚺ᴬ₁.Semisentence m) {u : Fin m → ℕ}
    (h : ℕ ⊧/u σ.val) : V ⊧/(fun i ↦ (u i : V)) σ.val := by
  simpa [Function.comp_def] using sigmaOne_upward_absolute V σ u h

/-- The $\Delta_1$ form of `Sigma1_cast`, reading the $\Sigma_1$ half of the definition.
- [HP98, Theorem I.1.6] -/
lemma Delta1_cast {m : ℕ} (σ : 𝚫ᴬ₁.Semisentence m) {u : Fin m → ℕ}
    (h : ℕ ⊧/u σ.val) : V ⊧/(fun i ↦ (u i : V)) σ.val := by
  have h' : ℕ ⊧/u σ.sigma.val := by rwa [HierarchySymbol.Semiformula.val_sigma]
  have := Sigma1_cast (V := V) σ.sigma h'
  rwa [HierarchySymbol.Semiformula.val_sigma] at this

/-- `Sigma1_cast` at two arguments.
- [HP98, Theorem I.1.6] -/
lemma Sigma1_cast₂ (σ : 𝚺ᴬ₁.Semisentence 2) {a b : ℕ} (h : ℕ ⊧/![a, b] σ.val) :
    V ⊧/![(a : V), (b : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using Sigma1_cast (V := V) σ h

/-- `Sigma1_cast` at three arguments.
- [HP98, Theorem I.1.6] -/
lemma Sigma1_cast₃ (σ : 𝚺ᴬ₁.Semisentence 3) {a b c : ℕ} (h : ℕ ⊧/![a, b, c] σ.val) :
    V ⊧/![(a : V), (b : V), (c : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using Sigma1_cast (V := V) σ h

/-- $\Sigma_0$ cast at one argument.
- [HP98, Theorem I.1.6] -/
lemma Sigma0_cast₁ (σ : 𝚺ᴬ₀.Semisentence 1) {a : ℕ} (h : ℕ ⊧/![a] σ.val) :
    V ⊧/![(a : V)] σ.val := by
  simpa [Function.comp_def, Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using (sigmaZero_absolute V σ ![a]).mp h

/-- $\Sigma_0$ cast at two arguments.
- [HP98, Theorem I.1.6] -/
lemma Sigma0_cast₂ (σ : 𝚺ᴬ₀.Semisentence 2) {a b : ℕ} (h : ℕ ⊧/![a, b] σ.val) :
    V ⊧/![(a : V), (b : V)] σ.val := by
  simpa [Function.comp_def, Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using (sigmaZero_absolute V σ ![a, b]).mp h

/-- $\Sigma_0$ cast at three arguments.
- [HP98, Theorem I.1.6] -/
lemma Sigma0_cast₃ (σ : 𝚺ᴬ₀.Semisentence 3) {a b c : ℕ} (h : ℕ ⊧/![a, b, c] σ.val) :
    V ⊧/![(a : V), (b : V), (c : V)] σ.val := by
  simpa [Function.comp_def, Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using (sigmaZero_absolute V σ ![a, b, c]).mp h

/-- `Delta1_cast` at one argument.
- [HP98, Theorem I.1.6] -/
lemma Delta1_cast₁ (σ : 𝚫ᴬ₁.Semisentence 1) {a : ℕ} (h : ℕ ⊧/![a] σ.val) :
    V ⊧/![(a : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton]
    using Delta1_cast (V := V) σ h

end Absoluteness

section PrenexDefinable

open scoped FFL.FirstOrder.Bounding FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V]

lemma PrenexDefinable.exists_of_sigmaZero {k : ℕ} {R : (Fin k → V) → V → Prop}
    (hR : 𝚺ᴬ₀.Definable fun v : Fin (k + 1) → V ↦ R (fun i ↦ v i.succ) (v 0)) :
    PrenexDefinable 𝚺 1 fun v ↦ ∃ x, R v x := by
  obtain ⟨φ, hφ⟩ := hR
  have h₁ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 0 φ.val :=
    Bounding.PrenexHierarchy.zero_iff.mpr φ.sigma_prop
  exact ⟨∃¹ φ.val, Bounding.PrenexHierarchy.exs h₁, by intro v; simp [hφ.iff]⟩

private lemma definable_exists_pair [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {k : ℕ} {R : (Fin k → V) → V → V → Prop}
    (hR : 𝚺ᴬ₀.Definable fun v : Fin (k + 2) → V ↦ R (fun i ↦ v i.succ.succ) (v 0) (v 1)) :
    𝚺ᴬ₀.Definable (k := k + 1) fun w ↦
      ∃ y ≤ w 0, ∃ x ≤ w 0, w 0 = ⟪x, y⟫ ∧ R (fun i ↦ w i.succ) x y := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
  have hR₁ : 𝚺ᴬ₀.Definable (k := k + 3) fun w ↦ R (fun i ↦ w i.succ.succ.succ) (w 0) (w 1) :=
    (hR.retraction (Fin.cons 0 (Fin.cons 1 fun i : Fin k ↦ i.succ.succ.succ))).of_iff
      (by intro w; simp)
  have hB : 𝚺ᴬ₀.Definable (k := k + 3) fun w ↦
      w 2 = ⟪w 0, w 1⟫ ∧ R (fun i ↦ w i.succ.succ.succ) (w 0) (w 1) := by
    definability
  have hI : 𝚺ᴬ₀.Definable (k := k + 2) fun u ↦
      ∃ x ≤ u 1, u 1 = ⟪x, u 0⟫ ∧ R (fun i ↦ u i.succ.succ) x (u 0) :=
    (Bounding.HierarchySymbol.Definable.arithmetic_bexs' (P := fun u x ↦
      u 1 = ⟪x, u 0⟫ ∧ R (fun i ↦ u i.succ.succ) x (u 0)) (hB.of_iff (by intro w; simp)) #1).of_iff
      (by intro u; simp)
  exact (Bounding.HierarchySymbol.Definable.arithmetic_bexs' (P := fun w y ↦
      ∃ x ≤ (y :> w) 1, (y :> w) 1 = ⟪x, (y :> w) 0⟫ ∧
        R (fun i ↦ (y :> w) i.succ.succ) x ((y :> w) 0))
    (hI.of_iff (by intro w; simp)) #0).of_iff (by intro w; simp)

lemma PrenexDefinable.exists_exists_of_sigmaZero [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {k : ℕ}
    {R : (Fin k → V) → V → V → Prop}
    (hR : 𝚺ᴬ₀.Definable fun v : Fin (k + 2) → V ↦ R (fun i ↦ v i.succ.succ) (v 0) (v 1)) :
    PrenexDefinable 𝚺 1 fun v ↦ ∃ x y, R v x y := by
  exact (PrenexDefinable.exists_of_sigmaZero
    (R := fun v p ↦ ∃ y ≤ p, ∃ x ≤ p, p = ⟪x, y⟫ ∧ R v x y) (definable_exists_pair hR)).of_iff
    fun v ↦ ⟨fun ⟨x, y, h⟩ ↦ ⟨⟪x, y⟫, y, le_pair_right x y, x, le_pair_left x y, rfl, h⟩,
      fun ⟨_, y, _, x, _, _, h⟩ ↦ ⟨x, y, h⟩⟩

lemma PrenexDefinable.exists_exists_exists_of_sigmaZero [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {k : ℕ}
    {R : (Fin k → V) → V → V → V → Prop}
    (hR : 𝚺ᴬ₀.Definable fun v : Fin (k + 3) → V ↦
      R (fun i ↦ v i.succ.succ.succ) (v 0) (v 1) (v 2)) :
    PrenexDefinable 𝚺 1 fun v ↦ ∃ x y z, R v x y z := by
  have hS := definable_exists_pair
    (R := fun u x y ↦ R (fun i ↦ u i.succ) x y (u 0)) (hR.of_iff (by intro w; simp))
  exact (PrenexDefinable.exists_exists_of_sigmaZero
    (R := fun v p t ↦ ∃ y ≤ p, ∃ x ≤ p, p = ⟪x, y⟫ ∧ R v x y t) hS).of_iff
    fun v ↦ ⟨fun ⟨x, y, z, h⟩ ↦ ⟨⟪x, y⟫, z, y, le_pair_right x y, x, le_pair_left x y, rfl, h⟩,
      fun ⟨_, t, y, _, x, _, _, h⟩ ↦ ⟨x, y, t, h⟩⟩

end PrenexDefinable

section Primrec

variable {ξ : Type*} (ε : ξ → ℕ)

/-- The truth of a $\Delta_0$ formula is primitive recursive in `List.Vector` form.
- [HP98, Theorem 0.35] -/
lemma bounded_primrec_vec :
    (k : ℕ) → (φ : ArithmeticSemiformula ξ k) → ℬ[<, ℒₒᵣ].Closure φ →
      PrimrecPred fun v : List.Vector ℕ k ↦ φ.Eval v.get ε
  | _, _, Bounding.Closure.verum _ => by simpa using PrimrecPred.const True
  | _, _, Bounding.Closure.falsum _ => by simpa using PrimrecPred.const False
  | _, _, Bounding.Closure.rel Language.Eq.eq v => by
    simpa [← Matrix.fun_eq_vec_two]
      using Primrec.eq.comp (term_primrec (v 0)) (term_primrec (v 1))
  | _, _, Bounding.Closure.nrel Language.Eq.eq v => by
    simpa [← Matrix.fun_eq_vec_two]
      using (Primrec.eq.comp (term_primrec (v 0)) (term_primrec (v 1))).not
  | _, _, Bounding.Closure.rel Language.LT.lt v => by
    simpa [← Matrix.fun_eq_vec_two]
      using Primrec.nat_lt.comp (term_primrec (v 0)) (term_primrec (v 1))
  | _, _, Bounding.Closure.nrel Language.LT.lt v => by
    simpa [← Matrix.fun_eq_vec_two]
      using (Primrec.nat_lt.comp (term_primrec (v 0)) (term_primrec (v 1))).not
  | _, _, Bounding.Closure.and hφ hψ => by
    simpa using (bounded_primrec_vec _ _ hφ).and (bounded_primrec_vec _ _ hψ)
  | _, _, Bounding.Closure.or hφ hψ => by
    simpa using (bounded_primrec_vec _ _ hφ).or (bounded_primrec_vec _ _ hψ)
  | n, _, Bounding.Closure.ball (φ := φ) hR pt hφ => by
    obtain rfl := Set.mem_singleton_iff.mp hR
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    have h : PrimrecRel fun (x : ℕ) (v : List.Vector ℕ n) ↦ φ.Eval (x ::ᵥ v).get ε :=
      (bounded_primrec_vec _ _ hφ).comp Primrec.vector_cons
    simpa [List.Vector.cons_get] using (PrimrecRel.forall_lt' h).comp (term_primrec t) .id
  | n, _, Bounding.Closure.bexs (φ := φ) hR pt hφ => by
    obtain rfl := Set.mem_singleton_iff.mp hR
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    have h : PrimrecRel fun (x : ℕ) (v : List.Vector ℕ n) ↦ φ.Eval (x ::ᵥ v).get ε :=
      (bounded_primrec_vec _ _ hφ).comp Primrec.vector_cons
    simpa [List.Vector.cons_get] using (PrimrecRel.exists_lt' h).comp (term_primrec t) .id

/-- The truth of a $\Delta_0$ formula is primitive recursive in `Fin k → ℕ` form.
- [HP98, Theorem 0.35] -/
@[primrec]
lemma bounded_primrec {k} {φ : ArithmeticSemiformula ξ k} (hφ : ℬ[<, ℒₒᵣ].Closure φ) :
    PrimrecPred fun v : Fin k → ℕ ↦ φ.Eval v ε :=
  PrimrecPred.comp_get_iff.mp (bounded_primrec_vec ε k φ hφ)

/-- The value of a term under an assignment read off a list is primitive recursive in the list.
- [HP98, Theorem 0.35] -/
@[primrec]
lemma primrec_termVal {α : Type*} [Primcodable α] {l : α → List ℕ} (hl : Primrec l) :
    (t : ArithmeticTerm ℕ) → Primrec fun a ↦ Semiterm.val ![] ((l a).getD · 0) t
  | #x => x.elim0
  | &x => by simpa using (Primrec.list_getD 0).comp hl (Primrec.const x)
  | .func Language.Zero.zero _ => by simpa using Primrec.const 0
  | .func Language.One.one _ => by simpa using Primrec.const 1
  | .func Language.Add.add v => by
    simpa [Semiterm.val_func] using
      Primrec.nat_add.comp (primrec_termVal hl (v 0)) (primrec_termVal hl (v 1))
  | .func Language.Mul.mul v => by
    simpa [Semiterm.val_func] using
      Primrec.nat_mul.comp (primrec_termVal hl (v 0)) (primrec_termVal hl (v 1))

end Primrec

end FFL.FirstOrder.Arithmetic
