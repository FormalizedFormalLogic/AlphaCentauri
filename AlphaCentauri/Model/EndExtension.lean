module

public import AlphaCentauri.ToFoundation.FirstOrder.Bounded
public import AlphaCentauri.Axiomatizability.Basic
public import Foundation.FirstOrder.Arithmetic.Collection.Basic
public import Foundation.FirstOrder.Arithmetic.Definability.PrenexDefinable
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.Arithmetic.Schema.DeltaInduction
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# End extensions and cuts

End extensions of `ℒₒᵣ`-structures, cuts, proper cuts, and overspill.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

section EndExtensions

/-! ## End extensions

An end extension of an `ℒₒᵣ`-structure `M` is a structure into which `M` embeds with nothing new
below the image of `M`. Bounded formulas take the same truth value in `M` and in an end extension
of it, $\Sigma_1$ formulas satisfied in `M` stay satisfied in an end extension of it, and both
`𝗣𝗔⁻` and any theory axiomatized by $\Pi_1$ sentences hold in `M` as soon as they hold in an end
extension of `M`.
-/

open Semiformula Tarski.Structure

universe u v

variable {ξ : Type*} {M : Type u} {N : Type v} [ORingStructure M]

/-- `N` is an end extension of `M`: a model into which `M` embeds so that nothing new lies below
the image of `M`.
- [HP98, Definition IV.1.3(2)]
- [vO99, §3.1] -/
class EndExtension (M : outParam (Type u)) (N : Type v) [ORingStructure M] where
  [oring : ORingStructure N]
  emb : M ↪ₛ[ℒₒᵣ] N
  mem_range_of_lt {a : M} {b : N} : b < emb a → b ∈ Set.range emb

@[inherit_doc] infix:50 " ⊆ₑ " => EndExtension

/-- `N` is a proper end extension of `M`: not every element of `N` comes from `M`.
- [HP98, Definition IV.1.14]
- [vO99, §3.2] -/
class ProperEndExtension (M : outParam (Type u)) (N : Type v) [ORingStructure M]
    extends EndExtension M N where
  not_surjective : ¬Function.Surjective emb

@[inherit_doc] infix:50 " ⊂ₑ " => ProperEndExtension

namespace EndExtension

instance [hMN : M ⊆ₑ N] : Coe M N := ⟨fun x ↦ hMN.emb x⟩

instance [hMN : M ⊆ₑ N] : ORingStructure N := hMN.oring

variable [hMN : M ⊆ₑ N]

lemma emb_injective : Function.Injective hMN.emb := EmbeddingClass.map_inj hMN.emb

@[simp] lemma emb_zero : hMN.emb 0 = 0 := by
  simpa [Function.comp_def] using HomClass.func hMN.emb Language.Zero.zero ![]

@[simp] lemma emb_one : hMN.emb 1 = 1 := by
  simpa [Function.comp_def] using HomClass.func hMN.emb Language.One.one ![]

@[simp] lemma emb_add (x y : M) : hMN.emb (x + y) = hMN.emb x + hMN.emb y := by
  simpa [Function.comp_def] using HomClass.func hMN.emb Language.Add.add ![x, y]

@[simp] lemma emb_mul (x y : M) : hMN.emb (x * y) = hMN.emb x * hMN.emb y := by
  simpa [Function.comp_def] using HomClass.func hMN.emb Language.Mul.mul ![x, y]

@[simp] lemma emb_lt_emb {x y : M} : hMN.emb x < hMN.emb y ↔ x < y := by
  simpa [Function.comp_def] using EmbeddingClass.rel hMN.emb Language.LT.lt ![x, y]

lemma emb_eq_emb {x y : M} : hMN.emb x = hMN.emb y ↔ x = y := hMN.emb_injective.eq_iff

/-- A structure with an end extension modelling `𝗣𝗔⁻` is itself a model of `𝗣𝗔⁻`.
- [vO99, Exercise 40] -/
theorem models_peanoMinus [N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_theory_iff.mpr <| by
  have inj : Function.Injective hMN.emb := hMN.emb_injective
  intro σ hσ
  rcases hσ
  case equal hσ =>
    have h₁ : M↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance
    exact models_theory_iff.mp h₁ _ hσ
  case addZero =>
    suffices ∀ x : M, x + 0 = x by simpa [models_iff] using this
    intro x
    exact inj (by simp)
  case addAssoc =>
    suffices ∀ x y z : M, x + y + z = x + (y + z) by simpa [models_iff] using this
    intro x y z
    exact inj (by simp [add_assoc])
  case addComm =>
    suffices ∀ x y : M, x + y = y + x by simpa [models_iff] using this
    intro x y
    exact inj (by simp [add_comm])
  case addEqOfLt =>
    suffices ∀ x y : M, x < y → ∃ z < y + 1, x + z = y by
      simpa [models_iff, Semiformula.eval_bexsLTSucc] using this
    intro x y h
    obtain ⟨z, hz, hzeq⟩ :=
      Arithmetic.add_eq_of_lt_bounded (hMN.emb x) (hMN.emb y) (by simpa using h)
    have h₁ : z ≤ hMN.emb y := hzeq ▸ le_add_self
    obtain ⟨w, rfl⟩ : z ∈ Set.range hMN.emb :=
      h₁.lt_or_eq.elim hMN.mem_range_of_lt fun h₂ ↦ ⟨y, h₂.symm⟩
    exact ⟨w, hMN.emb_lt_emb.mp (by simpa using hz), inj (by simpa using hzeq)⟩
  case zeroLe =>
    suffices ∀ x : M, 0 ≤ x by simpa [models_iff, le_iff_of_eq_of_lt, le_def] using this
    intro x
    rcases le_def.mp (Arithmetic.zero_le (hMN.emb x)) with h | h
    · exact le_def.mpr <| Or.inl <| inj (by simpa using h)
    · exact le_def.mpr <| Or.inr <| hMN.emb_lt_emb.mp (by simpa using h)
  case zeroLtOne =>
    suffices (0 : M) < 1 by simpa [models_iff] using this
    exact hMN.emb_lt_emb.mp (by simp)
  case oneLeOfZeroLt =>
    suffices ∀ x : M, 0 < x → 1 ≤ x by
      simpa [models_iff, le_iff_of_eq_of_lt, le_def] using this
    intro x h
    have h₁ : (0 : N) < hMN.emb x := by simpa using hMN.emb_lt_emb.mpr h
    rcases le_def.mp (one_le_of_zero_lt _ h₁) with h₂ | h₂
    · exact le_def.mpr <| Or.inl <| inj (by simpa using h₂)
    · exact le_def.mpr <| Or.inr <| hMN.emb_lt_emb.mp (by simpa using h₂)
  case addLtAdd =>
    suffices ∀ x y z : M, x < y → x + z < y + z by simpa [models_iff] using this
    intro x y z h
    exact hMN.emb_lt_emb.mp (by simpa using add_lt_add _ _ (hMN.emb z) (hMN.emb_lt_emb.mpr h))
  case mulZero =>
    suffices ∀ x : M, x * 0 = 0 by simpa [models_iff] using this
    intro x
    exact inj (by simp)
  case mulOne =>
    suffices ∀ x : M, x * 1 = x by simpa [models_iff] using this
    intro x
    exact inj (by simp)
  case mulAssoc =>
    suffices ∀ x y z : M, x * y * z = x * (y * z) by simpa [models_iff] using this
    intro x y z
    exact inj (by simp [mul_assoc])
  case mulComm =>
    suffices ∀ x y : M, x * y = y * x by simpa [models_iff] using this
    intro x y
    exact inj (by simp [mul_comm])
  case mulLtMul =>
    suffices ∀ x y z : M, x < y → 0 < z → x * z < y * z by simpa [models_iff] using this
    intro x y z h hz
    have h₁ : (0 : N) < hMN.emb z := by simpa using hMN.emb_lt_emb.mpr hz
    exact hMN.emb_lt_emb.mp (by simpa using mul_lt_mul _ _ (hMN.emb z) (hMN.emb_lt_emb.mpr h) h₁)
  case distr =>
    suffices ∀ x y z : M, x * (y + z) = x * y + x * z by simpa [models_iff] using this
    intro x y z
    exact inj (by simp [mul_add])
  case ltIrrefl =>
    suffices ∀ x : M, ¬x < x by simpa [models_iff] using this
    intro x h
    exact lt_irrefl (hMN.emb x) (hMN.emb_lt_emb.mpr h)
  case ltTrans =>
    suffices ∀ x y z : M, x < y → y < z → x < z by simpa [models_iff] using this
    intro x y z hxy hyz
    exact hMN.emb_lt_emb.mp
      (Arithmetic.lt_trans _ _ _ (hMN.emb_lt_emb.mpr hxy) (hMN.emb_lt_emb.mpr hyz))
  case ltTri =>
    suffices ∀ x y : M, x < y ∨ x = y ∨ y < x by simpa [models_iff] using this
    intro x y
    exact (lt_tri (hMN.emb x) (hMN.emb y)).imp hMN.emb_lt_emb.mp
      (Or.imp hMN.emb_eq_emb.mp hMN.emb_lt_emb.mp)

/-- Satisfaction of a $\Sigma_1$ formula carries over from `M` to an end extension of `M`.
- [HP98, Fact IV.1.3(4)] -/
theorem eval_of_Sigma1 {n : ℕ} {φ : ArithmeticSemiformula ξ n} (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ)
    (e : Fin n → M) (f : ξ → M) : φ.Eval e f → φ.Eval (hMN.emb ∘ e) (hMN.emb ∘ f) :=
  Bounding.Hierarchy.arithmetic_sigma₁_induction'
    (P := fun n φ ↦ ∀ (e : Fin n → M) (f : ξ → M), φ.Eval e f → φ.Eval (hMN.emb ∘ e) (hMN.emb ∘ f))
    hφ
    (fun _ _ _ _ ↦ by simp)
    (fun _ _ _ h ↦ by simp at h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open hMN.emb (by simp)).mp h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open hMN.emb (by simp)).mp h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open hMN.emb (by simp)).mp h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open hMN.emb (by simp)).mp h)
    (fun _ _ _ _ _ ih₁ ih₂ e f h ↦ ⟨ih₁ e f h.1, ih₂ e f h.2⟩)
    (fun _ _ _ _ _ ih₁ ih₂ e f h ↦ h.imp (ih₁ e f) (ih₂ e f))
    (fun _ t θ _ ih e f h ↦ by
      change (θ.ballLT t).Eval (hMN.emb ∘ e) (hMN.emb ∘ f)
      simp only [eval_ballLT, ← HomClass.val_term hMN.emb e f t]
      intro y hy
      obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt hy
      rw [← Matrix.comp_vecCons'']
      exact ih (x :> e) f (eval_ballLT.mp h x (by simpa using hy)))
    (fun _ _ _ ih e f ↦ by
      rintro ⟨x, hx⟩
      exact ⟨hMN.emb x, by rw [← Matrix.comp_vecCons'']; exact ih (x :> e) f hx⟩)
    e f

/-- A theory all of whose members are $\Pi_1$ sentences holds in `M` as soon as it holds in an
end extension of `M`.
- [HP98, Remark IV.1.18, Remark IV.1.21(2)] -/
theorem models_of_Pi1 {T : ArithmeticTheory} (hT : ∀ σ ∈ T, ℬ[<, ℒₒᵣ].Hierarchy 𝚷 1 σ)
    [N↓[ℒₒᵣ] ⊧* T] :
    M↓[ℒₒᵣ] ⊧* T :=
  models_theory_iff.mpr <| by
    intro σ hσ
    by_contra! h
    apply notModels_iff.mpr ?_ <| models_theory_iff.mp (inferInstance : N↓[ℒₒᵣ] ⊧* T) σ hσ
    · suffices (∼σ).Eval ![] Empty.elim by simpa
      exact Eval.of_eq
        (hMN.eval_of_Sigma1 (hT σ hσ).neg ![] Empty.elim (by simpa [models_iff] using h))
        (funext (·.elim0))
        (funext (·.elim))

/-- A $\Pi_1$-axiomatizable theory holds in `M` as soon as it holds in an end extension of `M`.
- [HP98, Remark IV.1.18, Remark IV.1.21(2)] -/
theorem models_of_Pi1Axiomatizable {T : ArithmeticTheory}
    (hT : Axiomatizable (ℬ[<, ℒₒᵣ].Hierarchy 𝚷 1) T) [N↓[ℒₒᵣ] ⊧* T] : M↓[ℒₒᵣ] ⊧* T := by
  obtain ⟨U, hU, hTU⟩ := hT
  have : U ⪯ T := hTU.symm.le
  have : T ⪯ U := hTU.le
  have : N↓[ℒₒᵣ] ⊧* U := models_of_subtheory ‹N↓[ℒₒᵣ] ⊧* T›
  exact models_of_subtheory (hMN.models_of_Pi1 hU)

end EndExtension

section Absolute

/-- `φ` is absolute for `T` when it takes the same truth value in every model of `T` as in every
end extension of that model which again models `T`. -/
def Absolute (T : ArithmeticTheory) {n : ℕ} (φ : ArithmeticSemiformula ξ n) : Prop :=
  ∀ (M : Type u) (N : Type v) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [hMN : M ⊆ₑ N] [N↓[ℒₒᵣ] ⊧* T]
    (e : Fin n → M) (f : ξ → M), φ.Eval e f ↔ φ.Eval (hMN.emb ∘ e) (hMN.emb ∘ f)

lemma absolute_of_open (T : ArithmeticTheory) {n} {φ : ArithmeticSemiformula ξ n} (hφ : φ.Open) :
    Absolute T φ := by
  intro M N _ _ hMN _ e f
  exact eval_hom_iff_of_open hMN.emb hφ

-- The universes of the models are parameters of `Absolute`, so the closure lemmas below pin
-- them explicitly: without the annotation each occurrence is generalized on its own.

variable {T : ArithmeticTheory} {n : ℕ}
  {φ ψ : ArithmeticSemiformula ξ n}
  {θ : ArithmeticSemiformula ξ (n + 1)} {t : ArithmeticSemiterm ξ n}

lemma and_absolute (hφ : Absolute.{u, v, _} T φ) (hψ : Absolute.{u, v, _} T ψ) :
    Absolute.{u, v, _} T (φ ⋏ ψ) := by
  intro M N _ _ hMN _ e f;
  simp [hφ M N e f, hψ M N e f]

lemma or_absolute (hφ : Absolute.{u, v, _} T φ) (hψ : Absolute.{u, v, _} T ψ) :
    Absolute.{u, v, _} T (φ ⋎ ψ) := by
  intro M N _ _ hMN _ e f;
  simp [hφ M N e f, hψ M N e f]

lemma ballLT_absolute (hθ : Absolute.{u, v, _} T θ) : Absolute.{u, v, _} T (θ.ballLT t) := by
  intro M N _ _ hMN _ e f
  simp only [eval_ballLT, ← HomClass.val_term hMN.emb e f t]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt hy
    rw [← Matrix.comp_vecCons'']
    exact (hθ M N (x :> e) f).mp (h x (by simpa using hy))
  · intro h x hx
    have h₁ := h (hMN.emb x) (by simpa using hx)
    rw [← Matrix.comp_vecCons''] at h₁
    exact (hθ M N (x :> e) f).mpr h₁

lemma bexsLT_absolute (hθ : Absolute.{u, v, _} T θ) : Absolute.{u, v, _} T (θ.bexsLT t) := by
  intro M N _ _ hMN _ e f
  simp only [eval_bexsLT, ← HomClass.val_term hMN.emb e f t]
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨hMN.emb x, by simpa using hx, ?_⟩
    rw [← Matrix.comp_vecCons'']
    exact (hθ M N (x :> e) f).mp h
  · rintro ⟨y, hy, h⟩
    obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt hy
    rw [← Matrix.comp_vecCons''] at h
    exact ⟨x, by simpa using hy, (hθ M N (x :> e) f).mpr h⟩

/-- Bounded formulas take the same truth value along an end extension.
- [HP98, Fact IV.1.3(4), Remark IV.1.18]
- [vO99, Exercise 37] -/
@[simp, grind .]
theorem absolute_of_bounded (hφ : ℬ[<, ℒₒᵣ].Closure φ) : Absolute T φ :=
  bounded_induction_open (P := fun _ φ ↦ Absolute T φ)
    (fun _ _ hφ ↦ absolute_of_open T hφ)
    (fun _ _ _ _ _ ihφ ihψ ↦ and_absolute ihφ ihψ)
    (fun _ _ _ _ _ ihφ ihψ ↦ or_absolute ihφ ihψ)
    (fun _ _ _ _ ih ↦ ballLT_absolute ih)
    (fun _ _ _ _ ih ↦ bexsLT_absolute ih)
    n φ hφ

end Absolute

end EndExtensions

section Cuts

/-! ## Cuts

A cut of an `ℒₒᵣ`-structure `M` is a subset closed under successor and downward closed under `<`.
A cut closed under the operations of the language is a substructure of `M`, and `M` is an end
extension of it.
-/

open Semiformula Tarski.Structure

universe u v

variable {M : Type u} [ORingStructure M]

/-- A cut of `M`: a subset closed under successor and downward closed under `<`.
- [HP98, Definition IV.1.14] -/
structure Cut (M : Type u) [ORingStructure M] where
  carrier : Set M
  succ_mem {a : M} : a ∈ carrier → a + 1 ∈ carrier
  mem_of_lt {a b : M} : a < b → b ∈ carrier → a ∈ carrier

namespace Cut

/-- A cut closed under the operations of `ℒₒᵣ`, hence a substructure of `M`.
- [HP98, Definition IV.2.8(2)] -/
class Closed (I : Cut M) : Prop where
  zero_mem : (0 : M) ∈ I.carrier
  one_mem : (1 : M) ∈ I.carrier
  add_mem {a b : M} : a ∈ I.carrier → b ∈ I.carrier → a + b ∈ I.carrier
  mul_mem {a b : M} : a ∈ I.carrier → b ∈ I.carrier → a * b ∈ I.carrier

variable (I : Cut M) [hI : I.Closed]

instance oringStructure : ORingStructure I.carrier where
  zero := ⟨0, hI.zero_mem⟩
  one := ⟨1, hI.one_mem⟩
  add a b := ⟨a.1 + b.1, hI.add_mem a.2 b.2⟩
  mul a b := ⟨a.1 * b.1, hI.mul_mem a.2 b.2⟩
  lt a b := a.1 < b.1

/-- `M` is an end extension of each of its cuts closed under the operations.
- [HP98, Definition IV.1.3(2)] -/
@[instance_reducible]
def endExtension : I.carrier ⊆ₑ M where
  emb := {
    toFun := Subtype.val,
    func' f v := by cases f <;> rfl
    rel' r _ := by cases r; exacts [congrArg Subtype.val, id]
    toFun_inj := Subtype.val_injective
    rel_inv' r _ := by cases r; exacts [Subtype.ext, id]
  }
  mem_range_of_lt {a b} h := ⟨⟨b, I.mem_of_lt h a.2⟩, rfl⟩

@[simp]
lemma endExtension_emb (x : I.carrier) : I.endExtension.emb x = x.val := rfl

end Cut

namespace EndExtension

variable {N : Type v} [hMN : M ⊆ₑ N]

private lemma eval_of_endExtension [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {φ : ArithmeticSemiformula ℕ 1}
    (hφ : ℬ[<, ℒₒᵣ].Closure φ)
    (v : ℕ → M) (h0 : φ.Eval ![0] v) (hs : ∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) (a : M) :
    φ.Eval ![a] v := by
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := hMN.models_peanoMinus
  have h₁ : ∀ x : M, φ.Eval ![x] v ↔ φ.Eval ![hMN.emb x] (hMN.emb ∘ v) := by
    intro x;
    simpa [Matrix.comp_vecCons'', Matrix.empty_eq] using
      absolute_of_bounded (T := 𝗣𝗔⁻) hφ M N ![x] v
  have h₂ : ∀ y : N, y < hMN.emb a + 1 → φ.Eval ![y] (hMN.emb ∘ v) := by
    refine InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0)
      ⟨(hMN.emb a + 1) :>ₙ fun j ↦ hMN.emb (v j),
        “#0 < &0” 🡒 (Rew.rewriteMap Nat.succ ▹ φ), by simp [hφ.hierarchy],
        by intro x; simp [Semiformula.eval_rewriteMap, Function.comp_def]⟩
      (by intro _; simpa using (h₁ 0).mp h0) ?_
    intro y ih hy
    have h₃ : y < hMN.emb a := lt_of_lt_of_le (lt_add_one y) (lt_succ_iff_le.mp hy)
    obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt h₃
    simpa using (h₁ (x + 1)).mp (hs x ((h₁ x).mpr (ih (lt_trans h₃ (lt_add_one _)))))
  exact (h₁ a).mpr (h₂ (hMN.emb a) (by simp))

/-- A structure with an end extension modelling `𝗜𝚺₀` is itself a model of `𝗜𝚺₀`.
- [HP98, Remark IV.1.21(2)] -/
theorem models_ISigma0 [hN : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
  simp only [Semantics.ModelsSet.union_iff, InductionScheme];
  and_intros;
  · exact hMN.models_peanoMinus
  · apply Semantics.ModelsSet.setOf_iff.mpr;
    rintro _ ⟨φ, hφ, rfl⟩
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs]
      using hMN.eval_of_endExtension
        (Bounding.PrenexHierarchy.zero_iff_bounded.mp hφ)

end EndExtension

end Cuts

section ProperCuts

/-! ## Proper cuts

No proper cut is definable by a $\Sigma_0$ formula with parameters in a model of `𝗜𝚺₀`, and no
model of `𝗜𝚫 n` has a proper cut whose membership relation and complement are both definable by
prenex $\Sigma_n$ formulas with parameters.
-/

open Semiformula Tarski.Structure

variable {M : Type*} [ORingStructure M]

/-- A cut is proper when it contains `0` and omits some element.
- [HP98, Definition IV.1.14]
- [Sla04, §1.1] -/
structure Cut.Proper (I : Cut M) : Prop where
  zero_mem : (0 : M) ∈ I.carrier
  exists_not_mem : ∃ c, c ∉ I.carrier

/-- A cut definable by a $\Sigma_0$ formula with parameters is not proper.
- [HP98, Observation IV.1.15] -/
lemma Cut.not_proper_of_definable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] (I : Cut M)
    (hI : 𝚺ᴬ₀.DefinablePred (· ∈ I.carrier)) : ¬I.Proper := by
  rintro ⟨h0, c, hc⟩
  exact hc <| ISigma0.succ_induction (P := (· ∈ I.carrier)) hI h0 (fun _ hx ↦ I.succ_mem hx) c

/-- A proper cut whose membership relation and complement are both definable by prenex $\Sigma_n$
formulas with parameters refutes $\Delta_s$ induction.
- [Sla04, §1.1] -/
lemma not_models_IDelta_of_proper_cut (I : Cut M) (n : ℕ) (hI : I.Proper)
    (hσ : PrenexDefinablePred 𝚺 n (· ∈ I.carrier))
    (hπ : PrenexDefinablePred 𝚺 n (· ∉ I.carrier)) : ¬M↓[ℒₒᵣ] ⊧* 𝗜𝚫 n := by
  intro hM
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_ss hM Set.subset_union_left
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
  have : M↓[ℒₒᵣ] ⊧* DeltaInductionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n) :=
    models_of_ss hM Set.subset_union_right
  obtain ⟨e₁, φ, hφ, hφe⟩ := PrenexDefinable.exists_eval_iff hσ
  obtain ⟨e₂, ψ, hψ, hψe⟩ := PrenexDefinable.exists_eval_iff hπ
  have heven : ∀ k : ℕ, 2 * k % 2 = 0 := by intro k; omega
  have hodd : ∀ k : ℕ, (2 * k + 1) % 2 ≠ 0 := by intro k; omega
  have hhalf₁ : ∀ k : ℕ, 2 * k / 2 = k := by intro k; omega
  have hhalf₂ : ∀ k : ℕ, (2 * k + 1) / 2 = k := by intro k; omega
  let e : ℕ → M := fun k ↦ if k % 2 = 0 then e₁ (k / 2) else e₂ (k / 2)
  have hφ' : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n (Rew.rewriteMap (fun k : ℕ ↦ 2 * k) ▹ φ) :=
    hφ.rew _
  have hψ' : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n (Rew.rewriteMap (fun k : ℕ ↦ 2 * k + 1) ▹ ψ) :=
    hψ.rew _
  have h₁ : ∀ x : M, (Rew.rewriteMap (fun k : ℕ ↦ 2 * k) ▹ φ).Eval ![x] e ↔ x ∈ I.carrier := by
    intro x
    simpa [Semiformula.eval_rewriteMap, e, heven, hhalf₁] using (hφe ![x]).symm
  have h₂ : ∀ x : M, (Rew.rewriteMap (fun k : ℕ ↦ 2 * k + 1) ▹ ψ).Eval ![x] e ↔ x ∉ I.carrier := by
    intro x
    simpa [Semiformula.eval_rewriteMap, e, hodd, hhalf₂] using (hψe ![x]).symm
  obtain ⟨h0, c, hc⟩ := hI
  have hind := (models_deltaInd_iff _ _).mp
    (Theory.models (T := DeltaInductionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n)) M
      (mem_DeltaInductionScheme_of_mem hφ' hψ')) e
    (fun x ↦ by rw [h₁ x, h₂ x, not_not])
    ((h₁ 0).mpr h0) (fun x hx ↦ (h₁ (x + 1)).mpr (I.succ_mem ((h₁ x).mp hx)))
  exact hc ((h₁ c).mp (hind c))

end ProperCuts

section Overspill

/-! ## Overspill

In a proper end extension satisfying induction for a hierarchy class, a formula of that class
which holds at every element of the base model holds below some element outside the base model.
-/

open Semiformula

universe u v

variable {M : Type u} {N : Type v} [ORingStructure M] [hMN : M ⊂ₑ N]

/-- Overspill: a formula of the induction class holding at every element of the base model holds
below some element outside it.
- [HP98, Corollary IV.1.16]
- [vO99, Lemma 3.2, Corollary 3.3] -/
theorem overspill (Γ : Polarity) (m : ℕ) [N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ m]
    {φ : ArithmeticSemiformula ℕ 1} (hφ : ℬ[<, ℒₒᵣ].Hierarchy Γ m φ) (e : ℕ → N)
    (h : ∀ a : M, φ.Eval ![hMN.emb a] e) :
    ∃ c : N, c ∉ Set.range hMN.emb ∧ ∀ x < c, φ.Eval ![x] e := by
  have : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ m)
  by_contra! hc
  have h₁ : ∀ x : N, (∀ y < x, φ.Eval ![y] e) → x ∈ Set.range hMN.emb := by grind;
  have h₂ : ∀ x : N, (∀ y < x, φ.Eval ![y] e) → ∀ y < x + 1, φ.Eval ![y] e := by
    intro x ih y hy;
    obtain ⟨a, rfl⟩ := h₁ x ih;
    rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hy) with hy' | rfl
    · exact ih y hy'
    · exact h a
  have h₃ : ∀ x : N, ∀ y < x, φ.Eval ![y] e :=
    InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].Hierarchy Γ m)
      ⟨e, (φ/[#0]).ballLT #0, by simp [hφ], fun x ↦ by simp [eval_ballLT]⟩
      (by simp) h₂
  exact hMN.not_surjective fun x ↦ h₁ x (h₃ x)

end Overspill

section ProperEndExtensionOfBSigma1

/-! ## End extensions of models of $\mathsf{B}\Sigma_1$

A model of $\mathsf{I}\Delta_0$ with a proper end extension to a model of $\mathsf{I}\Delta_0$
satisfies $\mathsf{B}\Sigma_1$, and a countable model of $\mathsf{B}\Sigma_1 + \mathrm{Exp}$ has
such an extension. Whether the hypothesis $\mathrm{Exp}$ can be dropped is open.

- [Kay91, Chapter 16, p. 269]
- [WP89]
-/

/-- Every countable model of $\mathsf{B}\Sigma_1$ has a proper end extension to a model of
$\mathsf{I}\Delta_0$. An open problem.
- [Kay91, Chapter 16, p. 269]
- [WP89] -/
def ExistsProperEndExtensionOfBSigma1 : Prop :=
  ∀ (M : Type) [Countable M] [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗕𝚺1],
    ∃ (N : Type) (_ : M ⊂ₑ N), N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀

end ProperEndExtensionOfBSigma1

end FFL.FirstOrder.Arithmetic
