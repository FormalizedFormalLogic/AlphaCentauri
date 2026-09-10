module

public import AlphaCentauri.Hierarchy.DeltaZero
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-! # End extensions

An end extension of an `ℒₒᵣ`-structure `M` is a structure into which `M` embeds with nothing new
below the image of `M`. Bounded formulas take the same truth value in `M` and in an end extension
of it, $\Sigma_1$ formulas satisfied in `M` stay satisfied in an end extension of it, and both
`𝗣𝗔⁻` and any theory axiomatized by $\Pi_1$ sentences hold in `M` as soon as they hold in an end
extension of `M`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula Structure

variable {ξ : Type*} {M : Type u} [ORingStructure M]

/-- An end extension of `M`: a model into which `M` embeds so that nothing new lies below `M`.
- [HP98, Definition IV.1.3(2)]
- [vO99, §3.1] -/
structure EndExtensionOf (M : Type u) [ORingStructure M] where
  carrier : Type u
  [oring : ORingStructure carrier]
  emb : M ↪ₛ[ℒₒᵣ] carrier
  mem_range_of_lt {a : M} {b : carrier} : b < emb a → b ∈ Set.range emb

namespace EndExtensionOf

instance : CoeSort (EndExtensionOf M) (Type u) := ⟨EndExtensionOf.carrier⟩

instance : CoeFun (EndExtensionOf M) (λ N => M → N.carrier) := ⟨λ N => N.emb⟩

instance (N : EndExtensionOf M) : ORingStructure N := N.oring

variable (N : EndExtensionOf M)

lemma emb_injective : Function.Injective N.emb := EmbeddingClass.map_inj N.emb

@[simp] lemma emb_zero : N 0 = 0 := by
  simpa [Function.comp_def] using HomClass.func N.emb Language.Zero.zero ![]

@[simp] lemma emb_one : N 1 = 1 := by
  simpa [Function.comp_def] using HomClass.func N.emb Language.One.one ![]

@[simp] lemma emb_add (x y : M) : N (x + y) = N x + N y := by
  simpa [Function.comp_def] using HomClass.func N.emb Language.Add.add ![x, y]

@[simp] lemma emb_mul (x y : M) : N (x * y) = N x * N y := by
  simpa [Function.comp_def] using HomClass.func N.emb Language.Mul.mul ![x, y]

@[simp] lemma emb_lt_emb {x y : M} : N x < N y ↔ x < y := by
  simpa [Function.comp_def] using EmbeddingClass.rel N.emb Language.LT.lt ![x, y]

lemma emb_eq_emb {x y : M} : N x = N y ↔ x = y := N.emb_injective.eq_iff

/-- `N` is a proper end extension of `M`: not every element of `N` comes from `M`.
- [HP98, Definition IV.1.14]
- [vO99, §3.2] -/
def IsProper : Prop := ¬Function.Surjective N.emb

lemma isProper_iff : N.IsProper ↔ ∃ c : N, c ∉ Set.range N.emb := by
  simp [IsProper, Function.Surjective, Set.range, not_forall]

/-- A structure with an end extension modelling `𝗣𝗔⁻` is itself a model of `𝗣𝗔⁻`.
- [vO99, Exercise 40] -/
theorem models_peanoMinus [N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_theory_iff.mpr <| by
  have inj : Function.Injective N.emb := N.emb_injective
  intro σ hσ
  rcases hσ
  case equal hσ =>
    have h₁ : M↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance
    exact models_theory_iff.mp h₁ _ hσ
  case addZero =>
    suffices ∀ x : M, x + 0 = x by simpa [models_iff] using this
    exact fun x ↦ inj (by simp)
  case addAssoc =>
    suffices ∀ x y z : M, x + y + z = x + (y + z) by simpa [models_iff] using this
    exact fun x y z ↦ inj (by simp [add_assoc])
  case addComm =>
    suffices ∀ x y : M, x + y = y + x by simpa [models_iff] using this
    exact fun x y ↦ inj (by simp [add_comm])
  case addEqOfLt =>
    suffices ∀ x y : M, x < y → ∃ z, x + z = y by simpa [models_iff] using this
    intro x y h
    obtain ⟨z, hz⟩ := Arithmetic.add_eq_of_lt (N.emb x) (N.emb y) (by simpa using h)
    have h₁ : z ≤ N.emb y := hz ▸ le_add_self
    obtain ⟨w, rfl⟩ : z ∈ Set.range N.emb :=
      h₁.lt_or_eq.elim N.mem_range_of_lt fun h₂ ↦ ⟨y, h₂.symm⟩
    exact ⟨w, inj (by simpa using hz)⟩
  case zeroLe =>
    suffices ∀ x : M, 0 ≤ x by simpa [models_iff, le_iff_of_eq_of_lt, le_def] using this
    intro x
    rcases le_def.mp (Arithmetic.zero_le (N.emb x)) with h | h
    · exact le_def.mpr (Or.inl (inj (by simpa using h)))
    · exact le_def.mpr (Or.inr (N.emb_lt_emb.mp (by simpa using h)))
  case zeroLtOne =>
    suffices (0 : M) < 1 by simpa [models_iff] using this
    exact N.emb_lt_emb.mp (by simp)
  case oneLeOfZeroLt =>
    suffices ∀ x : M, 0 < x → 1 ≤ x by
      simpa [models_iff, le_iff_of_eq_of_lt, le_def] using this
    intro x h
    have h₁ : (0 : N) < N.emb x := by simpa using N.emb_lt_emb.mpr h
    rcases le_def.mp (one_le_of_zero_lt _ h₁) with h₂ | h₂
    · exact le_def.mpr (Or.inl (inj (by simpa using h₂)))
    · exact le_def.mpr (Or.inr (N.emb_lt_emb.mp (by simpa using h₂)))
  case addLtAdd =>
    suffices ∀ x y z : M, x < y → x + z < y + z by simpa [models_iff] using this
    intro x y z h
    exact N.emb_lt_emb.mp (by simpa using add_lt_add _ _ (N.emb z) (N.emb_lt_emb.mpr h))
  case mulZero =>
    suffices ∀ x : M, x * 0 = 0 by simpa [models_iff] using this
    exact fun x ↦ inj (by simp)
  case mulOne =>
    suffices ∀ x : M, x * 1 = x by simpa [models_iff] using this
    exact fun x ↦ inj (by simp)
  case mulAssoc =>
    suffices ∀ x y z : M, x * y * z = x * (y * z) by simpa [models_iff] using this
    exact fun x y z ↦ inj (by simp [mul_assoc])
  case mulComm =>
    suffices ∀ x y : M, x * y = y * x by simpa [models_iff] using this
    exact fun x y ↦ inj (by simp [mul_comm])
  case mulLtMul =>
    suffices ∀ x y z : M, x < y → 0 < z → x * z < y * z by simpa [models_iff] using this
    intro x y z h hz
    have h₁ : (0 : N) < N.emb z := by simpa using N.emb_lt_emb.mpr hz
    exact N.emb_lt_emb.mp (by simpa using mul_lt_mul _ _ (N.emb z) (N.emb_lt_emb.mpr h) h₁)
  case distr =>
    suffices ∀ x y z : M, x * (y + z) = x * y + x * z by simpa [models_iff] using this
    exact fun x y z ↦ inj (by simp [mul_add])
  case ltIrrefl =>
    suffices ∀ x : M, ¬x < x by simpa [models_iff] using this
    exact fun x h ↦ lt_irrefl (N.emb x) (N.emb_lt_emb.mpr h)
  case ltTrans =>
    suffices ∀ x y z : M, x < y → y < z → x < z by simpa [models_iff] using this
    intro x y z hxy hyz
    exact N.emb_lt_emb.mp (Arithmetic.lt_trans _ _ _ (N.emb_lt_emb.mpr hxy) (N.emb_lt_emb.mpr hyz))
  case ltTri =>
    suffices ∀ x y : M, x < y ∨ x = y ∨ y < x by simpa [models_iff] using this
    intro x y
    exact (lt_tri (N.emb x) (N.emb y)).imp N.emb_lt_emb.mp
      (Or.imp N.emb_eq_emb.mp N.emb_lt_emb.mp)

/-- Satisfaction of a $\Sigma_1$ formula carries over from `M` to an end extension of `M`.
- [HP98, Fact IV.1.3(4)] -/
theorem eval_of_Sigma1 {n : ℕ} {φ : ArithmeticSemiformula ξ n} (hφ : Hierarchy 𝚺 1 φ)
    (e : Fin n → M) (f : ξ → M) : φ.Eval e f → φ.Eval (N ∘ e) (N ∘ f) :=
  sigma₁_induction' (P := fun n φ ↦ ∀ (e : Fin n → M) (f : ξ → M),
      φ.Eval e f → φ.Eval (N ∘ e) (N ∘ f)) hφ
    (fun _ _ _ _ ↦ by simp)
    (fun _ _ _ h ↦ by simp at h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open N.emb (by simp)).mp h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open N.emb (by simp)).mp h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open N.emb (by simp)).mp h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open N.emb (by simp)).mp h)
    (fun _ _ _ _ _ ih₁ ih₂ e f h ↦ ⟨ih₁ e f h.1, ih₂ e f h.2⟩)
    (fun _ _ _ _ _ ih₁ ih₂ e f h ↦ h.imp (ih₁ e f) (ih₂ e f))
    (fun _ t θ _ ih e f h ↦ by
      show (θ.ballLT t).Eval (N ∘ e) (N ∘ f)
      simp only [eval_ballLT, ← HomClass.val_term N.emb e f t]
      intro y hy
      obtain ⟨x, rfl⟩ := N.mem_range_of_lt hy
      rw [← Matrix.comp_vecCons'']
      exact ih (x :> e) f (eval_ballLT.mp h x (by simpa using hy)))
    (fun _ _ _ ih e f ↦ by
      rintro ⟨x, hx⟩
      exact ⟨N x, by rw [← Matrix.comp_vecCons'']; exact ih (x :> e) f hx⟩)
    e f

/-- A theory axiomatized by $\Pi_1$ sentences holds in `M` as soon as it holds in an end
extension of `M`.
- [HP98, Remark IV.1.18, Remark IV.1.21(2)] -/
theorem models_of_Pi1 {T : ArithmeticTheory} (hT : ∀ σ ∈ T, Hierarchy 𝚷 1 σ) [N↓[ℒₒᵣ] ⊧* T] :
    M↓[ℒₒᵣ] ⊧* T :=
  models_theory_iff.mpr <| by
    intro σ hσ
    by_contra! h
    apply notModels_iff.mpr ?_ <| models_theory_iff.mp (inferInstance : N.carrier↓[ℒₒᵣ] ⊧* T) σ hσ
    · suffices (∼σ).Eval ![] Empty.elim by simpa
      exact Eval.of_eq
        (N.eval_of_Sigma1 (hT σ hσ).neg ![] Empty.elim (by simpa [models_iff] using h))
        (funext (·.elim0))
        (funext (·.elim))

end EndExtensionOf

section Absolute

/-- `φ` is absolute for `T` when it takes the same truth value in every model of `T` as in every
end extension of that model which again models `T`. -/
def Absolute (T : ArithmeticTheory) {n : ℕ} (φ : ArithmeticSemiformula ξ n) : Prop :=
  ∀ (M : Type u) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (N : EndExtensionOf M) [N↓[ℒₒᵣ] ⊧* T]
    (e : Fin n → M) (f : ξ → M), φ.Eval e f ↔ φ.Eval (N ∘ e) (N ∘ f)

lemma absolute_of_open (T : ArithmeticTheory) {n} {φ : ArithmeticSemiformula ξ n} (hφ : φ.Open) :
    Absolute T φ := by
  intro M _ _ N _ e f
  exact eval_hom_iff_of_open N.emb hφ

-- The universe of the models is a parameter of `Absolute`, so the closure lemmas below pin it
-- explicitly: without the annotation each occurrence is generalized on its own.

variable {T : ArithmeticTheory} {n : ℕ}
  {φ ψ : ArithmeticSemiformula ξ n}
  {θ : ArithmeticSemiformula ξ (n + 1)} {t : ArithmeticSemiterm ξ n}

lemma and_absolute (hφ : Absolute.{_, u} T φ) (hψ : Absolute.{_, u} T ψ) :
    Absolute.{_, u} T (φ ⋏ ψ) := by
  intro M _ _ N _ e f;
  simp [hφ M N e f, hψ M N e f]

lemma or_absolute (hφ : Absolute.{_, u} T φ) (hψ : Absolute.{_, u} T ψ) :
    Absolute.{_, u} T (φ ⋎ ψ) := by
  intro M _ _ N _ e f;
  simp [hφ M N e f, hψ M N e f]

lemma ballLT_absolute (hθ : Absolute.{_, u} T θ) : Absolute.{_, u} T (θ.ballLT t) := by
  intro M _ _ N _ e f
  simp only [eval_ballLT, ← HomClass.val_term N.emb e f t]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := N.mem_range_of_lt hy
    rw [← Matrix.comp_vecCons'']
    exact (hθ M N (x :> e) f).mp (h x (by simpa using hy))
  · intro h x hx
    have h₁ := h (N x) (by simpa using hx)
    rw [← Matrix.comp_vecCons''] at h₁
    exact (hθ M N (x :> e) f).mpr h₁

lemma bexsLT_absolute (hθ : Absolute.{_, u} T θ) : Absolute.{_, u} T (θ.bexsLT t) := by
  intro M _ _ N _ e f
  simp only [eval_bexsLT, ← HomClass.val_term N.emb e f t]
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨N x, by simpa using hx, ?_⟩
    rw [← Matrix.comp_vecCons'']
    exact (hθ M N (x :> e) f).mp h
  · rintro ⟨y, hy, h⟩
    obtain ⟨x, rfl⟩ := N.mem_range_of_lt hy
    rw [← Matrix.comp_vecCons''] at h
    exact ⟨x, by simpa using hy, (hθ M N (x :> e) f).mpr h⟩

/-- Bounded formulas take the same truth value along an end extension.
- [HP98, Fact IV.1.3(4), Remark IV.1.18]
- [vO99, Exercise 37] -/
@[simp, grind .]
theorem absolute_of_deltaZero (hφ : Hierarchy 𝚺 0 φ) : Absolute T φ :=
  delta₀_induction_open (P := fun _ φ ↦ Absolute T φ)
    (fun _ _ hφ ↦ absolute_of_open T hφ)
    (fun _ _ _ _ _ ihφ ihψ ↦ and_absolute ihφ ihψ)
    (fun _ _ _ _ _ ihφ ihψ ↦ or_absolute ihφ ihψ)
    (fun _ _ _ _ ih ↦ ballLT_absolute ih)
    (fun _ _ _ _ ih ↦ bexsLT_absolute ih)
    n φ hφ

end Absolute

end FFL.FirstOrder.Arithmetic
