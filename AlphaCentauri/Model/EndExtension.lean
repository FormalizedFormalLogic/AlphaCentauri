module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Embedding
public import AlphaCentauri.ToFoundation.FirstOrder.Bounded
public import AlphaCentauri.ToFoundation.FirstOrder.ElementarySubstructure
public import AlphaCentauri.Axiomatizability.Basic
public import Foundation.FirstOrder.Arithmetic.Collection.Basic
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Absoluteness

/-! # End extensions

An end extension of an `ℒₒᵣ`-structure `M` is a structure into which `M` embeds with nothing new
below the image of `M`. Bounded formulas take the same truth value in `M` and in an end extension
of it, and $\Sigma_1$ formulas satisfied in `M` stay satisfied in an end extension of it. `𝗣𝗔⁻`,
`𝗜𝚺₀` and any theory axiomatized by $\Pi_1$ sentences hold in `M` as soon as they hold in an end
extension of `M`. An end extension is a $\Delta_0$-elementary substructure.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic


open Semiformula Tarski.Structure

universe u v w

variable {M : Type u} {N : Type v} {K : Type w} [ORingStructure M] [ORingStructure N]
  [ORingStructure K]

/-- An end extension of `M` to `N`: an embedding of `M` into `N` with nothing new below its image.
- [HP98, Definition IV.1.3(2)]
- [vO99, §3.1] -/
structure EndExtension (M : Type u) (N : Type v) [ORingStructure M] [ORingStructure N] where
  emb : M ↪ₛ[ℒₒᵣ] N
  mem_range_of_lt {a : M} {b : N} : b < emb a → b ∈ Set.range emb

@[inherit_doc]
infix:50 " ⊆ₑ " => EndExtension

/-- A proper end extension: an end extension which is not surjective.
- [HP98, Definition IV.1.14]
- [vO99, §3.2] -/
structure ProperEndExtension (M : Type u) (N : Type v) [ORingStructure M] [ORingStructure N]
    extends EndExtension M N where
  not_surjective : ¬Function.Surjective emb

@[inherit_doc]
infix:50 " ⊂ₑ " => ProperEndExtension

instance : CoeFun (M ⊆ₑ N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

instance : CoeFun (M ⊂ₑ N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

namespace EndExtension

variable (e : M ⊆ₑ N)

lemma emb_injective : Function.Injective e.emb := EmbeddingClass.map_inj e.emb

@[simp, grind =]
lemma emb_lt_emb {x y : M} : e x < e y ↔ x < y :=
  EmbeddingClass.map_lt_map_iff e.emb

@[grind =]
lemma emb_eq_emb {x y : M} : e x = e y ↔ x = y := e.emb_injective.eq_iff

instance : ℬ[<, ℒₒᵣ].IsInitial e.emb where
  operator_iff := by
    intro R hR a b
    obtain rfl := Set.mem_singleton_iff.mp hR
    simp
  initial := by
    intro R hR a b hb
    obtain rfl := Set.mem_singleton_iff.mp hR
    exact e.mem_range_of_lt (by simpa using hb)

variable (M) in
/-- The identity end extension. -/
@[refl]
protected def refl : M ⊆ₑ M where
  emb := {
    toFun := id
    func' _ _ := rfl
    rel' _ _ h := h
    toFun_inj := Function.injective_id
    rel_inv' _ _ h := h
  }
  mem_range_of_lt {_ b} _ := ⟨b, rfl⟩

@[simp]
lemma refl_apply (x : M) : EndExtension.refl M x = x := rfl

/-- The composition of end extensions. -/
@[trans]
protected def trans (e₁ : M ⊆ₑ N) (e₂ : N ⊆ₑ K) : M ⊆ₑ K where
  emb := {
    toFun := e₂ ∘ e₁
    func' f v := by simp [HomClass.func e₁.emb, HomClass.func e₂.emb, Function.comp_def]
    rel' r v h := HomClass.rel e₂.emb r _ (HomClass.rel e₁.emb r v h)
    toFun_inj := e₂.emb_injective.comp e₁.emb_injective
    rel_inv' r v h :=
      EmbeddingClass.map_rel_inv e₁.emb r v (EmbeddingClass.map_rel_inv e₂.emb r _ h)
  }
  mem_range_of_lt {a b} h := by
    obtain ⟨c, rfl⟩ := e₂.mem_range_of_lt h
    obtain ⟨x, rfl⟩ := e₁.mem_range_of_lt (e₂.emb_lt_emb.mp h)
    use x
    rfl

@[simp]
lemma trans_apply (e₁ : M ⊆ₑ N) (e₂ : N ⊆ₑ K) (x : M) : e₁.trans e₂ x = e₂ (e₁ x) := rfl

include e

/-- A structure with an end extension modelling `𝗣𝗔⁻` is itself a model of `𝗣𝗔⁻`.
- [vO99, Exercise 40] -/
theorem models_peanoMinus [N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_theory_iff.mpr <| by
  have inj : Function.Injective e.emb := e.emb_injective
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
      Arithmetic.add_eq_of_lt_bounded (e x) (e y) (by simpa using h)
    have h₁ : z ≤ e y := hzeq ▸ le_add_self
    obtain ⟨w, rfl⟩ : z ∈ Set.range e :=
      h₁.lt_or_eq.elim e.mem_range_of_lt fun h₂ ↦ ⟨y, h₂.symm⟩
    exact ⟨w, e.emb_lt_emb.mp (by simpa using hz), inj (by simpa using hzeq)⟩
  case zeroLe =>
    suffices ∀ x : M, 0 ≤ x by simpa [models_iff, le_iff_of_eq_of_lt, le_def] using this
    intro x
    rcases le_def.mp (Arithmetic.zero_le (e x)) with h | h
    · exact le_def.mpr <| Or.inl <| inj (by simpa using h)
    · exact le_def.mpr <| Or.inr <| e.emb_lt_emb.mp (by simpa using h)
  case zeroLtOne =>
    suffices (0 : M) < 1 by simpa [models_iff] using this
    exact e.emb_lt_emb.mp (by simp)
  case oneLeOfZeroLt =>
    suffices ∀ x : M, 0 < x → 1 ≤ x by
      simpa [models_iff, le_iff_of_eq_of_lt, le_def] using this
    intro x h
    have h₁ : (0 : N) < e x := by simpa using e.emb_lt_emb.mpr h
    rcases le_def.mp (one_le_of_zero_lt _ h₁) with h₂ | h₂
    · exact le_def.mpr <| Or.inl <| inj (by simpa using h₂)
    · exact le_def.mpr <| Or.inr <| e.emb_lt_emb.mp (by simpa using h₂)
  case addLtAdd =>
    suffices ∀ x y z : M, x < y → x + z < y + z by simpa [models_iff] using this
    intro x y z h
    exact e.emb_lt_emb.mp (by simpa using add_lt_add _ _ (e z) (e.emb_lt_emb.mpr h))
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
    have h₁ : (0 : N) < e z := by simpa using e.emb_lt_emb.mpr hz
    exact e.emb_lt_emb.mp (by simpa using mul_lt_mul _ _ (e z) (e.emb_lt_emb.mpr h) h₁)
  case distr =>
    suffices ∀ x y z : M, x * (y + z) = x * y + x * z by simpa [models_iff] using this
    intro x y z
    exact inj (by simp [mul_add])
  case ltIrrefl =>
    suffices ∀ x : M, ¬x < x by simpa [models_iff] using this
    intro x h
    exact lt_irrefl (e x) (by grind)
  case ltTrans =>
    suffices ∀ x y z : M, x < y → y < z → x < z by simpa [models_iff] using this
    intro x y z hxy hyz
    exact e.emb_lt_emb.mp
      (Arithmetic.lt_trans _ _ _ (e.emb_lt_emb.mpr hxy) (e.emb_lt_emb.mpr hyz))
  case ltTri =>
    suffices ∀ x y : M, x < y ∨ x = y ∨ y < x by simpa [models_iff] using this
    intro x y
    exact (lt_tri (e x) (e y)).imp e.emb_lt_emb.mp
      (Or.imp e.emb_eq_emb.mp e.emb_lt_emb.mp)

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
        (Bounding.sigma_one_upward e.emb (hT σ hσ).neg ![] Empty.elim
          (by simpa [models_iff] using h))
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
  exact models_of_subtheory (e.models_of_Pi1 hU)

/-- A structure with an end extension modelling `𝗜𝚺₀` is itself a model of `𝗜𝚺₀`.
- [HP98, Remark IV.1.21(2)] -/
theorem models_ISigma0 [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := e.models_peanoMinus
  have hind {φ : ArithmeticSemiformula ℕ 1} (hφ : ℬ[<, ℒₒᵣ].Closure φ) (v : ℕ → M)
      (h0 : φ.Eval ![0] v) (hs : ∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) (a : M) :
      φ.Eval ![a] v := by
    have h₁ : ∀ x : M, φ.Eval ![x] v ↔ φ.Eval ![e x] (e.emb ∘ v) := by
      intro x
      simpa [Matrix.comp_vecCons'', Matrix.empty_eq] using
        Bounding.bounded_absolute e.emb hφ ![x] v
    have h₂ : ∀ y : N, y < e a + 1 → φ.Eval ![y] (e.emb ∘ v) := by
      refine InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0)
        ⟨(e a + 1) :>ₙ fun j ↦ e (v j),
          “#0 < &0” 🡒 (Rew.rewriteMap Nat.succ ▹ φ), by simp [hφ.hierarchy],
          by intro x; simp [Semiformula.eval_rewriteMap, Function.comp_def]⟩
        (by intro _; simpa using (h₁ 0).mp h0) ?_
      intro y ih hy
      have h₃ : y < e a := lt_of_lt_of_le (lt_add_one y) (lt_succ_iff_le.mp hy)
      obtain ⟨x, rfl⟩ := e.mem_range_of_lt h₃
      simpa using (h₁ (x + 1)).mp (hs x ((h₁ x).mpr (ih (lt_trans h₃ (lt_add_one _)))))
    exact (h₁ a).mpr (h₂ (e a) (by simp))
  simp only [Semantics.ModelsSet.union_iff, InductionScheme]
  and_intros
  · exact this
  · apply Semantics.ModelsSet.setOf_iff.mpr
    rintro _ ⟨φ, hφ, rfl⟩
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs]
      using hind (Bounding.PrenexHierarchy.zero_iff_bounded.mp hφ)

end EndExtension

namespace ProperEndExtension

lemma exists_not_mem_range (e : M ⊂ₑ N) : ∃ c : N, c ∉ Set.range e.emb := by
  simpa [Function.Surjective, Set.range, not_forall] using e.not_surjective

/-- A proper end extension followed by an end extension is proper. -/
protected def transLeft (e₁ : M ⊂ₑ N) (e₂ : N ⊆ₑ K) : M ⊂ₑ K where
  toEndExtension := e₁.toEndExtension.trans e₂
  not_surjective h := e₁.not_surjective fun y ↦ by
    obtain ⟨x, hx⟩ := h (e₂ y)
    use x
    exact e₂.emb_injective hx

/-- An end extension followed by a proper end extension is proper. -/
protected def transRight (e₁ : M ⊆ₑ N) (e₂ : N ⊂ₑ K) : M ⊂ₑ K where
  toEndExtension := e₁.trans e₂.toEndExtension
  not_surjective h := e₂.not_surjective fun y ↦ by
    obtain ⟨x, hx⟩ := h y
    use e₁ x
    exact hx

/-- The composition of proper end extensions. -/
@[trans]
protected def trans (e₁ : M ⊂ₑ N) (e₂ : N ⊂ₑ K) : M ⊂ₑ K :=
  e₁.transLeft e₂.toEndExtension

end ProperEndExtension

/-- An end extension is a $\Delta_0$-elementary substructure.
- [Kay91, Theorem 2.7]
- [HP98, Fact IV.1.3(4)] -/
def EndExtension.toElementarySubstructureOn (e : M ⊆ₑ N) :
    M ≼ₑ[ℒₒᵣ; fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ] N where
  emb := e.emb
  isElementary hφ v f := (Bounding.bounded_absolute e.emb hφ v f).symm

/-- A proper end extension is a proper $\Delta_0$-elementary substructure. -/
def ProperEndExtension.toProperElementarySubstructureOn (e : M ⊂ₑ N) :
    M ≺ₑ[ℒₒᵣ; fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ] N where
  toElementarySubstructureOn := e.toEndExtension.toElementarySubstructureOn
  not_surjective := e.not_surjective

end FFL.FirstOrder.Arithmetic
