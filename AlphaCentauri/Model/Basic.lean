module

public import AlphaCentauri.Axiomatizability.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Embedding
public import AlphaCentauri.ToFoundation.FirstOrder.Bounded
public import AlphaCentauri.ToFoundation.FirstOrder.ElementarySubstructure
public import AlphaCentauri.ToFoundation.FirstOrder.Hierarchy
public import Foundation.FirstOrder.Arithmetic.Collection.Basic
public import Foundation.FirstOrder.Arithmetic.Definability.PrenexDefinable
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.Arithmetic.Schema.DeltaInduction
public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Absoluteness

/-! # End extensions, cuts and elementary embeddings

An end extension of an `ℒₒᵣ`-structure `M` is a structure into which `M` embeds with nothing new
below the image of `M`. Bounded formulas take the same truth value in `M` and in an end extension
of it, and $\Sigma_1$ formulas satisfied in `M` stay satisfied in an end extension of it. `𝗣𝗔⁻`,
`𝗜𝚺₀` and any theory axiomatized by $\Pi_1$ sentences hold in `M` as soon as they hold in an end
extension of `M`. An end extension is a $\Delta_0$-elementary substructure. In a proper end
extension satisfying induction for a hierarchy class, a formula of that class which holds at every
element of the base model holds below some element outside the base model.

A cut of `M` is a subset closed under successor and downward closed under `<`. A closed cut, one
closed under the operations of the language, is a substructure of `M`, and `M` is an end extension
of it. No proper cut is definable by a $\Sigma_0$ formula with parameters in a model of `𝗜𝚺₀`, and
no model of `𝗜𝚫 n` has a proper cut whose membership relation and complement are both definable by
prenex $\Sigma_n$ formulas with parameters.

An embedding of `ℒₒᵣ`-structures is $\Sigma_s$-elementary when it is elementary for the prenex
$\Sigma_m$ and $\Pi_m$ formulas with `m ≤ s`. The Tarski–Vaught test reduces this to the
absoluteness of bounded formulas and to finding witnesses in the substructure.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

universe u v w

open Semiformula Tarski.Structure

/-! ## End extensions -/

section

variable {M : Type u} {N : Type v} {K : Type w} [ORingStructure M] [ORingStructure N]
  [ORingStructure K]

/-- An end extension of `M` to `N`: an embedding of `M` into `N` with nothing new below its image.
- [HP98, Definition IV.1.3(2)]
- [vO99, §3.1] -/
structure EndExtension (M : Type u) (N : Type v) [ORingStructure M] [ORingStructure N] where
  emb : M ↪ₛ[ℒₒᵣ] N
  mem_range_of_lt {a : M} {b : N} : b < emb a → b ∈ Set.range emb

@[inherit_doc] infix:50 " ⊆ₑ " => EndExtension

/-- A proper end extension: an end extension which is not surjective.
- [HP98, Definition IV.1.14]
- [vO99, §3.2] -/
structure ProperEndExtension (M : Type u) (N : Type v) [ORingStructure M] [ORingStructure N]
    extends EndExtension M N where
  not_surjective : ¬Function.Surjective emb

@[inherit_doc] infix:50 " ⊂ₑ " => ProperEndExtension

instance : CoeFun (M ⊆ₑ N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

instance : CoeFun (M ⊂ₑ N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

namespace EndExtension

variable (e : M ⊆ₑ N)

lemma emb_injective : Function.Injective e.emb := EmbeddingClass.map_inj e.emb

@[simp, grind =] lemma emb_lt_emb {x y : M} : e x < e y ↔ x < y :=
  EmbeddingClass.map_lt_map_iff e.emb

@[grind =] lemma emb_eq_emb {x y : M} : e x = e y ↔ x = y := e.emb_injective.eq_iff

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
@[refl] protected def refl : M ⊆ₑ M where
  emb := {
    toFun := id
    func' _ _ := rfl
    rel' _ _ h := h
    toFun_inj := Function.injective_id
    rel_inv' _ _ h := h
  }
  mem_range_of_lt {_ b} _ := ⟨b, rfl⟩

@[simp] lemma refl_apply (x : M) : EndExtension.refl M x = x := rfl

/-- The composition of end extensions. -/
@[trans] protected def trans (e₁ : M ⊆ₑ N) (e₂ : N ⊆ₑ K) : M ⊆ₑ K where
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

@[simp] lemma trans_apply (e₁ : M ⊆ₑ N) (e₂ : N ⊆ₑ K) (x : M) : e₁.trans e₂ x = e₂ (e₁ x) := rfl

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

/-- A proper end extension followed by an end extension is proper. -/
protected def transLeft (e₁ : M ⊂ₑ N) (e₂ : N ⊆ₑ K) : M ⊂ₑ K where
  toEndExtension := e₁.toEndExtension.trans e₂
  not_surjective h := e₁.not_surjective fun y ↦ by
    obtain ⟨x, hx⟩ := h (e₂ y)
    use x
    exact e₂.emb_injective hx

/-- The composition of proper end extensions. -/
@[trans] protected def trans (e₁ : M ⊂ₑ N) (e₂ : N ⊂ₑ K) : M ⊂ₑ K :=
  e₁.transLeft e₂.toEndExtension

end ProperEndExtension

/-- An end extension is a $\Delta_0$-elementary substructure.
- [Kay91, Theorem 2.7]
- [HP98, Fact IV.1.3(4)] -/
def EndExtension.toElementarySubstructureOn (e : M ⊆ₑ N) :
    M ≼ₑ[ℒₒᵣ; fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ] N where
  emb := e.emb
  isElementary hφ v f := (Bounding.bounded_absolute e.emb hφ v f).symm

end

/-! ## Overspill -/

section

variable {M : Type u} {N : Type v} [ORingStructure M] [ORingStructure N] (e : M ⊂ₑ N)

/-- Overspill: a formula of the induction class holding at every element of the base model holds
below some element outside it.
- [HP98, Corollary IV.1.16]
- [vO99, Lemma 3.2, Corollary 3.3] -/
theorem overspill (Γ : Polarity) (m : ℕ) [N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ m]
    {φ : ArithmeticSemiformula ℕ 1} (hφ : ℬ[<, ℒₒᵣ].Hierarchy Γ m φ) (f : ℕ → N)
    (h : ∀ a : M, φ.Eval ![e a] f) :
    ∃ c : N, c ∉ Set.range e.emb ∧ ∀ x < c, φ.Eval ![x] f := by
  have : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ m)
  by_contra! hc
  have h₁ : ∀ x : N, (∀ y < x, φ.Eval ![y] f) → x ∈ Set.range e.emb := by grind;
  have h₂ : ∀ x : N, (∀ y < x, φ.Eval ![y] f) → ∀ y < x + 1, φ.Eval ![y] f := by
    intro x ih y hy;
    obtain ⟨a, rfl⟩ := h₁ x ih;
    rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hy) with hy' | rfl
    · exact ih y hy'
    · exact h a
  have h₃ : ∀ x : N, ∀ y < x, φ.Eval ![y] f :=
    InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].Hierarchy Γ m)
      ⟨f, (φ/[#0]).ballLT #0, by simp [hφ], fun x ↦ by simp [eval_ballLT]⟩
      (by simp) h₂
  exact e.not_surjective fun x ↦ h₁ x (h₃ x)

end

/-! ## Cuts -/

section

variable {M : Type u} [ORingStructure M]

/-- A cut of `M`: a subset closed under successor and downward closed under `<`.
- [HP98, Definition IV.1.14] -/
structure Cut (M : Type u) [ORingStructure M] where
  carrier : Set M
  succ_mem {a : M} : a ∈ carrier → a + 1 ∈ carrier
  mem_of_lt {a b : M} : a < b → b ∈ carrier → a ∈ carrier

/-- A cut closed under the operations of `ℒₒᵣ`, hence a substructure of `M`.
- [HP98, Definition IV.2.8(2)] -/
structure ClosedCut (M : Type u) [ORingStructure M] extends Cut M where
  zero_mem : (0 : M) ∈ carrier
  one_mem : (1 : M) ∈ carrier
  add_mem {a b : M} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  mul_mem {a b : M} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier

namespace ClosedCut

variable (I : ClosedCut M)

instance oringStructure : ORingStructure I.carrier where
  zero := ⟨0, I.zero_mem⟩
  one := ⟨1, I.one_mem⟩
  add a b := ⟨a.1 + b.1, I.add_mem a.2 b.2⟩
  mul a b := ⟨a.1 * b.1, I.mul_mem a.2 b.2⟩
  lt a b := a.1 < b.1

/-- `M` is an end extension of each of its closed cuts.
- [HP98, Definition IV.1.3(2)] -/
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
lemma endExtension_apply (x : I.carrier) : I.endExtension x = x.val := rfl

end ClosedCut

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

end

/-! ## $\Sigma_s$-elementary embeddings -/

section

variable {S M : Type} [ORingStructure S] [ORingStructure M]

variable (ι : S ↪ₛ[ℒₒᵣ] M)

lemma eval_ex_iff_of_witness {n : ℕ} {χ : ArithmeticSemiformula ℕ (n + 1)} {e : Fin n → S}
    {f : ℕ → S}
    (witness : (∃ x : M, χ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : S, χ.Eval (ι x :> ι ∘ e) (ι ∘ f))
    (h : ∀ x : S, χ.Eval (ι ∘ (x :> e)) (ι ∘ f) ↔ χ.Eval (x :> e) f) :
    (∃¹ χ).Eval (ι ∘ e) (ι ∘ f) ↔ (∃¹ χ).Eval e f := by
  simp only [eval_ex, Matrix.comp_vecCons''] at h ⊢
  constructor
  · intro h₁
    obtain ⟨x, hx⟩ := witness h₁
    use x
    exact (h x).mp hx
  · rintro ⟨x, hx⟩
    use ι x
    exact (h x).mpr hx

/-- The Tarski–Vaught test: bounded formulas are absolute along `ι`, and every prenex $\Pi_m$
formula, `m < s`, with parameters from `S` and a witness in `M` has a witness in `S`.
- [HP98, Lemma IV.1.19] -/
theorem isElementary_of_tarskiVaught (s : ℕ)
    (bounded : IsElementary (fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ) ι)
    (witness : ∀ m < s, ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ (n + 1)},
      ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 m φ → ∀ (e : Fin n → S) (f : ℕ → S),
        (∃ x : M, φ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : S, φ.Eval (ι x :> ι ∘ e) (ι ∘ f)) :
    IsElementary (ℬ[<, ℒₒᵣ].PrenexHierarchyLE s) ι := by
  suffices ∀ {Γ : Polarity} {m n : ℕ} {φ : ArithmeticSemiformula ℕ n}, m ≤ s →
      ℬ[<, ℒₒᵣ].PrenexHierarchy Γ m φ → ∀ (e : Fin n → S) (f : ℕ → S),
        φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f by
    rintro n φ ⟨m, hm, Γ, hφ⟩
    exact this hm hφ
  intro Γ m n φ hm hφ
  induction m generalizing Γ n φ with
  | zero => exact bounded (Bounding.PrenexHierarchy.zero_iff_bounded.mp hφ)
  | succ m ih =>
    intro e f
    rcases Γ
    · obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hφ
      exact eval_ex_iff_of_witness ι (witness m (by omega) hψ e f)
        fun x ↦ ih (by omega) hψ (x :> e) f
    · obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.pi_succ_iff.mp hφ
      simpa using (eval_ex_iff_of_witness ι (witness m (by omega) hψ.neg e f)
        fun x ↦ ih (by omega) hψ.neg (x :> e) f).not

/-- Bounded formulas are absolute along `ι` as soon as every bounded formula with parameters from
`S` and a witness in `M` has a witness in `S`. -/
lemma eval_iff_of_bounded_of_witness
    (witness : ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ (n + 1)}, ℬ[<, ℒₒᵣ].Closure φ →
      ∀ (e : Fin n → S) (f : ℕ → S),
        (∃ x : M, φ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : S, φ.Eval (ι x :> ι ∘ e) (ι ∘ f))
    {n : ℕ} {φ : ArithmeticSemiformula ℕ n} (hφ : ℬ[<, ℒₒᵣ].Closure φ)
    (e : Fin n → S) (f : ℕ → S) : φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f :=
  bounded_induction_open
    (P := fun n φ ↦ ∀ (e : Fin n → S) (f : ℕ → S), φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f)
    (fun _ _ hφ _ _ ↦ (eval_hom_iff_of_open ι hφ).symm)
    (fun _ _ _ _ _ ihφ ihψ e f ↦ by simp [ihφ e f, ihψ e f])
    (fun _ _ _ _ _ ihφ ihψ e f ↦ by simp [ihφ e f, ihψ e f])
    (fun _ t θ hθ ih e f ↦ by
      have hχ : ℬ[<, ℒₒᵣ].Closure (“#0 < !!(Rew.bShift t)” ⋏ ∼θ) :=
        .and (.of_open (by simp)) hθ.neg
      simpa [ball] using (eval_ex_iff_of_witness ι (witness hχ e f) fun x ↦ by
        simp [ih (x :> e) f, ← eval_hom_iff_of_open ι (φ := “#0 < !!(Rew.bShift t)”)]).not)
    (fun _ t θ hθ ih e f ↦ by
      have hχ : ℬ[<, ℒₒᵣ].Closure (“#0 < !!(Rew.bShift t)” ⋏ θ) := .and (.of_open (by simp)) hθ
      exact eval_ex_iff_of_witness ι (witness hχ e f) fun x ↦ by
        simp [ih (x :> e) f, ← eval_hom_iff_of_open ι (φ := “#0 < !!(Rew.bShift t)”)])
    n φ hφ e f

/-- A $\Delta_0$-elementary substructure of a model of `𝗣𝗔⁻` is a model of `𝗣𝗔⁻`.
- [HP98, Remark IV.1.21(2)] -/
theorem _root_.FFL.FirstOrder.IsElementary.models_peanoMinus {ι : S ↪ₛ[ℒₒᵣ] M}
    (hι : IsElementary (fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ) ι)
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] : S↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
  have h {Γ : Polarity} {n : ℕ} {φ : ArithmeticSemiformula ℕ n}
      (hφ : ℬ[<, ℒₒᵣ].PrenexBlock Γ φ) (hΓ : Γ = 𝚷) (e : Fin n → S) (f : ℕ → S) :
      φ.Eval (ι ∘ e) (ι ∘ f) → φ.Eval e f := by
    induction hφ with
    | bounded h =>
      exact (hι h e f).mp
    | exs => simp at hΓ
    | all _ ih =>
      simp only [eval_all]
      intro h₁ x
      exact ih rfl (x :> e) (by simpa [Matrix.comp_vecCons''] using h₁ (ι x))
  apply models_theory_iff.mpr
  intro σ hσ
  have h₁ := models_theory_iff.mp (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻) σ hσ
  simpa [models_iff] using h ((PeanoMinus.prenexBlock σ hσ).rew Rew.emb) rfl ![] (fun _ ↦ 0)
    (by simpa [models_iff] using h₁)

/-- A $\Sigma_s$-elementary embedding preserves the truth of $\Sigma_s$ and $\Pi_s$ sentences
between models of $\mathsf{B}\Sigma_s$. -/
lemma _root_.FFL.FirstOrder.IsElementary.models_iff_of_hierarchy {ι : S ↪ₛ[ℒₒᵣ] M} {s : ℕ}
    (hι : IsElementary (ℬ[<, ℒₒᵣ].PrenexHierarchyLE s) ι)
    [S↓[ℒₒᵣ] ⊧* 𝗕𝚺s] [M↓[ℒₒᵣ] ⊧* 𝗕𝚺s] {Γ : Polarity} {n : ℕ} {φ : ArithmeticSemisentence n}
    (hφ : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ) (v : Fin n → S) : M ⊧/(ι ∘ v) φ ↔ S ⊧/v φ := by
  obtain ⟨φ', hφ'⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) hφ
  rw [hφ' M, hφ' S]
  have := hι ⟨s, le_rfl, Γ, (φ'.rew Rew.emb).val_prenexHierarchy⟩ v (fun _ ↦ 0)
  rwa [Bounding.Prenex.val_rew, eval_emb, eval_emb] at this

end

end FFL.FirstOrder.Arithmetic
