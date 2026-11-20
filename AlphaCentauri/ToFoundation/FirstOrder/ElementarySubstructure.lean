module

public import Foundation.FirstOrder.LK.Soundness
public import Foundation.FirstOrder.Tarski.Elementary
public import Foundation.FirstOrder.Tarski.Eq

/-! # Elementary substructures

For a class $\Gamma$ of formulas of a language `L`, a $\Gamma$-elementary substructure of an
`L`-structure `N` is a structure `M` together with an embedding into `N` along which every formula
of $\Gamma$ takes the same truth value at elements of `M` as at their images. An elementary
substructure is a $\Gamma$-elementary substructure for every formula; a proper one is not
surjective. Models of a complete theory are elementarily equivalent.
-/

@[expose] public section

namespace FFL.FirstOrder

open Semiformula Tarski.Structure

universe u v w

variable {L : Language} {M : Type u} {N : Type v} {K : Type w}
  [Tarski.Structure L M] [Tarski.Structure L N] [Tarski.Structure L K]

/-- `ι` is $\Gamma$-elementary: every formula of $\Gamma$ takes the same truth value at elements of
`M` as at their images.
- [Kay91, §2.2]
- [HP98, Definition IV.1.17] -/
def IsElementary (Γ : ∀ {n : ℕ}, Semiformula L ℕ n → Prop) (ι : M ↪ₛ[L] N) : Prop :=
  ∀ {n : ℕ} {φ : Semiformula L ℕ n}, Γ φ → ∀ (e : Fin n → M) (f : ℕ → M),
    φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f

/-- The Tarski–Vaught test: an embedding is elementary as soon as every formula with parameters
from `M` and a witness in `N` has a witness in `M`.
- [Kay91, Theorem 0.5] -/
theorem IsElementary.of_tarskiVaught (ι : M ↪ₛ[L] N)
    (witness : ∀ {n : ℕ} (φ : Semiformula L ℕ (n + 1)) (e : Fin n → M) (f : ℕ → M),
      (∃ x : N, φ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : M, φ.Eval (ι x :> ι ∘ e) (ι ∘ f)) :
    IsElementary (fun {_} _ ↦ True) ι := by
  intro n φ _ e f
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => exact (eval_hom_iff_of_open ι (φ := rel r v) (by simp)).symm
  | hnrel r v => exact (eval_hom_iff_of_open ι (φ := nrel r v) (by simp)).symm
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih =>
    simp only [eval_all]
    constructor
    · intro h x
      exact (ih (x :> e)).mp <| by simpa [Matrix.comp_vecCons''] using h (ι x)
    · intro h
      by_contra hn
      push Not at hn
      obtain ⟨x, hx⟩ := witness (∼φ) e f <| by simpa using hn
      exact (by simpa using hx : ¬φ.Eval (ι x :> ι ∘ e) (ι ∘ f)) <| by
        simpa [Matrix.comp_vecCons''] using (ih (x :> e)).mpr (h x)
  | hexs φ ih =>
    simp only [eval_ex]
    constructor
    · intro h
      obtain ⟨x, hx⟩ := witness φ e f h
      use x
      exact (ih (x :> e)).mp <| by simpa [Matrix.comp_vecCons''] using hx
    · rintro ⟨x, hx⟩
      use ι x
      simpa [Matrix.comp_vecCons''] using (ih (x :> e)).mpr hx

/-- An elementary embedding preserves the truth of sentences. -/
lemma IsElementary.models_iff [Nonempty M] [Nonempty N] {ι : M ↪ₛ[L] N}
    (h : IsElementary (fun {_} _ ↦ True) ι) (σ : Sentence L) : N↓[L] ⊧ σ ↔ M↓[L] ⊧ σ := by
  rw [FFL.FirstOrder.models_iff, FFL.FirstOrder.models_iff]
  simpa [Matrix.empty_eq] using h (φ := Rewriting.emb σ) trivial ![] fun _ ↦ Classical.ofNonempty

/-- An elementary embedding into a model of `T` is from a model of `T`. -/
lemma IsElementary.modelsTheory [Nonempty M] [Nonempty N] {ι : M ↪ₛ[L] N}
    (h : IsElementary (fun {_} _ ↦ True) ι) {T : Theory L} [N↓[L] ⊧* T] : M↓[L] ⊧* T :=
  ⟨fun σ hσ ↦ (h.models_iff σ).mp <| Semantics.ModelsSet.models _ hσ⟩

/-- A $\Gamma$-elementary substructure: an embedding of `M` into `N` which is $\Gamma$-elementary.
- [Kay91, §2.2] -/
structure ElementarySubstructureOn (Γ : ∀ {n : ℕ}, Semiformula L ℕ n → Prop)
    (M : Type u) (N : Type v) [Tarski.Structure L M] [Tarski.Structure L N] where
  emb : M ↪ₛ[L] N
  isElementary : IsElementary Γ emb

variable (L) in
/-- An elementary substructure.
- [Kay91, §0.1] -/
abbrev ElementarySubstructure (M : Type u) (N : Type v) [Tarski.Structure L M]
    [Tarski.Structure L N] :=
  ElementarySubstructureOn (L := L) (fun {_} _ ↦ True) M N

/-- A proper $\Gamma$-elementary substructure: a $\Gamma$-elementary substructure which is not
surjective. -/
structure ProperElementarySubstructureOn (Γ : ∀ {n : ℕ}, Semiformula L ℕ n → Prop)
    (M : Type u) (N : Type v) [Tarski.Structure L M] [Tarski.Structure L N]
    extends ElementarySubstructureOn Γ M N where
  not_surjective : ¬Function.Surjective emb

variable (L) in
/-- A proper elementary substructure. -/
abbrev ProperElementarySubstructure (M : Type u) (N : Type v) [Tarski.Structure L M]
    [Tarski.Structure L N] :=
  ProperElementarySubstructureOn (L := L) (fun {_} _ ↦ True) M N

@[inherit_doc ElementarySubstructureOn]
notation:50 M " ≼ₑ[" L "; " Γ "] " N => @ElementarySubstructureOn L Γ M N _ _

@[inherit_doc ProperElementarySubstructureOn]
notation:50 M " ≺ₑ[" L "; " Γ "] " N => @ProperElementarySubstructureOn L Γ M N _ _

@[inherit_doc] notation:50 M " ≼ₑ[" L "] " N => ElementarySubstructure L M N

@[inherit_doc] notation:50 M " ≺ₑ[" L "] " N => ProperElementarySubstructure L M N

variable {Γ Γ' : ∀ {n : ℕ}, Semiformula L ℕ n → Prop}

instance : CoeFun (M ≼ₑ[L; Γ] N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

instance : CoeFun (M ≺ₑ[L; Γ] N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

namespace ElementarySubstructureOn

variable (M Γ) in
/-- The identity $\Gamma$-elementary substructure. -/
@[refl] protected def refl : M ≼ₑ[L; Γ] M where
  emb := {
    toFun := id
    func' _ _ := rfl
    rel' _ _ h := h
    toFun_inj := Function.injective_id
    rel_inv' _ _ h := h
  }
  isElementary _ _ _ := Iff.rfl

@[simp] lemma refl_apply (x : M) : ElementarySubstructureOn.refl M Γ x = x := rfl

/-- The composition of $\Gamma$-elementary substructures. -/
@[trans] protected def trans (e₁ : M ≼ₑ[L; Γ] N) (e₂ : N ≼ₑ[L; Γ] K) : M ≼ₑ[L; Γ] K where
  emb := {
    toFun := e₂ ∘ e₁
    func' f v := by simp [HomClass.func e₁.emb, HomClass.func e₂.emb, Function.comp_def]
    rel' r v h := HomClass.rel e₂.emb r _ (HomClass.rel e₁.emb r v h)
    toFun_inj := (EmbeddingClass.map_inj e₂.emb).comp (EmbeddingClass.map_inj e₁.emb)
    rel_inv' r v h :=
      EmbeddingClass.map_rel_inv e₁.emb r v (EmbeddingClass.map_rel_inv e₂.emb r _ h)
  }
  isElementary hφ e f := (e₂.isElementary hφ (e₁ ∘ e) (e₁ ∘ f)).trans (e₁.isElementary hφ e f)

@[simp] lemma trans_apply (e₁ : M ≼ₑ[L; Γ] N) (e₂ : N ≼ₑ[L; Γ] K) (x : M) :
    e₁.trans e₂ x = e₂ (e₁ x) := rfl

/-- A $\Gamma$-elementary substructure is $\Gamma'$-elementary for every $\Gamma'$ contained in
$\Gamma$. -/
def mono (e : M ≼ₑ[L; Γ] N) (h : ∀ {n : ℕ} {φ : Semiformula L ℕ n}, Γ' φ → Γ φ) :
    M ≼ₑ[L; Γ'] N where
  emb := e.emb
  isElementary hφ := e.isElementary (h hφ)

end ElementarySubstructureOn

/-- A proper $\Gamma$-elementary substructure is proper $\Gamma'$-elementary for every $\Gamma'$
contained in $\Gamma$. -/
def ProperElementarySubstructureOn.mono (e : M ≺ₑ[L; Γ] N)
    (h : ∀ {n : ℕ} {φ : Semiformula L ℕ n}, Γ' φ → Γ φ) : M ≺ₑ[L; Γ'] N where
  toElementarySubstructureOn := e.toElementarySubstructureOn.mono h
  not_surjective := e.not_surjective

lemma Tarski.Structure.ElementaryEquiv.of_complete (T : Theory L) [Entailment.Complete T]
    (M : Type u) (N : Type v) [Nonempty M] [Nonempty N] [Tarski.Structure L M]
    [Tarski.Structure L N] [M↓[L] ⊧* T] [N↓[L] ⊧* T] : M ≡ₑ[L] N := by
  constructor
  intro σ
  rcases Entailment.Complete.con (𝓢 := T) σ with h | h
  · exact iff_of_true (models_of_provable inferInstance h) (models_of_provable inferInstance h)
  · have hM := models_of_provable (M := M) inferInstance h
    have hN := models_of_provable (M := N) inferInstance h
    simp only [models_iff, LogicalConnective.HomClass.map_neg] at hM hN ⊢
    exact iff_of_false hM hN

lemma Tarski.Structure.ElementaryEquiv.existsUnique_iff [Nonempty M] [Nonempty N] [L.Eq]
    [Tarski.Structure.Eq L M] [Tarski.Structure.Eq L N] [M ≡ₑ[L] N] (θ : Semisentence L 1) :
    (∃! x : M, M ⊧/![x] θ) ↔ ∃! y : N, N ⊧/![y] θ := by
  simpa [existsUnique, models_iff, ExistsUnique, Matrix.constant_eq_singleton] using
    ElementaryEquiv.models (L := L) (M₁ := M) (M₂ := N) (φ := ∃¹! θ)

end FFL.FirstOrder
