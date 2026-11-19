module

public import Foundation.FirstOrder.Tarski.Elementary

/-! # Elementary substructures

For a class $\Gamma$ of formulas of a language `L`, a $\Gamma$-elementary substructure of an
`L`-structure `N` is a structure `M` together with an embedding into `N` along which every formula
of $\Gamma$ takes the same truth value at elements of `M` as at their images. An elementary
substructure is a $\Gamma$-elementary substructure for every formula; a proper one is not
surjective.
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

end FFL.FirstOrder
