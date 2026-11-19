module

public import AlphaCentauri.Model.EndExtension

/-! # Elementary substructures

For a class $\Gamma$ of formulas, a $\Gamma$-elementary substructure of an `ℒₒᵣ`-structure `N`
is a structure `M` together with an embedding into `N` along which every formula of $\Gamma$ takes
the same truth value at elements of `M` as at their images. An elementary substructure is a
$\Gamma$-elementary substructure for every formula; a proper one is not surjective. An end
extension is a $\Delta_0$-elementary substructure.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula Tarski.Structure

universe u v w

variable {M : Type u} {N : Type v} [ORingStructure M] [ORingStructure N]

/-- `ι` is $\Gamma$-elementary: every formula of $\Gamma$ takes the same truth value at elements of
`M` as at their images.
- [Kay91, §2.2]
- [HP98, Definition IV.1.17] -/
def IsElementary (Γ : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop) (ι : M ↪ₛ[ℒₒᵣ] N) : Prop :=
  ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ n}, Γ φ → ∀ (e : Fin n → M) (f : ℕ → M),
    φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f

/-- A $\Gamma$-elementary substructure: an embedding of `M` into `N` which is $\Gamma$-elementary.
- [Kay91, §2.2] -/
structure ElementarySubstructureOn (Γ : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop)
    (M : Type u) (N : Type v) [ORingStructure M] [ORingStructure N] where
  emb : M ↪ₛ[ℒₒᵣ] N
  isElementary : IsElementary Γ emb

/-- An elementary substructure.
- [Kay91, §0.1] -/
abbrev ElementarySubstructure (M : Type u) (N : Type v) [ORingStructure M] [ORingStructure N] :=
  ElementarySubstructureOn (fun {_} _ ↦ True) M N

/-- A proper $\Gamma$-elementary substructure: a $\Gamma$-elementary substructure which is not
surjective. -/
structure ProperElementarySubstructureOn (Γ : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop)
    (M : Type u) (N : Type v) [ORingStructure M] [ORingStructure N]
    extends ElementarySubstructureOn Γ M N where
  not_surjective : ¬Function.Surjective emb

/-- A proper elementary substructure. -/
abbrev ProperElementarySubstructure (M : Type u) (N : Type v) [ORingStructure M]
    [ORingStructure N] :=
  ProperElementarySubstructureOn (fun {_} _ ↦ True) M N

@[inherit_doc] notation:50 M " ≼ₑ[" Γ "] " N => ElementarySubstructureOn Γ M N

@[inherit_doc] notation:50 M " ≺ₑ[" Γ "] " N => ProperElementarySubstructureOn Γ M N

@[inherit_doc] infix:50 " ≼ₑ " => ElementarySubstructure

@[inherit_doc] infix:50 " ≺ₑ " => ProperElementarySubstructure

variable {Γ Γ' : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop}

instance : CoeFun (M ≼ₑ[Γ] N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

instance : CoeFun (M ≺ₑ[Γ] N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

namespace ElementarySubstructureOn

variable {K : Type w} [ORingStructure K]

variable (M Γ) in
/-- The identity $\Gamma$-elementary substructure. -/
@[refl] protected def refl : M ≼ₑ[Γ] M where
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
@[trans] protected def trans (e₁ : M ≼ₑ[Γ] N) (e₂ : N ≼ₑ[Γ] K) : M ≼ₑ[Γ] K where
  emb := {
    toFun := e₂ ∘ e₁
    func' f v := by simp [HomClass.func e₁.emb, HomClass.func e₂.emb, Function.comp_def]
    rel' r v h := HomClass.rel e₂.emb r _ (HomClass.rel e₁.emb r v h)
    toFun_inj := (EmbeddingClass.map_inj e₂.emb).comp (EmbeddingClass.map_inj e₁.emb)
    rel_inv' r v h :=
      EmbeddingClass.map_rel_inv e₁.emb r v (EmbeddingClass.map_rel_inv e₂.emb r _ h)
  }
  isElementary hφ e f := (e₂.isElementary hφ (e₁ ∘ e) (e₁ ∘ f)).trans (e₁.isElementary hφ e f)

@[simp] lemma trans_apply (e₁ : M ≼ₑ[Γ] N) (e₂ : N ≼ₑ[Γ] K) (x : M) :
    e₁.trans e₂ x = e₂ (e₁ x) := rfl

end ElementarySubstructureOn

/-- A $\Gamma$-elementary substructure is $\Gamma'$-elementary for every $\Gamma'$ contained in
$\Gamma$. -/
def ElementarySubstructureOn.mono (e : M ≼ₑ[Γ] N)
    (h : ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ n}, Γ' φ → Γ φ) : M ≼ₑ[Γ'] N where
  emb := e.emb
  isElementary hφ := e.isElementary (h hφ)

/-- A proper $\Gamma$-elementary substructure is proper $\Gamma'$-elementary for every $\Gamma'$
contained in $\Gamma$. -/
def ProperElementarySubstructureOn.mono (e : M ≺ₑ[Γ] N)
    (h : ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ n}, Γ' φ → Γ φ) : M ≺ₑ[Γ'] N where
  toElementarySubstructureOn := e.toElementarySubstructureOn.mono h
  not_surjective := e.not_surjective

/-- An end extension is a $\Delta_0$-elementary substructure.
- [Kay91, Theorem 2.7]
- [HP98, Fact IV.1.3(4)] -/
def EndExtension.toElementarySubstructureOn (e : M ⊆ₑ N) :
    M ≼ₑ[fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ] N where
  emb := e.emb
  isElementary hφ v f := (Bounding.bounded_absolute e.emb hφ v f).symm

/-- A proper end extension is a proper $\Delta_0$-elementary substructure. -/
def ProperEndExtension.toProperElementarySubstructureOn (e : M ⊂ₑ N) :
    M ≺ₑ[fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ] N where
  toElementarySubstructureOn := e.toEndExtension.toElementarySubstructureOn
  not_surjective := e.not_surjective

end FFL.FirstOrder.Arithmetic
