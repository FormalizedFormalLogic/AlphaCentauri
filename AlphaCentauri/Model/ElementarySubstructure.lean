module

public import AlphaCentauri.Model.Absolute

/-! # Elementary substructures

For a class $\Gamma$ of formulas, a $\Gamma$-elementary substructure of an `ℒₒᵣ`-structure `N`
is a structure `M` together with an embedding into `N` along which every formula of $\Gamma$ takes
the same truth value at elements of `M` as at their images. An elementary substructure is a
$\Gamma$-elementary substructure for every formula; a proper one is not surjective. An end
extension is a $\Delta_0$-elementary substructure.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula

universe u v

variable {M : Type u} {N : Type v} [ORingStructure M]

section

variable [ORingStructure N]

/-- `M` is a $\Gamma$-elementary substructure of `N`: along the embedding, every formula of
$\Gamma$ takes the same truth value at elements of `M` as at their images.
- [Kay91, §2.2] -/
class ElementarySubstructureOn (Γ : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop)
    (M : outParam (Type u)) (N : Type v) [ORingStructure M] [ORingStructure N] where
  emb : M ↪ₛ[ℒₒᵣ] N
  eval_iff {n : ℕ} {φ : ArithmeticSemiformula ℕ n} : Γ φ → ∀ (e : Fin n → M) (f : ℕ → M),
    φ.Eval (emb ∘ e) (emb ∘ f) ↔ φ.Eval e f

/-- `M` is an elementary substructure of `N`.
- [Kay91, §0.1] -/
abbrev ElementarySubstructure (M : outParam (Type u)) (N : Type v) [ORingStructure M]
    [ORingStructure N] :=
  ElementarySubstructureOn (fun {_} _ ↦ True) M N

/-- `M` is a proper $\Gamma$-elementary substructure of `N`: not every element of `N` comes from
`M`. -/
class ProperElementarySubstructureOn (Γ : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop)
    (M : outParam (Type u)) (N : Type v) [ORingStructure M] [ORingStructure N]
    extends ElementarySubstructureOn Γ M N where
  not_surjective : ¬Function.Surjective emb

/-- `M` is a proper elementary substructure of `N`. -/
abbrev ProperElementarySubstructure (M : outParam (Type u)) (N : Type v) [ORingStructure M]
    [ORingStructure N] :=
  ProperElementarySubstructureOn (fun {_} _ ↦ True) M N

@[inherit_doc] notation:50 M " ≼ₑ[" Γ "] " N => ElementarySubstructureOn Γ M N

@[inherit_doc] notation:50 M " ≺ₑ[" Γ "] " N => ProperElementarySubstructureOn Γ M N

@[inherit_doc] infix:50 " ≼ₑ " => ElementarySubstructure

@[inherit_doc] infix:50 " ≺ₑ " => ProperElementarySubstructure

namespace ElementarySubstructureOn

variable {Γ : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop} [hMN : M ≼ₑ[Γ] N]

/-- A $\Gamma$-elementary substructure is $\Gamma'$-elementary for every $\Gamma'$ contained in
$\Gamma$. -/
@[instance_reducible] def mono {Γ' : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop}
    (h : ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ n}, Γ' φ → Γ φ) : M ≼ₑ[Γ'] N where
  emb := hMN.emb
  eval_iff hφ := hMN.eval_iff (h hφ)

end ElementarySubstructureOn

namespace ProperElementarySubstructureOn

/-- A proper $\Gamma$-elementary substructure is proper $\Gamma'$-elementary for every $\Gamma'$
contained in $\Gamma$. -/
@[instance_reducible] def mono {Γ Γ' : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop}
    [hMN : M ≺ₑ[Γ] N]
    (h : ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ n}, Γ' φ → Γ φ) : M ≺ₑ[Γ'] N where
  toElementarySubstructureOn := ElementarySubstructureOn.mono h
  not_surjective := hMN.not_surjective

end ProperElementarySubstructureOn

end

/-- An end extension is a $\Delta_0$-elementary substructure.
- [Kay91, Theorem 2.7]
- [HP98, Fact IV.1.3(4)] -/
instance EndExtension.elementarySubstructureOn [hMN : M ⊆ₑ N] :
    M ≼ₑ[fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ] N where
  emb := hMN.emb
  eval_iff hφ e f := (absolute_of_bounded (T := ∅) hφ M N e f).symm

/-- A proper end extension is a proper $\Delta_0$-elementary substructure. -/
instance ProperEndExtension.properElementarySubstructureOn [hMN : M ⊂ₑ N] :
    M ≺ₑ[fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ] N where
  toElementarySubstructureOn := EndExtension.elementarySubstructureOn
  not_surjective := hMN.not_surjective

end FFL.FirstOrder.Arithmetic
