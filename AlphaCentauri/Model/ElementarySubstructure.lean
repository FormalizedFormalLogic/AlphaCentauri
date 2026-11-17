module

public import AlphaCentauri.Model.Absolute

/-! # Elementary substructures

For a class `C` of formulas, a $C$-elementary substructure of an `ℒₒᵣ`-structure `N` is a structure
`M` together with an embedding into `N` along which every formula of `C` takes the same truth value
at elements of `M` as at their images. An elementary substructure is a `C`-elementary substructure
for every formula; a proper one is not surjective. An end extension is a $\Delta_0$-elementary
substructure.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula

universe u v

variable {M : Type u} {N : Type v} [ORingStructure M]

section

variable [ORingStructure N]

/-- `ι` is `C`-elementary: every formula of `C` takes the same truth value at elements of `M` as at
their images.
- [HP98, Definition IV.1.17] -/
def IsElementary (C : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop)
    (ι : M ↪ₛ[ℒₒᵣ] N) : Prop :=
  ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ n}, C φ → ∀ (e : Fin n → M) (f : ℕ → M),
    φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f

/-- `M` is a `C`-elementary substructure of `N`. -/
class ElementarySubstructureOn (C : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop)
    (M : outParam (Type u)) (N : Type v) [ORingStructure M] [ORingStructure N] where
  emb : M ↪ₛ[ℒₒᵣ] N
  isElementary : IsElementary C emb

/-- `M` is an elementary substructure of `N`. -/
abbrev ElementarySubstructure (M : outParam (Type u)) (N : Type v) [ORingStructure M]
    [ORingStructure N] :=
  ElementarySubstructureOn (fun {_} _ ↦ True) M N

/-- `M` is a proper `C`-elementary substructure of `N`: not every element of `N` comes from
`M`. -/
class ProperElementarySubstructureOn (C : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop)
    (M : outParam (Type u)) (N : Type v) [ORingStructure M] [ORingStructure N]
    extends ElementarySubstructureOn C M N where
  not_surjective : ¬Function.Surjective emb

/-- `M` is a proper elementary substructure of `N`. -/
abbrev ProperElementarySubstructure (M : outParam (Type u)) (N : Type v) [ORingStructure M]
    [ORingStructure N] :=
  ProperElementarySubstructureOn (fun {_} _ ↦ True) M N

@[inherit_doc] notation:50 M " ≼ₑ[" C "] " N => ElementarySubstructureOn C M N

@[inherit_doc] notation:50 M " ≺ₑ[" C "] " N => ProperElementarySubstructureOn C M N

@[inherit_doc] infix:50 " ≼ₑ " => ElementarySubstructure

@[inherit_doc] infix:50 " ≺ₑ " => ProperElementarySubstructure

namespace ElementarySubstructureOn

variable {C : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop} [hMN : M ≼ₑ[C] N]

lemma eval_iff {n : ℕ} {φ : ArithmeticSemiformula ℕ n} (hφ : C φ) (e : Fin n → M) (f : ℕ → M) :
    φ.Eval (hMN.emb ∘ e) (hMN.emb ∘ f) ↔ φ.Eval e f :=
  hMN.isElementary hφ e f

/-- A `C`-elementary substructure is `C'`-elementary for every `C'` contained in `C`. -/
@[instance_reducible] def mono {C' : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop}
    (h : ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ n}, C' φ → C φ) : M ≼ₑ[C'] N where
  emb := hMN.emb
  isElementary hφ := hMN.isElementary (h hφ)

end ElementarySubstructureOn

namespace ProperElementarySubstructureOn

/-- A proper `C`-elementary substructure is proper `C'`-elementary for every `C'` contained in
`C`. -/
@[instance_reducible] def mono {C C' : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop}
    [hMN : M ≺ₑ[C] N]
    (h : ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ n}, C' φ → C φ) : M ≺ₑ[C'] N where
  toElementarySubstructureOn := ElementarySubstructureOn.mono h
  not_surjective := hMN.not_surjective

end ProperElementarySubstructureOn

end

/-- An end extension is a $\Delta_0$-elementary substructure.
- [HP98, Fact IV.1.3(4)] -/
instance EndExtension.elementarySubstructureOn [hMN : M ⊆ₑ N] :
    M ≼ₑ[fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ] N where
  emb := hMN.emb
  isElementary hφ e f := (absolute_of_bounded (T := ∅) hφ M N e f).symm

/-- A proper end extension is a proper $\Delta_0$-elementary substructure. -/
instance ProperEndExtension.properElementarySubstructureOn [hMN : M ⊂ₑ N] :
    M ≺ₑ[fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ] N where
  toElementarySubstructureOn := EndExtension.elementarySubstructureOn
  not_surjective := hMN.not_surjective

end FFL.FirstOrder.Arithmetic
