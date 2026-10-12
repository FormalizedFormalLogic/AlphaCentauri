module

public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import Foundation.FirstOrder.Arithmetic.Omega1.Nuon

/-!
# Block-coded sequences over $\mathsf{EA}$

Over a model of $\mathsf{EA}$, a number $S$ codes a sequence of length $i$ whose entries are the
blocks of width $\|a\|$ of $S$ below $2^{i \|a\|}$, read off by `Nuon.ext`. This file collects the
facts about appending an entry and about determining a code by its entries.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

attribute [local instance] ElementaryArithmetic.models_ISigma0_union_Omega1

lemma exists_exponential_mul_length (i a : V) : ∃ b, Exponential (i * ‖a‖) b :=
  ElementaryArithmetic.exponential_total _

namespace Nuon

section

variable {a i j : V}

axiom ext_add_mul_of_lt {S b x : V} (hb : Exponential (i * ‖a‖) b) (hS : S < b)
    (hx : x < a ⨳ 1) (hj : j < i) : Nuon.ext a (S + x * b) j = Nuon.ext a S j

axiom ext_add_mul_self {S b x : V} (hb : Exponential (i * ‖a‖) b) (hS : S < b)
    (hx : x < a ⨳ 1) : Nuon.ext a (S + x * b) i = x

axiom ext_ext {S S' b : V} (hb : Exponential (i * ‖a‖) b) (hS : S < b) (hS' : S' < b)
    (h : ∀ j < i, Nuon.ext a S j = Nuon.ext a S' j) : S = S'

end

end Nuon

end

end FFL.FirstOrder.Arithmetic
