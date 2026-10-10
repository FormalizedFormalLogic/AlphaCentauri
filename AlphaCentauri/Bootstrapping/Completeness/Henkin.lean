module

public import AlphaCentauri.Bootstrapping.Proof.Substitution
public import Foundation.FirstOrder.Incompleteness.Consistency

/-!
# Henkin completion inside $\mathsf{PA}$

Henkin's construction carried out in a model `V` of $\mathsf{PA}$. The free variables `^&u` of
internal formulas play the role of the Henkin constants.

## References

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.25]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (L : Language) [L.Encodable] [L.LORDefinable]

open Classical in
/-- The formula with code `n`, and `⊤` if `n` is not the code of a formula. -/
noncomputable def formulaOfCode (n : V) : V := if IsFormula L n then n else ^⊤

open Classical in
/-- The Henkin formula `∃x α → α(^&u)` of the code `n = ⌜∃x α⌝`, and `⊤` if `n` is not the code
of an existential formula. -/
noncomputable def henkinFormula (n u : V) : V :=
  if IsFormula L n ∧ ∃ p < n, n = ^∃ p then imp L n (substs1 L ^&u (π₂ (n - 1))) else ^⊤

variable {L} (S : Theory L) [S.Δ₁]

open Classical in
/-- The context after the `n`-th decision, given the context `s` before it: the Henkin formula of
`n` is witnessed by the free variable `^&(n + s)`, which is fresh for `s`, and `n`-th formula is
decided in favour of whichever of it and its negation `s` and the Henkin formula do not refute. -/
noncomputable def henkinStep (n s : V) : V :=
  insert (neg L (henkinFormula L n (n + s)))
    (insert (if Derivable S (insert (neg L (henkinFormula L n (n + s)))
        (insert (formulaOfCode L n) s)) then neg L (formulaOfCode L n) else formulaOfCode L n) s)

/-- `c n` is the sequent of the negated decisions and Henkin formulas below `n`. -/
def IsHenkinContext (c : V → V) : Prop := c 0 = ∅ ∧ ∀ n, c (n + 1) = henkinStep S n (c n)

/-- The formulas decided positively along the context `c`. -/
def HenkinMem (c : V → V) (x : V) : Prop :=
  IsFormula L x ∧ Derivable S (insert (neg L (henkinFormula L x (x + c x))) (insert x (c x)))

section axioms

variable {c : V → V}

axiom henkinMem_of_provable (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) {φ : V}
    (hφ : IsFormula L φ) (h : Provable S φ) : HenkinMem S c φ

axiom not_derivable_of_isHenkinContext (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) (n : V) :
    ¬Derivable S (c n)

axiom henkinMem_neg_iff (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) {φ : V}
    (hφ : IsFormula L φ) : HenkinMem S c (neg L φ) ↔ ¬HenkinMem S c φ

axiom henkinMem_of_derivable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) {s ψ : V}
    (hψ : IsFormula L ψ) (hs : ∀ p ∈ s, HenkinMem S c (neg L p)) (h : Derivable S (insert ψ s)) :
    HenkinMem S c ψ

axiom henkinMem_modus_ponens (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) {α β : V}
    (hα : HenkinMem S c α) (hαβ : HenkinMem S c (imp L α β)) : HenkinMem S c β

axiom exists_henkinMem_substs1 (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) {α : V}
    (hα : IsSemiformula L 1 α) (h : HenkinMem S c (^∃ α)) : ∃ u, HenkinMem S c (substs1 L ^&u α)

axiom henkinMem_henkinFormula (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (hc : IsHenkinContext S c) (hdef : 𝚫ᴬ_[2]-Function₁[V] c) (n : V) :
    HenkinMem S c (henkinFormula L n (n + c n))

end axioms

lemma HenkinMem.isFormula {c : V → V} {x : V} (h : HenkinMem S c x) : IsFormula L x := h.1

end FFL.FirstOrder.Arithmetic.Bootstrapping
