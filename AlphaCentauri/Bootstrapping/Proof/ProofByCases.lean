module

public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Coding
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed

/-!
# Proof by cases on an added axiom

A sentence is provable from the theory it is added to, and a formula code provable both from
`T + φ` and from `T + ψ + ¬φ` is provable from `T + (φ ∨ ψ)`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open _root_.FFL.Entailment

section union

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

lemma tprovable_union_singleton (σ : Sentence L) : (T ∪ {σ}).internalize V ⊢ ⌜σ⌝ := by
  have h₁ : T.internalize V ⊢ (⌜σ⌝ : Formula V L) 🡒 ⌜σ⌝ := by cl_prover
  rw [tprovable_iff_provable, Semiformula.val_imp, ← Sentence.quote_eq] at h₁
  exact tprovable_iff_provable.mpr <| (Derivation.provable_union_singleton_iff σ).mpr h₁

end union

section union_or

variable {T : ArithmeticTheory} [T.Δ₁] {φ ψ : ArithmeticSentence}

lemma provable_union_or {X : V} (h₁ : Provable (T ∪ {φ}) X) (h₂ : Provable (T ∪ {ψ} ∪ {∼φ}) X) :
    Provable (T ∪ {φ ⋎ ψ}) X := by
  rw [Derivation.provable_union_singleton_iff] at h₁ h₂ ⊢
  rw [Derivation.provable_union_singleton_iff] at h₂
  have hX : IsFormula ℒₒᵣ X := by
    simpa [Bootstrapping.imp] using h₁.toDerivable.isFormulaSet
  have h₁' : T.internalize V ⊢ (⌜φ⌝ : Formula V ℒₒᵣ) 🡒 ⟨X, hX⟩ := by
    rwa [tprovable_iff_provable, Semiformula.val_imp, ← Sentence.quote_eq]
  have h₂' : T.internalize V ⊢ (⌜ψ⌝ : Formula V ℒₒᵣ) 🡒 ∼⌜φ⌝ 🡒 ⟨X, hX⟩ := by
    rwa [tprovable_iff_provable, Semiformula.val_imp, Semiformula.val_imp, Semiformula.val_neg,
      ← Sentence.quote_eq, ← Sentence.quote_eq, ← quote_neg_sentence]
  have h₃ : T.internalize V ⊢ (⌜φ⌝ : Formula V ℒₒᵣ) ⋎ ⌜ψ⌝ 🡒 ⟨X, hX⟩ := by
    cl_prover [h₁', h₂']
  rwa [tprovable_iff_provable, Semiformula.val_imp, Semiformula.val_or, ← Sentence.quote_eq,
    ← Sentence.quote_eq, ← Sentence.quote_or] at h₃

end union_or

end FFL.FirstOrder.Arithmetic.Bootstrapping
