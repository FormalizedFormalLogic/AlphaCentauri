module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.HFS.Vec
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Language

/-!
# The language of arithmetic in models of $\mathsf{EA}$

The file `Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Language.lean` on the internalized
language $\mathcal{L}_{\mathrm{OR}}$, ported to models of $\mathsf{EA}$: the codes of the function
and relation symbols of $\mathcal{L}_{\mathrm{OR}}$ are the ones given by `zeroIndex`, ...,
`ltIndex`, and `isFunc_iff_LOR` and `isRel_iff_LOR` describe the codes of symbols.

- [HP98, §V.3]
-/

@[expose] public section


open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping.Arithmetic

-- `Arithmetic` is intentionally re-opened here, as in Foundation.
set_option linter.dupNamespace false

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping
  _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

@[simp] lemma LOR_func_zeroIndex : (ℒₒᵣ).IsFunc 0 (zeroIndex : V) := by
  simpa using! codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.Zero.zero

@[simp] lemma LOR_func_oneIndex : (ℒₒᵣ).IsFunc 0 (oneIndex : V) := by
  simpa using! codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.One.one

@[simp] lemma LOR_func_addIndex : (ℒₒᵣ).IsFunc 2 (addIndex : V) := by
  simpa using! codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.Add.add

@[simp] lemma LOR_func_mulIndex : (ℒₒᵣ).IsFunc 2 (mulIndex : V) := by
  simpa using! codeIn_func_quote (V := V) (L := ℒₒᵣ) Language.Mul.mul

@[simp] lemma LOR_rel_eqIndex : (ℒₒᵣ).IsRel 2 (eqIndex : V) := by
  simpa using! codeIn_rel_quote (V := V) (L := ℒₒᵣ) Language.Eq.eq

@[simp] lemma LOR_rel_ltIndex : (ℒₒᵣ).IsRel 2 (ltIndex : V) := by
  simpa using! codeIn_rel_quote (V := V) (L := ℒₒᵣ) Language.LT.lt

private lemma func_def_LOR :
    (ℒₒᵣ).isFunc =
      .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)” := rfl

private lemma rel_def_LOR : (ℒₒᵣ).isRel = .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” := rfl

@[reducible] instance gödelQuoteFuncLOR (k) : GödelQuote ((ℒₒᵣ).Func k) V := gödelQuoteFunc k

@[reducible] instance gödelQuoteRelLOR (k) : GödelQuote ((ℒₒᵣ).Rel k) V := gödelQuoteRel k

lemma isFunc_iff_LOR {k f : V} :
    (ℒₒᵣ).IsFunc k f ↔
    (k = 0 ∧ f = ⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝) ∨
    (k = 0 ∧ f = ⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝) ∨
    (k = 2 ∧ f = ⌜(Language.Add.add : (ℒₒᵣ).Func 2)⌝) ∨
    (k = 2 ∧ f = ⌜(Language.Mul.mul : (ℒₒᵣ).Func 2)⌝) := by
  rw [isFunc_def (L := ℒₒᵣ), func_def_LOR]
  suffices
    k = 0 ∧ f = 0 ∨ k = 0 ∧ f = 1 ∨ k = 2 ∧ f = 0 ∨ k = 2 ∧ f = 1 ↔ _ by simpa
  apply iff_of_eq
  congr
  · calc
      (1 : V) = (1 : ℕ) := by simp
      _       = ⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ := by rfl
  · calc
      (1 : V) = (1 : ℕ) := by simp
      _       = ⌜(Language.Mul.mul : (ℒₒᵣ).Func 2)⌝ := by rfl

lemma isRel_iff_LOR {k R : V} :
    (ℒₒᵣ).IsRel k R ↔
    (k = 2 ∧ R = ⌜(Language.Eq.eq : (ℒₒᵣ).Rel 2)⌝) ∨
    (k = 2 ∧ R = ⌜(Language.LT.lt : (ℒₒᵣ).Rel 2)⌝) := by
  rw [isRel_def (L := ℒₒᵣ), rel_def_LOR]
  suffices
    k = 2 ∧ R = 0 ∨ k = 2 ∧ R = 1 ↔ _ by simpa
  apply iff_of_eq
  congr
  · calc (1 : V) = (1 : ℕ) := by simp

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping.Arithmetic

