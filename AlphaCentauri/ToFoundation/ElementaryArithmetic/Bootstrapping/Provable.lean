module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.Bootstrapping.Syntax.Proof.Basic
public import AlphaCentauri.ToFoundation.ElementaryArithmetic.Bootstrapping.FixedPoint
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1

/-!
# Internal provability in models of $\mathsf{EA}$: instantiation, modus ponens and induction

The internal provability, in a model of $\mathsf{EA}$, of the codes of the theorems of a theory,
the derivations of an instance of a universal formula and of the conclusion of an implication, and
the induction on a numeral of a formula whose base case and induction step are theorems.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]
  {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁] [LocallyDelta0Axioms T V]

/-- A theorem of `T` is internally provable. -/
theorem provable_natCast_quote_of_provable {σ : Sentence L} (h : T ⊢ σ) :
    Provable T (((⌜σ⌝ : ℕ) : ℕ) : V) := by
  have hℕ : Arithmetic.Bootstrapping.Provable T (⌜σ⌝ : ℕ) :=
    Arithmetic.Bootstrapping.internalize_provability (V := ℕ) h
  have hℕ' : (Arithmetic.Bootstrapping.provable T).val.Evalb ![(⌜σ⌝ : ℕ)] := by
    simpa using hℕ
  have hV := bold_sigma_one_completeness (M := V)
    (Arithmetic.Bootstrapping.provable T).sigma_prop hℕ'
  have e : (ORingStructure.numeral ∘ ![(⌜σ⌝ : ℕ)] : Fin 1 → V) = ![((⌜σ⌝ : ℕ) : V)] := by
    funext i; rw [Fin.fin_one_eq_zero i]; simp [numeral_eq_natCast]
  have e' : (ORingStructure.numeral ∘ (Empty.elim : Empty → ℕ) : Empty → V) = Empty.elim :=
    funext fun x ↦ x.elim
  rw [e, e'] at hV
  exact ((Provable.defined (T := T) (V := V)).df ![_]).mp (by simpa using hV)

section codes

variable (L)

/-- The derivation of `{p(t)}` from a derivation `d` of `{∀ p}`: a cut on `∀ p` against
`∃ ¬p, p(t)`, which follows from the axiom `¬p(t), p(t)`. -/
noncomputable def specializeCode (d p t : V) : V :=
  cutRule {substs1 L t p} (^∀ p) (wkRule (insert (^∀ p) {substs1 L t p}) d)
    (exsIntro (insert (^∃ neg L p) {substs1 L t p}) (neg L p) t
      (axL (insert (neg L (substs1 L t p)) (insert (^∃ neg L p) {substs1 L t p}))
        (substs1 L t p)))

/-- The derivation of `{b}` from derivations `d₁` of `{a → b}` and `d₂` of `{a}`: a cut on
`¬a ∨ b` against `a ∧ ¬b, b`. -/
noncomputable def modusPonensCode (d₁ d₂ a b : V) : V :=
  cutRule {b} (imp L a b) (wkRule (insert (imp L a b) {b}) d₁)
    (andIntro (insert (a ^⋏ neg L b) {b}) a (neg L b)
      (wkRule (insert a (insert (a ^⋏ neg L b) {b})) d₂)
      (axL (insert (neg L b) (insert (a ^⋏ neg L b) {b})) b))

variable {L}

lemma derivationOf_specializeCode {d p t : V} (hp : IsSemiformula L 1 p) (ht : IsTerm L t)
    (hd : DerivationOf T d {^∀ p}) : DerivationOf T (specializeCode L d p t) {substs1 L t p} := by
  have hA : IsFormula L (substs1 L t p) := hp.substs1 ht
  have hall : IsFormula L (^∀ p) := by simpa using hp
  have hnp : IsSemiformula L 1 (neg L p) := by simpa using hp
  have hex : IsFormula L (^∃ neg L p) := by simpa using hnp
  have hnA : IsFormula L (neg L (substs1 L t p)) := by simpa using hA
  have hn : neg L (^∀ p) = ^∃ neg L p := neg_all hp.isUFormula
  have hsn : substs1 L t (neg L p) = neg L (substs1 L t p) :=
    substs_neg (m := 0) hp (by simp [ht])
  refine ⟨by simp [specializeCode], Derivation.cutRule ⟨by simp, ?_⟩ ⟨by simp [hn], ?_⟩⟩
  · refine Derivation.wkRule (by simp [hall, hA]) ?_ hd
    intro x hx
    simp only [mem_singleton_iff] at hx
    simp [hx]
  · refine Derivation.exsIntro (by simp) ht ⟨by simp [hsn], ?_⟩
    exact Derivation.axL (by simp [hA, hex, hnA]) (by simp) (by simp)

lemma derivationOf_modusPonensCode {d₁ d₂ a b : V} (ha : IsFormula L a) (hb : IsFormula L b)
    (hd₁ : DerivationOf T d₁ {imp L a b}) (hd₂ : DerivationOf T d₂ {a}) :
    DerivationOf T (modusPonensCode L d₁ d₂ a b) {b} := by
  have himp : IsFormula L (imp L a b) := by simp [ha, hb]
  have hnb : IsFormula L (neg L b) := by simpa using hb
  have hand : IsFormula L (a ^⋏ neg L b) := by simp [ha, hnb]
  have e : neg L (imp L a b) = a ^⋏ neg L b := by
    simp [imp, ha.isUFormula, hb.isUFormula]
  refine ⟨by simp [modusPonensCode], Derivation.cutRule ⟨by simp, ?_⟩ ⟨by simp [e], ?_⟩⟩
  · refine Derivation.wkRule (by simp [himp, hb]) ?_ hd₁
    intro x hx
    simp only [mem_singleton_iff] at hx
    simp [hx]
  · refine Derivation.andIntro (by simp) ⟨by simp, ?_⟩ ⟨by simp, ?_⟩
    · refine Derivation.wkRule (by simp [ha, hand, hb]) ?_ hd₂
      intro x hx
      simp only [mem_singleton_iff] at hx
      simp [hx]
    · exact Derivation.axL (by simp [hnb, hand, hb]) (by simp) (by simp)

end codes

section size

variable {n : V}

private lemma le_exp_exp_add {a : V} (k : V) (h : a ≤ Exp.exp (Exp.exp n)) :
    a ≤ Exp.exp (Exp.exp (n + k)) :=
  le_trans h (exp_exp_le_of_le le_self_add)

private lemma nine_le_exp_exp (hn : 2 ≤ n) : (9 : V) ≤ Exp.exp (Exp.exp n) := by
  have h2 : Exp.exp (2 : V) = 4 := by
    rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, exp_succ, exp_one]; norm_num
  have h4 : Exp.exp (4 : V) = 16 := by
    rw [show (4 : V) = 2 * 2 by norm_num, exp_even, h2, sq]; norm_num
  refine le_trans ?_ (exp_exp_le_of_le hn)
  rw [h2, h4]
  exact_mod_cast (by norm_num : (9 : ℕ) ≤ 16)

private lemma tag_le_exp_exp (hn : 2 ≤ n) {k : ℕ} (hk : k ≤ 9) :
    (k : V) ≤ Exp.exp (Exp.exp n) :=
  le_trans (by exact_mod_cast hk) (nine_le_exp_exp hn)

/-- A set of elements at most `n` is at most `2 ^ 2 ^ n`. -/
lemma set_le_exp_exp {s : V} (h : ∀ x ∈ s, x ≤ n) : s ≤ Exp.exp (Exp.exp n) :=
  le_trans (lt_exp_iff.mpr fun x hx ↦ lt_succ_iff_le.mpr (h x hx)).le
    (exp_monotone_le.mpr (succ_le_iff_lt.mpr (lt_exp n)))

private lemma adjoin_le_of {a b m : V} (hn : 2 ≤ n) (ha : a ≤ Exp.exp (Exp.exp n))
    (hb : b ≤ Exp.exp (Exp.exp m)) (hnm : n ≤ m := by simp [add_assoc]) :
    a ∷ b ≤ Exp.exp (Exp.exp (m + 2)) :=
  adjoin_le_exp_exp (le_trans (le_trans one_le_two hn) hnm)
    (le_trans ha (exp_exp_le_of_le hnm)) hb

private lemma pair_le_of {a b m : V} (hn : 2 ≤ n) (ha : a ≤ Exp.exp (Exp.exp n))
    (hb : b ≤ Exp.exp (Exp.exp m)) (hnm : n ≤ m := by simp [add_assoc]) :
    ⟪a, b⟫ ≤ Exp.exp (Exp.exp (m + 2)) :=
  le_trans (by rw [adjoin_def]; exact le_self_add) (adjoin_le_of hn ha hb hnm)

variable (hn : 2 ≤ n)
include hn

lemma axL_le_exp_exp {s p : V} (hs : s ≤ Exp.exp (Exp.exp n)) (hp : p ≤ Exp.exp (Exp.exp n)) :
    axL s p ≤ Exp.exp (Exp.exp (n + 2 + 2)) :=
  adjoin_le_of hn hs (pair_le_of hn zero_le hp)

lemma wkRule_le_exp_exp {s d : V} (hs : s ≤ Exp.exp (Exp.exp n))
    (hd : d ≤ Exp.exp (Exp.exp n)) : wkRule s d ≤ Exp.exp (Exp.exp (n + 2 + 2)) :=
  adjoin_le_of hn hs (pair_le_of hn (tag_le_exp_exp hn (k := 6) (by simp)) hd)

lemma exsIntro_le_exp_exp {s p t d : V} (hs : s ≤ Exp.exp (Exp.exp n))
    (hp : p ≤ Exp.exp (Exp.exp n)) (ht : t ≤ Exp.exp (Exp.exp n))
    (hd : d ≤ Exp.exp (Exp.exp n)) :
    exsIntro s p t d ≤ Exp.exp (Exp.exp (n + 2 + 2 + 2 + 2)) :=
  adjoin_le_of hn hs <| pair_le_of hn (tag_le_exp_exp hn (k := 5) (by simp)) <|
    pair_le_of hn hp <| pair_le_of hn ht hd

lemma andIntro_le_exp_exp {s p q dp dq : V} (hs : s ≤ Exp.exp (Exp.exp n))
    (hp : p ≤ Exp.exp (Exp.exp n)) (hq : q ≤ Exp.exp (Exp.exp n))
    (hdp : dp ≤ Exp.exp (Exp.exp n)) (hdq : dq ≤ Exp.exp (Exp.exp n)) :
    andIntro s p q dp dq ≤ Exp.exp (Exp.exp (n + 2 + 2 + 2 + 2 + 2)) :=
  adjoin_le_of hn hs <| pair_le_of hn (tag_le_exp_exp hn (k := 2) (by simp)) <|
    pair_le_of hn hp <| pair_le_of hn hq <| pair_le_of hn hdp hdq

lemma cutRule_le_exp_exp {s p d₁ d₂ : V} (hs : s ≤ Exp.exp (Exp.exp n))
    (hp : p ≤ Exp.exp (Exp.exp n)) (hd₁ : d₁ ≤ Exp.exp (Exp.exp n))
    (hd₂ : d₂ ≤ Exp.exp (Exp.exp n)) :
    cutRule s p d₁ d₂ ≤ Exp.exp (Exp.exp (n + 2 + 2 + 2 + 2)) :=
  adjoin_le_of hn hs <| pair_le_of hn (tag_le_exp_exp hn (k := 8) (by simp)) <|
    pair_le_of hn hp <| pair_le_of hn hd₁ hd₂

end size

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
