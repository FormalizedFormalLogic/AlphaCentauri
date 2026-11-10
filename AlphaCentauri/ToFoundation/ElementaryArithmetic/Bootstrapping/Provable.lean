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

section transfer

open Bounding

omit [V↓[ℒₒᵣ] ⊧* 𝗘𝗔] in
private lemma numeral_comp_elim :
    (ORingStructure.numeral ∘ (Empty.elim : Empty → ℕ) : Empty → V) = Empty.elim :=
  funext fun x ↦ x.elim

/-- A function on `V` and a function on `ℕ` defined by the same $\Sigma_1$ formula agree on
standard arguments. -/
lemma natCast_apply_of_defined {k : ℕ} {F : 𝚺ᴬ₁.Semisentence (k + 1)}
    {f : (Fin k → V) → V} {g : (Fin k → ℕ) → ℕ} (hf : 𝚺ᴬ₁.DefinedFunction f F)
    (hg : 𝚺ᴬ₁.DefinedFunction g F) (a : Fin k → ℕ) :
    f (fun i ↦ (a i : V)) = (g a : V) := by
  have hℕ : F.val.Evalb (g a :> a) := (hg.df (g a :> a)).mpr (by simp)
  have hV := bold_sigma_one_completeness (M := V) F.sigma_prop hℕ
  have e : (ORingStructure.numeral ∘ (g a :> a) : Fin (k + 1) → V) =
      ((g a : V) :> fun i ↦ (a i : V)) := by
    funext i; cases i using Fin.cases <;> simp [numeral_eq_natCast]
  rw [e, numeral_comp_elim] at hV
  simpa [hf.iff, eq_comm] using hV

/-- A predicate on `V` and a predicate on `ℕ` defined by the same $\Sigma_1$ formula: the second
at standard arguments implies the first. -/
lemma of_natCast_of_defined {k : ℕ} {F : 𝚺ᴬ₁.Semisentence k}
    {P : (Fin k → V) → Prop} {Q : (Fin k → ℕ) → Prop} (hP : 𝚺ᴬ₁.Defined P F)
    (hQ : 𝚺ᴬ₁.Defined Q F) {a : Fin k → ℕ} (h : Q a) : P (fun i ↦ (a i : V)) := by
  have hV := bold_sigma_one_completeness (M := V) F.sigma_prop ((hQ.df a).mpr h)
  have e : (ORingStructure.numeral ∘ a : Fin k → V) = fun i ↦ (a i : V) := by
    funext i; simp [numeral_eq_natCast]
  rw [e, numeral_comp_elim] at hV
  simpa [hP.iff] using hV

lemma natCast_qqAll (a : ℕ) : ((Arithmetic.Bootstrapping.qqAll a : ℕ) : V) = ^∀ (a : V) :=
  (natCast_apply_of_defined (f := fun v ↦ ^∀ (v 0))
    (g := fun v ↦ Arithmetic.Bootstrapping.qqAll (v 0))
    (qqForall_defined.of_zero (ℌ := 𝚺ᴬ₁))
    (Arithmetic.Bootstrapping.qqForall_defined.of_zero (ℌ := 𝚺ᴬ₁)) ![a]).symm

lemma natCast_qqBvar (a : ℕ) : ((Arithmetic.Bootstrapping.qqBvar a : ℕ) : V) = ^#(a : V) :=
  (natCast_apply_of_defined (f := fun v ↦ ^#(v 0))
    (g := fun v ↦ Arithmetic.Bootstrapping.qqBvar (v 0))
    (qqBvar_defined.of_zero (ℌ := 𝚺ᴬ₁))
    (Arithmetic.Bootstrapping.qqBvar_defined.of_zero (ℌ := 𝚺ᴬ₁)) ![a]).symm

lemma natCast_adjoin (a b : ℕ) : (((a ∷ b : ℕ) : ℕ) : V) = (a : V) ∷ (b : V) :=
  (natCast_apply_of_defined (f := fun v ↦ v 0 ∷ v 1) (g := fun v ↦ v 0 ∷ v 1)
    (adjoin_defined.of_zero (ℌ := 𝚺ᴬ₁))
    (FFL.FirstOrder.Arithmetic.adjoin_defined.of_zero (ℌ := 𝚺ᴬ₁)) ![a, b]).symm

lemma natCast_imp (a b : ℕ) :
    ((Arithmetic.Bootstrapping.imp ℒₒᵣ a b : ℕ) : V) = imp ℒₒᵣ (a : V) (b : V) := by
  simpa using (natCast_apply_of_defined (imp.defined (L := ℒₒᵣ))
    (Arithmetic.Bootstrapping.imp.defined (L := ℒₒᵣ)) ![a, b]).symm

lemma natCast_subst (a b : ℕ) :
    ((Arithmetic.Bootstrapping.subst ℒₒᵣ a b : ℕ) : V) = subst ℒₒᵣ (a : V) (b : V) := by
  simpa using (natCast_apply_of_defined (subst.defined (L := ℒₒᵣ))
    (Arithmetic.Bootstrapping.subst.defined (L := ℒₒᵣ)) ![a, b]).symm

lemma natCast_numeral (a : ℕ) :
    ((Arithmetic.Bootstrapping.Arithmetic.numeral a : ℕ) : V) = Arithmetic.numeral (a : V) := by
  simpa using (natCast_apply_of_defined Arithmetic.numeral_defined
    Arithmetic.Bootstrapping.Arithmetic.numeral_defined ![a]).symm

lemma natCast_qqAdd (a b : ℕ) :
    ((Arithmetic.Bootstrapping.Arithmetic.qqAdd a b : ℕ) : V) =
      Arithmetic.qqAdd (a : V) (b : V) := by
  simpa using (natCast_apply_of_defined Arithmetic.qqAdd_defined
    Arithmetic.Bootstrapping.Arithmetic.qqAdd_defined ![a, b]).symm

lemma isSemiformula_natCast {n a : ℕ} (h : Arithmetic.Bootstrapping.IsSemiformula ℒₒᵣ n a) :
    IsSemiformula ℒₒᵣ (n : V) (a : V) := by
  simpa using of_natCast_of_defined
    (F := (Arithmetic.Bootstrapping.isSemiformula ℒₒᵣ).sigma)
    (P := fun v ↦ IsSemiformula ℒₒᵣ (v 0) (v 1))
    (Q := fun v ↦ Arithmetic.Bootstrapping.IsSemiformula ℒₒᵣ (v 0) (v 1))
    (.mk (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).df)
    (.mk (Arithmetic.Bootstrapping.IsSemiformula.defined (L := ℒₒᵣ) (V := ℕ)).df)
    (a := ![n, a]) h

lemma natCast_matrixToVec {k : ℕ} (v : Fin k → ℕ) :
    ((FFL.FirstOrder.Arithmetic.matrixToVec v : ℕ) : V) = matrixToVec fun i ↦ (v i : V) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [FFL.FirstOrder.Arithmetic.matrixToVec_succ, natCast_adjoin, ih, matrixToVec_succ]
    rfl

end transfer

section quote

open FFL.FirstOrder

variable {n : ℕ}

lemma natCast_quote_all (φ : ArithmeticSemisentence (n + 1)) :
    ((⌜∀¹ φ⌝ : ℕ) : V) = ^∀ ((⌜φ⌝ : ℕ) : V) := by
  rw [Sentence.quote_all, natCast_qqAll]

lemma natCast_quote_imply (φ ψ : ArithmeticSemisentence n) :
    ((⌜φ 🡒 ψ⌝ : ℕ) : V) = imp ℒₒᵣ ((⌜φ⌝ : ℕ) : V) ((⌜ψ⌝ : ℕ) : V) := by
  rw [← natCast_imp, Sentence.quote_eq, LCWQIsoGödelQuote.imply]
  rfl

lemma isSemiformula_natCast_quote (φ : ArithmeticSemisentence n) :
    IsSemiformula ℒₒᵣ (n : V) ((⌜φ⌝ : ℕ) : V) := by
  simpa using isSemiformula_natCast (V := V) (Sentence.quote_isSemiformula (V := ℕ) φ)

lemma natCast_quote_rew_subst {k : ℕ} (φ : ArithmeticSemisentence k)
    (w : Fin k → ArithmeticSemiterm Empty n) :
    ((⌜Rew.subst w ▹ φ⌝ : ℕ) : V) = subst ℒₒᵣ
      (matrixToVec fun i ↦ ((⌜(Rew.emb (w i) : SyntacticSemiterm ℒₒᵣ n)⌝ : ℕ) : V))
      ((⌜φ⌝ : ℕ) : V) := by
  rw [← natCast_matrixToVec, ← natCast_subst]
  congr 1
  simp [Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_emb]
  rfl

lemma natCast_quote_bvar (i : Fin n) :
    ((⌜(Rew.emb (#i : ArithmeticSemiterm Empty n) : SyntacticSemiterm ℒₒᵣ n)⌝ : ℕ) : V) =
      ^#(i : V) := by
  simpa using natCast_qqBvar (V := V) i

lemma natCast_quote_numeral (k : ℕ) :
    ((⌜(Rew.emb (↑k : ArithmeticSemiterm Empty n) : SyntacticSemiterm ℒₒᵣ n)⌝ : ℕ) : V) =
      Arithmetic.numeral (k : V) := by
  have : (⌜(Rew.emb (↑k : ArithmeticSemiterm Empty n) : SyntacticSemiterm ℒₒᵣ n)⌝ : ℕ) =
      (Arithmetic.Bootstrapping.Arithmetic.typedNumeral k :
        Arithmetic.Bootstrapping.Semiterm ℕ ℒₒᵣ n).val :=
    congrArg Arithmetic.Bootstrapping.Semiterm.val (by simp)
  rw [this]
  exact natCast_numeral k

lemma natCast_quote_bvar_add_one :
    ((⌜(Rew.emb (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) :
      SyntacticSemiterm ℒₒᵣ (n + 1))⌝ : ℕ) : V) = (Arithmetic.qqAdd (^#0) 𝟏 : V) := by
  have : (⌜(Rew.emb (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) :
      SyntacticSemiterm ℒₒᵣ (n + 1))⌝ : ℕ) =
      (Arithmetic.Bootstrapping.Semiterm.bvar 0 +
        Arithmetic.Bootstrapping.Arithmetic.typedNumeral 1 :
          Arithmetic.Bootstrapping.Semiterm ℕ ℒₒᵣ (n + 1)).val :=
    congrArg Arithmetic.Bootstrapping.Semiterm.val (by simp)
  rw [this]
  change ((Arithmetic.Bootstrapping.Arithmetic.qqAdd
    (Arithmetic.Bootstrapping.qqBvar ((0 : ℕ) : ℕ))
    (Arithmetic.Bootstrapping.Arithmetic.numeral ((1 : ℕ) : ℕ)) : ℕ) : V) = _
  rw [natCast_qqAdd, natCast_qqBvar, natCast_numeral]
  simp

end quote

section

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]
  [LocallyDelta0Axioms T V]

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
  rw [e, numeral_comp_elim] at hV
  exact ((Provable.defined (T := T) (V := V)).df ![_]).mp (by simpa using hV)

section codes

variable (L)

/-- A derivation of `{p(t)}` from a derivation `d` of `{∀ p}`. -/
noncomputable def specializeCode (d p t : V) : V :=
  cutRule {substs1 L t p} (^∀ p) (wkRule (insert (^∀ p) {substs1 L t p}) d)
    (exsIntro (insert (^∃ neg L p) {substs1 L t p}) (neg L p) t
      (axL (insert (neg L (substs1 L t p)) (insert (^∃ neg L p) {substs1 L t p}))
        (substs1 L t p)))

/-- A derivation of `{b}` from derivations `d₁` of `{a → b}` and `d₂` of `{a}`. -/
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

private lemma le_exp_exp_add_four {a : V} (h : a ≤ Exp.exp (Exp.exp n)) :
    a ≤ Exp.exp (Exp.exp (n + 2 + 2)) := by
  simpa [add_assoc] using le_exp_exp_add (2 + 2) h

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

private lemma set3_le_exp_exp {N a b c : V} (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) :
    (insert a (insert b {c}) : V) ≤ Exp.exp (Exp.exp N) :=
  set_le_exp_exp <| by
    intro x hx
    rcases (by simpa using hx : x = a ∨ x = b ∨ x = c) with rfl | rfl | rfl <;> assumption

private lemma set2_le_exp_exp {N a b : V} (ha : a ≤ N) (hb : b ≤ N) :
    (insert a {b} : V) ≤ Exp.exp (Exp.exp N) :=
  set_le_exp_exp <| by
    intro x hx
    rcases (by simpa using hx : x = a ∨ x = b) with rfl | rfl <;> assumption

private lemma set1_le_exp_exp {N a : V} (ha : a ≤ N) : ({a} : V) ≤ Exp.exp (Exp.exp N) :=
  set_le_exp_exp <| by
    intro x hx
    rw [(by simpa using hx : x = a)]
    exact ha

section rules

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

end rules

variable (L) in
/-- The largest code of a formula or term occurring in `specializeCode L d p t`. -/
noncomputable def specializeSize (p t : V) : V :=
  max (substs1 L t p) (max (^∀ p) (max (^∃ neg L p) (max (neg L p)
    (max (neg L (substs1 L t p)) t))))

lemma specializeCode_le_exp_exp {n d p t : V} (hn : 2 ≤ n) (hN : specializeSize L p t ≤ n)
    (hd : d ≤ Exp.exp (Exp.exp n)) :
    specializeCode L d p t ≤ Exp.exp (Exp.exp (n + 20)) := by
  simp only [specializeSize, max_le_iff] at hN
  obtain ⟨hA, hall, hex, hnp, hnA, ht⟩ := hN
  have hD1 := axL_le_exp_exp hn (set3_le_exp_exp hnA hex hA) (le_exp_exp hA)
  have hD2 := exsIntro_le_exp_exp (n := n + 2 + 2) (le_trans hn (by simp [add_assoc]))
    (le_exp_exp_add_four (set2_le_exp_exp hex hA)) (le_exp_exp_add_four (le_exp_exp hnp))
    (le_exp_exp_add_four (le_exp_exp ht)) hD1
  have hD0 := wkRule_le_exp_exp hn (set2_le_exp_exp hall hA) hd
  have := cutRule_le_exp_exp (n := n + 2 + 2 + 2 + 2 + 2 + 2) (le_trans hn (by simp [add_assoc]))
    (le_trans (set1_le_exp_exp hA) (exp_exp_le_of_le (by simp [add_assoc])))
    (le_trans (le_exp_exp hall) (exp_exp_le_of_le (by simp [add_assoc])))
    (le_trans hD0 (exp_exp_le_of_le (by simp [add_assoc]))) hD2
  exact le_trans this (exp_exp_le_of_le (le_of_eq (by norm_num [add_assoc])))

variable (L) in
/-- The largest code of a formula occurring in `modusPonensCode L d₁ d₂ a b`. -/
noncomputable def modusPonensSize (a b : V) : V :=
  max (imp L a b) (max a (max b (max (a ^⋏ neg L b) (neg L b))))

lemma modusPonensCode_le_exp_exp {n d₁ d₂ a b : V} (hn : 2 ≤ n) (hN : modusPonensSize L a b ≤ n)
    (hd₁ : d₁ ≤ Exp.exp (Exp.exp n)) (hd₂ : d₂ ≤ Exp.exp (Exp.exp n)) :
    modusPonensCode L d₁ d₂ a b ≤ Exp.exp (Exp.exp (n + 22)) := by
  simp only [modusPonensSize, max_le_iff] at hN
  obtain ⟨himp, ha, hb, hand, hnb⟩ := hN
  have hwk := wkRule_le_exp_exp hn (set3_le_exp_exp ha hand hb) hd₂
  have hax := axL_le_exp_exp hn (set3_le_exp_exp hnb hand hb) (le_exp_exp hb)
  have hand' := andIntro_le_exp_exp (n := n + 2 + 2) (le_trans hn (by simp [add_assoc]))
    (le_exp_exp_add_four (set2_le_exp_exp hand hb)) (le_exp_exp_add_four (le_exp_exp ha))
    (le_exp_exp_add_four (le_exp_exp hnb)) hwk hax
  have hwk₁ := wkRule_le_exp_exp hn (set2_le_exp_exp himp hb) hd₁
  have := cutRule_le_exp_exp (n := n + 2 + 2 + 2 + 2 + 2 + 2 + 2)
    (le_trans hn (by simp [add_assoc]))
    (le_trans (set1_le_exp_exp hb) (exp_exp_le_of_le (by simp [add_assoc])))
    (le_trans (le_exp_exp himp) (exp_exp_le_of_le (by simp [add_assoc])))
    (le_trans hwk₁ (exp_exp_le_of_le (by simp [add_assoc]))) hand'
  exact le_trans this (exp_exp_le_of_le (le_of_eq (by norm_num [add_assoc])))

end size

end

section numerals

open FFL.FirstOrder Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁] [LocallyDelta0Axioms T V] {m : ℕ}

lemma substNumerals_cons (φ x : V) (v : Fin m → V) :
    substNumerals φ (x :> v) = subst ℒₒᵣ (numeral x ∷ matrixToVec fun i ↦ numeral (v i)) φ :=
  rfl

lemma isSemitermVec_numerals (v : Fin m → V) (n : V) :
    IsSemitermVec ℒₒᵣ (m : V) n (matrixToVec fun i ↦ numeral (v i)) :=
  isSemitermVec_matrixToVec.mpr fun i ↦ numeral_semiterm n (v i)

lemma subst_natCast_quote_rew_subst {k j : ℕ} (φ : ArithmeticSemisentence k)
    (u : Fin k → ArithmeticSemiterm Empty j) {u' : Fin k → V}
    (hu : ∀ i, ((⌜(Rew.emb (u i) : SyntacticSemiterm ℒₒᵣ j)⌝ : ℕ) : V) = u' i)
    (hu' : ∀ i, IsSemiterm ℒₒᵣ (j : V) (u' i)) {n W : V} (hW : IsSemitermVec ℒₒᵣ (j : V) n W) :
    subst ℒₒᵣ W ((⌜Rew.subst u ▹ φ⌝ : ℕ) : V) =
      subst ℒₒᵣ (matrixToVec fun i ↦ termSubst ℒₒᵣ W (u' i)) ((⌜φ⌝ : ℕ) : V) := by
  rw [natCast_quote_rew_subst, funext hu,
    substs_substs (isSemiformula_natCast_quote φ) hW (isSemitermVec_matrixToVec.mpr hu'),
    termSubstVec_matrixToVec fun i ↦ (hu' i).isUTerm]

lemma substNumerals_natCast_quote_all (φ : ArithmeticSemisentence (m + 1)) (v : Fin m → V) :
    substNumerals ((⌜∀¹ φ⌝ : ℕ) : V) v =
      ^∀ subst ℒₒᵣ (qVec ℒₒᵣ (matrixToVec fun i ↦ numeral (v i))) ((⌜φ⌝ : ℕ) : V) := by
  rw [substNumerals, natCast_quote_all, substs_all (isSemiformula_natCast_quote φ).isUFormula]

lemma isSemiformula_subst_qVec_numerals (φ : ArithmeticSemisentence (m + 1)) (v : Fin m → V) :
    IsSemiformula ℒₒᵣ 1
      (subst ℒₒᵣ (qVec ℒₒᵣ (matrixToVec fun i ↦ numeral (v i))) ((⌜φ⌝ : ℕ) : V)) := by
  simpa using (isSemiformula_natCast_quote (V := V) φ).subst (isSemitermVec_numerals v 0).qVec

lemma substs1_subst_qVec_numerals (φ : ArithmeticSemisentence (m + 1)) (v : Fin m → V) (x : V) :
    substs1 ℒₒᵣ (numeral x)
        (subst ℒₒᵣ (qVec ℒₒᵣ (matrixToVec fun i ↦ numeral (v i))) ((⌜φ⌝ : ℕ) : V)) =
      substNumerals ((⌜φ⌝ : ℕ) : V) (x :> v) := by
  rw [substNumerals_cons, substs1_subst_qVec (isSemitermVec_numerals v 0)
    (by simpa using isSemiformula_natCast_quote (V := V) φ) (numeral_semiterm 0 x)]

/-- Instantiating an internally provable instance by numerals of `∀¹ φ` at one more numeral. -/
lemma provable_substNumerals_of_provable_substNumerals_all (φ : ArithmeticSemisentence (m + 1))
    {v : Fin m → V} (h : Provable T (substNumerals ((⌜∀¹ φ⌝ : ℕ) : V) v)) (x : V) :
    Provable T (substNumerals ((⌜φ⌝ : ℕ) : V) (x :> v)) := by
  obtain ⟨d, hd⟩ := h
  rw [substNumerals_natCast_quote_all] at hd
  rw [← substs1_subst_qVec_numerals]
  exact ⟨_, derivationOf_specializeCode (isSemiformula_subst_qVec_numerals φ v)
    (numeral_semiterm 0 x) hd⟩

/-- Instantiating an internally provable universal closure at numerals. -/
lemma provable_substNumerals_of_provable_allClosure {k : ℕ} (φ : ArithmeticSemisentence k)
    (h : Provable T ((⌜∀¹* φ⌝ : ℕ) : V)) (v : Fin k → V) :
    Provable T (substNumerals ((⌜φ⌝ : ℕ) : V) v) := by
  induction k with
  | zero =>
    rwa [substNumerals, matrixToVec_nil,
      subst_eq_self (by simpa using isSemiformula_natCast_quote (V := V) φ) (by simp) (by simp)]
  | succ k ih =>
    rw [← Matrix.cons_head_tail v]
    exact provable_substNumerals_of_provable_substNumerals_all φ (ih (∀¹ φ) h _) _

private lemma max_specializeSize_modusPonensSize_locallyDelta0 {S : V} {A : V → V}
    (hA : LocallyDelta0Function₁ A) :
    LocallyDelta0Function₁ fun y ↦
      max (specializeSize ℒₒᵣ S (numeral y)) (modusPonensSize ℒₒᵣ (A y) (A (y + 1))) := by
  have hn := numeral_locallyDelta0.comp₁ (LocallyDelta0Function.var (V := V) (0 : Fin 1))
  have hs := (substs1_locallyDelta0 (L := ℒₒᵣ)).comp₂ hn (LocallyDelta0Function.const S)
  have ha : LocallyDelta0Function fun v : Fin 1 → V ↦ A (v 0) := hA
  have hb := hA.comp₁
    (LocallyDelta0Function.add_one (LocallyDelta0Function.var (V := V) (0 : Fin 1)))
  have hnb := (neg_locallyDelta0 (L := ℒₒᵣ)).comp₁ hb
  have hmax := LocallyDelta0Function.max (V := V)
  exact hmax.comp₂
    (hmax.comp₂ hs <| hmax.comp₂ (.const _) <| hmax.comp₂ (.const _) <| hmax.comp₂ (.const _) <|
      hmax.comp₂ ((neg_locallyDelta0 (L := ℒₒᵣ)).comp₁ hs) hn)
    (hmax.comp₂ ((imp_locallyDelta0 (L := ℒₒᵣ)).comp₂ ha hb) <| hmax.comp₂ ha <| hmax.comp₂ hb <|
      hmax.comp₂ (qqAnd_locallyDelta0.comp₂ ha hnb) hnb)

lemma modusPonensCode_specializeCode_le_exp_exp {n e d S t a b : V} (hn : 2 ≤ n)
    (hN : max (specializeSize ℒₒᵣ S t) (modusPonensSize ℒₒᵣ a b) ≤ n)
    (he : e ≤ Exp.exp (Exp.exp n)) (hd : d ≤ Exp.exp (Exp.exp n)) :
    modusPonensCode ℒₒᵣ (specializeCode ℒₒᵣ e S t) d a b ≤ Exp.exp (Exp.exp (n + 42)) := by
  rw [max_le_iff] at hN
  have := modusPonensCode_le_exp_exp (n := n + 20) (le_trans hn le_self_add)
    (le_trans hN.2 le_self_add) (specializeCode_le_exp_exp hn hN.1 he)
    (le_trans hd (exp_exp_le_of_le le_self_add))
  exact le_trans this (exp_exp_le_of_le (le_of_eq (by norm_num [add_assoc])))

/-- If `{∀ S}` and `{A 1}` are derivable and the instance of `S` at the numeral of each `y > 0` is
`A y → A (y + 1)`, then every `A (y + 1)` is internally provable. -/
lemma provable_succ_of_derivationOf_all {S e d : V} {A : V → V} (hA : LocallyDelta0Function₁ A)
    (hS : IsSemiformula ℒₒᵣ 1 S) (hAf : ∀ y, IsFormula ℒₒᵣ (A y))
    (he : DerivationOf T e {^∀ S}) (hd : DerivationOf T d {A 1})
    (hstep : ∀ y, 0 < y → substs1 ℒₒᵣ (numeral y) S = imp ℒₒᵣ (A y) (A (y + 1))) (y : V) :
    Provable T (A (y + 1)) := by
  set c : V → V := fun y ↦
    max (specializeSize ℒₒᵣ S (numeral y)) (modusPonensSize ℒₒᵣ (A y) (A (y + 1)))
  have hc : LocallyDelta0Function₁ c := max_specializeSize_modusPonensSize_locallyDelta0 hA
  set M := d + e + 2
  set B : V → V := fun y ↦ Exp.exp (Exp.exp (42 * y + (prefixMax c y + M)))
  have hB : LocallyDelta0Function₁ B := LocallyDelta0Function.exp_exp_mul_add 42
    (LocallyDelta0Function.var 0)
    (LocallyDelta0Function.add.comp₂ (prefixMax_locallyDelta0 hc) (LocallyDelta0Function.const M))
  have hP : LocallyDelta0Pred fun y ↦ ∃ d ≤ B (y + 1), DerivationOf T d {A (y + 1)} := by
    have := LocallyDelta0.bexs_le_function
      (hB.comp₁ (LocallyDelta0Function.add_one (LocallyDelta0Function.var (V := V) (0 : Fin 1))))
      (P := fun u : Fin 2 → V ↦ fstIdx (u 0) = Exp.exp (A (u 1 + 1)) ∧ Derivation T (u 0))
      ((LocallyDelta0.eq (fstIdx_locallyDelta0.comp₁ (LocallyDelta0Function.var 0))
        (LocallyDelta0Function.exp.comp₁
          (hA.comp₁ (LocallyDelta0Function.add_one (LocallyDelta0Function.var 1))))).and
        (derivation_locallyDelta0.pred_comp (LocallyDelta0Function.var 0)))
    exact this.of_iff fun v ↦ by simp [DerivationOf, singleton_def]
  have hM : ∀ x, M ≤ 42 * x + (prefixMax c x + M) := fun x ↦ le_trans le_add_self le_add_self
  have key : ∀ y, ∃ d ≤ B (y + 1), DerivationOf T d {A (y + 1)} := by
    apply LocallyDelta0Pred.succ_induction hP
    · use d
      exact ⟨le_exp_exp (le_trans (le_trans le_self_add le_self_add) (hM _)), by simpa using hd⟩
    · rintro y ⟨d', hd'B, hd'⟩
      have hspec := derivationOf_specializeCode hS (numeral_semiterm 0 (y + 1)) he
      rw [hstep (y + 1) (by simp)] at hspec
      have h₁ : 42 * (y + 1) + (prefixMax c (y + 1) + M) + 42 ≤
          42 * (y + 1 + 1) + (prefixMax c (y + 1 + 1) + M) := by
        have := prefixMax_monotone hc (le_self_add (a := y + 1) (b := 1))
        calc 42 * (y + 1) + (prefixMax c (y + 1) + M) + 42
            = 42 * (y + 1) + 42 + (prefixMax c (y + 1) + M) := by grind
          _ ≤ 42 * (y + 1) + 42 + (prefixMax c (y + 1 + 1) + M) := by gcongr
          _ = 42 * (y + 1 + 1) + (prefixMax c (y + 1 + 1) + M) := by grind
      use modusPonensCode ℒₒᵣ (specializeCode ℒₒᵣ e S (numeral (y + 1))) d'
        (A (y + 1)) (A (y + 1 + 1))
      exact ⟨le_trans (modusPonensCode_specializeCode_le_exp_exp
        (le_trans (by simp [M]) (hM (y + 1)))
        (le_trans (le_prefixMax hc le_rfl) (le_trans le_self_add le_add_self))
        (le_exp_exp (le_trans (le_trans le_add_self le_self_add) (hM (y + 1)))) hd'B)
        (exp_exp_le_of_le h₁), derivationOf_modusPonensCode (hAf _) (hAf _) hspec hd'⟩
  obtain ⟨d', -, hd'⟩ := key y
  exact ⟨d', hd'⟩

omit [T.Δ₁] in
private lemma provable_one_of_provable_zero_of_provable_succ [𝗣𝗔⁻ ⪯ T]
    (φ : ArithmeticSemisentence (m + 1)) (h₀ : T ⊢ ∀¹* (Rew.subst (‘0’ :> fun i ↦ #i) ▹ φ))
    (hs : T ⊢ ∀¹* (φ 🡒 Rew.subst (‘#0 + 1’ :> fun i ↦ #i.succ) ▹ φ)) :
    T ⊢ ∀¹* (Rew.subst (‘1’ :> fun i ↦ #i) ▹ φ) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance
  apply Arithmetic.complete.{0} T _
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory hM
  have h₀' := models_of_provable hM h₀
  have hs' := models_of_provable hM hs
  simp only [models_iff, Semiformula.eval_allClosure, Semiformula.eval_substs,
    LogicalConnective.HomClass.map_imply] at h₀' hs' ⊢
  intro e
  have e₀ : (Semiterm.val e Empty.elim ∘ ((‘0’ : ArithmeticSemiterm Empty m) :> fun i ↦ #i)) =
      (0 :> e) := by
    funext i; cases i using Fin.cases <;> simp
  have e₁ : (Semiterm.val e Empty.elim ∘ ((‘1’ : ArithmeticSemiterm Empty m) :> fun i ↦ #i)) =
      (1 :> e) := by
    funext i; cases i using Fin.cases <;> simp
  have e₂ : (Semiterm.val (0 :> e) Empty.elim ∘
      ((‘#0 + 1’ : ArithmeticSemiterm Empty (m + 1)) :> fun i ↦ #i.succ)) = (1 :> e) := by
    funext i; cases i using Fin.cases <;> simp
  have h₁ := hs' (0 :> e)
  have h₂ := h₀' e
  rw [e₂] at h₁
  rw [e₀] at h₂
  rw [e₁]
  exact h₁ h₂

private lemma provable_substNumerals_cons_of_provable (φ : ArithmeticSemisentence (m + 1))
    (t : ArithmeticSemiterm Empty m) {a : V}
    (ht : ((⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ m)⌝ : ℕ) : V) = numeral a)
    (h : T ⊢ ∀¹* (Rew.subst (t :> fun i ↦ #i) ▹ φ)) (p : Fin m → V) :
    Provable T (substNumerals ((⌜φ⌝ : ℕ) : V) (a :> p)) := by
  have hw := isSemitermVec_numerals p (0 : V)
  have := provable_substNumerals_of_provable_allClosure _ (provable_natCast_quote_of_provable h) p
  rw [substNumerals, subst_natCast_quote_rew_subst φ _ (u' := numeral a :> fun i ↦ ^#(i : V)) ?_ ?_
    hw, matrixToVec_succ] at this
  · rw [substNumerals_cons]
    simpa [Matrix.vecHead, Matrix.vecTail, Function.comp_def, numeral_substs hw] using this
  · intro i
    cases i using Fin.cases with
    | zero => simpa using ht
    | succ i => simpa using natCast_quote_bvar (V := V) i
  · intro i
    cases i using Fin.cases <;> simp

private lemma substs1_subst_qVec_numerals_imp (φ : ArithmeticSemisentence (m + 1))
    (p : Fin m → V) {y : V} (hy : 0 < y) :
    substs1 ℒₒᵣ (numeral y) (subst ℒₒᵣ (qVec ℒₒᵣ (matrixToVec fun i ↦ numeral (p i)))
      ((⌜φ 🡒 Rew.subst (‘#0 + 1’ :> fun i ↦ #i.succ) ▹ φ⌝ : ℕ) : V)) =
    imp ℒₒᵣ (substNumerals ((⌜φ⌝ : ℕ) : V) (y :> p))
      (substNumerals ((⌜φ⌝ : ℕ) : V) ((y + 1) :> p)) := by
  have hW : IsSemitermVec ℒₒᵣ ((m + 1 : ℕ) : V) 0
      (numeral y ∷ matrixToVec fun i ↦ numeral (p i)) := by
    simpa using (isSemitermVec_numerals p 0).adjoin (numeral_semiterm 0 y)
  rw [substs1_subst_qVec_numerals, substNumerals_cons, substNumerals_cons, substNumerals_cons,
    natCast_quote_imply,
    subst_imp (isSemiformula_natCast_quote φ) (isSemiformula_natCast_quote _) hW,
    subst_natCast_quote_rew_subst φ _ (u' := (^#0 ^+ 𝟏 : V) :> fun i ↦ (^#((i : V) + 1) : V))
      ?_ ?_ hW, matrixToVec_succ, numeral_succ_pos hy]
  · have h₁ : IsUTerm ℒₒᵣ (𝟏 : V) := by simpa using numeral_uterm (1 : V)
    have h₂ : termSubst ℒₒᵣ (numeral y ∷ matrixToVec fun i ↦ numeral (p i)) 𝟏 = 𝟏 := by
      simpa using numeral_substs hW 1
    simp [Matrix.vecHead, Matrix.vecTail, Function.comp_def, termSubst_qqAdd, h₁, h₂]
  · intro i
    cases i using Fin.cases with
    | zero => simpa using natCast_quote_bvar_add_one (V := V) (n := m)
    | succ i => simpa using natCast_quote_bvar (V := V) i.succ
  · intro i
    cases i using Fin.cases
    · simp [qqAdd, qqOne_eq_qqFunc]
    · simp

/-- If `T` proves the base case `∀ p⃗, φ(0, p⃗)` and the induction step
`∀ x p⃗, φ(x, p⃗) 🡒 φ(x + 1, p⃗)`, then every instance of `φ` by numerals is internally provable. -/
theorem provable_substNumerals_of_provable_zero_of_provable_succ [𝗣𝗔⁻ ⪯ T]
    (φ : ArithmeticSemisentence (m + 1)) (h₀ : T ⊢ ∀¹* (Rew.subst (‘0’ :> fun i ↦ #i) ▹ φ))
    (hs : T ⊢ ∀¹* (φ 🡒 Rew.subst (‘#0 + 1’ :> fun i ↦ #i.succ) ▹ φ)) (x : V) (p : Fin m → V) :
    Provable T (Arithmetic.substNumerals (((⌜φ⌝ : ℕ) : ℕ) : V) (x :> p)) := by
  set w : V := matrixToVec fun i ↦ numeral (p i)
  have hW (y : V) : IsSemitermVec ℒₒᵣ ((m + 1 : ℕ) : V) 0 (numeral y ∷ w) := by
    simpa using (isSemitermVec_numerals p 0).adjoin (numeral_semiterm 0 y)
  have hA : LocallyDelta0Function₁ fun y ↦ substNumerals ((⌜φ⌝ : ℕ) : V) (y :> p) := by
    simp only [substNumerals_cons]
    exact subst_locallyDelta0.comp₂ (LocallyDelta0Function.adjoin.comp₂
      (numeral_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)) (LocallyDelta0Function.const w))
      (LocallyDelta0Function.const _)
  rcases zero_or_succ x with rfl | ⟨y, rfl⟩
  · exact provable_substNumerals_cons_of_provable φ _
      ((natCast_quote_numeral 0).trans (by simp)) h₀ p
  obtain ⟨_, hd₁⟩ := provable_substNumerals_cons_of_provable φ _ (a := 1)
    ((natCast_quote_numeral 1).trans (by simp))
    (provable_one_of_provable_zero_of_provable_succ φ h₀ hs) p
  obtain ⟨_, he⟩ := provable_substNumerals_of_provable_allClosure
    (∀¹ (φ 🡒 Rew.subst (‘#0 + 1’ :> fun i ↦ #i.succ) ▹ φ)) (provable_natCast_quote_of_provable hs) p
  rw [substNumerals_natCast_quote_all] at he
  exact provable_succ_of_derivationOf_all hA (isSemiformula_subst_qVec_numerals _ p)
    (fun y ↦ (isSemiformula_natCast_quote φ).subst (hW y)) he hd₁
    (fun _ hy ↦ substs1_subst_qVec_numerals_imp φ p hy) y

end numerals

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
