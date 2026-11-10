module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.Bootstrapping.Interpretability.Value
public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import AlphaCentauri.Bootstrapping.Proof.ExistsElimination
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Iteration
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
public import Foundation.FirstOrder.Incompleteness.Consistency

/-!
# Internal soundness of a translation

The coded set of the translations of a set of formulas along a table, its definability, and its
behaviour under shift and under free-variable substitution. For a set `Γ` of $L_2$-formulas,
`TranslatedDerivable` states that $\Gamma^*$ together with the negated instances of the domain
formula is derivable in `S`, and this property is preserved by each rule of the derivation calculus.

Along a table of a direct translation, the translations of `φ[t]` and of `φ[&b]` are provably
equivalent under the hypotheses `substHyp`, for every formula `φ`. Translated derivability is
closed under the existential rule: for `^∃ p ∈ Γ` and a closed term `t`, the translated
derivability of `Γ` follows from that of `insert (substs1 t p) Γ`. Every set of $L_2$-formulas
derivable in a theory `S'` is translated derivable in `S`, provided the $\Delta_1$ axioms of `S'`
are provable in `S` after translation. Consequently, provability of formula codes is transferred
along a translation, and so is consistency.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Translated sets -/

section translateSets

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

section translateSet

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

variable (L₁ L₂) in
lemma translate_sigmaOne (tbl : V) : 𝚺ᴬ₁-Function₁ (translate L₁ L₂ tbl) := by
  definability

variable (L₁ L₂) in
/-- `translateSet L₁ L₂ tbl s` is the coded set of the translations along `tbl` of the coded
$L_2$-formulas in `s`. -/
noncomputable def translateSet (tbl s : V) : V := by
  letI : 𝚺ᴬ₁-Function₁ (translate L₁ L₂ tbl) := translate_sigmaOne L₁ L₂ tbl
  exact hfsImage (translate L₁ L₂ tbl) s

variable (L₁ L₂) in
/-- The $\Sigma_1$ graph of `translateSet`; argument order `(t, tbl, s)`,
`t = translateSet tbl s`. -/
noncomputable def translateSetGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “t tbl s. (∀ z ∈' t, ∃ p ∈' s, !(translateGraph L₁ L₂) z tbl p) ∧
    (∀ p ∈' s, ∃ z, !(translateGraph L₁ L₂) z tbl p ∧ z ∈ t)”

@[simp] lemma mem_translateSet_iff {tbl s x : V} :
    x ∈ translateSet L₁ L₂ tbl s ↔ ∃ p ∈ s, x = translate L₁ L₂ tbl p := by
  let _ : 𝚺ᴬ₁-Function₁ (translate L₁ L₂ tbl) := translate_sigmaOne L₁ L₂ tbl
  exact mem_hfsImage_iff

section graph

variable {Γ : SigmaPiDelta} {m : ℕ}

private lemma translateSet_graph (t tbl s : V) :
    t = translateSet L₁ L₂ tbl s ↔ (∀ z ∈ t, ∃ p ∈ s, z = translate L₁ L₂ tbl p) ∧
      (∀ p ∈ s, translate L₁ L₂ tbl p ∈ t) := by
  constructor
  · rintro rfl
    simp only [mem_translateSet_iff, forall_exists_index, and_imp]
    exact ⟨by grind, fun p hp ↦ ⟨p, hp, rfl⟩⟩
  · rintro ⟨h₁, h₂⟩
    apply mem_ext
    intro y
    simp only [mem_translateSet_iff]
    grind

instance translateSet.defined : 𝚺ᴬ₁-Function₂[V] translateSet L₁ L₂ via translateSetGraph L₁ L₂ :=
  .mk fun v ↦ by simp [translateSetGraph, translateSet_graph]

instance translateSet.definable : 𝚺ᴬ₁-Function₂[V] translateSet L₁ L₂ :=
  translateSet.defined.to_definable

instance translateSet.definable' : Γᴬ_[m + 1]-Function₂[V] translateSet L₁ L₂ :=
  translateSet.definable.of_sigmaOne

end graph

@[simp] lemma translateSet_empty (tbl : V) : translateSet L₁ L₂ tbl ∅ = ∅ := by
  let _ := translate_sigmaOne L₁ L₂ tbl
  exact hfsImage_empty

@[simp] lemma translateSet_insert (tbl p s : V) :
    translateSet L₁ L₂ tbl (insert p s) =
      insert (translate L₁ L₂ tbl p) (translateSet L₁ L₂ tbl s) := by
  let _ := translate_sigmaOne L₁ L₂ tbl
  exact mem_hfsImage_insert

lemma translateSet_mono {tbl s s' : V} (h : s ⊆ s') :
    translateSet L₁ L₂ tbl s ⊆ translateSet L₁ L₂ tbl s' := by
  let _ := translate_sigmaOne L₁ L₂ tbl
  exact hfsImage_subset_of_subset h

lemma IsFormulaSet.translateSet {tbl s : V} (hT : IsTable L₁ L₂ tbl) (hs : IsFormulaSet L₂ s) :
    IsFormulaSet L₁ (Bootstrapping.translateSet L₁ L₂ tbl s) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := mem_translateSet_iff.mp hp
  exact IsSemiformula.translate hT (hs q hq)

lemma translateSet_setShift {tbl s : V} (hT : IsTable L₁ L₂ tbl) (hs : IsFormulaSet L₂ s) :
    translateSet L₁ L₂ tbl (setShift L₂ s) = setShift L₁ (translateSet L₁ L₂ tbl s) := by
  apply mem_ext
  intro x
  simp only [mem_translateSet_iff, mem_setShift_iff]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨translate L₁ L₂ tbl q, ⟨q, hq, rfl⟩, translate_shift hT (hs q hq)⟩
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨shift L₂ q, ⟨q, hq, rfl⟩, (translate_shift hT (hs q hq)).symm⟩

lemma freshVec_fvar (j : V) : ∀ i < len (freshVec j : V), ∃ x, (freshVec j : V).[i] = ^&x := by
  intro i hi
  rw [len_freshVec] at hi
  rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with h' | rfl
  · exact ⟨i + 1, nth_freshVec_of_lt h'⟩
  · exact ⟨0, by simp⟩

lemma fvSubstImage_freshVec_translateSet_of {tbl Γ j : V} (hT : IsTable L₁ L₂ tbl)
    (hΓ : IsFormulaSet L₂ Γ) (h : ∀ q ∈ Γ, fvSubst L₂ (freshVec j) q = shift L₂ q) :
    fvSubstImage (L := L₁) (freshVec j) (translateSet L₁ L₂ tbl Γ) =
      setShift L₁ (translateSet L₁ L₂ tbl Γ) := by
  have key : ∀ p ∈ Γ, fvSubst L₁ (freshVec j) (translate L₁ L₂ tbl p) =
      shift L₁ (translate L₁ L₂ tbl p) := by
    intro p hp
    rw [← translate_fvSubst hT (freshVec_fvar j) (hΓ p hp), h p hp, translate_shift hT (hΓ p hp)]
  refine mem_ext fun x ↦ ?_
  simp only [mem_fvSubstImage_iff, mem_translateSet_iff, mem_setShift_iff]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, key p hp⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, (key p hp).symm⟩

end translateSet

end translateSets

/-! ## The rules of derivations -/

section rules

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open PeanoMinus ISigma0 ISigma1

section definition

variable {L₁ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
variable (S : Theory L₁) [S.Δ₁]
variable (L₂ : Language) [L₂.Encodable] [L₂.LORDefinable]
variable (tbl Γ : V)

/-- $\Gamma^* \cup D_\Gamma$ is derivable in `S`.

- [Lin97, Fact 12]
-/
def TranslatedDerivable : Prop :=
  Derivable S (translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ)

instance : 𝚺ᴬ₁-Predicate (TranslatedDerivable S L₂ tbl) := by
  unfold TranslatedDerivable
  definability

end definition

section generic

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma free_imp {δ q : V} (hδ : IsSemiformula L 1 δ) (hds : shift L δ = δ)
    (hq : IsSemiformula L 1 q) :
    free L (imp L δ q) = neg L (substs1 L (^&0) δ) ^⋎ free L q := by
  have hw : IsSemitermVec L 1 0 (?[^&0] : V) := IsSemitermVec.singleton.mpr (IsSemiterm.fvar _ _)
  rw [free, shift_imp hδ hq, hds, substs1, subst_imp hw hδ hq.shift]
  rfl

end generic

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] {S : Theory L₁} [S.Δ₁] {tbl : V}

lemma isFormulaSet_translated_union {Γ : V} (hT : IsTable L₁ L₂ tbl) (hΓ : IsFormulaSet L₂ Γ)
    (M : V) : IsFormulaSet L₁ (translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] M) :=
  IsFormulaSet.union.mpr ⟨IsFormulaSet.translateSet hT hΓ, IsFormulaSet.negDomSet hT.domain M⟩

lemma translateSet_insert_cup (p s t : V) :
    translateSet L₁ L₂ tbl (insert p s) ∪ t =
      insert (translate L₁ L₂ tbl p) (translateSet L₁ L₂ tbl s ∪ t) := by
  apply mem_ext
  intro x
  simp; grind

lemma domainAt_zero (hT : IsTable L₁ L₂ tbl) : domainAt L₁ tbl 0 = tbl.[0] := by
  unfold domainAt
  have hw : IsUTermVec L₁ (1 : V) ?[^#0] :=
    (IsSemitermVec.singleton.mpr (IsSemiterm.bvar.mpr (show (0 : V) < 1 by simp))).isUTerm
  have H : ∀ i < (1 : V), (?[^#0] : V).[i] = ^#i := by
    intro i hi
    obtain rfl : i = 0 := by simpa using hi
    simp
  exact subst_eq_self_of_le hT.domain hw (le_refl _) H

lemma translate_free (hT : IsTable L₁ L₂ tbl) {p : V} (hp : IsSemiformula L₂ 1 p) :
    translate L₁ L₂ tbl (free L₂ p) = free L₁ (translate L₁ L₂ tbl p) := by
  simp only [free]
  rw [translate_substs1_fvar hT 0 hp.shift, translate_shift hT hp]

lemma elim_translateSet (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (hT : IsTable L₁ L₂ tbl) (hdom : Provable S (^∃ tbl.[0])) {Γ₁ m M : V}
    (hΓ₁ : IsFormulaSet L₂ Γ₁) (hm : m ≤ M)
    (hfresh : ∀ j, m ≤ j → j < M → ∀ q ∈ Γ₁, fvSubst L₂ (freshVec j) q = shift L₂ q)
    (hd : Derivable S (translateSet L₁ L₂ tbl Γ₁ ∪ negDomSet L₁ tbl.[0] M)) :
    Derivable S (translateSet L₁ L₂ tbl Γ₁ ∪ negDomSet L₁ tbl.[0] m) :=
  Derivable.elim_negDomSet hS hT.domain hT.domain_shift hdom
    (IsFormulaSet.translateSet hT hΓ₁) hm
    (fun j hmj hjM ↦ fvSubstImage_freshVec_translateSet_of hT hΓ₁ (hfresh j hmj hjM)) hd

lemma translated_of_le (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (hT : IsTable L₁ L₂ tbl) (hdom : Provable S (^∃ tbl.[0])) {Γ M : V} (hΓ : IsFormulaSet L₂ Γ)
    (hM : Γ ≤ M)
    (hd : Derivable S (translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] M)) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hfresh : ∀ j, Γ ≤ j → j < M → ∀ q ∈ Γ, fvSubst L₂ (freshVec j) q = shift L₂ q := by
    intro j hΓj _ q hq
    have hu : j < len (freshVec j : V) := by
      rw [len_freshVec]
      exact lt_add_one j
    exact fvSubst_eq_shift hu (fun x hx ↦ nth_freshVec_of_lt hx) (hΓ q hq)
      (le_trans (lt_of_mem hq).le hΓj)
  exact elim_translateSet hS hT hdom hΓ hM hfresh hd

lemma derivable_translated_bound (hT : IsTable L₁ L₂ tbl) {Γ M : V}
    (hΓ : IsFormulaSet L₂ Γ) (hM : Γ ≤ M) (hd : TranslatedDerivable S L₂ tbl Γ) :
    Derivable S (translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] M) := by
  unfold TranslatedDerivable at hd
  have hU : translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ ⊆
      translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] M := by
    intro x hx
    exact mem_cup_iff.mpr ((mem_cup_iff.mp hx).imp id (negDomSet_mono hM ·))
  exact Derivable.wk (isFormulaSet_translated_union hT hΓ M) hU hd

lemma translated_insert (hT : IsTable L₁ L₂ tbl) {p Γ M : V}
    (hp : IsFormula L₂ p) (hΓ : IsFormulaSet L₂ Γ) (hM : insert p Γ ≤ M)
    (hd : TranslatedDerivable S L₂ tbl (insert p Γ)) :
    Derivable S
      (insert (translate L₁ L₂ tbl p) (translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] M)) := by
  have hw := derivable_translated_bound hT (IsFormulaSet.insert_iff.mpr ⟨hp, hΓ⟩) hM hd
  rw [translateSet_insert_cup] at hw
  exact hw

lemma translated_em (hT : IsTable L₁ L₂ tbl) {Γ p : V}
    (hΓ : IsFormulaSet L₂ Γ) (hp : p ∈ Γ) (hnp : neg L₂ p ∈ Γ) :
    TranslatedDerivable S L₂ tbl Γ := by
  unfold TranslatedDerivable
  have hp' : translate L₁ L₂ tbl p ∈ translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ :=
    by simp; grind
  have hn : translate L₁ L₂ tbl (neg L₂ p) ∈ translateSet L₁ L₂ tbl Γ := by simp; grind
  rw [translate_neg hT (hΓ p hp)] at hn
  exact Derivable.em (isFormulaSet_translated_union hT hΓ Γ) _ hp'
    (mem_cup_iff.mpr (Or.inl hn))

lemma translated_verum (hT : IsTable L₁ L₂ tbl) {Γ : V}
    (hΓ : IsFormulaSet L₂ Γ) (hv : ^⊤ ∈ Γ) :
    TranslatedDerivable S L₂ tbl Γ := by
  unfold TranslatedDerivable
  have hv' : ^⊤ ∈ translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ :=
    by simp; grind [translate_verum]
  exact Derivable.verum (isFormulaSet_translated_union hT hΓ Γ) hv'

lemma translated_axm (hT : IsTable L₁ L₂ tbl) {Γ p : V}
    (hΓ : IsFormulaSet L₂ Γ) (hp : p ∈ Γ) (hax : Provable S (translate L₁ L₂ tbl p)) :
    TranslatedDerivable S L₂ tbl Γ := by
  unfold TranslatedDerivable
  exact Derivable.wk (isFormulaSet_translated_union hT hΓ Γ)
    (by intro x hx; simp at hx ⊢; grind) hax.toDerivable

lemma translated_and (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (hT : IsTable L₁ L₂ tbl) (hdom : Provable S (^∃ tbl.[0])) {Γ p q : V}
    (hΓ : IsFormulaSet L₂ Γ) (hpq : p ^⋏ q ∈ Γ)
    (h₁ : TranslatedDerivable S L₂ tbl (insert p Γ))
    (h₂ : TranslatedDerivable S L₂ tbl (insert q Γ)) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hpq' := hΓ _ hpq
  have hp : IsFormula L₂ p := (IsSemiformula.and.mp hpq').1
  have hq : IsFormula L₂ q := (IsSemiformula.and.mp hpq').2
  have hpM : insert p Γ ≤ insert p Γ + insert q Γ + Γ := le_add_right (le_add_right le_rfl)
  have hqM : insert q Γ ≤ insert p Γ + insert q Γ + Γ := le_add_right (le_add_left le_rfl)
  have hΓM : Γ ≤ insert p Γ + insert q Γ + Γ := le_add_left le_rfl
  have d₁ := translated_insert hT hp hΓ hpM h₁
  have d₂ := translated_insert hT hq hΓ hqM h₂
  have hmem : translate L₁ L₂ tbl (p ^⋏ q) ∈
      translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] (insert p Γ + insert q Γ + Γ) :=
    by simp; grind
  rw [translate_and (IsSemiformula.isUFormula hp) (IsSemiformula.isUFormula hq)] at hmem
  exact translated_of_le hS hT hdom hΓ hΓM (Derivable.and_m hmem d₁ d₂)

lemma translated_or (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (hT : IsTable L₁ L₂ tbl) (hdom : Provable S (^∃ tbl.[0])) {Γ p q : V}
    (hΓ : IsFormulaSet L₂ Γ) (hpq : p ^⋎ q ∈ Γ)
    (hd : TranslatedDerivable S L₂ tbl (insert p (insert q Γ))) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hpq' := hΓ _ hpq
  have hp : IsFormula L₂ p := (IsSemiformula.or.mp hpq').1
  have hq : IsFormula L₂ q := (IsSemiformula.or.mp hpq').2
  have hM : insert p (insert q Γ) ≤ insert p (insert q Γ) + Γ := le_add_right le_rfl
  have hΓM : Γ ≤ insert p (insert q Γ) + Γ := le_add_left le_rfl
  have hd' := derivable_translated_bound hT
    (IsFormulaSet.insert_iff.mpr ⟨hp, IsFormulaSet.insert_iff.mpr ⟨hq, hΓ⟩⟩) hM hd
  rw [translateSet_insert_cup, translateSet_insert_cup] at hd'
  have hmem : translate L₁ L₂ tbl p ^⋎ translate L₁ L₂ tbl q ∈
      translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] (insert p (insert q Γ) + Γ) := by
    rw [← translate_or (IsSemiformula.isUFormula hp) (IsSemiformula.isUFormula hq)]
    simp; grind
  exact translated_of_le hS hT hdom hΓ hΓM (Derivable.or_m hmem hd')

lemma translated_cut (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (hT : IsTable L₁ L₂ tbl) (hdom : Provable S (^∃ tbl.[0])) {Γ p : V}
    (hΓ : IsFormulaSet L₂ Γ) (hp : IsFormula L₂ p)
    (h₁ : TranslatedDerivable S L₂ tbl (insert p Γ))
    (h₂ : TranslatedDerivable S L₂ tbl (insert (neg L₂ p) Γ)) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hnp : IsFormula L₂ (neg L₂ p) := IsSemiformula.neg hp
  have hpM : insert p Γ ≤ insert p Γ + insert (neg L₂ p) Γ + Γ :=
    le_add_right (le_add_right le_rfl)
  have hnpM : insert (neg L₂ p) Γ ≤ insert p Γ + insert (neg L₂ p) Γ + Γ :=
    le_add_right (le_add_left le_rfl)
  have hΓM : Γ ≤ insert p Γ + insert (neg L₂ p) Γ + Γ := le_add_left le_rfl
  have d₁ := translated_insert hT hp hΓ hpM h₁
  have d₂ := translated_insert hT hnp hΓ hnpM h₂
  rw [translate_neg hT hp] at d₂
  exact translated_of_le hS hT hdom hΓ hΓM (Derivable.cut (translate L₁ L₂ tbl p) d₁ d₂)

lemma translated_wk (hT : IsTable L₁ L₂ tbl) {Γ Γ' : V}
    (hΓ' : IsFormulaSet L₂ Γ') (hsub : Γ ⊆ Γ')
    (hd : TranslatedDerivable S L₂ tbl Γ) :
    TranslatedDerivable S L₂ tbl Γ' := by
  unfold TranslatedDerivable at hd ⊢
  have hU : translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ ⊆
      translateSet L₁ L₂ tbl Γ' ∪ negDomSet L₁ tbl.[0] Γ' := by
    intro x hx
    exact mem_cup_iff.mpr
      ((mem_cup_iff.mp hx).imp (translateSet_mono hsub ·) (negDomSet_mono (le_of_subset hsub) ·))
  exact Derivable.wk (isFormulaSet_translated_union hT hΓ' Γ') hU hd

lemma translated_shift (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (hT : IsTable L₁ L₂ tbl) (hdom : Provable S (^∃ tbl.[0])) {Γ : V}
    (hΓ : IsFormulaSet L₂ Γ) (hd : TranslatedDerivable S L₂ tbl Γ) :
    TranslatedDerivable S L₂ tbl (setShift L₂ Γ) := by
  have hΓs : IsFormulaSet L₂ (setShift L₂ Γ) := IsFormulaSet.setShift hΓ
  have hM : setShift L₂ Γ ≤ Γ + setShift L₂ Γ + 1 := le_add_right (le_add_left le_rfl)
  unfold TranslatedDerivable at hd ⊢
  have hU : setShift L₁ (translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ) ⊆
      translateSet L₁ L₂ tbl (setShift L₂ Γ) ∪ negDomSet L₁ tbl.[0] (Γ + setShift L₂ Γ + 1) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_setShift_iff.mp hx
    rcases mem_cup_iff.mp hy with hy | hy
    · obtain ⟨q, hq, rfl⟩ := mem_translateSet_iff.mp hy
      exact mem_cup_iff.mpr (Or.inl (mem_translateSet_iff.mpr
        ⟨shift L₂ q, mem_setShift_iff.mpr ⟨q, hq, rfl⟩, (translate_shift hT (hΓ q hq)).symm⟩))
    · obtain ⟨i, hi, rfl⟩ := mem_negDomSet_iff.mp hy
      have hi' : i + 1 < Γ + setShift L₂ Γ + 1 :=
        lt_of_le_of_lt (le_trans (lt_iff_succ_le.mp hi) (le_add_right le_rfl)) (lt_add_one _)
      exact mem_cup_iff.mpr (Or.inr (mem_negDomSet_iff.mpr
        ⟨i + 1, hi', shift_neg_substs1_qqFvar hT.domain hT.domain_shift⟩))
  have hd' : Derivable S
      (translateSet L₁ L₂ tbl (setShift L₂ Γ) ∪ negDomSet L₁ tbl.[0] (Γ + setShift L₂ Γ + 1)) :=
    Derivable.wk (isFormulaSet_translated_union hT hΓs _) hU (Derivable.shift hd)
  exact translated_of_le hS hT hdom hΓs hM hd'

lemma translated_all (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (hT : IsTable L₁ L₂ tbl) (hdom : Provable S (^∃ tbl.[0])) {Γ p : V}
    (hΓ : IsFormulaSet L₂ Γ) (hp : ^∀ p ∈ Γ)
    (hd : TranslatedDerivable S L₂ tbl (insert (free L₂ p) (setShift L₂ Γ))) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hpΓ : p ≤ Γ := le_trans (le_qqAll p) (lt_of_mem hp).le
  have hp1 : IsSemiformula L₂ 1 p := by simpa using IsSemiformula.all.mp (hΓ _ hp)
  have hΓ₁ : IsFormulaSet L₂ (insert (free L₂ p) (setShift L₂ Γ)) :=
    IsFormulaSet.insert_iff.mpr ⟨IsSemiformula.free hp1, IsFormulaSet.setShift hΓ⟩
  have hM₁ : insert (free L₂ p) (setShift L₂ Γ) ≤
      insert (free L₂ p) (setShift L₂ Γ) + (Γ + 1) := le_add_right le_rfl
  have hΓM : Γ + 1 ≤ insert (free L₂ p) (setShift L₂ Γ) + (Γ + 1) := le_add_left le_rfl
  have hfresh : ∀ j, Γ + 1 ≤ j → j < insert (free L₂ p) (setShift L₂ Γ) + (Γ + 1) →
      ∀ q ∈ insert (free L₂ p) (setShift L₂ Γ), fvSubst L₂ (freshVec j) q = shift L₂ q := by
    intro j hj _ q hq
    have hΓj : Γ < j := lt_of_lt_of_le (lt_add_one Γ) hj
    rcases mem_bitInsert_iff.mp hq with rfl | hq
    · exact fvSubst_freshVec_free hp1 hpΓ hΓj
    · obtain ⟨ψ, hψ, rfl⟩ := mem_setShift_iff.mp hq
      exact fvSubst_freshVec_shift (hΓ ψ hψ) (lt_of_mem hψ).le hΓj
  have hd' := derivable_translated_bound hT hΓ₁ hM₁ hd
  have hd'' := elim_translateSet hS hT hdom hΓ₁ hΓM hfresh hd'
  rw [translateSet_insert, translate_free hT hp1, translateSet_setShift hT hΓ,
    negDomSet_succ_eq_insert_setShift (d := tbl.[0]) hT.domain hT.domain_shift Γ] at hd''
  have hd3 : Derivable S (insert (neg L₁ (substs1 L₁ (^&0) tbl.[0]))
      (insert (free L₁ (translate L₁ L₂ tbl p))
        (setShift L₁ (translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ)))) :=
    Derivable.ofSetEq
      (fun x ↦ by simp only [mem_setShift_union, mem_cup_iff, mem_bitInsert_iff]; tauto) hd''
  obtain ⟨hnd, hF₂⟩ := IsFormulaSet.insert_iff.mp hd3.isFormulaSet
  obtain ⟨htf, hs⟩ := IsFormulaSet.insert_iff.mp hF₂
  have hX := derivable_insert_or hs hnd htf hd3
  have hmem : ^∀ imp L₁ tbl.[0] (translate L₁ L₂ tbl p) ∈ translateSet L₁ L₂ tbl Γ := by
    have h₁ : translate L₁ L₂ tbl (^∀ p) ∈ translateSet L₁ L₂ tbl Γ :=
      by simp; grind
    rw [translate_all (IsSemiformula.isUFormula hp1), domainAt_zero hT] at h₁
    exact h₁
  have hfree : free L₁ (imp L₁ tbl.[0] (translate L₁ L₂ tbl p)) =
      neg L₁ (substs1 L₁ (^&0) tbl.[0]) ^⋎ free L₁ (translate L₁ L₂ tbl p) :=
    free_imp hT.domain hT.domain_shift (IsSemiformula.translate hT hp1)
  have hp' : Derivable S (insert (free L₁ (imp L₁ tbl.[0] (translate L₁ L₂ tbl p)))
      (setShift L₁ (translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ))) := by
    rw [hfree]
    exact hX
  unfold TranslatedDerivable
  exact Derivable.all_m (mem_cup_iff.mpr (Or.inl hmem)) hp'

end rules

/-! ## Substitution of a closed term into translated formulas -/

section formSubst

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

section defs

variable (L₁ L₂ : Language) [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

/-- The code of the equivalence between the translations of `φ[t]` and `φ[&b]`. -/
noncomputable def translateSubstEquiv (tbl t b p : V) : V :=
  iff L₁ (translate L₁ L₂ tbl (substs1 L₂ t p)) (translate L₁ L₂ tbl (substs1 L₂ (^&b) p))

instance translateSubstEquiv.definable : 𝚺ᴬ₁-Function₄[V] translateSubstEquiv L₁ L₂ := by
  definability

/-- The fresh free variable of the quantifier case, bounding the codes of `substHyp` and of the
equivalence of the translated matrices. It has no counterpart in the literature. -/
noncomputable def quantFresh (tbl t b x : V) : V :=
  max (substHyp L₁ L₂ tbl t b) (iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#0, t] (π₂ (x - 1))))
    (translate L₁ L₂ tbl (subst L₂ ?[^#0, ^&b] (π₂ (x - 1)))))

instance quantFresh.definable : 𝚺ᴬ₁-Function₄[V] quantFresh L₁ L₂ := by
  definability

end defs

section value

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S] {tbl : V}

omit [L₂.Eq] in
lemma translate_substs1_all {t q : V} (ht : IsSemiterm L₂ 0 t)
    (hq : IsSemiformula L₂ 2 q) :
    translate L₁ L₂ tbl (substs1 L₂ t (^∀ q)) =
      ^∀ imp L₁ (domainAt L₁ tbl 0) (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q)) := by
  have h₁ : IsSemitermVec L₂ 2 1 (?[^#(0 : V), t] : V) := by simp [IsSemiterm.of_zero ht]
  unfold substs1
  rw [substs_all hq.isUFormula, qVec_closed ht, translate_all (hq.subst h₁).isUFormula]

omit [L₂.Eq] in
lemma translate_substs1_exs {t q : V} (ht : IsSemiterm L₂ 0 t)
    (hq : IsSemiformula L₂ 2 q) :
    translate L₁ L₂ tbl (substs1 L₂ t (^∃ q)) =
      ^∃ (domainAt L₁ tbl 0 ^⋏ translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q)) := by
  have h₁ : IsSemitermVec L₂ 2 1 (?[^#(0 : V), t] : V) := by simp [IsSemiterm.of_zero ht]
  unfold substs1
  rw [substs_ex hq.isUFormula, qVec_closed ht, translate_exs (hq.subst h₁).isUFormula]

omit [L₁.Eq] [𝗘𝗤 L₁ ⪯ S] in
lemma derivable_all_iff_V {δ θ₁ θ₂ s : V} (hδ : IsSemiformula L₁ 1 δ)
    (hθ₁ : IsSemiformula L₁ 1 θ₁) (hθ₂ : IsSemiformula L₁ 1 θ₂)
    (h : Derivable S (insert (^∀ (iff L₁ θ₁ θ₂)) s)) :
    Derivable S (insert (iff L₁ (^∀ imp L₁ δ θ₁) (^∀ imp L₁ δ θ₂)) s) := by
  have h₁ : Derivable S (insert (∀¹ ((⟨θ₁, by simpa using hθ₁⟩ : Semiformula V L₁ 1) 🡘
      ⟨θ₂, by simpa using hθ₂⟩)).val s) := by
    simpa only [Semiformula.val_all, Semiformula.val_iff] using h
  have h₂ := Derivable.of_tprovable_imp
    (tprovable_all_iff_all_domain (T := S) ⟨δ, by simpa using hδ⟩
      ⟨θ₁, by simpa using hθ₁⟩ ⟨θ₂, by simpa using hθ₂⟩) h₁
  simpa only [Semiformula.val_all, Semiformula.val_iff, Semiformula.val_imp] using h₂

omit [L₁.Eq] [𝗘𝗤 L₁ ⪯ S] in
lemma derivable_exs_iff_V {δ θ₁ θ₂ s : V} (hδ : IsSemiformula L₁ 1 δ)
    (hθ₁ : IsSemiformula L₁ 1 θ₁) (hθ₂ : IsSemiformula L₁ 1 θ₂)
    (h : Derivable S (insert (^∀ (iff L₁ θ₁ θ₂)) s)) :
    Derivable S (insert (iff L₁ (^∃ (δ ^⋏ θ₁)) (^∃ (δ ^⋏ θ₂))) s) := by
  have h₁ : Derivable S (insert (∀¹ ((⟨θ₁, by simpa using hθ₁⟩ : Semiformula V L₁ 1) 🡘
      ⟨θ₂, by simpa using hθ₂⟩)).val s) := by
    simpa only [Semiformula.val_all, Semiformula.val_iff] using h
  have h₂ := Derivable.of_tprovable_imp
    (tprovable_all_iff_exs_domain (T := S) ⟨δ, by simpa using hδ⟩
      ⟨θ₁, by simpa using hθ₁⟩ ⟨θ₂, by simpa using hθ₂⟩) h₁
  simpa only [Semiformula.val_exs, Semiformula.val_iff, Semiformula.val_and] using h₂

omit [L₁.Eq] [𝗘𝗤 L₁ ⪯ S] in
lemma derivable_iff_and_V {X X' Y Y' s : V} (hX : IsSemiformula L₁ 0 X)
    (hX' : IsSemiformula L₁ 0 X') (hY : IsSemiformula L₁ 0 Y) (hY' : IsSemiformula L₁ 0 Y')
    (h₁ : Derivable S (insert (iff L₁ X X') s))
    (h₂ : Derivable S (insert (iff L₁ Y Y') s)) :
    Derivable S (insert (iff L₁ (X ^⋏ Y) (X' ^⋏ Y')) s) := by
  have h₃ : Derivable S (insert ((⟨X, hX⟩ : Formula V L₁) 🡘 ⟨X', hX'⟩).val s) := by
    simpa only [Semiformula.val_iff] using h₁
  have h₄ : Derivable S (insert ((⟨Y, hY⟩ : Formula V L₁) 🡘 ⟨Y', hY'⟩).val s) := by
    simpa only [Semiformula.val_iff] using h₂
  have h₅ : Derivable S (insert
      (((⟨X, hX⟩ : Formula V L₁) ⋏ ⟨Y, hY⟩) 🡘 ((⟨X', hX'⟩ : Formula V L₁) ⋏ ⟨Y', hY'⟩)).val s) :=
    Derivable.of_tprovable_imp₂ (by cl_prover) h₃ h₄
  simpa only [Semiformula.val_and, Semiformula.val_iff] using h₅

omit [L₁.Eq] [𝗘𝗤 L₁ ⪯ S] in
lemma derivable_iff_or_V {X X' Y Y' s : V} (hX : IsSemiformula L₁ 0 X)
    (hX' : IsSemiformula L₁ 0 X') (hY : IsSemiformula L₁ 0 Y) (hY' : IsSemiformula L₁ 0 Y')
    (h₁ : Derivable S (insert (iff L₁ X X') s))
    (h₂ : Derivable S (insert (iff L₁ Y Y') s)) :
    Derivable S (insert (iff L₁ (X ^⋎ Y) (X' ^⋎ Y')) s) := by
  have h₃ : Derivable S (insert ((⟨X, hX⟩ : Formula V L₁) 🡘 ⟨X', hX'⟩).val s) := by
    simpa only [Semiformula.val_iff] using h₁
  have h₄ : Derivable S (insert ((⟨Y, hY⟩ : Formula V L₁) 🡘 ⟨Y', hY'⟩).val s) := by
    simpa only [Semiformula.val_iff] using h₂
  have h₅ : Derivable S (insert
      (((⟨X, hX⟩ : Formula V L₁) ⋎ ⟨Y, hY⟩) 🡘 ((⟨X', hX'⟩ : Formula V L₁) ⋎ ⟨Y', hY'⟩)).val s) :=
    Derivable.of_tprovable_imp₂ (by cl_prover) h₃ h₄
  simpa only [Semiformula.val_or, Semiformula.val_iff] using h₅

omit [L₁.Eq] [𝗘𝗤 L₁ ⪯ S] in
lemma derivable_iff_neg_V {X X' s : V} (hX : IsSemiformula L₁ 0 X)
    (hX' : IsSemiformula L₁ 0 X') (h : Derivable S (insert (iff L₁ X X') s)) :
    Derivable S (insert (iff L₁ (neg L₁ X) (neg L₁ X')) s) := by
  have h₁ : Derivable S (insert ((⟨X, hX⟩ : Formula V L₁) 🡘 ⟨X', hX'⟩).val s) := by
    simpa only [Semiformula.val_iff] using h
  have h₂ : Derivable S (insert
      ((∼(⟨X, hX⟩ : Formula V L₁)) 🡘 ∼(⟨X', hX'⟩ : Formula V L₁)).val s) :=
    Derivable.of_tprovable_imp (by cl_prover) h₁
  simpa only [Semiformula.val_neg, Semiformula.val_iff] using h₂

omit [L₂.Eq] in
lemma translate_substs1_nrel {t k R v : V} (ht : IsSemiterm L₂ 0 t)
    (hR : L₂.IsRel k R) (hv : IsSemitermVec L₂ k 1 v) :
    translate L₁ L₂ tbl (substs1 L₂ t (^nrel k R v)) =
      neg L₁ (translate L₁ L₂ tbl (substs1 L₂ t (^rel k R v))) := by
  have hw : IsSemitermVec L₂ 1 0 (?[t] : V) := by simp [ht]
  unfold substs1
  rw [substs_nrel hR hv.isUTerm, substs_rel hR hv.isUTerm,
    translate_nrel hR (hw.termSubstVec hv).isUTerm, translate_rel hR (hw.termSubstVec hv).isUTerm]

omit [L₂.Eq] in
lemma substs_rel_val {k : ℕ} (R : L₂.Rel k) {c v : V} (hc : IsSemiterm L₂ 0 c)
    (hv : IsSemitermVec L₂ (k : V) 1 v) :
    ∃ u : Fin k → Term V L₂, (∀ i : Fin k, (u i).val = termSubst L₂ ?[c] v.[(i : ℕ)]) ∧
      subst L₂ ?[c] (^rel (k : V) ⌜R⌝ v) = (Semiformula.rel R u).val := by
  have hw : IsSemitermVec L₂ (1 : V) 0 ?[c] := by simp [hc]
  obtain ⟨u, hu⟩ := exists_termVec (IsSemitermVec.termSubstVec hw hv)
  refine ⟨u, fun i ↦ ?_, ?_⟩
  · rw [← nth_termSubstVec hv.isUTerm (by simp), ← hu]
    simp
  · rw [substs_rel (codeIn_rel_quote R) hv.isUTerm, Semiformula.rel_val, hu]

lemma derivable_iff_translate_rel (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {t b : V}
    (ht : IsSemiterm L₂ 0 t)
    {k : ℕ} (R : L₂.Rel k) {v : V} (hv : IsSemitermVec L₂ (k : V) 1 v) :
    Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b (^rel (k : V) ⌜R⌝ v))
      (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.toIsTable
  have hH := isFormulaSet_substHyp hT ht b
  obtain ⟨u₁, hu₁, hf₁⟩ := substs_rel_val R ht hv
  obtain ⟨u₂, hu₂, hf₂⟩ := substs_rel_val R (c := ^&b) (by simp) hv
  unfold translateSubstEquiv substs1
  rw [hf₁, hf₂, translate_rel_typed hT R u₁, translate_rel_typed hT R u₂]
  have hΦ (i : Fin k) : Derivable S (insert (∀¹ (h.domT 🡒
      (varEqualT hT (u₁ i) 🡘 varEqualT hT (u₂ i)))).val (substHyp L₁ L₂ tbl t b)) := by
    rw [← termSubstEquiv_eq_typed h (hu₁ i) (hu₂ i)]
    exact derivable_termSubstEquiv hS h hL₂ ht (hv.nth (by simp))
  have hc := Derivable.conj_typed hH hΦ
  let C : Semiformula V L₁ (0 + k) :=
    (h.relT R).subst (fun i ↦ Semiterm.bvar (i.addCast 0))
  have hg := Derivable.of_tprovable_imp
    (relativizedImp_congr (T := S) h.domT (fun i ↦ varEqualT hT (u₁ i))
      (fun i ↦ varEqualT hT (u₂ i)) C) hc
  simpa only [Semiformula.val_iff] using hg

omit [L₂.Eq] in
lemma isSemiformula_translate_subst (hT : IsTable L₁ L₂ tbl) {t q : V} (ht : IsSemiterm L₂ 0 t)
    (hq : IsSemiformula L₂ 2 q) :
    IsSemiformula L₁ 1 (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q)) :=
  have h : IsSemitermVec L₂ 2 1 (?[^#(0 : V), t] : V) := by simp [IsSemiterm.of_zero ht]
  IsSemiformula.translate hT (hq.subst h)

omit [𝗘𝗤 _ ⪯ S] [L₂.Eq] in
lemma derivable_all_of_quantFresh (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (hT : IsTable L₁ L₂ tbl) {t b q x : V} (ht : IsSemiterm L₂ 0 t) (hq : IsSemiformula L₂ 2 q)
    (hx : π₂(x - 1) = q)
    (ih : Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b
      (subst L₂ ?[^&(quantFresh L₁ L₂ tbl t b x), ^#(0 : V)] q)) (substHyp L₁ L₂ tbl t b))) :
    Derivable S (insert (^∀ iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q))
      (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q))) (substHyp L₁ L₂ tbl t b)) := by
  have hb : IsSemiterm L₂ 0 (^&b) := by simp
  have hA₁ := isSemiformula_translate_subst (tbl := tbl) (L₁ := L₁) hT ht hq
  have hA₂ := isSemiformula_translate_subst (tbl := tbl) (L₁ := L₁) hT hb hq
  unfold translateSubstEquiv at ih
  have hθ₁ : IsSemiformula L₂ 1 (subst L₂ ?[^#(0 : V), t] q) :=
    hq.subst (by simp [IsSemiterm.of_zero ht])
  have hθ₂ : IsSemiformula L₂ 1 (subst L₂ ?[^#(0 : V), ^&b] q) := hq.subst (by simp)
  rw [substs1_subst_fvar_bvar ht hq, substs1_subst_fvar_bvar hb hq,
    translate_substs1_fvar hT _ hθ₁, translate_substs1_fvar hT _ hθ₂] at ih
  have e : substs1 L₁ (^&(quantFresh L₁ L₂ tbl t b x))
      (iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q))
        (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q))) =
      iff L₁ (substs1 L₁ (^&(quantFresh L₁ L₂ tbl t b x))
          (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q)))
        (substs1 L₁ (^&(quantFresh L₁ L₂ tbl t b x))
          (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q))) := by
    unfold substs1
    exact subst_iff (m := 0) hA₁ hA₂ (by simp)
  have hsu : substHyp L₁ L₂ tbl t b ≤ quantFresh L₁ L₂ tbl t b x := le_max_left _ _
  have hpu : iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q))
      (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q)) ≤ quantFresh L₁ L₂ tbl t b x := by
    unfold quantFresh
    rw [hx]
    exact le_max_right _ _
  exact Derivable.all_of_fresh hS hsu hpu (IsSemiformula.iff.mpr ⟨hA₁, hA₂⟩)
    (by rw [e]; exact ih)

theorem derivable_translateSubstEquiv
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {t b p : V}
    (ht : IsSemiterm L₂ 0 t) (hp : IsSemiformula L₂ 1 p) :
    Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b p) (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.toIsTable
  have hH := isFormulaSet_substHyp hT ht b
  have hb : IsSemiterm L₂ 0 (^&b) := by simp
  have hδ : IsSemiformula L₁ 1 (domainAt L₁ tbl 0) := hT.isSemiformula_domainAt (by simp)
  have hP : 𝚺ᴬ₁-Predicate fun p : V ↦
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b p) (substHyp L₁ L₂ tbl t b)) := by
    definability
  have hg : 𝚺ᴬ₁-Function₁ (quantFresh L₁ L₂ tbl t b) := by
    definability
  have hrel : ∀ k r v, L₂.IsRel k r → IsSemitermVec L₂ k 1 v →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b (^rel k r v))
        (substHyp L₁ L₂ tbl t b)) := by
    intro k r v hR hv
    obtain ⟨k', R', rfl, rfl⟩ := hL₂.1 _ _ hR
    exact derivable_iff_translate_rel hS h hL₂ ht R' hv
  have hnrel : ∀ k r v, L₂.IsRel k r → IsSemitermVec L₂ k 1 v →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b (^nrel k r v))
        (substHyp L₁ L₂ tbl t b)) := by
    intro k r v hR hv
    obtain ⟨k', R', rfl, rfl⟩ := hL₂.1 _ _ hR
    have hX := derivable_iff_translate_rel (b := b) hS h hL₂ ht R' hv
    have hX₁ : IsSemiformula L₁ 0 (translate L₁ L₂ tbl (substs1 L₂ t (^rel (k' : V) ⌜R'⌝ v))) :=
      IsSemiformula.translate hT (IsSemiformula.substs1 ht (IsSemiformula.rel.mpr ⟨hR, hv⟩))
    have hX₂ : IsSemiformula L₁ 0 (translate L₁ L₂ tbl (substs1 L₂ (^&b) (^rel (k' : V) ⌜R'⌝ v))) :=
      IsSemiformula.translate hT (IsSemiformula.substs1 hb (IsSemiformula.rel.mpr ⟨hR, hv⟩))
    unfold translateSubstEquiv at hX ⊢
    rw [translate_substs1_nrel ht hR hv, translate_substs1_nrel hb hR hv]
    exact derivable_iff_neg_V hX₁ hX₂ hX
  have hverum : Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b ^⊤)
      (substHyp L₁ L₂ tbl t b)) := by
    have h₁ := Derivable.of_tprovable (T := S) (φ := (⊤ : Formula V L₁) 🡘 ⊤) hH (by cl_prover)
    simp only [translateSubstEquiv, substs1, substs_verum, translate_verum]
    simpa only [Semiformula.val_iff, Semiformula.val_verum] using h₁
  have hfalsum : Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b ^⊥)
      (substHyp L₁ L₂ tbl t b)) := by
    have h₁ := Derivable.of_tprovable (T := S) (φ := (⊥ : Formula V L₁) 🡘 ⊥) hH (by cl_prover)
    simp only [translateSubstEquiv, substs1, substs_falsum, translate_falsum]
    simpa only [Semiformula.val_iff, Semiformula.val_falsum] using h₁
  have hand : ∀ p q, IsSemiformula L₂ 1 p → IsSemiformula L₂ 1 q →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b p) (substHyp L₁ L₂ tbl t b)) →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b q) (substHyp L₁ L₂ tbl t b)) →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b (p ^⋏ q))
        (substHyp L₁ L₂ tbl t b)) := by
    intro p q hp₁ hq₁ ih₁ ih₂
    unfold translateSubstEquiv at ih₁ ih₂ ⊢
    rw [substs1_and hp₁ hq₁, substs1_and hp₁ hq₁ (t := ^&b),
      translate_and (IsSemiformula.substs1 ht hp₁).isUFormula
        (IsSemiformula.substs1 ht hq₁).isUFormula,
      translate_and (IsSemiformula.substs1 hb hp₁).isUFormula
        (IsSemiformula.substs1 hb hq₁).isUFormula]
    exact derivable_iff_and_V (IsSemiformula.translate hT (IsSemiformula.substs1 ht hp₁))
      (IsSemiformula.translate hT (IsSemiformula.substs1 hb hp₁))
      (IsSemiformula.translate hT (IsSemiformula.substs1 ht hq₁))
      (IsSemiformula.translate hT (IsSemiformula.substs1 hb hq₁)) ih₁ ih₂
  have hor : ∀ p q, IsSemiformula L₂ 1 p → IsSemiformula L₂ 1 q →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b p) (substHyp L₁ L₂ tbl t b)) →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b q) (substHyp L₁ L₂ tbl t b)) →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b (p ^⋎ q))
        (substHyp L₁ L₂ tbl t b)) := by
    intro p q hp₁ hq₁ ih₁ ih₂
    unfold translateSubstEquiv at ih₁ ih₂ ⊢
    rw [substs1_or hp₁ hq₁, substs1_or hp₁ hq₁ (t := ^&b),
      translate_or (IsSemiformula.substs1 ht hp₁).isUFormula
        (IsSemiformula.substs1 ht hq₁).isUFormula,
      translate_or (IsSemiformula.substs1 hb hp₁).isUFormula
        (IsSemiformula.substs1 hb hq₁).isUFormula]
    exact derivable_iff_or_V (IsSemiformula.translate hT (IsSemiformula.substs1 ht hp₁))
      (IsSemiformula.translate hT (IsSemiformula.substs1 hb hp₁))
      (IsSemiformula.translate hT (IsSemiformula.substs1 ht hq₁))
      (IsSemiformula.translate hT (IsSemiformula.substs1 hb hq₁)) ih₁ ih₂
  have hall : ∀ q, IsSemiformula L₂ 2 q →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b
        (subst L₂ ?[^&(quantFresh L₁ L₂ tbl t b (^∀ q)), ^#(0 : V)] q)) (substHyp L₁ L₂ tbl t b)) →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b (^∀ q))
        (substHyp L₁ L₂ tbl t b)) := by
    intro q hq ih
    have hA := derivable_all_of_quantFresh hS hT ht hq (pi2_qqAll_sub_one q) ih
    unfold translateSubstEquiv
    rw [translate_substs1_all ht hq, translate_substs1_all hb hq]
    exact derivable_all_iff_V hδ (isSemiformula_translate_subst hT ht hq)
      (isSemiformula_translate_subst hT hb hq) hA
  have hexs : ∀ q, IsSemiformula L₂ 2 q →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b
        (subst L₂ ?[^&(quantFresh L₁ L₂ tbl t b (^∃ q)), ^#(0 : V)] q)) (substHyp L₁ L₂ tbl t b)) →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b (^∃ q))
        (substHyp L₁ L₂ tbl t b)) := by
    intro q hq ih
    have hA := derivable_all_of_quantFresh hS hT ht hq (pi2_qqExs_sub_one q) ih
    unfold translateSubstEquiv
    rw [translate_substs1_exs ht hq, translate_substs1_exs hb hq]
    exact derivable_exs_iff_V hδ (isSemiformula_translate_subst hT ht hq)
      (isSemiformula_translate_subst hT hb hq) hA
  exact IsSemiformula.sigma1_induction_fvar hP hg hrel hnrel hverum hfalsum hand hor hall hexs hp
end value

end formSubst

/-! ## The existential rule -/

section existsRule

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open PeanoMinus ISigma0 ISigma1

section rules

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S] {tbl : V}

omit [𝗘𝗤 _ ⪯ S] [L₂.Eq] in
lemma derivable_insert_translate_substs (hT : IsTable L₁ L₂ tbl) {t b p Θ : V}
    (ht : IsSemiterm L₂ 0 t) (hp : IsSemiformula L₂ 1 p) (hΘ : IsFormulaSet L₁ Θ)
    (hD : negDomSet L₁ tbl.[0] t ⊆ Θ)
    (hX : Derivable S (insert (translate L₁ L₂ tbl (substs1 L₂ t p)) Θ))
    (hI : Derivable S (insert (iff L₁ (translate L₁ L₂ tbl (substs1 L₂ t p))
      (translate L₁ L₂ tbl (substs1 L₂ (^&b) p))) (substHyp L₁ L₂ tbl t b))) :
    Derivable S (insert (translate L₁ L₂ tbl (substs1 L₂ (^&b) p))
      (insert (neg L₁ (substs1 L₁ (^&b) tbl.[0]))
        (insert (neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t))) Θ))) := by
  have hn₁ : IsFormula L₁ (neg L₁ (substs1 L₁ (^&b) tbl.[0])) :=
    (IsSemiformula.substs1 (n := 0) (by simp) hT.domain).neg
  have hE : IsSemiformula L₁ 1 (varEqual L₁ L₂ tbl t) := by
    simpa using IsSemiformula.varEqual hT ht
  have hn₂ : IsFormula L₁ (neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t))) :=
    (IsSemiformula.substs1 (n := 0) (by simp) hE).neg
  have hpt : IsFormula L₂ (substs1 L₂ t p) := IsSemiformula.substs1 (n := 0) ht hp
  have hpb : IsFormula L₂ (substs1 L₂ (^&b) p) := IsSemiformula.substs1 (n := 0) (by simp) hp
  have hX' : IsFormula L₁ (translate L₁ L₂ tbl (substs1 L₂ t p)) := IsSemiformula.translate hT hpt
  have hY' : IsFormula L₁ (translate L₁ L₂ tbl (substs1 L₂ (^&b) p)) :=
    IsSemiformula.translate hT hpb
  have hs : IsFormulaSet L₁ (insert (neg L₁ (substs1 L₁ (^&b) tbl.[0]))
      (insert (neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t))) Θ)) :=
    IsFormulaSet.insert_iff.mpr ⟨hn₁, IsFormulaSet.insert_iff.mpr ⟨hn₂, hΘ⟩⟩
  have hXs := Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨hX', hs⟩) (by
    intro x hx
    simp at hx ⊢
    tauto) hX
  have hIs := Derivable.wk (IsFormulaSet.insert_iff.mpr
    ⟨IsSemiformula.iff.mpr ⟨hX', hY'⟩, hs⟩) (by
    intro x hx
    simp only [substHyp, mem_bitInsert_iff] at hx ⊢
    have := @hD x
    grind) hI
  exact derivable_of_iff_mp (⟨_, hX'⟩ : Formula V L₁) ⟨_, hY'⟩ hIs hXs

omit [𝗘𝗤 _ ⪯ S] [L₂.Eq] in
lemma derivable_exs_body (hT : IsTable L₁ L₂ tbl) {p b s : V} (hs : IsFormulaSet L₁ s)
    (hp : IsSemiformula L₂ 1 p) (hm : ^∃ (tbl.[0] ^⋏ translate L₁ L₂ tbl p) ∈ s)
    (hn : neg L₁ (substs1 L₁ (^&b) tbl.[0]) ∈ s)
    (hd : Derivable S (insert (translate L₁ L₂ tbl (substs1 L₂ (^&b) p)) s)) :
    Derivable S s := by
  have hδ : IsSemiformula L₁ 1 tbl.[0] := hT.domain
  have hp' : IsSemiformula L₁ 1 (translate L₁ L₂ tbl p) := IsSemiformula.translate hT hp
  have hA : IsFormula L₁ (substs1 L₁ (^&b) tbl.[0]) := IsSemiformula.substs1 (n := 0) (by simp) hδ
  have hB : IsFormula L₁ (substs1 L₁ (^&b) (translate L₁ L₂ tbl p)) :=
    IsSemiformula.substs1 (n := 0) (by simp) hp'
  have hAB : IsFormula L₁ (substs1 L₁ (^&b) tbl.[0] ^⋏ substs1 L₁ (^&b) (translate L₁ L₂ tbl p)) :=
    IsSemiformula.and.mpr ⟨hA, hB⟩
  have hs' : IsFormulaSet L₁ (insert (substs1 L₁ (^&b) tbl.[0] ^⋏
      substs1 L₁ (^&b) (translate L₁ L₂ tbl p)) s) :=
    IsFormulaSet.insert_iff.mpr ⟨hAB, hs⟩
  have hmem : substs1 L₁ (^&b) (tbl.[0] ^⋏ translate L₁ L₂ tbl p) =
      substs1 L₁ (^&b) tbl.[0] ^⋏ substs1 L₁ (^&b) (translate L₁ L₂ tbl p) := by
    unfold substs1
    rw [substs_and hδ.isUFormula hp'.isUFormula]
  rw [translate_substs1_fvar hT b hp] at hd
  have d₁ := Derivable.em (T := S) (IsFormulaSet.insert_iff.mpr ⟨hA, hs'⟩)
    (substs1 L₁ (^&b) tbl.[0])
    (mem_bitInsert_iff.mpr (Or.inl rfl))
    (mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr hn))))
  have d₂ := Derivable.wk (IsFormulaSet.insert_iff.mpr ⟨hB, hs'⟩) (by
    intro x hx
    simp at hx ⊢
    tauto) hd
  have h₁ : Derivable S (insert (substs1 L₁ (^&b) (tbl.[0] ^⋏ translate L₁ L₂ tbl p)) s) := by
    rw [hmem]
    exact Derivable.and_m (mem_bitInsert_iff.mpr (Or.inl rfl)) d₁ d₂
  exact Derivable.ex_m hm (by simp) h₁

omit [𝗘𝗤 _ ⪯ S] [L₂.Eq] in
lemma derivable_neg_exs_definesElement
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p) (hT : IsTable L₁ L₂ tbl)
    {t b Θ : V} (ht : IsSemiterm L₂ 0 t) (hΘ : IsFormulaSet L₁ Θ) (hsu : Θ ≤ b)
    (hpu : tbl.[0] ^⋏ varEqual L₁ L₂ tbl t ≤ b)
    (hd : Derivable S (insert (neg L₁ (substs1 L₁ (^&b) tbl.[0]))
      (insert (neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t))) Θ))) :
    Derivable S (insert (neg L₁ (^∃ (tbl.[0] ^⋏ varEqual L₁ L₂ tbl t))) Θ) := by
  have hδ : IsSemiformula L₁ 1 tbl.[0] := hT.domain
  have hE : IsSemiformula L₁ 1 (varEqual L₁ L₂ tbl t) := by
    simpa using IsSemiformula.varEqual hT ht
  have hn₁ : IsFormula L₁ (neg L₁ (substs1 L₁ (^&b) tbl.[0])) :=
    (IsSemiformula.substs1 (n := 0) (by simp) hδ).neg
  have hn₂ : IsFormula L₁ (neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t))) :=
    (IsSemiformula.substs1 (n := 0) (by simp) hE).neg
  have hA : IsFormula L₁ (substs1 L₁ (^&b) tbl.[0]) := IsSemiformula.substs1 (n := 0) (by simp) hδ
  have hB : IsFormula L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t)) :=
    IsSemiformula.substs1 (n := 0) (by simp) hE
  have hsub : substs1 L₁ (^&b) (tbl.[0] ^⋏ varEqual L₁ L₂ tbl t) =
      substs1 L₁ (^&b) tbl.[0] ^⋏ substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t) := by
    unfold substs1
    rw [substs_and hδ.isUFormula hE.isUFormula]
  have hneg : neg L₁ (substs1 L₁ (^&b) (tbl.[0] ^⋏ varEqual L₁ L₂ tbl t)) =
      neg L₁ (substs1 L₁ (^&b) tbl.[0]) ^⋎ neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t)) := by
    rw [hsub, neg_and hA.isUFormula hB.isUFormula]
  have hp : IsSemiformula L₁ 1 (tbl.[0] ^⋏ varEqual L₁ L₂ tbl t) := IsSemiformula.and.mpr ⟨hδ, hE⟩
  have h₁ := derivable_insert_or hΘ hn₁ hn₂ hd
  rw [← hneg] at h₁
  exact Derivable.neg_exs_of_fresh hS hsu hpu hp h₁

lemma derivable_exs_definesElement
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {t Θ : V}
    (ht : IsSemiterm L₂ 0 t)
    (hΘ : IsFormulaSet L₁ Θ) (hD : negDomSet L₁ tbl.[0] t ⊆ Θ) :
    Derivable S (insert (^∃ (tbl.[0] ^⋏ varEqual L₁ L₂ tbl t)) Θ) := by
  have hT := h.toIsTable
  have hd : tbl.[0] = h.domT.val := rfl
  have hDef : Derivable S (insert (definesElement h.domT
      (varEqualT hT (⟨t, ht⟩ : Term V L₂))).val (negDomSet L₁ tbl.[0] t)) := by
    rw [definesElement_domT_val h]
    exact derivable_definesElement hS h hL₂ ht
  have h₁ := Derivable.of_tprovable_imp
    (definesElement_exists (T := S) h.domT (varEqualT hT (⟨t, ht⟩ : Term V L₂))) hDef
  have hval : (∃¹ (h.domT ⋏ varEqualT hT (⟨t, ht⟩ : Term V L₂))).val =
      ^∃ (tbl.[0] ^⋏ varEqual L₁ L₂ tbl t) := by
    simp only [Semiformula.val_exs, Semiformula.val_and, varEqualT_val, ← hd]
  rw [hval] at h₁
  have hδ : IsSemiformula L₁ 1 tbl.[0] := hT.domain
  have hE : IsSemiformula L₁ 1 (varEqual L₁ L₂ tbl t) := by
    simpa using IsSemiformula.varEqual hT ht
  have hδE : IsSemiformula L₁ 1 (tbl.[0] ^⋏ varEqual L₁ L₂ tbl t) :=
    IsSemiformula.and.mpr ⟨hδ, hE⟩
  have hF : IsFormulaSet L₁ (insert (^∃ (tbl.[0] ^⋏ varEqual L₁ L₂ tbl t)) Θ) :=
    IsFormulaSet.insert_iff.mpr ⟨IsSemiformula.exs.mpr (by simpa using hδE), hΘ⟩
  exact Derivable.wk hF (by
    intro x hx
    simp only [mem_bitInsert_iff] at hx ⊢
    have := @hD x
    grind) h₁

lemma translated_exs (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {Γ p t : V}
    (hΓ : IsFormulaSet L₂ Γ)
    (hp : ^∃ p ∈ Γ) (ht : IsTerm L₂ t)
    (hd : TranslatedDerivable S L₂ tbl (insert (substs1 L₂ t p) Γ)) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hT := h.toIsTable
  have hp1 : IsSemiformula L₂ 1 p := by simpa using IsSemiformula.exs.mp (hΓ _ hp)
  have hpt : IsFormula L₂ (substs1 L₂ t p) := IsSemiformula.substs1 (n := 0) ht hp1
  set M := insert (substs1 L₂ t p) Γ + t
  set Θ := translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] M
  have hM : insert (substs1 L₂ t p) Γ ≤ M := le_add_right le_rfl
  have htM : t ≤ M := le_add_left le_rfl
  have hΓM : Γ ≤ M := by
    have h₁ : Γ ≤ insert (substs1 L₂ t p) Γ := le_of_subset (by
      intro x hx
      simp [hx])
    exact le_trans h₁ hM
  have hΘf : IsFormulaSet L₁ Θ := isFormulaSet_translated_union hT hΓ M
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b, Θ ≤ b ∧ tbl.[0] ^⋏ varEqual L₁ L₂ tbl t ≤ b :=
    ⟨Θ + (tbl.[0] ^⋏ varEqual L₁ L₂ tbl t), le_add_right le_rfl, le_add_left le_rfl⟩
  have hX := translated_insert hT hpt hΓ hM hd
  have hD : negDomSet L₁ tbl.[0] t ⊆ Θ := by
    intro x hx
    exact mem_cup_iff.mpr (Or.inr (negDomSet_mono htM hx))
  have hK := derivable_insert_translate_substs hT ht hp1 hΘf hD hX
    (derivable_translateSubstEquiv (t := t) (b := b) hS h hL₂ ht hp1)
  have hm0 : translate L₁ L₂ tbl (^∃ p) ∈ translateSet L₁ L₂ tbl Γ :=
    by simp; grind
  rw [translate_exs (IsSemiformula.isUFormula hp1), domainAt_zero hT] at hm0
  have hm : ^∃ (tbl.[0] ^⋏ translate L₁ L₂ tbl p) ∈
      insert (neg L₁ (substs1 L₁ (^&b) tbl.[0]))
        (insert (neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t))) Θ) :=
    mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl hm0)))))
  have hS2 := derivable_exs_body hT (IsFormulaSet.insert_iff.mp hK.isFormulaSet).2 hp1 hm
    (mem_bitInsert_iff.mpr (Or.inl rfl)) hK
  have hS3 := derivable_neg_exs_definesElement hS hT ht hΘf hb₁ hb₂ hS2
  have hS4 := derivable_exs_definesElement hS h hL₂ ht hΘf hD
  exact translated_of_le hS hT h.exs_domain hΓ hΓM (Derivable.cut _ hS4 hS3)

end rules

end existsRule

/-! ## Translated derivability of derivable sets -/

section soundness

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open PeanoMinus ISigma0 ISigma1

section rules

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S] {tbl : V}

theorem TranslatedDerivable.of_derivable
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {S' : Theory L₂} [S'.Δ₁]
    (hax : ∀ p ∈ S'.Δ₁Class (V := V), IsFormula L₂ p →
      Provable S (Bootstrapping.translate L₁ L₂ tbl p)) {s : V}
    (hs : Derivable S' s) : TranslatedDerivable S L₂ tbl s := by
  have hT := h.toIsTable
  have hdom := h.exs_domain
  obtain ⟨d, hds, hd⟩ := hs
  subst hds
  apply Derivation.induction1 𝚺 (P := fun d ↦ TranslatedDerivable S L₂ tbl (fstIdx d)) ?_ hd
  · intro s hs p hp hn
    simp only [fstIdx_axL]
    exact translated_em hT hs hp hn
  · intro s hs hv
    simp only [fstIdx_verumIntro]
    exact translated_verum hT hs hv
  · intro s hs p q dp dq hpq hdp hdq ihp ihq
    simp only [hdp.1] at ihp
    simp only [hdq.1] at ihq
    simp only [fstIdx_andIntro]
    exact translated_and hS hT hdom hs hpq ihp ihq
  · intro s hs p q d hpq hd ih
    simp only [hd.1] at ih
    simp only [fstIdx_orIntro]
    exact translated_or hS hT hdom hs hpq ih
  · intro s hs p d hp hd ih
    simp only [hd.1] at ih
    simp only [fstIdx_allIntro]
    exact translated_all hS hT hdom hs hp ih
  · intro s hs p t d hp ht hd ih
    simp only [hd.1] at ih
    simp only [fstIdx_exsIntro]
    exact translated_exs hS h hL₂ hs hp ht ih
  · intro s hs d hsub _ ih
    simp only [fstIdx_wkRule]
    exact translated_wk hT hs hsub ih
  · intro s hs d hds hd' ih
    simp only [fstIdx_shiftRule]
    subst hds
    exact translated_shift hS hT hdom (Derivation.isFormulaSet hd') ih
  · intro s hs p d₁ d₂ h₁ h₂ ih₁ ih₂
    simp only [h₁.1] at ih₁
    simp only [h₂.1] at ih₂
    simp only [fstIdx_cutRule]
    have hp : IsFormula L₂ p := (IsFormulaSet.insert_iff.mp h₁.isFormulaSet).1
    exact translated_cut hS hT hdom hs hp ih₁ ih₂
  · intro s hs p hps hpT
    simp only [fstIdx_axm]
    exact translated_axm hT hs hps (hax p hpT (hs p hps))
  · definability

end rules

end soundness

/-! ## Corollaries -/

section corollaries

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open PeanoMinus ISigma0 ISigma1

section translation

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S] {tbl : V}

/-- A formula code fixed by the shift of free variables and provable in `S'` has its translation
provable in `S`.
- [Lin97, Corollary 6.1]
- [HP98, Lemma III.2.42] -/
theorem provable_translate (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {S' : Theory L₂} [S'.Δ₁]
    (hax : ∀ p ∈ S'.Δ₁Class (V := V), IsFormula L₂ p →
      Provable S (Bootstrapping.translate L₁ L₂ tbl p)) {φ : V}
    (hφ : Bootstrapping.shift L₂ φ = φ) (hpr : Provable S' φ) :
    Provable S (Bootstrapping.translate L₁ L₂ tbl φ) := by
  have hΓ : IsFormulaSet L₂ (insert φ ∅ : V) := hpr.toDerivable.isFormulaSet
  have hφF : IsFormula L₂ φ := (IsFormulaSet.insert_iff.mp hΓ).1
  have hfresh : ∀ j, 0 ≤ j → j < (insert φ ∅ : V) → ∀ q ∈ (insert φ ∅ : V),
      fvSubst L₂ (freshVec j) q = shift L₂ q := by
    intro j _ _ q hq
    obtain rfl : q = φ := by simpa using hq
    exact (fvSubst_eq_self_of_shift hφF hφ).trans hφ.symm
  have hd : Derivable S (translateSet L₁ L₂ tbl (insert φ ∅) ∪
      negDomSet L₁ tbl.[0] (insert φ ∅)) :=
    TranslatedDerivable.of_derivable hS h hL₂ hax hpr.toDerivable
  have h₀ := elim_translateSet hS h.toIsTable h.exs_domain hΓ zero_le hfresh hd
  rw [negDomSet_zero, translateSet_insert, translateSet_empty] at h₀
  exact internal_provable_iff_internal_derivable.mpr (Derivable.ofSetEq (fun x ↦ by simp) h₀)

/-- If `S` is consistent in `V`, then so is `S'`.
- [Lin97, Corollary 6.1]
- [HP98, Lemma III.2.42] -/
theorem consistent_of_translate (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {S' : Theory L₂} [S'.Δ₁]
    (hax : ∀ p ∈ S'.Δ₁Class (V := V), IsFormula L₂ p →
      Provable S (Bootstrapping.translate L₁ L₂ tbl p))
    (hcon : S.Consistent V) : S'.Consistent V := by
  intro hp
  apply hcon
  have h₁ := provable_translate hS h hL₂ hax (φ := (⌜(⊥ : Sentence L₂)⌝ : V))
    (shift_falsum (L := L₂)) hp
  have h₂ : Bootstrapping.translate L₁ L₂ tbl (⌜(⊥ : Sentence L₂)⌝ : V) =
      (⌜(⊥ : Sentence L₁)⌝ : V) :=
    translate_falsum tbl
  rw [h₂] at h₁
  exact h₁

end translation

section finite

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]

/-- For a finite theory `S'` interpreted in `S`, provability of a formula code from `S'` yields
provability of its translation in `S`, without assuming the hypothesis on the axioms.
- [Lin97, Corollary 6.1]
- [HP98, Lemma III.2.42] -/
theorem provable_translate_of_finite (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (l : List (Sentence L₂)) (π : S ⊳ {φ | φ ∈ l})
    {tbl : V} (h : IsTableOf π.trln tbl) (hL₂ : L₂.SymbolsStandard V) {φ : V}
    (hφ : Bootstrapping.shift L₂ φ = φ) :
    letI := Theory.Δ₁.ofList l
    Provable ({φ | φ ∈ l} : Theory L₂) φ → Provable S (Bootstrapping.translate L₁ L₂ tbl φ) := by
  let _ := Theory.Δ₁.ofList l
  intro hpr
  have hax : ∀ p ∈ Theory.Δ₁Class (V := V) ({φ | φ ∈ l} : Theory L₂),
      Provable S (Bootstrapping.translate L₁ L₂ tbl p) := by
    intro p hp
    obtain ⟨σ, hσ, rfl⟩ := (Derivation.mem_deltaClass_ofList_iff l p).mp hp
    rw [h.translate_quote_sentence σ]
    exact internalize_provability (π.interpret_theory σ hσ)
  exact provable_translate hS (h.isTranslationTable hL₂) hL₂ (fun p hp _ ↦ hax p hp) hφ hpr

end finite

end corollaries

end FFL.FirstOrder.Arithmetic.Bootstrapping
