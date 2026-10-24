module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.Bootstrapping.Interpretability.ValueLemma
public import AlphaCentauri.Bootstrapping.Proof.ExistsElimination

/-!
# Translated derivability is closed under the rules of derivations

The coded set of the translations of a set of formulas along a table, its definability, and its
behaviour under shift and under free-variable substitution. For a set `Γ` of $L_2$-formulas,
`TranslatedDerivable` states that $\Gamma^*$ together with the negated instances of the domain
formula is derivable in `S`. The lemmas of this module show that this property is preserved by
each rule of the derivation calculus.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Translated sets -/

section translateSets

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-! ## Translated sets -/

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

lemma fvSubstImage_freshVec_translateSet_of {tbl Γ j : V} (hT : IsTable L₁ L₂ tbl)
    (hΓ : IsFormulaSet L₂ Γ) (h : ∀ q ∈ Γ, fvSubst L₂ (freshVec j) q = shift L₂ q) :
    fvSubstImage (L := L₁) (freshVec j) (translateSet L₁ L₂ tbl Γ) =
      setShift L₁ (translateSet L₁ L₂ tbl Γ) := by
  have hw : ∀ i < len (freshVec j : V), ∃ x, (freshVec j : V).[i] = ^&x := by
    intro i hi
    rw [len_freshVec] at hi
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with h' | rfl
    · exact ⟨i + 1, nth_freshVec_of_lt h'⟩
    · exact ⟨0, by simp⟩
  have key : ∀ p ∈ Γ, fvSubst L₁ (freshVec j) (translate L₁ L₂ tbl p) =
      shift L₁ (translate L₁ L₂ tbl p) := by
    intro p hp
    rw [← translate_fvSubst hT hw (hΓ p hp), h p hp, translate_shift hT (hΓ p hp)]
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

section rules

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {π : DirectTranslation S L₂} {tbl : V}

omit [L₂.Eq] in
lemma isFormulaSet_translated_union {Γ : V} (hT : IsTable L₁ L₂ tbl) (hΓ : IsFormulaSet L₂ Γ)
    (M : V) : IsFormulaSet L₁ (translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] M) :=
  IsFormulaSet.union.mpr ⟨IsFormulaSet.translateSet hT hΓ, IsFormulaSet.negDomSet hT.domain M⟩

omit [L₂.Eq] in
lemma translateSet_insert_cup (p s t : V) :
    translateSet L₁ L₂ tbl (insert p s) ∪ t =
      insert (translate L₁ L₂ tbl p) (translateSet L₁ L₂ tbl s ∪ t) := by
  apply mem_ext
  intro x
  simp; grind

omit [L₂.Eq] in
lemma domainAt_zero (hT : IsTable L₁ L₂ tbl) : domainAt L₁ tbl 0 = tbl.[0] := by
  unfold domainAt
  have hw : IsUTermVec L₁ (1 : V) ?[^#0] :=
    (IsSemitermVec.singleton.mpr (IsSemiterm.bvar.mpr (show (0 : V) < 1 by simp))).isUTerm
  have H : ∀ i < (1 : V), (?[^#0] : V).[i] = ^#i := by
    intro i hi
    obtain rfl : i = 0 := by simpa using hi
    simp
  exact subst_eq_self_of_le hT.domain hw (le_refl _) H

omit [L₂.Eq] in
lemma translate_free (hT : IsTable L₁ L₂ tbl) {p : V} (hp : IsSemiformula L₂ 1 p) :
    translate L₁ L₂ tbl (free L₂ p) = free L₁ (translate L₁ L₂ tbl p) := by
  simp only [free]
  rw [translate_substs1_fvar hT 0 hp.shift, translate_shift hT hp]

lemma elim_translateSet (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ₁ m M : V} (hΓ₁ : IsFormulaSet L₂ Γ₁)
    (hm : m ≤ M)
    (hfresh : ∀ j, m ≤ j → j < M → ∀ q ∈ Γ₁, fvSubst L₂ (freshVec j) q = shift L₂ q)
    (hd : Derivable S (translateSet L₁ L₂ tbl Γ₁ ∪ negDomSet L₁ tbl.[0] M)) :
    Derivable S (translateSet L₁ L₂ tbl Γ₁ ∪ negDomSet L₁ tbl.[0] m) := by
  have hT := h.isTable hL₂
  exact Derivable.elim_negDomSet hS hT.domain hT.domain_shift (provable_exs_domain π h)
    (IsFormulaSet.translateSet hT hΓ₁) hm
    (fun j hmj hjM ↦ fvSubstImage_freshVec_translateSet_of hT hΓ₁ (hfresh j hmj hjM)) hd

lemma translated_of_le (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ M : V} (hΓ : IsFormulaSet L₂ Γ)
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
  exact elim_translateSet hS h hL₂ hΓ hM hfresh hd

lemma derivable_translated_bound (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ M : V}
    (hΓ : IsFormulaSet L₂ Γ) (hM : Γ ≤ M) (hd : TranslatedDerivable S L₂ tbl Γ) :
    Derivable S (translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] M) := by
  have hT := h.isTable hL₂
  unfold TranslatedDerivable at hd
  have hU : translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ ⊆
      translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] M := by
    intro x hx
    exact mem_cup_iff.mpr ((mem_cup_iff.mp hx).imp id (negDomSet_mono hM ·))
  exact Derivable.wk (isFormulaSet_translated_union hT hΓ M) hU hd

lemma translated_insert (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {p Γ M : V}
    (hp : IsFormula L₂ p) (hΓ : IsFormulaSet L₂ Γ) (hM : insert p Γ ≤ M)
    (hd : TranslatedDerivable S L₂ tbl (insert p Γ)) :
    Derivable S
      (insert (translate L₁ L₂ tbl p) (translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] M)) := by
  have hw := derivable_translated_bound h hL₂ (IsFormulaSet.insert_iff.mpr ⟨hp, hΓ⟩) hM hd
  rw [translateSet_insert_cup] at hw
  exact hw

lemma translated_em (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ p : V}
    (hΓ : IsFormulaSet L₂ Γ) (hp : p ∈ Γ) (hnp : neg L₂ p ∈ Γ) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hT := h.isTable hL₂
  unfold TranslatedDerivable
  have hp' : translate L₁ L₂ tbl p ∈ translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ :=
    by simp; grind
  have hn : translate L₁ L₂ tbl (neg L₂ p) ∈ translateSet L₁ L₂ tbl Γ := by simp; grind
  rw [translate_neg hT (hΓ p hp)] at hn
  exact Derivable.em (isFormulaSet_translated_union hT hΓ Γ) _ hp'
    (mem_cup_iff.mpr (Or.inl hn))

lemma translated_verum (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ : V}
    (hΓ : IsFormulaSet L₂ Γ) (hv : ^⊤ ∈ Γ) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hT := h.isTable hL₂
  unfold TranslatedDerivable
  have hv' : ^⊤ ∈ translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ :=
    by simp; grind [translate_verum]
  exact Derivable.verum (isFormulaSet_translated_union hT hΓ Γ) hv'

lemma translated_axm (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ p : V}
    (hΓ : IsFormulaSet L₂ Γ) (hp : p ∈ Γ) (hax : Provable S (translate L₁ L₂ tbl p)) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hT := h.isTable hL₂
  unfold TranslatedDerivable
  exact Derivable.wk (isFormulaSet_translated_union hT hΓ Γ)
    (by intro x hx; simp at hx ⊢; grind) hax.toDerivable

lemma translated_and (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ p q : V}
    (hΓ : IsFormulaSet L₂ Γ) (hpq : p ^⋏ q ∈ Γ)
    (h₁ : TranslatedDerivable S L₂ tbl (insert p Γ))
    (h₂ : TranslatedDerivable S L₂ tbl (insert q Γ)) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hT := h.isTable hL₂
  have hpq' := hΓ _ hpq
  have hp : IsFormula L₂ p := (IsSemiformula.and.mp hpq').1
  have hq : IsFormula L₂ q := (IsSemiformula.and.mp hpq').2
  have hpM : insert p Γ ≤ insert p Γ + insert q Γ + Γ := le_add_right (le_add_right le_rfl)
  have hqM : insert q Γ ≤ insert p Γ + insert q Γ + Γ := le_add_right (le_add_left le_rfl)
  have hΓM : Γ ≤ insert p Γ + insert q Γ + Γ := le_add_left le_rfl
  have d₁ := translated_insert h hL₂ hp hΓ hpM h₁
  have d₂ := translated_insert h hL₂ hq hΓ hqM h₂
  have hmem : translate L₁ L₂ tbl (p ^⋏ q) ∈
      translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] (insert p Γ + insert q Γ + Γ) :=
    by simp; grind
  rw [translate_and (IsSemiformula.isUFormula hp) (IsSemiformula.isUFormula hq)] at hmem
  exact translated_of_le hS h hL₂ hΓ hΓM (Derivable.and_m hmem d₁ d₂)

lemma translated_or (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ p q : V}
    (hΓ : IsFormulaSet L₂ Γ) (hpq : p ^⋎ q ∈ Γ)
    (hd : TranslatedDerivable S L₂ tbl (insert p (insert q Γ))) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hT := h.isTable hL₂
  have hpq' := hΓ _ hpq
  have hp : IsFormula L₂ p := (IsSemiformula.or.mp hpq').1
  have hq : IsFormula L₂ q := (IsSemiformula.or.mp hpq').2
  have hM : insert p (insert q Γ) ≤ insert p (insert q Γ) + Γ := le_add_right le_rfl
  have hΓM : Γ ≤ insert p (insert q Γ) + Γ := le_add_left le_rfl
  have hd' := derivable_translated_bound h hL₂
    (IsFormulaSet.insert_iff.mpr ⟨hp, IsFormulaSet.insert_iff.mpr ⟨hq, hΓ⟩⟩) hM hd
  rw [translateSet_insert_cup, translateSet_insert_cup] at hd'
  have hmem : translate L₁ L₂ tbl p ^⋎ translate L₁ L₂ tbl q ∈
      translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] (insert p (insert q Γ) + Γ) := by
    rw [← translate_or (IsSemiformula.isUFormula hp) (IsSemiformula.isUFormula hq)]
    simp; grind
  exact translated_of_le hS h hL₂ hΓ hΓM (Derivable.or_m hmem hd')

lemma translated_cut (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ p : V}
    (hΓ : IsFormulaSet L₂ Γ) (hp : IsFormula L₂ p)
    (h₁ : TranslatedDerivable S L₂ tbl (insert p Γ))
    (h₂ : TranslatedDerivable S L₂ tbl (insert (neg L₂ p) Γ)) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hT := h.isTable hL₂
  have hnp : IsFormula L₂ (neg L₂ p) := IsSemiformula.neg hp
  have hpM : insert p Γ ≤ insert p Γ + insert (neg L₂ p) Γ + Γ :=
    le_add_right (le_add_right le_rfl)
  have hnpM : insert (neg L₂ p) Γ ≤ insert p Γ + insert (neg L₂ p) Γ + Γ :=
    le_add_right (le_add_left le_rfl)
  have hΓM : Γ ≤ insert p Γ + insert (neg L₂ p) Γ + Γ := le_add_left le_rfl
  have d₁ := translated_insert h hL₂ hp hΓ hpM h₁
  have d₂ := translated_insert h hL₂ hnp hΓ hnpM h₂
  rw [translate_neg hT hp] at d₂
  exact translated_of_le hS h hL₂ hΓ hΓM (Derivable.cut (translate L₁ L₂ tbl p) d₁ d₂)

lemma translated_wk (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ Γ' : V}
    (hΓ' : IsFormulaSet L₂ Γ') (hsub : Γ ⊆ Γ')
    (hd : TranslatedDerivable S L₂ tbl Γ) :
    TranslatedDerivable S L₂ tbl Γ' := by
  have hT := h.isTable hL₂
  unfold TranslatedDerivable at hd ⊢
  have hU : translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] Γ ⊆
      translateSet L₁ L₂ tbl Γ' ∪ negDomSet L₁ tbl.[0] Γ' := by
    intro x hx
    exact mem_cup_iff.mpr
      ((mem_cup_iff.mp hx).imp (translateSet_mono hsub ·) (negDomSet_mono (le_of_subset hsub) ·))
  exact Derivable.wk (isFormulaSet_translated_union hT hΓ' Γ') hU hd

lemma translated_shift (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ : V}
    (hΓ : IsFormulaSet L₂ Γ) (hd : TranslatedDerivable S L₂ tbl Γ) :
    TranslatedDerivable S L₂ tbl (setShift L₂ Γ) := by
  have hT := h.isTable hL₂
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
  exact translated_of_le hS h hL₂ hΓs hM hd'

lemma translated_all (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ p : V}
    (hΓ : IsFormulaSet L₂ Γ) (hp : ^∀ p ∈ Γ)
    (hd : TranslatedDerivable S L₂ tbl (insert (free L₂ p) (setShift L₂ Γ))) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hT := h.isTable hL₂
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
  have hd' := derivable_translated_bound h hL₂ hΓ₁ hM₁ hd
  have hd'' := elim_translateSet hS h hL₂ hΓ₁ hΓM hfresh hd'
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

end rules

end FFL.FirstOrder.Arithmetic.Bootstrapping
