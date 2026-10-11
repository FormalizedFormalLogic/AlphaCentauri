module

public import AlphaCentauri.Bootstrapping.Interpretability.Quote
public import AlphaCentauri.Bootstrapping.Interpretability.Translation
public import AlphaCentauri.Bootstrapping.Syntax.SubstCongruence

/-!
# Commutation of the internal translation with negation and shift

Along a table satisfying `IsTable`, the internal translation sends negation to negation and shift
to shift, and it sends a coded $L_2$-formula to a coded $L_1$-formula of the same arity.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `tbl` lists, for the languages `L₁` and `L₂`, shift-invariant formulas of the right arities. -/
structure IsTable (L₁ L₂ : Language) [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq] [L₂.Encodable]
    [L₂.LORDefinable] (tbl : V) : Prop where
  domain : IsSemiformula L₁ 1 (tableDomain tbl)
  domain_shift : shift L₁ (tableDomain tbl) = tableDomain tbl
  rel {k r : V} : L₂.IsRel k r → IsSemiformula L₁ k (tableRel tbl k r)
  rel_shift {k r : V} : L₂.IsRel k r → shift L₁ (tableRel tbl k r) = tableRel tbl k r
  func {k f : V} : L₂.IsFunc k f → IsSemiformula L₁ (k + 1) (tableFunc tbl k f)
  func_shift {k f : V} : L₂.IsFunc k f → shift L₁ (tableFunc tbl k f) = tableFunc tbl k f

section generic

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma IsSemiformula.of_le {n m p : V} (h : IsSemiformula L n p) (hnm : n ≤ m) :
    IsSemiformula L m p := isSemiformula_iff.mpr ⟨h.isUFormula, h.bv_le.trans hnm⟩

lemma add_arity_comm (k n : V) : k + 1 + n = n + 1 + k := by
  simp only [add_comm, add_left_comm]

lemma IsSemitermVec.pair {n s t : V} (hs : IsSemiterm L n s) (ht : IsSemiterm L n t) :
    IsSemitermVec L 2 n ?[s, t] := by
  simpa using (IsSemitermVec.singleton.mpr ht).adjoin hs

lemma IsUTermVec.pair {s t : V} (hs : IsUTerm L s) (ht : IsUTerm L t) :
    IsUTermVec L 2 (?[s, t] : V) := by
  rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two]]
  exact ((IsUTermVec.empty : IsUTermVec (V := V) L 0 0).adjoin ht).adjoin hs

lemma termShiftVec_bvarVec (s n : V) : termShiftVec L n (bvarVec s n) = bvarVec s n := by
  have h₁ : IsUTermVec L n (bvarVec s n) :=
    (IsSemitermVec.bvarVec (L := L) (n := s + n) le_rfl).isUTerm
  apply nth_ext' n (by rw [len_termShiftVec h₁]) (by simp)
  intro i hi
  rw [nth_termShiftVec h₁ hi, nth_bvarVec _ _ _ hi, termShift_bvar]

lemma termShiftVec_bvarVec_cons (i s n : V) :
    termShiftVec L (n + 1) (^#i ∷ bvarVec s n) = ^#i ∷ bvarVec s n := by
  have h₁ : IsUTermVec L n (bvarVec s n) :=
    (IsSemitermVec.bvarVec (L := L) (n := s + n) le_rfl).isUTerm
  rw [termShiftVec_cons (show IsUTerm L ^#i by simp) h₁, termShift_bvar, termShiftVec_bvarVec]

lemma relocate_eq_subst {n i s p : V} (hp : IsSemiformula L (n + 1) p) :
    relocate L i s p = subst L (^#i ∷ bvarVec s n) p := by
  have h₁ : IsSemiformula L (bv L p) p := isSemiformula_iff.mpr ⟨hp.isUFormula, le_rfl⟩
  have h₂ : IsUTermVec L (bv L p + 1) (^#i ∷ bvarVec s (bv L p)) :=
    (IsSemitermVec.bvarVec (L := L) (n := s + bv L p) le_rfl).isUTerm.adjoin (by simp)
  have h₃ : IsUTermVec L (n + 1) (^#i ∷ bvarVec s n) :=
    (IsSemitermVec.bvarVec (L := L) (n := s + n) le_rfl).isUTerm.adjoin (by simp)
  rw [relocate]
  apply subst_congr h₁ h₂ h₃ (by simp) hp.bv_le
  intro j hj
  rcases zero_or_succ j with (rfl | ⟨j, rfl⟩)
  · simp
  · have h₄ : j < n := by
      have h₅ : j + 1 < n + 1 := lt_of_lt_of_le hj hp.bv_le
      simpa using h₅
    have h₆ : j < bv L p := lt_trans (by simp) hj
    rw [nth_adjoin_succ, nth_adjoin_succ, nth_bvarVec _ _ _ h₆, nth_bvarVec _ _ _ h₄]

lemma IsSemiformula.relocate {n m i s p : V} (hp : IsSemiformula L (n + 1) p) (hi : i < m)
    (hs : s + n ≤ m) : IsSemiformula L m (relocate L i s p) := by
  rw [relocate_eq_subst hp]
  exact hp.subst (IsSemitermVec.adjoin (IsSemitermVec.bvarVec hs) (IsSemiterm.bvar.mpr hi))

lemma shift_relocate {n m i s p : V} (hp : IsSemiformula L (n + 1) p) (hi : i < m)
    (hs : s + n ≤ m) : shift L (relocate L i s p) = relocate L i s (shift L p) := by
  have h₁ : IsSemitermVec L (n + 1) m (^#i ∷ bvarVec s n) :=
    IsSemitermVec.adjoin (IsSemitermVec.bvarVec hs) (IsSemiterm.bvar.mpr hi)
  rw [relocate_eq_subst hp, relocate_eq_subst hp.shift, shift_substs hp h₁,
    termShiftVec_bvarVec_cons]

lemma shift_qqConj_exists {n : V} (ps : V) (hps : ∀ i < len ps, IsSemiformula L n ps.[i]) :
    ∃ qs, len qs = len ps ∧ (∀ i < len ps, qs.[i] = shift L ps.[i]) ∧
      shift L (^⋀ ps) = ^⋀ qs := by
  revert hps
  induction ps using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => intro _; exact ⟨0, by simp, by simp, by simp⟩
  case adjoin p ps ih =>
    intro hps
    have h₁ : IsSemiformula L n p := by simpa using hps 0 (by simp)
    have h₂ : ∀ i < len ps, IsSemiformula L n ps.[i] := by
      intro i hi
      simpa using hps (i + 1) (by simpa using hi)
    obtain ⟨qs, hlen, hq, hsh⟩ := ih h₂
    have h₃ : IsUFormula L (^⋀ ps) := (qqConj_semiformula.mpr h₂).isUFormula
    have h₄ : shift L (^⋀ (p ∷ ps)) = ^⋀ (shift L p ∷ qs) := by
      rw [qqConj_cons, qqConj_cons, shift_and h₁.isUFormula h₃, hsh]
    refine ⟨shift L p ∷ qs, by simp [hlen], ?_, h₄⟩
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simpa using hq i (by simpa using hi)

lemma shift_imp {n p q : V} (hp : IsSemiformula L n p) (hq : IsSemiformula L n q) :
    shift L (imp L p q) = imp L (shift L p) (shift L q) := by
  unfold imp
  rw [shift_or hp.isUFormula.neg hq.isUFormula, shift_neg hp]

lemma neg_imp {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    neg L (imp L p q) = p ^⋏ neg L q := by
  unfold imp
  rw [neg_or hp.neg hq, hp.neg_neg]

end generic

section table

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

lemma IsTable.shift_domainAt {tbl : V} (hT : IsTable L₁ L₂ tbl) (i : V) :
    shift L₁ (domainAt L₁ tbl i) = domainAt L₁ tbl i := by
  have h₁ : IsSemitermVec L₁ 1 (i + 1) ?[^#i] :=
    IsSemitermVec.singleton.mpr (IsSemiterm.bvar.mpr (by simp))
  rw [domainAt, shift_substs hT.domain h₁, hT.domain_shift,
    termShiftVec_cons₁ (show IsUTerm L₁ ^#i by simp),
    termShift_bvar]

lemma IsTable.isSemiformula_domainAt {tbl : V} (hT : IsTable L₁ L₂ tbl) {m i : V} (hi : i < m) :
    IsSemiformula L₁ m (domainAt L₁ tbl i) :=
  hT.domain.subst (IsSemitermVec.singleton.mpr (IsSemiterm.bvar.mpr hi))

lemma IsTable.isSemiformula_funcTail {tbl k f m : V} (hT : IsTable L₁ L₂ tbl) (hf : L₂.IsFunc k f)
    (hk : k < m) : IsSemiformula L₁ m (funcTail L₁ tbl k f) := by
  have h₁ : IsSemitermVec L₁ (k + 1) m (^#k ∷ bvarVec 0 k) :=
    IsSemitermVec.adjoin (IsSemitermVec.bvarVec (by simpa using hk.le)) (IsSemiterm.bvar.mpr hk)
  rw [funcTail]
  exact (hT.func hf).subst h₁

lemma IsTable.shift_funcTail {tbl k f : V} (hT : IsTable L₁ L₂ tbl) (hf : L₂.IsFunc k f) :
    shift L₁ (funcTail L₁ tbl k f) = funcTail L₁ tbl k f := by
  have h₁ : IsSemitermVec L₁ (k + 1) (k + 1) (^#k ∷ bvarVec 0 k) :=
    IsSemitermVec.adjoin (IsSemitermVec.bvarVec (by simp)) (IsSemiterm.bvar.mpr (by simp))
  rw [funcTail, shift_substs (hT.func hf) h₁, termShiftVec_bvarVec_cons, hT.func_shift hf]

lemma IsTable.isSemiformula_guardVec {tbl n m k s w j : V} (hT : IsTable L₁ L₂ tbl) (hk : k ≤ m)
    (hs : s + n ≤ m) (hw : ∀ i < k, IsSemiformula L₁ (n + 1) w.[i]) (hj : j < k) :
    IsSemiformula L₁ m (guardVec L₁ tbl s w k).[j] := by
  rw [nth_guardVec tbl s w k j hj]
  exact IsSemiformula.and.mpr
    ⟨hT.isSemiformula_domainAt (lt_of_lt_of_le hj hk), (hw j hj).relocate (lt_of_lt_of_le hj hk) hs⟩

lemma IsSemiformula.qqConj_guardVec {tbl n m k s w : V} (hT : IsTable L₁ L₂ tbl) (hk : k ≤ m)
    (hs : s + n ≤ m) (hw : ∀ i < k, IsSemiformula L₁ (n + 1) w.[i]) :
    IsSemiformula L₁ m (^⋀ guardVec L₁ tbl s w k) :=
  qqConj_semiformula.mpr fun j hj ↦ hT.isSemiformula_guardVec hk hs hw (by simpa using hj)

lemma IsTable.shift_qqConj_guardVec {tbl n m k s w w' : V} (hT : IsTable L₁ L₂ tbl) (hk : k ≤ m)
    (hs : s + n ≤ m) (hw : ∀ i < k, IsSemiformula L₁ (n + 1) w.[i])
    (hw' : ∀ i < k, w'.[i] = shift L₁ w.[i]) :
    shift L₁ (^⋀ guardVec L₁ tbl s w k) = ^⋀ guardVec L₁ tbl s w' k := by
  obtain ⟨qs, hlen, hq, hsh⟩ := shift_qqConj_exists (L := L₁) (guardVec L₁ tbl s w k)
    (fun j hj ↦ hT.isSemiformula_guardVec hk hs hw (by simpa using hj))
  rw [hsh]
  congr 1
  apply nth_ext' k (by simp [hlen]) (by simp)
  intro i hi
  rw [hq i (by simpa using hi), nth_guardVec tbl s w k i hi, nth_guardVec tbl s w' k i hi, hw' i hi,
    shift_and (hT.isSemiformula_domainAt (lt_of_lt_of_le hi hk)).isUFormula
      ((hw i hi).relocate (lt_of_lt_of_le hi hk) hs).isUFormula,
    hT.shift_domainAt, shift_relocate (hw i hi) (lt_of_lt_of_le hi hk) hs]

lemma isRel_eq_quote : L₁.IsRel 2 (Encodable.encode (Language.Eq.eq : L₁.Rel 2) : V) :=
  codeIn_rel_quote (V := V) Language.Eq.eq

lemma IsTable.isSemiformula_funcBody {tbl n k f v : V} (hT : IsTable L₁ L₂ tbl) (hf : L₂.IsFunc k f)
    (hv : IsSemitermVec L₂ k n v)
    (H : ∀ i < k, IsSemiformula L₁ (n + 1) (varEqual L₁ L₂ tbl v.[i])) :
    IsSemiformula L₁ (n + 1 + k)
      (imp L₁ (^⋀ guardVec L₁ tbl (k + 1) (varEqualVec L₁ L₂ tbl k v) k)
        (funcTail L₁ tbl k f)) := by
  have h₁ : ∀ i < k, IsSemiformula L₁ (n + 1) (varEqualVec L₁ L₂ tbl k v).[i] := by
    intro i hi
    rw [nth_varEqualVec hv.isUTerm hi]
    exact H i hi
  have h₂ : k ≤ n + 1 + k := by simp
  have h₃ : k + 1 + n ≤ n + 1 + k := (add_arity_comm k n).le
  exact IsSemiformula.imp.mpr
    ⟨IsSemiformula.qqConj_guardVec hT h₂ h₃ h₁, hT.isSemiformula_funcTail hf (by simp)⟩

lemma IsSemiformula.varEqual {tbl n t : V} (hT : IsTable L₁ L₂ tbl) (ht : IsSemiterm L₂ n t) :
    IsSemiformula L₁ (n + 1) (Bootstrapping.varEqual L₁ L₂ tbl t) := by
  have h₁ : ∀ t, IsSemiterm L₂ n t →
      IsSemiformula L₁ (n + 1) (Bootstrapping.varEqual L₁ L₂ tbl t) := by
    apply IsSemiterm.sigma1_induction
      (P := fun t ↦ IsSemiformula L₁ (n + 1) (Bootstrapping.varEqual L₁ L₂ tbl t))
    · definability
    · intro z hz
      rw [varEqual_bvar]
      exact IsSemiformula.rel.mpr ⟨isRel_eq_quote,
        IsSemitermVec.pair (IsSemiterm.bvar.mpr (by simp))
          (IsSemiterm.bvar.mpr (by simpa using hz))⟩
    · intro x
      rw [varEqual_fvar]
      exact IsSemiformula.rel.mpr ⟨isRel_eq_quote,
        IsSemitermVec.pair (IsSemiterm.bvar.mpr (by simp)) (IsSemiterm.fvar _ _)⟩
    · intro k f v hf hv ih
      rw [varEqual_func hf hv.isUTerm]
      exact IsSemiformula.qqAlls (hT.isSemiformula_funcBody hf hv ih)
  exact h₁ t ht

lemma IsTable.isSemiformula_varEqualVec_nth {tbl n k v i : V} (hT : IsTable L₁ L₂ tbl)
    (hv : IsSemitermVec L₂ k n v) (hi : i < k) :
    IsSemiformula L₁ (n + 1) (varEqualVec L₁ L₂ tbl k v).[i] := by
  rw [nth_varEqualVec hv.isUTerm hi]
  exact IsSemiformula.varEqual hT (hv.nth hi)

lemma IsSemiformula.translateRel {tbl n k R v : V} (hT : IsTable L₁ L₂ tbl) (hR : L₂.IsRel k R)
    (hv : IsSemitermVec L₂ k n v) :
    IsSemiformula L₁ n (Bootstrapping.translateRel L₁ L₂ tbl k R v) := by
  have h₁ : k ≤ n + k := by simp
  have h₂ : k + n ≤ n + k := (add_comm k n).le
  have h₃ : IsSemiformula L₁ (n + k)
      (^⋀ guardVec L₁ tbl k (varEqualVec L₁ L₂ tbl k v) k) :=
    IsSemiformula.qqConj_guardVec hT h₁ h₂ (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi)
  have h₄ : IsSemiformula L₁ (n + k) (tableRel tbl k R) := (hT.rel hR).of_le h₁
  unfold Bootstrapping.translateRel
  exact IsSemiformula.qqAlls (IsSemiformula.imp.mpr ⟨h₃, h₄⟩)

lemma IsSemiformula.translate {tbl n p : V} (hT : IsTable L₁ L₂ tbl) (hp : IsSemiformula L₂ n p) :
    IsSemiformula L₁ n (Bootstrapping.translate L₁ L₂ tbl p) := by
  apply IsSemiformula.sigma1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    rw [translate_rel hR hv.isUTerm]
    exact IsSemiformula.translateRel hT hR hv
  · intro n k R v hR hv
    rw [translate_nrel hR hv.isUTerm]
    exact (IsSemiformula.translateRel hT hR hv).neg
  · intro n
    simp
  · intro n
    simp
  · intro n p q hp hq ihp ihq
    rw [translate_and hp.isUFormula hq.isUFormula]
    exact IsSemiformula.and.mpr ⟨ihp, ihq⟩
  · intro n p q hp hq ihp ihq
    rw [translate_or hp.isUFormula hq.isUFormula]
    exact IsSemiformula.or.mpr ⟨ihp, ihq⟩
  · intro n p hp ih
    rw [translate_all hp.isUFormula]
    exact IsSemiformula.all.mpr
      (IsSemiformula.imp.mpr ⟨hT.isSemiformula_domainAt (by simp), ih⟩)
  · intro n p hp ih
    rw [translate_exs hp.isUFormula]
    exact IsSemiformula.exs.mpr
      (IsSemiformula.and.mpr ⟨hT.isSemiformula_domainAt (by simp), ih⟩)

lemma translate_neg {tbl n p : V} (hT : IsTable L₁ L₂ tbl) (hp : IsSemiformula L₂ n p) :
    translate L₁ L₂ tbl (neg L₂ p) = neg L₁ (translate L₁ L₂ tbl p) := by
  apply IsSemiformula.sigma1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    rw [neg_rel hR hv.isUTerm, translate_nrel hR hv.isUTerm, translate_rel hR hv.isUTerm]
  · intro n k R v hR hv
    rw [neg_nrel hR hv.isUTerm, translate_rel hR hv.isUTerm, translate_nrel hR hv.isUTerm,
      IsUFormula.neg_neg (IsSemiformula.translateRel hT hR hv).isUFormula]
  · intro n
    simp
  · intro n
    simp
  · intro n p q hp hq ihp ihq
    rw [neg_and hp.isUFormula hq.isUFormula, translate_or hp.isUFormula.neg hq.isUFormula.neg, ihp,
      ihq, translate_and hp.isUFormula hq.isUFormula,
      neg_and (IsSemiformula.translate hT hp).isUFormula (IsSemiformula.translate hT hq).isUFormula]
  · intro n p q hp hq ihp ihq
    rw [neg_or hp.isUFormula hq.isUFormula, translate_and hp.isUFormula.neg hq.isUFormula.neg, ihp,
      ihq, translate_or hp.isUFormula hq.isUFormula,
      neg_or (IsSemiformula.translate hT hp).isUFormula (IsSemiformula.translate hT hq).isUFormula]
  · intro n p hp ih
    have h₁ : IsSemiformula L₁ (n + 1) (domainAt L₁ tbl 0) :=
      hT.isSemiformula_domainAt (by simp)
    have h₂ : IsSemiformula L₁ (n + 1) (translate L₁ L₂ tbl p) :=
      IsSemiformula.translate hT hp
    rw [neg_all hp.isUFormula, translate_exs hp.isUFormula.neg, ih, translate_all hp.isUFormula,
      neg_all (IsSemiformula.imp.mpr ⟨h₁, h₂⟩).isUFormula, neg_imp h₁.isUFormula h₂.isUFormula]
  · intro n p hp ih
    have h₁ : IsSemiformula L₁ (n + 1) (domainAt L₁ tbl 0) :=
      hT.isSemiformula_domainAt (by simp)
    have h₂ : IsSemiformula L₁ (n + 1) (translate L₁ L₂ tbl p) :=
      IsSemiformula.translate hT hp
    rw [neg_ex hp.isUFormula, translate_all hp.isUFormula.neg, ih, translate_exs hp.isUFormula,
      neg_ex (IsSemiformula.and.mpr ⟨h₁, h₂⟩).isUFormula,
      neg_and h₁.isUFormula h₂.isUFormula]
    rfl

lemma varEqual_termShift {tbl n t : V} (hT : IsTable L₁ L₂ tbl) (ht : IsSemiterm L₂ n t) :
    varEqual L₁ L₂ tbl (termShift L₂ t) = shift L₁ (varEqual L₁ L₂ tbl t) := by
  have h₁ : ∀ t, IsSemiterm L₂ n t →
      varEqual L₁ L₂ tbl (termShift L₂ t) = shift L₁ (varEqual L₁ L₂ tbl t) := by
    apply IsSemiterm.sigma1_induction
      (P := fun t ↦ varEqual L₁ L₂ tbl (termShift L₂ t) = shift L₁ (varEqual L₁ L₂ tbl t))
    · definability
    · intro z hz
      rw [termShift_bvar, varEqual_bvar,
        shift_rel isRel_eq_quote
          (IsUTermVec.pair (show IsUTerm L₁ (^#0 : V) by simp)
            (show IsUTerm L₁ (^#(z + 1) : V) by simp)),
        termShiftVec_cons₂ (show IsUTerm L₁ (^#0 : V) by simp)
          (show IsUTerm L₁ (^#(z + 1) : V) by simp),
        termShift_bvar, termShift_bvar]
    · intro x
      rw [termShift_fvar, varEqual_fvar, varEqual_fvar,
        shift_rel isRel_eq_quote
          (IsUTermVec.pair (show IsUTerm L₁ (^#0 : V) by simp) (show IsUTerm L₁ (^&x : V) by simp)),
        termShiftVec_cons₂ (show IsUTerm L₁ (^#0 : V) by simp) (show IsUTerm L₁ (^&x : V) by simp),
        termShift_bvar, termShift_fvar]
    · intro k f v hf hv ih
      have h₂ :=
        hT.isSemiformula_funcBody hf hv (fun i hi ↦ IsSemiformula.varEqual hT (hv.nth hi))
      have h₃ := (IsSemiformula.imp.mp h₂).1
      have h₄ := hT.isSemiformula_funcTail hf (show k < n + 1 + k by simp)
      have h₅ : k ≤ n + 1 + k := by simp
      have h₆ : k + 1 + n ≤ n + 1 + k := (add_arity_comm k n).le
      have h₇ : ∀ i < k, (varEqualVec L₁ L₂ tbl k (termShiftVec L₂ k v)).[i] =
          shift L₁ (varEqualVec L₁ L₂ tbl k v).[i] := by
        intro i hi
        rw [nth_varEqualVec hv.termShiftVec.isUTerm hi, nth_varEqualVec hv.isUTerm hi,
          nth_termShiftVec hv.isUTerm hi]
        exact ih i hi
      rw [termShift_func hf hv.isUTerm, varEqual_func hf hv.termShiftVec.isUTerm,
        varEqual_func hf hv.isUTerm, shift_qqAlls h₂.isUFormula k, shift_imp h₃ h₄,
        hT.shift_qqConj_guardVec h₅ h₆ (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₇,
        hT.shift_funcTail hf]
  exact h₁ t ht

lemma shift_translateRel {tbl n k R v : V} (hT : IsTable L₁ L₂ tbl) (hR : L₂.IsRel k R)
    (hv : IsSemitermVec L₂ k n v) :
    shift L₁ (Bootstrapping.translateRel L₁ L₂ tbl k R v) =
      Bootstrapping.translateRel L₁ L₂ tbl k R (termShiftVec L₂ k v) := by
  have h₁ : k ≤ n + k := by simp
  have h₂ : k + n ≤ n + k := (add_comm k n).le
  have h₃ : IsSemiformula L₁ (n + k) (^⋀ guardVec L₁ tbl k (varEqualVec L₁ L₂ tbl k v) k) :=
    IsSemiformula.qqConj_guardVec hT h₁ h₂ (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi)
  have h₄ : IsSemiformula L₁ (n + k) (tableRel tbl k R) := (hT.rel hR).of_le h₁
  have h₅ : ∀ i < k, (varEqualVec L₁ L₂ tbl k (termShiftVec L₂ k v)).[i] =
      shift L₁ (varEqualVec L₁ L₂ tbl k v).[i] := by
    intro i hi
    rw [nth_varEqualVec hv.termShiftVec.isUTerm hi, nth_varEqualVec hv.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi]
    exact varEqual_termShift hT (hv.nth hi)
  unfold Bootstrapping.translateRel
  rw [shift_qqAlls (IsSemiformula.imp.mpr ⟨h₃, h₄⟩).isUFormula k, shift_imp h₃ h₄,
    hT.shift_qqConj_guardVec h₁ h₂ (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₅,
    hT.rel_shift hR]

lemma translate_shift {tbl n p : V} (hT : IsTable L₁ L₂ tbl) (hp : IsSemiformula L₂ n p) :
    translate L₁ L₂ tbl (shift L₂ p) = shift L₁ (translate L₁ L₂ tbl p) := by
  apply IsSemiformula.sigma1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    rw [shift_rel hR hv.isUTerm, translate_rel hR hv.termShiftVec.isUTerm,
      translate_rel hR hv.isUTerm, shift_translateRel hT hR hv]
  · intro n k R v hR hv
    rw [shift_nrel hR hv.isUTerm, translate_nrel hR hv.termShiftVec.isUTerm,
      translate_nrel hR hv.isUTerm, shift_neg (IsSemiformula.translateRel hT hR hv),
      shift_translateRel hT hR hv]
  · intro n
    simp
  · intro n
    simp
  · intro n p q hp hq ihp ihq
    rw [shift_and hp.isUFormula hq.isUFormula,
      translate_and hp.isUFormula.shift hq.isUFormula.shift, ihp, ihq,
      translate_and hp.isUFormula hq.isUFormula,
      shift_and (IsSemiformula.translate hT hp).isUFormula
        (IsSemiformula.translate hT hq).isUFormula]
  · intro n p q hp hq ihp ihq
    rw [shift_or hp.isUFormula hq.isUFormula,
      translate_or hp.isUFormula.shift hq.isUFormula.shift, ihp, ihq,
      translate_or hp.isUFormula hq.isUFormula,
      shift_or (IsSemiformula.translate hT hp).isUFormula
        (IsSemiformula.translate hT hq).isUFormula]
  · intro n p hp ih
    have h₁ : IsSemiformula L₁ (n + 1) (domainAt L₁ tbl 0) :=
      hT.isSemiformula_domainAt (by simp)
    have h₂ : IsSemiformula L₁ (n + 1) (translate L₁ L₂ tbl p) :=
      IsSemiformula.translate hT hp
    rw [shift_all hp.isUFormula, translate_all hp.isUFormula.shift, ih,
      translate_all hp.isUFormula, shift_all (IsSemiformula.imp.mpr ⟨h₁, h₂⟩).isUFormula,
      shift_imp h₁ h₂, hT.shift_domainAt]
  · intro n p hp ih
    have h₁ : IsSemiformula L₁ (n + 1) (domainAt L₁ tbl 0) :=
      hT.isSemiformula_domainAt (by simp)
    have h₂ : IsSemiformula L₁ (n + 1) (translate L₁ L₂ tbl p) :=
      IsSemiformula.translate hT hp
    rw [shift_exs hp.isUFormula, translate_exs hp.isUFormula.shift, ih,
      translate_exs hp.isUFormula, shift_exs (IsSemiformula.and.mpr ⟨h₁, h₂⟩).isUFormula,
      shift_and h₁.isUFormula h₂.isUFormula, hT.shift_domainAt]

end table

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Language

/-- Every relation and function symbol of `L` in `V` is a standard one. -/
def SymbolsStandard (L : Language) [L.Encodable] [L.LORDefinable] (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop :=
  (∀ k r : V, L.IsRel k r → ∃ (k' : ℕ) (R : L.Rel k'), k = k' ∧ r = (⌜R⌝ : V)) ∧
  (∀ k f : V, L.IsFunc k f → ∃ (k' : ℕ) (F : L.Func k'), k = k' ∧ f = (⌜F⌝ : V))

end FFL.FirstOrder.Language

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section isTable

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq]

lemma shift_quote_semisentence {L : Language} [L.Encodable] [L.LORDefinable] {n : ℕ}
    (σ : Semisentence L n) : shift L (⌜σ⌝ : V) = ⌜σ⌝ := by
  have h₁ : Rewriting.shift (Rewriting.emb σ : Semiproposition L n) = Rewriting.emb σ := by
    simpa [Rewriting.shifts] using Rewriting.shifts_emb ({σ} : Multiset (Semisentence L n))
  rw [Sentence.quote_def, ← Semiformula.quote_shift, h₁]

lemma IsTableOf.isTable {T : Theory L₁} [𝗘𝗤 _ ⪯ T] {π : DirectTranslation T L₂} {tbl : V}
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) : IsTable L₁ L₂ tbl where
  domain := by
    rw [h.domain]
    simp
  domain_shift := by
    rw [h.domain]
    exact shift_quote_semisentence _
  rel hr := by
    obtain ⟨k', R, rfl, rfl⟩ := hL₂.1 _ _ hr
    rw [h.rel R]
    exact Sentence.quote_isSemiformula _
  rel_shift hr := by
    obtain ⟨k', R, rfl, rfl⟩ := hL₂.1 _ _ hr
    rw [h.rel R]
    exact shift_quote_semisentence _
  func hf := by
    obtain ⟨k', F, rfl, rfl⟩ := hL₂.2 _ _ hf
    rw [h.func F]
    simpa using Sentence.quote_isSemiformula (π.func F).sentence
  func_shift hf := by
    obtain ⟨k', F, rfl, rfl⟩ := hL₂.2 _ _ hf
    rw [h.func F]
    exact shift_quote_semisentence _

end isTable

end FFL.FirstOrder.Arithmetic.Bootstrapping
