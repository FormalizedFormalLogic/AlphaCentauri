module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.Bootstrapping.Proof.Substitution

/-!
# Commutation of the internal translation with free-variable substitution

Along a table satisfying `IsTable`, the internal translation commutes with the substitution of
free variables by a vector of free variables. The module also records the coded set of the
translations of a set of formulas, its definability, and its behaviour under shift and under
free-variable substitution.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section generic

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma isSemitermVec_of_fvar {w : V} (n : V) (hw : ∀ i < len w, ∃ x, w.[i] = ^&x) :
    IsSemitermVec L (len w) n w :=
  IsSemitermVec.iff.mpr ⟨rfl, fun i hi ↦ by obtain ⟨x, hx⟩ := hw i hi; simp [hx]⟩

lemma termFvSubstVec_bvarVec (w s n : V) : termFvSubstVec L n w (bvarVec s n) = bvarVec s n := by
  have h₁ : IsUTermVec L n (bvarVec s n) :=
    (IsSemitermVec.bvarVec (L := L) (n := s + n) le_rfl).isUTerm
  apply nth_ext' n (by rw [len_termFvSubstVec h₁]) (by simp)
  intro i hi
  rw [nth_termFvSubstVec h₁ hi, nth_bvarVec _ _ _ hi, termFvSubst_bvar]

lemma termFvSubstVec_bvar_cons (w i s n : V) :
    termFvSubstVec L (n + 1) w (^#i ∷ bvarVec s n) = ^#i ∷ bvarVec s n := by
  have h₁ : IsUTermVec L n (bvarVec s n) :=
    (IsSemitermVec.bvarVec (L := L) (n := s + n) le_rfl).isUTerm
  rw [termFvSubstVec_cons (show IsUTerm L ^#i by simp) h₁, termFvSubst_bvar,
    termFvSubstVec_bvarVec]

lemma termFvSubstVec_pair {w s t : V} (hs : IsUTerm L s) (ht : IsUTerm L t) :
    termFvSubstVec L 2 w (?[s, t] : V) = ?[termFvSubst L w s, termFvSubst L w t] := by
  have h₁ : IsUTermVec L (0 + 1) (?[t] : V) := (IsUTermVec.empty (V := V) (L := L)).adjoin ht
  rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two], termFvSubstVec_cons hs h₁,
    termFvSubstVec_cons ht (IsUTermVec.empty (V := V) (L := L)),
    termFvSubstVec_nil]

lemma fvSubst_imp {w n p q : V} (hw : IsSemitermVec L (len w) n w) (hp : IsSemiformula L n p)
    (hq : IsSemiformula L n q) :
    fvSubst L w (imp L p q) = imp L (fvSubst L w p) (fvSubst L w q) := by
  unfold imp
  rw [fvSubst_or hp.isUFormula.neg hq.isUFormula, fvSubst_neg hw hp]

lemma fvSubst_qqAlls {w p : V} (hp : IsUFormula L p) (k : V) :
    fvSubst L w (qqAlls p k) = qqAlls (fvSubst L w p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [qqAlls_succ, fvSubst_all (isUFormula_qqAlls.mpr hp), ih, qqAlls_succ]

lemma fvSubst_qqConj_exists {w n : V} (ps : V) (hps : ∀ i < len ps, IsSemiformula L n ps.[i]) :
    ∃ qs, len qs = len ps ∧ (∀ i < len ps, qs.[i] = fvSubst L w ps.[i]) ∧
      fvSubst L w (^⋀ ps) = ^⋀ qs := by
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
    have h₄ : fvSubst L w (^⋀ (p ∷ ps)) = ^⋀ (fvSubst L w p ∷ qs) := by
      rw [qqConj_cons, qqConj_cons, fvSubst_and h₁.isUFormula h₃, hsh]
    have h₅ : ∀ i < len (p ∷ ps), (fvSubst L w p ∷ qs).[i] = fvSubst L w (p ∷ ps).[i] := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp
      · simpa using hq i (by simpa using hi)
    exact ⟨fvSubst L w p ∷ qs, by simp [hlen], h₅, h₄⟩

lemma fvSubst_relocate {w n i s p : V} (hw : IsSemitermVec L (len w) 0 w)
    (hp : IsSemiformula L (n + 1) p) :
    fvSubst L w (relocate L i s p) = relocate L i s (fvSubst L w p) := by
  have hw₁ : IsSemitermVec L (len w) (n + 1) w := hw.weaken (by simp)
  have hv : IsSemitermVec L (n + 1) (i + (s + n) + 1) (^#i ∷ bvarVec s n) :=
    IsSemitermVec.adjoin (IsSemitermVec.bvarVec (le_trans le_add_self le_self_add))
      (IsSemiterm.bvar.mpr (lt_of_le_of_lt le_self_add (lt_add_one _)))
  rw [relocate_eq_subst hp, relocate_eq_subst (hp.fvSubst hw₁), fvSubst_subst hw hv hp,
    termFvSubstVec_bvar_cons]

end generic

section table

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

lemma IsTable.fvSubst_domainAt {tbl w i m : V} (hT : IsTable L₁ L₂ tbl) (hi : i < m) :
    fvSubst L₁ w (domainAt L₁ tbl i) = domainAt L₁ tbl i :=
  fvSubst_eq_self_of_shift (hT.isSemiformula_domainAt hi) (hT.shift_domainAt i)

lemma IsTable.fvSubst_funcTail {tbl w k f m : V} (hT : IsTable L₁ L₂ tbl) (hf : L₂.IsFunc k f)
    (hk : k < m) : fvSubst L₁ w (funcTail L₁ tbl k f) = funcTail L₁ tbl k f :=
  fvSubst_eq_self_of_shift (hT.isSemiformula_funcTail hf hk) (hT.shift_funcTail hf)

lemma IsTable.fvSubst_qqConj_guardVec {tbl n m k s w u u' : V} (hT : IsTable L₁ L₂ tbl)
    (hw : ∀ i < len w, ∃ x, w.[i] = ^&x) (hk : k ≤ m) (hs : s + n ≤ m)
    (hu : ∀ i < k, IsSemiformula L₁ (n + 1) u.[i]) (hu' : ∀ i < k, u'.[i] = fvSubst L₁ w u.[i]) :
    fvSubst L₁ w (^⋀ guardVec L₁ tbl s u k) = ^⋀ guardVec L₁ tbl s u' k := by
  obtain ⟨qs, hlen, hq, hsh⟩ := fvSubst_qqConj_exists (L := L₁) (w := w) (guardVec L₁ tbl s u k)
    (fun j hj ↦ hT.isSemiformula_guardVec hk hs hu (by simpa using hj))
  rw [hsh]
  congr 1
  apply nth_ext' k (by simp [hlen]) (by simp)
  intro i hi
  rw [hq i (by simpa using hi), nth_guardVec tbl s u k i hi, nth_guardVec tbl s u' k i hi, hu' i hi,
    fvSubst_and (hT.isSemiformula_domainAt (lt_of_lt_of_le hi hk)).isUFormula
      ((hu i hi).relocate (lt_of_lt_of_le hi hk) hs).isUFormula,
    hT.fvSubst_domainAt (lt_of_lt_of_le hi hk),
    fvSubst_relocate (isSemitermVec_of_fvar (L := L₁) 0 hw) (hu i hi)]

lemma varEqual_termFvSubst {tbl w n t : V} (hT : IsTable L₁ L₂ tbl)
    (hw : ∀ i < len w, ∃ x, w.[i] = ^&x) (ht : IsSemiterm L₂ n t) :
    varEqual L₁ L₂ tbl (termFvSubst L₂ w t) = fvSubst L₁ w (varEqual L₁ L₂ tbl t) := by
  have h₁ : ∀ t, IsSemiterm L₂ n t →
      varEqual L₁ L₂ tbl (termFvSubst L₂ w t) = fvSubst L₁ w (varEqual L₁ L₂ tbl t) := by
    apply IsSemiterm.sigma1_induction
      (P := fun t ↦ varEqual L₁ L₂ tbl (termFvSubst L₂ w t) = fvSubst L₁ w (varEqual L₁ L₂ tbl t))
    · definability
    · intro z _
      rw [termFvSubst_bvar, varEqual_bvar, fvSubst_rel isRel_eq_quote
          (IsUTermVec.pair (show IsUTerm L₁ (^#0 : V) by simp)
            (show IsUTerm L₁ (^#(z + 1) : V) by simp)),
        termFvSubstVec_pair (show IsUTerm L₁ (^#0 : V) by simp)
          (show IsUTerm L₁ (^#(z + 1) : V) by simp),
        termFvSubst_bvar, termFvSubst_bvar]
    · intro x
      by_cases hx : x < len w
      · obtain ⟨y, hy⟩ := hw x hx
        have h₂ : termFvSubst L₂ w ^&x = ^&y := by rw [termFvSubst_fvar, ite_eq_left hx, hy]
        have h₃ : termFvSubst L₁ w ^&x = ^&y := by rw [termFvSubst_fvar, ite_eq_left hx, hy]
        rw [h₂, varEqual_fvar, varEqual_fvar, fvSubst_rel isRel_eq_quote
          (IsUTermVec.pair (show IsUTerm L₁ (^#0 : V) by simp)
            (show IsUTerm L₁ (^&x : V) by simp)),
          termFvSubstVec_pair (show IsUTerm L₁ (^#0 : V) by simp)
            (show IsUTerm L₁ (^&x : V) by simp),
          termFvSubst_bvar, h₃]
      · have h₂ : termFvSubst L₂ w ^&x = ^&x := by rw [termFvSubst_fvar, ite_eq_right hx]
        rw [h₂, varEqual_fvar, fvSubst_rel isRel_eq_quote
          (IsUTermVec.pair (show IsUTerm L₁ (^#0 : V) by simp)
            (show IsUTerm L₁ (^&x : V) by simp)),
          termFvSubstVec_pair (show IsUTerm L₁ (^#0 : V) by simp)
            (show IsUTerm L₁ (^&x : V) by simp),
          termFvSubst_bvar, termFvSubst_fvar, ite_eq_right hx]
    · intro k f v hf hv ih
      have h₂ := hT.isSemiformula_funcBody hf hv (fun i hi ↦ IsSemiformula.varEqual hT (hv.nth hi))
      have h₃ := (IsSemiformula.imp.mp h₂).1
      have h₄ := hT.isSemiformula_funcTail hf (show k < n + 1 + k by simp)
      have h₅ : k ≤ n + 1 + k := by simp
      have h₆ : k + 1 + n ≤ n + 1 + k := (add_arity_comm k n).le
      have hvw : IsUTermVec L₂ k (termFvSubstVec L₂ k w v) :=
        (IsSemitermVec.termFvSubstVec (isSemitermVec_of_fvar n hw) hv).isUTerm
      have h₇ : ∀ i < k, (varEqualVec L₁ L₂ tbl k (termFvSubstVec L₂ k w v)).[i] =
          fvSubst L₁ w (varEqualVec L₁ L₂ tbl k v).[i] := by
        intro i hi
        rw [nth_varEqualVec hvw hi, nth_termFvSubstVec hv.isUTerm hi, nth_varEqualVec hv.isUTerm hi]
        exact ih i hi
      rw [termFvSubst_func hf hv.isUTerm,
        varEqual_func hf hvw,
        varEqual_func hf hv.isUTerm,
        fvSubst_qqAlls (IsSemiformula.imp.mpr ⟨h₃, h₄⟩).isUFormula k,
        fvSubst_imp (isSemitermVec_of_fvar (L := L₁) (n + 1 + k) hw) h₃ h₄,
        hT.fvSubst_funcTail hf (show k < n + 1 + k by simp),
        hT.fvSubst_qqConj_guardVec hw h₅ h₆ (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₇]
  exact h₁ t ht

lemma fvSubst_translateRel {tbl n k R v w : V} (hT : IsTable L₁ L₂ tbl)
    (hw : ∀ i < len w, ∃ x, w.[i] = ^&x) (hR : L₂.IsRel k R) (hv : IsSemitermVec L₂ k n v) :
    fvSubst L₁ w (Bootstrapping.translateRel L₁ L₂ tbl k R v) =
      Bootstrapping.translateRel L₁ L₂ tbl k R (termFvSubstVec L₂ k w v) := by
  have h₁ : k ≤ n + k := by simp
  have h₂ : k + n ≤ n + k := (add_comm k n).le
  have h₃ : IsSemiformula L₁ (n + k)
      (^⋀ guardVec L₁ tbl k (varEqualVec L₁ L₂ tbl k v) k) :=
    IsSemiformula.qqConj_guardVec hT h₁ h₂ (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi)
  have h₄ : IsSemiformula L₁ (n + k) (tableRel tbl k R) := (hT.rel hR).of_le h₁
  have h₅ : ∀ i < k, (varEqualVec L₁ L₂ tbl k (termFvSubstVec L₂ k w v)).[i] =
      fvSubst L₁ w (varEqualVec L₁ L₂ tbl k v).[i] := by
    intro i hi
    rw [nth_varEqualVec (IsSemitermVec.termFvSubstVec (isSemitermVec_of_fvar n hw) hv).isUTerm hi,
      nth_termFvSubstVec hv.isUTerm hi, nth_varEqualVec hv.isUTerm hi]
    exact varEqual_termFvSubst hT hw (hv.nth hi)
  unfold Bootstrapping.translateRel
  rw [fvSubst_qqAlls (IsSemiformula.imp.mpr ⟨h₃, h₄⟩).isUFormula k,
    fvSubst_imp (isSemitermVec_of_fvar (L := L₁) (n + k) hw) h₃ h₄,
    hT.fvSubst_qqConj_guardVec hw h₁ h₂ (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₅,
    fvSubst_eq_self_of_shift h₄ (hT.rel_shift hR)]

lemma translate_fvSubst {tbl w n p : V} (hT : IsTable L₁ L₂ tbl)
    (hw : ∀ i < len w, ∃ x, w.[i] = ^&x) (hp : IsSemiformula L₂ n p) :
    translate L₁ L₂ tbl (fvSubst L₂ w p) = fvSubst L₁ w (translate L₁ L₂ tbl p) := by
  apply IsSemiformula.sigma1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    rw [fvSubst_rel hR hv.isUTerm,
      translate_rel hR (IsSemitermVec.termFvSubstVec (isSemitermVec_of_fvar n hw) hv).isUTerm,
      translate_rel hR hv.isUTerm, fvSubst_translateRel hT hw hR hv]
  · intro n k R v hR hv
    rw [fvSubst_nrel hR hv.isUTerm,
      translate_nrel hR (IsSemitermVec.termFvSubstVec (isSemitermVec_of_fvar n hw) hv).isUTerm,
      translate_nrel hR hv.isUTerm,
      fvSubst_neg (isSemitermVec_of_fvar (L := L₁) n hw) (IsSemiformula.translateRel hT hR hv),
      fvSubst_translateRel hT hw hR hv]
  · intro n
    simp
  · intro n
    simp
  · intro n p q hp hq ihp ihq
    rw [fvSubst_and hp.isUFormula hq.isUFormula,
      translate_and (IsSemiformula.fvSubst (isSemitermVec_of_fvar n hw) hp).isUFormula
        (IsSemiformula.fvSubst (isSemitermVec_of_fvar n hw) hq).isUFormula, ihp, ihq,
      translate_and hp.isUFormula hq.isUFormula,
      fvSubst_and (IsSemiformula.translate hT hp).isUFormula
        (IsSemiformula.translate hT hq).isUFormula]
  · intro n p q hp hq ihp ihq
    rw [fvSubst_or hp.isUFormula hq.isUFormula,
      translate_or (IsSemiformula.fvSubst (isSemitermVec_of_fvar n hw) hp).isUFormula
        (IsSemiformula.fvSubst (isSemitermVec_of_fvar n hw) hq).isUFormula, ihp, ihq,
      translate_or hp.isUFormula hq.isUFormula,
      fvSubst_or (IsSemiformula.translate hT hp).isUFormula
        (IsSemiformula.translate hT hq).isUFormula]
  · intro n p hp ih
    have h₁ : IsSemiformula L₁ (n + 1) (domainAt L₁ tbl 0) :=
      hT.isSemiformula_domainAt (by simp)
    have h₂ : IsSemiformula L₁ (n + 1) (translate L₁ L₂ tbl p) :=
      IsSemiformula.translate hT hp
    have h₃ : fvSubst L₁ w (domainAt L₁ tbl 0) = domainAt L₁ tbl 0 :=
      hT.fvSubst_domainAt (m := n + 1) (by simp)
    rw [fvSubst_all hp.isUFormula,
      translate_all (IsSemiformula.fvSubst (isSemitermVec_of_fvar (n + 1) hw) hp).isUFormula, ih,
      translate_all hp.isUFormula, fvSubst_all (IsSemiformula.imp.mpr ⟨h₁, h₂⟩).isUFormula,
      fvSubst_imp (isSemitermVec_of_fvar (L := L₁) (n + 1) hw) h₁ h₂, h₃]
  · intro n p hp ih
    have h₁ : IsSemiformula L₁ (n + 1) (domainAt L₁ tbl 0) :=
      hT.isSemiformula_domainAt (by simp)
    have h₂ : IsSemiformula L₁ (n + 1) (translate L₁ L₂ tbl p) :=
      IsSemiformula.translate hT hp
    have h₃ : fvSubst L₁ w (domainAt L₁ tbl 0) = domainAt L₁ tbl 0 :=
      hT.fvSubst_domainAt (m := n + 1) (by simp)
    rw [fvSubst_exs hp.isUFormula,
      translate_exs (IsSemiformula.fvSubst (isSemitermVec_of_fvar (n + 1) hw) hp).isUFormula, ih,
      translate_exs hp.isUFormula, fvSubst_exs (IsSemiformula.and.mpr ⟨h₁, h₂⟩).isUFormula,
      fvSubst_and h₁.isUFormula h₂.isUFormula, h₃]

end table

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

lemma mem_translateSet_iff {tbl s x : V} :
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
    exact ⟨fun y hy ↦ mem_translateSet_iff.mp hy, fun x hx ↦ mem_translateSet_iff.mpr ⟨x, hx, rfl⟩⟩
  · rintro ⟨h₁, h₂⟩
    apply mem_ext
    intro y
    constructor
    · intro hy
      exact mem_translateSet_iff.mpr (h₁ y hy)
    · intro hy
      obtain ⟨p, hp, rfl⟩ := mem_translateSet_iff.mp hy
      exact h₂ p hp

instance translateSet.defined : 𝚺ᴬ₁-Function₂[V] translateSet L₁ L₂ via translateSetGraph L₁ L₂ :=
  .mk fun v ↦ by simp [translateSetGraph, translateSet_graph]

instance translateSet.definable : 𝚺ᴬ₁-Function₂[V] translateSet L₁ L₂ :=
  translateSet.defined.to_definable

instance translateSet.definable' : Γᴬ_[m + 1]-Function₂[V] translateSet L₁ L₂ :=
  translateSet.definable.of_sigmaOne

end graph

lemma translateSet_empty (tbl : V) : translateSet L₁ L₂ tbl ∅ = ∅ := by
  apply mem_ext
  intro x
  simp [mem_translateSet_iff]

lemma translateSet_insert (tbl p s : V) :
    translateSet L₁ L₂ tbl (insert p s) =
      insert (translate L₁ L₂ tbl p) (translateSet L₁ L₂ tbl s) := by
  apply mem_ext
  intro x
  simp only [mem_translateSet_iff, mem_bitInsert_iff]
  constructor
  · rintro ⟨q, (rfl | hq), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨q, hq, rfl⟩
  · rintro (rfl | ⟨q, hq, rfl⟩)
    · exact ⟨p, Or.inl rfl, rfl⟩
    · exact ⟨q, Or.inr hq, rfl⟩

lemma translateSet_union (tbl s t : V) :
    translateSet L₁ L₂ tbl (s ∪ t) = translateSet L₁ L₂ tbl s ∪ translateSet L₁ L₂ tbl t := by
  apply mem_ext
  intro x
  simp only [mem_translateSet_iff, mem_cup_iff]
  constructor
  · rintro ⟨q, hq | hq, rfl⟩
    · exact Or.inl ⟨q, hq, rfl⟩
    · exact Or.inr ⟨q, hq, rfl⟩
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact ⟨q, Or.inl hq, rfl⟩
    · exact ⟨q, Or.inr hq, rfl⟩

lemma translateSet_mono {tbl s s' : V} (h : s ⊆ s') :
    translateSet L₁ L₂ tbl s ⊆ translateSet L₁ L₂ tbl s' := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := mem_translateSet_iff.mp hx
  exact mem_translateSet_iff.mpr ⟨p, h hp, rfl⟩

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
  apply mem_ext
  intro x
  rw [mem_fvSubstImage_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨p, hp, rfl⟩ := mem_translateSet_iff.mp hq
    exact mem_setShift_iff.mpr ⟨_, mem_translateSet_iff.mpr ⟨p, hp, rfl⟩, key p hp⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_setShift_iff.mp hx
    obtain ⟨p, hp, rfl⟩ := mem_translateSet_iff.mp hy
    exact ⟨_, mem_translateSet_iff.mpr ⟨p, hp, rfl⟩, (key p hp).symm⟩

end translateSet

end FFL.FirstOrder.Arithmetic.Bootstrapping
