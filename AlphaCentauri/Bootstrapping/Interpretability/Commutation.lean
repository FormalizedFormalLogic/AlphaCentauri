module

public import AlphaCentauri.Bootstrapping.Interpretability.Translation
public import AlphaCentauri.Bootstrapping.Proof.Substitution
public import AlphaCentauri.Bootstrapping.Syntax.SubstCongruence

/-!
# Commutation of the internal translation

Along a table satisfying `IsTable`, the internal translation sends negation to negation and shift
to shift, and it sends a coded $L_2$-formula to a coded $L_1$-formula of the same arity. It
commutes with the substitution of a vector of variables for the variables of a formula, and with
the substitution of free variables by a vector of free variables.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Negation, shift and arity -/

section negShift

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

lemma exists_map_qqConj {n : V} {f : V → V} [𝚺ᴬ₁-Function₁ f]
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q → f (p ^⋏ q) = f p ^⋏ f q) (hverum : f ^⊤ = ^⊤)
    (ps : V) (hps : ∀ i < len ps, IsSemiformula L n ps.[i]) :
    ∃ qs, len qs = len ps ∧ (∀ i < len ps, qs.[i] = f ps.[i]) ∧ f (^⋀ ps) = ^⋀ qs := by
  revert hps
  induction ps using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => intro _; exact ⟨0, by simp [hverum]⟩
  case adjoin p ps ih =>
    intro hps
    have h₁ : IsSemiformula L n p := by simpa using hps 0 (by simp)
    have h₂ : ∀ i < len ps, IsSemiformula L n ps.[i] := fun i hi ↦ by
      simpa using hps (i + 1) (by simpa using hi)
    obtain ⟨qs, hlen, hq, hsh⟩ := ih h₂
    refine ⟨f p ∷ qs, by simp [hlen], fun i hi ↦ ?_, ?_⟩
    · rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp
      · simpa using hq i (by simpa using hi)
    · rw [qqConj_cons, qqConj_cons, hand p _ h₁.isUFormula (qqConj_semiformula.mpr h₂).isUFormula,
        hsh]

lemma shift_imp {n p q : V} (hp : IsSemiformula L n p) (hq : IsSemiformula L n q) :
    shift L (imp L p q) = imp L (shift L p) (shift L q) := by
  unfold imp
  rw [shift_or hp.isUFormula.neg hq.isUFormula, shift_neg hp]

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

lemma IsTable.isSemiformula_domainAt_zero {tbl : V} (hT : IsTable L₁ L₂ tbl) (n : V) :
    IsSemiformula L₁ (n + 1) (domainAt L₁ tbl 0) := hT.isSemiformula_domainAt (by simp)

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

lemma IsTable.map_qqConj_guardVec {f : V → V} [𝚺ᴬ₁-Function₁ f] {tbl n m k s u u' : V}
    (hT : IsTable L₁ L₂ tbl)
    (hand : ∀ p q, IsUFormula L₁ p → IsUFormula L₁ q → f (p ^⋏ q) = f p ^⋏ f q)
    (hverum : f ^⊤ = ^⊤) (hk : k ≤ m) (hs : s + n ≤ m)
    (hu : ∀ i < k, IsSemiformula L₁ (n + 1) u.[i])
    (hdomain : ∀ i < k, f (domainAt L₁ tbl i) = domainAt L₁ tbl i)
    (hrelocate : ∀ i < k, f (relocate L₁ i s u.[i]) = relocate L₁ i s u'.[i]) :
    f (^⋀ guardVec L₁ tbl s u k) = ^⋀ guardVec L₁ tbl s u' k := by
  obtain ⟨qs, hlen, hq, hsh⟩ := exists_map_qqConj hand hverum (guardVec L₁ tbl s u k)
    (n := m) fun j hj ↦ hT.isSemiformula_guardVec hk hs hu (by simpa using hj)
  rw [hsh]
  congr 1
  apply nth_ext' k (by simp [hlen]) (by simp)
  intro i hi
  rw [hq i (by simpa using hi), nth_guardVec tbl s u k i hi, nth_guardVec tbl s u' k i hi,
    hand _ _ (hT.isSemiformula_domainAt (lt_of_lt_of_le hi hk)).isUFormula
      ((hu i hi).relocate (lt_of_lt_of_le hi hk) hs).isUFormula, hdomain i hi, hrelocate i hi]

lemma IsTable.shift_qqConj_guardVec {tbl n m k s w w' : V} (hT : IsTable L₁ L₂ tbl) (hk : k ≤ m)
    (hs : s + n ≤ m) (hw : ∀ i < k, IsSemiformula L₁ (n + 1) w.[i])
    (hw' : ∀ i < k, w'.[i] = shift L₁ w.[i]) :
    shift L₁ (^⋀ guardVec L₁ tbl s w k) = ^⋀ guardVec L₁ tbl s w' k :=
  hT.map_qqConj_guardVec (fun _ _ ↦ shift_and) (by simp) hk hs hw (fun i _ ↦ hT.shift_domainAt i)
    fun i hi ↦ by rw [shift_relocate (hw i hi) (lt_of_lt_of_le hi hk) hs, hw' i hi]

@[simp] lemma isRel_eq_quote : L₁.IsRel 2 (Encodable.encode (Language.Eq.eq : L₁.Rel 2) : V) :=
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
      simp [hz]
    · intro x
      simp
    · intro k f v hf hv ih
      rw [varEqual_func hf hv.isUTerm]
      exact IsSemiformula.qqAlls (hT.isSemiformula_funcBody hf hv ih)
  exact h₁ t ht

lemma IsTable.isSemiformula_varEqualVec_nth {tbl n k v i : V} (hT : IsTable L₁ L₂ tbl)
    (hv : IsSemitermVec L₂ k n v) (hi : i < k) :
    IsSemiformula L₁ (n + 1) (varEqualVec L₁ L₂ tbl k v).[i] := by
  rw [nth_varEqualVec hv.isUTerm hi]
  exact IsSemiformula.varEqual hT (hv.nth hi)

lemma IsTable.isSemiformula_relBody {tbl n k R v : V} (hT : IsTable L₁ L₂ tbl) (hR : L₂.IsRel k R)
    (hv : IsSemitermVec L₂ k n v) :
    IsSemiformula L₁ (n + k)
      (imp L₁ (^⋀ guardVec L₁ tbl k (varEqualVec L₁ L₂ tbl k v) k) (tableRel tbl k R)) :=
  IsSemiformula.imp.mpr
    ⟨IsSemiformula.qqConj_guardVec hT (by simp) (add_comm k n).le
      fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi, (hT.rel hR).of_le (by simp)⟩

lemma IsSemiformula.translateRel {tbl n k R v : V} (hT : IsTable L₁ L₂ tbl) (hR : L₂.IsRel k R)
    (hv : IsSemitermVec L₂ k n v) :
    IsSemiformula L₁ n (Bootstrapping.translateRel L₁ L₂ tbl k R v) :=
  IsSemiformula.qqAlls (hT.isSemiformula_relBody hR hv)

lemma IsSemiformula.translate {tbl n p : V} (hT : IsTable L₁ L₂ tbl) (hp : IsSemiformula L₂ n p) :
    IsSemiformula L₁ n (Bootstrapping.translate L₁ L₂ tbl p) := by
  have hd := hT.isSemiformula_domainAt_zero
  apply IsSemiformula.sigma1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    simpa [hR, hv.isUTerm] using IsSemiformula.translateRel hT hR hv
  · intro n k R v hR hv
    simpa [hR, hv.isUTerm] using (IsSemiformula.translateRel hT hR hv).neg
  · intro n
    simp
  · intro n
    simp
  · intro n p q hp hq ihp ihq
    simp [*, hp.isUFormula, hq.isUFormula]
  · intro n p q hp hq ihp ihq
    simp [*, hp.isUFormula, hq.isUFormula]
  · intro n p hp ih
    simp [*, hp.isUFormula]
  · intro n p hp ih
    simp [*, hp.isUFormula]

lemma IsUFormula.translate {tbl p : V} (hT : IsTable L₁ L₂ tbl) (hp : IsUFormula L₂ p) :
    IsUFormula L₁ (Bootstrapping.translate L₁ L₂ tbl p) :=
  (IsSemiformula.translate hT hp.isSemiformula).isUFormula

lemma translate_neg {tbl n p : V} (hT : IsTable L₁ L₂ tbl) (hp : IsSemiformula L₂ n p) :
    translate L₁ L₂ tbl (neg L₂ p) = neg L₁ (translate L₁ L₂ tbl p) := by
  have hd := (hT.isSemiformula_domainAt_zero 0).isUFormula
  apply IsSemiformula.sigma1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    simp [hR, hv.isUTerm]
  · intro n k R v hR hv
    simp [hR, hv.isUTerm, (IsSemiformula.translateRel hT hR hv).isUFormula]
  · intro n
    simp
  · intro n
    simp
  · intro n p q hp hq ihp ihq
    simp [*, hp.isUFormula, hq.isUFormula, IsUFormula.translate hT]
  · intro n p q hp hq ihp ihq
    simp [*, hp.isUFormula, hq.isUFormula, IsUFormula.translate hT]
  · intro n p hp ih
    simp [*, imp, hp.isUFormula, IsUFormula.translate hT]
  · intro n p hp ih
    simp [*, imp, hp.isUFormula, IsUFormula.translate hT]

lemma nth_varEqualVec_map {tbl k v v' : V} {F : V → V} (hv : IsUTermVec L₂ k v)
    (hv' : IsUTermVec L₂ k v')
    (H : ∀ i < k, varEqual L₁ L₂ tbl v'.[i] = F (varEqual L₁ L₂ tbl v.[i])) :
    ∀ i < k, (varEqualVec L₁ L₂ tbl k v').[i] = F (varEqualVec L₁ L₂ tbl k v).[i] := fun i hi ↦ by
  rw [nth_varEqualVec hv' hi, nth_varEqualVec hv hi, H i hi]

lemma varEqual_termShift {tbl n t : V} (hT : IsTable L₁ L₂ tbl) (ht : IsSemiterm L₂ n t) :
    varEqual L₁ L₂ tbl (termShift L₂ t) = shift L₁ (varEqual L₁ L₂ tbl t) := by
  have h₁ : ∀ t, IsSemiterm L₂ n t →
      varEqual L₁ L₂ tbl (termShift L₂ t) = shift L₁ (varEqual L₁ L₂ tbl t) := by
    apply IsSemiterm.sigma1_induction
      (P := fun t ↦ varEqual L₁ L₂ tbl (termShift L₂ t) = shift L₁ (varEqual L₁ L₂ tbl t))
    · definability
    · intro z hz
      simp
    · intro x
      simp
    · intro k f v hf hv ih
      have h₂ :=
        hT.isSemiformula_funcBody hf hv (fun i hi ↦ IsSemiformula.varEqual hT (hv.nth hi))
      obtain ⟨h₃, h₄⟩ := IsSemiformula.imp.mp h₂
      have h₅ := nth_varEqualVec_map (tbl := tbl) (F := shift L₁) hv.isUTerm
        hv.termShiftVec.isUTerm fun i hi ↦ by rw [nth_termShiftVec hv.isUTerm hi]; exact ih i hi
      rw [termShift_func hf hv.isUTerm, varEqual_func hf hv.termShiftVec.isUTerm,
        varEqual_func hf hv.isUTerm, shift_qqAlls h₂.isUFormula k, shift_imp h₃ h₄,
        hT.shift_qqConj_guardVec (by simp) (add_arity_comm k n).le
          (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₅, hT.shift_funcTail hf]
  exact h₁ t ht

lemma shift_translateRel {tbl n k R v : V} (hT : IsTable L₁ L₂ tbl) (hR : L₂.IsRel k R)
    (hv : IsSemitermVec L₂ k n v) :
    shift L₁ (Bootstrapping.translateRel L₁ L₂ tbl k R v) =
      Bootstrapping.translateRel L₁ L₂ tbl k R (termShiftVec L₂ k v) := by
  obtain ⟨h₁, h₂⟩ := IsSemiformula.imp.mp (hT.isSemiformula_relBody hR hv)
  have h₃ := nth_varEqualVec_map (tbl := tbl) (F := shift L₁) hv.isUTerm hv.termShiftVec.isUTerm
    fun i hi ↦ by rw [nth_termShiftVec hv.isUTerm hi]; exact varEqual_termShift hT (hv.nth hi)
  unfold Bootstrapping.translateRel
  rw [shift_qqAlls (hT.isSemiformula_relBody hR hv).isUFormula k, shift_imp h₁ h₂,
    hT.shift_qqConj_guardVec (by simp) (add_comm k n).le
      (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₃, hT.rel_shift hR]

lemma translate_shift {tbl n p : V} (hT : IsTable L₁ L₂ tbl) (hp : IsSemiformula L₂ n p) :
    translate L₁ L₂ tbl (shift L₂ p) = shift L₁ (translate L₁ L₂ tbl p) := by
  have hd := hT.isSemiformula_domainAt_zero
  have hdu := (hd 0).isUFormula
  apply IsSemiformula.sigma1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    simp [hR, hv.isUTerm, hv.termShiftVec.isUTerm, shift_translateRel hT hR hv]
  · intro n k R v hR hv
    simp [hR, hv.isUTerm, hv.termShiftVec.isUTerm, shift_neg (IsSemiformula.translateRel hT hR hv),
      shift_translateRel hT hR hv]
  · intro n
    simp
  · intro n
    simp
  · intro n p q hp hq ihp ihq
    simp [*, hp.isUFormula, hq.isUFormula, IsUFormula.translate hT]
  · intro n p q hp hq ihp ihq
    simp [*, hp.isUFormula, hq.isUFormula, IsUFormula.translate hT]
  · intro n p hp ih
    simp [*, hp.isUFormula, IsUFormula.translate hT, hT.shift_domainAt,
      shift_imp (hd n) (IsSemiformula.translate hT hp)]
  · intro n p hp ih
    simp [*, hp.isUFormula, IsUFormula.translate hT, hT.shift_domainAt]

end table

end negShift

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

/-! ## Substitution of variables -/

section substVars

section generic

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma IsSemitermVec.of_var {L' : Language} [L'.Encodable] [L'.LORDefinable] {n m w : V}
    (hw : IsSemitermVec L n m w) (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) :
    IsSemitermVec L' n m w := by
  refine IsSemitermVec.iff.mpr ⟨hw.lh, fun i hi ↦ ?_⟩
  have h := hw.nth hi
  rcases hvar i hi with ⟨z, hz⟩ | ⟨x, hx⟩
  · rw [hz] at h
    rw [hz]
    exact IsSemiterm.bvar.mpr (IsSemiterm.bvar.mp h)
  · rw [hx]
    exact IsSemiterm.fvar _ _

lemma termSubst_bvarVec_termBShift (k : V) {m t : V} (ht : IsSemiterm L m t) :
    termSubst L (bvarVec k (m + 1)) (termBShift L t) = termSubst L (bvarVec (k + 1) m) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termBShift_bvar, termSubst_bvar, termSubst_bvar, nth_bvarVec _ _ _ (by simpa using hz),
      nth_bvarVec _ _ _ hz]
    congr 1
    simp only [add_comm, add_left_comm]
  · intro x; simp
  · intro k' f v hf hv ih
    rw [termBShift_func hf hv.isUTerm, termSubst_func hf hv.termBShiftVec.isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k' (len_termSubstVec hv.termBShiftVec.isUTerm) (len_termSubstVec hv.isUTerm)
    intro i hi
    rw [nth_termSubstVec hv.termBShiftVec.isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi, ih i hi]

lemma termBShift_termSubst_bvarVec (k : V) {m t : V} (ht : IsSemiterm L m t) :
    termBShift L (termSubst L (bvarVec k m) t) = termSubst L (bvarVec (k + 1) m) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termSubst_bvar, termSubst_bvar, nth_bvarVec _ _ _ hz, nth_bvarVec _ _ _ hz, termBShift_bvar]
    congr 1
    simp only [add_assoc, add_comm, add_left_comm]
  · intro x; simp
  · intro k' f v hf hv ih
    have hs : IsSemitermVec L k' (m + k) (termSubstVec L k' (bvarVec k m) v) :=
      (IsSemitermVec.bvarVec (k := m) (n := m + k) (j := k) (add_comm k m).le).termSubstVec hv
    rw [termSubst_func hf hv.isUTerm, termBShift_func hf hs.isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k' (len_termBShiftVec hs.isUTerm) (len_termSubstVec hv.isUTerm)
    intro i hi
    simp only [nth_termBShiftVec hs.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
    exact ih i hi

lemma termSubst_bvarVec_zero {m t : V} (ht : IsSemiterm L m t) : termSubst L (bvarVec 0 m) t = t :=
  termSubst_eq_self ht fun i hi ↦ by rw [nth_bvarVec _ _ _ hi, zero_add]

@[simp] lemma nth_qVec_zero (w : V) : (qVec L w).[0] = ^#0 := by simp [qVec]

lemma nth_qVec_succ_semi {m n w i : V} (hw : IsSemitermVec L n m w) (hi : i < n) :
    (qVec L w).[i + 1] = termBShift L w.[i] := by
  have h₁ : IsUTermVec L (len w) w := by rw [hw.lh]; exact hw.isUTerm
  rw [qVec, nth_adjoin_succ, nth_termBShiftVec h₁ (by rw [hw.lh]; exact hi)]

lemma qVec_eq_of_var {L' : Language} [L'.Encodable] [L'.LORDefinable] {n m w : V}
    (hw : IsSemitermVec L n m w) (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) :
    qVec L w = qVec L' w := by
  have h₁ : IsUTermVec L (len w) w := by rw [hw.lh]; exact hw.isUTerm
  have h₂ : IsUTermVec L' (len w) w := by rw [hw.lh]; exact (hw.of_var (L' := L') hvar).isUTerm
  have h₃ : termBShiftVec L (len w) w = termBShiftVec L' (len w) w := by
    apply nth_ext' (len w) (len_termBShiftVec h₁) (len_termBShiftVec h₂)
    intro i hi
    rw [nth_termBShiftVec h₁ hi, nth_termBShiftVec h₂ hi]
    rcases hvar i (by rw [hw.lh] at hi; exact hi) with ⟨z, hz⟩ | ⟨x, hx⟩
    · rw [hz, termBShift_bvar, termBShift_bvar]
    · rw [hx, termBShift_fvar, termBShift_fvar]
  unfold qVec
  rw [h₃]

lemma hvar_qVec {n m w : V} (hw : IsSemitermVec L n m w)
    (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) :
    ∀ i < n + 1, (∃ z, (qVec L w).[i] = ^#z) ∨ (∃ x, (qVec L w).[i] = ^&x) := by
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · exact Or.inl ⟨0, nth_qVec_zero w⟩
  · have hi' : i < n := by simpa using hi
    rcases hvar i hi' with ⟨z, hz⟩ | ⟨x, hx⟩
    · exact Or.inl ⟨z + 1, by rw [nth_qVec_succ_semi hw hi', hz, termBShift_bvar]⟩
    · exact Or.inr ⟨x, by rw [nth_qVec_succ_semi hw hi', hx, termBShift_fvar]⟩

lemma exists_vec_shift {n m w : V} (hw : IsSemitermVec L n m w) (k : V) :
    ∃ v, IsSemitermVec L (n + k) (m + k) v ∧ (∀ i < k, v.[i] = ^#i) ∧
      ∀ j < n, v.[k + j] = termSubst L (bvarVec k m) w.[j] := by
  have hsub : IsSemitermVec L m (m + k) (bvarVec k m) :=
    IsSemitermVec.bvarVec (j := k) (k := m) (n := m + k) (add_comm k m).le
  have hrest : IsSemitermVec L n (m + k) (termSubstVec L n (bvarVec k m) w) :=
    hsub.termSubstVec hw
  have hl : len (termSubstVec L n (bvarVec k m) w) = n := len_termSubstVec hw.isUTerm
  obtain ⟨v, hvl, hv₁, hv₂⟩ := exists_vec_bvar_append (termSubstVec L n (bvarVec k m) w) k
  refine ⟨v, IsSemitermVec.iff.mpr ⟨by rw [hvl, hl, add_comm], fun i hi ↦ ?_⟩, hv₁, fun j hj ↦ ?_⟩
  · rcases lt_or_ge i k with hik | hik
    · rw [hv₁ i hik]
      exact IsSemiterm.bvar.mpr (lt_of_lt_of_le hik le_add_self)
    · obtain ⟨j, rfl⟩ := exists_add_of_le hik
      have hj' : j < n := by
        rw [add_comm n k] at hi
        exact (add_lt_add_iff_left k).mp hi
      rw [hv₂ j (by rw [hl]; exact hj'), nth_termSubstVec hw.isUTerm hj']
      exact hsub.termSubst (hw.nth hj')
  · rw [hv₂ j (by rw [hl]; exact hj), nth_termSubstVec hw.isUTerm hj]

lemma subst_eq_self_of_le {m k p w : V} (hp : IsSemiformula L m p) (hw : IsUTermVec L k w)
    (hk : m ≤ k) (H : ∀ i < m, w.[i] = ^#i) : subst L w p = p := by
  have h₁ : IsSemitermVec L m m (bvarVec 0 m) := IsSemitermVec.bvarVec (by simp)
  calc subst L w p = subst L (bvarVec 0 m) p := by
        apply subst_congr hp hw h₁.isUTerm hk le_rfl
        intro i hi
        rw [H i hi, nth_bvarVec _ _ _ hi, zero_add]
    _ = p := subst_eq_self hp h₁ fun i hi ↦ by rw [nth_bvarVec _ _ _ hi, zero_add]

lemma subst_imp {n m w p q : V} (hw : IsSemitermVec L n m w) (hp : IsSemiformula L n p)
    (hq : IsSemiformula L n q) : subst L w (imp L p q) = imp L (subst L w p) (subst L w q) := by
  unfold imp
  rw [substs_or hp.isUFormula.neg hq.isUFormula, substs_neg hp hw]

lemma subst_qqAlls_vec {k n m w v p : V} (hw : IsSemitermVec L n m w) (hp : IsUFormula L p)
    (hv : IsSemitermVec L (n + k) (m + k) v) (h₁ : ∀ i < k, v.[i] = ^#i)
    (h₂ : ∀ j < n, v.[k + j] = termSubst L (bvarVec k m) w.[j]) :
    subst L w (qqAlls p k) = qqAlls (subst L v p) k := by
  induction k using ISigma1.pi1_succ_induction generalizing p v
  · definability
  case zero =>
    have hvw : v = w := nth_ext' n (by simpa using hv.lh) hw.lh fun i hi ↦ by
      simpa [termSubst_bvarVec_zero (hw.nth hi)] using h₂ i hi
    rw [qqAlls_zero, qqAlls_zero, hvw]
  case succ k ih =>
    obtain ⟨v', hv', hv'₁, hv'₂⟩ := exists_vec_shift hw k
    have hqv : qVec L v' = v := by
      have hl : len (qVec L v') = len v := by rw [len_qVec hv'.isUTerm, hv.lh, add_assoc]
      refine nth_ext' (len v) hl rfl ?_
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · rw [nth_qVec_zero, h₁ 0 (by simp)]
      · rcases lt_or_ge i k with hik | hik
        · rw [nth_qVec_succ_semi hv' (lt_of_lt_of_le hik le_add_self), hv'₁ i hik, termBShift_bvar,
            h₁ (i + 1) (by simpa using hik)]
        · obtain ⟨j, rfl⟩ := exists_add_of_le hik
          have hj : j < n := by
            have e : n + (k + 1) = k + (n + 1) := by rw [← add_assoc, add_comm n k, add_assoc]
            rw [hv.lh, e, add_assoc k j 1] at hi
            exact (add_lt_add_iff_right 1).mp ((add_lt_add_iff_left k).mp hi)
          have hkj : k + j < n + k := by
            rw [add_comm n k]
            exact (add_lt_add_iff_left k).mpr hj
          rw [nth_qVec_succ_semi hv' hkj, hv'₂ j hj, termBShift_termSubst_bvarVec k (hw.nth hj),
            show k + j + 1 = k + 1 + j by simp only [add_assoc, add_comm, add_left_comm], h₂ j hj]
    rw [qqAlls_succ' p k, qqAlls_succ' (subst L v p) k,
      ih (IsUFormula.all.mpr hp) hv' hv'₁ hv'₂, substs_all hp, hqv]

lemma subst_relocate_qVec {a b c j s v w E : V} (hw : IsSemitermVec L a c w)
    (hE : IsSemiformula L (a + 1) E) (hv : IsSemitermVec L (s + a) b v) (hj : j < s)
    (hvj : v.[j] = ^#j) (hvs : ∀ z < a, v.[s + z] = termSubst L (bvarVec s c) w.[z]) :
    subst L v (relocate L j s E) = relocate L j s (subst L (qVec L w) E) := by
  have hqw : IsSemitermVec L (a + 1) (c + 1) (qVec L w) := hw.qVec
  have hσ : IsSemitermVec L (a + 1) (s + a) (^#j ∷ bvarVec s a) :=
    IsSemitermVec.adjoin (IsSemitermVec.bvarVec le_rfl)
      (IsSemiterm.bvar.mpr (lt_of_lt_of_le hj le_self_add))
  have hτ : IsSemitermVec L (c + 1) (s + c) (^#j ∷ bvarVec s c) :=
    IsSemitermVec.adjoin (IsSemitermVec.bvarVec le_rfl)
      (IsSemiterm.bvar.mpr (lt_of_lt_of_le hj le_self_add))
  rw [relocate_eq_subst hE, relocate_eq_subst (hE.subst hqw), substs_substs hE hv hσ,
    substs_substs hE hτ hqw]
  apply subst_congr hE (hv.termSubstVec hσ).isUTerm (hτ.termSubstVec hqw).isUTerm le_rfl le_rfl
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp [nth_termSubstVec hσ.isUTerm hi, nth_termSubstVec hqw.isUTerm hi, nth_qVec_zero, hvj]
  · have hi' : i < a := by simpa using hi
    rw [nth_termSubstVec hσ.isUTerm hi, nth_adjoin_succ, nth_bvarVec _ _ _ hi', termSubst_bvar,
      hvs i hi', nth_termSubstVec hqw.isUTerm hi, nth_qVec_succ_semi hw hi',
      substs_cons_bShift (hw.nth hi')]

end generic

section table

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

lemma IsTable.subst_domainAt {tbl i l v : V} (hT : IsTable L₁ L₂ tbl) (hv : IsUTermVec L₁ l v)
    (hk : i + 1 ≤ l) (H : ∀ x < i + 1, v.[x] = ^#x) :
    subst L₁ v (domainAt L₁ tbl i) = domainAt L₁ tbl i :=
  subst_eq_self_of_le (hT.isSemiformula_domainAt (lt_add_one i)) hv hk H

lemma IsTable.subst_qVec_domainAt {tbl n m w : V} (hT : IsTable L₁ L₂ tbl)
    (hw : IsSemitermVec L₁ n m w) :
    subst L₁ (qVec L₁ w) (domainAt L₁ tbl 0) = domainAt L₁ tbl 0 :=
  hT.subst_domainAt hw.qVec.isUTerm (by simp) fun x hx ↦ by
    obtain rfl : x = 0 := by simpa using hx
    exact nth_qVec_zero w

lemma IsTable.subst_funcTail {tbl k f l v : V} (hT : IsTable L₁ L₂ tbl) (hf : L₂.IsFunc k f)
    (hv : IsUTermVec L₁ l v) (hk : k + 1 ≤ l) (H : ∀ x < k + 1, v.[x] = ^#x) :
    subst L₁ v (funcTail L₁ tbl k f) = funcTail L₁ tbl k f :=
  subst_eq_self_of_le (hT.isSemiformula_funcTail hf (lt_add_one k)) hv hk H

lemma IsTable.subst_qqConj_guardVec {tbl n m k s N b w v u u' : V} (hT : IsTable L₁ L₂ tbl)
    (hw : IsSemitermVec L₁ n m w) (hv : IsSemitermVec L₁ (s + n) b v) (hks : k ≤ s) (hkt : k ≤ N)
    (hst : s + n ≤ N) (hvj : ∀ j < k, v.[j] = ^#j)
    (hvs : ∀ z < n, v.[s + z] = termSubst L₁ (bvarVec s m) w.[z])
    (hu : ∀ i < k, IsSemiformula L₁ (n + 1) u.[i])
    (hu' : ∀ i < k, u'.[i] = subst L₁ (qVec L₁ w) u.[i]) :
    subst L₁ v (^⋀ guardVec L₁ tbl s u k) = ^⋀ guardVec L₁ tbl s u' k :=
  haveI : 𝚺ᴬ₁-Function₁ (subst L₁ v) := by definability
  hT.map_qqConj_guardVec (fun _ _ ↦ substs_and) (by simp) hkt hst hu
    (fun i hi ↦ hT.subst_domainAt hv.isUTerm
      (succ_le_iff_lt.mpr (lt_of_lt_of_le (lt_of_lt_of_le hi hks) le_self_add))
      fun x hx ↦ hvj x (lt_of_le_of_lt (lt_succ_iff_le.mp hx) hi))
    fun i hi ↦ by
      rw [subst_relocate_qVec hw (hu i hi) hv (lt_of_lt_of_le hi hks) (hvj i hi) hvs, hu' i hi]

lemma varEqual_termSubst {tbl : V} (hT : IsTable L₁ L₂ tbl) {n m w t : V}
    (hw : IsSemitermVec L₂ n m w)
    (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) (ht : IsSemiterm L₂ n t) :
    varEqual L₁ L₂ tbl (termSubst L₂ w t) = subst L₁ (qVec L₁ w) (varEqual L₁ L₂ tbl t) := by
  have hw₁ : IsSemitermVec L₁ n m w := hw.of_var hvar
  have h₁ : ∀ t, IsSemiterm L₂ n t →
      varEqual L₁ L₂ tbl (termSubst L₂ w t) = subst L₁ (qVec L₁ w) (varEqual L₁ L₂ tbl t) := by
    apply IsSemiterm.sigma1_induction
      (P := fun t ↦
        varEqual L₁ L₂ tbl (termSubst L₂ w t) = subst L₁ (qVec L₁ w) (varEqual L₁ L₂ tbl t))
    · definability
    · intro z hz
      rcases hvar z hz with ⟨y, hy⟩ | ⟨x, hx⟩
      · simp [hy, nth_qVec_succ_semi hw₁ hz]
      · simp [hx, nth_qVec_succ_semi hw₁ hz]
    · intro x
      simp
    · intro k f v hf hv ih
      have h₂ := hT.isSemiformula_funcBody hf hv (fun i hi ↦ IsSemiformula.varEqual hT (hv.nth hi))
      obtain ⟨h₃, h₄⟩ := IsSemiformula.imp.mp h₂
      have hvw : IsUTermVec L₂ k (termSubstVec L₂ k w v) :=
        (IsSemitermVec.termSubstVec hw hv).isUTerm
      have h₅ := nth_varEqualVec_map (tbl := tbl) (F := subst L₁ (qVec L₁ w)) hv.isUTerm hvw
        fun i hi ↦ by rw [nth_termSubstVec hv.isUTerm hi]; exact ih i hi
      obtain ⟨v', hv', h₆, h₇⟩ := exists_vec_shift hw₁.qVec k
      have hk0 : v'.[k] = ^#k := by
        have h₈ := h₇ 0 (by simp)
        rw [nth_qVec_zero, termSubst_bvar, nth_bvarVec _ _ _ (by simp)] at h₈
        simpa using h₈
      have hvs : ∀ z < n, v'.[k + 1 + z] = termSubst L₁ (bvarVec (k + 1) m) w.[z] := by
        intro z hz
        have e : k + 1 + z = k + (z + 1) := by simp only [add_comm, add_left_comm]
        rw [e, h₇ (z + 1) (by simpa using hz), nth_qVec_succ_semi hw₁ hz,
          termSubst_bvarVec_termBShift k (hw₁.nth hz)]
      have hv₁ : IsSemitermVec L₁ (k + 1 + n) (m + 1 + k) v' := by
        rw [add_arity_comm k n]
        exact hv'
      rw [termSubst_func hf hv.isUTerm, varEqual_func hf hvw, varEqual_func hf hv.isUTerm,
        subst_qqAlls_vec hw₁.qVec h₂.isUFormula hv' h₆ h₇, subst_imp hv' h₃ h₄,
        hT.subst_qqConj_guardVec hw₁ hv₁ le_self_add le_add_self (add_arity_comm k n).le h₆ hvs
          (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₅,
        hT.subst_funcTail hf hv'.isUTerm (le_self_add.trans (add_arity_comm k n).le)
          (fun x hx ↦ by
          rcases lt_or_ge x k with hxk | hxk
          · exact h₆ x hxk
          · obtain rfl : x = k := le_antisymm (lt_succ_iff_le.mp hx) hxk
            exact hk0)]
  exact h₁ t ht

lemma subst_translateRel {tbl n m k R v w : V} (hT : IsTable L₁ L₂ tbl)
    (hw : IsSemitermVec L₂ n m w) (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x))
    (hR : L₂.IsRel k R) (hv : IsSemitermVec L₂ k n v) :
    subst L₁ w (Bootstrapping.translateRel L₁ L₂ tbl k R v) =
      Bootstrapping.translateRel L₁ L₂ tbl k R (termSubstVec L₂ k w v) := by
  have hw₁ : IsSemitermVec L₁ n m w := hw.of_var hvar
  obtain ⟨h₁, h₂⟩ := IsSemiformula.imp.mp (hT.isSemiformula_relBody hR hv)
  have h₃ := nth_varEqualVec_map (tbl := tbl) (F := subst L₁ (qVec L₁ w)) hv.isUTerm
    (IsSemitermVec.termSubstVec hw hv).isUTerm fun i hi ↦ by
      rw [nth_termSubstVec hv.isUTerm hi]; exact varEqual_termSubst hT hw hvar (hv.nth hi)
  obtain ⟨v', hv', h₆, h₇⟩ := exists_vec_shift hw₁ k
  have hv'' : IsSemitermVec L₁ (k + n) (m + k) v' := by
    rw [add_comm k n]
    exact hv'
  unfold Bootstrapping.translateRel
  rw [subst_qqAlls_vec hw₁ (hT.isSemiformula_relBody hR hv).isUFormula hv' h₆ h₇,
    subst_imp hv' h₁ h₂,
    hT.subst_qqConj_guardVec hw₁ hv'' le_rfl (by simp) (add_comm k n).le h₆ h₇
      (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₃,
    subst_eq_self_of_le (hT.rel hR) hv'.isUTerm (by simp) h₆]

lemma translate_subst_aux {tbl : V} (hT : IsTable L₁ L₂ tbl) {n p : V} (hp : IsSemiformula L₂ n p) :
    ∀ m w : V, IsSemitermVec L₂ n m w → (∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) →
      translate L₁ L₂ tbl (subst L₂ w p) = subst L₁ w (translate L₁ L₂ tbl p) := by
  have hd := hT.isSemiformula_domainAt_zero
  have hdu := (hd 0).isUFormula
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv m w hw hvar
    simp [hR, hv.isUTerm, (IsSemitermVec.termSubstVec hw hv).isUTerm,
      subst_translateRel hT hw hvar hR hv]
  · intro n k R v hR hv m w hw hvar
    simp [hR, hv.isUTerm, (IsSemitermVec.termSubstVec hw hv).isUTerm,
      substs_neg (IsSemiformula.translateRel hT hR hv) (hw.of_var hvar),
      subst_translateRel hT hw hvar hR hv]
  · intro n m w hw hvar
    simp
  · intro n m w hw hvar
    simp
  · intro n p q hp hq ihp ihq m w hw hvar
    simp [*, hp.isUFormula, hq.isUFormula, IsUFormula.translate hT, (hp.subst hw).isUFormula,
      (hq.subst hw).isUFormula, ihp m w hw hvar, ihq m w hw hvar]
  · intro n p q hp hq ihp ihq m w hw hvar
    simp [*, hp.isUFormula, hq.isUFormula, IsUFormula.translate hT, (hp.subst hw).isUFormula,
      (hq.subst hw).isUFormula, ihp m w hw hvar, ihq m w hw hvar]
  · intro n p hp ih m w hw hvar
    have hq := qVec_eq_of_var (L' := L₁) hw hvar
    have hw₁ : IsSemitermVec L₁ n m w := hw.of_var hvar
    have hw' : IsSemitermVec L₂ (n + 1) (m + 1) (qVec L₁ w) := by rw [← hq]; exact hw.qVec
    have ih' := ih (m + 1) (qVec L₁ w) hw' (by rw [← hq]; exact hvar_qVec hw hvar)
    simp [*, hp.isUFormula, IsUFormula.translate hT, (hp.subst hw').isUFormula,
      subst_imp hw₁.qVec (hd n) (IsSemiformula.translate hT hp), hT.subst_qVec_domainAt hw₁]
  · intro n p hp ih m w hw hvar
    have hq := qVec_eq_of_var (L' := L₁) hw hvar
    have hw₁ : IsSemitermVec L₁ n m w := hw.of_var hvar
    have hw' : IsSemitermVec L₂ (n + 1) (m + 1) (qVec L₁ w) := by rw [← hq]; exact hw.qVec
    have ih' := ih (m + 1) (qVec L₁ w) hw' (by rw [← hq]; exact hvar_qVec hw hvar)
    simp [*, hp.isUFormula, IsUFormula.translate hT, (hp.subst hw').isUFormula,
      hT.subst_qVec_domainAt hw₁]

lemma translate_subst {tbl : V} (hT : IsTable L₁ L₂ tbl) {n m w p : V} (hw : IsSemitermVec L₂ n m w)
    (hvar : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) (hp : IsSemiformula L₂ n p) :
    translate L₁ L₂ tbl (subst L₂ w p) = subst L₁ w (translate L₁ L₂ tbl p) :=
  translate_subst_aux hT hp m w hw hvar

lemma translate_substs1_fvar {tbl : V} (hT : IsTable L₁ L₂ tbl) {p : V} (x : V)
    (hp : IsSemiformula L₂ 1 p) :
    translate L₁ L₂ tbl (substs1 L₂ (^&x) p) = substs1 L₁ (^&x) (translate L₁ L₂ tbl p) := by
  have hw : IsSemitermVec L₂ 1 0 (?[^&x] : V) := IsSemitermVec.singleton.mpr (IsSemiterm.fvar _ _)
  have hvar : ∀ i < 1, (∃ z, (?[^&x] : V).[i] = ^#z) ∨ (∃ y, (?[^&x] : V).[i] = ^&y) := by
    intro i hi
    obtain rfl : i = 0 := by simpa using hi
    exact Or.inr ⟨x, by simp⟩
  unfold substs1
  exact translate_subst hT hw hvar hp

end table

end substVars

/-! ## Substitution of free variables -/

section substFvars

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
    fvSubst L₁ w (^⋀ guardVec L₁ tbl s u k) = ^⋀ guardVec L₁ tbl s u' k :=
  haveI : 𝚺ᴬ₁-Function₁ (fvSubst L₁ w) := by definability
  hT.map_qqConj_guardVec (fun _ _ ↦ fvSubst_and) (by simp) hk hs hu
    (fun i hi ↦ hT.fvSubst_domainAt (lt_of_lt_of_le hi hk))
    fun i hi ↦ by
      rw [fvSubst_relocate (isSemitermVec_of_fvar (L := L₁) 0 hw) (hu i hi), hu' i hi]

lemma varEqual_termFvSubst {tbl w n t : V} (hT : IsTable L₁ L₂ tbl)
    (hw : ∀ i < len w, ∃ x, w.[i] = ^&x) (ht : IsSemiterm L₂ n t) :
    varEqual L₁ L₂ tbl (termFvSubst L₂ w t) = fvSubst L₁ w (varEqual L₁ L₂ tbl t) := by
  have h₁ : ∀ t, IsSemiterm L₂ n t →
      varEqual L₁ L₂ tbl (termFvSubst L₂ w t) = fvSubst L₁ w (varEqual L₁ L₂ tbl t) := by
    apply IsSemiterm.sigma1_induction
      (P := fun t ↦ varEqual L₁ L₂ tbl (termFvSubst L₂ w t) = fvSubst L₁ w (varEqual L₁ L₂ tbl t))
    · definability
    · intro z _
      simp [termFvSubstVec_pair]
    · intro x
      by_cases hx : x < len w
      · obtain ⟨y, hy⟩ := hw x hx
        simp [termFvSubstVec_pair, hx, hy]
      · simp [termFvSubstVec_pair, hx]
    · intro k f v hf hv ih
      have h₂ := hT.isSemiformula_funcBody hf hv (fun i hi ↦ IsSemiformula.varEqual hT (hv.nth hi))
      obtain ⟨h₃, h₄⟩ := IsSemiformula.imp.mp h₂
      have hvw : IsUTermVec L₂ k (termFvSubstVec L₂ k w v) :=
        (IsSemitermVec.termFvSubstVec (isSemitermVec_of_fvar n hw) hv).isUTerm
      have h₅ := nth_varEqualVec_map (tbl := tbl) (F := fvSubst L₁ w) hv.isUTerm hvw
        fun i hi ↦ by rw [nth_termFvSubstVec hv.isUTerm hi]; exact ih i hi
      rw [termFvSubst_func hf hv.isUTerm, varEqual_func hf hvw, varEqual_func hf hv.isUTerm,
        fvSubst_qqAlls h₂.isUFormula k,
        fvSubst_imp (isSemitermVec_of_fvar (L := L₁) (n + 1 + k) hw) h₃ h₄,
        hT.fvSubst_funcTail hf (show k < n + 1 + k by simp),
        hT.fvSubst_qqConj_guardVec hw (by simp) (add_arity_comm k n).le
          (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₅]
  exact h₁ t ht

lemma fvSubst_translateRel {tbl n k R v w : V} (hT : IsTable L₁ L₂ tbl)
    (hw : ∀ i < len w, ∃ x, w.[i] = ^&x) (hR : L₂.IsRel k R) (hv : IsSemitermVec L₂ k n v) :
    fvSubst L₁ w (Bootstrapping.translateRel L₁ L₂ tbl k R v) =
      Bootstrapping.translateRel L₁ L₂ tbl k R (termFvSubstVec L₂ k w v) := by
  obtain ⟨h₁, h₂⟩ := IsSemiformula.imp.mp (hT.isSemiformula_relBody hR hv)
  have h₃ := nth_varEqualVec_map (tbl := tbl) (F := fvSubst L₁ w) hv.isUTerm
    (IsSemitermVec.termFvSubstVec (isSemitermVec_of_fvar n hw) hv).isUTerm fun i hi ↦ by
      rw [nth_termFvSubstVec hv.isUTerm hi]; exact varEqual_termFvSubst hT hw (hv.nth hi)
  unfold Bootstrapping.translateRel
  rw [fvSubst_qqAlls (hT.isSemiformula_relBody hR hv).isUFormula k,
    fvSubst_imp (isSemitermVec_of_fvar (L := L₁) (n + k) hw) h₁ h₂,
    hT.fvSubst_qqConj_guardVec hw (by simp) (add_comm k n).le
      (fun i hi ↦ hT.isSemiformula_varEqualVec_nth hv hi) h₃,
    fvSubst_eq_self_of_shift h₂ (hT.rel_shift hR)]

lemma translate_fvSubst {tbl w n p : V} (hT : IsTable L₁ L₂ tbl)
    (hw : ∀ i < len w, ∃ x, w.[i] = ^&x) (hp : IsSemiformula L₂ n p) :
    translate L₁ L₂ tbl (fvSubst L₂ w p) = fvSubst L₁ w (translate L₁ L₂ tbl p) := by
  have hd := hT.isSemiformula_domainAt_zero
  have hdu := (hd 0).isUFormula
  apply IsSemiformula.sigma1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    simp [hR, hv.isUTerm, (IsSemitermVec.termFvSubstVec (isSemitermVec_of_fvar n hw) hv).isUTerm,
      fvSubst_translateRel hT hw hR hv]
  · intro n k R v hR hv
    simp [hR, hv.isUTerm, (IsSemitermVec.termFvSubstVec (isSemitermVec_of_fvar n hw) hv).isUTerm,
      fvSubst_neg (isSemitermVec_of_fvar (L := L₁) n hw) (IsSemiformula.translateRel hT hR hv),
      fvSubst_translateRel hT hw hR hv]
  · intro n
    simp
  · intro n
    simp
  · intro n p q hp hq ihp ihq
    simp [*, hp.isUFormula, hq.isUFormula, IsUFormula.translate hT,
      (hp.fvSubst (isSemitermVec_of_fvar n hw)).isUFormula,
      (hq.fvSubst (isSemitermVec_of_fvar n hw)).isUFormula]
  · intro n p q hp hq ihp ihq
    simp [*, hp.isUFormula, hq.isUFormula, IsUFormula.translate hT,
      (hp.fvSubst (isSemitermVec_of_fvar n hw)).isUFormula,
      (hq.fvSubst (isSemitermVec_of_fvar n hw)).isUFormula]
  · intro n p hp ih
    simp [*, hp.isUFormula, IsUFormula.translate hT,
      (hp.fvSubst (isSemitermVec_of_fvar (n + 1) hw)).isUFormula,
      fvSubst_imp (isSemitermVec_of_fvar (L := L₁) (n + 1) hw) (hd n)
        (IsSemiformula.translate hT hp),
      hT.fvSubst_domainAt (i := 0) (m := n + 1) (by simp)]
  · intro n p hp ih
    simp [*, hp.isUFormula, IsUFormula.translate hT,
      (hp.fvSubst (isSemitermVec_of_fvar (n + 1) hw)).isUFormula,
      hT.fvSubst_domainAt (i := 0) (m := n + 1) (by simp)]

end table

end substFvars

end FFL.FirstOrder.Arithmetic.Bootstrapping
