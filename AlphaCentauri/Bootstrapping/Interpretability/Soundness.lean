module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.Bootstrapping.Interpretability.DefinesElement
public import AlphaCentauri.Bootstrapping.Interpretability.SoundnessRules
public import AlphaCentauri.Bootstrapping.Interpretability.ValueLemma
public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import AlphaCentauri.ToFoundation.FvarInduction
public import AlphaCentauri.ToFoundation.Syntax
public import AlphaCentauri.ToFoundation.TypedProof
public import Foundation.FirstOrder.Incompleteness.Consistency

/-!
# Internal soundness of a translation

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
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {π : DirectTranslation S L₂} {tbl : V}

omit [L₂.Eq] in
lemma isSemiterm_of_zero {n t : V} (ht : IsSemiterm L₂ 0 t) : IsSemiterm L₂ n t :=
  IsSemiterm.def.mpr ⟨(IsSemiterm.def.mp ht).1, (IsSemiterm.def.mp ht).2.trans (by simp)⟩

omit [L₂.Eq] in
lemma substs1_subst_fvar_bvar {t u q : V} (ht : IsSemiterm L₂ 0 t) (hq : IsSemiformula L₂ 2 q) :
    substs1 L₂ t (subst L₂ ?[^&u, ^#(0 : V)] q) =
      substs1 L₂ (^&u) (subst L₂ ?[^#(0 : V), t] q) := by
  have h₁ : IsSemitermVec L₂ 2 1 (?[^&u, ^#(0 : V)] : V) := isSemitermVec_fvar_bvar u
  have h₂ : IsSemitermVec L₂ 1 0 (?[t] : V) := by simp [ht]
  have h₃ : IsSemitermVec L₂ 2 1 (?[^#(0 : V), t] : V) := by
    simp [isSemiterm_of_zero ht]
  have h₄ : IsSemitermVec L₂ 1 1 (?[^&u] : V) := by simp
  have h₅ : termSubstVec L₂ 2 (?[t] : V) (?[^&u, ^#(0 : V)] : V) =
      termSubstVec L₂ 2 (?[^&u] : V) (?[^#(0 : V), t] : V) := by
    simp [termSubstVec_cons₂ (t₁ := ^#(0 : V)) (by simp) ht.isUTerm, termSubst_zero ht]
  unfold substs1
  rw [substs_substs hq h₂ h₁, substs_substs hq h₄ h₃, h₅]

omit [L₂.Eq] in
lemma qVec_closed {t : V} (ht : IsSemiterm L₂ 0 t) :
    qVec L₂ (?[t] : V) = (?[^#(0 : V), t] : V) := by
  simp [qVec, len_adjoin, termBShift_zero ht, termBShiftVec_cons₁ ht.isUTerm]

omit [L₂.Eq] in
lemma translate_substs1_all {t q : V} (ht : IsSemiterm L₂ 0 t)
    (hq : IsSemiformula L₂ 2 q) :
    translate L₁ L₂ tbl (substs1 L₂ t (^∀ q)) =
      ^∀ imp L₁ (domainAt L₁ tbl 0) (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q)) := by
  have h₁ : IsSemitermVec L₂ 2 1 (?[^#(0 : V), t] : V) := by simp [isSemiterm_of_zero ht]
  unfold substs1
  rw [substs_all hq.isUFormula, qVec_closed ht, translate_all (hq.subst h₁).isUFormula]

omit [L₂.Eq] in
lemma translate_substs1_exs {t q : V} (ht : IsSemiterm L₂ 0 t)
    (hq : IsSemiformula L₂ 2 q) :
    translate L₁ L₂ tbl (substs1 L₂ t (^∃ q)) =
      ^∃ (domainAt L₁ tbl 0 ^⋏ translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q)) := by
  have h₁ : IsSemitermVec L₂ 2 1 (?[^#(0 : V), t] : V) := by simp [isSemiterm_of_zero ht]
  unfold substs1
  rw [substs_ex hq.isUFormula, qVec_closed ht, translate_exs (hq.subst h₁).isUFormula]

omit [L₁.Eq] in
lemma substs_iff_V {m w p q : V} (hp : IsSemiformula L₁ 1 p) (hq : IsSemiformula L₁ 1 q)
    (hw : IsSemitermVec L₁ 1 m w) :
    subst L₁ w (iff L₁ p q) = iff L₁ (subst L₁ w p) (subst L₁ w q) := by
  have hpq : IsUFormula L₁ (neg L₁ p ^⋎ q) := (IsSemiformula.imp.mpr ⟨hp, hq⟩).isUFormula
  have hqp : IsUFormula L₁ (neg L₁ q ^⋎ p) := (IsSemiformula.imp.mpr ⟨hq, hp⟩).isUFormula
  unfold iff imp
  rw [substs_and hpq hqp, substs_or hp.isUFormula.neg hq.isUFormula,
    substs_or hq.isUFormula.neg hp.isUFormula, substs_neg hp hw, substs_neg hq hw]

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
  have hi (i : Fin k) : IsSemiterm L₂ 0 (termSubst L₂ ?[c] v.[(i : ℕ)]) :=
    IsSemitermVec.termSubst hw (hv.nth (by simp))
  refine ⟨fun i ↦ ⟨termSubst L₂ ?[c] v.[(i : ℕ)], hi i⟩, fun i ↦ rfl, ?_⟩
  rw [substs_rel (codeIn_rel_quote R) hv.isUTerm, Semiformula.rel_val]
  congr 1
  change termSubstVec L₂ (k : V) ?[c] v = matrixToVec fun i : Fin k ↦ termSubst L₂ ?[c] v.[(i : ℕ)]
  rw [eq_matrixToVec_iff]
  constructor
  · simp [hv.isUTerm]
  · intro i
    rw [nth_termSubstVec hv.isUTerm (by simp)]

lemma derivable_iff_translate_rel (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {t b : V} (ht : IsSemiterm L₂ 0 t)
    {k : ℕ} (R : L₂.Rel k) {v : V} (hv : IsSemitermVec L₂ (k : V) 1 v) :
    Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b (^rel (k : V) ⌜R⌝ v))
      (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.isTable hL₂
  have hH := isFormulaSet_substHyp hT ht b
  obtain ⟨u₁, hu₁, hf₁⟩ := substs_rel_val R ht hv
  obtain ⟨u₂, hu₂, hf₂⟩ := substs_rel_val R (c := ^&b) (by simp) hv
  unfold translateSubstEquiv substs1
  rw [hf₁, hf₂, translate_rel_typed h hT R u₁, translate_rel_typed h hT R u₂]
  have hΦ (i : Fin k) : Derivable S (insert (∀¹ (domT π 🡒
      (varEqualT hT (u₁ i) 🡘 varEqualT hT (u₂ i)))).val (substHyp L₁ L₂ tbl t b)) := by
    rw [← termSubstEquiv_eq_typed h hT (hu₁ i) (hu₂ i)]
    exact derivable_termSubstEquiv hS h hL₂ ht (hv.nth (by simp))
  have hc := Derivable.conj_typed hH hΦ
  let C : Semiformula V L₁ (0 + k) :=
    (⌜(π.rel R).sentence⌝ : Semiformula V L₁ k).subst (fun i ↦ Semiterm.bvar (i.addCast 0))
  have hg := Derivable.of_tprovable_imp
    (relativizedImp_congr (T := S) (domT π) (fun i ↦ varEqualT hT (u₁ i))
      (fun i ↦ varEqualT hT (u₂ i)) C) hc
  simpa only [Semiformula.val_iff] using hg

omit [L₂.Eq] in
lemma substs1_and_V {t p q : V} (hp : IsSemiformula L₂ 1 p) (hq : IsSemiformula L₂ 1 q) :
    substs1 L₂ t (p ^⋏ q) = substs1 L₂ t p ^⋏ substs1 L₂ t q := by
  unfold substs1
  exact substs_and hp.isUFormula hq.isUFormula

omit [L₂.Eq] in
lemma substs1_or_V {t p q : V} (hp : IsSemiformula L₂ 1 p) (hq : IsSemiformula L₂ 1 q) :
    substs1 L₂ t (p ^⋎ q) = substs1 L₂ t p ^⋎ substs1 L₂ t q := by
  unfold substs1
  exact substs_or hp.isUFormula hq.isUFormula

lemma pi2_qqAll_sub_one (q : V) : π₂ ((^∀ q) - 1) = q := by
  simp [qqAll]

lemma pi2_qqExs_sub_one (q : V) : π₂ ((^∃ q) - 1) = q := by
  simp [qqExs]

omit [L₂.Eq] in
lemma quantFresh_all (tbl t b q : V) :
    quantFresh L₁ L₂ tbl t b (^∀ q) = max (substHyp L₁ L₂ tbl t b)
      (iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q))
        (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q))) := by
  simp only [quantFresh, pi2_qqAll_sub_one]

omit [L₂.Eq] in
lemma quantFresh_exs (tbl t b q : V) :
    quantFresh L₁ L₂ tbl t b (^∃ q) = max (substHyp L₁ L₂ tbl t b)
      (iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q))
        (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q))) := by
  simp only [quantFresh, pi2_qqExs_sub_one]

omit [L₂.Eq] in
lemma isSemiterm_fvar_closed (b : V) : IsSemiterm L₂ 0 (^&b) := by simp

theorem derivable_translateSubstEquiv
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {t b p : V} (ht : IsSemiterm L₂ 0 t)
    (hp : IsSemiformula L₂ 1 p) :
    Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b p) (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.isTable hL₂
  have hH := isFormulaSet_substHyp hT ht b
  have hb : IsSemiterm L₂ 0 (^&b) := isSemiterm_fvar_closed b
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
    rw [substs1_and_V hp₁ hq₁, substs1_and_V hp₁ hq₁ (t := ^&b),
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
    rw [substs1_or_V hp₁ hq₁, substs1_or_V hp₁ hq₁ (t := ^&b),
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
    have h₁ : IsSemitermVec L₂ 2 1 (?[^#(0 : V), t] : V) := by simp [isSemiterm_of_zero ht]
    have h₂ : IsSemitermVec L₂ 2 1 (?[^#(0 : V), ^&b] : V) := by simp
    have hθ₁ : IsSemiformula L₂ 1 (subst L₂ ?[^#(0 : V), t] q) := hq.subst h₁
    have hθ₂ : IsSemiformula L₂ 1 (subst L₂ ?[^#(0 : V), ^&b] q) := hq.subst h₂
    have hA₁ : IsSemiformula L₁ 1 (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q)) :=
      IsSemiformula.translate hT hθ₁
    have hA₂ : IsSemiformula L₁ 1 (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q)) :=
      IsSemiformula.translate hT hθ₂
    unfold translateSubstEquiv at ih ⊢
    rw [substs1_subst_fvar_bvar ht hq, substs1_subst_fvar_bvar hb hq,
      translate_substs1_fvar hT _ hθ₁, translate_substs1_fvar hT _ hθ₂] at ih
    have e : substs1 L₁ (^&(quantFresh L₁ L₂ tbl t b (^∀ q)))
        (iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q))
          (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q))) =
      iff L₁ (substs1 L₁ (^&(quantFresh L₁ L₂ tbl t b (^∀ q)))
          (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q)))
        (substs1 L₁ (^&(quantFresh L₁ L₂ tbl t b (^∀ q)))
          (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q))) := by
      unfold substs1
      exact substs_iff_V (m := 0) hA₁ hA₂ (by simp)
    have hsu : substHyp L₁ L₂ tbl t b ≤ quantFresh L₁ L₂ tbl t b (^∀ q) := by
      rw [quantFresh_all]
      exact le_max_left _ _
    have hpu : iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q))
        (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q)) ≤
        quantFresh L₁ L₂ tbl t b (^∀ q) := by
      rw [quantFresh_all]
      exact le_max_right _ _
    have hA : Derivable S (insert (^∀ (iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q))
        (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q)))) (substHyp L₁ L₂ tbl t b)) :=
      Derivable.all_of_fresh hS hsu hpu (IsSemiformula.iff.mpr ⟨hA₁, hA₂⟩) (by rw [e]; exact ih)
    rw [translate_substs1_all ht hq, translate_substs1_all hb hq]
    exact derivable_all_iff_V hδ hA₁ hA₂ hA
  have hexs : ∀ q, IsSemiformula L₂ 2 q →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b
        (subst L₂ ?[^&(quantFresh L₁ L₂ tbl t b (^∃ q)), ^#(0 : V)] q)) (substHyp L₁ L₂ tbl t b)) →
      Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b (^∃ q))
        (substHyp L₁ L₂ tbl t b)) := by
    intro q hq ih
    have h₁ : IsSemitermVec L₂ 2 1 (?[^#(0 : V), t] : V) := by simp [isSemiterm_of_zero ht]
    have h₂ : IsSemitermVec L₂ 2 1 (?[^#(0 : V), ^&b] : V) := by simp
    have hθ₁ : IsSemiformula L₂ 1 (subst L₂ ?[^#(0 : V), t] q) := hq.subst h₁
    have hθ₂ : IsSemiformula L₂ 1 (subst L₂ ?[^#(0 : V), ^&b] q) := hq.subst h₂
    have hA₁ : IsSemiformula L₁ 1 (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q)) :=
      IsSemiformula.translate hT hθ₁
    have hA₂ : IsSemiformula L₁ 1 (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q)) :=
      IsSemiformula.translate hT hθ₂
    unfold translateSubstEquiv at ih ⊢
    rw [substs1_subst_fvar_bvar ht hq, substs1_subst_fvar_bvar hb hq,
      translate_substs1_fvar hT _ hθ₁, translate_substs1_fvar hT _ hθ₂] at ih
    have e : substs1 L₁ (^&(quantFresh L₁ L₂ tbl t b (^∃ q)))
        (iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q))
          (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q))) =
      iff L₁ (substs1 L₁ (^&(quantFresh L₁ L₂ tbl t b (^∃ q)))
          (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q)))
        (substs1 L₁ (^&(quantFresh L₁ L₂ tbl t b (^∃ q)))
          (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q))) := by
      unfold substs1
      exact substs_iff_V (m := 0) hA₁ hA₂ (by simp)
    have hsu : substHyp L₁ L₂ tbl t b ≤ quantFresh L₁ L₂ tbl t b (^∃ q) := by
      rw [quantFresh_exs]
      exact le_max_left _ _
    have hpu : iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q))
        (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q)) ≤
        quantFresh L₁ L₂ tbl t b (^∃ q) := by
      rw [quantFresh_exs]
      exact le_max_right _ _
    have hA : Derivable S (insert (^∀ (iff L₁ (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), t] q))
        (translate L₁ L₂ tbl (subst L₂ ?[^#(0 : V), ^&b] q)))) (substHyp L₁ L₂ tbl t b)) :=
      Derivable.all_of_fresh hS hsu hpu (IsSemiformula.iff.mpr ⟨hA₁, hA₂⟩) (by rw [e]; exact ih)
    rw [translate_substs1_exs ht hq, translate_substs1_exs hb hq]
    exact derivable_exs_iff_V hδ hA₁ hA₂ hA
  exact IsSemiformula.sigma1_induction_fvar hP hg hrel hnrel hverum hfalsum hand hor hall hexs hp
end value

end formSubst

/-! ## The existential rule -/

section existsRule

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open PeanoMinus ISigma0 ISigma1

section rules

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {π : DirectTranslation S L₂} {tbl : V}

omit [L₂.Eq] [𝗘𝗤 _ ⪯ S] in
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
    simp only [mem_bitInsert_iff] at hx ⊢
    tauto) hX
  have hIs := Derivable.wk (IsFormulaSet.insert_iff.mpr
    ⟨IsSemiformula.iff.mpr ⟨hX', hY'⟩, hs⟩) (by
    intro x hx
    simp only [substHyp, mem_bitInsert_iff] at hx ⊢
    rcases hx with hx | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr (hD hx)))) hI
  exact derivable_of_iff_mp (⟨_, hX'⟩ : Formula V L₁) ⟨_, hY'⟩ hIs hXs

omit [L₂.Eq] [𝗘𝗤 _ ⪯ S] in
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
    simp only [mem_bitInsert_iff] at hx ⊢
    tauto) hd
  have h₁ : Derivable S (insert (substs1 L₁ (^&b) (tbl.[0] ^⋏ translate L₁ L₂ tbl p)) s) := by
    rw [hmem]
    exact Derivable.and_m (mem_bitInsert_iff.mpr (Or.inl rfl)) d₁ d₂
  exact Derivable.ex_m hm (by simp) h₁

omit [L₂.Eq] [𝗘𝗤 _ ⪯ S] in
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
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {t Θ : V} (ht : IsSemiterm L₂ 0 t)
    (hΘ : IsFormulaSet L₁ Θ) (hD : negDomSet L₁ tbl.[0] t ⊆ Θ) :
    Derivable S (insert (^∃ (tbl.[0] ^⋏ varEqual L₁ L₂ tbl t)) Θ) := by
  have hT := h.isTable hL₂
  have hd : tbl.[0] = (domT π).val := h.domain
  have hv : (definesElement (domT π) (varEqualT hT (⟨t, ht⟩ : Term V L₂))).val =
      definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t) := by
    rw [definesElement_val, varEqualT_val, ← hd]
  have hDef : Derivable S (insert (definesElement (domT π)
      (varEqualT hT (⟨t, ht⟩ : Term V L₂))).val (negDomSet L₁ tbl.[0] t)) := by
    rw [hv]
    exact derivable_definesElement hS h hL₂ ht
  have h₁ := Derivable.of_tprovable_imp
    (definesElement_exists (T := S) (domT π) (varEqualT hT (⟨t, ht⟩ : Term V L₂))) hDef
  have hval : (∃¹ (domT π ⋏ varEqualT hT (⟨t, ht⟩ : Term V L₂))).val =
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
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hD hx)) h₁

lemma translated_exs (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {Γ p t : V} (hΓ : IsFormulaSet L₂ Γ)
    (hp : ^∃ p ∈ Γ) (ht : IsTerm L₂ t)
    (hd : TranslatedDerivable S L₂ tbl (insert (substs1 L₂ t p) Γ)) :
    TranslatedDerivable S L₂ tbl Γ := by
  have hT := h.isTable hL₂
  have hp1 : IsSemiformula L₂ 1 p := by simpa using IsSemiformula.exs.mp (hΓ _ hp)
  have hpt : IsFormula L₂ (substs1 L₂ t p) := IsSemiformula.substs1 (n := 0) ht hp1
  set M := insert (substs1 L₂ t p) Γ + t
  set Θ := translateSet L₁ L₂ tbl Γ ∪ negDomSet L₁ tbl.[0] M
  have hM : insert (substs1 L₂ t p) Γ ≤ M := le_add_right le_rfl
  have htM : t ≤ M := le_add_left le_rfl
  have hΓM : Γ ≤ M := by
    have h₁ : Γ ≤ insert (substs1 L₂ t p) Γ := le_of_subset (by
      intro x hx
      exact mem_bitInsert_iff.mpr (Or.inr hx))
    exact le_trans h₁ hM
  have hΘf : IsFormulaSet L₁ Θ := isFormulaSet_translated_union hT hΓ M
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b, Θ ≤ b ∧ tbl.[0] ^⋏ varEqual L₁ L₂ tbl t ≤ b :=
    ⟨Θ + (tbl.[0] ^⋏ varEqual L₁ L₂ tbl t), le_add_right le_rfl, le_add_left le_rfl⟩
  have hX := translated_insert h hL₂ hpt hΓ hM hd
  have hD : negDomSet L₁ tbl.[0] t ⊆ Θ := by
    intro x hx
    exact mem_cup_iff.mpr (Or.inr (negDomSet_mono htM hx))
  have hK := derivable_insert_translate_substs hT ht hp1 hΘf hD hX
    (derivable_translateSubstEquiv (t := t) (b := b) hS h hL₂ ht hp1)
  have hm0 : translate L₁ L₂ tbl (^∃ p) ∈ translateSet L₁ L₂ tbl Γ :=
    mem_translateSet_iff.mpr ⟨^∃ p, hp, rfl⟩
  rw [translate_exs (IsSemiformula.isUFormula hp1), domainAt_zero hT] at hm0
  have hm : ^∃ (tbl.[0] ^⋏ translate L₁ L₂ tbl p) ∈
      insert (neg L₁ (substs1 L₁ (^&b) tbl.[0]))
        (insert (neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t))) Θ) :=
    mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl hm0)))))
  have hS2 := derivable_exs_body hT (IsFormulaSet.insert_iff.mp hK.isFormulaSet).2 hp1 hm
    (mem_bitInsert_iff.mpr (Or.inl rfl)) hK
  have hS3 := derivable_neg_exs_definesElement hS hT ht hΘf hb₁ hb₂ hS2
  have hS4 := derivable_exs_definesElement hS h hL₂ ht hΘf hD
  exact translated_of_le hS h hL₂ hΓ hΓM (Derivable.cut _ hS4 hS3)

end rules

end existsRule

/-! ## Translated derivability of derivable sets -/

section soundness

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open PeanoMinus ISigma0 ISigma1

section rules

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {π : DirectTranslation S L₂} {tbl : V}

theorem TranslatedDerivable.of_derivable
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {S' : Theory L₂} [S'.Δ₁]
    (hax : ∀ p ∈ S'.Δ₁Class (V := V), Provable S (Bootstrapping.translate L₁ L₂ tbl p)) {s : V}
    (hs : Derivable S' s) : TranslatedDerivable S L₂ tbl s := by
  obtain ⟨d, hds, hd⟩ := hs
  subst hds
  apply Derivation.induction1 𝚺 (P := fun d ↦ TranslatedDerivable S L₂ tbl (fstIdx d)) ?_ hd
  · intro s hs p hp hn
    simp only [fstIdx_axL]
    exact translated_em h hL₂ hs hp hn
  · intro s hs hv
    simp only [fstIdx_verumIntro]
    exact translated_verum h hL₂ hs hv
  · intro s hs p q dp dq hpq hdp hdq ihp ihq
    simp only [hdp.1] at ihp
    simp only [hdq.1] at ihq
    simp only [fstIdx_andIntro]
    exact translated_and hS h hL₂ hs hpq ihp ihq
  · intro s hs p q d hpq hd ih
    simp only [hd.1] at ih
    simp only [fstIdx_orIntro]
    exact translated_or hS h hL₂ hs hpq ih
  · intro s hs p d hp hd ih
    simp only [hd.1] at ih
    simp only [fstIdx_allIntro]
    exact translated_all hS h hL₂ hs hp ih
  · intro s hs p t d hp ht hd ih
    simp only [hd.1] at ih
    simp only [fstIdx_exsIntro]
    exact translated_exs hS h hL₂ hs hp ht ih
  · intro s hs d hsub _ ih
    simp only [fstIdx_wkRule]
    exact translated_wk h hL₂ hs hsub ih
  · intro s hs d hds hd' ih
    simp only [fstIdx_shiftRule]
    subst hds
    exact translated_shift hS h hL₂ (Derivation.isFormulaSet hd') ih
  · intro s hs p d₁ d₂ h₁ h₂ ih₁ ih₂
    simp only [h₁.1] at ih₁
    simp only [h₂.1] at ih₂
    simp only [fstIdx_cutRule]
    have hp : IsFormula L₂ p := (IsFormulaSet.insert_iff.mp h₁.isFormulaSet).1
    exact translated_cut hS h hL₂ hs hp ih₁ ih₂
  · intro s hs p hps hpT
    simp only [fstIdx_axm]
    exact translated_axm h hL₂ hs hps (hax p hpT)
  · definability

end rules

end soundness

/-! ## Corollaries -/

section corollaries

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open PeanoMinus ISigma0 ISigma1

section translation

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {π : DirectTranslation S L₂} {tbl : V}

/-- A formula code fixed by the shift of free variables and provable in `S'` has its translation
provable in `S`.
- [Lin97, Corollary 6.1]
- [HP98, Lemma III.2.42] -/
theorem provable_translate (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {S' : Theory L₂} [S'.Δ₁]
    (hax : ∀ p ∈ S'.Δ₁Class (V := V), Provable S (Bootstrapping.translate L₁ L₂ tbl p)) {φ : V}
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
  have h₀ := elim_translateSet hS h hL₂ hΓ zero_le hfresh hd
  rw [negDomSet_zero, translateSet_insert, translateSet_empty] at h₀
  exact internal_provable_iff_internal_derivable.mpr (Derivable.ofSetEq (fun x ↦ by simp) h₀)

/-- If `S` is consistent in `V`, then so is `S'`.
- [Lin97, Corollary 6.1]
- [HP98, Lemma III.2.42] -/
theorem consistent_of_translate (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {S' : Theory L₂} [S'.Δ₁]
    (hax : ∀ p ∈ S'.Δ₁Class (V := V), Provable S (Bootstrapping.translate L₁ L₂ tbl p))
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
  exact provable_translate hS h hL₂ hax hφ hpr

end finite

end corollaries

end FFL.FirstOrder.Arithmetic.Bootstrapping
