module

public import AlphaCentauri.Bootstrapping.Interpretability.TermSubst
public import AlphaCentauri.Bootstrapping.Interpretability.SubstCommutation
public import AlphaCentauri.ToFoundation.FvarInduction
public import AlphaCentauri.ToFoundation.TypedQuantifierBlock
public import AlphaCentauri.ToFoundation.Syntax

/-!
# Substitution of a closed term into the translated formulas

Along a table of a direct translation, the translations of `φ[t]` and of `φ[&b]` are provably
equivalent under the hypotheses `substHyp`, for every formula `φ`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section tautology

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

lemma tprovable_all_imp_imp_all (E F : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (E 🡒 F) 🡒 ∀¹ E 🡒 ∀¹ F := by
  have h₂ := TProof.all_imp_subst (T := T) (E.shift 🡒 F.shift) (Semiterm.fvar 0)
  have h₃ := TProof.all_imp_subst (T := T) E.shift (Semiterm.fvar 0)
  simp only [Semiformula.substs_imp] at h₂ h₃
  have h₁ : T.internalize V ⊢ ((∀¹ (E 🡒 F)) ⋏ (∀¹ E)) 🡒 ∀¹ F := by
    have h₄ : T.internalize V ⊢ ((∀¹ (E 🡒 F)) ⋏ (∀¹ E)).shift 🡒 F.free := by
      simp only [Semiformula.shift_and, Semiformula.shift_all, Semiformula.shift_imp,
        Semiformula.free]
      cl_prover [h₂, h₃]
    exact Nonempty.map TProof.generalizeAux h₄
  cl_prover [h₁]

lemma tprovable_all_iff_all (E F : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (E 🡘 F) 🡒 (∀¹ E 🡘 ∀¹ F) := by
  have h₁ : T.internalize V ⊢ ∀¹ (E 🡘 F) 🡒 ∀¹ (E 🡒 F) := by
    apply TProof.all_imp_all_of_free
    simp only [Semiformula.free, Semiformula.shift_imp, Semiformula.shift_iff,
      Semiformula.substs_imp, Semiformula.substs_imply]
    cl_prover
  have h₂ : T.internalize V ⊢ ∀¹ (E 🡘 F) 🡒 ∀¹ (F 🡒 E) := by
    apply TProof.all_imp_all_of_free
    simp only [Semiformula.free, Semiformula.shift_imp, Semiformula.shift_iff,
      Semiformula.substs_imp, Semiformula.substs_imply]
    cl_prover
  cl_prover [h₁, h₂, tprovable_all_imp_imp_all (T := T) E F,
    tprovable_all_imp_imp_all (T := T) F E]

lemma tprovable_all_iff_all_domain (d A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 (∀¹ (d 🡒 A) 🡘 ∀¹ (d 🡒 B)) := by
  have h₁ : T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 ∀¹ ((d 🡒 A) 🡘 (d 🡒 B)) := by
    apply TProof.all_imp_all_of_free
    simp only [Semiformula.free, Semiformula.shift_imp, Semiformula.shift_iff,
      Semiformula.substs_imp, Semiformula.substs_imply]
    cl_prover
  cl_prover [h₁, tprovable_all_iff_all (T := T) (d 🡒 A) (d 🡒 B)]

lemma tprovable_all_iff_exs_domain (d A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 (∃¹ (d ⋏ A) 🡘 ∃¹ (d ⋏ B)) := by
  have h₁ : T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 ∀¹ (∼(d ⋏ A) 🡘 ∼(d ⋏ B)) := by
    apply TProof.all_imp_all_of_free
    simp only [Semiformula.free, Semiformula.shift_iff,
      Semiformula.shift_and, Semiformula.shift_neg, Semiformula.substs_imply,
      Semiformula.substs_and, Semiformula.substs_neg]
    cl_prover
  have h₂ : T.internalize V ⊢ ∀¹ (∼(d ⋏ A) 🡘 ∼(d ⋏ B)) 🡒 (∼(∃¹ (d ⋏ A)) 🡘 ∼(∃¹ (d ⋏ B))) := by
    simp only [Semiformula.neg_ex]
    exact tprovable_all_iff_all (T := T) _ _
  cl_prover [h₁, h₂]

lemma tprovable_iff_and_iff (X X' Y Y' : Formula V L) :
    T.internalize V ⊢ (X 🡘 X') 🡒 (Y 🡘 Y') 🡒 ((X ⋏ Y) 🡘 (X' ⋏ Y')) := by
  cl_prover

lemma tprovable_iff_or_iff (X X' Y Y' : Formula V L) :
    T.internalize V ⊢ (X 🡘 X') 🡒 (Y 🡘 Y') 🡒 ((X ⋎ Y) 🡘 (X' ⋎ Y')) := by
  cl_prover

lemma tprovable_iff_neg_iff (X X' : Formula V L) :
    T.internalize V ⊢ (X 🡘 X') 🡒 (∼X 🡘 ∼X') := by
  cl_prover

lemma tprovable_iff_self (X : Formula V L) : T.internalize V ⊢ X 🡘 X := by
  cl_prover

end tautology

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
  have h₅ := Derivable.of_tprovable_imp₂
    (tprovable_iff_and_iff (T := S) ⟨X, hX⟩ ⟨X', hX'⟩ ⟨Y, hY⟩ ⟨Y', hY'⟩) h₃ h₄
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
  have h₅ := Derivable.of_tprovable_imp₂
    (tprovable_iff_or_iff (T := S) ⟨X, hX⟩ ⟨X', hX'⟩ ⟨Y, hY⟩ ⟨Y', hY'⟩) h₃ h₄
  simpa only [Semiformula.val_or, Semiformula.val_iff] using h₅

omit [L₁.Eq] [𝗘𝗤 L₁ ⪯ S] in
lemma derivable_iff_neg_V {X X' s : V} (hX : IsSemiformula L₁ 0 X)
    (hX' : IsSemiformula L₁ 0 X') (h : Derivable S (insert (iff L₁ X X') s)) :
    Derivable S (insert (iff L₁ (neg L₁ X) (neg L₁ X')) s) := by
  have h₁ : Derivable S (insert ((⟨X, hX⟩ : Formula V L₁) 🡘 ⟨X', hX'⟩).val s) := by
    simpa only [Semiformula.val_iff] using h
  have h₂ := Derivable.of_tprovable_imp (tprovable_iff_neg_iff (T := S) ⟨X, hX⟩ ⟨X', hX'⟩) h₁
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
    have h₁ := Derivable.of_tprovable hH (tprovable_iff_self (T := S) (⊤ : Formula V L₁))
    simp only [translateSubstEquiv, substs1, substs_verum, translate_verum]
    simpa only [Semiformula.val_iff, Semiformula.val_verum] using h₁
  have hfalsum : Derivable S (insert (translateSubstEquiv L₁ L₂ tbl t b ^⊥)
      (substHyp L₁ L₂ tbl t b)) := by
    have h₁ := Derivable.of_tprovable hH (tprovable_iff_self (T := S) (⊥ : Formula V L₁))
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

end FFL.FirstOrder.Arithmetic.Bootstrapping
