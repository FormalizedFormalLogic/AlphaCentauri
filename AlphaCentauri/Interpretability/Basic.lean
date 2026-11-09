module

public import Foundation.FirstOrder.LK.Interpretation

/-!
# API for `DirectInterpretation`

Additional API for Foundation's `DirectTranslation` and `DirectInterpretation` (`T ⊳ U`):
transport of a translation along a stronger base theory, consistency transfer, monotonicity in
both arguments, the disjunction lemma, and faithful interpretations.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace DirectTranslation

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]

/-- Transport a translation along a stronger base theory: the same domain, relations, and
function graphs, with the provability conditions reproved in `T'`.
- [HP98, Remarks III.1.7] -/
def ofWeakerThan (π : DirectTranslation T L₂) {T' : Theory L₁} [𝗘𝗤 _ ⪯ T'] [T ⪯ T'] :
    DirectTranslation T' L₂ where
  domain := π.domain
  rel := π.rel
  func := π.func
  domain_nonempty := Entailment.WeakerThan.pbl π.domain_nonempty
  func_defined f := Entailment.WeakerThan.pbl (π.func_defined f)
  preserve_eq := Entailment.WeakerThan.pbl π.preserve_eq

section ofWeakerThan

variable {T' : Theory L₁} [𝗘𝗤 _ ⪯ T'] [T ⪯ T'] (π : DirectTranslation T L₂)

@[simp] lemma ofWeakerThan_domain : (π.ofWeakerThan (T' := T')).domain = π.domain := rfl

@[simp] lemma ofWeakerThan_rel {k} (R : L₂.Rel k) :
    (π.ofWeakerThan (T' := T')).rel R = π.rel R := rfl

@[simp] lemma ofWeakerThan_func {k} (f : L₂.Func k) :
    (π.ofWeakerThan (T' := T')).func f = π.func f := rfl

@[simp] lemma ofWeakerThan_varEqual {ξ n} (t : Semiterm L₂ ξ n) :
    (π.ofWeakerThan (T' := T')).varEqual t = π.varEqual t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih => simp [DirectTranslation.varEqual, ih]

@[simp] lemma ofWeakerThan_translate {ξ n} (φ : Semiformula L₂ ξ n) :
    (π.ofWeakerThan (T' := T')).translate φ = π.translate φ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => simp only [translate_rel, translateRel, ofWeakerThan_varEqual,
      ofWeakerThan_domain, ofWeakerThan_rel]
  | hnrel r v => simp only [translate_nrel, translateRel, ofWeakerThan_varEqual,
      ofWeakerThan_domain, ofWeakerThan_rel]
  | hand _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hor _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hall _ ih => simp [translate_all, DirectTranslation.fal, ih]
  | hexs _ ih => simp [translate_ex, DirectTranslation.exs, ih]

end ofWeakerThan

section models

variable {M : Type*} [Nonempty M] [Tarski.Structure L₁ M] [Tarski.Structure.Eq L₁ M]

omit [L₁.Eq] [Tarski.Structure.Eq L₁ M] in
lemma models_domainNonempty_iff (D : Semiformula.Operator L₁ 1) :
    M↓[L₁] ⊧ “∃ x, %D x” ↔ ∃ x : M, D.val ![x] := by
  simp [models_iff]

lemma models_funcDefined_iff {k} (D : Semiformula.Operator L₁ 1)
    (F : Semiformula.Operator L₁ (k + 1)) :
    M↓[L₁] ⊧ ∀¹* “(⋀ i, %D #(i : Fin k)) → ∃! y, %D y ∧ %F y ⋯” ↔
      ∀ e : Fin k → M, (∀ i, D.val ![e i]) → ∃! y : M, D.val ![y] ∧ F.val (y :> e) := by
  simp [models_iff, Function.comp_def, Matrix.constant_eq_singleton]

lemma models_preserveEq_iff (D : Semiformula.Operator L₁ 1) (E : Semiformula.Operator L₁ 2) :
    M↓[L₁] ⊧ “∀ x y, %D x → %D y → (%E x y ↔ x = y)” ↔
      ∀ x y : M, D.val ![x] → D.val ![y] → (E.val ![x, y] ↔ x = y) := by
  simp [models_iff]

end models

section congruence

variable {U : Theory L₁} [𝗘𝗤 _ ⪯ U] {M : Type*} [Tarski.Structure L₁ M]
  (π : DirectTranslation T L₂) (π' : DirectTranslation U L₂)
  (hD : ∀ e : Fin 1 → M, π.domain.val e ↔ π'.domain.val e)
  (hR : ∀ {k} (R : L₂.Rel k) (e : Fin k → M), (π.rel R).val e ↔ (π'.rel R).val e)
  (hF : ∀ {k} (f : L₂.Func k) (e : Fin (k + 1) → M), (π.func f).val e ↔ (π'.func f).val e)

include hD hF in
lemma eval_varEqual_congr {ξ n} (t : Semiterm L₂ ξ n) :
    ∀ {e : Fin (n + 1) → M} {ε : ξ → M},
      Semiformula.Eval e ε (π.varEqual t) ↔ Semiformula.Eval e ε (π'.varEqual t) := by
  induction t with
  | bvar x => intro e ε; rfl
  | fvar x => intro e ε; rfl
  | func f v ih =>
    intro e ε
    simp [varEqual, ih, hD, hF]

include hD hR hF in
lemma eval_translateRel_congr {ξ n k} (r : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n)
    {e : Fin n → M} {ε : ξ → M} :
    Semiformula.Eval e ε (π.translateRel r v) ↔ Semiformula.Eval e ε (π'.translateRel r v) := by
  simp [translateRel, eval_varEqual_congr π π' hD hF, hD, hR]

include hD hR hF in
lemma eval_translate_congr {ξ n} (σ : Semiformula L₂ ξ n) {e : Fin n → M} {ε : ξ → M} :
    Semiformula.Eval e ε (π.translate σ) ↔ Semiformula.Eval e ε (π'.translate σ) := by
  induction σ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => exact eval_translateRel_congr π π' hD hR hF r v
  | hnrel r v => simp [translate_nrel, eval_translateRel_congr π π' hD hR hF]
  | hand _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hor _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hall _ ih => simp [translate_all, fal, hD, ih]
  | hexs _ ih => simp [translate_ex, exs, hD, ih]

end congruence

section ite

variable (φ : Sentence L₁) [𝗘𝗤 _ ⪯ insert φ T] [𝗘𝗤 _ ⪯ insert (∼φ) T]
  (π₀ : DirectTranslation (insert φ T) L₂) (π₁ : DirectTranslation (insert (∼φ) T) L₂)

omit [L₁.Eq] in
private lemma eval_rew_empty_iff {M : Type*} [Nonempty M] [Tarski.Structure L₁ M] {n}
    {e : Fin n → M} (σ : Sentence L₁) :
    (⟨Rew.empty ▹ σ⟩ : Semiformula.Operator L₁ n).val e ↔ M↓[L₁] ⊧ σ := by
  simp only [Semiformula.Operator.val]
  rw [Semiformula.eval_empty]
  exact ⟨fun h ↦ Semiformula.Eval.of_eq h rfl (funext fun a ↦ a.elim),
    fun h ↦ Semiformula.Eval.of_eq h rfl (funext fun a ↦ a.elim)⟩

omit [L₁.Eq] in
private lemma models_insert_cases {M : Type*} [Nonempty M] [Tarski.Structure L₁ M]
    (hT : M↓[L₁] ⊧* T) : (M↓[L₁] ⊧ φ ∧ M↓[L₁] ⊧* insert φ T) ∨
      (M↓[L₁] ⊧ ∼φ ∧ M↓[L₁] ⊧* insert (∼φ) T) := by
  rcases Classical.em (M↓[L₁] ⊧ φ) with hφ | hφ
  · exact Or.inl ⟨hφ, Semantics.ModelsSet.insert_iff.mpr ⟨hφ, hT⟩⟩
  · have hφ' : M↓[L₁] ⊧ ∼φ := by simp [hφ]
    exact Or.inr ⟨hφ', Semantics.ModelsSet.insert_iff.mpr ⟨hφ', hT⟩⟩

omit [L₁.Eq] in
private lemma ite_gate_iff {M : Type*} [Nonempty M] [Tarski.Structure L₁ M] (hφ : M↓[L₁] ⊧ φ) {k}
    {e : Fin k → M} {X Y : Semiformula.Operator L₁ k} :
    (((⟨Rew.empty ▹ φ⟩ : Semiformula.Operator L₁ k).and X).or
      ((⟨Rew.empty ▹ ∼φ⟩ : Semiformula.Operator L₁ k).and Y)).val e ↔ X.val e := by
  have hφ' : ¬ M↓[L₁] ⊧ ∼φ := by simpa using hφ
  simp only [Semiformula.val_operator_or, Semiformula.val_operator_and, eval_rew_empty_iff]
  tauto

omit [L₁.Eq] in
private lemma ite_gate_iff' {M : Type*} [Nonempty M] [Tarski.Structure L₁ M] (hφ' : M↓[L₁] ⊧ ∼φ)
    {k} {e : Fin k → M} {X Y : Semiformula.Operator L₁ k} :
    (((⟨Rew.empty ▹ φ⟩ : Semiformula.Operator L₁ k).and X).or
      ((⟨Rew.empty ▹ ∼φ⟩ : Semiformula.Operator L₁ k).and Y)).val e ↔ Y.val e := by
  have hφ : ¬ M↓[L₁] ⊧ φ := by simpa using hφ'
  simp only [Semiformula.val_operator_or, Semiformula.val_operator_and, eval_rew_empty_iff]
  tauto

/-- Combine an interpretation of `insert φ T` and one of `insert (∼φ) T` into one interpretation
of `T`, following `π₀` where `φ` holds and `π₁` where `∼φ` holds.
- [Lin97, Lemma 6.4]
- [HP98, Lemma III.1.8] -/
def ite : DirectTranslation T L₂ where
  domain := ((⟨Rew.empty ▹ φ⟩ : Semiformula.Operator L₁ 1).and π₀.domain).or
    ((⟨Rew.empty ▹ ∼φ⟩ : Semiformula.Operator L₁ 1).and π₁.domain)
  rel {k} R := ((⟨Rew.empty ▹ φ⟩ : Semiformula.Operator L₁ k).and (π₀.rel R)).or
    ((⟨Rew.empty ▹ ∼φ⟩ : Semiformula.Operator L₁ k).and (π₁.rel R))
  func {k} f := ((⟨Rew.empty ▹ φ⟩ : Semiformula.Operator L₁ (k + 1)).and (π₀.func f)).or
    ((⟨Rew.empty ▹ ∼φ⟩ : Semiformula.Operator L₁ (k + 1)).and (π₁.func f))
  domain_nonempty := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    rw [models_domainNonempty_iff]
    rcases models_insert_cases φ hT with ⟨hφ, hT'⟩ | ⟨hφ', hT'⟩
    · have H := (models_domainNonempty_iff _).mp (models_of_provable hT' π₀.domain_nonempty)
      simpa only [ite_gate_iff φ hφ] using H
    · have H := (models_domainNonempty_iff _).mp (models_of_provable hT' π₁.domain_nonempty)
      simpa only [ite_gate_iff' φ hφ'] using H
  func_defined f := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    rw [models_funcDefined_iff]
    rcases models_insert_cases φ hT with ⟨hφ, hT'⟩ | ⟨hφ', hT'⟩
    · have H := (models_funcDefined_iff _ _).mp (models_of_provable hT' (π₀.func_defined f))
      simpa only [ite_gate_iff φ hφ] using H
    · have H := (models_funcDefined_iff _ _).mp (models_of_provable hT' (π₁.func_defined f))
      simpa only [ite_gate_iff' φ hφ'] using H
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    rw [models_preserveEq_iff]
    rcases models_insert_cases φ hT with ⟨hφ, hT'⟩ | ⟨hφ', hT'⟩
    · have H := (models_preserveEq_iff _ _).mp (models_of_provable hT' π₀.preserve_eq)
      simpa only [ite_gate_iff φ hφ] using H
    · have H := (models_preserveEq_iff _ _).mp (models_of_provable hT' π₁.preserve_eq)
      simpa only [ite_gate_iff' φ hφ'] using H

variable {M : Type*} [Nonempty M] [Tarski.Structure L₁ M]

private lemma ite_translate_iff (hφ : M↓[L₁] ⊧ φ) {ξ n} (σ : Semiformula L₂ ξ n) {e : Fin n → M}
    {ε : ξ → M} :
    Semiformula.Eval e ε ((ite φ π₀ π₁).translate σ) ↔ Semiformula.Eval e ε (π₀.translate σ) :=
  eval_translate_congr _ _ (fun _ ↦ ite_gate_iff φ hφ) (fun _ _ ↦ ite_gate_iff φ hφ)
    (fun _ _ ↦ ite_gate_iff φ hφ) σ

private lemma ite_translate_iff' (hφ' : M↓[L₁] ⊧ ∼φ) {ξ n} (σ : Semiformula L₂ ξ n) {e : Fin n → M}
    {ε : ξ → M} :
    Semiformula.Eval e ε ((ite φ π₀ π₁).translate σ) ↔ Semiformula.Eval e ε (π₁.translate σ) :=
  eval_translate_congr _ _ (fun _ ↦ ite_gate_iff' φ hφ') (fun _ _ ↦ ite_gate_iff' φ hφ')
    (fun _ _ ↦ ite_gate_iff' φ hφ') σ

end ite

end DirectTranslation

namespace DirectInterpretation

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T] {U : Theory L₂}

/-- Consistency transfers along interpretation: if `T` interprets `U` and `T` is consistent, so
is `U`.
- [HP98, Corollary III.1.6]
- [Lin97, p. 76] -/
theorem consistent (π : T ⊳ U) [Entailment.Consistent T] : Entailment.Consistent U :=
  Entailment.Consistent.of_unprovable (φ := ⊥) fun h ↦
    Entailment.Consistent.not_bot (𝓢 := T) (by simpa using π.sound h)

/-- If `T` interprets `U` and `U'` is (provably) weaker than `U`, then `T` interprets `U'`,
via the same translation.
- [Lin97, Ch. 6 §1] -/
abbrev ofWeakerThanRight (π : T ⊳ U) {U' : Theory L₂} [U' ⪯ U] : T ⊳ U' where
  trln := π.trln
  interpret_theory _φ hφ := π.sound (Entailment.WeakerThan.pbl (Entailment.by_axm hφ))

/-- If `T` interprets `U` and `T'` is (provably) stronger than `T`, then `T'` interprets `U`.
- [Lin97, Ch. 6 §1] -/
abbrev ofWeakerThanLeft (π : T ⊳ U) {T' : Theory L₁} [𝗘𝗤 _ ⪯ T'] [T ⪯ T'] : T' ⊳ U where
  trln := π.trln.ofWeakerThan
  interpret_theory φ hφ := by
    have h : T' ⊢ π.trln.translate φ := Entailment.WeakerThan.pbl (π.interpret_theory φ hφ)
    simpa using h

/-- From an interpretation of `U` in `insert φ T` and one in `insert (∼φ) T`, build an
interpretation of `U` in `T`, following `π₀` where `φ` holds and `π₁` where `∼φ` holds.
- [Lin97, Lemma 6.4]
- [HP98, Lemma III.1.8] -/
abbrev orCases (φ : Sentence L₁) [𝗘𝗤 _ ⪯ insert φ T] [𝗘𝗤 _ ⪯ insert (∼φ) T]
    (π₀ : insert φ T ⊳ U) (π₁ : insert (∼φ) T ⊳ U) : T ⊳ U where
  trln := DirectTranslation.ite φ π₀.trln π₁.trln
  interpret_theory σ hσ := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    rcases DirectTranslation.models_insert_cases φ hT with ⟨hφ, hT'⟩ | ⟨hφ', hT'⟩
    · exact (DirectTranslation.ite_translate_iff φ π₀.trln π₁.trln hφ σ).mpr
        (models_of_provable hT' (π₀.interpret_theory σ hσ))
    · exact (DirectTranslation.ite_translate_iff' φ π₀.trln π₁.trln hφ' σ).mpr
        (models_of_provable hT' (π₁.interpret_theory σ hσ))

/-- An interpretation is faithful when provability of a translated sentence in `T` implies
provability of the sentence itself in `U`.
- [Lin97, §6.2 p. 84]
- [HP98, Definition III.1.9] -/
def Faithful (π : T ⊳ U) : Prop := ∀ σ : Sentence L₂, T ⊢ π.translate σ → U ⊢ σ

/-- An interpretation is faithful on `Γ` when the implication of `Faithful` holds for sentences
in `Γ`.
- [Lin97, §6.2 p. 84]
- [HP98, Definition III.1.9] -/
def FaithfulOn (π : T ⊳ U) (Γ : Set (Sentence L₂)) : Prop := ∀ σ ∈ Γ, T ⊢ π.translate σ → U ⊢ σ

lemma Faithful.faithfulOn {π : T ⊳ U} (h : π.Faithful) (Γ : Set (Sentence L₂)) : π.FaithfulOn Γ :=
  fun σ _ ↦ h σ

lemma Faithful.of_faithfulOn_univ {π : T ⊳ U} (h : π.FaithfulOn Set.univ) : π.Faithful :=
  fun σ ↦ h σ (Set.mem_univ σ)

end DirectInterpretation

end FFL.FirstOrder
