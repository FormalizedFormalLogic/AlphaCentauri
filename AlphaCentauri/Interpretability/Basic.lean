module

public import Foundation.FirstOrder.Interpretation

/-!
# API for `DirectInterpretation`

Additional API for Foundation's `DirectTranslation` and `DirectInterpretation` (`T ⊳ U`):
transport of a translation along a stronger base theory, consistency transfer, monotonicity in
both arguments, the disjunction lemma, and faithful interpretations.
-/

@[expose] public section

namespace LO.FirstOrder

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

variable {T' : Theory L₁} [𝗘𝗤 _ ⪯ T'] [T ⪯ T'] (π : DirectTranslation T L₂)

@[simp] lemma ofWeakerThan_domain : (π.ofWeakerThan (T' := T')).domain = π.domain := rfl

@[simp] lemma ofWeakerThan_rel {k} (R : L₂.Rel k) : (π.ofWeakerThan (T' := T')).rel R = π.rel R := rfl

@[simp] lemma ofWeakerThan_func {k} (f : L₂.Func k) : (π.ofWeakerThan (T' := T')).func f = π.func f := rfl

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
  | hrel => simp [DirectTranslation.translateRel, ofWeakerThan_varEqual]
  | hnrel => simp [DirectTranslation.translateRel, ofWeakerThan_varEqual]
  | hand _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hor _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hall _ ih => simp [DirectTranslation.fal, ih]
  | hexs _ ih => simp [DirectTranslation.exs, ih]

omit [𝗘𝗤 L₁ ⪯ T] [T ⪯ T'] in
private lemma func_defined_iff {U : Theory L₁} [𝗘𝗤 _ ⪯ U] (τ : DirectTranslation U L₂)
    {M : Type*} [Nonempty M] [Structure L₁ M] [Structure.Eq L₁ M] (hU : M↓[L₁] ⊧* U)
    {k} (g : L₂.Func k) {e' : Fin k → M} (h : ∀ i, Semiformula.Eval ![e' i] Empty.elim τ.domain) :
    ∃! y : M, Semiformula.Eval ![y] Empty.elim τ.domain ∧ Semiformula.Eval (y :> e') Empty.elim (τ.func g) := by
  have H := models_of_provable hU (τ.func_defined g)
  rw [models_iff, Semiformula.Realize] at H
  simp only [Semiformula.eval_allClosure, LogicalConnective.HomClass.map_imply,
    Semiformula.eval_substs, Matrix.conj_hom_prop, Semiformula.eval_existsUnique,
    Function.comp_def, Matrix.comp_vecCons', Semiterm.val_bvar, Matrix.empty_eq] at H
  simpa using H e' h

omit [𝗘𝗤 L₁ ⪯ T] [T ⪯ T'] in
private lemma preserve_eq_iff {U : Theory L₁} [𝗘𝗤 _ ⪯ U] (τ : DirectTranslation U L₂)
    {M : Type*} [Nonempty M] [Structure L₁ M] [Structure.Eq L₁ M] (hU : M↓[L₁] ⊧* U)
    {x y : M} (hx : Semiformula.Eval ![x] Empty.elim τ.domain) (hy : Semiformula.Eval ![y] Empty.elim τ.domain) :
    Semiformula.Eval ![x, y] Empty.elim (τ.rel Language.Eq.eq) ↔ x = y := by
  have H := models_of_provable hU τ.preserve_eq
  rw [models_iff, Semiformula.Realize] at H
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Function.comp_def,
    Matrix.comp_vecCons', Semiterm.val_bvar, Matrix.empty_eq, Semiformula.eval_all] at H
  simpa using H x y hx hy

section ite

variable (φ : Sentence L₁) [𝗘𝗤 _ ⪯ insert φ T] [𝗘𝗤 _ ⪯ insert (∼φ) T]
  (π₀ : DirectTranslation (insert φ T) L₂) (π₁ : DirectTranslation (insert (∼φ) T) L₂)

@[simp] private lemma isEmpty_elim_eq_elim {α : Sort*} : (IsEmpty.elim (α := Empty) inferInstance : Empty → α) = Empty.elim :=
  funext fun a ↦ a.elim

omit [L₁.Eq] in
private lemma eval_rew_empty_iff {M : Type*} [Nonempty M] [Structure L₁ M] {n} {e : Fin n → M} (σ : Sentence L₁) :
    Semiformula.Eval e Empty.elim (Rew.empty ▹ σ) ↔ M↓[L₁] ⊧ σ := by
  rw [Semiformula.eval_empty]
  exact ⟨fun h ↦ Semiformula.Eval.of_eq h rfl (funext fun a ↦ a.elim),
    fun h ↦ Semiformula.Eval.of_eq h rfl (funext fun a ↦ a.elim)⟩

omit [L₁.Eq] in
private lemma ite_eval_iff {M : Type*} [Nonempty M] [Structure L₁ M] {n} {e : Fin n → M} {X Y : Semisentence L₁ n} :
    Semiformula.Eval e Empty.elim ((Rew.empty ▹ φ ⋏ X) ⋎ (Rew.empty ▹ ∼φ ⋏ Y)) ↔
      (M↓[L₁] ⊧ φ ∧ Semiformula.Eval e Empty.elim X) ∨ (M↓[L₁] ⊧ ∼φ ∧ Semiformula.Eval e Empty.elim Y) := by
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or, eval_rew_empty_iff]
  exact Iff.rfl

omit [L₁.Eq] in
private lemma ite_gate_iff {M : Type*} [Nonempty M] [Structure L₁ M] (hφ : M↓[L₁] ⊧ φ) {n} {e : Fin n → M}
    {X Y : Semisentence L₁ n} :
    (M↓[L₁] ⊧ φ ∧ Semiformula.Eval e Empty.elim X) ∨ (M↓[L₁] ⊧ ∼φ ∧ Semiformula.Eval e Empty.elim Y) ↔
      Semiformula.Eval e Empty.elim X := by
  constructor
  · rintro (⟨_, h⟩ | ⟨hne, _⟩)
    · exact h
    · exact absurd hφ (by simpa using hne)
  · exact fun h ↦ Or.inl ⟨hφ, h⟩

omit [L₁.Eq] in
private lemma ite_gate_iff' {M : Type*} [Nonempty M] [Structure L₁ M] (hφ' : M↓[L₁] ⊧ ∼φ) {n} {e : Fin n → M}
    {X Y : Semisentence L₁ n} :
    (M↓[L₁] ⊧ φ ∧ Semiformula.Eval e Empty.elim X) ∨ (M↓[L₁] ⊧ ∼φ ∧ Semiformula.Eval e Empty.elim Y) ↔
      Semiformula.Eval e Empty.elim Y := by
  constructor
  · rintro (⟨hφ, _⟩ | ⟨_, h⟩)
    · exact absurd hφ (by simpa using hφ')
    · exact h
  · exact fun h ↦ Or.inr ⟨hφ', h⟩

/-- Combine an interpretation of `insert φ T` and one of `insert (∼φ) T` into one interpretation
of `T`, following `π₀` where `φ` holds and `π₁` where `∼φ` holds.
- [Lin97, Lemma 6.4]
- [HP98, Lemma III.1.8] -/
def ite : DirectTranslation T L₂ where
  domain := (Rew.empty ▹ φ ⋏ π₀.domain) ⋎ (Rew.empty ▹ ∼φ ⋏ π₁.domain)
  rel R := (Rew.empty ▹ φ ⋏ π₀.rel R) ⋎ (Rew.empty ▹ ∼φ ⋏ π₁.rel R)
  func f := (Rew.empty ▹ φ ⋏ π₀.func f) ⋎ (Rew.empty ▹ ∼φ ⋏ π₁.func f)
  domain_nonempty := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    rcases Classical.em (M↓[L₁] ⊧ φ) with hφ | hφ
    · have hT' : M↓[L₁] ⊧* insert φ T := Semantics.ModelsSet.insert_iff.mpr ⟨hφ, hT⟩
      obtain ⟨x, hx⟩ : ∃ x : M, Semiformula.Eval ![x] Empty.elim π₀.domain := by
        simpa [models_iff] using models_of_provable hT' π₀.domain_nonempty
      exact models_iff.mpr ⟨x, Or.inl ⟨eval_rew_empty_iff φ |>.mpr hφ, hx⟩⟩
    · have hφ' : M↓[L₁] ⊧ ∼φ := by simp [hφ]
      have hT' : M↓[L₁] ⊧* insert (∼φ) T := Semantics.ModelsSet.insert_iff.mpr ⟨hφ', hT⟩
      obtain ⟨x, hx⟩ : ∃ x : M, Semiformula.Eval ![x] Empty.elim π₁.domain := by
        simpa [models_iff] using models_of_provable hT' π₁.domain_nonempty
      exact models_iff.mpr ⟨x, Or.inr ⟨eval_rew_empty_iff (∼φ) |>.mpr hφ', hx⟩⟩
  func_defined f := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    rw [models_iff, Semiformula.Realize]
    simp only [Semiformula.eval_allClosure]
    intro e'
    simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Matrix.conj_hom_prop,
      Function.comp_def, Semiformula.eval_existsUnique, Matrix.comp_vecCons', ite_eval_iff,
      Semiterm.val_bvar, Matrix.empty_eq, LogicalConnective.HomClass.map_and]
    intro h
    rcases Classical.em (M↓[L₁] ⊧ φ) with hφ | hφ
    · have hT' : M↓[L₁] ⊧* insert φ T := Semantics.ModelsSet.insert_iff.mpr ⟨hφ, hT⟩
      have hdom : ∀ i, Semiformula.Eval ![e' i] Empty.elim π₀.domain := fun i ↦ by
        rcases h i with ⟨_, hi⟩ | ⟨hne, _⟩
        · exact hi
        · exact absurd hφ (by simpa using hne)
      obtain ⟨y, ⟨hy1, hy2⟩, huniq⟩ := func_defined_iff π₀ hT' f hdom
      refine ⟨y, ⟨Or.inl ⟨hφ, hy1⟩, Or.inl ⟨hφ, hy2⟩⟩, ?_⟩
      rintro z ⟨(⟨_, hzdom⟩ | ⟨hne, _⟩), (⟨_, hzfunc⟩ | ⟨hne', _⟩)⟩
      · exact huniq z ⟨hzdom, hzfunc⟩
      · exact absurd hφ (by simpa using hne')
      · exact absurd hφ (by simpa using hne)
      · exact absurd hφ (by simpa using hne)
    · have hφ' : M↓[L₁] ⊧ ∼φ := by simp [hφ]
      have hT' : M↓[L₁] ⊧* insert (∼φ) T := Semantics.ModelsSet.insert_iff.mpr ⟨hφ', hT⟩
      have hdom : ∀ i, Semiformula.Eval ![e' i] Empty.elim π₁.domain := fun i ↦ by
        rcases h i with ⟨hne, _⟩ | ⟨_, hi⟩
        · exact absurd hne hφ
        · exact hi
      obtain ⟨y, ⟨hy1, hy2⟩, huniq⟩ := func_defined_iff π₁ hT' f hdom
      refine ⟨y, ⟨Or.inr ⟨hφ', hy1⟩, Or.inr ⟨hφ', hy2⟩⟩, ?_⟩
      rintro z ⟨(⟨hne, _⟩ | ⟨_, hzdom⟩), (⟨hne', _⟩ | ⟨_, hzfunc⟩)⟩
      · exact absurd hne hφ
      · exact absurd hne hφ
      · exact absurd hne' hφ
      · exact huniq z ⟨hzdom, hzfunc⟩
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    rw [models_iff, Semiformula.Realize]
    simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
      LogicalConnective.HomClass.map_iff, LogicalConnective.Prop.iff_eq, Semiformula.eval_substs,
      Function.comp_def, Matrix.comp_vecCons', Semiterm.val_bvar, Matrix.empty_eq, ite_eval_iff]
    intro x y hx hy
    rcases Classical.em (M↓[L₁] ⊧ φ) with hφ | hφ
    · have hT' : M↓[L₁] ⊧* insert φ T := Semantics.ModelsSet.insert_iff.mpr ⟨hφ, hT⟩
      have hx' : Semiformula.Eval ![x] Empty.elim π₀.domain := hx.resolve_right (fun ⟨hne, _⟩ ↦ absurd hφ (by simpa using hne)) |>.2
      have hy' : Semiformula.Eval ![y] Empty.elim π₀.domain := hy.resolve_right (fun ⟨hne, _⟩ ↦ absurd hφ (by simpa using hne)) |>.2
      have heq := preserve_eq_iff π₀ hT' hx' hy'
      rw [show (Semiformula.Eval (M := M) ![y, x] Empty.elim (“#1 = #0” : Semisentence L₁ 2)) = (x = y) from by simp]
      refine ⟨fun h ↦ ?_, fun h ↦ Or.inl ⟨hφ, heq.mpr h⟩⟩
      rcases h with ⟨_, h⟩ | ⟨hne, _⟩
      · exact heq.mp h
      · exact absurd hφ (by simpa using hne)
    · have hφ' : M↓[L₁] ⊧ ∼φ := by simp [hφ]
      have hx' : Semiformula.Eval ![x] Empty.elim π₁.domain := hx.resolve_left (fun ⟨hφx, _⟩ ↦ hφ hφx) |>.2
      have hy' : Semiformula.Eval ![y] Empty.elim π₁.domain := hy.resolve_left (fun ⟨hφy, _⟩ ↦ hφ hφy) |>.2
      have hT' : M↓[L₁] ⊧* insert (∼φ) T := Semantics.ModelsSet.insert_iff.mpr ⟨hφ', hT⟩
      have heq := preserve_eq_iff π₁ hT' hx' hy'
      rw [show (Semiformula.Eval (M := M) ![y, x] Empty.elim (“#1 = #0” : Semisentence L₁ 2)) = (x = y) from by simp]
      refine ⟨fun h ↦ ?_, fun h ↦ Or.inr ⟨hφ', heq.mpr h⟩⟩
      rcases h with ⟨hφx, _⟩ | ⟨_, h⟩
      · exact absurd hφx hφ
      · exact heq.mp h

variable {M : Type*} [Nonempty M] [Structure L₁ M]

@[simp] lemma ite_domain_def : (ite φ π₀ π₁).domain = (Rew.empty ▹ φ ⋏ π₀.domain) ⋎ (Rew.empty ▹ ∼φ ⋏ π₁.domain) := rfl

@[simp] lemma ite_rel_def {k} (R : L₂.Rel k) :
    (ite φ π₀ π₁).rel R = (Rew.empty ▹ φ ⋏ π₀.rel R) ⋎ (Rew.empty ▹ ∼φ ⋏ π₁.rel R) := rfl

@[simp] lemma ite_func_def {k} (f : L₂.Func k) :
    (ite φ π₀ π₁).func f = (Rew.empty ▹ φ ⋏ π₀.func f) ⋎ (Rew.empty ▹ ∼φ ⋏ π₁.func f) := rfl

private lemma ite_varEqual_iff (hφ : M↓[L₁] ⊧ φ) {ξ n} (t : Semiterm L₂ ξ n) :
    ∀ {e : Fin (n + 1) → M} {ε : ξ → M},
      Semiformula.Eval e ε ((ite φ π₀ π₁).varEqual t) ↔ Semiformula.Eval e ε (π₀.varEqual t) := by
  induction t with
  | bvar x => intro e ε; rfl
  | fvar x => intro e ε; rfl
  | func f v ih =>
    rename_i k
    intro e ε
    simp only [varEqual]
    simp only [Semiformula.eval_allItr, LogicalConnective.HomClass.map_imply, Matrix.conj_hom_prop,
      Semiformula.eval_embSubsts, Semiformula.eval_emb, Function.comp_def, Matrix.comp_vecCons',
      LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Semiterm.val_bvar,
      Matrix.empty_eq, ih, ite_domain_def, ite_func_def, ite_eval_iff, ite_gate_iff φ hφ]

private lemma ite_translateRel_iff (hφ : M↓[L₁] ⊧ φ) {ξ n k} (r : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n)
    {e : Fin n → M} {ε : ξ → M} :
    Semiformula.Eval e ε ((ite φ π₀ π₁).translateRel r v) ↔ Semiformula.Eval e ε (π₀.translateRel r v) := by
  simp only [translateRel]
  simp only [Semiformula.eval_allItr, LogicalConnective.HomClass.map_imply, Matrix.conj_hom_prop,
    Semiformula.eval_embSubsts, Semiformula.eval_emb, Function.comp_def, Matrix.comp_vecCons',
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Semiterm.val_bvar, Matrix.empty_eq,
    ite_varEqual_iff φ π₀ π₁ hφ, ite_domain_def, ite_rel_def, ite_eval_iff, ite_gate_iff φ hφ]

private lemma ite_translate_iff (hφ : M↓[L₁] ⊧ φ) {ξ n} (σ : Semiformula L₂ ξ n) {e : Fin n → M} {ε : ξ → M} :
    Semiformula.Eval e ε ((ite φ π₀ π₁).translate σ) ↔ Semiformula.Eval e ε (π₀.translate σ) := by
  induction σ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => exact ite_translateRel_iff φ π₀ π₁ hφ r v
  | hnrel r v => simp only [translate_nrel, LogicalConnective.HomClass.map_neg, ite_translateRel_iff φ π₀ π₁ hφ]
  | hand _ _ ih₁ ih₂ => simp only [LogicalConnective.HomClass.map_and, ih₁, ih₂]
  | hor _ _ ih₁ ih₂ => simp only [LogicalConnective.HomClass.map_or, ih₁, ih₂]
  | hall _ ih =>
    simp only [translate_all, fal]
    simp only [Semiformula.eval_ball, Semiformula.eval_emb,
      Semiformula.eval_substs, Function.comp_def, Matrix.comp_vecCons', Semiterm.val_bvar,
      ite_domain_def, ite_eval_iff, ite_gate_iff φ hφ, ih]
  | hexs _ ih =>
    simp only [translate_ex, exs]
    simp only [Semiformula.eval_bexs, Semiformula.eval_emb,
      Semiformula.eval_substs, Function.comp_def, Matrix.comp_vecCons', Semiterm.val_bvar,
      ite_domain_def, ite_eval_iff, ite_gate_iff φ hφ, ih]

private lemma ite_varEqual_iff' (hφ' : M↓[L₁] ⊧ ∼φ) {ξ n} (t : Semiterm L₂ ξ n) :
    ∀ {e : Fin (n + 1) → M} {ε : ξ → M},
      Semiformula.Eval e ε ((ite φ π₀ π₁).varEqual t) ↔ Semiformula.Eval e ε (π₁.varEqual t) := by
  induction t with
  | bvar x => intro e ε; rfl
  | fvar x => intro e ε; rfl
  | func f v ih =>
    rename_i k
    intro e ε
    simp only [varEqual]
    simp only [Semiformula.eval_allItr, LogicalConnective.HomClass.map_imply, Matrix.conj_hom_prop,
      Semiformula.eval_embSubsts, Semiformula.eval_emb, Function.comp_def, Matrix.comp_vecCons',
      LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Semiterm.val_bvar,
      Matrix.empty_eq, ih, ite_domain_def, ite_func_def, ite_eval_iff, ite_gate_iff' φ hφ']

private lemma ite_translateRel_iff' (hφ' : M↓[L₁] ⊧ ∼φ) {ξ n k} (r : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n)
    {e : Fin n → M} {ε : ξ → M} :
    Semiformula.Eval e ε ((ite φ π₀ π₁).translateRel r v) ↔ Semiformula.Eval e ε (π₁.translateRel r v) := by
  simp only [translateRel]
  simp only [Semiformula.eval_allItr, LogicalConnective.HomClass.map_imply, Matrix.conj_hom_prop,
    Semiformula.eval_embSubsts, Semiformula.eval_emb, Function.comp_def, Matrix.comp_vecCons',
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Semiterm.val_bvar, Matrix.empty_eq,
    ite_varEqual_iff' φ π₀ π₁ hφ', ite_domain_def, ite_rel_def, ite_eval_iff, ite_gate_iff' φ hφ']

private lemma ite_translate_iff' (hφ' : M↓[L₁] ⊧ ∼φ) {ξ n} (σ : Semiformula L₂ ξ n) {e : Fin n → M} {ε : ξ → M} :
    Semiformula.Eval e ε ((ite φ π₀ π₁).translate σ) ↔ Semiformula.Eval e ε (π₁.translate σ) := by
  induction σ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => exact ite_translateRel_iff' φ π₀ π₁ hφ' r v
  | hnrel r v => simp only [translate_nrel, LogicalConnective.HomClass.map_neg, ite_translateRel_iff' φ π₀ π₁ hφ']
  | hand _ _ ih₁ ih₂ => simp only [LogicalConnective.HomClass.map_and, ih₁, ih₂]
  | hor _ _ ih₁ ih₂ => simp only [LogicalConnective.HomClass.map_or, ih₁, ih₂]
  | hall _ ih =>
    simp only [translate_all, fal]
    simp only [Semiformula.eval_ball, Semiformula.eval_emb,
      Semiformula.eval_substs, Function.comp_def, Matrix.comp_vecCons', Semiterm.val_bvar,
      ite_domain_def, ite_eval_iff, ite_gate_iff' φ hφ', ih]
  | hexs _ ih =>
    simp only [translate_ex, exs]
    simp only [Semiformula.eval_bexs, Semiformula.eval_emb,
      Semiformula.eval_substs, Function.comp_def, Matrix.comp_vecCons', Semiterm.val_bvar,
      ite_domain_def, ite_eval_iff, ite_gate_iff' φ hφ', ih]

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
    Entailment.Consistent.not_bot (𝓢 := T) (by simpa using π.of_provability h)

/-- If `T` interprets `U` and `U'` is (provably) weaker than `U`, then `T` interprets `U'`,
via the same translation.
- [Lin97, Ch. 6 §1] -/
abbrev ofWeakerThanRight (π : T ⊳ U) {U' : Theory L₂} [U' ⪯ U] : T ⊳ U' where
  trln := π.trln
  interpret_theory _φ hφ := π.of_provability (Entailment.WeakerThan.pbl (Entailment.by_axm hφ))

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
    rcases Classical.em (M↓[L₁] ⊧ φ) with hφ | hφ
    · have hT' : M↓[L₁] ⊧* insert φ T := Semantics.ModelsSet.insert_iff.mpr ⟨hφ, hT⟩
      have h := models_of_provable hT' (π₀.interpret_theory σ hσ)
      exact (DirectTranslation.ite_translate_iff φ π₀.trln π₁.trln hφ σ).mpr h
    · have hφ' : M↓[L₁] ⊧ ∼φ := by simp [hφ]
      have hT' : M↓[L₁] ⊧* insert (∼φ) T := Semantics.ModelsSet.insert_iff.mpr ⟨hφ', hT⟩
      have h := models_of_provable hT' (π₁.interpret_theory σ hσ)
      exact (DirectTranslation.ite_translate_iff' φ π₀.trln π₁.trln hφ' σ).mpr h

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

end LO.FirstOrder
