module

public import AlphaCentauri.Axiomatizability.Basic
public import AlphaCentauri.Reflection.CollapseFormula
public import AlphaCentauri.ToFoundation.Theory

@[expose] public section
/-!
# The unboundedness theorem for a $\Gamma_{n + 1}$-axiomatizable extension

The local reflection schema of `T` on a class is not contained in any consistent extension of `T`
axiomatized by a $\Delta_1$-presented set of sentences of the dual class. The axiomatization is
collapsed to the single sentence `collapseSentence` of
`AlphaCentauri.Reflection.CollapseFormula`, which reduces the claim to the case of an extension by
one sentence.

Two narrowings of [AB05], which asks only for an r.e. extension: the axiomatization is
$\Delta_1$-presented, since Craig's trick is in neither Foundation nor this repository, and its
sentences are strict prenex, since the partial truth predicates agree with truth only there.

- [AB05, Theorem 23]
- [AB05, Remark 24]
- [Lin97, Theorem 4.3]
- [Lin97, Corollary 4.2]
-/

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping

variable {T : ArithmeticTheory} [T.Δ₁] {n : ℕ} {Γ : Polarity}

section
variable {U : ArithmeticTheory} [U.Δ₁]

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Reading standard codes inside a model -/

/-- Membership in the $\Delta_1$ class of a theory is absolute between `ℕ` and a model of `𝗜𝚺₁` at
standard codes. -/
lemma mem_Δ₁Class_natCast_iff {m : ℕ} : m ∈ U.Δ₁Class ↔ (m : V) ∈ U.Δ₁Class := by
  simpa using Defined.shigmaOne_absolute V (φ := U.Δ₁ch)
    (R := fun v ↦ v 0 ∈ U.Δ₁Class) (R' := fun v ↦ v 0 ∈ U.Δ₁Class)
    Δ₁Class.defined Δ₁Class.defined ![m]

/-- Being the code of a formula is absolute between `ℕ` and a model of `𝗜𝚺₁` at standard codes. -/
lemma isSemiformula_natCast_iff {m : ℕ} :
    IsSemiformula ℒₒᵣ 0 m ↔ IsSemiformula ℒₒᵣ (0 : V) (m : V) := by
  simpa using Defined.shigmaOne_absolute V (φ := isSemiformula ℒₒᵣ)
    (R := fun v ↦ IsSemiformula ℒₒᵣ (v 0) (v 1)) (R' := fun v ↦ IsSemiformula ℒₒᵣ (v 0) (v 1))
    IsSemiformula.defined IsSemiformula.defined ![0, m]

/-- A standard code of a formula that lies in the $\Delta_1$ class of `U` is the code of a member
of `U`. -/
lemma exists_mem_eq_quote {m : ℕ} (hmem : (m : V) ∈ U.Δ₁Class)
    (hsemi : IsSemiformula ℒₒᵣ (0 : V) (m : V)) : ∃ σ ∈ U, (m : V) = (⌜σ⌝ : V) := by
  obtain ⟨F, hF⟩ := IsSemiformula.sound (L := ℒₒᵣ) (isSemiformula_natCast_iff (V := V) |>.mpr hsemi)
  have : (⌜F⌝ : ℕ) ∈ U.Δ₁Class := by
    rw [hF]; exact mem_Δ₁Class_natCast_iff (V := V) |>.mpr hmem
  obtain ⟨σ, hσ, rfl⟩ := Δ₁Class.mem_iff_s.mp this
  exact ⟨σ, hσ, by rw [← hF]; simp [Sentence.quote_def, Semiformula.coe_quote_eq_quote]⟩

/-! ## Semantics of the collapse sentence -/

/-- Truth of `collapseFormula` at polarity `𝚷` in a model of `𝗜𝚺₁`. -/
lemma eval_collapseFormula_pi (c : V) :
    V ⊧/![c] (collapseFormula T U n 𝚷) ↔
      ∀ y ∈ U.Δ₁Class, IsSemiformula ℒₒᵣ (0 : V) y → IsStrictPi (n + 1) y →
        (∀ u < y, ¬Proof T u (neg ℒₒᵣ c)) → PiSatisfaction (n + 1) y 0 := by
  simp [collapseFormula, HierarchySymbol.Semiformula.val_sigma,
    (Δ₁Class.defined (T := U) (V := V)).df,
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).df,
    (IsStrictPi.defined (V := V) (n + 1)).df,
    (neg.defined (L := ℒₒᵣ) (V := V)).df,
    (Proof.defined (T := T) (V := V)).proper.iff',
    (Proof.defined (T := T) (V := V)).df,
    (PiSatisfaction.defined (V := V) n).df]

/-- Truth of `collapseFormula` at polarity `𝚺` in a model of `𝗜𝚺₁`. -/
lemma eval_collapseFormula_sigma (c : V) :
    V ⊧/![c] (collapseFormula T U n 𝚺) ↔
      ∃ y : V, (∃ u < y, Proof T u (neg ℒₒᵣ c)) ∧
        ∀ z < y, z ∈ U.Δ₁Class → IsSemiformula ℒₒᵣ (0 : V) z → IsStrictSigma (n + 1) z →
          SigmaSatisfaction (n + 1) z 0 := by
  simp [collapseFormula, HierarchySymbol.Semiformula.val_sigma,
    (Δ₁Class.defined (T := U) (V := V)).proper.iff',
    (Δ₁Class.defined (T := U) (V := V)).df,
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).proper.iff',
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).df,
    (IsStrictSigma.defined (V := V) (n + 1)).proper.iff',
    (IsStrictSigma.defined (V := V) (n + 1)).df,
    (neg.defined (L := ℒₒᵣ) (V := V)).df,
    (Proof.defined (T := T) (V := V)).df,
    (SigmaSatisfaction.defined (V := V) n).df]

/-- Truth of `collapseSentence` at polarity `𝚷` in a model of `𝗜𝚺₁`. -/
lemma models_collapseSentence_pi_iff :
    V↓[ℒₒᵣ] ⊧ collapseSentence T U n 𝚷 ↔
      ∀ y ∈ U.Δ₁Class, IsSemiformula ℒₒᵣ (0 : V) y → IsStrictPi (n + 1) y →
        (∀ u < y, ¬Proof T u (⌜∼fixedpoint (collapseFormula T U n 𝚷)⌝ : V)) →
          PiSatisfaction (n + 1) y 0 := by
  have h : V↓[ℒₒᵣ] ⊧ collapseSentence T U n 𝚷 ↔
      V ⊧/![(⌜fixedpoint (collapseFormula T U n 𝚷)⌝ : V)] (collapseFormula T U n 𝚷) := by
    simp [collapseSentence, models_iff]
  rw [h, eval_collapseFormula_pi]
  simp [Sentence.quote_eq]

/-- Truth of `collapseSentence` at polarity `𝚺` in a model of `𝗜𝚺₁`. -/
lemma models_collapseSentence_sigma_iff :
    V↓[ℒₒᵣ] ⊧ collapseSentence T U n 𝚺 ↔
      ∃ y : V, (∃ u < y, Proof T u (⌜∼fixedpoint (collapseFormula T U n 𝚺)⌝ : V)) ∧
        ∀ z < y, z ∈ U.Δ₁Class → IsSemiformula ℒₒᵣ (0 : V) z → IsStrictSigma (n + 1) z →
          SigmaSatisfaction (n + 1) z 0 := by
  have h : V↓[ℒₒᵣ] ⊧ collapseSentence T U n 𝚺 ↔
      V ⊧/![(⌜fixedpoint (collapseFormula T U n 𝚺)⌝ : V)] (collapseFormula T U n 𝚺) := by
    simp [collapseSentence, models_iff]
  rw [h, eval_collapseFormula_sigma]
  simp [Sentence.quote_eq]

end

/-! ## The collapse -/

variable [𝗜𝚺₁ ⪯ T]

/-- `T` refutes `collapseSentence` exactly when it refutes the fixed point of `collapseFormula`. -/
private lemma neg_collapseSentence_iff :
    T ⊢ ∼collapseSentence T U n Γ ↔ T ⊢ ∼fixedpoint (collapseFormula T U n Γ) :=
  (provable_neg_iff (WeakerThan.pbl (provable_fixedpoint_collapseFormula_iff T U n Γ))).symm

/-- The polarity `𝚷` case of `inconsistent_union_of_inconsistent_insert`. -/
private lemma inconsistent_union_of_inconsistent_insert_pi
    (hΓ : ∀ σ ∈ U, StrictHierarchy 𝚷 (n + 1) σ)
    (h : Inconsistent (insert (collapseSentence T U n 𝚷) T)) : Inconsistent (T ∪ U) := by
  have : 𝗜𝚺₁ ⪯ T ∪ U := WeakerThan.trans (𝓣 := T) inferInstance inferInstance
  have : 𝗘𝗤 ℒₒᵣ ⪯ T ∪ U := WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  have hneg : T ⊢ ∼collapseSentence T U n 𝚷 := provable_neg_of_inconsistent_insert h
  have hnegζ : T ⊢ ∼fixedpoint (collapseFormula T U n 𝚷) :=
    neg_collapseSentence_iff.mp hneg
  have hprov : T ∪ U ⊢ collapseSentence T U n 𝚷 := by
    apply Arithmetic.complete.{0}
    intro M _ _
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ (T ∪ U) inferInstance
    apply models_collapseSentence_pi_iff.mpr
    intro y hmem hsemi _ hlt
    have hp : Proof T ((⌜hnegζ.get⌝ : ℕ) : M) ⌜∼fixedpoint (collapseFormula T U n 𝚷)⌝ := by
      simp [coe_quote_proof_eq]
    have hle : y ≤ ((⌜hnegζ.get⌝ : ℕ) : M) := by
      by_contra hcon
      exact hlt _ (not_le.mp hcon) hp
    obtain ⟨m, rfl⟩ := eq_nat_of_le_nat hle
    obtain ⟨σ, hσ, hmσ⟩ := exists_mem_eq_quote hmem hsemi
    rw [hmσ]
    apply (piSatisfaction_quote_iff (hΓ σ hσ) ![]).mpr
    have hσM : M↓[ℒₒᵣ] ⊧ σ := models_of_mem (Set.mem_union_right T hσ)
    simpa [models_iff] using hσM
  exact inconsistent_of_provable_of_unprovable hprov (WeakerThan.pbl hneg)

/-- The polarity `𝚺` case of `inconsistent_union_of_inconsistent_insert`. -/
private lemma inconsistent_union_of_inconsistent_insert_sigma
    (hΓ : ∀ σ ∈ U, StrictHierarchy 𝚺 (n + 1) σ)
    (h : Inconsistent (insert (collapseSentence T U n 𝚺) T)) : Inconsistent (T ∪ U) := by
  have : 𝗜𝚺₁ ⪯ T ∪ U := WeakerThan.trans (𝓣 := T) inferInstance inferInstance
  have : 𝗘𝗤 ℒₒᵣ ⪯ T ∪ U := WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  have hneg : T ⊢ ∼collapseSentence T U n 𝚺 := provable_neg_of_inconsistent_insert h
  have hnegζ : T ⊢ ∼fixedpoint (collapseFormula T U n 𝚺) :=
    neg_collapseSentence_iff.mp hneg
  have hprov : T ∪ U ⊢ collapseSentence T U n 𝚺 := by
    apply Arithmetic.complete.{0}
    intro M _ _
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ (T ∪ U) inferInstance
    have hp : Proof T ((⌜hnegζ.get⌝ : ℕ) : M) ⌜∼fixedpoint (collapseFormula T U n 𝚺)⌝ := by
      simp [coe_quote_proof_eq]
    refine models_collapseSentence_sigma_iff.mpr
      ⟨((⌜hnegζ.get⌝ : ℕ) + 1 : ℕ), ⟨_, by push_cast; simp, hp⟩, ?_⟩
    intro z hz hmem hsemi _
    obtain ⟨m, rfl⟩ := eq_nat_of_lt_nat hz
    obtain ⟨σ, hσ, hmσ⟩ := exists_mem_eq_quote hmem hsemi
    rw [hmσ]
    apply (sigmaSatisfaction_quote_iff (hΓ σ hσ) ![]).mpr
    have hσM : M↓[ℒₒᵣ] ⊧ σ := models_of_mem (Set.mem_union_right T hσ)
    simpa [models_iff] using hσM
  exact inconsistent_of_provable_of_unprovable hprov (WeakerThan.pbl hneg)

/-- If adjoining `collapseSentence` to `T` is inconsistent then so is `T ∪ U`.
- [Lin97, Theorem 4.3] -/
private lemma inconsistent_union_of_inconsistent_insert
    (hΓ : ∀ σ ∈ U, StrictHierarchy Γ (n + 1) σ)
    (h : Inconsistent (insert (collapseSentence T U n Γ) T)) : Inconsistent (T ∪ U) := by
  cases Γ with
  | sigma => exact inconsistent_union_of_inconsistent_insert_sigma hΓ h
  | pi => exact inconsistent_union_of_inconsistent_insert_pi hΓ h

/-- The polarity `𝚷` case of `provable_of_mem`. -/
private lemma provable_of_mem_pi (hΓ : ∀ σ ∈ U, StrictHierarchy 𝚷 (n + 1) σ)
    (hcon : Consistent (insert (collapseSentence T U n 𝚷) T))
    {σ : ArithmeticSentence} (hσ : σ ∈ U) :
    insert (collapseSentence T U n 𝚷) T ⊢ σ := by
  have hnζ : ¬T ⊢ ∼fixedpoint (collapseFormula T U n 𝚷) := fun h ↦
    hcon.not_inc (inconsistent_insert_of_provable_neg (neg_collapseSentence_iff.mpr h))
  have key : 𝗜𝚺₁ ⊢ collapseSentence T U n 𝚷 🡒 σ := by
    apply Arithmetic.complete.{0}
    intro M _ _
    simp only [Semantics.Imp.models_imply]
    intro hθ
    have hsat := models_collapseSentence_pi_iff.mp hθ (⌜σ⌝ : M) (by simp [hσ])
      (by simp) ((isStrictPi_quote_iff σ).mpr (hΓ σ hσ)) ?_
    · exact (piSatisfaction_quote_iff (hΓ σ hσ) ![]).mp (by simpa using hsat)
    · intro u hu hpu
      rw [← Sentence.coe_quote_eq_quote] at hu
      obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hu
      exact hnζ (provable_of_standard_proof (V := M) hpu)
  have hT : T ⪯ insert (collapseSentence T U n 𝚷) T := WeakerThan.ofSubset (Set.subset_insert _ _)
  have key' : insert (collapseSentence T U n 𝚷) T ⊢ collapseSentence T U n 𝚷 🡒 σ :=
    hT.pbl (WeakerThan.pbl (𝓢 := 𝗜𝚺₁) key)
  exact key' ⨀ by_axm (Set.mem_insert _ _)

/-- The polarity `𝚺` case of `provable_of_mem`. -/
private lemma provable_of_mem_sigma (hΓ : ∀ σ ∈ U, StrictHierarchy 𝚺 (n + 1) σ)
    (hcon : Consistent (insert (collapseSentence T U n 𝚺) T))
    {σ : ArithmeticSentence} (hσ : σ ∈ U) :
    insert (collapseSentence T U n 𝚺) T ⊢ σ := by
  have hnζ : ¬T ⊢ ∼fixedpoint (collapseFormula T U n 𝚺) := fun h ↦
    hcon.not_inc (inconsistent_insert_of_provable_neg (neg_collapseSentence_iff.mpr h))
  have key : 𝗜𝚺₁ ⊢ collapseSentence T U n 𝚺 🡒 σ := by
    apply Arithmetic.complete.{0}
    intro M _ _
    simp only [Semantics.Imp.models_imply]
    intro hθ
    obtain ⟨y, ⟨u, huy, hpu⟩, hall⟩ := models_collapseSentence_sigma_iff.mp hθ
    have hnu : ¬u ≤ (⌜σ⌝ : M) := by
      intro hle
      rw [← Sentence.coe_quote_eq_quote] at hle
      obtain ⟨j, rfl⟩ := eq_nat_of_le_nat hle
      exact hnζ (provable_of_standard_proof (V := M) hpu)
    have hlt : (⌜σ⌝ : M) < y := lt_trans (not_le.mp hnu) huy
    have hsat := hall (⌜σ⌝ : M) hlt (by simp [hσ]) (by simp)
      ((isStrictSigma_quote_iff σ).mpr (hΓ σ hσ))
    exact (sigmaSatisfaction_quote_iff (hΓ σ hσ) ![]).mp (by simpa using hsat)
  have hT : T ⪯ insert (collapseSentence T U n 𝚺) T := WeakerThan.ofSubset (Set.subset_insert _ _)
  have key' : insert (collapseSentence T U n 𝚺) T ⊢ collapseSentence T U n 𝚺 🡒 σ :=
    hT.pbl (WeakerThan.pbl (𝓢 := 𝗜𝚺₁) key)
  exact key' ⨀ by_axm (Set.mem_insert _ _)

/-- A consistent extension of `T` by `collapseSentence` proves every member of `U`.
- [Lin97, Theorem 4.3] -/
private lemma provable_of_mem (hΓ : ∀ σ ∈ U, StrictHierarchy Γ (n + 1) σ)
    (hcon : Consistent (insert (collapseSentence T U n Γ) T))
    {σ : ArithmeticSentence} (hσ : σ ∈ U) :
    insert (collapseSentence T U n Γ) T ⊢ σ := by
  cases Γ with
  | sigma => exact provable_of_mem_sigma hΓ hcon hσ
  | pi => exact provable_of_mem_pi hΓ hcon hσ

/-- The case of `exists_sentence_weakerThan_of_consistent` where `U` axiomatizes itself.
- [Lin97, Theorem 4.3] -/
private lemma exists_sentence_weakerThan_of_forall_mem
    (hΓ : ∀ σ ∈ U, StrictHierarchy Γ (n + 1) σ) [Consistent (T ∪ U)] :
    ∃ θ : ArithmeticSentence, Hierarchy Γ (n + 1) θ ∧
      T ∪ U ⪯ insert θ T ∧ Consistent (insert θ T) := by
  have hcon : Consistent (insert (collapseSentence T U n Γ) T) := by
    by_contra hc
    exact (inconsistent_union_of_inconsistent_insert hΓ
      (not_consistent_iff_inconsistent.mp hc)).not_con inferInstance
  refine ⟨collapseSentence T U n Γ, hierarchy_collapseSentence T U n Γ, ?_, hcon⟩
  apply WeakerThan.ofAxm!
  rintro φ (hφ | hφ)
  · exact by_axm (Set.mem_insert_of_mem _ hφ)
  · exact provable_of_mem hΓ hcon hφ

end

/-! ## The unboundedness theorem -/

variable {U U' : ArithmeticTheory} [U'.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- A consistent extension of `T` by a $\Gamma_{n + 1}$-axiomatizable theory is contained in a
consistent extension of `T` by a single `Γ (n + 1)` sentence.
- [Lin97, Theorem 4.3] -/
theorem exists_sentence_weakerThan_of_consistent
    (hΓ : AxiomatizableBy (StrictHierarchy Γ (n + 1)) U U') [Consistent (T ∪ U)] :
    ∃ θ : ArithmeticSentence, Hierarchy Γ (n + 1) θ ∧
      T ∪ U ⪯ insert θ T ∧ Consistent (insert θ T) := by
  have e : T ∪ U ≊ T ∪ U' := hΓ.equiv.union_right T
  have : Consistent (T ∪ U') := Consistent.of_le ‹Consistent (T ∪ U)› e.symm.le
  obtain ⟨θ, hθ, hle, hcon⟩ := exists_sentence_weakerThan_of_forall_mem (T := T) hΓ.forall_mem
  exact ⟨θ, hθ, e.le.trans hle, hcon⟩

/-- Unboundedness: a $\Gamma_{n + 1}$-axiomatizable extension of `T` proving the local reflection
schema of `T` on the dual class is inconsistent.
- [AB05, Theorem 23]
- [Lin97, Corollary 4.2] -/
theorem inconsistent_of_localReflectionOn_weakerThan_union
    (hΓ : AxiomatizableBy (StrictHierarchy Γ (n + 1)) U U')
    (h : 𝗥𝗳𝗻[Hierarchy Γ.alt (n + 1)] T ⪯ T ∪ U) : Inconsistent (T ∪ U) := by
  by_contra hc
  have : Consistent (T ∪ U) := not_inconsistent_iff_consistent.mp hc
  obtain ⟨θ, hθ, hle, hcon⟩ := exists_sentence_weakerThan_of_consistent (T := T) hΓ
  exact hcon.not_inc
    (inconsistent_of_localReflectionOn_weakerThan_insert hθ (h.trans hle))

/-- Unboundedness: a consistent $\Gamma_{n + 1}$-axiomatizable extension of `T` does not contain
the local reflection schema of `T` on the dual class.
- [AB05, Theorem 23]
- [Lin97, Corollary 4.2] -/
theorem not_localReflectionOn_weakerThan_union
    (hΓ : AxiomatizableBy (StrictHierarchy Γ (n + 1)) U U') [Consistent (T ∪ U)] :
    ¬𝗥𝗳𝗻[Hierarchy Γ.alt (n + 1)] T ⪯ T ∪ U :=
  fun h ↦ (inconsistent_of_localReflectionOn_weakerThan_union hΓ h).not_con
    inferInstance

end FFL.FirstOrder.Arithmetic
