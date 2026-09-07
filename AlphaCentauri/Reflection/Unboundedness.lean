module

public import AlphaCentauri.Reflection.CollapseFormula

@[expose] public section
/-!
# The unboundedness theorem for a `Δ₁` set of `Γ_{n + 1}` sentences

The local reflection schema of `T` on a class is not contained in any consistent extension of `T`
by a `Δ₁`-presented set of sentences of the dual class. The extension is collapsed to the single
sentence `collapseSentence` of `AlphaCentauri.Reflection.CollapseFormula`, which reduces the claim
to the case of an extension by one sentence.

- [AB05, Theorem 23]
- [AB05, Remark 24]
- [Lin97, Theorem 4.3]
- [Lin97, Corollary 4.2]
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment Bootstrapping

variable {T U : ArithmeticTheory} [T.Δ₁] [U.Δ₁] {n : ℕ} {Γ : Polarity}

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Reading standard codes inside a model -/

/-- Membership in the `Δ₁` class of a theory is absolute between `ℕ` and a model of `𝗜𝚺₁` at
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

/-- A standard code of a formula that lies in the `Δ₁` class of `U` is the code of a member of
`U`. -/
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
        (∀ u < y, ¬Proof T u (neg ℒₒᵣ c)) → SatPi (n + 1) y 0 := by
  simp [collapseFormula, HierarchySymbol.Semiformula.val_sigma,
    (Δ₁Class.defined (T := U) (V := V)).df,
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).df,
    (IsStrictPi.defined (V := V) (n + 1)).df,
    (neg.defined (L := ℒₒᵣ) (V := V)).df,
    (Proof.defined (T := T) (V := V)).proper.iff',
    (Proof.defined (T := T) (V := V)).df,
    (SatPi.defined (V := V) n).df]

/-- Truth of `collapseFormula` at polarity `𝚺` in a model of `𝗜𝚺₁`. -/
lemma eval_collapseFormula_sigma (c : V) :
    V ⊧/![c] (collapseFormula T U n 𝚺) ↔
      ∃ y : V, (∃ u < y, Proof T u (neg ℒₒᵣ c)) ∧
        ∀ z < y, z ∈ U.Δ₁Class → IsSemiformula ℒₒᵣ (0 : V) z → IsStrictSigma (n + 1) z →
          SatSigma (n + 1) z 0 := by
  simp [collapseFormula, HierarchySymbol.Semiformula.val_sigma,
    (Δ₁Class.defined (T := U) (V := V)).proper.iff',
    (Δ₁Class.defined (T := U) (V := V)).df,
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).proper.iff',
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).df,
    (IsStrictSigma.defined (V := V) (n + 1)).proper.iff',
    (IsStrictSigma.defined (V := V) (n + 1)).df,
    (neg.defined (L := ℒₒᵣ) (V := V)).df,
    (Proof.defined (T := T) (V := V)).df,
    (SatSigma.defined (V := V) n).df]

/-- Truth of `collapseSentence` at polarity `𝚷` in a model of `𝗜𝚺₁`. -/
lemma models_collapseSentence_pi_iff :
    V↓[ℒₒᵣ] ⊧ collapseSentence T U n 𝚷 ↔
      ∀ y ∈ U.Δ₁Class, IsSemiformula ℒₒᵣ (0 : V) y → IsStrictPi (n + 1) y →
        (∀ u < y, ¬Proof T u (⌜∼fixedpoint (collapseFormula T U n 𝚷)⌝ : V)) →
          SatPi (n + 1) y 0 := by
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
          SatSigma (n + 1) z 0 := by
  have h : V↓[ℒₒᵣ] ⊧ collapseSentence T U n 𝚺 ↔
      V ⊧/![(⌜fixedpoint (collapseFormula T U n 𝚺)⌝ : V)] (collapseFormula T U n 𝚺) := by
    simp [collapseSentence, models_iff]
  rw [h, eval_collapseFormula_sigma]
  simp [Sentence.quote_eq]

end

/-! ## The collapse -/

/-- Negation transfers along a provable equivalence. -/
private lemma neg_of_iff {S : ArithmeticTheory} {φ ψ : ArithmeticSentence}
    (e : S ⊢ φ 🡘 ψ) (h : S ⊢ ∼ψ) : S ⊢ ∼φ := by cl_prover [e, h]

/-- Negation transfers along a provable equivalence, in the other direction. -/
private lemma neg_of_iff' {S : ArithmeticTheory} {φ ψ : ArithmeticSentence}
    (e : S ⊢ φ 🡘 ψ) (h : S ⊢ ∼φ) : S ⊢ ∼ψ := by cl_prover [e, h]

/-- If adjoining `φ` makes `S` inconsistent then `S` refutes `φ`. -/
private lemma neg_of_inconsistent_insert {S : ArithmeticTheory} {φ : ArithmeticSentence}
    (h : Inconsistent (insert φ S)) : S ⊢ ∼φ := by
  have h' := deduction_iff.mp (h ⊥); cl_prover [h']

/-- If `S` refutes `φ` then adjoining `φ` makes `S` inconsistent. -/
private lemma inconsistent_insert_of_provable_neg {S : ArithmeticTheory} {φ : ArithmeticSentence}
    (h : S ⊢ ∼φ) : Inconsistent (insert φ S) :=
  inconsistent_of_provable (deduction_iff.mpr (by cl_prover [h]))

variable [𝗜𝚺₁ ⪯ T]

/-- `T` refutes the fixed point of `collapseFormula` if it refutes `collapseSentence`. -/
private lemma neg_fixedpoint_of_neg_collapseSentence
    (h : T ⊢ ∼collapseSentence T U n Γ) : T ⊢ ∼fixedpoint (collapseFormula T U n Γ) :=
  neg_of_iff (WeakerThan.pbl (provable_fixedpoint_collapseFormula_iff T U n Γ)) h

/-- `T` refutes `collapseSentence` if it refutes the fixed point of `collapseFormula`. -/
private lemma neg_collapseSentence_of_neg_fixedpoint
    (h : T ⊢ ∼fixedpoint (collapseFormula T U n Γ)) : T ⊢ ∼collapseSentence T U n Γ :=
  neg_of_iff' (WeakerThan.pbl (provable_fixedpoint_collapseFormula_iff T U n Γ)) h

/-- The polarity `𝚷` case of `inconsistent_union_of_inconsistent_insert`. -/
private lemma inconsistent_union_of_inconsistent_insert_pi
    (hΓ : ∀ σ ∈ U, StrictHierarchy 𝚷 (n + 1) σ)
    (h : Inconsistent (insert (collapseSentence T U n 𝚷) T)) : Inconsistent (T ∪ U) := by
  have : 𝗜𝚺₁ ⪯ T ∪ U := WeakerThan.trans (𝓣 := T) inferInstance inferInstance
  have : 𝗘𝗤 ℒₒᵣ ⪯ T ∪ U := WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  have hneg : T ⊢ ∼collapseSentence T U n 𝚷 := neg_of_inconsistent_insert h
  have hnegζ : T ⊢ ∼fixedpoint (collapseFormula T U n 𝚷) :=
    neg_fixedpoint_of_neg_collapseSentence hneg
  have hprov : T ∪ U ⊢ collapseSentence T U n 𝚷 := by
    apply Arithmetic.complete.{0}
    intro M _ _
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ (T ∪ U) inferInstance
    refine models_collapseSentence_pi_iff.mpr ?_
    intro y hmem hsemi _ hlt
    have hp : Proof T ((⌜hnegζ.get⌝ : ℕ) : M) ⌜∼fixedpoint (collapseFormula T U n 𝚷)⌝ := by
      simp [coe_quote_proof_eq]
    have hle : y ≤ ((⌜hnegζ.get⌝ : ℕ) : M) := by
      by_contra hcon
      exact hlt _ (not_le.mp hcon) hp
    obtain ⟨m, rfl⟩ := eq_nat_of_le_nat hle
    obtain ⟨σ, hσ, hmσ⟩ := exists_mem_eq_quote hmem hsemi
    rw [hmσ]
    refine (satPi_quote_iff (hΓ σ hσ) ![]).mpr ?_
    have hσM : M↓[ℒₒᵣ] ⊧ σ := models_of_mem (Set.mem_union_right T hσ)
    simpa [models_iff] using hσM
  exact inconsistent_of_provable_of_unprovable hprov (WeakerThan.pbl hneg)

/-- The polarity `𝚺` case of `inconsistent_union_of_inconsistent_insert`. -/
private lemma inconsistent_union_of_inconsistent_insert_sigma
    (hΓ : ∀ σ ∈ U, StrictHierarchy 𝚺 (n + 1) σ)
    (h : Inconsistent (insert (collapseSentence T U n 𝚺) T)) : Inconsistent (T ∪ U) := by
  have : 𝗜𝚺₁ ⪯ T ∪ U := WeakerThan.trans (𝓣 := T) inferInstance inferInstance
  have : 𝗘𝗤 ℒₒᵣ ⪯ T ∪ U := WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  have hneg : T ⊢ ∼collapseSentence T U n 𝚺 := neg_of_inconsistent_insert h
  have hnegζ : T ⊢ ∼fixedpoint (collapseFormula T U n 𝚺) :=
    neg_fixedpoint_of_neg_collapseSentence hneg
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
    refine (satSigma_quote_iff (hΓ σ hσ) ![]).mpr ?_
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
    hcon.not_inc (inconsistent_insert_of_provable_neg (neg_collapseSentence_of_neg_fixedpoint h))
  have key : 𝗜𝚺₁ ⊢ collapseSentence T U n 𝚷 🡒 σ := by
    apply Arithmetic.complete.{0}
    intro M _ _
    simp only [Semantics.Imp.models_imply]
    intro hθ
    have hsat := models_collapseSentence_pi_iff.mp hθ (⌜σ⌝ : M) (by simp [hσ])
      (by simp) ((isStrictPi_quote_iff σ).mpr (hΓ σ hσ)) ?_
    · exact (satPi_quote_iff (hΓ σ hσ) ![]).mp (by simpa using hsat)
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
    hcon.not_inc (inconsistent_insert_of_provable_neg (neg_collapseSentence_of_neg_fixedpoint h))
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
    exact (satSigma_quote_iff (hΓ σ hσ) ![]).mp (by simpa using hsat)
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

/-! ## The unboundedness theorem -/

/-- If `T ∪ U` is consistent, for a `Δ₁`-presented theory `U` all of whose members are
`StrictHierarchy Γ (n + 1)`, then there is a `Γ (n + 1)` sentence `θ` such that `T ∪ U ⪯ insert θ T`
and `insert θ T` is consistent.

`U`'s presentation is read as `Δ₁` rather than r.e.: this is a deliberate narrowing of [AB05]'s
"consistent r.e. extension", which reduces to an elementary presentation via Craig's trick, a
result absent from both Foundation and this repository. Restricting `U`'s members to
`StrictHierarchy Γ (n + 1)` rather than `Hierarchy Γ (n + 1)` is likewise deliberate: the partial
truth predicate used to build `θ` agrees with truth only on the strict prenex classes.
- [Lin97, Theorem 4.3] -/
theorem exists_sentence_weakerThan_of_consistent
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

/-- Unboundedness, for an extension by a `Δ₁`-presented set: if `T ∪ U`, for a `Δ₁`-presented
theory `U` all of whose members are `StrictHierarchy Γ (n + 1)`, proves the local reflection
schema of `T` on the dual class, then `T ∪ U` is inconsistent.

As in `exists_sentence_weakerThan_of_consistent`, `U`'s presentation is read as `Δ₁` rather than
r.e., and its members are restricted to `StrictHierarchy Γ (n + 1)` rather than
`Hierarchy Γ (n + 1)`.
- [AB05, Theorem 23]
- [Lin97, Corollary 4.2] -/
theorem inconsistent_of_localReflectionOnHierarchy_weakerThan_union
    (hΓ : ∀ σ ∈ U, StrictHierarchy Γ (n + 1) σ)
    (h : 𝗥𝗳𝗻[Γ.alt (n + 1)] T ⪯ T ∪ U) : Inconsistent (T ∪ U) := by
  by_contra hc
  have : Consistent (T ∪ U) := not_inconsistent_iff_consistent.mp hc
  obtain ⟨θ, hθ, hle, hcon⟩ := exists_sentence_weakerThan_of_consistent (T := T) hΓ
  exact hcon.not_inc
    (inconsistent_of_localReflectionOnHierarchy_weakerThan_insert hθ (h.trans hle))

/-- Unboundedness, for an extension by a `Δ₁`-presented set: a consistent `T ∪ U`, for a
`Δ₁`-presented theory `U` all of whose members are `StrictHierarchy Γ (n + 1)`, does not contain
the local reflection schema of `T` on the dual class.

As in `exists_sentence_weakerThan_of_consistent`, `U`'s presentation is read as `Δ₁` rather than
r.e., and its members are restricted to `StrictHierarchy Γ (n + 1)` rather than
`Hierarchy Γ (n + 1)`.
- [AB05, Theorem 23]
- [Lin97, Corollary 4.2] -/
theorem not_localReflectionOnHierarchy_weakerThan_union
    (hΓ : ∀ σ ∈ U, StrictHierarchy Γ (n + 1) σ) [Consistent (T ∪ U)] :
    ¬𝗥𝗳𝗻[Γ.alt (n + 1)] T ⪯ T ∪ U :=
  fun h ↦ (inconsistent_of_localReflectionOnHierarchy_weakerThan_union hΓ h).not_con
    inferInstance

end LO.FirstOrder.Arithmetic
