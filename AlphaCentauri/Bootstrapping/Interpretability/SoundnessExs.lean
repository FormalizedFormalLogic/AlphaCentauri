module

public import AlphaCentauri.Bootstrapping.Interpretability.FormSubst
public import AlphaCentauri.Bootstrapping.Interpretability.PiFacts
public import AlphaCentauri.Bootstrapping.Interpretability.SoundnessRules
public import AlphaCentauri.Bootstrapping.Interpretability.TermSubst
public import AlphaCentauri.Bootstrapping.Interpretability.TypedShapes
public import AlphaCentauri.Bootstrapping.Interpretability.ValueLemma
public import AlphaCentauri.ToFoundation.DefinesElement
public import AlphaCentauri.ToFoundation.TypedBridge

/-!
# Translated derivability is closed under the existential rule

For `^∃ p ∈ Γ` and a closed term `t`, the translated derivability of `Γ` follows from that of
`insert (substs1 t p) Γ`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

section generic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

lemma derivable_of_iff_mp {s : V} (X Y : Formula V L)
    (hI : Derivable T (insert (X 🡘 Y).val s)) (hX : Derivable T (insert X.val s)) :
    Derivable T (insert Y.val s) := by
  have h : T.internalize V ⊢ (X 🡘 Y) 🡒 X 🡒 Y := by cl_prover
  exact Derivable.of_tprovable_imp₂ h hI hX

end generic

section rules

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
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

end FFL.FirstOrder.Arithmetic.Bootstrapping
