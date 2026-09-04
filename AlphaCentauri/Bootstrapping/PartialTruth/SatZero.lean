module

public import AlphaCentauri.Bootstrapping.Delta0
public import AlphaCentauri.Bootstrapping.TermVal
public import AlphaCentauri.Bootstrapping.PartialTruth.PSatZero

/-!
# Satisfaction for `Δ₀` formulas

This module defines the satisfaction predicate for internally coded `Δ₀` formulas from the
partial satisfaction tables of `PSatZero`, proves it is `𝚫₁`, and proves Tarski's satisfaction
conditions for it.

- [HP98, Theorem I.1.70]
- [HP98, Definition I.1.71(2)]
- [HP98, Lemma I.1.73]
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every well-formed internally `Δ₀` formula has a partial satisfaction table.
- [HP98, Lemma I.1.72(3)] -/
axiom PSatZero.exists {z e : V} (hz : IsDelta0 z) (hz' : IsUFormula ℒₒᵣ z) :
    ∃ q, PSatZero q z e

/-- Equality is the binary relation of `ℒₒᵣ` with index `0`, in plain numerals.
- No source; a numeral restatement of `Arithmetic.LOR_rel_eqIndex`. -/
@[simp] lemma isRel_two_zero : (ℒₒᵣ).IsRel (2 : V) 0 := by
  simpa using Arithmetic.LOR_rel_eqIndex (V := V)

/-- Less-than is the binary relation of `ℒₒᵣ` with index `1`, in plain numerals.
- No source; a numeral restatement of `Arithmetic.LOR_rel_ltIndex`. -/
@[simp] lemma isRel_two_one : (ℒₒᵣ).IsRel (2 : V) 1 := by
  simpa using Arithmetic.LOR_rel_ltIndex (V := V)

/-- A `Δ₀` code beginning with the bounded existential constructor has a `Δ₀` body.
- [HP98, Lemma I.1.68(2)] -/
lemma IsDelta0.of_qqBex {u p : V} (h : IsDelta0 (qqBex u p)) : IsDelta0 p := by
  obtain ⟨u', q', -, hq', heq⟩ :=
    IsDelta0.of_ex (p := (Arithmetic.qqLT (qqBvar 0) u) ^⋏ p) h
  obtain ⟨-, rfl⟩ := (qqAnd_inj _ _ _ _).mp heq
  exact hq'

/-- A `Δ₀` code beginning with the bounded universal constructor has a `Δ₀` body.
- [HP98, Lemma I.1.68(2)] -/
lemma IsDelta0.of_qqBall {u p : V} (h : IsDelta0 (qqBall u p)) : IsDelta0 p := by
  obtain ⟨u', q', -, hq', heq⟩ :=
    IsDelta0.of_all (p := (Arithmetic.qqNLT (qqBvar 0) u) ^⋎ p) h
  obtain ⟨-, rfl⟩ := (qqOr_inj _ _ _ _).mp heq
  exact hq'

/-- The code of `ℒₒᵣ`'s equality symbol is the numeral `0`.
- No source; a quoted restatement of `coe_eqIndex_eq`. -/
lemma coe_quote_eq : (⌜(Language.Eq.eq : (ℒₒᵣ).Rel 2)⌝ : V) = 0 := coe_eqIndex_eq

/-- The code of `ℒₒᵣ`'s less-than symbol is the numeral `1`.
- No source; a quoted restatement of `coe_ltIndex_eq`. -/
lemma coe_quote_lt : (⌜(Language.LT.lt : (ℒₒᵣ).Rel 2)⌝ : V) = 1 := coe_ltIndex_eq

/-- A well-formed positive atom of `ℒₒᵣ` is a coded equality or a coded less-than.
- [HP98, 1.64] -/
lemma rel_cases {k r v : V} (h : IsUFormula ℒₒᵣ (^rel k r v)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r v = t ^= u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r v = t ^< u) := by
  obtain ⟨hr, hv⟩ := IsUFormula.rel.mp h
  rcases Arithmetic.isRel_iff_LOR.mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv
  · exact Or.inl ⟨a, b, ha, hb, by rw [Arithmetic.qqEQ, coe_quote_eq, coe_eqIndex_eq]⟩
  · exact Or.inr ⟨a, b, ha, hb, by rw [Arithmetic.qqLT, coe_quote_lt, coe_ltIndex_eq]⟩

/-- A well-formed negative atom of `ℒₒᵣ` is a coded inequality or a coded not-less-than.
- [HP98, 1.64] -/
lemma nrel_cases {k r v : V} (h : IsUFormula ℒₒᵣ (^nrel k r v)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r v = t ^≠ u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r v = t ^≮ u) := by
  obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp h
  rcases Arithmetic.isRel_iff_LOR.mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv
  · exact Or.inl ⟨a, b, ha, hb, by rw [Arithmetic.qqNEQ, coe_quote_eq, coe_eqIndex_eq]⟩
  · exact Or.inr ⟨a, b, ha, hb, by rw [Arithmetic.qqNLT, coe_quote_lt, coe_ltIndex_eq]⟩

/-- `SatZero z e` says that the internally coded `Δ₀` formula `z` is satisfied by `e`. The
well-formedness of `z` is part of the definition, as in the source, where satisfaction is
introduced only for `Δ₀` formulas* and their evaluations*: a table alone does not witness it,
since a code whose bounded quantifier has an empty range carries a table no matter what its
body is.
- [HP98, Definition I.1.71(2)] -/
def SatZero (z e : V) : Prop :=
  (IsDelta0 z ∧ IsUFormula ℒₒᵣ z) ∧ ∃ q, PSatZero q z e ∧ ⟪⟪z, e⟫, 1⟫ ∈ q

namespace SatZero

variable {z e p q t u : V}

/-! ## Reading satisfaction off a table -/

/-- Satisfaction at a node of a table is the value the table takes there: the two tables agree
at the node, since it belongs to both domains.
- [HP98, Lemma I.1.72(2)] -/
lemma iff_mem {r z e p e' : V} (hr : PSatZero r z e) (hn : ⟪p, e'⟫ ∈ domain r)
    (hp : IsDelta0 p) (hp' : IsUFormula ℒₒᵣ p) :
    SatZero p e' ↔ ⟪⟪p, e'⟫, 1⟫ ∈ r := by
  constructor
  · rintro ⟨-, s, hs, h1⟩
    exact (hs.agree hr p e' hs.mem_dom_root hn).1.mp h1
  · intro h1
    obtain ⟨s, hs⟩ := PSatZero.exists hp hp'
    exact ⟨⟨hp, hp'⟩, s, hs, (hr.agree hs p e' hn hs.mem_dom_root).1.mp h1⟩

/-- Satisfaction of the root of a table is the value the table takes at the root.
- [HP98, Lemma I.1.72(2)] -/
lemma iff_val {r : V} (hz : IsDelta0 z) (hz' : IsUFormula ℒₒᵣ z) (hr : PSatZero r z e) :
    SatZero z e ↔ ⟪⟪z, e⟫, 1⟫ ∈ r := iff_mem hr hr.mem_dom_root hz hz'

/-- On the `Δ₀` domain, the `𝚺₁` and the `𝚷₁` readings of satisfaction agree: a table exists,
and all tables give the root the same value.
- [HP98, Lemma I.1.73(1)] -/
lemma exists_iff_forall (hz : IsDelta0 z) (hz' : IsUFormula ℒₒᵣ z) :
    (∃ r, PSatZero r z e ∧ ⟪⟪z, e⟫, 1⟫ ∈ r) ↔ ∀ r, PSatZero r z e → ⟪⟪z, e⟫, 1⟫ ∈ r := by
  constructor
  · rintro ⟨s, hs, h1⟩ r hr
    exact (hs.agree hr z e hs.mem_dom_root hr.mem_dom_root).1.mp h1
  · intro h
    obtain ⟨r, hr⟩ := PSatZero.exists hz hz'
    exact ⟨r, hr, h r hr⟩

/-- The `𝚷₁` form of satisfaction.
- [HP98, Lemma I.1.73(1)] -/
lemma iff_forall {z e : V} :
    SatZero z e ↔
      (IsDelta0 z ∧ IsUFormula ℒₒᵣ z) ∧ ∀ r, PSatZero r z e → ⟪⟪z, e⟫, 1⟫ ∈ r :=
  and_congr_right fun ⟨hz, hz'⟩ ↦ exists_iff_forall hz hz'

end SatZero

/-- The `𝚫₁` formula defining satisfaction for internally coded `Δ₀` formulas.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
noncomputable def satZero : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “z e. (!isDelta0.sigma z ∧ !(isUFormula ℒₒᵣ).sigma z) ∧
    ∃ q, !pSatZero.sigma q z e ∧ !PSatZeroF.nodeValDef q z e 1”)
  (.mkPi “z e. (!isDelta0.pi z ∧ !(isUFormula ℒₒᵣ).pi z) ∧
    ∀ q, !pSatZero.sigma q z e → !PSatZeroF.nodeValDef q z e 1”)

/-- The formula `satZero` defines `SatZero`.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
instance SatZero.defined : 𝚫₁-Relation (SatZero : V → V → Prop) via satZero := .mk <| by
  constructor
  · intro v
    suffices IsDelta0 (v 0) → IsUFormula ℒₒᵣ (v 0) →
        ((∃ r, PSatZero r (v 0) (v 1) ∧ ⟪⟪v 0, v 1⟫, 1⟫ ∈ r) ↔
          ∀ r, PSatZero r (v 0) (v 1) → ⟪⟪v 0, v 1⟫, 1⟫ ∈ r) by
      simpa [satZero, HierarchySymbol.Semiformula.val_sigma,
        (IsDelta0.defined (V := V)).df, (IsUFormula.defined (V := V) (L := ℒₒᵣ)).df,
        (PSatZero.defined (V := V)).df, PSatZeroF.nodeVal_defined.df] using this
    exact fun hz hz' ↦ SatZero.exists_iff_forall hz hz'
  · intro v
    simp [satZero, HierarchySymbol.Semiformula.val_sigma, SatZero,
      (IsDelta0.defined (V := V)).df, (IsUFormula.defined (V := V) (L := ℒₒᵣ)).df,
      (PSatZero.defined (V := V)).df, PSatZeroF.nodeVal_defined.df]

/-- Satisfaction for internally coded `Δ₀` formulas is `𝚫₁`-definable.
- [HP98, Theorem I.1.70]
- [HP98, Lemma I.1.73(1)] -/
instance SatZero.definable : 𝚫₁-Relation (SatZero : V → V → Prop) :=
  SatZero.defined.to_definable


/-! ## Tarski conditions -/

namespace SatZero

variable {z e p q t u : V}

/-- Satisfaction implies that its formula code belongs to the `Δ₀` domain.
- [HP98, Theorem I.1.70(i)] -/
lemma dom {z e : V} : SatZero z e → IsDelta0 z ∧ IsUFormula ℒₒᵣ z := And.left

/-- The coded truth constant is satisfied.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma verum (e : V) : SatZero (^⊤ : V) e := by
  obtain ⟨r, hr⟩ := PSatZero.exists (z := (^⊤ : V)) (e := e) (by simp) (by simp)
  exact ⟨⟨by simp, by simp⟩, r, hr, hr.val_verum hr.mem_dom_root⟩

/-- The coded falsehood constant is not satisfied.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma falsum (e : V) : ¬SatZero (^⊥ : V) e := by
  rintro ⟨-, r, hr, h1⟩
  exact hr.val_one_ne_zero h1 (hr.val_falsum hr.mem_dom_root)

/-- Satisfaction of coded equality agrees with equality of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma eq_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^= u) e ↔ termVal e t = termVal e u := by
  have hd : IsDelta0 (t ^= u : V) := by simp [Arithmetic.qqEQ]
  have hf : IsUFormula ℒₒᵣ (t ^= u : V) := by simp [Arithmetic.qqEQ, ht, hu]
  obtain ⟨r, hr⟩ := PSatZero.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_eq hr.mem_dom_root

/-- Satisfaction of coded inequality agrees with inequality of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma neq_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^≠ u) e ↔ termVal e t ≠ termVal e u := by
  have hd : IsDelta0 (t ^≠ u : V) := by simp [Arithmetic.qqNEQ]
  have hf : IsUFormula ℒₒᵣ (t ^≠ u : V) := by simp [Arithmetic.qqNEQ, ht, hu]
  obtain ⟨r, hr⟩ := PSatZero.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_neq hr.mem_dom_root

/-- Satisfaction of coded less-than agrees with comparison of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma lt_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^< u) e ↔ termVal e t < termVal e u := by
  have hd : IsDelta0 (t ^< u : V) := by simp [Arithmetic.qqLT]
  have hf : IsUFormula ℒₒᵣ (t ^< u : V) := by simp [Arithmetic.qqLT, ht, hu]
  obtain ⟨r, hr⟩ := PSatZero.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_lt hr.mem_dom_root

/-- Satisfaction of coded negated less-than agrees with failure of comparison.
- [HP98, Theorem I.1.70(ii)] -/
lemma nlt_iff {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    SatZero (t ^≮ u) e ↔ ¬(termVal e t < termVal e u) := by
  have hd : IsDelta0 (t ^≮ u : V) := by simp [Arithmetic.qqNLT]
  have hf : IsUFormula ℒₒᵣ (t ^≮ u : V) := by simp [Arithmetic.qqNLT, ht, hu]
  obtain ⟨r, hr⟩ := PSatZero.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_nlt hr.mem_dom_root

/-- Satisfaction commutes with coded conjunction.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma and_iff {p q e : V} :
    SatZero (p ^⋏ q) e ↔ SatZero p e ∧ SatZero q e := by
  constructor
  · rintro ⟨⟨hd, hf⟩, r, hr, h1⟩
    obtain ⟨hdp, hdq⟩ := IsDelta0.and_iff.mp hd
    obtain ⟨hfp, hfq⟩ := IsUFormula.and.mp hf
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_and hr.mem_dom_root
    obtain ⟨v₁, v₂⟩ := (hr.val_and hr.mem_dom_root).mp h1
    exact ⟨(iff_mem hr hn₁ hdp hfp).mpr v₁, (iff_mem hr hn₂ hdq hfq).mpr v₂⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨hdp, hfp⟩ := h₁.dom
    obtain ⟨hdq, hfq⟩ := h₂.dom
    have hd : IsDelta0 (p ^⋏ q) := IsDelta0.and_iff.mpr ⟨hdp, hdq⟩
    have hf : IsUFormula ℒₒᵣ (p ^⋏ q) := by simp [hfp, hfq]
    obtain ⟨r, hr⟩ := PSatZero.exists hd hf
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_and hr.mem_dom_root
    exact (iff_val hd hf hr).mpr ((hr.val_and hr.mem_dom_root).mpr
      ⟨(iff_mem hr hn₁ hdp hfp).mp h₁, (iff_mem hr hn₂ hdq hfq).mp h₂⟩)

/-- Satisfaction commutes with coded disjunction.
- [HP98, Theorem I.1.70(ii)] -/
@[simp] lemma or_iff {p q e : V} (hdp : IsDelta0 p) (hfp : IsUFormula ℒₒᵣ p)
    (hdq : IsDelta0 q) (hfq : IsUFormula ℒₒᵣ q) :
    SatZero (p ^⋎ q) e ↔ SatZero p e ∨ SatZero q e := by
  constructor
  · rintro ⟨-, r, hr, h1⟩
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_or hr.mem_dom_root
    rcases (hr.val_or hr.mem_dom_root).mp h1 with v | v
    · exact Or.inl ((iff_mem hr hn₁ hdp hfp).mpr v)
    · exact Or.inr ((iff_mem hr hn₂ hdq hfq).mpr v)
  · intro h
    have hd : IsDelta0 (p ^⋎ q) := IsDelta0.or_iff.mpr ⟨hdp, hdq⟩
    have hf : IsUFormula ℒₒᵣ (p ^⋎ q) := by simp [hfp, hfq]
    obtain ⟨r, hr⟩ := PSatZero.exists hd hf
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_or hr.mem_dom_root
    refine (iff_val hd hf hr).mpr ((hr.val_or hr.mem_dom_root).mpr ?_)
    rcases h with h | h
    · exact Or.inl ((iff_mem hr hn₁ hdp hfp).mp h)
    · exact Or.inr ((iff_mem hr hn₂ hdq hfq).mp h)

/-- Satisfaction of a bounded universal is bounded universal satisfaction of its body.
- [HP98, Theorem I.1.70(iv)] -/
lemma ball_iff {t q e : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsDelta0 q)
    (hq' : IsUFormula ℒₒᵣ q) :
    SatZero (qqBall (termBShift ℒₒᵣ t) q) e ↔ ∀ x < termVal e t, SatZero q (x ∷ e) := by
  have hd : IsDelta0 (qqBall (termBShift ℒₒᵣ t) q) := IsDelta0.ball ht hq
  have hf : IsUFormula ℒₒᵣ (qqBall (termBShift ℒₒᵣ t) q) := by
    simp [qqBall, Arithmetic.qqNLT, ht.termBShift, hq']
  obtain ⟨r, hr⟩ := PSatZero.exists hd hf
  rw [iff_val hd hf hr, hr.val_ball ht hr.mem_dom_root]
  exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
    (iff_mem hr (hr.mem_dom_ball ht hr.mem_dom_root hx) hq hq').symm

/-- Satisfaction of a bounded existential is bounded existential satisfaction of its body.
- [HP98, Theorem I.1.70(iv)] -/
lemma bex_iff {t q e : V} (ht : IsUTerm ℒₒᵣ t) :
    SatZero (qqBex (termBShift ℒₒᵣ t) q) e ↔ ∃ x < termVal e t, SatZero q (x ∷ e) := by
  constructor
  · rintro ⟨⟨hd, hf⟩, r, hr, h1⟩
    have hq : IsDelta0 q := hd.of_qqBex
    have hq' : IsUFormula ℒₒᵣ q := by
      simpa [qqBex, Arithmetic.qqLT, ht.termBShift] using hf
    obtain ⟨x, hx, v⟩ := (hr.val_bex ht hr.mem_dom_root).mp h1
    exact ⟨x, hx, (iff_mem hr (hr.mem_dom_bex ht hr.mem_dom_root hx) hq hq').mpr v⟩
  · rintro ⟨x, hx, hsat⟩
    obtain ⟨hq, hq'⟩ := hsat.dom
    have hd : IsDelta0 (qqBex (termBShift ℒₒᵣ t) q) := IsDelta0.bex ht hq
    have hf : IsUFormula ℒₒᵣ (qqBex (termBShift ℒₒᵣ t) q) := by
      simp [qqBex, Arithmetic.qqLT, ht.termBShift, hq']
    obtain ⟨r, hr⟩ := PSatZero.exists hd hf
    refine (iff_val hd hf hr).mpr ((hr.val_bex ht hr.mem_dom_root).mpr ⟨x, hx, ?_⟩)
    exact (iff_mem hr (hr.mem_dom_bex ht hr.mem_dom_root hx) hq hq').mp hsat

/-- Satisfaction commutes with coded negation on `Δ₀` formulas.
- [HP98, Theorem I.1.70(iii)] -/
lemma neg_iff {p e : V} (hp : IsDelta0 p) (hp' : IsUFormula ℒₒᵣ p) :
    SatZero (neg ℒₒᵣ p) e ↔ ¬SatZero p e := by
  have H : ∀ p : V, IsDelta0 p → IsUFormula ℒₒᵣ p →
      ∀ e, (SatZero (neg ℒₒᵣ p) e ↔ ¬SatZero p e) := by
    apply IsDelta0.induction 𝚷
      (P := fun p ↦ IsUFormula ℒₒᵣ p → ∀ e, (SatZero (neg ℒₒᵣ p) e ↔ ¬SatZero p e))
    · definability
    · intro _ e; simp
    · intro _ e; simp
    · intro k r v h e
      rcases rel_cases h with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩
      · rw [heq, Arithmetic.neg_eq ht hu, neq_iff ht hu, eq_iff ht hu]
      · rw [heq, Arithmetic.neg_lt ht hu, nlt_iff ht hu, lt_iff ht hu]
    · intro k r v h e
      rcases nrel_cases h with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩
      · rw [heq, Arithmetic.neg_neq ht hu, eq_iff ht hu, neq_iff ht hu]; simp
      · rw [heq, Arithmetic.neg_nlt ht hu, lt_iff ht hu, nlt_iff ht hu]; simp
    · intro p q hdp hdq ihp ihq h e
      obtain ⟨hfp, hfq⟩ := IsUFormula.and.mp h
      rw [neg_and hfp hfq,
        or_iff (IsDelta0.neg hfp hdp) hfp.neg (IsDelta0.neg hfq hdq) hfq.neg,
        ihp hfp e, ihq hfq e, and_iff]
      tauto
    · intro p q hdp hdq ihp ihq h e
      obtain ⟨hfp, hfq⟩ := IsUFormula.or.mp h
      rw [neg_or hfp hfq, and_iff, ihp hfp e, ihq hfq e, or_iff hdp hfp hdq hfq]
      tauto
    · intro t q ht hdq ih h e
      obtain ⟨-, hfq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBall, Arithmetic.qqNLT] using h
      rw [neg_qqBall ht.termBShift hfq, bex_iff ht, ball_iff ht hdq hfq]
      constructor
      · rintro ⟨x, hx, hnx⟩ hall
        exact (ih hfq (x ∷ e)).mp hnx (hall x hx)
      · intro hn
        by_contra hc
        exact hn fun x hx ↦ by
          by_contra hnx
          exact hc ⟨x, hx, (ih hfq (x ∷ e)).mpr hnx⟩
    · intro t q ht hdq ih h e
      obtain ⟨-, hfq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBex, Arithmetic.qqLT] using h
      rw [neg_qqBex ht.termBShift hfq,
        ball_iff ht (IsDelta0.neg hfq hdq) hfq.neg, bex_iff ht]
      constructor
      · rintro hall ⟨x, hx, hx'⟩
        exact (ih hfq (x ∷ e)).mp (hall x hx) hx'
      · intro hn x hx
        exact (ih hfq (x ∷ e)).mpr fun hc ↦ hn ⟨x, hx, hc⟩
  exact H p hp hp' e

end SatZero

end LO.FirstOrder.Arithmetic.Bootstrapping
