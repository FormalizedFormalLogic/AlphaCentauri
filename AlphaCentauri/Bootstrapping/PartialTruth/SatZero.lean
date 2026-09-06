module

public import AlphaCentauri.Bootstrapping.Delta0
public import AlphaCentauri.Bootstrapping.TermVal
public import AlphaCentauri.Bootstrapping.PartialTruth.PSatZero
public import AlphaCentauri.Bootstrapping.PartialTruth.PSatZeroExists

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

@[simp] lemma isRel_two_zero : (ℒₒᵣ).IsRel (2 : V) 0 := by
  simpa using Arithmetic.LOR_rel_eqIndex (V := V)

@[simp] lemma isRel_two_one : (ℒₒᵣ).IsRel (2 : V) 1 := by
  simpa using Arithmetic.LOR_rel_ltIndex (V := V)

/-- A `Δ₀` code beginning with the bounded existential constructor has a `Δ₀` body.
- [HP98, Lemma I.1.68(2)] -/
lemma IsDelta0.of_qqBex {u p : V} (h : IsDelta0 (qqBex u p)) : IsDelta0 p := by
  obtain ⟨u', q', -, hq', heq⟩ :=
    IsDelta0.of_ex (p := (Arithmetic.qqLT (qqBvar 0) u) ^⋏ p) h
  obtain ⟨-, rfl⟩ := (qqAnd_inj _ _ _ _).mp heq
  exact hq'

lemma coe_quote_eq : (⌜(Language.Eq.eq : (ℒₒᵣ).Rel 2)⌝ : V) = 0 := coe_eqIndex_eq

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

/-! ## Substitution and the coded quantifiers -/

lemma isSemiterm_of_termBShift {n t : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t)) : IsSemiterm ℒₒᵣ n t :=
  (IsSemiterm.def (L := ℒₒᵣ)).mpr
    ⟨ht, (termBV_termBShift_le (L := ℒₒᵣ) ht n).mp ((IsSemiterm.def (L := ℒₒᵣ)).mp h).2⟩

lemma isSemiformula_qqBall {n t p : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiformula ℒₒᵣ n (qqBall (termBShift ℒₒᵣ t) p)) :
    IsSemiterm ℒₒᵣ n t ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
  have h' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
    simpa [qqBall, Arithmetic.qqNLT] using h
  exact ⟨isSemiterm_of_termBShift ht h'.1, h'.2⟩

lemma isSemiformula_qqBex {n t p : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiformula ℒₒᵣ n (qqBex (termBShift ℒₒᵣ t) p)) :
    IsSemiterm ℒₒᵣ n t ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
  have h' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
    simpa [qqBex, Arithmetic.qqLT] using h
  exact ⟨isSemiterm_of_termBShift ht h'.1, h'.2⟩

/-- Substitution distributes over the coded equality atom.
- [HP98, 1.64(4)] -/
lemma substs_qqEQ {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^= u)
      = (termSubst ℒₒᵣ w t) ^= (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqEQ, ht, hu]

/-- Substitution distributes over the coded inequality atom.
- [HP98, 1.64(4)] -/
lemma substs_qqNEQ {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^≠ u)
      = (termSubst ℒₒᵣ w t) ^≠ (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqNEQ, ht, hu]

/-- Substitution distributes over the coded less-than atom.
- [HP98, 1.64(4)] -/
lemma substs_qqLT {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^< u)
      = (termSubst ℒₒᵣ w t) ^< (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqLT, ht, hu]

/-- Substitution distributes over the coded not-less-than atom.
- [HP98, 1.64(4)] -/
lemma substs_qqNLT {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^≮ u)
      = (termSubst ℒₒᵣ w t) ^≮ (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqNLT, ht, hu]

/-- Substitution commutes with the bounded universal coding operation.
- [HP98, 1.64(4)] -/
lemma substs_qqBall {n m w t p : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t)
    (hp : IsUFormula ℒₒᵣ p) :
    Bootstrapping.subst ℒₒᵣ w (qqBall (termBShift ℒₒᵣ t) p)
      = qqBall (termBShift ℒₒᵣ (termSubst ℒₒᵣ w t)) (Bootstrapping.subst ℒₒᵣ (qVec ℒₒᵣ w) p) := by
  have hbt : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) := ht.isUTerm.termBShift
  have hlt : IsUFormula ℒₒᵣ ((qqBvar 0 : V) ^≮ termBShift ℒₒᵣ t) := by
    simp [Arithmetic.qqNLT, hbt]
  rw [show qqBall (termBShift ℒₒᵣ t) p = ^∀ (((qqBvar 0 : V) ^≮ termBShift ℒₒᵣ t) ^⋎ p) from rfl,
    substs_all (by simp [hlt, hp]), substs_or hlt hp, substs_qqNLT (by simp) hbt,
    substs_qVec_bShift ht hw]
  simp [qVec, qqBall]

/-- Substitution commutes with the bounded existential coding operation.
- [HP98, 1.64(4)] -/
lemma substs_qqBex {n m w t p : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t)
    (hp : IsUFormula ℒₒᵣ p) :
    Bootstrapping.subst ℒₒᵣ w (qqBex (termBShift ℒₒᵣ t) p)
      = qqBex (termBShift ℒₒᵣ (termSubst ℒₒᵣ w t)) (Bootstrapping.subst ℒₒᵣ (qVec ℒₒᵣ w) p) := by
  have hbt : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) := ht.isUTerm.termBShift
  have hlt : IsUFormula ℒₒᵣ ((qqBvar 0 : V) ^< termBShift ℒₒᵣ t) := by
    simp [Arithmetic.qqLT, hbt]
  rw [show qqBex (termBShift ℒₒᵣ t) p = ^∃ (((qqBvar 0 : V) ^< termBShift ℒₒᵣ t) ^⋏ p) from rfl,
    substs_ex (by simp [hlt, hp]), substs_and hlt hp, substs_qqLT (by simp) hbt,
    substs_qVec_bShift ht hw]
  simp [qVec, qqBex]

/-- Evaluating the vector that enters a quantifier extends the evaluated substitution.
- [HP98, 1.64(5)] -/
lemma termValVec_qVec {n m w e x : V} (hw : IsSemitermVec ℒₒᵣ n m w) :
    termValVec (x ∷ e) (n + 1) (qVec ℒₒᵣ w) = x ∷ termValVec e n w := by
  have hq : IsUTermVec ℒₒᵣ (n + 1) (qVec ℒₒᵣ w) := hw.qVec.isUTerm
  apply nth_ext' (n + 1) (by simp [hq]) (by simp [len_termValVec hw.isUTerm])
  intro i hi
  rw [nth_termValVec hq hi]
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · simp [qVec]
  · have hj : j < n := by simpa using hi
    have hnth : (qVec ℒₒᵣ w).[j + 1] = termBShift ℒₒᵣ w.[j] := by
      rw [qVec, hw.lh]
      simp [nth_termBShiftVec hw.isUTerm hj]
    rw [hnth, termVal_termBShift (hw.isUTerm.nth hj) x e]
    simp [nth_termValVec hw.isUTerm hj]

/-- `Δ₀` shape is preserved by substitution.
- [HP98, Lemma I.1.68(2)] -/
lemma IsDelta0.subst {n m w p : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (h : IsDelta0 p) :
    IsDelta0 (Bootstrapping.subst ℒₒᵣ w p) := by
  have H : ∀ p : V, IsDelta0 p → ∀ n m w, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
      IsDelta0 (Bootstrapping.subst ℒₒᵣ w p) := by
    apply IsDelta0.induction 𝚷
      (P := fun p ↦ ∀ n m w, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
        IsDelta0 (Bootstrapping.subst ℒₒᵣ w p))
    · definability
    · intro n m w _ _; simp
    · intro n m w _ _; simp
    · intro k r v n m w _ hp
      obtain ⟨hr, hv⟩ := IsUFormula.rel.mp hp.isUFormula
      simp [hr, hv]
    · intro k r v n m w _ hp
      obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp hp.isUFormula
      simp [hr, hv]
    · intro p q _ _ ihp ihq n m w hw hpq
      obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq
      rw [substs_and hp.isUFormula hq.isUFormula]
      exact IsDelta0.and_iff.mpr ⟨ihp n m w hw hp, ihq n m w hw hq⟩
    · intro p q _ _ ihp ihq n m w hw hpq
      obtain ⟨hp, hq⟩ := IsSemiformula.or.mp hpq
      rw [substs_or hp.isUFormula hq.isUFormula]
      exact IsDelta0.or_iff.mpr ⟨ihp n m w hw hp, ihq n m w hw hq⟩
    · intro t q ht _ ih n m w hw hpq
      obtain ⟨ht', hq⟩ := isSemiformula_qqBall ht hpq
      rw [substs_qqBall hw ht' hq.isUFormula]
      exact IsDelta0.ball (hw.termSubst ht').isUTerm
        (ih (n + 1) (m + 1) (qVec ℒₒᵣ w) hw.qVec hq)
    · intro t q ht _ ih n m w hw hpq
      obtain ⟨ht', hq⟩ := isSemiformula_qqBex ht hpq
      rw [substs_qqBex hw ht' hq.isUFormula]
      exact IsDelta0.bex (hw.termSubst ht').isUTerm
        (ih (n + 1) (m + 1) (qVec ℒₒᵣ w) hw.qVec hq)
  exact H p h n m w hw hp

/-- `SatZero z e` says that `z` is an internally coded `Δ₀` formula satisfied by `e`.
- [HP98, Definition I.1.71(2)] -/
def SatZero (z e : V) : Prop :=
  (IsDelta0 z ∧ IsUFormula ℒₒᵣ z) ∧ ∃ q, PSatZero q z e ∧ ⟪⟪z, e⟫, 1⟫ ∈ q

namespace SatZero

variable {z e : V}

/-! ## Reading satisfaction off a table -/

/-- Satisfaction at a node of a table is the value the table takes there.
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

/-- Existential and universal table characterizations of `Δ₀` satisfaction agree.
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

section
variable {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u)
include ht hu

/-- Satisfaction of coded equality agrees with equality of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma eq_iff : SatZero (t ^= u) e ↔ termVal e t = termVal e u := by
  have hd : IsDelta0 (t ^= u : V) := by simp [Arithmetic.qqEQ]
  have hf : IsUFormula ℒₒᵣ (t ^= u : V) := by simp [Arithmetic.qqEQ, ht, hu]
  obtain ⟨r, hr⟩ := PSatZero.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_eq hr.mem_dom_root

/-- Satisfaction of coded inequality agrees with inequality of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma neq_iff : SatZero (t ^≠ u) e ↔ termVal e t ≠ termVal e u := by
  have hd : IsDelta0 (t ^≠ u : V) := by simp [Arithmetic.qqNEQ]
  have hf : IsUFormula ℒₒᵣ (t ^≠ u : V) := by simp [Arithmetic.qqNEQ, ht, hu]
  obtain ⟨r, hr⟩ := PSatZero.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_neq hr.mem_dom_root

/-- Satisfaction of coded less-than agrees with comparison of term values.
- [HP98, Theorem I.1.70(ii)] -/
lemma lt_iff : SatZero (t ^< u) e ↔ termVal e t < termVal e u := by
  have hd : IsDelta0 (t ^< u : V) := by simp [Arithmetic.qqLT]
  have hf : IsUFormula ℒₒᵣ (t ^< u : V) := by simp [Arithmetic.qqLT, ht, hu]
  obtain ⟨r, hr⟩ := PSatZero.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_lt hr.mem_dom_root

/-- Satisfaction of coded negated less-than agrees with failure of comparison.
- [HP98, Theorem I.1.70(ii)] -/
lemma nlt_iff : SatZero (t ^≮ u) e ↔ ¬(termVal e t < termVal e u) := by
  have hd : IsDelta0 (t ^≮ u : V) := by simp [Arithmetic.qqNLT]
  have hf : IsUFormula ℒₒᵣ (t ^≮ u : V) := by simp [Arithmetic.qqNLT, ht, hu]
  obtain ⟨r, hr⟩ := PSatZero.exists hd hf
  rw [iff_val hd hf hr]
  exact hr.val_nlt hr.mem_dom_root

end

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

/-- Satisfaction commutes with coded disjunction of well-formed formulas.
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

section
variable {t q e : V} (ht : IsUTerm ℒₒᵣ t)
include ht

/-- Satisfaction of a bounded universal is bounded universal satisfaction of its body.
- [HP98, Theorem I.1.70(iv)] -/
lemma ball_iff (hq : IsDelta0 q) (hq' : IsUFormula ℒₒᵣ q) :
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
lemma bex_iff : SatZero (qqBex (termBShift ℒₒᵣ t) q) e ↔ ∃ x < termVal e t, SatZero q (x ∷ e) := by
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

end

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

/-- Satisfaction commutes with substitution of a coded vector of terms.
- [HP98, 1.64(4)]
- [HP98, Theorem I.1.70] -/
lemma subst {n m w p e : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (hp' : IsDelta0 p) :
    SatZero (Bootstrapping.subst ℒₒᵣ w p) e ↔ SatZero p (termValVec e n w) := by
  have H : ∀ p : V, IsDelta0 p → ∀ n m w e, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
      (SatZero (Bootstrapping.subst ℒₒᵣ w p) e ↔ SatZero p (termValVec e n w)) := by
    apply IsDelta0.induction 𝚷
      (P := fun p ↦ ∀ n m w e, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
        (SatZero (Bootstrapping.subst ℒₒᵣ w p) e ↔ SatZero p (termValVec e n w)))
    · definability
    · intro n m w e _ _; simp
    · intro n m w e _ _; simp
    · intro k r v n m w e hw hp
      rcases rel_cases hp.isUFormula with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩
      · rw [heq] at hp ⊢
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqEQ] using hp
        rw [substs_qqEQ ht hu,
          eq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm, eq_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus]
      · rw [heq] at hp ⊢
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqLT] using hp
        rw [substs_qqLT ht hu,
          lt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm, lt_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus]
    · intro k r v n m w e hw hp
      rcases nrel_cases hp.isUFormula with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩
      · rw [heq] at hp ⊢
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqNEQ] using hp
        rw [substs_qqNEQ ht hu,
          neq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm, neq_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus]
      · rw [heq] at hp ⊢
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqNLT] using hp
        rw [substs_qqNLT ht hu,
          nlt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm, nlt_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus]
    · intro p q _ _ ihp ihq n m w e hw hpq
      obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq
      rw [substs_and hp.isUFormula hq.isUFormula, and_iff, and_iff,
        ihp n m w e hw hp, ihq n m w e hw hq]
    · intro p q hdp hdq ihp ihq n m w e hw hpq
      obtain ⟨hp, hq⟩ := IsSemiformula.or.mp hpq
      rw [substs_or hp.isUFormula hq.isUFormula,
        or_iff (IsDelta0.subst hw hp hdp) (hp.subst hw).isUFormula
          (IsDelta0.subst hw hq hdq) (hq.subst hw).isUFormula,
        or_iff hdp hp.isUFormula hdq hq.isUFormula,
        ihp n m w e hw hp, ihq n m w e hw hq]
    · intro t q ht hdq ih n m w e hw hpq
      obtain ⟨hts, hq⟩ := isSemiformula_qqBall ht hpq
      rw [substs_qqBall hw hts hq.isUFormula,
        ball_iff (hw.termSubst hts).isUTerm (IsDelta0.subst hw.qVec hq hdq)
          (hq.subst hw.qVec).isUFormula,
        ball_iff ht hdq hq.isUFormula, termVal_termSubst hw hts]
      refine forall_congr' fun x ↦ imp_congr_right fun _ ↦ ?_
      rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw]
    · intro t q ht hdq ih n m w e hw hpq
      obtain ⟨hts, hq⟩ := isSemiformula_qqBex ht hpq
      rw [substs_qqBex hw hts hq.isUFormula, bex_iff (hw.termSubst hts).isUTerm,
        bex_iff ht, termVal_termSubst hw hts]
      refine exists_congr fun x ↦ and_congr_right fun _ ↦ ?_
      rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw]
  exact H p hp' n m w e hw hp

end SatZero

end LO.FirstOrder.Arithmetic.Bootstrapping
