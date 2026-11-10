module

public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Equality
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.ProvableIff
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.QuantifierBlock
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Iteration
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions

/-!
# The deduction theorem for finite sets of axioms

The internal deduction theorem for finite sets of axioms, and the equivalence of provability from
`T` with an added sentence `σ` and provability of `σ → p` from `T`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

section DeductionTheorem

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

namespace Derivation

/-- A formula code belongs to the $\Delta_1$-class of a finite list of sentences, presented as a
theory, iff it is the quote of one of the listed sentences. -/
lemma mem_deltaClass_ofList_iff (l : List (Sentence L)) (p : V) :
    p ∈ @Theory.Δ₁Class V _ L _ _ {p | p ∈ l} (Theory.Δ₁.ofList l) ↔
      ∃ σ ∈ l, p = (⌜σ⌝ : V) := by
  induction l with
  | nil =>
    change False ↔ ∃ σ ∈ ([] : List (Sentence L)), p = (⌜σ⌝ : V)
    simp
  | cons σ l ih =>
    change V ⊧/![p] (((Theory.Δ₁.singleton σ).add
      (Theory.Δ₁.ofList l)).ch).val ↔
      ∃ τ ∈ σ :: l, p = (⌜τ⌝ : V)
    change V ⊧/![p] (((Theory.Δ₁.singleton σ).ch ⋎
      (Theory.Δ₁.ofList l).ch).val) ↔
      ∃ τ ∈ σ :: l, p = (⌜τ⌝ : V)
    simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or,
      LogicalConnective.Prop.or_eq]
    rw [Theory.Δ₁.singleton_toTDef_ch_val]
    have ih' : V ⊧/![p] (Theory.Δ₁.ofList l).ch.val ↔
        ∃ τ ∈ l, p = (⌜τ⌝ : V) := ih
    rw [ih']
    simp [Sentence.quote_eq_encode, numeral_eq_natCast]

variable {U : Theory L} [U.Δ₁]

/-- Given a coded formula set `a` closed under the external-variable shift such that every axiom
of `T` is an axiom of `U` or has its negation in `a`, every derivation from `T` yields a derivation
from `U` of the same end-sequent with `a` adjoined. -/
theorem deductionAux {a d : V} (ha : IsFormulaSet L a) (hsa : setShift L a = a)
    (hax : ∀ p, p ∈ T.Δ₁Class → p ∈ U.Δ₁Class ∨ neg L p ∈ a) (hd : Derivation T d) :
    ∃ d', Derivation U d' ∧ fstIdx d' = fstIdx d ∪ a := by
  have insert_union (x s : V) : insert x s ∪ a = insert x (s ∪ a) := by
    apply mem_ext
    intro z
    simp only [mem_cup_iff, mem_bitInsert_iff]
    tauto
  apply Derivation.induction1 𝚺 (P := fun d ↦
      ∃ d', Derivation U d' ∧ fstIdx d' = fstIdx d ∪ a) (by definability) hd
  · intro s hs p hp hnp
    exact ⟨Bootstrapping.axL (s ∪ a) p,
      Derivation.axL (by simp [hs, ha]) (by simp [hp]) (by simp [hnp]), by simp⟩
  · intro s hs hv
    exact ⟨Bootstrapping.verumIntro (s ∪ a),
      Derivation.verumIntro (by simp [hs, ha]) (by simp [hv]), by simp⟩
  · intro s _ p q dp dq hpq hdp hdq ihp ihq
    obtain ⟨dp', hdp', edp⟩ := ihp
    obtain ⟨dq', hdq', edq⟩ := ihq
    refine ⟨Bootstrapping.andIntro (s ∪ a) p q dp' dq',
      Derivation.andIntro (by simp [hpq]) ?_ ?_, by simp⟩
    · exact ⟨by rw [edp, hdp.1, insert_union], hdp'⟩
    · exact ⟨by rw [edq, hdq.1, insert_union], hdq'⟩
  · intro s _ p q dp hpq hdp ih
    obtain ⟨dp', hdp', edp⟩ := ih
    refine ⟨Bootstrapping.orIntro (s ∪ a) p q dp',
      Derivation.orIntro (by simp [hpq]) ?_, by simp⟩
    exact ⟨by rw [edp, hdp.1, insert_union, insert_union], hdp'⟩
  · intro s _ p dp hp hdp ih
    obtain ⟨dp', hdp', edp⟩ := ih
    refine ⟨Bootstrapping.allIntro (s ∪ a) p dp',
      Derivation.allIntro (by simp [hp]) ?_, by simp⟩
    exact ⟨by rw [edp, hdp.1, insert_union, mem_setShift_union, hsa], hdp'⟩
  · intro s _ p t dp hp ht hdp ih
    obtain ⟨dp', hdp', edp⟩ := ih
    refine ⟨Bootstrapping.exsIntro (s ∪ a) p t dp',
      Derivation.exsIntro (by simp [hp]) ht ?_, by simp⟩
    exact ⟨by rw [edp, hdp.1, insert_union], hdp'⟩
  · intro s hs d hsd _ ih
    obtain ⟨d', hd', ed⟩ := ih
    have hsub : fstIdx d' ⊆ s ∪ a := by
      rw [ed]
      intro p hp
      rcases mem_cup_iff.mp hp with hp | hp
      · exact mem_cup_iff.mpr (Or.inl (hsd hp))
      · exact mem_cup_iff.mpr (Or.inr hp)
    exact ⟨Bootstrapping.wkRule (s ∪ a) d',
      Derivation.wkRule (by simp [hs, ha]) hsub ⟨rfl, hd'⟩,
      by simp⟩
  · rintro _ _ d rfl _ ih
    obtain ⟨d', hd', ed⟩ := ih
    exact ⟨Bootstrapping.shiftRule (setShift L (fstIdx d ∪ a)) d', Derivation.shiftRule ⟨ed, hd'⟩,
      by simp [mem_setShift_union, hsa]⟩
  · intro s _ p d₁ d₂ hd₁ hd₂ ih₁ ih₂
    obtain ⟨d₁', hd₁', ed₁⟩ := ih₁
    obtain ⟨d₂', hd₂', ed₂⟩ := ih₂
    exact ⟨Bootstrapping.cutRule (s ∪ a) p d₁' d₂',
      Derivation.cutRule ⟨by rw [ed₁, hd₁.1, insert_union], hd₁'⟩
        ⟨by rw [ed₂, hd₂.1, insert_union], hd₂'⟩, by simp⟩
  · intro s hs p hp hT
    rcases hax p hT with hU | hn
    · exact ⟨Bootstrapping.axm (s ∪ a) p,
        Derivation.axm (by simp [hs, ha]) (by simp [hp]) hU, by simp⟩
    · exact ⟨Bootstrapping.axL (s ∪ a) p,
        Derivation.axL (by simp [hs, ha]) (by simp [hp]) (by simp [hn]), by simp⟩

/-- Given a coded formula set `a` closed under the external-variable shift such that every axiom
`p ≤ d` of `T` follows in pure logic from the negation of some member of `a`, a derivation `d`
from `T` yields a pure derivation of its end-sequent with `a` adjoined.
- [HP98, Section I.4(a)] -/
theorem derivable_union_of_replacement {a d : V} (ha : IsFormulaSet L a)
    (hsa : setShift L a = a)
    (hax : ∀ p ≤ d, p ∈ T.Δ₁Class →
      ∃ q, neg L q ∈ a ∧ Derivable (∅ : Theory L) (insert (neg L q) ({p} : V)))
    (hd : Derivation T d) : Derivable (∅ : Theory L) (fstIdx d ∪ a) := by
  have insert_union (x s : V) : insert x s ∪ a = insert x (s ∪ a) :=
    mem_ext fun z ↦ by simp only [mem_cup_iff, mem_bitInsert_iff]; tauto
  suffices d ≤ d → Derivable (∅ : Theory L) (fstIdx d ∪ a) from this le_rfl
  apply Derivation.induction1 𝚺 (P := fun e ↦ e ≤ d → Derivable (∅ : Theory L) (fstIdx e ∪ a))
    (by definability) hd
  · intro s hs p hp hnp _
    rw [fstIdx_axL]
    exact Derivable.em (by simp [hs, ha]) p (by simp [hp]) (by simp [hnp])
  · intro s hs hv _
    rw [fstIdx_verumIntro]
    exact Derivable.verum (by simp [hs, ha]) (by simp [hv])
  · intro s _ p q dp dq hpq hdp hdq ihp ihq hle
    have h₁ := ihp ((dp_lt_andIntro _ _ _ _ _).le.trans hle)
    have h₂ := ihq ((dq_lt_andIntro _ _ _ _ _).le.trans hle)
    rw [hdp.1, insert_union] at h₁
    rw [hdq.1, insert_union] at h₂
    rw [fstIdx_andIntro]
    exact Derivable.and_m (mem_cup_iff.mpr <| Or.inl hpq) h₁ h₂
  · intro s _ p q dp hpq hdp ih hle
    have h := ih ((d_lt_orIntro _ _ _ _).le.trans hle)
    rw [hdp.1, insert_union, insert_union] at h
    rw [fstIdx_orIntro]
    exact Derivable.or_m (mem_cup_iff.mpr <| Or.inl hpq) h
  · intro s _ p dp hp hdp ih hle
    have h := ih ((s_lt_allIntro _ _ _).le.trans hle)
    rw [hdp.1, insert_union, ← hsa, ← mem_setShift_union] at h
    rw [fstIdx_allIntro]
    exact Derivable.all_m (mem_cup_iff.mpr <| Or.inl hp) h
  · intro s _ p t dp hp ht hdp ih hle
    have h := ih ((d_lt_exsIntro _ _ _ _).le.trans hle)
    rw [hdp.1, insert_union] at h
    rw [fstIdx_exsIntro]
    exact Derivable.ex_m (mem_cup_iff.mpr <| Or.inl hp) ht h
  · intro s hs e hse _ ih hle
    rw [fstIdx_wkRule]
    refine Derivable.wk (by simp [hs, ha]) ?_ (ih ((d_lt_wkRule _ _).le.trans hle))
    intro x hx
    rcases mem_cup_iff.mp hx with hx | hx
    · exact mem_cup_iff.mpr <| Or.inl <| hse hx
    · exact mem_cup_iff.mpr <| Or.inr hx
  · rintro _ _ e rfl _ ih hle
    have h := (ih ((d_lt_shiftRule _ _).le.trans hle)).shift
    rwa [mem_setShift_union, hsa, ← fstIdx_shiftRule (setShift L (fstIdx e)) e] at h
  · intro s _ p d₁ d₂ hd₁ hd₂ ih₁ ih₂ hle
    have h₁ := ih₁ ((d₁_lt_cutRule _ _ _ _).le.trans hle)
    have h₂ := ih₂ ((d₂_lt_cutRule _ _ _ _).le.trans hle)
    rw [hd₁.1, insert_union] at h₁
    rw [hd₂.1, insert_union] at h₂
    rw [fstIdx_cutRule]
    exact Derivable.cut p h₁ h₂
  · intro s hs p hp hT hle
    obtain ⟨q, hq, hqp⟩ := hax p ((p_lt_axm _ _).le.trans hle) hT
    rw [fstIdx_axm]
    refine Derivable.wk (by simp [hs, ha]) ?_ hqp
    intro x hx
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · exact mem_cup_iff.mpr <| Or.inr hq
    · exact mem_cup_iff.mpr <| Or.inl <| (mem_singleton_iff.mp hx) ▸ hp

section InsertAxiom

/-- The $\Delta_1$-class of the singleton theory `{σ}` consists of the code of `σ` alone. -/
lemma mem_deltaClass_singleton_iff (σ : Sentence L) (p : V) :
    p ∈ ({σ} : Theory L).Δ₁Class ↔ p = ⌜σ⌝ := by
  change V ⊧/![p] ({σ} : Theory L).Δ₁ch.val ↔ p = ⌜σ⌝
  rw [Theory.Δ₁.singleton_toTDef_ch_val]
  simp [Sentence.quote_eq_encode, numeral_eq_natCast]

/-- If every axiom of `U` is an axiom of `T` or the sentence `σ`, every derivation from `U` yields
a derivation from `T` of the same end-sequent with `¬σ` adjoined.
- [HP98, Section I.4(a)] -/
theorem deduction_insert {σ : Sentence L} {d : V}
    (hU : ∀ p : V, p ∈ U.Δ₁Class → p ∈ T.Δ₁Class ∨ p = ⌜σ⌝) (hd : Derivation U d) :
    ∃ d', Derivation T d' ∧ fstIdx d' = insert (neg L ⌜σ⌝) (fstIdx d) := by
  have hax (p : V) (hp : p ∈ U.Δ₁Class) : p ∈ T.Δ₁Class ∨ neg L p ∈ insert (neg L ⌜σ⌝) (∅ : V) := by
    rcases hU p hp with hp | rfl
    · exact Or.inl hp
    · exact Or.inr <| by simp
  have hs : shift L (neg L (⌜σ⌝ : V)) = neg L ⌜σ⌝ := by
    rw [shift_neg (n := 0) (by simp), Semisentence.shift_quote]
  obtain ⟨d', hd', e⟩ :=
    deductionAux (by simp) (by rw [mem_setShift_insert, setShift_empty, hs]) hax hd
  refine ⟨d', hd', ?_⟩
  rw [e]
  apply mem_ext
  intro x
  simp [or_comm]

/-- If `U` contains the axioms of `T` and the sentence `σ`, a sequent derivable from `T` with
`¬σ` adjoined is derivable from `U`. -/
theorem derivable_of_derivable_insert_neg {σ : Sentence L} {s : V}
    (hU : T.Δ₁Class (V := V) ⊆ U.Δ₁Class) (hσ : (⌜σ⌝ : V) ∈ U.Δ₁Class)
    (hd : Derivable T (insert (neg L ⌜σ⌝) s)) : Derivable U s := by
  have hs : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp hd.isFormulaSet).2
  have h : Derivable U (insert (⌜σ⌝ : V) s) := Derivable.by_axm (by simp [hs]) _ (by simp) hσ
  exact Derivable.cut _ h <| Derivable.of_ss hU hd

/-- A formula is provable from a theory whose axioms are those of `T` together with `σ` iff the
sequent consisting of it and `¬σ` is derivable from `T`.
- [HP98, Section I.4(a)] -/
theorem provable_iff_derivable_insert_neg {σ : Sentence L} {p : V}
    (hU : ∀ p : V, p ∈ U.Δ₁Class → p ∈ T.Δ₁Class ∨ p = ⌜σ⌝)
    (hU' : T.Δ₁Class (V := V) ⊆ U.Δ₁Class) (hσ : (⌜σ⌝ : V) ∈ U.Δ₁Class) :
    Provable U p ↔ Derivable T (insert (neg L ⌜σ⌝) ({p} : V)) := by
  constructor
  · rintro ⟨d, e, hd⟩
    obtain ⟨d', hd', e'⟩ := deduction_insert hU hd
    exact ⟨d', by rw [e', e], hd'⟩
  · exact derivable_of_derivable_insert_neg hU' hσ

/-- A formula is provable from a theory whose axioms are those of `T` together with `σ` iff
`σ → p` is provable from `T`.
- [HP98, Section I.4(a)] -/
theorem provable_iff_provable_imp {σ : Sentence L} {p : V}
    (hU : ∀ p : V, p ∈ U.Δ₁Class → p ∈ T.Δ₁Class ∨ p = ⌜σ⌝)
    (hU' : T.Δ₁Class (V := V) ⊆ U.Δ₁Class) (hσ : (⌜σ⌝ : V) ∈ U.Δ₁Class) :
    Provable U p ↔ Provable T (imp L ⌜σ⌝ p) := by
  rw [provable_iff_derivable_insert_neg hU hU' hσ]
  constructor
  · intro h
    exact Derivable.toProvable <| Derivable.or <| h.ofSetEq <| by intro x; simp
  · intro h
    have hd := h.toDerivable
    have hp : IsFormula L p := by simpa [Bootstrapping.imp] using hd.isFormulaSet
    have h₁ : Derivable T (insert (imp L ⌜σ⌝ p) (insert (neg L ⌜σ⌝) ({p} : V))) :=
      hd.wk (by simp [hp]) (by intro x; simp +contextual)
    have h₂ : Derivable T (insert (⌜σ⌝ ^⋏ neg L p) (insert (neg L ⌜σ⌝) ({p} : V))) :=
      Derivable.and (Derivable.em (by simp [hp]) ⌜σ⌝ (by simp) (by simp))
        (Derivable.em (by simp [hp]) p (by simp) (by simp))
    apply Derivable.cut _ h₁
    simpa [Bootstrapping.imp, hp.isUFormula] using h₂

/-- The internal deduction theorem: `p` is provable from `T ∪ {σ}` iff `σ → p` is provable
from `T`.
- [HP98, Section I.4(a)] -/
theorem provable_union_singleton_iff (σ : Sentence L) {p : V} :
    Provable (T ∪ {σ}) p ↔ Provable T (imp L ⌜σ⌝ p) := by
  apply provable_iff_provable_imp
  · intro q hq
    simpa [mem_deltaClass_singleton_iff] using hq
  · intro q hq
    simp [hq]
  · simp

end InsertAxiom

section Deduction

variable [L.DecidableEq]

/-- The finite sequent consisting of the negations of the listed axioms.
- [HP98, Section I.4(a)] -/
noncomputable def negatedAxioms (l : List (Sentence L)) : Finset (Proposition L) :=
  l.toFinset.image fun σ : Sentence L ↦ ∼(↑σ : Proposition L)

/-- The internal deduction transform replaces every axiom leaf by an excluded-middle leaf and
adjoins the negations of the finite list of axioms to every sequent.
- [HP98, Section I.4(a)] -/
theorem deduction (l : List (Sentence L)) {d : V} :
    let _ : Theory.Δ₁ {p | p ∈ l} := Theory.Δ₁.ofList l
    Derivation {p | p ∈ l} d →
      ∃ d', Derivation (∅ : Theory L) d' ∧
        fstIdx d' = fstIdx d ∪ (⌜negatedAxioms l⌝ : V) := by
  let _ : Theory.Δ₁ {p | p ∈ l} := Theory.Δ₁.ofList l
  dsimp only
  intro hd
  apply deductionAux (T := {p | p ∈ l}) (a := (⌜negatedAxioms l⌝ : V))
  · exact LK2.Derivation.formulaSet_quote_finset _
  · rw [LK2.Derivation.setShift_quote]
    congr 1
    ext p
    have hshift (σ : Sentence L) :
        Rewriting.shift (↑σ : Proposition L) = (↑σ : Proposition L) := by simp
    simp [negatedAxioms, hshift]
  · intro p hp
    right
    rw [mem_deltaClass_ofList_iff l p] at hp
    obtain ⟨σ, hσ, rfl⟩ := hp
    have hneg : neg L (⌜σ⌝ : V) = (⌜∼(↑σ : Proposition L)⌝ : V) := by
      exact congrArg (fun q : Bootstrapping.Formula V L ↦ q.val)
        (Semiformula.typedQuote_neg (V := V) (↑σ : Proposition L)).symm
    rw [hneg]
    exact (LK2.Derivation.Sequent.mem_quote_iff (V := V)).mpr
      (show ∼(↑σ : Proposition L) ∈ negatedAxioms l by simp [negatedAxioms, hσ])
  · exact hd

/-- Provability from a finite list of axioms yields a pure derivation after adjoining their
negations to the end sequent.
- [HP98, Section I.4(a)] -/
theorem provable_deduction (l : List (Sentence L)) {p : V} :
    let _ : Theory.Δ₁ {q | q ∈ l} := Theory.Δ₁.ofList l
    Provable {q | q ∈ l} p →
      Derivable (∅ : Theory L) (insert p (⌜negatedAxioms l⌝ : V)) := by
  let _ : Theory.Δ₁ {q | q ∈ l} := Theory.Δ₁.ofList l
  dsimp only
  rintro ⟨d, hd⟩
  obtain ⟨d', hd', heq⟩ := deduction l hd.2
  have heq' : fstIdx d' = insert p (⌜negatedAxioms l⌝ : V) := by
    rw [heq, hd.1]
    apply mem_ext
    intro x
    simp only [mem_cup_iff, mem_singleton_iff, mem_bitInsert_iff]
  exact ⟨d', heq', hd'⟩

end Deduction

end Derivation

end DeductionTheorem

end FFL.FirstOrder.Arithmetic.Bootstrapping
