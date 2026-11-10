module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping.Syntax.Formula.Quantifier
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Hierarchy

/-!
# Internal arithmetical hierarchy in models of $\mathsf{EA}$

The part of `Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Formula/Hierarchy.lean` in the
namespace `Bootstrapping`, ported to models of $\mathsf{EA}$: the unbounded quantifier `qqQuant` of
a given polarity, the iterated quantifier prefix `qqToPrenex`, and the predicates `IsHierarchy Γ n`
and `IsPrenexHierarchy Γ n` on codes of formulas, closed under negation. The formulas are
Foundation's `qqQuantDef`, `qqToPrenexDef`, `IsHierarchyF.blueprint`, `isHierarchy` and
`isPrenexHierarchy`.

## References

- [HP98, Lemma I.1.69]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (isHierarchy isPrenexHierarchy)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

/-! ## Unbounded quantifier of a given polarity -/

section qqQuant

/-- The code of the unbounded quantifier of polarity `Γ`. -/
noncomputable def qqQuant : Polarity → V → V
  | 𝚺, p => ^∃ p
  | 𝚷, p => ^∀ p

@[simp] lemma qqQuant_sigma (p : V) : qqQuant 𝚺 p = ^∃ p := rfl

@[simp] lemma qqQuant_pi (p : V) : qqQuant 𝚷 p = ^∀ p := rfl

instance qqQuant_defined (Γ : Polarity) :
    𝚺ᴬ₀-Function₁ (qqQuant Γ : V → V) via qqQuantDef Γ := by
  cases Γ
  · exact qqExsists_defined
  · exact qqForall_defined

lemma qqQuant_locallyDelta0 (Γ : Polarity) : LocallyDelta0Function₁ (qqQuant Γ : V → V) := by
  cases Γ
  · exact qqExs_locallyDelta0
  · exact qqAll_locallyDelta0

@[simp] lemma lt_qqQuant (Γ : Polarity) (p : V) : p < qqQuant Γ p := by
  cases Γ <;> simp [lt_exists, lt_forall]

variable {Γ Γ' : Polarity} {p q : V}

@[simp] lemma qqQuant_inj : qqQuant Γ p = qqQuant Γ' q ↔ Γ = Γ' ∧ p = q := by
  cases Γ <;> cases Γ' <;> simp [qqExs, qqAll]

@[simp] lemma isUFormula_qqQuant {L : Language} [L.Encodable] [L.LORDefinable] :
    IsUFormula L (qqQuant Γ p) ↔ IsUFormula L p := by
  cases Γ <;> simp

lemma neg_qqQuant (hp : IsUFormula ℒₒᵣ p) :
    neg ℒₒᵣ (qqQuant Γ p) = qqQuant Γ.alt (neg ℒₒᵣ p) := by
  cases Γ <;> simp [hp]

end qqQuant

section qqToPrenex

/-- The code of the quantifier prefix of `s` alternating blocks of unbounded quantifiers starting
with polarity `Γ`, followed by `θ`. -/
noncomputable def qqToPrenex : Polarity → ℕ → V → V
  | _, 0, θ => θ
  | Γ, s + 1, θ => qqQuant Γ (qqToPrenex Γ.alt s θ)

variable {Γ : Polarity} {s : ℕ} {θ θ' : V}

@[simp] lemma qqToPrenex_zero : qqToPrenex Γ 0 θ = θ := rfl

@[simp] lemma qqToPrenex_succ : qqToPrenex Γ (s + 1) θ = qqQuant Γ (qqToPrenex Γ.alt s θ) := rfl

@[simp] lemma qqToPrenex_inj : qqToPrenex Γ s θ = qqToPrenex Γ s θ' ↔ θ = θ' := by
  induction s generalizing Γ <;> simp [*]

@[simp] lemma le_qqToPrenex : θ ≤ qqToPrenex Γ s θ := by
  induction s generalizing Γ with
  | zero => simp
  | succ s ih => exact ih.trans (lt_qqQuant _ _).le

instance qqToPrenex_defined : (Γ : Polarity) → (s : ℕ) →
    𝚺ᴬ₀-Function₁ (qqToPrenex Γ s : V → V) via qqToPrenexDef Γ s
  | _, 0 => .mk fun v ↦ by simp [qqToPrenexDef]
  | Γ, s + 1 => .mk fun v ↦ by
    simp +contextual [qqToPrenexDef, (qqToPrenex_defined Γ.alt s).df, (qqQuant_defined Γ).df]

end qqToPrenex

/-! ## Internal hierarchy predicate `IsHierarchy` -/

section isHierarchy

namespace IsHierarchyF

open IsBoundedF (locallyDelta0_binary locallyDelta0_bounded)

/-- The operator generating the codes of formulas of a level of the hierarchy from the formulas
of the lower level `P`. -/
def Phi (Γ : Polarity) (P : V → Prop) (C : Set V) (p : V) : Prop :=
  P p ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
  (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C ∧ p = qqBall u q) ∨
  (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C ∧ p = qqBex u q) ∨
  (∃ q, q ∈ C ∧ p = qqQuant Γ q)

private lemma phi_iff (Γ : Polarity) (P : V → Prop) (C p : V) :
    Phi Γ P {x | x ∈ C} p ↔
    P p ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqBall u q) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqBex u q) ∨
    (∃ q < p, q ∈ C ∧ p = qqQuant Γ q) := by
  constructor
  · rintro (hp | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩
      | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · disj 1; exact hp
    · disj 2; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩
    · disj 3; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩
    · disj 4
      exact ⟨termBShift ℒₒᵣ t, by simp, q, by simp,
        ⟨t, lt_of_le_of_lt (le_termBShift ht) (by simp), ht, rfl⟩, hq, rfl⟩
    · disj 5
      exact ⟨termBShift ℒₒᵣ t, by simp, q, by simp,
        ⟨t, lt_of_le_of_lt (le_termBShift ht) (by simp), ht, rfl⟩, hq, rfl⟩
    · disj 6; exact ⟨q, by simp, hq, rfl⟩
  · unfold Phi
    rintro (hp | ⟨p₁, _, p₂, _, hp, hq, rfl⟩ | ⟨p₁, _, p₂, _, hp, hq, rfl⟩
      | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩ | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩
      | ⟨q, _, hq, rfl⟩) <;> grind

lemma phi_locallyDelta0 (Γ : Polarity) {P : V → Prop} (hP : LocallyDelta0Pred P) :
    LocallyDelta0 fun w : Fin 2 → V ↦ Phi Γ P {x | x ∈ w 1} (w 0) := by
  have hquant : LocallyDelta0 fun y : Fin 3 → V ↦ y 0 ∈ y 2 ∧ y 1 = qqQuant Γ (y 0) :=
    (LocallyDelta0.mem (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 2)).and <|
      LocallyDelta0.eq (LocallyDelta0Function.var 1)
        ((qqQuant_locallyDelta0 Γ).comp₁ (LocallyDelta0Function.var 0))
  have hex := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) hquant
  exact ((hP.pred_comp (LocallyDelta0Function.var (0 : Fin 2))).or <|
    (locallyDelta0_binary qqAnd_locallyDelta0).or <|
    (locallyDelta0_binary qqOr_locallyDelta0).or <|
    (locallyDelta0_bounded qqBall_locallyDelta0).or <|
    (locallyDelta0_bounded qqBex_locallyDelta0).or hex).of_iff
    fun w ↦ by simpa using phi_iff Γ P (w 1) (w 0)

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.IsHierarchyF (blueprint) in
/-- The construction of the codes of formulas of a level of the hierarchy from the formulas of
the lower level `P`. -/
def construction (Γ : Polarity) {P : V → Prop} {θ : 𝚫ᴬ₁.Semisentence 1}
    (hP : 𝚫ᴬ₁-Predicate P via θ) (hP' : LocallyDelta0Pred P) :
    Fixpoint.Construction V (blueprint Γ θ) where
  Φ := fun _ ↦ Phi Γ P
  defined := .mk <| by
    have := hP
    constructor
    · intro v
      simp [blueprint, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ)).df, qqBall_defined.df, qqBex_defined.df,
        (qqQuant_defined Γ).df]
    · intro v
      simpa [blueprint, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ)).df, qqBall_defined.df, qqBex_defined.df,
        (qqQuant_defined Γ).df] using (phi_iff Γ P _ _).symm
  monotone := by
    unfold Phi
    intro C C' hC _ x
    grind
  Φ_locallyDelta0 := phi_locallyDelta0 Γ hP'

instance (Γ : Polarity) {P : V → Prop} {θ : 𝚫ᴬ₁.Semisentence 1}
    (hP : 𝚫ᴬ₁-Predicate P via θ) (hP' : LocallyDelta0Pred P) :
    (construction Γ hP hP').StrongFinite V where
  strong_finite := by
    unfold construction Phi
    rintro C _ x (h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨u, q, ht, hq, rfl⟩
      | ⟨u, q, ht, hq, rfl⟩ | ⟨q, hq, rfl⟩) <;>
      grind [lt_K!_left, lt_K!_right, lt_or_left, lt_or_right, lt_q_qqBall, lt_q_qqBex, lt_qqQuant]

end IsHierarchyF

namespace IsHierarchyF

-- The predicate of each level is bundled with its definability and local $\Delta_0$-ness, which
-- the construction of the next level depends on.
/-- The predicate of the level `n` of the hierarchy of polarity `Γ`. -/
noncomputable def pred :
    (Γ : Polarity) → (n : ℕ) →
      {P : V → Prop // (𝚫ᴬ₁-Predicate P via isHierarchy Γ n) ∧ LocallyDelta0Pred P}
  | _, 0 => ⟨IsBounded, IsBounded.defined, isBounded_locallyDelta0⟩
  | Γ, n + 1 =>
    ⟨(construction Γ (pred Γ.alt n).2.1 (pred Γ.alt n).2.2).Fixpoint ![],
      (construction Γ (pred Γ.alt n).2.1 (pred Γ.alt n).2.2).fixpoint_definedΔ₁,
      (construction Γ (pred Γ.alt n).2.1 (pred Γ.alt n).2.2).fixpoint_locallyDelta0.of_iff
        fun w ↦ iff_of_eq <| congrArg
          (fun u ↦ (construction Γ (pred Γ.alt n).2.1 (pred Γ.alt n).2.2).Fixpoint u (w 0))
          (Subsingleton.elim _ _)⟩

end IsHierarchyF

/-- The predicate that `p` is the code of a formula of the level `n` of the hierarchy of
polarity `Γ`. -/
def IsHierarchy (Γ : Polarity) (n : ℕ) (p : V) : Prop := (IsHierarchyF.pred Γ n).1 p

abbrev IsSigma (n : ℕ) (p : V) : Prop := IsHierarchy 𝚺 n p

abbrev IsPi (n : ℕ) (p : V) : Prop := IsHierarchy 𝚷 n p

instance IsHierarchy.defined (Γ : Polarity) (n : ℕ) :
    𝚫ᴬ₁-Predicate (IsHierarchy (V := V) Γ n) via isHierarchy Γ n :=
  (IsHierarchyF.pred Γ n).2.1

instance IsHierarchy.definable (Γ : Polarity) (n : ℕ) :
    𝚫ᴬ₁-Predicate (IsHierarchy (V := V) Γ n) :=
  (IsHierarchy.defined Γ n).to_definable

lemma isHierarchy_locallyDelta0 (Γ : Polarity) (n : ℕ) :
    LocallyDelta0Pred (IsHierarchy (V := V) Γ n) :=
  (IsHierarchyF.pred Γ n).2.2

variable {Γ : Polarity} {n : ℕ} {p q : V}

lemma IsHierarchy.zero_iff : IsHierarchy Γ 0 p ↔ IsBounded p := by rfl

lemma IsHierarchy.succ_iff :
    IsHierarchy Γ (n + 1) p ↔
    IsHierarchy Γ.alt n p ∨
    (∃ p₁ p₂, IsHierarchy Γ (n + 1) p₁ ∧ IsHierarchy Γ (n + 1) p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsHierarchy Γ (n + 1) p₁ ∧ IsHierarchy Γ (n + 1) p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsHierarchy Γ (n + 1) q
      ∧ p = qqBall u q) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsHierarchy Γ (n + 1) q
      ∧ p = qqBex u q) ∨
    (∃ q, IsHierarchy Γ (n + 1) q ∧ p = qqQuant Γ q) :=
  (IsHierarchyF.construction Γ (IsHierarchyF.pred Γ.alt n).2.1
    (IsHierarchyF.pred Γ.alt n).2.2).case

alias ⟨IsHierarchy.succ_case, IsHierarchy.succ_mk⟩ := IsHierarchy.succ_iff

lemma IsHierarchy.succ_induction {P : V → Prop} (hP : LocallyDelta0Pred P)
    (hbase : ∀ p, IsHierarchy Γ.alt n p → P p)
    (hand : ∀ p q, IsHierarchy Γ (n + 1) p → IsHierarchy Γ (n + 1) q → P p → P q →
      P (p ^⋏ q))
    (hor : ∀ p q, IsHierarchy Γ (n + 1) p → IsHierarchy Γ (n + 1) q → P p → P q →
      P (p ^⋎ q))
    (hball : ∀ t q, IsUTerm ℒₒᵣ t → IsHierarchy Γ (n + 1) q → P q →
      P (qqBall (termBShift ℒₒᵣ t) q))
    (hbex : ∀ t q, IsUTerm ℒₒᵣ t → IsHierarchy Γ (n + 1) q → P q →
      P (qqBex (termBShift ℒₒᵣ t) q))
    (hquant : ∀ q, IsHierarchy Γ (n + 1) q → P q → P (qqQuant Γ q)) :
    ∀ p, IsHierarchy Γ (n + 1) p → P p :=
  (IsHierarchyF.construction Γ (IsHierarchyF.pred Γ.alt n).2.1
    (IsHierarchyF.pred Γ.alt n).2.2).induction (v := ![]) hP (by
    rintro C hC x (hx | ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩
      | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact hbase x hx
    · exact hand p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2
    · exact hor p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2
    · exact hball t q ht (hC q hq).1 (hC q hq).2
    · exact hbex t q ht (hC q hq).1 (hC q hq).2
    · exact hquant q (hC q hq).1 (hC q hq).2)

/-! ### Closure properties -/

lemma IsHierarchy.of_alt (h : IsHierarchy Γ.alt n p) : IsHierarchy Γ (n + 1) p :=
  IsHierarchy.succ_mk <| by left; exact h

lemma IsHierarchy.of_bounded (h : IsBounded p) : IsHierarchy Γ n p := by
  induction n generalizing Γ with
  | zero => exact IsHierarchy.zero_iff.mpr h
  | succ n ih => exact IsHierarchy.of_alt ih

@[simp] lemma IsHierarchy.verum : IsHierarchy Γ n (^⊤ : V) :=
  IsHierarchy.of_bounded (by simp)

@[simp] lemma IsHierarchy.falsum : IsHierarchy Γ n (^⊥ : V) :=
  IsHierarchy.of_bounded (by simp)

@[simp] lemma IsHierarchy.rel {k r v : V} : IsHierarchy Γ n (^rel k r v) :=
  IsHierarchy.of_bounded (by simp)

@[simp] lemma IsHierarchy.nrel {k r v : V} : IsHierarchy Γ n (^nrel k r v) :=
  IsHierarchy.of_bounded (by simp)

@[simp] lemma IsHierarchy.and_iff :
    IsHierarchy Γ n (p ^⋏ q) ↔ IsHierarchy Γ n p ∧ IsHierarchy Γ n q := by
  induction n generalizing Γ with
  | zero => exact IsBounded.and_iff
  | succ n ih =>
    constructor
    · intro h
      rcases h.succ_case with (h | h | h | h | h | h)
      · exact ⟨(ih.mp h).1.of_alt, (ih.mp h).2.of_alt⟩
      all_goals cases Γ <;> simp_all [qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex]
    · rintro ⟨hp, hq⟩
      exact IsHierarchy.succ_mk <| by disj 2; exact ⟨p, q, hp, hq, rfl⟩

@[simp] lemma IsHierarchy.or_iff :
    IsHierarchy Γ n (p ^⋎ q) ↔ IsHierarchy Γ n p ∧ IsHierarchy Γ n q := by
  induction n generalizing Γ with
  | zero => exact IsBounded.or_iff
  | succ n ih =>
    constructor
    · intro h
      rcases h.succ_case with (h | h | h | h | h | h)
      · exact ⟨(ih.mp h).1.of_alt, (ih.mp h).2.of_alt⟩
      all_goals cases Γ <;> simp_all [qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex]
    · rintro ⟨hp, hq⟩
      exact IsHierarchy.succ_mk <| by disj 3; exact ⟨p, q, hp, hq, rfl⟩

lemma IsHierarchy.ball {t : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsHierarchy Γ n q) :
    IsHierarchy Γ n (qqBall (termBShift ℒₒᵣ t) q) := by
  cases n with
  | zero => exact IsBounded.ball ht hq
  | succ n => exact IsHierarchy.succ_mk <| by disj 4; exact ⟨_, q, ⟨t, ht, rfl⟩, hq, rfl⟩

lemma IsHierarchy.bex {t : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsHierarchy Γ n q) :
    IsHierarchy Γ n (qqBex (termBShift ℒₒᵣ t) q) := by
  cases n with
  | zero => exact IsBounded.bex ht hq
  | succ n => exact IsHierarchy.succ_mk <| by disj 5; exact ⟨_, q, ⟨t, ht, rfl⟩, hq, rfl⟩

lemma IsHierarchy.quant (h : IsHierarchy Γ (n + 1) p) : IsHierarchy Γ (n + 1) (qqQuant Γ p) :=
  IsHierarchy.succ_mk <| by disj 6; exact ⟨p, h, rfl⟩

lemma IsSigma.ex (h : IsSigma (n + 1) p) : IsSigma (n + 1) (^∃ p) := IsHierarchy.quant h

lemma IsPi.all (h : IsPi (n + 1) p) : IsPi (n + 1) (^∀ p) := IsHierarchy.quant h

lemma IsSigma.sigma (h : IsPi n p) : IsSigma (n + 1) (^∃ p) :=
  IsSigma.ex (IsHierarchy.of_alt (Γ := 𝚺) h)

lemma IsPi.pi (h : IsSigma n p) : IsPi (n + 1) (^∀ p) :=
  IsPi.all (IsHierarchy.of_alt (Γ := 𝚷) h)

lemma IsHierarchy.succ (h : IsHierarchy Γ n p) : IsHierarchy Γ (n + 1) p := by
  induction n generalizing Γ p with
  | zero => exact IsHierarchy.of_bounded h
  | succ n ih =>
    apply IsHierarchy.succ_induction (P := IsHierarchy Γ (n + 1 + 1))
      (isHierarchy_locallyDelta0 Γ (n + 1 + 1))
      (fun p hp ↦ (ih hp).of_alt) (fun p q _ _ hp hq ↦ IsHierarchy.and_iff.mpr ⟨hp, hq⟩)
      (fun p q _ _ hp hq ↦ IsHierarchy.or_iff.mpr ⟨hp, hq⟩)
      (fun t q ht _ hq ↦ IsHierarchy.ball ht hq) (fun t q ht _ hq ↦ IsHierarchy.bex ht hq)
      (fun q _ hq ↦ IsHierarchy.quant hq) p h

lemma IsHierarchy.accum (Γ' : Polarity) (h : IsHierarchy Γ n p) : IsHierarchy Γ' (n + 1) p := by
  cases Γ <;> cases Γ'
  · exact h.succ
  · exact IsHierarchy.of_alt (Γ := 𝚷) h
  · exact IsHierarchy.of_alt (Γ := 𝚺) h
  · exact h.succ

lemma IsHierarchy.mono {m : ℕ} (hmn : m ≤ n) (h : IsHierarchy Γ m p) : IsHierarchy Γ n p := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih.succ

/-! ### Inversion of unbounded quantifiers -/

lemma IsHierarchy.of_all (h : IsHierarchy Γ (n + 1) (^∀ p)) :
    IsHierarchy Γ.alt n (^∀ p) ∨
    IsHierarchy Γ (n + 1) p ∧
      (Γ = 𝚷 ∨ ∃ t q, IsUTerm ℒₒᵣ t ∧ p = (^#0 ^≮ termBShift ℒₒᵣ t) ^⋎ q) := by
  rcases h.succ_case with (h | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, q, ⟨t, ht, rfl⟩, hq, h⟩
    | ⟨_, _, _, _, h⟩ | ⟨q, hq, h⟩)
  · left; exact h
  · simp [qqAll, qqAnd] at h
  · simp [qqAll, qqOr] at h
  · obtain rfl := (qqAll_inj _ _).mp h
    right
    exact ⟨IsHierarchy.or_iff.mpr ⟨by simp [Arithmetic.qqNLT], hq⟩,
      by right; exact ⟨t, q, ht, rfl⟩⟩
  · simp [qqAll, qqBex, qqExs] at h
  · cases Γ
    · simp [qqAll, qqExs] at h
    · right
      obtain rfl : p = q := (qqAll_inj _ _).mp h
      exact ⟨hq, by left; rfl⟩

lemma IsHierarchy.of_ex (h : IsHierarchy Γ (n + 1) (^∃ p)) :
    IsHierarchy Γ.alt n (^∃ p) ∨
    IsHierarchy Γ (n + 1) p ∧
      (Γ = 𝚺 ∨ ∃ t q, IsUTerm ℒₒᵣ t ∧ p = (^#0 ^< termBShift ℒₒᵣ t : V) ^⋏ q) := by
  rcases h.succ_case with (h | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
    | ⟨_, q, ⟨t, ht, rfl⟩, hq, h⟩ | ⟨q, hq, h⟩)
  · left; exact h
  · simp [qqExs, qqAnd] at h
  · simp [qqExs, qqOr] at h
  · simp [qqExs, qqBall, qqAll] at h
  · obtain rfl := (qqExs_inj _ _).mp h
    right
    exact ⟨IsHierarchy.and_iff.mpr ⟨by simp [Arithmetic.qqLT], hq⟩,
      by right; exact ⟨t, q, ht, rfl⟩⟩
  · cases Γ
    · right
      obtain rfl : p = q := (qqExs_inj _ _).mp h
      exact ⟨hq, by left; rfl⟩
    · simp [qqAll, qqExs] at h

/-! ### Negation -/

lemma IsHierarchy.neg (hp : IsUFormula ℒₒᵣ p) (h : IsHierarchy Γ n p) :
    IsHierarchy Γ.alt n (Bootstrapping.neg ℒₒᵣ p) := by
  induction n generalizing Γ p with
  | zero => exact IsBounded.neg hp h
  | succ n ih =>
    suffices ∀ p : V, IsHierarchy Γ (n + 1) p →
        IsUFormula ℒₒᵣ p → IsHierarchy Γ.alt (n + 1) (Bootstrapping.neg ℒₒᵣ p) from this p h hp
    apply IsHierarchy.succ_induction
      (P := fun p ↦ IsUFormula ℒₒᵣ p → IsHierarchy Γ.alt (n + 1) (Bootstrapping.neg ℒₒᵣ p))
      ((isUFormula_locallyDelta0 (L := ℒₒᵣ)).imp <|
        (isHierarchy_locallyDelta0 Γ.alt (n + 1)).pred_comp <|
          neg_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
    · intro p h hp
      exact IsHierarchy.of_alt (Γ := Γ.alt) (by simpa using ih hp h)
    · simp +contextual
    · simp +contextual
    · intro t q ht _ ih h
      have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBall]
      simpa [neg_qqBall ht.termBShift hq] using IsHierarchy.bex ht (ih hq)
    · intro t q ht _ ih h
      have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBex]
      simpa [neg_qqBex ht.termBShift hq] using IsHierarchy.ball ht (ih hq)
    · intro q _ ih h
      have hq : IsUFormula ℒₒᵣ q := isUFormula_qqQuant.mp h
      simpa [neg_qqQuant hq] using IsHierarchy.quant (ih hq)

end isHierarchy

/-! ## Internal prenex classes -/

section isPrenexHierarchy

/-- The predicate that `p` is the code of a formula consisting of `n` alternating blocks of
unbounded quantifiers of polarity `Γ` first, followed by a bounded formula. -/
def IsPrenexHierarchy : Polarity → ℕ → V → Prop
  | _, 0 => IsBounded
  | Γ, n + 1 => fun p ↦ ∃ q, p = qqQuant Γ q ∧ IsPrenexHierarchy Γ.alt n q

instance IsPrenexHierarchy.defined : (Γ : Polarity) → (n : ℕ) →
    𝚫ᴬ₁-Predicate (IsPrenexHierarchy (V := V) Γ n) via isPrenexHierarchy Γ n
  | _, 0 => IsBounded.defined
  | Γ, n + 1 =>
    have : 𝚫ᴬ₁-Predicate (IsPrenexHierarchy (V := V) Γ.alt n) via isPrenexHierarchy Γ.alt n :=
      IsPrenexHierarchy.defined Γ.alt n
    .mk ⟨fun v ↦ by
        simp [isPrenexHierarchy, Bounding.HierarchySymbol.Semiformula.val_sigma],
      fun v ↦ by
        simp [isPrenexHierarchy, IsPrenexHierarchy, (qqQuant_defined Γ).df]
        grind [lt_qqQuant]⟩

instance IsPrenexHierarchy.definable (Γ : Polarity) (n : ℕ) :
    𝚫ᴬ₁-Predicate (IsPrenexHierarchy (V := V) Γ n) :=
  (IsPrenexHierarchy.defined Γ n).to_definable

lemma isPrenexHierarchy_locallyDelta0 (Γ : Polarity) (n : ℕ) :
    LocallyDelta0Pred (IsPrenexHierarchy (V := V) Γ n) := by
  induction n generalizing Γ with
  | zero => exact isBounded_locallyDelta0
  | succ n ih =>
    have := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 1)) <|
      (LocallyDelta0.eq (LocallyDelta0Function.var 1)
        ((qqQuant_locallyDelta0 Γ).comp₁ (LocallyDelta0Function.var 0))).and
        ((ih Γ.alt).pred_comp (LocallyDelta0Function.var (0 : Fin 2)))
    refine this.of_iff fun w ↦ ?_
    constructor
    · rintro ⟨q, hp, h⟩
      exact ⟨q, hp ▸ lt_qqQuant Γ q, hp, h⟩
    · rintro ⟨q, -, hp, h⟩
      exact ⟨q, hp, h⟩

variable {Γ : Polarity} {n : ℕ} {p : V}

@[simp] lemma IsPrenexHierarchy.quant_iff :
    IsPrenexHierarchy Γ (n + 1) (qqQuant Γ p) ↔ IsPrenexHierarchy Γ.alt n p := by
  simp [IsPrenexHierarchy]

lemma isPrenexHierarchy_iff_exists_qqToPrenex :
    IsPrenexHierarchy Γ n p ↔ ∃ θ, p = qqToPrenex Γ n θ ∧ IsBounded θ := by
  induction n generalizing Γ p <;> simp [IsPrenexHierarchy, *]

lemma IsPrenexHierarchy.neg (hp : IsUFormula ℒₒᵣ p) (h : IsPrenexHierarchy Γ n p) :
    IsPrenexHierarchy Γ.alt n (Bootstrapping.neg ℒₒᵣ p) := by
  induction n generalizing Γ p with
  | zero => exact IsBounded.neg hp h
  | succ n ih =>
    obtain ⟨q, rfl, hq⟩ := h
    have hq' : IsUFormula ℒₒᵣ q := isUFormula_qqQuant.mp hp
    exact ⟨neg ℒₒᵣ q, neg_qqQuant hq', ih hq' hq⟩

end isPrenexHierarchy

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
