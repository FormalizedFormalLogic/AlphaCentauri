module

public import AlphaCentauri.Bootstrapping.PartialTruth.Assignment

/-!
# Truth by complexity

`ComplexitySatisfied N e p` says that the internal formula `p` of complexity at most `N` is
satisfied when its bound variables take the values listed in `e` and its free variables the
value `0`. It is $\Delta_{N+1}$, agrees with $\Delta_0$ satisfaction on formulas of complexity
`0`, does not depend on the bound `N` once `N` is at least the complexity of the formula, and
satisfies the Tarski conditions for the connectives and quantifiers, for negation and for
substitution. It is the satisfaction of a standard arithmetic formula of complexity at most `N`
when applied to the code of that formula.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `ComplexitySatisfied N e p`: the formula code `p`, of complexity at most `N`, is satisfied when
its bound variables take the values listed in `e` and its free variables the value `0`. -/
def ComplexitySatisfied : ℕ → V → V → Prop
  | 0 => fun e p ↦ formulaComplexity ℒₒᵣ p = 0 ∧ BoundedSatisfied e p
  | N + 1 => fun e p ↦
    (formulaComplexity ℒₒᵣ p = 0 → BoundedSatisfied e p) ∧
    (∀ q < p, ∀ r < p, p = q ^⋏ r → ComplexitySatisfied N e q ∧ ComplexitySatisfied N e r) ∧
    (∀ q < p, ∀ r < p, p = q ^⋎ r → ComplexitySatisfied N e q ∨ ComplexitySatisfied N e r) ∧
    (∀ q < p, p = ^∀ q → ∀ x, ComplexitySatisfied N (x ∷ e) q) ∧
    (∀ q < p, p = ^∃ q → ∃ x, ComplexitySatisfied N (x ∷ e) q)

instance ComplexitySatisfied.definable :
    (N : ℕ) → 𝚫ᴬ_[N + 1]-Relation (ComplexitySatisfied N : V → V → Prop)
  | 0 => by
    have : 𝚫ᴬ_[1]-Relation fun e p : V ↦ formulaComplexity ℒₒᵣ p = 0 ∧ BoundedSatisfied e p := by
      definability
    exact this.of_iff fun _ ↦ Iff.rfl
  | N + 1 => by
    have := ComplexitySatisfied.definable N
    have : 𝚫ᴬ_[N + 1]-Relation (BoundedSatisfied : V → V → Prop) :=
      BoundedSatisfied.definable.of_deltaOne
    have hc : 𝚫ᴬ_[N + 1]-Relation fun e p : V ↦
        (formulaComplexity ℒₒᵣ p = 0 → BoundedSatisfied e p) ∧
        (∀ q < p, ∀ r < p, p = q ^⋏ r → ComplexitySatisfied N e q ∧ ComplexitySatisfied N e r) ∧
        (∀ q < p, ∀ r < p, p = q ^⋎ r → ComplexitySatisfied N e q ∨ ComplexitySatisfied N e r) := by
      definability
    have hall : 𝚷ᴬ_[N + 1]-Relation fun e p : V ↦
        ∀ q < p, p = ^∀ q → ∀ x, ComplexitySatisfied N (x ∷ e) q := by
      definability
    have hex : 𝚺ᴬ_[N + 1]-Relation fun e p : V ↦
        ∀ q < p, p = ^∃ q → ∃ x, ComplexitySatisfied N (x ∷ e) q := by
      definability
    exact (((hc.of_lt (by simp)).and (hall.of_lt (by simp))).and (hex.of_lt (by simp))).of_iff
      fun _ ↦ by simp [ComplexitySatisfied, and_assoc]

instance ComplexitySatisfied.definable' (Γ : SigmaPiDelta) (N : ℕ) :
    Γᴬ_[N + 1]-Relation (ComplexitySatisfied N : V → V → Prop) :=
  (ComplexitySatisfied.definable N).of_delta

variable {N : ℕ} {e p q r : V}

namespace ComplexitySatisfied

lemma iff_boundedSatisfied (h : formulaComplexity ℒₒᵣ p = 0) :
    ComplexitySatisfied N e p ↔ BoundedSatisfied e p := by
  cases N with
  | zero => simp [ComplexitySatisfied, h]
  | succ N =>
    constructor
    · rintro ⟨h₁, -⟩
      exact h₁ h
    · intro hb
      obtain ⟨-, hu⟩ := hb.dom
      and_intros
      · exact fun _ ↦ hb
      · rintro q - r - rfl
        obtain ⟨hq, hr⟩ := IsUFormula.and.mp hu
        simp [hq, hr] at h
      · rintro q - r - rfl
        obtain ⟨hq, hr⟩ := IsUFormula.or.mp hu
        simp [hq, hr] at h
      · rintro q - rfl
        simp [IsUFormula.all.mp hu] at h
      · rintro q - rfl
        simp [IsUFormula.ex.mp hu] at h

private lemma succ_and (hq : IsUFormula ℒₒᵣ q) (hr : IsUFormula ℒₒᵣ r) :
    ComplexitySatisfied (N + 1) e (q ^⋏ r) ↔
      ComplexitySatisfied N e q ∧ ComplexitySatisfied N e r := by
  constructor
  · intro h
    exact h.2.1 q (by simp) r (by simp) rfl
  · intro h
    and_intros
    · simp [hq, hr]
    · rintro q' - r' - he
      obtain ⟨rfl, rfl⟩ := (qqAnd_inj _ _ _ _).mp he
      exact h
    all_goals
      first
      | (rintro q' - r' - he; simp [qqAnd, qqOr] at he)
      | (rintro q' - he; simp [qqAnd, qqAll, qqExs] at he)

private lemma succ_or (hq : IsUFormula ℒₒᵣ q) (hr : IsUFormula ℒₒᵣ r) :
    ComplexitySatisfied (N + 1) e (q ^⋎ r) ↔
      ComplexitySatisfied N e q ∨ ComplexitySatisfied N e r := by
  constructor
  · intro h
    exact h.2.2.1 q (by simp) r (by simp) rfl
  · intro h
    and_intros
    · simp [hq, hr]
    · rintro q' - r' - he
      simp [qqAnd, qqOr] at he
    · rintro q' - r' - he
      obtain ⟨rfl, rfl⟩ := (qqOr_inj _ _ _ _).mp he
      exact h
    all_goals
      rintro q' - he
      simp [qqOr, qqAll, qqExs] at he

private lemma succ_all (hq : IsUFormula ℒₒᵣ q) :
    ComplexitySatisfied (N + 1) e (^∀ q) ↔ ∀ x, ComplexitySatisfied N (x ∷ e) q := by
  constructor
  · intro h
    exact h.2.2.2.1 q (by simp) rfl
  · intro h
    and_intros
    · simp [hq]
    · rintro q' - r' - he
      simp [qqAnd, qqAll] at he
    · rintro q' - r' - he
      simp [qqOr, qqAll] at he
    · rintro q' - he
      obtain rfl := (qqAll_inj _ _).mp he
      exact h
    · rintro q' - he
      simp [qqAll, qqExs] at he

private lemma succ_exs (hq : IsUFormula ℒₒᵣ q) :
    ComplexitySatisfied (N + 1) e (^∃ q) ↔ ∃ x, ComplexitySatisfied N (x ∷ e) q := by
  constructor
  · intro h
    exact h.2.2.2.2 q (by simp) rfl
  · intro h
    and_intros
    · simp [hq]
    · rintro q' - r' - he
      simp [qqAnd, qqExs] at he
    · rintro q' - r' - he
      simp [qqOr, qqExs] at he
    · rintro q' - he
      simp [qqAll, qqExs] at he
    · rintro q' - he
      obtain rfl := (qqExs_inj _ _).mp he
      exact h

lemma succ_iff (hp : IsUFormula ℒₒᵣ p) (h : formulaComplexity ℒₒᵣ p ≤ N) :
    ComplexitySatisfied (N + 1) e p ↔ ComplexitySatisfied N e p := by
  induction N generalizing e p with
  | zero =>
    have hc : formulaComplexity ℒₒᵣ p = 0 := by simpa using h
    rw [iff_boundedSatisfied hc, iff_boundedSatisfied hc]
  | succ N ih =>
    by_cases hc : formulaComplexity ℒₒᵣ p = 0
    · rw [iff_boundedSatisfied hc, iff_boundedSatisfied hc]
    rcases hp.cases_of_formulaComplexity_ne_zero hc with
      ⟨q, r, hq, hr, rfl⟩ | ⟨q, r, hq, hr, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨h₁, h₂⟩ : formulaComplexity ℒₒᵣ q ≤ N ∧ formulaComplexity ℒₒᵣ r ≤ N := by
        simpa [hq, hr] using h
      rw [succ_and hq hr, succ_and hq hr, ih hq h₁, ih hr h₂]
    · obtain ⟨h₁, h₂⟩ : formulaComplexity ℒₒᵣ q ≤ N ∧ formulaComplexity ℒₒᵣ r ≤ N := by
        simpa [hq, hr] using h
      rw [succ_or hq hr, succ_or hq hr, ih hq h₁, ih hr h₂]
    · rw [succ_all hq, succ_all hq]
      exact forall_congr' fun x ↦ ih hq (by simpa [hq] using h)
    · rw [succ_exs hq, succ_exs hq]
      exact exists_congr fun x ↦ ih hq (by simpa [hq] using h)

lemma and_iff (hq : IsUFormula ℒₒᵣ q) (hr : IsUFormula ℒₒᵣ r)
    (h : formulaComplexity ℒₒᵣ (q ^⋏ r) ≤ N) :
    ComplexitySatisfied N e (q ^⋏ r) ↔
      ComplexitySatisfied N e q ∧ ComplexitySatisfied N e r := by
  cases N with
  | zero => simp [hq, hr] at h
  | succ N =>
    obtain ⟨h₁, h₂⟩ : formulaComplexity ℒₒᵣ q ≤ N ∧ formulaComplexity ℒₒᵣ r ≤ N := by
      simpa [hq, hr] using h
    rw [succ_and hq hr, succ_iff hq h₁, succ_iff hr h₂]

lemma or_iff (hq : IsUFormula ℒₒᵣ q) (hr : IsUFormula ℒₒᵣ r)
    (h : formulaComplexity ℒₒᵣ (q ^⋎ r) ≤ N) :
    ComplexitySatisfied N e (q ^⋎ r) ↔
      ComplexitySatisfied N e q ∨ ComplexitySatisfied N e r := by
  cases N with
  | zero => simp [hq, hr] at h
  | succ N =>
    obtain ⟨h₁, h₂⟩ : formulaComplexity ℒₒᵣ q ≤ N ∧ formulaComplexity ℒₒᵣ r ≤ N := by
      simpa [hq, hr] using h
    rw [succ_or hq hr, succ_iff hq h₁, succ_iff hr h₂]

lemma all_iff (hq : IsUFormula ℒₒᵣ q) (h : formulaComplexity ℒₒᵣ (^∀ q) ≤ N) :
    ComplexitySatisfied N e (^∀ q) ↔ ∀ x, ComplexitySatisfied N (x ∷ e) q := by
  cases N with
  | zero => simp [hq] at h
  | succ N =>
    rw [succ_all hq]
    exact forall_congr' fun x ↦ (succ_iff hq (by simpa [hq] using h)).symm

lemma exs_iff (hq : IsUFormula ℒₒᵣ q) (h : formulaComplexity ℒₒᵣ (^∃ q) ≤ N) :
    ComplexitySatisfied N e (^∃ q) ↔ ∃ x, ComplexitySatisfied N (x ∷ e) q := by
  cases N with
  | zero => simp [hq] at h
  | succ N =>
    rw [succ_exs hq]
    exact exists_congr fun x ↦ (succ_iff hq (by simpa [hq] using h)).symm

@[simp] lemma verum : ComplexitySatisfied N e (^⊤ : V) := by
  rw [iff_boundedSatisfied (by simp)]
  simp

@[simp] lemma not_falsum : ¬ComplexitySatisfied N e (^⊥ : V) := by
  rw [iff_boundedSatisfied (by simp)]
  simp

lemma subst {n m w : V} (hw : IsSemitermVec ℒₒᵣ n m w) (hp : IsSemiformula ℒₒᵣ n p) :
    ComplexitySatisfied N e (Bootstrapping.subst ℒₒᵣ w p) ↔
      ComplexitySatisfied N (termValVec e n w) p := by
  induction N generalizing n m w e p with
  | zero =>
    simp only [ComplexitySatisfied, fomulaComplexity_substs hp hw]
    apply and_congr_right
    intro hc
    exact BoundedSatisfied.subst hw hp (hp.isUFormula.isBounded_of_formulaComplexity_eq_zero hc)
  | succ N ih =>
    by_cases hc : formulaComplexity ℒₒᵣ p = 0
    · rw [iff_boundedSatisfied (by rwa [fomulaComplexity_substs hp hw]), iff_boundedSatisfied hc]
      exact BoundedSatisfied.subst hw hp (hp.isUFormula.isBounded_of_formulaComplexity_eq_zero hc)
    rcases hp.isUFormula.cases_of_formulaComplexity_ne_zero hc with
      ⟨q, r, hq, hr, rfl⟩ | ⟨q, r, hq, hr, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨hq', hr'⟩ := IsSemiformula.and.mp hp
      rw [substs_and hq hr, succ_and (hq'.subst hw).isUFormula (hr'.subst hw).isUFormula,
        succ_and hq hr, ih hw hq', ih hw hr']
    · obtain ⟨hq', hr'⟩ := IsSemiformula.or.mp hp
      rw [substs_or hq hr, succ_or (hq'.subst hw).isUFormula (hr'.subst hw).isUFormula,
        succ_or hq hr, ih hw hq', ih hw hr']
    · have hq' := IsSemiformula.all.mp hp
      rw [substs_all hq, succ_all (hq'.subst hw.qVec).isUFormula, succ_all hq]
      exact forall_congr' fun x ↦ by rw [ih hw.qVec hq', termValVec_qVec hw]
    · have hq' := IsSemiformula.exs.mp hp
      rw [substs_ex hq, succ_exs (hq'.subst hw.qVec).isUFormula, succ_exs hq]
      exact exists_congr fun x ↦ by rw [ih hw.qVec hq', termValVec_qVec hw]

lemma neg_iff (hp : IsUFormula ℒₒᵣ p) (h : formulaComplexity ℒₒᵣ p ≤ N) :
    ComplexitySatisfied N e (neg ℒₒᵣ p) ↔ ¬ComplexitySatisfied N e p := by
  induction N generalizing e p with
  | zero =>
    have hc : formulaComplexity ℒₒᵣ p = 0 := by simpa using h
    rw [iff_boundedSatisfied (by simpa [hp] using hc), iff_boundedSatisfied hc]
    exact BoundedSatisfied.neg_iff (hp.isBounded_of_formulaComplexity_eq_zero hc) hp
  | succ N ih =>
    by_cases hc : formulaComplexity ℒₒᵣ p = 0
    · rw [iff_boundedSatisfied (by simpa [hp] using hc), iff_boundedSatisfied hc]
      exact BoundedSatisfied.neg_iff (hp.isBounded_of_formulaComplexity_eq_zero hc) hp
    rcases hp.cases_of_formulaComplexity_ne_zero hc with
      ⟨q, r, hq, hr, rfl⟩ | ⟨q, r, hq, hr, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨h₁, h₂⟩ : formulaComplexity ℒₒᵣ q ≤ N ∧ formulaComplexity ℒₒᵣ r ≤ N := by
        simpa [hq, hr] using h
      rw [neg_and hq hr, succ_or hq.neg hr.neg, succ_and hq hr, ih hq h₁, ih hr h₂,
        not_and_or]
    · obtain ⟨h₁, h₂⟩ : formulaComplexity ℒₒᵣ q ≤ N ∧ formulaComplexity ℒₒᵣ r ≤ N := by
        simpa [hq, hr] using h
      rw [neg_or hq hr, succ_and hq.neg hr.neg, succ_or hq hr, ih hq h₁, ih hr h₂,
        not_or]
    · rw [neg_all hq, succ_exs hq.neg, succ_all hq, not_forall]
      exact exists_congr fun x ↦ ih hq (by simpa [hq] using h)
    · rw [neg_ex hq, succ_all hq.neg, succ_exs hq, not_exists]
      exact forall_congr' fun x ↦ ih hq (by simpa [hq] using h)

theorem quote_iff {n : ℕ} (φ : ArithmeticSemisentence n) (h : φ.complexity ≤ N)
    (v : Fin n → V) : ComplexitySatisfied N (matrixToVec v) ⌜φ⌝ ↔ V ⊧/v φ := by
  induction φ using Semiformula.rec' generalizing N with
  | hrel R w | hnrel R w | hverum | hfalsum =>
    rw [iff_boundedSatisfied (by simp)]
    exact boundedSatisfied_quote_iff (by simp) v
  | hand φ ψ ihφ ihψ =>
    have hV : formulaComplexity ℒₒᵣ (⌜φ ⋏ ψ⌝ : V) ≤ N := by
      rw [Semisentence.formulaComplexity_quote]
      exact_mod_cast h
    simp only [Semiformula.complexity_and] at h
    rw [Sentence.quote_and] at hV ⊢
    rw [and_iff (Sentence.quote_isUFormula φ) (Sentence.quote_isUFormula ψ) hV,
      ihφ (by omega), ihψ (by omega)]
    simp
  | hor φ ψ ihφ ihψ =>
    have hV : formulaComplexity ℒₒᵣ (⌜φ ⋎ ψ⌝ : V) ≤ N := by
      rw [Semisentence.formulaComplexity_quote]
      exact_mod_cast h
    simp only [Semiformula.complexity_or] at h
    rw [Sentence.quote_or] at hV ⊢
    rw [or_iff (Sentence.quote_isUFormula φ) (Sentence.quote_isUFormula ψ) hV,
      ihφ (by omega), ihψ (by omega)]
    simp
  | hall φ ih =>
    have hV : formulaComplexity ℒₒᵣ (⌜∀¹ φ⌝ : V) ≤ N := by
      rw [Semisentence.formulaComplexity_quote]
      exact_mod_cast h
    simp only [Semiformula.complexity_all] at h
    rw [Sentence.quote_all] at hV ⊢
    rw [all_iff (Sentence.quote_isUFormula φ) hV, FirstOrder.Semiformula.eval_all]
    exact forall_congr' fun x ↦ by
      rw [show x ∷ matrixToVec v = matrixToVec (x :> v) by simp]
      exact ih (by omega) _
  | hexs φ ih =>
    have hV : formulaComplexity ℒₒᵣ (⌜∃¹ φ⌝ : V) ≤ N := by
      rw [Semisentence.formulaComplexity_quote]
      exact_mod_cast h
    simp only [Semiformula.complexity_exs] at h
    rw [Sentence.quote_ex] at hV ⊢
    rw [exs_iff (Sentence.quote_isUFormula φ) hV, FirstOrder.Semiformula.eval_ex]
    exact exists_congr fun x ↦ by
      rw [show x ∷ matrixToVec v = matrixToVec (x :> v) by simp]
      exact ih (by omega) _

theorem quote_sentence_iff {σ : ArithmeticSentence} (h : σ.complexity ≤ N) :
    ComplexitySatisfied N 0 (⌜σ⌝ : V) ↔ V↓[ℒₒᵣ] ⊧ σ := by
  simpa [matrixToVec_nil, models_iff] using quote_iff (V := V) σ h ![]

end ComplexitySatisfied

end FFL.FirstOrder.Arithmetic.Bootstrapping
