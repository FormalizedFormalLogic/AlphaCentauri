module

public import AlphaCentauri.Bootstrapping.Completeness.Henkin
public import AlphaCentauri.ToFoundation.SquarePair

/-!
# Satisfaction in the Henkin set along a list of free variables

For a list `s` coded by `squarePair`, a coded formula `a` with `n` bound variables is satisfied in
the Henkin set when its instance by the free variables `^&s₀, …, ^&s_{n-1}` belongs to the Henkin
set, and a coded term `t` equates to `z` when the equation of its instance with `^&z` belongs to the
Henkin set. Both relations are defined by arithmetical formulas that do not depend on the model.
Satisfaction commutes with the connectives and quantifiers, the quantifiers ranging over the free
variables put in front of the list, and it reduces atomic formulas and terms to the values of their
arguments.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Bounding

section fvarVec

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace SquarePairFvarVec

def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y s. y = 0”
  succ := .mkSigma
    “y ih k s. ∃ a, !squarePairNthGraph a s k ∧ ∃ f, !qqFvarDef f a ∧ !concatDef y ih f”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun x k ih ↦ concat ih (^&(squarePairNth (x 0) k))
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end SquarePairFvarVec

/-- The vector `^&s₀, …, ^&s_{n-1}` of the free variables listed by the first `n` entries of the
list `s`. -/
noncomputable def squarePairFvarVec (n s : V) : V := SquarePairFvarVec.construction.result ![s] n

def squarePairFvarVecGraph : 𝚺ᴬ₁.Semisentence 3 := SquarePairFvarVec.blueprint.resultDef

instance squarePairFvarVec.defined :
    𝚺ᴬ₁-Function₂ (squarePairFvarVec : V → V → V) via squarePairFvarVecGraph := .mk fun v ↦ by
  simp [SquarePairFvarVec.construction.result_defined_iff, squarePairFvarVecGraph]; rfl

instance squarePairFvarVec.definable : 𝚺ᴬ₁-Function₂ (squarePairFvarVec : V → V → V) :=
  squarePairFvarVec.defined.to_definable

@[simp] lemma squarePairFvarVec_zero (s : V) : squarePairFvarVec 0 s = 0 := by
  simp [squarePairFvarVec, SquarePairFvarVec.construction]

lemma squarePairFvarVec_succ (n s : V) :
    squarePairFvarVec (n + 1) s = concat (squarePairFvarVec n s) (^&(squarePairNth s n)) := by
  simp [squarePairFvarVec, SquarePairFvarVec.construction]

@[simp] lemma len_squarePairFvarVec (n s : V) : len (squarePairFvarVec n s) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => simp [squarePairFvarVec_succ, ih]

lemma nth_squarePairFvarVec (n s : V) :
    ∀ i < n, (squarePairFvarVec n s).[i] = ^&(squarePairNth s i) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    intro i hi
    rcases (lt_succ_iff_le.mp hi).lt_or_eq with hlt | rfl
    · rw [squarePairFvarVec_succ, concat_nth_lt _ _ (by simpa using hlt)]
      exact ih i hlt
    · rw [squarePairFvarVec_succ, concat_nth_len' _ _ (by simp)]

lemma squarePairFvarVec_squarePair (n a s : V) :
    squarePairFvarVec (n + 1) (squarePair a s) = ^&a ∷ squarePairFvarVec n s := by
  apply nth_ext' (n + 1) (by simp) (by simp)
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp [nth_squarePairFvarVec _ _ 0 hi]
  · rw [nth_squarePairFvarVec _ _ _ hi, nth_adjoin_succ,
      nth_squarePairFvarVec _ _ _ (by simpa using hi), squarePairNth_squarePair_succ]

lemma isSemitermVec_squarePairFvarVec (L : Language) [L.Encodable] [L.LORDefinable] (n s : V) :
    IsSemitermVec L n 0 (squarePairFvarVec n s) :=
  IsSemitermVec.iff.mpr ⟨by simp, fun i hi ↦ by simp [nth_squarePairFvarVec _ _ _ hi]⟩

end fvarVec

section satisfaction

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

variable {L : Language} [L.Encodable] [L.LORDefinable] (S : Theory L) [S.Δ₁]

/-- The instance of the coded formula `a` by the free variables listed by the first `n` entries of
`s` is in the Henkin set of `S`. -/
def HenkinSatisfies (a n s : V) : Prop := HenkinSet S (subst L (squarePairFvarVec n s) a)

/-- The $\Sigma_2$ formula defining `HenkinSatisfies S`. -/
noncomputable def henkinSatisfiesDef : 𝚺ᴬ_[2].Semisentence 3 := .mkSigma
  “a n s. ∃ w, !squarePairFvarVecGraph w n s ∧ ∃ c, !(substsGraph L) c w a ∧
    !(henkinSetDef S).sigma.val c”
  (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt])

instance HenkinSatisfies.defined :
    𝚺ᴬ_[2]-Relation₃[V] (HenkinSatisfies S) via henkinSatisfiesDef S := .mk fun v ↦ by
  simp [henkinSatisfiesDef, HenkinSatisfies]

section equality

variable [L.Eq]

/-- The equation of the instance of the coded term `t` by the free variables listed by the first
`n` entries of `s` with the free variable `^&z` is in the Henkin set of `S`. -/
def HenkinEquates (t n s z : V) : Prop :=
  HenkinSet S (^rel 2 (Encodable.encode (Language.Eq.eq : L.Rel 2) : V)
    ?[termSubst L (squarePairFvarVec n s) t, ^&z])

/-- The $\Sigma_2$ formula defining `HenkinEquates S`. -/
noncomputable def henkinEquatesDef : 𝚺ᴬ_[2].Semisentence 4 := .mkSigma
  “t n s z. ∃ w, !squarePairFvarVecGraph w n s ∧ ∃ u, !(termSubstGraph L) u w t ∧
    ∃ x, !qqFvarDef x z ∧ ∃ e, !mkVec₂Def e u x ∧
    ∃ c, !qqRelDef c 2 ↑(Encodable.encode (Language.Eq.eq : L.Rel 2)) e ∧
    !(henkinSetDef S).sigma.val c”
  (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt])

instance HenkinEquates.defined :
    𝚺ᴬ_[2]-Relation₄[V] (HenkinEquates S) via henkinEquatesDef S := .mk fun v ↦ by
  simp [henkinEquatesDef, HenkinEquates, numeral_eq_natCast]

/-- The $\Sigma_2$ formula defining `HenkinEq S`. -/
noncomputable def henkinEqDef : 𝚺ᴬ_[2].Semisentence 2 := .mkSigma
  “y z. ∃ t, !qqFvarDef t y ∧ ∃ x, !qqFvarDef x z ∧ ∃ e, !mkVec₂Def e t x ∧
    ∃ c, !qqRelDef c 2 ↑(Encodable.encode (Language.Eq.eq : L.Rel 2)) e ∧
    !(henkinSetDef S).sigma.val c”
  (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt])

instance HenkinEq.defined : 𝚺ᴬ_[2]-Relation[V] (HenkinEq S) via henkinEqDef S := .mk fun v ↦ by
  simp [henkinEqDef, HenkinEq, Semiformula.equal, numeral_eq_natCast, quote_rel_def]

instance IsRepresentative.defined :
    𝚷ᴬ_[2]-Predicate[V] (IsRepresentative S) via henkinDomainDef S := .mk fun v ↦ by
  simp [henkinDomainDef, IsRepresentative, HenkinEq, Semiformula.equal, numeral_eq_natCast,
    quote_rel_def]

end equality

section closure

variable {S}

private lemma henkinSet_subst_iff {n p : V} (hp : IsSemiformula L n p) (s : V) :
    HenkinSatisfies S p n s ↔ HenkinSet S
      (⟨subst L (squarePairFvarVec n s) p, hp.subst (isSemitermVec_squarePairFvarVec L n s)⟩ :
        Formula V L).val := Iff.rfl

variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

omit hS hcons in
lemma henkinSatisfies_verum (n s : V) : HenkinSatisfies S ^⊤ n s := by
  simpa [HenkinSatisfies] using henkinSet_of_tprovable S (φ := (⊤ : Formula V L)) (by simp)

lemma not_henkinSatisfies_falsum (n s : V) : ¬HenkinSatisfies S ^⊥ n s := by
  simpa [HenkinSatisfies] using henkinSet_not_falsum S hS hcons

lemma henkinSatisfies_and_iff {n p q : V} (hp : IsSemiformula L n p) (hq : IsSemiformula L n q)
    (s : V) :
    HenkinSatisfies S (p ^⋏ q) n s ↔ HenkinSatisfies S p n s ∧ HenkinSatisfies S q n s := by
  rw [henkinSet_subst_iff hp, henkinSet_subst_iff hq, ← henkinSet_and_iff S hS hcons]
  simp [HenkinSatisfies, hp.isUFormula, hq.isUFormula]

lemma henkinSatisfies_or_iff {n p q : V} (hp : IsSemiformula L n p) (hq : IsSemiformula L n q)
    (s : V) :
    HenkinSatisfies S (p ^⋎ q) n s ↔ HenkinSatisfies S p n s ∨ HenkinSatisfies S q n s := by
  rw [henkinSet_subst_iff hp, henkinSet_subst_iff hq, ← henkinSet_or_iff S hS hcons]
  simp [HenkinSatisfies, hp.isUFormula, hq.isUFormula]

lemma henkinSatisfies_neg_iff {n p : V} (hp : IsSemiformula L n p) (s : V) :
    HenkinSatisfies S (neg L p) n s ↔ ¬HenkinSatisfies S p n s := by
  rw [henkinSet_subst_iff hp, ← henkinSet_neg_iff S hS hcons, HenkinSatisfies,
    substs_neg hp (isSemitermVec_squarePairFvarVec L n s)]
  rfl

lemma henkinSatisfies_all_iff {n p : V} (hp : IsSemiformula L (n + 1) p) (s : V) :
    HenkinSatisfies S (^∀ p) n s ↔ ∀ u, HenkinSatisfies S p (n + 1) (squarePair u s) := by
  have hw := isSemitermVec_squarePairFvarVec L n s
  let φ : Semiformula V L 1 := ⟨subst L (qVec L (squarePairFvarVec n s)) p, by
    simpa using hp.subst hw.qVec⟩
  have h₁ : HenkinSatisfies S (^∀ p) n s ↔ HenkinSet S (∀¹ φ).val := by
    simp [HenkinSatisfies, φ, hp.isUFormula]
  rw [h₁, henkinSet_all_iff S hS hcons]
  refine forall_congr' fun u ↦ ?_
  rw [Semiformula.val_subst_fvar, HenkinSatisfies, squarePairFvarVec_squarePair]
  simp only [φ]
  rw [substs1_subst_qVec hw hp (by simp)]

lemma henkinSatisfies_exs_iff {n p : V} (hp : IsSemiformula L (n + 1) p) (s : V) :
    HenkinSatisfies S (^∃ p) n s ↔ ∃ u, HenkinSatisfies S p (n + 1) (squarePair u s) := by
  have hw := isSemitermVec_squarePairFvarVec L n s
  let φ : Semiformula V L 1 := ⟨subst L (qVec L (squarePairFvarVec n s)) p, by
    simpa using hp.subst hw.qVec⟩
  have h₁ : HenkinSatisfies S (^∃ p) n s ↔ HenkinSet S (∃¹ φ).val := by
    simp [HenkinSatisfies, φ, hp.isUFormula]
  rw [h₁, henkinSet_exs_iff S hS hcons]
  refine exists_congr fun u ↦ ?_
  rw [Semiformula.val_subst_fvar, HenkinSatisfies, squarePairFvarVec_squarePair]
  simp only [φ]
  rw [substs1_subst_qVec hw hp (by simp)]

omit hS hcons in
lemma henkinSatisfies_zero_iff {p : V} (hp : IsFormula L p) (s : V) :
    HenkinSatisfies S p 0 s ↔ HenkinSet S p := by
  rw [HenkinSatisfies, squarePairFvarVec_zero,
    subst_eq_self hp (by simp) (fun i hi ↦ absurd hi (by simp))]

end closure

section atomic

variable [L.Eq] {S}

omit [L.Eq] in
private lemma isSemiterm_termSubst {n t : V} (ht : IsSemiterm L n t) (s : V) :
    IsSemiterm L 0 (termSubst L (squarePairFvarVec n s) t) :=
  (isSemitermVec_squarePairFvarVec L n s).termSubst ht

private lemma henkinEquates_iff {n t : V} (ht : IsSemiterm L n t) (s z : V) :
    HenkinEquates S t n s z ↔ HenkinSet S (Semiformula.equal
      (⟨termSubst L (squarePairFvarVec n s) t, isSemiterm_termSubst ht s⟩ : Term V L)
      (Semiterm.fvar z)).val := by
  simp [HenkinEquates, Semiformula.equal, quote_rel_def]

omit [L.Eq] in
lemma isSemitermVec_matrixToVec {n : V} {k : ℕ} {t : Fin k → V}
    (ht : ∀ j, IsSemiterm L n (t j)) : IsSemitermVec L (k : V) n (matrixToVec t) := by
  refine IsSemitermVec.iff.mpr ⟨by simp, fun i hi ↦ ?_⟩
  obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hi
  have hj : j < k := by exact_mod_cast hi
  have e := matrixToVec_nth t ⟨j, hj⟩
  simp only at e
  rw [e]
  exact ht _

omit [L.Eq] in
private lemma termSubstVec_matrixToVec {n : V} {k : ℕ} {t : Fin k → V}
    (ht : ∀ j, IsSemiterm L n (t j)) (s : V) :
    termSubstVec L (k : V) (squarePairFvarVec n s) (matrixToVec t) =
      SemitermVec.val (fun j ↦ (⟨termSubst L (squarePairFvarVec n s) (t j),
        isSemiterm_termSubst (ht j) s⟩ : Term V L)) := by
  have hv := (isSemitermVec_matrixToVec ht).isUTerm
  apply nth_ext' (k : V) (by simp [hv]) (by simp)
  intro i hi
  obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hi
  have hj : j < k := by exact_mod_cast hi
  rw [nth_termSubstVec hv hi]
  have e := SemitermVec.val_nth_eq (fun j ↦
    (⟨termSubst L (squarePairFvarVec n s) (t j), isSemiterm_termSubst (ht j) s⟩ : Term V L))
    ⟨j, hj⟩
  simp only at e
  rw [e]
  have e' := matrixToVec_nth t ⟨j, hj⟩
  simp only at e'
  rw [e']

variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

variable [𝗘𝗤 L ⪯ S]

lemma henkinSatisfies_rel_iff {k : ℕ} (R : L.Rel k) {n : V} {t z : Fin k → V}
    (ht : ∀ j, IsSemiterm L n (t j)) (s : V) (h : ∀ j, HenkinEquates S (t j) n s (z j)) :
    HenkinSatisfies S (^rel (k : V) ⌜R⌝ (matrixToVec t)) n s ↔
      HenkinSet S (Semiformula.rel R (fun j ↦ Semiterm.fvar (z j)) : Formula V L).val := by
  have hv := (isSemitermVec_matrixToVec ht).isUTerm
  rw [HenkinSatisfies, substs_rel (by simp) hv, termSubstVec_matrixToVec ht s,
    ← Semiformula.rel_val]
  exact henkinSet_rel_iff S hS hcons R fun j ↦ (henkinEquates_iff (ht j) s (z j)).mp (h j)

lemma henkinEquates_func {k : ℕ} (f : L.Func k) {n : V} {t z : Fin k → V}
    (ht : ∀ j, IsSemiterm L n (t j)) (s y : V) (h : ∀ j, HenkinEquates S (t j) n s (z j))
    (hf : HenkinSet S (Semiformula.equal (Semiterm.func f fun j ↦ Semiterm.fvar (z j))
      (Semiterm.fvar y) : Formula V L).val) :
    HenkinEquates S (^func (k : V) ⌜f⌝ (matrixToVec t)) n s y := by
  have hv := isSemitermVec_matrixToVec ht
  have ht' : IsSemiterm L n (^func (k : V) ⌜f⌝ (matrixToVec t)) :=
    IsSemiterm.func.mpr ⟨by simp, hv⟩
  rw [henkinEquates_iff ht']
  have e : (⟨termSubst L (squarePairFvarVec n s) (^func (k : V) ⌜f⌝ (matrixToVec t)),
      isSemiterm_termSubst ht' s⟩ : Term V L) = Semiterm.func f (fun j ↦
        ⟨termSubst L (squarePairFvarVec n s) (t j), isSemiterm_termSubst (ht j) s⟩) := by
    apply Semiterm.ext
    change termSubst L _ _ = _
    rw [Semiterm.func_val, termSubst_func (by simp) hv.isUTerm, termSubstVec_matrixToVec ht s]
  rw [e]
  exact henkinSet_equal_trans S hS hcons (henkinSet_equal_func S hS hcons f
    fun j ↦ (henkinEquates_iff (ht j) s (z j)).mp (h j)) hf

omit hS hcons [𝗘𝗤 L ⪯ S] in
lemma henkinEquates_bvar_iff {n i : V} (hi : i < n) (s z : V) :
    HenkinEquates S (^#i) n s z ↔ HenkinEq S (squarePairNth s i) z := by
  simp [HenkinEquates, HenkinEq, Semiformula.equal, quote_rel_def,
    nth_squarePairFvarVec _ _ _ hi]

end atomic

end satisfaction

end FFL.FirstOrder.Arithmetic.Bootstrapping
