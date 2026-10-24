module

public import AlphaCentauri.Bootstrapping.Completeness.Henkin
public import AlphaCentauri.ToFoundation.InternalEquality

/-!
# The Henkin set as a term model

The Henkin set of a theory $S$ in a model of $\mathsf{PA}$ in which $S$ is consistent behaves like
the set of sentences true in a term model: it is a complete theory closed under internal
provability with the Henkin property. Provable equality of free variables is an equivalence
relation, every class has a least element, its representative, and every application of a function
symbol to free variables equals the free variable of a unique representative. Equality of
arbitrary terms is symmetric and transitive, and function and relation symbols respect it.

The arithmetical operators of the Henkin translation of a language $L$ into arithmetic are read
off from the Henkin set: the domain consists of the representatives, a relation holds of
representatives when the atomic formula on the corresponding free variables is in the Henkin set,
and a function symbol is interpreted by the graph given by the equation of its application with a
free variable.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq]
variable (S : Theory L) [S.Δ₁]

section closure

variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons
omit [L.Eq]

omit hS hcons in
theorem henkinSet_of_tprovable {φ : Formula V L} (h : S.internalize V ⊢ φ) :
    HenkinSet S φ.val :=
  HenkinSet.of_provable S (Semiformula.isSemiformula_zero φ) (tprovable_iff_provable.mp h)

theorem henkinSet_of_tprovable_imp {φ ψ : Formula V L} (h : S.internalize V ⊢ φ 🡒 ψ)
    (hφ : HenkinSet S φ.val) : HenkinSet S ψ.val :=
  HenkinSet.modus_ponens hS hcons hφ (henkinSet_of_tprovable S h)

theorem henkinSet_neg_iff {φ : Formula V L} : HenkinSet S (∼φ).val ↔ ¬HenkinSet S φ.val :=
  HenkinSet.neg_iff hS hcons (Semiformula.isSemiformula_zero φ)

theorem henkinSet_not_falsum : ¬HenkinSet S (⊥ : Formula V L).val := by
  have h : HenkinSet S (∼(⊥ : Formula V L)).val :=
    henkinSet_of_tprovable S <| by simp [Entailment.verum]
  exact (henkinSet_neg_iff S hS hcons).mp h

theorem henkinSet_and_iff {φ ψ : Formula V L} :
    HenkinSet S (φ ⋏ ψ).val ↔ HenkinSet S φ.val ∧ HenkinSet S ψ.val := by
  constructor
  · intro h
    exact ⟨henkinSet_of_tprovable_imp S hS hcons Entailment.and₁ h,
      henkinSet_of_tprovable_imp S hS hcons Entailment.and₂ h⟩
  · rintro ⟨h₁, h₂⟩
    exact HenkinSet.modus_ponens hS hcons h₂
      (henkinSet_of_tprovable_imp S hS hcons Entailment.and₃ h₁)

theorem henkinSet_or_iff {φ ψ : Formula V L} :
    HenkinSet S (φ ⋎ ψ).val ↔ HenkinSet S φ.val ∨ HenkinSet S ψ.val := by
  have e : φ ⋎ ψ = ∼(∼φ ⋏ ∼ψ) := by simp
  rw [e, henkinSet_neg_iff S hS hcons, henkinSet_and_iff S hS hcons, henkinSet_neg_iff S hS hcons,
    henkinSet_neg_iff S hS hcons]
  tauto

omit hS hcons in
private lemma tprovable_subst_imp_exs (φ : Semiformula V L 1) (t : Semiterm V L 0) :
    S.internalize V ⊢ φ.subst ![t] 🡒 ∃¹ φ := ⟨by
  rw [Semiformula.imp_def]
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.exs t
  exact TDerivation.em (φ.subst ![t])⟩

omit hS hcons in
private lemma tprovable_all_imp_subst (φ : Semiformula V L 1) (t : Semiterm V L 0) :
    S.internalize V ⊢ ∀¹ φ 🡒 φ.subst ![t] := ⟨by
  rw [Semiformula.imp_def, Semiformula.neg_all]
  apply TDerivation.or
  apply TDerivation.exs t
  simpa using TDerivation.em (φ.subst ![t])⟩

theorem henkinSet_exs_iff {φ : Semiformula V L 1} :
    HenkinSet S (∃¹ φ).val ↔
      ∃ u : V, HenkinSet S (φ.subst ![(Semiterm.fvar u : Semiterm V L 0)]).val := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := HenkinSet.exists_substs1 hS hcons (Semiformula.isSemiformula_one φ) h
    exact ⟨u, by simpa [substs1] using hu⟩
  · rintro ⟨u, hu⟩
    exact henkinSet_of_tprovable_imp S hS hcons (tprovable_subst_imp_exs S φ _) hu

theorem henkinSet_all_iff {φ : Semiformula V L 1} :
    HenkinSet S (∀¹ φ).val ↔
      ∀ u : V, HenkinSet S (φ.subst ![(Semiterm.fvar u : Semiterm V L 0)]).val := by
  constructor
  · intro h u
    exact henkinSet_of_tprovable_imp S hS hcons (tprovable_all_imp_subst S φ _) h
  · intro h
    by_contra hn
    have h₁ : HenkinSet S (∼(∀¹ φ)).val := (henkinSet_neg_iff S hS hcons).mpr hn
    rw [Semiformula.neg_all] at h₁
    obtain ⟨u, hu⟩ := (henkinSet_exs_iff S hS hcons).mp h₁
    rw [Semiformula.substs_neg, henkinSet_neg_iff S hS hcons] at hu
    exact hu (h u)

end closure

section equality

variable [𝗘𝗤 L ⪯ S]

/-- The free variables `^&u` and `^&v` are provably equal in the Henkin set. -/
def HenkinEq (u v : V) : Prop :=
  HenkinSet S (Semiformula.equal (Semiterm.fvar u) (Semiterm.fvar v) : Formula V L).val

/-- The free variable `^&a` is the least of the free variables provably equal to it. -/
def IsRepresentative (a : V) : Prop := ∀ y < a, ¬HenkinEq S y a

omit [𝗘𝗤 L ⪯ S] in
private lemma henkinEq_definable (u : V) : 𝚫ᴬ_[2]-Predicate[V] fun a ↦ HenkinEq S a u := by
  have hf : 𝚺ᴬ₁-Function₁[V] fun a ↦
      (Semiformula.equal (Semiterm.fvar a) (Semiterm.fvar u) : Formula V L).val := by
    simp only [Semiformula.equal, Semiformula.rel_val, Nat.cast_ofNat, SemitermVec.val_succ,
      Matrix.head_cons, Semiterm.fvar_val, Matrix.tail_cons, SemitermVec.val_nil]
    definability
  exact (henkinSet_definable S).comp (hf.of_lt (by simp))

variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

omit hS hcons in
theorem HenkinEq.refl (u : V) : HenkinEq S u u :=
  henkinSet_of_tprovable S (tprovable_equal_refl S (Semiterm.fvar u))

theorem HenkinEq.symm {u v : V} (h : HenkinEq S u v) : HenkinEq S v u :=
  henkinSet_of_tprovable_imp S hS hcons
    (tprovable_equal_symm_imp S (Semiterm.fvar u) (Semiterm.fvar v)) h

theorem HenkinEq.trans {u v w : V} (h₁ : HenkinEq S u v) (h₂ : HenkinEq S v w) :
    HenkinEq S u w :=
  henkinSet_of_tprovable_imp S hS hcons
    (tprovable_equal_trans_imp S (Semiterm.fvar u) (Semiterm.fvar v) (Semiterm.fvar w))
    ((henkinSet_and_iff S hS hcons).mpr ⟨h₁, h₂⟩)

theorem exists_isRepresentative (u : V) : ∃ a, IsRepresentative S a ∧ HenkinEq S a u := by
  obtain ⟨a, ha, hmin⟩ := InductionOnHierarchy.least_number_sigma 𝚫 2
    (P := fun a ↦ HenkinEq S a u) (henkinEq_definable S u) (x := u) (HenkinEq.refl S u)
  exact ⟨a, fun y hy hya ↦ hmin y hy (HenkinEq.trans S hS hcons hya ha), ha⟩

theorem IsRepresentative.eq_of_henkinEq {a b : V} (ha : IsRepresentative S a)
    (hb : IsRepresentative S b) (h : HenkinEq S a b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (hb a hab h).elim
  · exact hab
  · exact (ha b hab (HenkinEq.symm S hS hcons h)).elim

end equality

section function

variable [𝗘𝗤 L ⪯ S]
variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

theorem exists_isRepresentative_henkinFunc {k : ℕ} (f : L.Func k) (v : Fin k → V) :
    ∃ y, IsRepresentative S y ∧
      HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
        (Semiterm.fvar y) : Formula V L).val := by
  set t : Semiterm V L 0 := Semiterm.func f (fun i ↦ Semiterm.fvar (v i))
  have h₁ : S.internalize V ⊢ ∃¹ (Semiformula.equal t.bShift (Semiterm.bvar 0)) :=
    TProof.ex_intro! _ t <| by simpa [Semiformula.equal] using tprovable_equal_refl S t
  obtain ⟨u, hu⟩ := (henkinSet_exs_iff S hS hcons).mp (henkinSet_of_tprovable S h₁)
  obtain ⟨a, ha, hau⟩ := exists_isRepresentative S hS hcons u
  have h₂ : HenkinSet S (Semiformula.equal t (Semiterm.fvar u) : Formula V L).val := by
    simpa [Semiformula.equal] using hu
  have h₃ : HenkinSet S (Semiformula.equal (Semiterm.fvar u) (Semiterm.fvar a) :
      Formula V L).val := HenkinEq.symm S hS hcons hau
  exact ⟨a, ha, henkinSet_of_tprovable_imp S hS hcons
    (tprovable_equal_trans_imp S t (Semiterm.fvar u) (Semiterm.fvar a))
    ((henkinSet_and_iff S hS hcons).mpr ⟨h₂, h₃⟩)⟩

theorem IsRepresentative.eq_of_henkinFunc {k : ℕ} (f : L.Func k) (v : Fin k → V) {y y' : V}
    (hy : IsRepresentative S y) (hy' : IsRepresentative S y')
    (h : HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
      (Semiterm.fvar y) : Formula V L).val)
    (h' : HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
      (Semiterm.fvar y') : Formula V L).val) : y = y' := by
  set t : Semiterm V L 0 := Semiterm.func f (fun i ↦ Semiterm.fvar (v i))
  have h₁ : HenkinEq S y y' :=
    henkinSet_of_tprovable_imp S hS hcons
      (tprovable_equal_trans_imp S (Semiterm.fvar y) t (Semiterm.fvar y'))
      ((henkinSet_and_iff S hS hcons).mpr
        ⟨henkinSet_of_tprovable_imp S hS hcons
          (tprovable_equal_symm_imp S t (Semiterm.fvar y)) h, h'⟩)
  exact hy.eq_of_henkinEq S hS hcons hy' h₁

theorem henkinSet_equal_fvar_iff {a b : V} (ha : IsRepresentative S a) (hb : IsRepresentative S b) :
    HenkinSet S (Semiformula.equal (Semiterm.fvar a) (Semiterm.fvar b) : Formula V L).val ↔
      a = b := by
  constructor
  · intro h
    exact ha.eq_of_henkinEq S hS hcons hb h
  · rintro rfl
    exact HenkinEq.refl S a

end function

section congruence

variable [𝗘𝗤 L ⪯ S]
variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

omit [L.Eq] [𝗘𝗤 L ⪯ S] in
theorem henkinSet_conj_iff {k : ℕ} (v : Fin k → Formula V L) :
    HenkinSet S (Matrix.conj v).val ↔ ∀ i, HenkinSet S (v i).val := by
  induction k with
  | zero =>
    simpa using henkinSet_of_tprovable S (φ := (⊤ : Formula V L)) (by simp)
  | succ k ih =>
    rw [Matrix.conj, henkinSet_and_iff S hS hcons, ih, Fin.forall_fin_succ]
    exact Iff.rfl

omit hS hcons in
theorem henkinSet_equal_refl (t : Semiterm V L 0) : HenkinSet S (Semiformula.equal t t).val :=
  henkinSet_of_tprovable S <| tprovable_equal_refl S t

theorem henkinSet_equal_symm {s t : Semiterm V L 0}
    (h : HenkinSet S (Semiformula.equal s t).val) : HenkinSet S (Semiformula.equal t s).val :=
  henkinSet_of_tprovable_imp S hS hcons (tprovable_equal_symm_imp S s t) h

theorem henkinSet_equal_trans {s t u : Semiterm V L 0}
    (h₁ : HenkinSet S (Semiformula.equal s t).val)
    (h₂ : HenkinSet S (Semiformula.equal t u).val) : HenkinSet S (Semiformula.equal s u).val :=
  henkinSet_of_tprovable_imp S hS hcons (tprovable_equal_trans_imp S s t u)
    ((henkinSet_and_iff S hS hcons).mpr ⟨h₁, h₂⟩)

theorem henkinSet_equal_func {k : ℕ} (f : L.Func k) {s u : SemitermVec V L k 0}
    (h : ∀ i, HenkinSet S (Semiformula.equal (s i) (u i)).val) :
    HenkinSet S (Semiformula.equal (Semiterm.func f s) (Semiterm.func f u)).val :=
  henkinSet_of_tprovable_imp S hS hcons (tprovable_equal_func_imp S f s u)
    ((henkinSet_conj_iff S hS hcons _).mpr h)

private theorem henkinSet_rel_imp {k : ℕ} (R : L.Rel k) {s u : SemitermVec V L k 0}
    (h : ∀ i, HenkinSet S (Semiformula.equal (s i) (u i)).val)
    (hs : HenkinSet S (Semiformula.rel R s).val) : HenkinSet S (Semiformula.rel R u).val :=
  HenkinSet.modus_ponens hS hcons hs <|
    henkinSet_of_tprovable_imp S hS hcons (tprovable_rel_congr_imp S R s u)
      ((henkinSet_conj_iff S hS hcons _).mpr h)

theorem henkinSet_rel_iff {k : ℕ} (R : L.Rel k) {s u : SemitermVec V L k 0}
    (h : ∀ i, HenkinSet S (Semiformula.equal (s i) (u i)).val) :
    HenkinSet S (Semiformula.rel R s).val ↔ HenkinSet S (Semiformula.rel R u).val :=
  ⟨henkinSet_rel_imp S hS hcons R h,
    henkinSet_rel_imp S hS hcons R fun i ↦ henkinSet_equal_symm S hS hcons (h i)⟩

end congruence

section operators

lemma eq_matrixToVec_iff {k : ℕ} {w : V} {u : Fin k → V} :
    w = matrixToVec u ↔ (k : V) = len w ∧ ∀ i : Fin k, w.[((i : ℕ) : V)] = u i := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h₁, h₂⟩
    apply nth_ext' (k : V) h₁.symm (by simp)
    intro i hi
    obtain ⟨i, rfl⟩ := eq_fin_of_lt_nat hi
    simp [h₂]

/-- The $\Pi_2$ formula of `henkinDomain S`. -/
noncomputable def henkinDomainDef : 𝚷ᴬ_[2].Semisentence 1 := .mkPi
  “a. ∀ y < a, ∀ t, !qqFvarDef t y → ∀ s, !qqFvarDef s a → ∀ e, !mkVec₂Def e t s →
    ∀ c, !qqRelDef c 2 ↑(Encodable.encode (Language.Eq.eq : L.Rel 2)) e →
    ¬!(henkinSetDef S).sigma.val c”
  (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt])

/-- The $\Sigma_2$ formula of `henkinRel S R`. -/
noncomputable def henkinRelDef {k : ℕ} (R : L.Rel k) : 𝚺ᴬ_[2].Semisentence k := .mkSigma
  “∃ w, !lenDef ↑k w ∧ (⋀ i, ∃ z, !nthDef z w ↑(i : Fin k).val ∧ !qqFvarDef z #i.succ.succ) ∧
    ∃ c, !qqRelDef c ↑k ↑(Encodable.encode R) w ∧ !(henkinSetDef S).sigma.val c”
  (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt])

/-- The $\Sigma_2$ formula of `henkinFunc S f`. -/
noncomputable def henkinFuncDef {k : ℕ} (f : L.Func k) : 𝚺ᴬ_[2].Semisentence (k + 1) := .mkSigma
  “z. ∃ w, !lenDef ↑k w ∧
    (⋀ i, ∃ t, !nthDef t w ↑(i : Fin k).val ∧ !qqFvarDef t #i.succ.succ.succ) ∧
    ∃ t, !qqFuncDef t ↑k ↑(Encodable.encode f) w ∧ ∃ s, !qqFvarDef s z ∧ ∃ e, !mkVec₂Def e t s ∧
    ∃ c, !qqRelDef c 2 ↑(Encodable.encode (Language.Eq.eq : L.Rel 2)) e ∧
    !(henkinSetDef S).sigma.val c”
  (by simp [HierarchySymbol.Semiformula.hierarchy_of_lt])

/-- The representatives of the free variables up to provable equality. -/
noncomputable def henkinDomain : Semiformula.Operator ℒₒᵣ 1 := ⟨(henkinDomainDef S).val⟩

/-- The relation symbol `R` holds of the free variables `y₀, …, y_{k-1}` when `R(^&y₀, …)` is in
the Henkin set. -/
noncomputable def henkinRel {k : ℕ} (R : L.Rel k) : Semiformula.Operator ℒₒᵣ k :=
  ⟨(henkinRelDef S R).val⟩

/-- The function symbol `f` maps the free variables `y₀, …, y_{k-1}` to `z` when
`f(^&y₀, …) = ^&z` is in the Henkin set. -/
noncomputable def henkinFunc {k : ℕ} (f : L.Func k) : Semiformula.Operator ℒₒᵣ (k + 1) :=
  ⟨(henkinFuncDef S f).val⟩

theorem henkinDomain_val (a : V) : (henkinDomain S).val ![a] ↔ IsRepresentative S a := by
  simp [henkinDomain, henkinDomainDef, Semiformula.Operator.val, IsRepresentative, HenkinEq,
    Semiformula.equal, numeral_eq_natCast, quote_rel_def]

omit [L.Eq] in
theorem henkinRel_val {k : ℕ} (R : L.Rel k) (v : Fin k → V) :
    (henkinRel S R).val v ↔
      HenkinSet S (Semiformula.rel R (fun i ↦ Semiterm.fvar (v i)) : Formula V L).val := by
  simp [henkinRel, henkinRelDef, Semiformula.Operator.val]
  simp only [numeral_eq_natCast, ← and_assoc, ← eq_matrixToVec_iff, exists_eq_left]
  rfl

theorem henkinFunc_val {k : ℕ} (f : L.Func k) (z : V) (v : Fin k → V) :
    (henkinFunc S f).val (z :> v) ↔
      HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
        (Semiterm.fvar z) : Formula V L).val := by
  simp [henkinFunc, henkinFuncDef, Semiformula.Operator.val]
  simp only [numeral_eq_natCast, ← and_assoc, ← eq_matrixToVec_iff, exists_eq_left]
  rfl

end operators

end FFL.FirstOrder.Arithmetic.Bootstrapping
