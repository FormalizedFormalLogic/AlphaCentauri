module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.Interpretability.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Equality
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.ProvableIff
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.QuantifierBlock
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed

/-!
# Tables of translations

A table `tbl` is a table of a translation of $L_2$ in a theory $S$ of $L_1$, in a model `V` of
$\mathsf{I}\Sigma_1$, when its entries are formulas of the right arities and `S` proves in `V`
that the domain formula of `tbl` is nonempty, and that the graph of each function symbol defines
a unique value on the domain and respects equality. A table of a direct translation `π` is a table
of a translation in this sense.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping
variable {Γ : SigmaPiDelta} {m : ℕ}

attribute [local simp] Semiformula.substs_substs

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Vectors of domain formulas and of equations -/

section vectors

variable (L : Language) [L.Encodable] [L.LORDefinable]

noncomputable def domainVec.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y tbl s. y = 0”
  succ := .mkSigma
    “y ih k tbl s. ∃ d, !(domainAtGraph L) d tbl (s + k) ∧ !concatDef y ih d”

noncomputable def domainVec.construction : PR.Construction V (domainVec.blueprint L) where
  zero := fun _ ↦ 0
  succ := fun x k ih ↦ concat ih (domainAt L (x 0) (x 1 + k))
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

/-- `domainVec L tbl s k` is the vector whose `j`-th entry, for `j < k`, is the domain formula of
`tbl` at `^#(s + j)`. -/
noncomputable def domainVec (tbl s k : V) : V := (domainVec.construction L).result ![tbl, s] k

/-- The $\Sigma_1$ graph of `domainVec`, with argument order `(y, tbl, s, k)`. -/
noncomputable def domainVecGraph : 𝚺ᴬ₁.Semisentence 4 :=
  (domainVec.blueprint L).resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

variable [L.Eq]

noncomputable def equationVec.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y a b. y = 0”
  succ := .mkSigma
    “y ih k a b. ∃ x, !qqBvarDef x (a + k) ∧ ∃ z, !qqBvarDef z (b + k) ∧ ∃ e, !mkVec₂Def e x z ∧
      ∃ r, !qqRelDef r 2 ↑(Encodable.encode (Language.Eq.eq : L.Rel 2)) e ∧ !concatDef y ih r”

noncomputable def equationVec.construction : PR.Construction V (equationVec.blueprint L) where
  zero := fun _ ↦ 0
  succ := fun x k ih ↦
    concat ih (^rel 2 (Encodable.encode (Language.Eq.eq : L.Rel 2) : V) ?[^#(x 0 + k), ^#(x 1 + k)])
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]

/-- `equationVec L a b k` is the vector whose `j`-th entry, for `j < k`, is the equation
`^#(a + j) = ^#(b + j)`. -/
noncomputable def equationVec (a b k : V) : V := (equationVec.construction L).result ![a, b] k

/-- The $\Sigma_1$ graph of `equationVec`, with argument order `(y, a, b, k)`. -/
noncomputable def equationVecGraph : 𝚺ᴬ₁.Semisentence 4 :=
  (equationVec.blueprint L).resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

variable {L}

omit [L.Eq] in
instance domainVec.defined : 𝚺ᴬ₁-Function₃[V] domainVec L via domainVecGraph L := .mk fun v ↦ by
  simp [(domainVec.construction L).result_defined_iff, domainVecGraph]; rfl

omit [L.Eq] in
instance domainVec.definable : 𝚺ᴬ₁-Function₃[V] domainVec L := domainVec.defined.to_definable

omit [L.Eq] in
instance domainVec.definable' : Γᴬ_[m + 1]-Function₃[V] domainVec L :=
  domainVec.definable.of_sigmaOne

instance equationVec.defined : 𝚺ᴬ₁-Function₃[V] equationVec L via equationVecGraph L :=
  .mk fun v ↦ by simp [(equationVec.construction L).result_defined_iff, equationVecGraph]; rfl

instance equationVec.definable : 𝚺ᴬ₁-Function₃[V] equationVec L :=
  equationVec.defined.to_definable

instance equationVec.definable' : Γᴬ_[m + 1]-Function₃[V] equationVec L :=
  equationVec.definable.of_sigmaOne

omit [L.Eq] in
@[simp] lemma domainVec_zero (tbl s : V) : domainVec L tbl s 0 = 0 := by
  simp [domainVec, domainVec.construction]

omit [L.Eq] in
@[simp] lemma domainVec_succ (tbl s k : V) :
    domainVec L tbl s (k + 1) = concat (domainVec L tbl s k) (domainAt L tbl (s + k)) := by
  simp [domainVec, domainVec.construction]

omit [L.LORDefinable] in
@[simp] lemma equationVec_zero (a b : V) : equationVec L a b 0 = 0 := by
  simp [equationVec, equationVec.construction]

omit [L.LORDefinable] in
@[simp] lemma equationVec_succ (a b k : V) :
    equationVec L a b (k + 1) = concat (equationVec L a b k)
      (^rel 2 (Encodable.encode (Language.Eq.eq : L.Rel 2) : V) ?[^#(a + k), ^#(b + k)]) := by
  simp [equationVec, equationVec.construction]

omit [L.Eq] in
@[simp] lemma len_domainVec (tbl s k : V) : len (domainVec L tbl s k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

omit [L.Eq] in
lemma nth_domainVec (tbl s k : V) :
    ∀ j < k, (domainVec L tbl s k).[j] = domainAt L tbl (s + j) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro j hj
    rcases (lt_succ_iff_le.mp hj).lt_or_eq with hlt | rfl
    · rw [domainVec_succ, concat_nth_lt _ _ (by simpa using hlt)]
      exact ih j hlt
    · rw [domainVec_succ, concat_nth_len' _ _ (by simp)]

omit [L.LORDefinable] in
@[simp] lemma len_equationVec (a b k : V) : len (equationVec L a b k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

omit [L.LORDefinable] in
lemma nth_equationVec (a b k : V) : ∀ j < k, (equationVec L a b k).[j] =
    ^rel 2 (Encodable.encode (Language.Eq.eq : L.Rel 2) : V) ?[^#(a + j), ^#(b + j)] := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro j hj
    rcases (lt_succ_iff_le.mp hj).lt_or_eq with hlt | rfl
    · rw [equationVec_succ, concat_nth_lt _ _ (by simpa using hlt)]
      exact ih j hlt
    · rw [equationVec_succ, concat_nth_len' _ _ (by simp)]

end vectors

/-! ## Codes of the conditions on a table -/

section codes

variable (L : Language) [L.Encodable] [L.LORDefinable] [L.Eq]

/-- The code of `⋀ i, δ(^#i) → ∃ y, δ(y) ∧ γ(y, ^#0, …, ^#(k - 1))` (with `k` free bound
variables), where `δ` is the domain formula of `tbl` and `γ` the graph of the `k`-ary function
symbol `f`. -/
noncomputable def funcExistsCode (tbl k f : V) : V :=
  imp L (^⋀ domainVec L tbl 0 k)
    (^∃ (domainAt L tbl 0 ^⋏ subst L (^#0 ∷ bvarVec 1 k) (tableFunc tbl k f)))

/-- The code of the uniqueness of the value of the graph `γ` of `f` on the domain `δ`, with `k + 2`
free bound variables: `⋀ i, δ(^#(i + 2)) ∧ δ(^#0) ∧ δ(^#1) ∧ γ(^#0, …) ∧ γ(^#1, …) → ^#0 = ^#1`. -/
noncomputable def funcUniqueCode (tbl k f : V) : V :=
  imp L ((^⋀ domainVec L tbl 2 k) ^⋏ domainAt L tbl 0 ^⋏ domainAt L tbl 1 ^⋏
      subst L (^#0 ∷ bvarVec 2 k) (tableFunc tbl k f) ^⋏
        subst L (^#1 ∷ bvarVec 2 k) (tableFunc tbl k f))
    (^rel 2 (Encodable.encode (Language.Eq.eq : L.Rel 2) : V) ?[^#0, ^#1])

/-- The code of the invariance of the graph `γ` of `f` under equality, with `2(k + 1)` free bound
variables: `⋀ j ≤ k, ^#j = ^#(k + 1 + j) → (γ(^#0, …, ^#k) → γ(^#(k + 1), …, ^#(2k + 1)))`. -/
noncomputable def funcCongrCode (tbl k f : V) : V :=
  imp L (^⋀ equationVec L 0 (k + 1) (k + 1))
    (imp L (subst L (bvarVec 0 (k + 1)) (tableFunc tbl k f))
      (subst L (bvarVec (k + 1) (k + 1)) (tableFunc tbl k f)))

instance funcExistsCode.definable : 𝚺ᴬ₁-Function₃[V] funcExistsCode L := by
  unfold funcExistsCode
  definability

instance funcUniqueCode.definable : 𝚺ᴬ₁-Function₃[V] funcUniqueCode L := by
  unfold funcUniqueCode
  definability

instance funcCongrCode.definable : 𝚺ᴬ₁-Function₃[V] funcCongrCode L := by
  unfold funcCongrCode
  definability

end codes

section preserveEqCode

variable (L₁ L₂ : Language) [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq]

/-- The code of `δ(^#1) → δ(^#0) → (ε(^#1, ^#0) ↔ ^#1 = ^#0)` (with two free bound variables),
where `δ` is the domain formula of `tbl` and `ε` the formula interpreting equality. -/
noncomputable def preserveEqCode (tbl : V) : V :=
  imp L₁ (domainAt L₁ tbl 1) (imp L₁ (domainAt L₁ tbl 0)
    (iff L₁ (subst L₁ ?[^#1, ^#0]
        (tableRel tbl 2 (Encodable.encode (Language.Eq.eq : L₂.Rel 2) : V)))
      (^rel 2 (Encodable.encode (Language.Eq.eq : L₁.Rel 2) : V) ?[^#1, ^#0])))

instance preserveEqCode.definable : 𝚺ᴬ₁-Function₁[V] preserveEqCode L₁ L₂ := by
  unfold preserveEqCode
  definability

end preserveEqCode

/-! ## Typed formulas of a table -/

section typed

section typedVal

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma val_allItr {n k : ℕ} (φ : Semiformula V L (n + k)) :
    (∀¹^[k] φ).val = qqAlls φ.val k := by
  induction k with
  | zero => simp
  | succ k ih => simpa [allItr_succ, qqAlls_all] using ih (∀¹ φ)

lemma val_conj_typed {n m : ℕ} (v : Fin m → Semiformula V L n) :
    (Matrix.conj v).val = ^⋀ matrixToVec fun i ↦ (v i).val := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Matrix.conj, ih, matrixToVec_succ, qqConj_cons, Semiformula.val_and]
    rfl

lemma val_allItr_imp_conj {n k : ℕ} (d : Semiformula V L 1) (A : Fin k → Semiformula V L 1)
    (C : Semiformula V L (n + k)) :
    (∀¹^[k] (Matrix.conj (fun i : Fin k ↦
        d.subst ![Semiterm.bvar (i.addCast n)] ⋏ (A i).subst ![Semiterm.bvar (i.addCast n)])
          🡒 C)).val =
      qqAlls (imp L (^⋀ matrixToVec fun i ↦
        (d.subst ![Semiterm.bvar (i.addCast n)] ⋏ (A i).subst ![Semiterm.bvar (i.addCast n)]).val)
          C.val) k := by
  rw [val_allItr, Semiformula.val_imp, val_conj_typed]

end typedVal

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] {tbl : V}

namespace IsTable

variable (hT : IsTable L₁ L₂ tbl)

/-- The domain formula of the table, as a typed formula. -/
noncomputable def domT : Semiformula V L₁ 1 := ⟨tableDomain tbl, by simpa using hT.domain⟩

/-- The formula of the graph of the function symbol `F`, as a typed formula. -/
noncomputable def funcT {k : ℕ} (F : L₂.Func k) : Semiformula V L₁ (k + 1) :=
  ⟨tableFunc tbl k ⌜F⌝, by simpa using hT.func (codeIn_func_quote F)⟩

/-- The formula interpreting the relation symbol `R`, as a typed formula. -/
noncomputable def relT {k : ℕ} (R : L₂.Rel k) : Semiformula V L₁ k :=
  ⟨tableRel tbl k ⌜R⌝, hT.rel (codeIn_rel_quote R)⟩

@[simp] lemma domT_val : hT.domT.val = tableDomain tbl := rfl

@[simp] lemma funcT_val {k : ℕ} (F : L₂.Func k) : (hT.funcT F).val = tableFunc tbl k ⌜F⌝ := rfl

@[simp] lemma relT_val {k : ℕ} (R : L₂.Rel k) : (hT.relT R).val = tableRel tbl k ⌜R⌝ := rfl

lemma domT_shift : hT.domT.shift = hT.domT := by
  ext
  simp [hT.domain_shift]

lemma funcT_shift {k : ℕ} (F : L₂.Func k) : (hT.funcT F).shift = hT.funcT F := by
  ext
  simp [hT.func_shift (codeIn_func_quote F)]

lemma relT_shift {k : ℕ} (R : L₂.Rel k) : (hT.relT R).shift = hT.relT R := by
  ext
  simp [hT.rel_shift (codeIn_rel_quote R)]

end IsTable

section bodies

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {k : ℕ} {f : V}

/-- `⋀ i, d(#i) → ∃ y, d(y) ∧ g(y, #0, …, #(k - 1))`. -/
noncomputable def funcExistsBody (d : Semiformula V L 1) (g : Semiformula V L (k + 1)) :
    Semiformula V L k :=
  Matrix.conj (fun i ↦ d.subst ![Semiterm.bvar i]) 🡒
    ∃¹ (d.subst ![Semiterm.bvar 0] ⋏ g.subst (Semiterm.bvar 0 :> fun i ↦ Semiterm.bvar i.succ))

/-- `⋀ i, d(#(i + 2)) ∧ d(#0) ∧ d(#1) ∧ g(#0, …) ∧ g(#1, …) → #0 = #1`. -/
noncomputable def funcUniqueBody (d : Semiformula V L 1) (g : Semiformula V L (k + 1)) :
    Semiformula V L (k + 2) :=
  (Matrix.conj (fun i ↦ d.subst ![Semiterm.bvar i.succ.succ]) ⋏
    d.subst ![Semiterm.bvar 0] ⋏ d.subst ![Semiterm.bvar 1] ⋏
    g.subst (Semiterm.bvar 0 :> fun i ↦ Semiterm.bvar i.succ.succ) ⋏
    g.subst (Semiterm.bvar 1 :> fun i ↦ Semiterm.bvar i.succ.succ)) 🡒
      Semiformula.equal (Semiterm.bvar 0) (Semiterm.bvar 1)

/-- `⋀ j, #j = #(k + 1 + j) → (g(#0, …, #k) → g(#(k + 1), …, #(2k + 1)))`. -/
noncomputable def funcCongrBody (g : Semiformula V L (k + 1)) :
    Semiformula V L ((k + 1) + (k + 1)) :=
  Matrix.conj (fun j : Fin (k + 1) ↦
      Semiformula.equal (Semiterm.bvar (Fin.castAdd (k + 1) j))
        (Semiterm.bvar (Fin.natAdd (k + 1) j))) 🡒
    (g.subst (fun j ↦ Semiterm.bvar (Fin.castAdd (k + 1) j)) 🡒
      g.subst (fun j ↦ Semiterm.bvar (Fin.natAdd (k + 1) j)))

omit [L.Eq] in
lemma val_conj_domainAt (d : Semiformula V L 1) (hd : d.val = tableDomain tbl) {n : ℕ} (s : ℕ)
    (f : Fin k → Fin n) (hf : ∀ i, (f i : ℕ) = s + i) :
    (Matrix.conj fun i ↦ d.subst ![Semiterm.bvar (f i)]).val = ^⋀ domainVec L tbl s k := by
  rw [val_conj_typed]
  congr 1
  symm
  rw [eq_matrixToVec_iff]
  constructor
  · simp
  · intro i
    rw [nth_domainVec _ _ _ _ (by simp), Semiformula.val_substs, hd, domainAt]
    simp [hf]

lemma val_conj_equation {n : ℕ} (a b : ℕ) (f g : Fin k → Fin n) (hf : ∀ i, (f i : ℕ) = a + i)
    (hg : ∀ i, (g i : ℕ) = b + i) :
    (Matrix.conj fun i ↦ Semiformula.equal (L := L) (Semiterm.bvar (f i))
      (Semiterm.bvar (g i)) : Semiformula V L n).val =
        ^⋀ equationVec L (a : V) (b : V) (k : V) := by
  rw [val_conj_typed]
  congr 1
  symm
  rw [eq_matrixToVec_iff]
  constructor
  · simp
  · intro i
    rw [nth_equationVec _ _ _ _ (by simp)]
    simp [Semiformula.equal, hf, hg, quote_rel_def]

omit [L.Eq] in
lemma val_subst_funcArgs (g : Semiformula V L (k + 1)) (hg : g.val = tableFunc tbl k f) {n : ℕ}
    (a : Fin n) (s : ℕ) (b : Fin k → Fin n) (hb : ∀ i, (b i : ℕ) = s + i) :
    (g.subst (Semiterm.bvar a :> fun i ↦ Semiterm.bvar (b i))).val =
      subst L (^#(a : V) ∷ bvarVec (s : V) k) (tableFunc tbl k f) := by
  rw [Semiformula.val_substs, hg, SemitermVec.val_cons, bvarVec_eq_matrixToVec]
  change subst L (^#(a : V) ∷ matrixToVec fun i ↦ (Semiterm.bvar (b i) : Semiterm V L n).val) _ = _
  congr 3
  funext i
  simp [hb, add_comm]

omit [L.Eq] in
lemma funcExistsBody_val (d : Semiformula V L 1) (hd : d.val = tableDomain tbl)
    (g : Semiformula V L (k + 1)) (hg : g.val = tableFunc tbl k f) :
    (funcExistsBody d g).val = funcExistsCode L tbl k f := by
  have hc := val_conj_domainAt d hd (n := k) 0 (fun i ↦ i) (by simp)
  rw [funcExistsBody, Semiformula.val_imp, hc,
    Semiformula.val_exs, Semiformula.val_and,
    val_subst_funcArgs g hg 0 1 Fin.succ (by simp [add_comm]), Semiformula.val_substs, hd]
  simp [funcExistsCode, domainAt]

lemma funcUniqueBody_val (d : Semiformula V L 1) (hd : d.val = tableDomain tbl)
    (g : Semiformula V L (k + 1)) (hg : g.val = tableFunc tbl k f) :
    (funcUniqueBody d g).val = funcUniqueCode L tbl k f := by
  rw [funcUniqueBody, Semiformula.val_imp, Semiformula.val_and,
    val_conj_domainAt d hd 2 (fun i ↦ i.succ.succ) (fun i ↦ by simp; omega), Semiformula.val_and,
    Semiformula.val_and, Semiformula.val_and,
    val_subst_funcArgs g hg 0 2 (fun i ↦ i.succ.succ) (fun i ↦ by simp; omega),
    val_subst_funcArgs g hg 1 2 (fun i ↦ i.succ.succ) (fun i ↦ by simp; omega),
    Semiformula.val_substs, Semiformula.val_substs, hd]
  simp [funcUniqueCode, domainAt, Semiformula.equal, quote_rel_def]

lemma funcCongrBody_val (g : Semiformula V L (k + 1)) (hg : g.val = tableFunc tbl k f) :
    (funcCongrBody g).val = funcCongrCode L tbl k f := by
  have hc := val_conj_equation (V := V) (L := L) (k := k + 1) (n := k + 1 + (k + 1)) 0 (k + 1)
    (fun j ↦ Fin.castAdd (k + 1) j) (fun j ↦ Fin.natAdd (k + 1) j) (by simp) (by simp [add_comm])
  have h₀ := bvarVec_eq_matrixToVec (V := V) 0 (k + 1)
  have h₁ := bvarVec_eq_matrixToVec (V := V) ((k + 1 : ℕ) : V) (k + 1)
  push_cast at hc h₀ h₁
  rw [funcCongrBody, Semiformula.val_imp, Semiformula.val_imp, funcCongrCode, hc,
    Semiformula.val_substs, Semiformula.val_substs, hg, h₀, h₁]
  congr 3 <;>
  · change matrixToVec (fun j ↦ (Semiterm.bvar _ : Semiterm V L (k + 1 + (k + 1))).val) = _
    congr 1
    funext j
    simp

omit [L.Eq] in
lemma funcExistsBody_shift {d : Semiformula V L 1} {g : Semiformula V L (k + 1)}
    (hd : d.shift = d) (hg : g.shift = g) : (funcExistsBody d g).shift = funcExistsBody d g := by
  simp only [funcExistsBody, Semiformula.shift_imp, Semiformula.shift_conj, Semiformula.shift_exs,
    Semiformula.shift_and, Semiformula.shift_substs, Semiterm.shift_vecMap_bvar,
    Matrix.vecMap_cons', Matrix.head_cons, Matrix.tail_cons, Matrix.vecMap_nil, Semiterm.shift_bvar,
    hd, hg]

lemma funcUniqueBody_shift {d : Semiformula V L 1} {g : Semiformula V L (k + 1)}
    (hd : d.shift = d) (hg : g.shift = g) : (funcUniqueBody d g).shift = funcUniqueBody d g := by
  simp [funcUniqueBody, Semiformula.shift_substs, hd, hg]

lemma funcCongrBody_shift {g : Semiformula V L (k + 1)} (hg : g.shift = g) :
    (funcCongrBody g).shift = funcCongrBody g := by
  simp only [funcCongrBody, Semiformula.shift_imp, Semiformula.shift_conj,
    Semiformula.shift_substs, Semiterm.shift_vecMap_bvar, hg]
  simp

end bodies

/-- `d(#1) → d(#0) → (e(#1, #0) ↔ #1 = #0)`. -/
noncomputable def preserveEqBody (d : Semiformula V L₁ 1) (e : Semiformula V L₁ 2) :
    Semiformula V L₁ 2 :=
  d.subst ![Semiterm.bvar 1] 🡒 d.subst ![Semiterm.bvar 0] 🡒
    (e.subst ![Semiterm.bvar 1, Semiterm.bvar 0] 🡘
      Semiformula.equal (Semiterm.bvar 1) (Semiterm.bvar 0))

omit [L₂.LORDefinable] in
lemma preserveEqBody_val [L₂.Eq] (d : Semiformula V L₁ 1) (hd : d.val = tableDomain tbl)
    (e : Semiformula V L₁ 2)
    (he : e.val = tableRel tbl 2 (Encodable.encode (Language.Eq.eq : L₂.Rel 2) : V)) :
    (preserveEqBody d e).val = preserveEqCode L₁ L₂ tbl := by
  simp [preserveEqBody, preserveEqCode, Semiformula.val_substs, hd, he, domainAt,
    Semiformula.equal, quote_rel_def]

lemma preserveEqBody_shift {d : Semiformula V L₁ 1} {e : Semiformula V L₁ 2} (hd : d.shift = d)
    (he : e.shift = e) : (preserveEqBody d e).shift = preserveEqBody d e := by
  simp [preserveEqBody, Semiformula.shift_substs, hd, he]

end typed

/-! ## Tables of translations -/

section translationTable

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {tbl : V}

variable (L₂) in
/-- `tbl` is a table of a translation of `L₂` in `S`: its entries are formulas of the right
arities without free variables, and `S` proves that the domain formula is nonempty, that the
graph of each function symbol defines a unique value on the domain and respects equality, and
that the formula interpreting equality agrees with equality on the domain. -/
structure IsTranslationTable (S : Theory L₁) [S.Δ₁] (tbl : V) : Prop extends IsTable L₁ L₂ tbl where
  exs_domain : Provable S (^∃ tableDomain tbl)
  func_exists {k f : V} : L₂.IsFunc k f → Provable S (qqAlls (funcExistsCode L₁ tbl k f) k)
  func_unique {k f : V} : L₂.IsFunc k f → Provable S (qqAlls (funcUniqueCode L₁ tbl k f) (k + 2))
  func_congr {k f : V} : L₂.IsFunc k f →
    Provable S (qqAlls (funcCongrCode L₁ tbl k f) (k + 1 + (k + 1)))
  preserve_eq : Provable S (qqAlls (preserveEqCode L₁ L₂ tbl) 2)

section

variable {L : Language} [L.Encodable] [L.LORDefinable] {S : Theory L} [S.Δ₁]

lemma tprovable_subst_of_provable_qqAlls :
    ∀ {n : ℕ} (φ : Semiformula V L n) (w : SemitermVec V L n 0),
      Provable S (qqAlls φ.val n) → S.internalize V ⊢ φ.subst w
  | 0, φ, w, h => by
    rw [Semiformula.subst_nil_eq_self]
    exact tprovable_iff_provable.mpr (by simpa using h)
  | n + 1, φ, w, h => by
    have h₁ := tprovable_subst_of_provable_qqAlls (∀¹ φ) (Matrix.vecTail w)
      (by simpa [qqAlls_all] using h)
    rw [Semiformula.substs_all] at h₁
    have h₂ := TProof.specialize! h₁ (w 0)
    rwa [Semiformula.substs_q_substs_single,
      show (w 0 :> Matrix.vecTail w) = w from Matrix.cons_head_tail w] at h₂

lemma provable_qqAlls_of_forall_tprovable : ∀ {n : ℕ} (φ : Semiformula V L n), φ.shift = φ →
    (∀ w : SemitermVec V L n 0, S.internalize V ⊢ φ.subst w) → Provable S (qqAlls φ.val n)
  | 0, φ, _, h => by
    have h₁ := h ![]
    rw [Semiformula.subst_nil_eq_self] at h₁
    simpa using tprovable_iff_provable.mp h₁
  | n + 1, φ, hφ, h => by
    have h₁ := provable_qqAlls_of_forall_tprovable (∀¹ φ) (by rw [Semiformula.shift_all, hφ])
      fun w ↦ by
        rw [Semiformula.substs_all]
        apply TProof.all!
        simp only [Semiformula.free, Semiformula.shift_substs, hφ, Semiformula.substs_substs]
        exact h _
    simpa [qqAlls_all] using h₁

end

namespace IsTranslationTable

variable {S : Theory L₁} [S.Δ₁] (h : IsTranslationTable L₂ S tbl) {k : ℕ}

include h

lemma tprovable_func_exists (F : L₂.Func k) (w : Fin k → Term V L₁) :
    S.internalize V ⊢ Matrix.conj (fun i ↦ h.domT.subst ![w i]) 🡒
      ∃¹ (h.domT ⋏ (h.funcT F).subst (Semiterm.bvar 0 :> fun i ↦ (w i).bShift)) := by
  have h₁ := tprovable_subst_of_provable_qqAlls (S := S) (funcExistsBody h.domT (h.funcT F)) w
    (by rw [funcExistsBody_val _ rfl _ rfl]; exact h.func_exists (codeIn_func_quote F))
  simpa [funcExistsBody, SemitermVec.q_eq_cons] using h₁

lemma tprovable_func_unique (F : L₂.Func k) (y z : Term V L₁) (w : Fin k → Term V L₁) :
    S.internalize V ⊢ Matrix.conj (fun i ↦ h.domT.subst ![w i]) ⋏ h.domT.subst ![y] ⋏
      h.domT.subst ![z] ⋏ (h.funcT F).subst (y :> w) ⋏ (h.funcT F).subst (z :> w) 🡒
        Semiformula.equal y z := by
  have h₁ := tprovable_subst_of_provable_qqAlls (S := S) (funcUniqueBody h.domT (h.funcT F))
    (y :> z :> w)
    (by
      rw [funcUniqueBody_val _ rfl _ rfl]
      simpa [add_assoc, one_add_one_eq_two] using h.func_unique (codeIn_func_quote F))
  simpa [funcUniqueBody] using h₁

lemma tprovable_func_congr (F : L₂.Func k) (y z : Term V L₁) (w w' : Fin k → Term V L₁) :
    S.internalize V ⊢ Semiformula.equal y z ⋏
      Matrix.conj (fun i ↦ Semiformula.equal (w i) (w' i)) 🡒
        (h.funcT F).subst (y :> w) 🡒 (h.funcT F).subst (z :> w') := by
  have h₁ := tprovable_subst_of_provable_qqAlls (S := S) (funcCongrBody (h.funcT F))
    (Fin.append (y :> w) (z :> w'))
    (by
      rw [funcCongrBody_val _ rfl]
      simpa using h.func_congr (codeIn_func_quote F))
  simpa [funcCongrBody, Matrix.conj, Matrix.vecTail, Function.comp_def, Fin.append_addNat] using h₁

lemma tprovable_preserve_eq (y z : Term V L₁) :
    S.internalize V ⊢ h.domT.subst ![y] 🡒 h.domT.subst ![z] 🡒
      ((h.relT (Language.Eq.eq : L₂.Rel 2)).subst ![y, z] 🡘 Semiformula.equal y z) := by
  have h₁ := tprovable_subst_of_provable_qqAlls (S := S)
    (preserveEqBody h.domT (h.relT (Language.Eq.eq : L₂.Rel 2))) ![z, y]
    (by rw [preserveEqBody_val _ rfl _ rfl]; simpa using h.preserve_eq)
  simp only [preserveEqBody, LogicalConnective.iff, Semiformula.substs_imp,
    Semiformula.substs_and, Semiformula.substs_substs, Semiformula.substs_equal] at h₁
  convert h₁ using 3 <;> simp [LogicalConnective.iff, Matrix.vecMap_cons']

end IsTranslationTable

/-! ## Tables of direct translations -/

section directTranslation

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S] (π : DirectTranslation S L₂) {k : ℕ}

omit [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq] in
lemma operator_bvar_eq_sentence (o : Semiformula.Operator L₁ 1) :
    (o.operator ![#0] : Semisentence L₁ 1) = o.sentence := by
  simp [Semiformula.Operator.operator, Rewriting.emb]


omit [L₁.Eq] in
lemma quote_operator_bvar {m n : ℕ} (o : Semiformula.Operator L₁ m) (f : Fin m → Fin n) :
    (⌜(o.operator (fun i ↦ #(f i)) : Semisentence L₁ n)⌝ : Semiformula V L₁ n) =
      (⌜o.sentence⌝ : Semiformula V L₁ m).subst (fun i ↦ Semiterm.bvar (f i)) := by
  rw [Sentence.typed_quote_def, Sentence.typed_quote_def]
  simp [Semiformula.Operator.operator, Rewriting.emb]

omit [L₁.Eq] in
lemma quote_operator_cons {m n : ℕ} (o : Semiformula.Operator L₁ (m + 1)) (a : Fin n)
    (f : Fin m → Fin n) :
    (⌜(o.operator (#a :> fun i ↦ #(f i)) : Semisentence L₁ n)⌝ : Semiformula V L₁ n) =
      (⌜o.sentence⌝ : Semiformula V L₁ (m + 1)).subst
        (Semiterm.bvar a :> fun i ↦ Semiterm.bvar (f i)) := by
  have h : (#a :> fun i : Fin m ↦ (#(f i) : FirstOrder.Semiterm L₁ Empty n)) =
      fun j ↦ #((a :> f : Fin (m + 1) → Fin n) j) := by
    funext j
    cases j using Fin.cases <;> rfl
  rw [h, quote_operator_bvar]
  congr 1
  funext j
  cases j using Fin.cases <;> rfl

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma quote_domain_bvar {n : ℕ} (i : Fin n) :
    (⌜(π.domain.operator ![#i] : Semisentence L₁ n)⌝ : Semiformula V L₁ n) =
      (⌜π.domain.sentence⌝ : Semiformula V L₁ 1).subst ![Semiterm.bvar i] := by
  have h : (![#i] : Fin 1 → FirstOrder.Semiterm L₁ Empty n) = fun j ↦ #((fun _ ↦ i) j) := by
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl
  rw [h, quote_operator_bvar]
  congr 1
  funext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rfl

lemma quote_eq_bvar {n : ℕ} (i j : Fin n) :
    (⌜(op(=).operator ![#i, #j] : Semisentence L₁ n)⌝ : Semiformula V L₁ n) =
      Semiformula.equal (Semiterm.bvar i) (Semiterm.bvar j) := by
  rw [Sentence.typed_quote_def]
  simp only [Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.rew_rel_eq_comp, Rew.emb_eq_id, Semiformula.typed_quote_rel, Function.comp_apply,
    Rew.id_app, Rew.subst_bvar, Semiformula.equal]
  congr 1
  funext t
  match t with
  | 0 => rfl
  | 1 => rfl

noncomputable abbrev funcExistsSent (F : L₂.Func k) : Semisentence L₁ k :=
  (Matrix.conj fun i : Fin k ↦ π.domain.operator ![#i]) 🡒
    ∃¹ (π.domain.operator ![#0] ⋏ (π.func F).operator (#0 :> fun i ↦ #i.succ))

omit [L₁.Encodable] [L₁.LORDefinable] [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma funcExists_external (F : L₂.Func k) : S ⊢ ∀¹* (funcExistsSent π F) := by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ _ _ hT
  have h := (DirectTranslation.models_funcDefined_iff _ _).mp
    (models_of_provable hT (π.func_defined F))
  simpa [models_iff, funcExistsSent, Function.comp_def, Matrix.constant_eq_singleton] using
    fun e' hD ↦ (h e' hD).exists

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma quote_funcExistsSent (F : L₂.Func k) :
    (⌜funcExistsSent π F⌝ : Semiformula V L₁ k) =
      funcExistsBody ⌜π.domain.sentence⌝ (⌜(π.func F).sentence⌝ : Semiformula V L₁ (k + 1)) := by
  unfold funcExistsBody
  simp only [funcExistsSent, LCWQIsoGödelQuote.imply, LCWQIsoGödelQuote.exs,
    LCWQIsoGödelQuote.and, quote_conj, quote_domain_bvar, quote_operator_cons]

noncomputable abbrev uniqSent (F : L₂.Func k) : Semisentence L₁ (k + 2) :=
  (Matrix.conj (fun i : Fin k ↦ π.domain.operator ![#i.succ.succ]) ⋏ π.domain.operator ![#0] ⋏
    π.domain.operator ![#1] ⋏ (π.func F).operator (#0 :> fun i ↦ #i.succ.succ) ⋏
    (π.func F).operator (#1 :> fun i ↦ #i.succ.succ)) 🡒 op(=).operator ![#0, #1]

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma quote_uniqSent (F : L₂.Func k) :
    (⌜uniqSent π F⌝ : Semiformula V L₁ (k + 2)) =
      funcUniqueBody ⌜π.domain.sentence⌝ (⌜(π.func F).sentence⌝ : Semiformula V L₁ (k + 1)) := by
  unfold funcUniqueBody
  simp only [uniqSent, LCWQIsoGödelQuote.imply, LCWQIsoGödelQuote.and, quote_conj,
    quote_domain_bvar, quote_operator_cons, quote_eq_bvar]

omit [L₁.Encodable] [L₁.LORDefinable] [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma uniqSent_external (F : L₂.Func k) : S ⊢ ∀¹* (uniqSent π F) := by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ _ _ hT
  have h := (DirectTranslation.models_funcDefined_iff _ _).mp
    (models_of_provable hT (π.func_defined F))
  have key (e' : Fin (k + 2) → M) (a : Fin (k + 2)) :
      (FirstOrder.Semiterm.val (L := L₁) (M := M) e' Empty.elim ∘
        (#a :> fun i : Fin k ↦ #i.succ.succ) : Fin (k + 1) → M) =
          (e' a :> fun i ↦ e' i.succ.succ) := by
    funext j
    cases j using Fin.cases <;> simp
  suffices H : ∀ e' : Fin (k + 2) → M, (∀ i : Fin k, π.domain.val ![e' i.succ.succ]) →
      π.domain.val ![e' 0] → π.domain.val ![e' 1] →
      (π.func F).val (e' 0 :> fun i ↦ e' i.succ.succ) →
      (π.func F).val (e' 1 :> fun i ↦ e' i.succ.succ) → e' 0 = e' 1 by
    simpa [models_iff, uniqSent, key] using H
  intro e' hW hD0 hD1 hG0 hG1
  obtain ⟨x, -, hu⟩ := h (fun i ↦ e' i.succ.succ) hW
  exact (hu _ ⟨hD0, hG0⟩).trans (hu _ ⟨hD1, hG1⟩).symm

noncomputable abbrev congrSent (F : L₂.Func k) : Semisentence L₁ ((k + 1) + (k + 1)) :=
  (op(=).operator ![#(Fin.castAdd (k + 1) 0), #(Fin.natAdd (k + 1) 0)] ⋏
    Matrix.conj (fun i : Fin k ↦
      op(=).operator ![#(Fin.castAdd (k + 1) i.succ), #(Fin.natAdd (k + 1) i.succ)])) 🡒
    ((π.func F).operator (fun j ↦ #(Fin.castAdd (k + 1) j)) 🡒
      (π.func F).operator (fun j ↦ #(Fin.natAdd (k + 1) j)))

omit [L₁.Encodable] [L₁.LORDefinable] [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma congrSent_external (F : L₂.Func k) : S ⊢ ∀¹* (congrSent π F) := by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ _ _ hT
  simp only [congrSent, Fin.natAdd_eq_addNat, models_iff, Semiformula.eval_allClosure,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_operator, Matrix.comp₂, Nat.succ_eq_add_one, Nat.reduceAdd,
    Semiterm.val_bvar, Tarski.Structure.eq_iff_eq, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one, Matrix.conj_hom_prop,
    LogicalConnective.Prop.and_eq, LogicalConnective.Prop.arrow_eq, and_imp]
  intro e' h0 hconj hG
  have hv : (fun j : Fin (k + 1) ↦ e' (j.addNat (k + 1))) =
      (fun j ↦ e' (Fin.castAdd (k + 1) j)) := by
    funext j
    cases j using Fin.cases with
    | zero => exact h0.symm
    | succ i => exact (hconj i).symm
  simpa [Function.comp_def, hv] using hG

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma quote_congrSent (F : L₂.Func k) :
    (⌜congrSent π F⌝ : Semiformula V L₁ ((k + 1) + (k + 1))) =
      funcCongrBody (⌜(π.func F).sentence⌝ : Semiformula V L₁ (k + 1)) := by
  unfold funcCongrBody
  simp only [congrSent, LCWQIsoGödelQuote.imply, LCWQIsoGödelQuote.and, quote_conj,
    quote_eq_bvar, quote_operator_bvar]
  rfl

noncomputable abbrev preserveEqSent : Semisentence L₁ 2 :=
  π.domain.operator ![#1] 🡒 π.domain.operator ![#0] 🡒
    ((π.rel Language.Eq.eq).operator ![#1, #0] 🡘 op(=).operator ![#1, #0])

omit [L₁.Encodable] [L₁.LORDefinable] [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma preserveEq_external : S ⊢ ∀¹* (preserveEqSent π) := by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ _ _ hT
  have h : ∀ x y : M, π.domain.val ![x] → π.domain.val ![y] →
      ((π.rel Language.Eq.eq).val ![x, y] ↔ x = y) := by
    simpa [models_iff, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      models_of_provable hT π.preserve_eq
  simpa [models_iff, preserveEqSent, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
    fun e' : Fin 2 → M ↦ h (e' 1) (e' 0)

omit [L₂.Encodable] [L₂.LORDefinable] [S.Δ₁] in
lemma quote_preserveEqSent :
    (⌜preserveEqSent π⌝ : Semiformula V L₁ 2) =
      preserveEqBody ⌜π.domain.sentence⌝
        (⌜(π.rel Language.Eq.eq).sentence⌝ : Semiformula V L₁ 2) := by
  have h : (![#1, #0] : Fin 2 → FirstOrder.Semiterm L₁ Empty 2) =
      fun i ↦ #((![1, 0] : Fin 2 → Fin 2) i) := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
  have h' : (![Semiterm.bvar 1, Semiterm.bvar 0] : Fin 2 → Semiterm V L₁ 2) =
      fun i ↦ Semiterm.bvar ((![1, 0] : Fin 2 → Fin 2) i) := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
  unfold preserveEqBody
  simp only [preserveEqSent, LCWQIsoGödelQuote.imply, LCWQIsoGödelQuote.iff, quote_domain_bvar,
    quote_eq_bvar]
  rw [h, quote_operator_bvar, h']

omit [L₁.LORDefinable] [L₁.Eq] in
lemma quote_allClosure_semisentence {L : Language} [L.Encodable] [L.LORDefinable] {m : ℕ}
    (θ : Semisentence L m) : (⌜∀¹* θ⌝ : V) = qqAlls (⌜θ⌝ : V) (m : V) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show (∀¹* θ : Sentence L) = ∀¹* (∀¹ θ) from rfl]
    simpa [Sentence.quote_all, qqAlls_all] using ih (∀¹ θ)

variable {π} in
/-- A table of a direct translation `π` is a table of a translation. -/
theorem IsTableOf.isTranslationTable (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) :
    IsTranslationTable L₂ S tbl where
  toIsTable := h.isTable hL₂
  exs_domain := by
    have h₁ := internalize_provability (V := V) π.domain_nonempty
    rw [Sentence.quote_ex, operator_bvar_eq_sentence] at h₁
    rw [h.domain]
    exact h₁
  func_exists hf := by
    obtain ⟨k, F, rfl, rfl⟩ := hL₂.2 _ _ hf
    have hd : (h.isTable hL₂).domT = ⌜π.domain.sentence⌝ := Semiformula.ext h.domain
    have hg : (h.isTable hL₂).funcT F = ⌜(π.func F).sentence⌝ := Semiformula.ext (h.func F)
    rw [← funcExistsBody_val (h.isTable hL₂).domT rfl ((h.isTable hL₂).funcT F) rfl, hd, hg,
      ← quote_funcExistsSent]
    have h₁ := internalize_provability (V := V) (funcExists_external π F)
    rwa [quote_allClosure_semisentence] at h₁
  func_unique hf := by
    obtain ⟨k, F, rfl, rfl⟩ := hL₂.2 _ _ hf
    have hd : (h.isTable hL₂).domT = ⌜π.domain.sentence⌝ := Semiformula.ext h.domain
    have hg : (h.isTable hL₂).funcT F = ⌜(π.func F).sentence⌝ := Semiformula.ext (h.func F)
    rw [← funcUniqueBody_val (h.isTable hL₂).domT rfl ((h.isTable hL₂).funcT F) rfl, hd, hg,
      ← quote_uniqSent]
    have h₁ := internalize_provability (V := V) (uniqSent_external π F)
    rw [quote_allClosure_semisentence, Nat.cast_add, Nat.cast_ofNat] at h₁
    exact h₁
  func_congr hf := by
    obtain ⟨k, F, rfl, rfl⟩ := hL₂.2 _ _ hf
    have hg : (h.isTable hL₂).funcT F = ⌜(π.func F).sentence⌝ := Semiformula.ext (h.func F)
    rw [← funcCongrBody_val ((h.isTable hL₂).funcT F) rfl, hg, ← quote_congrSent]
    have h₁ := internalize_provability (V := V) (congrSent_external π F)
    rw [quote_allClosure_semisentence, Nat.cast_add, Nat.cast_succ] at h₁
    exact h₁
  preserve_eq := by
    have hd : (h.isTable hL₂).domT = ⌜π.domain.sentence⌝ := Semiformula.ext h.domain
    have he : (h.isTable hL₂).relT (Language.Eq.eq : L₂.Rel 2) =
        ⌜(π.rel Language.Eq.eq).sentence⌝ := Semiformula.ext (h.rel _)
    rw [← preserveEqBody_val (h.isTable hL₂).domT rfl
      ((h.isTable hL₂).relT (Language.Eq.eq : L₂.Rel 2)) rfl, hd, he, ← quote_preserveEqSent]
    have h₁ := internalize_provability (V := V) (preserveEq_external π)
    rwa [quote_allClosure_semisentence] at h₁

end directTranslation

end translationTable

end Bootstrapping
end FFL.FirstOrder.Arithmetic
