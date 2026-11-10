module

public import AlphaCentauri.Bootstrapping.Interpretability.Commutation
public import AlphaCentauri.Bootstrapping.Interpretability.DefinesElement
public import AlphaCentauri.Interpretability.Basic
public import AlphaCentauri.ToFoundation.InternalEquality
public import AlphaCentauri.ToFoundation.TypedProof

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

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

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

section

variable {Γ : SigmaPiDelta} {m : ℕ}

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

end

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
lemma nth_domainVec (tbl s k : V) : ∀ j < k, (domainVec L tbl s k).[j] = domainAt L tbl (s + j) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro j hj
    rcases (lt_succ_iff_le.mp hj).lt_or_eq with hlt | rfl
    · rw [domainVec_succ, concat_nth_lt _ _ (by simpa using hlt)]
      exact ih j hlt
    · rw [domainVec_succ, concat_nth_len' _ _ (by simp)]

@[simp] lemma len_equationVec (a b k : V) : len (equationVec L a b k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

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

section

variable {Γ : SigmaPiDelta} {m : ℕ}

instance funcExistsCode.definable : 𝚺ᴬ₁-Function₃[V] funcExistsCode L := by
  unfold funcExistsCode
  definability

instance funcUniqueCode.definable : 𝚺ᴬ₁-Function₃[V] funcUniqueCode L := by
  unfold funcUniqueCode
  definability

instance funcCongrCode.definable : 𝚺ᴬ₁-Function₃[V] funcCongrCode L := by
  unfold funcCongrCode
  definability

end

end codes

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

end IsTable

section bodies

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {k : ℕ}

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
noncomputable def funcCongrBody (g : Semiformula V L (k + 1)) : Semiformula V L ((k + 1) + (k + 1)) :=
  Matrix.conj (fun j : Fin (k + 1) ↦
      Semiformula.equal (Semiterm.bvar (Fin.castAdd (k + 1) j)) (Semiterm.bvar (Fin.natAdd (k + 1) j))) 🡒
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
      (Semiterm.bvar (g i)) : Semiformula V L n).val = ^⋀ equationVec L (a : V) (b : V) (k : V) := by
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

end bodies

end typed

end FFL.FirstOrder.Arithmetic.Bootstrapping
