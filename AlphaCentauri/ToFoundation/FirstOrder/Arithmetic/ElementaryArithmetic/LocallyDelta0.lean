module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.Bit

/-!
# Relations that are $\Delta_0$ below every bound

A relation `R` on a model of $\mathsf{PA}^-$ is *locally* $\Delta_0$ if, for every bound `X`, it
agrees on the arguments below `X` with a $\Delta_0$ relation with parameters. A function is
locally $\Delta_0$ if its graph is, and it is bounded on every bounded set of arguments. In models
of $\mathsf{EA}$ the functions defined by bounded recursion, such as those of the coded syntax,
have this form although their graphs are not $\Delta_0$, and $\Delta_0$ induction and
comprehension extend to locally $\Delta_0$ predicates. This replaces, for $\mathsf{EA}$, the use
of $\Sigma_1$ definability in $\mathsf{I}\Sigma_1$.

- [HP98, §V.3]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open Bounding

variable {V : Type*} [ORingStructure V] {k l : ℕ}

/-- `R` agrees, on the arguments below any given bound, with a $\Delta_0$ relation with
parameters. -/
def LocallyDelta0 (R : (Fin k → V) → Prop) : Prop :=
  ∀ X : V, ∃ Q : (Fin k → V) → Prop, 𝚺ᴬ₀.Definable Q ∧ ∀ v, (∀ i, v i ≤ X) → (R v ↔ Q v)

abbrev LocallyDelta0Pred (P : V → Prop) : Prop := LocallyDelta0 (k := 1) fun v ↦ P (v 0)

abbrev LocallyDelta0Rel (R : V → V → Prop) : Prop := LocallyDelta0 (k := 2) fun v ↦ R (v 0) (v 1)

/-- `f` has a locally $\Delta_0$ graph and is bounded on every bounded set of arguments. -/
structure LocallyDelta0Function (f : (Fin k → V) → V) : Prop where
  graph : LocallyDelta0 (k := k + 1) fun v ↦ v 0 = f (v ·.succ)
  bounded : ∀ X : V, ∃ Y, ∀ v, (∀ i, v i ≤ X) → f v ≤ Y

abbrev LocallyDelta0Function₁ (f : V → V) : Prop := LocallyDelta0Function (k := 1) fun v ↦ f (v 0)

abbrev LocallyDelta0Function₂ (f : V → V → V) : Prop :=
  LocallyDelta0Function (k := 2) fun v ↦ f (v 0) (v 1)

namespace LocallyDelta0

variable {R R' : (Fin k → V) → Prop}

lemma of_definable (h : 𝚺ᴬ₀.Definable R) : LocallyDelta0 R := by
  intro _
  use R
  exact ⟨h, fun _ _ ↦ Iff.rfl⟩

lemma of_iff (h : LocallyDelta0 R) (e : ∀ v, R' v ↔ R v) : LocallyDelta0 R' := by
  intro X
  obtain ⟨Q, hQ, hRQ⟩ := h X
  use Q
  exact ⟨hQ, fun v hv ↦ (e v).trans (hRQ v hv)⟩

lemma and (h : LocallyDelta0 R) (h' : LocallyDelta0 R') : LocallyDelta0 fun v ↦ R v ∧ R' v := by
  intro X
  obtain ⟨Q, hQ, hRQ⟩ := h X
  obtain ⟨Q', hQ', hRQ'⟩ := h' X
  use fun v ↦ Q v ∧ Q' v
  exact ⟨hQ.and hQ', fun v hv ↦ and_congr (hRQ v hv) (hRQ' v hv)⟩

lemma or (h : LocallyDelta0 R) (h' : LocallyDelta0 R') : LocallyDelta0 fun v ↦ R v ∨ R' v := by
  intro X
  obtain ⟨Q, hQ, hRQ⟩ := h X
  obtain ⟨Q', hQ', hRQ'⟩ := h' X
  use fun v ↦ Q v ∨ Q' v
  exact ⟨hQ.or hQ', fun v hv ↦ or_congr (hRQ v hv) (hRQ' v hv)⟩

lemma not (h : LocallyDelta0 R) : LocallyDelta0 fun v ↦ ¬R v := by
  intro X
  obtain ⟨Q, hQ, hRQ⟩ := h X
  use fun v ↦ ¬Q v
  exact ⟨hQ.notSigma.of_zero, fun v hv ↦ not_congr (hRQ v hv)⟩

lemma imp (h : LocallyDelta0 R) (h' : LocallyDelta0 R') : LocallyDelta0 fun v ↦ R v → R' v :=
  (h.not.or h').of_iff fun _ ↦ imp_iff_not_or

lemma iff (h : LocallyDelta0 R) (h' : LocallyDelta0 R') : LocallyDelta0 fun v ↦ R v ↔ R' v :=
  ((h.imp h').and (h'.imp h)).of_iff fun _ ↦ iff_iff_implies_and_implies

lemma retraction {R : (Fin l → V) → Prop} (h : LocallyDelta0 R) (σ : Fin l → Fin k) :
    LocallyDelta0 fun v : Fin k → V ↦ R fun i ↦ v (σ i) := by
  intro X
  obtain ⟨Q, hQ, hRQ⟩ := h X
  use fun v ↦ Q fun i ↦ v (σ i)
  exact ⟨hQ.retraction σ, fun v hv ↦ hRQ _ fun i ↦ hv (σ i)⟩

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- Substitution of locally $\Delta_0$ functions into a locally $\Delta_0$ relation. -/
lemma comp {R : (Fin l → V) → Prop} {f : Fin l → (Fin k → V) → V} (h : LocallyDelta0 R)
    (hf : ∀ i, LocallyDelta0Function (f i)) :
    LocallyDelta0 fun v ↦ R fun i ↦ f i v := by
  intro X
  choose Y hY using fun i ↦ (hf i).bounded X
  set Z : V := ∑ i, Y i
  have hYZ (i : Fin l) : Y i ≤ Z := Finset.single_le_sum (fun j _ ↦ by simp) (by simp)
  obtain ⟨Q, hQ, hRQ⟩ := h Z
  choose G hG hfG using fun i ↦ (hf i).graph (X + Z)
  use fun v ↦ ∃ w ≤ (fun _ : Fin l ↦ Z), (∀ i, G i (w i :> v)) ∧ Q w
  constructor
  · apply HierarchySymbol.Definable.arithmetic_bexs_vec_le_boundedFunction
      (fun _ ↦ by simp)
    apply HierarchySymbol.Definable.and
    · apply HierarchySymbol.Definable.fintype_all
      intro i
      exact ((hG i).retraction (Fin.natAdd k i :> fun j ↦ Fin.castAdd l j)).of_iff fun w ↦
        iff_of_eq <| congrArg (G i) <| funext fun j ↦ by cases j using Fin.cases <;> simp
    · simpa using hQ.retraction fun j ↦ Fin.natAdd k j
  · intro v hv
    have hgraph (i : Fin l) (y : V) (hy : y ≤ Z) : y = f i v ↔ G i (y :> v) := by
      refine Iff.trans (by simp) (hfG i (y :> v) ?_)
      intro j
      cases j using Fin.cases with
      | zero => simpa using le_trans hy le_add_self
      | succ j => simpa using le_trans (hv j) le_self_add
    constructor
    · intro hR
      use fun i ↦ f i v
      and_intros
      · intro i; exact le_trans (hY i v hv) (hYZ i)
      · intro i; exact (hgraph i _ (le_trans (hY i v hv) (hYZ i))).mp rfl
      · exact (hRQ _ fun i ↦ le_trans (hY i v hv) (hYZ i)).mp hR
    · rintro ⟨w, hw, hwG, hwQ⟩
      have : w = fun i ↦ f i v := funext fun i ↦ (hgraph i (w i) (hw i)).mpr (hwG i)
      subst this
      exact (hRQ _ hw).mpr hwQ

/-- Bounded universal quantification below a variable. -/
lemma ball_le {P : (Fin (k + 1) → V) → Prop} (h : LocallyDelta0 P) :
    LocallyDelta0 fun v : Fin (k + 1) → V ↦ ∀ x ≤ v 0, P (x :> fun i ↦ v i.succ) := by
  intro X
  obtain ⟨Q, hQ, hPQ⟩ := h X
  use fun v ↦ ∀ x ≤ v 0, Q (x :> fun i ↦ v i.succ)
  constructor
  · apply HierarchySymbol.Definable.arithmetic_ball_ble
      (DefinableBoundedFunction.var 0)
    exact (hQ.retraction (0 :> fun i ↦ i.succ.succ)).of_iff fun w ↦ iff_of_eq <| congrArg Q <|
      funext fun i ↦ by cases i using Fin.cases <;> simp
  · intro v hv
    apply forall₂_congr
    intro x hx
    apply hPQ
    intro i
    cases i using Fin.cases with
    | zero => simpa using le_trans hx (hv 0)
    | succ i => simpa using hv i.succ

/-- Bounded existential quantification below a variable. -/
lemma bexs_le {P : (Fin (k + 1) → V) → Prop} (h : LocallyDelta0 P) :
    LocallyDelta0 fun v : Fin (k + 1) → V ↦ ∃ x ≤ v 0, P (x :> fun i ↦ v i.succ) :=
  (ball_le h.not).not.of_iff fun _ ↦ by simp

end LocallyDelta0

namespace LocallyDelta0Function

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

lemma of_definableBoundedFunction {f : (Fin k → V) → V}
    (hf : Arithmetic.DefinableBoundedFunction f) : LocallyDelta0Function f where
  graph := LocallyDelta0.of_definable hf.2
  bounded X := by
    obtain ⟨t, ht⟩ := hf.1.bounded
    use t.val (fun _ ↦ X) id
    intro v hv
    exact le_trans (ht v) (Tarski.Structure.Monotone.term_monotone t hv fun _ ↦ le_rfl)

lemma var (i : Fin k) : LocallyDelta0Function fun v : Fin k → V ↦ v i :=
  of_definableBoundedFunction (DefinableBoundedFunction.var i)

lemma const (c : V) : LocallyDelta0Function fun _ : Fin k → V ↦ c :=
  of_definableBoundedFunction (DefinableBoundedFunction.const c)

omit [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] in
lemma retraction {f : (Fin l → V) → V} (hf : LocallyDelta0Function f) (σ : Fin l → Fin k) :
    LocallyDelta0Function fun v : Fin k → V ↦ f fun i ↦ v (σ i) where
  graph := (hf.graph.retraction (0 :> fun i ↦ (σ i).succ)).of_iff fun v ↦ by simp
  bounded X := by
    obtain ⟨Y, hY⟩ := hf.bounded X
    use Y
    intro v hv
    exact hY _ fun i ↦ hv (σ i)

lemma comp {g : (Fin l → V) → V} {f : Fin l → (Fin k → V) → V} (hg : LocallyDelta0Function g)
    (hf : ∀ i, LocallyDelta0Function (f i)) : LocallyDelta0Function fun v ↦ g fun i ↦ f i v where
  graph := by
    have := LocallyDelta0.comp (k := k + 1) hg.graph
      (f := (fun v ↦ v 0) :> fun i v ↦ f i (v ·.succ)) fun i ↦ by
        cases i using Fin.cases with
        | zero => simpa using var 0
        | succ i =>
          simpa using (hf i).retraction Fin.succ
    exact this.of_iff fun v ↦ by simp
  bounded X := by
    choose Y hY using fun i ↦ (hf i).bounded X
    obtain ⟨Z, hZ⟩ := hg.bounded (∑ i, Y i)
    use Z
    intro v hv
    exact hZ _ fun i ↦ le_trans (hY i v hv)
      (Finset.single_le_sum (fun j _ ↦ by simp) (by simp))

lemma comp₁ {g : V → V} {f : (Fin k → V) → V} (hg : LocallyDelta0Function₁ g)
    (hf : LocallyDelta0Function f) : LocallyDelta0Function fun v ↦ g (f v) :=
  hg.comp (f := fun _ ↦ f) fun _ ↦ hf

lemma comp₂ {g : V → V → V} {f f' : (Fin k → V) → V} (hg : LocallyDelta0Function₂ g)
    (hf : LocallyDelta0Function f) (hf' : LocallyDelta0Function f') :
    LocallyDelta0Function fun v ↦ g (f v) (f' v) :=
  hg.comp (f := ![f, f']) <|
    Fin.forall_fin_succ.mpr ⟨hf, Fin.forall_fin_succ.mpr ⟨hf', finZeroElim⟩⟩

lemma comp₃ {g : V → V → V → V} {f f' f'' : (Fin k → V) → V}
    (hg : LocallyDelta0Function (k := 3) fun v ↦ g (v 0) (v 1) (v 2))
    (hf : LocallyDelta0Function f) (hf' : LocallyDelta0Function f')
    (hf'' : LocallyDelta0Function f'') : LocallyDelta0Function fun v ↦ g (f v) (f' v) (f'' v) :=
  hg.comp (f := ![f, f', f'']) <| Fin.forall_fin_succ.mpr ⟨hf, Fin.forall_fin_succ.mpr
    ⟨hf', Fin.forall_fin_succ.mpr ⟨hf'', finZeroElim⟩⟩⟩

/-- Substitution of locally $\Delta_0$ functions for the variables of a locally $\Delta_0$
function, one of them for the first variable. -/
lemma comp_cons {g : (Fin (l + 1) → V) → V} {f : (Fin k → V) → V}
    {u : Fin l → (Fin k → V) → V} (hg : LocallyDelta0Function g) (hf : LocallyDelta0Function f)
    (hu : ∀ j, LocallyDelta0Function (u j)) :
    LocallyDelta0Function fun v ↦ g (f v :> fun j ↦ u j v) := by
  have := hg.comp (f := f :> u) fun i ↦ by
    cases i using Fin.cases with
    | zero => simpa using hf
    | succ j => simpa using hu j
  convert this using 3 with v
  ext i
  cases i using Fin.cases <;> simp

lemma add : LocallyDelta0Function₂ (· + · : V → V → V) :=
  of_definableBoundedFunction ⟨inferInstance, by definability⟩

lemma mul : LocallyDelta0Function₂ (· * · : V → V → V) :=
  of_definableBoundedFunction ⟨inferInstance, by definability⟩

lemma add_one {f : (Fin k → V) → V} (hf : LocallyDelta0Function f) :
    LocallyDelta0Function fun v ↦ f v + 1 :=
  add.comp₂ hf (const 1)

end LocallyDelta0Function

namespace LocallyDelta0

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {P : (Fin (k + 1) → V) → Prop} {f : (Fin k → V) → V}

lemma comp₂ {R : (Fin 2 → V) → Prop} {f f' : (Fin k → V) → V} (h : LocallyDelta0 R)
    (hf : LocallyDelta0Function f) (hf' : LocallyDelta0Function f') :
    LocallyDelta0 fun v ↦ R ![f v, f' v] :=
  (h.comp (f := ![f, f'])
    (Fin.forall_fin_succ.mpr ⟨hf, Fin.forall_fin_succ.mpr ⟨hf', finZeroElim⟩⟩)).of_iff
    fun _ ↦ iff_of_eq <| congrArg R <|
      funext (Fin.cases rfl (Fin.cases rfl finZeroElim))

lemma comp₃ {R : (Fin 3 → V) → Prop} {f f' f'' : (Fin k → V) → V} (h : LocallyDelta0 R)
    (hf : LocallyDelta0Function f) (hf' : LocallyDelta0Function f')
    (hf'' : LocallyDelta0Function f'') : LocallyDelta0 fun v ↦ R ![f v, f' v, f'' v] :=
  (h.comp (f := ![f, f', f''])
    (Fin.forall_fin_succ.mpr ⟨hf, Fin.forall_fin_succ.mpr
      ⟨hf', Fin.forall_fin_succ.mpr ⟨hf'', finZeroElim⟩⟩⟩)).of_iff
    fun _ ↦ iff_of_eq <| congrArg R <|
      funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl finZeroElim)))

lemma pred_comp {P : V → Prop} (h : LocallyDelta0Pred P) (hf : LocallyDelta0Function f) :
    LocallyDelta0 fun v ↦ P (f v) :=
  (h.comp (f := fun _ ↦ f) fun _ ↦ hf).of_iff fun _ ↦ Iff.rfl

lemma rel_comp₂ {R : V → V → Prop} {f f' : (Fin k → V) → V} (h : LocallyDelta0Rel R)
    (hf : LocallyDelta0Function f) (hf' : LocallyDelta0Function f') :
    LocallyDelta0 fun v ↦ R (f v) (f' v) :=
  (h.comp₂ hf hf').of_iff fun _ ↦ Iff.rfl

lemma eq {f' : (Fin k → V) → V} (hf : LocallyDelta0Function f) (hf' : LocallyDelta0Function f') :
    LocallyDelta0 fun v ↦ f v = f' v :=
  (of_definable (R := fun w : Fin 2 → V ↦ w 0 = w 1) (by definability)).comp₂ hf hf'

lemma le {f' : (Fin k → V) → V} (hf : LocallyDelta0Function f) (hf' : LocallyDelta0Function f') :
    LocallyDelta0 fun v ↦ f v ≤ f' v :=
  (of_definable (R := fun w : Fin 2 → V ↦ w 0 ≤ w 1) (by definability)).comp₂ hf hf'

lemma lt {f' : (Fin k → V) → V} (hf : LocallyDelta0Function f) (hf' : LocallyDelta0Function f') :
    LocallyDelta0 fun v ↦ f v < f' v :=
  (of_definable (R := fun w : Fin 2 → V ↦ w 0 < w 1) (by definability)).comp₂ hf hf'

/-- Substitution of locally $\Delta_0$ functions for the variables of a locally $\Delta_0$
relation, one of them for the first variable. -/
lemma comp_cons {R : (Fin (l + 1) → V) → Prop} {u : Fin l → (Fin k → V) → V}
    (h : LocallyDelta0 R) (hf : LocallyDelta0Function f)
    (hu : ∀ j, LocallyDelta0Function (u j)) : LocallyDelta0 fun v ↦ R (f v :> fun j ↦ u j v) :=
  (h.comp (f := f :> u) fun i ↦ by
    cases i using Fin.cases with
    | zero => simpa using hf
    | succ j => simpa using hu j).of_iff fun v ↦ iff_of_eq <| congrArg R <| funext fun i ↦ by
      cases i using Fin.cases <;> simp

/-- Substitution of locally $\Delta_0$ functions for the variables of a locally $\Delta_0$
relation, two of them for the first two variables. -/
lemma comp_cons₂ {R : (Fin (l + 2) → V) → Prop} {f' : (Fin k → V) → V}
    {u : Fin l → (Fin k → V) → V} (h : LocallyDelta0 R) (hf : LocallyDelta0Function f)
    (hf' : LocallyDelta0Function f') (hu : ∀ j, LocallyDelta0Function (u j)) :
    LocallyDelta0 fun v ↦ R (f v :> f' v :> fun j ↦ u j v) :=
  (h.comp (f := f :> f' :> u) fun i ↦ by
    cases i using Fin.cases with
    | zero => simpa using hf
    | succ j =>
      cases j using Fin.cases with
      | zero => simpa using hf'
      | succ j => simpa using hu j).of_iff fun v ↦ iff_of_eq <| congrArg R <| funext fun i ↦ by
        cases i using Fin.cases
        · simp
        · rename_i j
          cases j using Fin.cases <;> simp

/-- Bounded existential quantification below a locally $\Delta_0$ function. -/
lemma bexs_le_function (hf : LocallyDelta0Function f) (h : LocallyDelta0 P) :
    LocallyDelta0 fun v ↦ ∃ x ≤ f v, P (x :> v) := by
  have := (bexs_le h).comp (f := f :> fun i v ↦ v i) fun j ↦ by
    cases j using Fin.cases with
    | zero => simpa using hf
    | succ j => simpa using LocallyDelta0Function.var j
  apply this.of_iff
  intro v
  apply exists_congr
  intro x
  apply and_congr (by simp)
  apply iff_of_eq
  congr 1

/-- Bounded universal quantification below a locally $\Delta_0$ function. -/
lemma ball_le_function (hf : LocallyDelta0Function f) (h : LocallyDelta0 P) :
    LocallyDelta0 fun v ↦ ∀ x ≤ f v, P (x :> v) :=
  (bexs_le_function hf h.not).not.of_iff fun _ ↦ by simp

private lemma lt_function (hf : LocallyDelta0Function f) :
    LocallyDelta0 fun v : Fin (k + 1) → V ↦ v 0 < f (v ·.succ) :=
  ((LocallyDelta0.of_definable (R := fun w : Fin 2 → V ↦ w 0 < w 1) (by definability)).comp₂
    (LocallyDelta0Function.var 0) (hf.retraction Fin.succ)).of_iff fun v ↦ by simp

/-- Bounded existential quantification strictly below a locally $\Delta_0$ function. -/
lemma bexs_lt_function (hf : LocallyDelta0Function f) (h : LocallyDelta0 P) :
    LocallyDelta0 fun v ↦ ∃ x < f v, P (x :> v) :=
  (bexs_le_function hf ((lt_function hf).and h)).of_iff fun v ↦
    ⟨fun ⟨x, hx, hP⟩ ↦ ⟨x, hx.le, by simpa using hx, hP⟩,
      fun ⟨x, _, hx, hP⟩ ↦ ⟨x, by simpa using hx, hP⟩⟩

/-- Bounded universal quantification strictly below a locally $\Delta_0$ function. -/
lemma ball_lt_function (hf : LocallyDelta0Function f) (h : LocallyDelta0 P) :
    LocallyDelta0 fun v ↦ ∀ x < f v, P (x :> v) :=
  (bexs_lt_function hf h.not).not.of_iff fun _ ↦ by simp

end LocallyDelta0

/-- A case distinction on a locally $\Delta_0$ condition. -/
lemma LocallyDelta0Function.ite [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {Q : (Fin k → V) → Prop} [DecidablePred Q]
    {f g : (Fin k → V) → V} (hQ : LocallyDelta0 Q) (hf : LocallyDelta0Function f)
    (hg : LocallyDelta0Function g) : LocallyDelta0Function fun v ↦ if Q v then f v else g v where
  graph := by
    have hQ' : LocallyDelta0 fun w : Fin (k + 1) → V ↦ Q (w ·.succ) := hQ.retraction Fin.succ
    exact ((hQ'.and hf.graph).or (hQ'.not.and hg.graph)).of_iff fun w ↦ by
      by_cases h : Q (w ·.succ) <;> simp [h]
  bounded X := by
    obtain ⟨Y, hY⟩ := hf.bounded X
    obtain ⟨Z, hZ⟩ := hg.bounded X
    use Y + Z
    intro v hv
    by_cases h : Q v
    · simpa [h] using le_trans (hY v hv) le_self_add
    · simpa [h] using le_trans (hZ v hv) le_add_self

section exponential

variable [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

lemma LocallyDelta0Function.exp : LocallyDelta0Function₁ (Exp.exp : V → V) where
  graph := LocallyDelta0.of_definable exp_definable_deltaZero
  bounded X := by
    use Exp.exp X
    intro v hv
    exact exp_monotone_le.mpr (hv 0)

lemma LocallyDelta0Function.exp_exp_mul_add {f g : (Fin k → V) → V} (a : V)
    (hf : LocallyDelta0Function f) (hg : LocallyDelta0Function g) :
    LocallyDelta0Function fun v ↦ Exp.exp (Exp.exp (a * f v + g v)) :=
  exp.comp₁ <| exp.comp₁ <| add.comp₂ (mul.comp₂ (const a) hf) hg

end exponential

section induction

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {P : V → Prop}

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] in
private lemma exists_definable_of_le (hP : LocallyDelta0Pred P) (X : V) :
    ∃ Q : V → Prop, 𝚺ᴬ₀.DefinablePred Q ∧ ∀ x ≤ X, (P x ↔ Q x) := by
  obtain ⟨Q, hQ, hPQ⟩ := hP X
  use fun x ↦ Q ![x]
  constructor
  · exact (hQ.retraction (![0] : Fin 1 → Fin 1)).of_iff fun v ↦ iff_of_eq <| congrArg Q <|
      funext fun i ↦ by simp
  · intro x hx
    simpa [Matrix.constant_eq_singleton] using hPQ ![x] (by simpa using hx)

lemma LocallyDelta0Pred.succ_induction (hP : LocallyDelta0Pred P) (zero : P 0)
    (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  intro X
  obtain ⟨Q, hQ, hPQ⟩ := exists_definable_of_le hP X
  have : ∀ x, x ≤ X → Q x := by
    intro x
    induction x using ISigma0.succ_induction
    · definability
    case zero => intro _; exact (hPQ 0 (by simp)).mp zero
    case succ x ih =>
      intro hx
      have hx' : x ≤ X := le_trans le_self_add hx
      exact (hPQ _ hx).mp <| succ x <| (hPQ x hx').mpr <| ih hx'
  exact (hPQ X le_rfl).mpr (this X le_rfl)

lemma LocallyDelta0Pred.order_induction (hP : LocallyDelta0Pred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  intro X
  obtain ⟨Q, hQ, hPQ⟩ := exists_definable_of_le hP X
  have : ∀ x, x ≤ X → Q x := by
    intro x
    induction x using ISigma0.order_induction
    · definability
    case ind x ih =>
      intro hx
      apply (hPQ x hx).mp
      apply ind
      intro y hy
      exact (hPQ y (le_trans hy.le hx)).mpr <| ih y hy (le_trans hy.le hx)
  exact (hPQ X le_rfl).mpr (this X le_rfl)

lemma LocallyDelta0Pred.least_number (hP : LocallyDelta0Pred P) {x : V} (h : P x) :
    ∃ y, P y ∧ ∀ z < y, ¬P z := by
  by_contra A
  have : ∀ y, ¬P y := by
    apply LocallyDelta0Pred.order_induction (P := fun y ↦ ¬P y) hP.not
    intro y ih hy
    exact A ⟨y, hy, ih⟩
  exact this x h

end induction

section comprehension

variable [V↓[ℒₒᵣ] ⊧* 𝗘𝗔] {P : V → Prop}

/-- Comprehension for a locally $\Delta_0$ predicate on `{0, …, a - 1}`. -/
theorem LocallyDelta0Pred.finset_comprehension (hP : LocallyDelta0Pred P) (a : V) :
    ∃ s < Exp.exp a, ∀ i < a, i ∈ s ↔ P i := by
  obtain ⟨Q, hQ, hPQ⟩ := hP a
  obtain ⟨s, hs, Hs⟩ := ElementaryArithmetic.finset_comprehension (P := fun x ↦ Q ![x])
    ((hQ.retraction (![0] : Fin 1 → Fin 1)).of_iff fun v ↦ iff_of_eq <| congrArg Q <|
      funext fun i ↦ by simp) a
  use s
  exact ⟨hs, fun i hi ↦ (Hs i hi).trans <| by
    simpa [Matrix.constant_eq_singleton] using (hPQ ![i] (by simpa using hi.le)).symm⟩

theorem LocallyDelta0Pred.finite_comprehension! (hP : LocallyDelta0Pred P)
    (fin : ∃ m, ∀ i, P i → i < m) : ∃! s : V, ∀ i, i ∈ s ↔ P i := by
  obtain ⟨m, hm⟩ := fin
  obtain ⟨s, hs, Hs⟩ := hP.finset_comprehension m
  have H : ∀ i, i ∈ s ↔ P i := fun i ↦
    ⟨fun h ↦ (Hs i (exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem h) hs))).mp h,
      fun h ↦ (Hs i (hm i h)).mpr h⟩
  exact ExistsUnique.intro s H fun s' H' ↦ mem_ext fun i ↦ by simp [H, H']

end comprehension

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
