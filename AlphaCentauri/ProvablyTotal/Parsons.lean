module

public import AlphaCentauri.Calculus.Induction.Forcing
public import AlphaCentauri.Calculus.Induction.Witnessing
public import AlphaCentauri.ProvablyTotal.Basic
public import AlphaCentauri.Schemata.StrictInduction
public import AlphaCentauri.ToFoundation.Primrec
public import AlphaCentauri.ToMathlib.Vector
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
public import Mathlib.Computability.Ackermann

/-!
# Parsons' theorem

The `𝗜𝚺₁`-provably total functions are exactly the primitive recursive functions, and the
Ackermann function is therefore not `𝗜𝚺₁`-provably total.

One direction is a construction inside a model: the graph of a primitive recursive function is
assembled by composition and primitive recursion, and `𝗜𝚺₁` proves it functional. For the other,
a function whose graph is a strict $\Sigma_1$ formula whose totality `𝗜 𝚺 1` proves is primitive
recursive: the proof of totality becomes an anchored derivation of the graph at the arguments as
free variables, witnessing reads a primitive recursive bound off that derivation, and the value
is recovered by a bounded search below the bound.

- [Bus98A, Theorem 3.1.1, Section 3.1.3]
- [HP98, Theorem I.1.54, Lemma I.1.55, Corollary IV.3.7]
-/

@[expose] public section

namespace FFL.FirstOrder

/-! ## The graphs of the primitive recursive functions -/

open Arithmetic HierarchySymbol

variable {k n : ℕ}

namespace Arithmetic

variable {V : Type*} [ORingStructure V]

private lemma definedFunction_zero :
    𝚺₁.DefinedFunction (fun _ : Fin 0 → V ↦ 0) (.mkSigma “y. y = 0”) := .mk fun _ ↦ by simp

private lemma definedFunction_succ :
    𝚺₁.DefinedFunction (fun v : Fin 1 → V ↦ v 0 + 1) (.mkSigma “y x. y = x + 1”) :=
  .mk fun _ ↦ by simp

private lemma definedFunction_get (i : Fin k) :
    𝚺₁.DefinedFunction (fun v : Fin k → V ↦ v i)
      ((.mkSigma “y x. y = x” : 𝚺₁.Semisentence 2).rew (Rew.subst ![#0, #i.succ])) :=
  .mk fun _ ↦ by simp

/-- The blueprint of the primitive recursion whose base and step are given by the graphs `ψ` and
`χ`, the arguments of `χ` being the recursion variable, the previous value, and the parameters.
- [HP98, Lemma I.1.55] -/
private def precBlueprint (ψ : 𝚺₁.Semisentence (n + 1)) (χ : 𝚺₁.Semisentence (n + 3)) :
    PR.Blueprint n where
  zero := ψ
  succ := χ.rew (Rew.subst (#0 :> #2 :> #1 :> (#·.succ.succ.succ)))

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {ψ : 𝚺₁.Semisentence (n + 1)} {χ : 𝚺₁.Semisentence (n + 3)}

/-- The primitive recursion built inside a model of `𝗜𝚺₁` from the functions defined by `ψ` and
`χ`.
- [HP98, Lemma I.1.55] -/
private def precConstruction {f : (Fin n → V) → V} {g : (Fin (n + 2) → V) → V}
    (hf : 𝚺₁.DefinedFunction f ψ) (hg : 𝚺₁.DefinedFunction g χ) :
    PR.Construction V (precBlueprint ψ χ) where
  zero := f
  succ := fun v i z ↦ g (i :> z :> v)
  zero_defined := hf
  succ_defined := .mk fun v ↦ by
    simp [precBlueprint, Semiformula.eval_rew, Empty.eq_elim, hg.iff, Matrix.comp_vecCons']

private lemma result_precConstruction {f : (Fin n → ℕ) → ℕ} {g : (Fin (n + 2) → ℕ) → ℕ}
    (hf : 𝚺₁.DefinedFunction (V := ℕ) f ψ) (hg : 𝚺₁.DefinedFunction (V := ℕ) g χ)
    (v : Fin n → ℕ) (u : ℕ) :
    (precConstruction hf hg).result v u = u.rec (f v) fun y ih ↦ g (y :> ih :> v) := by
  induction u with
  | zero => simp [precConstruction]
  | succ u ih => rw [PR.Construction.result_succ, ih]; rfl

end Arithmetic

namespace ArithmeticTheory.ProvablyFunctionalVia

variable {T : ArithmeticTheory}

section
variable {f g : (Fin k → ℕ) → ℕ} {φ : 𝚺₁.Semisentence (k + 1)}

private lemma of_eq (hf : T.ProvablyFunctionalVia f φ) (h : ∀ v, f v = g v) :
    T.ProvablyFunctionalVia g φ :=
  ⟨⟨DefinedFunction.of_eq h hf.defined, hf.total⟩, hf.functional⟩

end

section
variable [𝗘𝗤 ℒₒᵣ ⪯ T]

private lemma zero : T.ProvablyFunctionalVia (fun _ : Fin 0 → ℕ ↦ 0) (.mkSigma “y. y = 0”) :=
  of_models definedFunction_zero fun _ _ _ ↦ ⟨_, definedFunction_zero⟩

private lemma succ :
    T.ProvablyFunctionalVia (fun v : Fin 1 → ℕ ↦ v 0 + 1) (.mkSigma “y x. y = x + 1”) :=
  of_models definedFunction_succ fun _ _ _ ↦ ⟨_, definedFunction_succ⟩

private lemma get (i : Fin k) :
    T.ProvablyFunctionalVia (fun v : Fin k → ℕ ↦ v i)
      ((.mkSigma “y x. y = x” : 𝚺₁.Semisentence 2).rew (Rew.subst ![#0, #i.succ])) :=
  of_models (definedFunction_get i) fun _ _ _ ↦ ⟨_, definedFunction_get i⟩

section comp
variable {l : ℕ} {g : (Fin l → ℕ) → ℕ} {h : Fin l → (Fin k → ℕ) → ℕ}
  {ψ : 𝚺₁.Semisentence (l + 1)} {χ : Fin l → 𝚺₁.Semisentence (k + 1)}

private lemma comp (hg : T.ProvablyFunctionalVia g ψ)
    (hh : ∀ i, T.ProvablyFunctionalVia (h i) (χ i)) :
    T.ProvablyFunctionalVia (fun v ↦ g fun i ↦ h i v) (compGraph ψ χ) := by
  refine of_models (definedFunction_compGraph hg.defined fun i ↦ (hh i).defined) fun V _ _ ↦ ?_
  obtain ⟨G, hG⟩ := hg.models V
  choose H hH using fun i ↦ (hh i).models V
  exact ⟨_, definedFunction_compGraph hG hH⟩

end comp

section prec
variable {f : (Fin n → ℕ) → ℕ} {g : (Fin (n + 2) → ℕ) → ℕ}
  {ψ : 𝚺₁.Semisentence (n + 1)} {χ : 𝚺₁.Semisentence (n + 3)}

private lemma prec [𝗜𝚺₁ ⪯ T] (hf : T.ProvablyFunctionalVia f ψ)
    (hg : T.ProvablyFunctionalVia g χ) :
    T.ProvablyFunctionalVia
      (fun v : Fin (n + 1) → ℕ ↦ (v 0).rec (f (v ·.succ)) fun y ih ↦ g (y :> ih :> (v ·.succ)))
      (precBlueprint ψ χ).resultDef := by
  refine of_models (DefinedFunction.of_eq
    (fun v ↦ result_precConstruction hf.defined hg.defined _ _)
    (precConstruction hf.defined hg.defined).result_defined) fun V _ _ ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
  obtain ⟨F, hF⟩ := hf.models V
  obtain ⟨G, hG⟩ := hg.models V
  exact ⟨_, (precConstruction hF hG).result_defined⟩

end prec

end

end ArithmeticTheory.ProvablyFunctionalVia

namespace Arithmetic

open ArithmeticTheory

open ProvablyFunctionalVia in
/-- Every primitive recursive function, in Mathlib's `List.Vector` form `Nat.Primrec'`, is
`𝗜𝚺₁`-provably functional.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
theorem provablyFunctional_of_primrec' {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    𝗜𝚺₁.ProvablyFunctional (fun v ↦ f (.ofFn v)) := by
  induction hf with
  | zero => exact (zero.of_eq (by simp)).toProvablyFunctional
  | succ => exact (succ.of_eq (by simp)).toProvablyFunctional
  | get i => exact ((get i).of_eq (by simp)).toProvablyFunctional
  | comp g _ _ ihf ihg =>
    obtain ⟨ψ, hψ⟩ := ihf
    choose χ hχ using ihg
    exact ((hψ.comp hχ).of_eq (by simp)).toProvablyFunctional
  | prec _ _ ihf ihg =>
    obtain ⟨ψ, hψ⟩ := ihf
    obtain ⟨χ, hχ⟩ := ihg
    exact ((hψ.prec hχ).of_eq (by simp)).toProvablyFunctional

/-- Every primitive recursive function, in Mathlib's curried form `Primrec`, is `𝗜𝚺₁`-provably
functional.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
theorem provablyFunctional_of_primrec {f : List.Vector ℕ k → ℕ} (hf : Primrec f) :
    𝗜𝚺₁.ProvablyFunctional (fun v ↦ f (.ofFn v)) :=
  provablyFunctional_of_primrec' (Nat.Primrec'.prim_iff.mpr hf)

/-- Every primitive recursive function, in Mathlib's `List.Vector` form `Nat.Primrec'`, is
`𝗜𝚺₁`-provably total.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
lemma provablyTotal_of_primrec' {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) :=
  (provablyFunctional_of_primrec' hf).toProvablyTotal

/-- Every primitive recursive function, in Mathlib's curried form `Primrec`, is `𝗜𝚺₁`-provably
total.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
lemma provablyTotal_of_primrec {f : List.Vector ℕ k → ℕ} (hf : Primrec f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) :=
  (provablyFunctional_of_primrec hf).toProvablyTotal

/-! ## From a proof of totality to an anchored derivation -/

namespace LKI.Canonical

open LK.Derivation Rewriting

variable {k : ℕ} {φ : 𝚺₁.Semisentence (k + 1)}

/-- The graph of `φ` at the free variables `&0 … &(k-1)` is strict $\Sigma_1$. -/
lemma strictHierarchy_embSubsts_exs (hφ : StrictHierarchy 𝚺 1 φ.val) :
    StrictHierarchy 𝚺 1
      (Rew.embSubsts (fun i : Fin k ↦ (&i : ArithmeticTerm ℕ)) ▹ (∃¹ φ.val)) :=
  StrictHierarchy.rew _ hφ.exs

/-- A proof of totality in `𝗜 𝚺 1` becomes an anchored derivation of the graph of `φ` at the
free variables `&0 … &(k-1)`.

- [Bus98A, Section 3.1.3] -/
theorem nonempty_anchored_instance_of_provable_totality (h : 𝗜 𝚺 1 ⊢ totalitySentence φ) :
    ⊢ᴸᴷᴵ[StrictHierarchy 𝚺 1, fun ψ ↦ StrictHierarchy 𝚺 1 ψ ∨ StrictHierarchy 𝚷 1 ψ]
      ⦃Rew.embSubsts (fun i : Fin k ↦ (&i : ArithmeticTerm ℕ)) ▹ (∃¹ φ.val)⦄ := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp h
  have dcut : ⊢ᴸᴷ¹ ⦃Rew.embSubsts (fun i : Fin k ↦ (&i : ArithmeticTerm ℕ)) ▹ (∃¹ φ.val)⦄
      + ∼LK.Sequent.embed Δ :=
    (cut (φ := (totalitySentence φ : ArithmeticProposition)) (Γ := ∼LK.Sequent.embed Δ)
      (Δ := ⦃Rew.embSubsts (fun i : Fin k ↦ (&i : ArithmeticTerm ℕ)) ▹ (∃¹ φ.val)⦄)
      (d.cast (by simp [add_comm]))
      ((specializeMany (∃¹ φ.val) fun i ↦ &i).cast
        (by simp [totalitySentence, add_comm]))).cast (by simp [add_comm])
  exact nonempty_anchored_of_derivation (fun _ hη _ ↦ .inl (StrictHierarchy.rew _ hη))
    (fun τ hτ ↦ .inr (StrictHierarchy.rew _ (PeanoMinus.strictHierarchy τ hτ))) hΔ dcut

end LKI.Canonical

/-! ## Recovering the value by a bounded search -/

section

open Rewriting LKI LKI.Canonical

variable {k : ℕ} {f : (Fin k → ℕ) → ℕ} {φ : 𝚺₁.Semisentence (k + 1)}

/-- Substituting terms with free variables into a sentence reads the values of those terms as the
assignment to the bound variables. -/
private lemma evalBound_embSubsts {n : ℕ} {χ : ArithmeticSemisentence n}
    {w : Fin n → ArithmeticTerm ℕ} {ε : ℕ → ℕ} {b : ℕ} :
    EvalBound ![] ε b (Rew.embSubsts w ▹ χ) ↔
      EvalBound (fun i ↦ Semiterm.val ![] ε (w i)) Empty.elim b χ := by
  rw [evalBound_rew]
  simp [Function.comp_def, Empty.eq_elim]

/-- The graph of `φ` at the free variables `&0 … &(k-1)` is approximated by the graph at the
arguments themselves. -/
private lemma evalBound_instance {v : Fin k → ℕ} {b : ℕ} :
    EvalBound ![] ((List.ofFn v).getD · 0) b
        (Rew.embSubsts (fun i : Fin k ↦ (&i : ArithmeticTerm ℕ)) ▹ (∃¹ φ.val)) ↔
      ∃ y < b, EvalBound (y :> v) Empty.elim b φ.val := by
  rw [evalBound_embSubsts]
  simp

/-- The graph of `φ` with the value at `&0` and the arguments at `&1 … &k` is approximated by the
graph at the value and the arguments themselves. -/
private lemma evalBound_graph {v : Fin k → ℕ} {y b : ℕ} :
    EvalBound ![] ((y :: List.ofFn v).getD · 0) b
        (Rew.embSubsts (&0 :> fun i : Fin k ↦ (&i.succ : ArithmeticTerm ℕ)) ▹ φ.val) ↔
      EvalBound (y :> v) Empty.elim b φ.val := by
  rw [evalBound_embSubsts]
  have e : (fun j : Fin (k + 1) ↦ Semiterm.val ![] ((y :: List.ofFn v).getD · 0)
      ((&0 :> fun i : Fin k ↦ (&i.succ : ArithmeticTerm ℕ)) j)) = y :> v := by
    funext j; cases j using Fin.cases <;> simp
  rw [e]

/-- A `𝗜 𝚺 1`-proof of totality yields a primitive recursive bound on the witness of the graph.

- [Bus98A, Section 3.1.3] -/
private lemma exists_primrec_bound (hφ : StrictHierarchy 𝚺 1 φ.val)
    (h : 𝗜 𝚺 1 ⊢ totalitySentence φ) :
    ∃ g : List ℕ → ℕ → ℕ, Primrec₂ g ∧ ∀ v : Fin k → ℕ,
      ∃ y < g (List.ofFn v) 0, EvalBound (y :> v) Empty.elim (g (List.ofFn v) 0) φ.val := by
  obtain ⟨d, hd⟩ := Classical.choice (nonempty_anchored_instance_of_provable_totality h)
  obtain ⟨g, hg, H⟩ := exists_witnesses d hd
    (by simpa using Or.inl (strictHierarchy_embSubsts_exs hφ))
  refine ⟨g, hg, fun v ↦ ?_⟩
  obtain ⟨χ, hχ, -, hbnd⟩ := H (List.ofFn v) 0 fun ψ hψ hn ↦ by
    rw [Multiset.mem_singleton.mp hψ] at hn
    exact absurd (strictHierarchy_embSubsts_exs hφ) hn
  rw [Multiset.mem_singleton.mp hχ] at hbnd
  exact evalBound_instance.mp hbnd

/-- Every function that is `𝗜 𝚺 1`-provably total via a strict $\Sigma_1$ graph is primitive
recursive.

- [Bus98A, Theorem 3.1.1]
- [HP98, Corollary IV.3.7] -/
theorem primrec_of_provablyTotalVia (hφ : StrictHierarchy 𝚺 1 φ.val)
    (h : (𝗜 𝚺 1).ProvablyTotalVia f φ) : Primrec fun v : List.Vector ℕ k ↦ f v.get := by
  classical
  obtain ⟨g, hg, hgb⟩ := exists_primrec_bound hφ h.total
  set χ : ArithmeticProposition :=
    Rew.embSubsts (&0 :> fun i : Fin k ↦ (&i.succ : ArithmeticTerm ℕ)) ▹ φ.val
  have huniq : ∀ (v : Fin k → ℕ) (b y : ℕ),
      EvalBound ![] ((y :: List.ofFn v).getD · 0) b χ → y = f v := fun v b y hy ↦ by
    simpa using h.graph_iff.mp (eval_of_evalBound (evalBound_graph.mp hy))
  have hval : ∀ v : Fin k → ℕ,
      maxBelow (fun y ↦ if EvalBound ![] ((y :: List.ofFn v).getD · 0) (g (List.ofFn v) 0) χ
        then y else 0) (g (List.ofFn v) 0) = f v := fun v ↦ by
    obtain ⟨y, hy, hby⟩ := hgb v
    obtain rfl := huniq v _ y (evalBound_graph.mpr hby)
    exact maxBelow_ite_eq (evalBound_graph.mpr hby) hy (huniq v _)
  have hB : Primrec fun w : List.Vector ℕ k ↦ g w.toList 0 :=
    hg.comp Primrec.vector_toList (Primrec.const 0)
  have hP : PrimrecRel fun (w : List.Vector ℕ k) (y : ℕ) ↦
      EvalBound ![] ((y :: w.toList).getD · 0) (g w.toList 0) χ :=
    (primrecRel_evalBound (StrictHierarchy.rew _ hφ)).comp₂ (Primrec.to₂ (hB.comp Primrec.fst))
      (Primrec.to₂ (Primrec.list_cons.comp Primrec.snd (Primrec.vector_toList.comp Primrec.fst)))
  have hstep : Primrec₂ fun (w : List.Vector ℕ k) (y : ℕ) ↦
      if EvalBound ![] ((y :: w.toList).getD · 0) (g w.toList 0) χ then y else 0 :=
    Primrec.ite hP Primrec.snd (Primrec.const 0)
  refine (primrec_maxBelow hstep hB).of_eq fun w ↦ ?_
  have e : List.ofFn w.get = w.toList := by
    rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
  rw [← e]
  exact hval w.get

/-- Every function that is `𝗜 𝚺 1`-provably total via a strict $\Sigma_1$ graph is primitive
recursive, in `Nat.Primrec'` form.

- [Bus98A, Theorem 3.1.1]
- [HP98, Corollary IV.3.7] -/
theorem primrec'_of_provablyTotalVia (hφ : StrictHierarchy 𝚺 1 φ.val)
    (h : (𝗜 𝚺 1).ProvablyTotalVia f φ) : Nat.Primrec' fun v : List.Vector ℕ k ↦ f v.get :=
  Nat.Primrec'.prim_iff.mpr (primrec_of_provablyTotalVia hφ h)

end

/-! ## Normalising the graph to a strict $\Sigma_1$ formula -/

section

open _root_.FFL.Entailment

/-- The reading of a provable equivalence of graph formulas in a model. -/
private lemma models_allClosure_iff_evalb {k : ℕ} {φ ψ : ArithmeticSemisentence (k + 1)}
    {V : Type*} [ORingStructure V] :
    V↓[ℒₒᵣ] ⊧ (∀¹* (φ 🡘 ψ) : ArithmeticSentence) ↔
      ∀ v : Fin (k + 1) → V, φ.Evalb v ↔ ψ.Evalb v := by
  simp [models_iff]

/-- An `𝗜𝚺₁`-provably total function has a strict $\Sigma_1$ graph whose totality is already
provable in the strict induction theory `𝗜 𝚺 1`.
- [HP98, Theorem I.2.5(3)]
- [HP98, Lemma I.2.9] -/
theorem exists_strictHierarchy_provablyTotalVia {k : ℕ} {f : (Fin k → ℕ) → ℕ}
    (h : 𝗜𝚺₁.ProvablyTotal f) :
    ∃ φ : 𝚺₁.Semisentence (k + 1), StrictHierarchy 𝚺 1 φ.val ∧ (𝗜 𝚺 1).ProvablyTotalVia f φ := by
  obtain ⟨φ, hφ⟩ := h
  have hBS : 𝗕𝚺₁ ⪯ 𝗜 𝚺 1 :=
    WeakerThan.trans (𝓣 := 𝗜𝚺₁) (BSigma_weakerThan_ISigma 0) inferInstance
  have hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, StrictHierarchy 𝚺 1 ψ →
      𝗜 𝚺 1 ⊢ (.univCl (collectionAxiom ψ) : ArithmeticSentence) := fun ψ hψ ↦
    WeakerThan.pbl (𝓢 := 𝗕𝚺₁)
      (by_axm (Set.mem_union_right _ (mem_CollectionScheme_of_mem hψ.hierarchy)))
  obtain ⟨ψ, hψ, hprov⟩ := exists_strictHierarchy_of_collection (𝗜 𝚺 1) hcol φ.sigma_prop
  have hmono : (𝗜 𝚺 1).ProvablyTotalVia f φ := hφ.mono inferInstance
  have heval : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜 𝚺 1],
      ∀ v : Fin (k + 1) → V, φ.val.Evalb v ↔ ψ.Evalb v := fun V _ _ ↦
    models_allClosure_iff_evalb.mp (consequence_iff'.mp (Theory.Proof.sound hprov) V)
  refine ⟨.mkSigma ψ hψ.hierarchy, by simpa using hψ, ?_, ?_⟩
  · exact .mk fun v ↦ (heval ℕ v).symm.trans hmono.graph_iff
  · exact Arithmetic.complete _ _ fun (V : Type) _ _ ↦
      models_totalitySentence_iff.mpr fun v ↦
        have ⟨y, hy⟩ := hmono.models V v
        ⟨y, by simpa using (heval V (y :> v)).mp hy⟩

end

/-! ## Parsons' theorem -/

/-- Every `𝗜𝚺₁`-provably total function is primitive recursive.
- [HP98, Corollary IV.3.7] -/
theorem primrec'_of_provablyTotal {k : ℕ} {f : List.Vector ℕ k → ℕ}
    (hf : 𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v))) : Nat.Primrec' f :=
  have ⟨_, hφ, h⟩ := exists_strictHierarchy_provablyTotalVia hf
  (primrec'_of_provablyTotalVia hφ h).of_eq fun v ↦ by simp

/-- **Parsons' theorem**: the `𝗜𝚺₁`-provably total functions are exactly the primitive recursive
functions.
- [HP98, Corollary IV.3.7] -/
theorem primrec'_iff_provablyTotal {k : ℕ} (f : List.Vector ℕ k → ℕ) :
    Nat.Primrec' f ↔ 𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) :=
  ⟨provablyTotal_of_primrec', primrec'_of_provablyTotal⟩

/-- **Parsons' theorem**, under its usual name. -/
alias parsons := primrec'_iff_provablyTotal

/-- **Parsons' theorem** in class form: the class of `𝗜𝚺₁`-provably total functions of arity `k`
is the class of primitive recursive functions of arity `k`.
- [HP98, Corollary IV.3.7] -/
theorem provablyTotalFunctions_ISigma1 (k : ℕ) :
    𝗜𝚺₁.provablyTotalFunctions k = {f | Nat.Primrec' fun v : List.Vector ℕ k ↦ f v.get} := by
  ext f
  have e : (fun v : Fin k → ℕ ↦ f (List.Vector.ofFn v).get) = f :=
    funext fun v ↦ congrArg f (funext (List.Vector.get_ofFn v))
  simpa [e] using (primrec'_iff_provablyTotal fun v : List.Vector ℕ k ↦ f v.get).symm

/-- In Mathlib's `Primrec` form, the `𝗜𝚺₁`-provably total functions are exactly the primitive
recursive functions.
- [HP98, Corollary IV.3.7] -/
theorem primrec_iff_provablyTotal {k : ℕ} (f : List.Vector ℕ k → ℕ) :
    Primrec f ↔ 𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) :=
  Nat.Primrec'.prim_iff.symm.trans (primrec'_iff_provablyTotal f)

/-- **Parsons' theorem** in Mathlib's `Primrec` form, under its usual name. -/
alias parsons_primrec := primrec_iff_provablyTotal

/-- The Ackermann function is not `𝗜𝚺₁`-provably total.
- [HP98, Corollary IV.3.7] -/
theorem not_provablyTotal_ackermann :
    ¬𝗜𝚺₁.ProvablyTotal (fun v : Fin 2 → ℕ ↦ _root_.ack (v 0) (v 1)) := by
  intro h
  have hp : Primrec fun w : List.Vector ℕ 2 ↦ _root_.ack (w.get 0) (w.get 1) :=
    Nat.Primrec'.prim_iff.mp ((primrec'_iff_provablyTotal _).mpr (by simpa using h))
  have hc : Primrec fun p : ℕ × ℕ ↦ (p.1 ::ᵥ p.2 ::ᵥ List.Vector.nil : List.Vector ℕ 2) :=
    Primrec.vector_cons.comp Primrec.fst (Primrec.vector_cons.comp Primrec.snd (Primrec.const _))
  exact not_primrec₂_ack ((hp.comp hc).of_eq (by intro p; rfl))

end Arithmetic

end FFL.FirstOrder
