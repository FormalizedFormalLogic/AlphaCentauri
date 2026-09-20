module

public import AlphaCentauri.Calculus.Induction.Instantiation
public import AlphaCentauri.Calculus.Induction.Witnessing
public import AlphaCentauri.ProvablyTotal.Basic

/-!
# Witnessing provably total functions

A function whose graph is a strict $\Sigma_1$ formula whose totality `𝗜 𝚺 1` proves is
primitive recursive: the proof of totality becomes an anchored derivation of the graph at the
arguments as free variables, witnessing reads a primitive recursive bound off that derivation,
and the value is recovered by a bounded search below the bound.

- [Bus98A, Theorem 3.1.1, Section 3.1.3]
- [HP98, Corollary IV.3.7]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

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

open Rewriting LKI LKI.Canonical

section
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

end FFL.FirstOrder.Arithmetic

end
