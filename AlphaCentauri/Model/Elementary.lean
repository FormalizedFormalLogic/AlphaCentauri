module

public import AlphaCentauri.Model.Absolute
public import AlphaCentauri.Model.Cut
public import AlphaCentauri.Model.Overspill
public import AlphaCentauri.ToFoundation.FirstOrder.Hierarchy
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv

/-! # Elementary substructures

An embedding of `ℒₒᵣ`-structures is $\Sigma_s$-elementary when prenex $\Sigma_m$ and $\Pi_m$
formulas, for `m ≤ s`, take the same truth value at elements of the substructure as at their images.
The Tarski–Vaught test reduces this to the absoluteness of bounded formulas and to finding witnesses
in the substructure. A proper cut $\Sigma_j$-elementary in a model of $\mathsf{I}\Sigma_j$ satisfies
$\mathsf{B}\Sigma_{j+1}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

section Elementary

open Semiformula

variable {S M : Type} [ORingStructure S] [ORingStructure M]

/-- `ι` is $\Sigma_s$-elementary: for `m ≤ s`, prenex $\Sigma_m$ and $\Pi_m$ formulas take the same
truth value at elements of `S` as at their images.
- [HP98, Definition IV.1.17] -/
def SigmaElementary (ι : S ↪ₛ[ℒₒᵣ] M) (s : ℕ) : Prop :=
  ∀ {Γ : Polarity} {m n : ℕ} {φ : ArithmeticSemiformula ℕ n}, m ≤ s →
    ℬ[<, ℒₒᵣ].PrenexHierarchy Γ m φ → ∀ (e : Fin n → S) (f : ℕ → S),
      φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f

variable (ι : S ↪ₛ[ℒₒᵣ] M)

lemma eval_ex_iff_of_witness {n : ℕ} {χ : ArithmeticSemiformula ℕ (n + 1)} {e : Fin n → S}
    {f : ℕ → S}
    (witness : (∃ x : M, χ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : S, χ.Eval (ι x :> ι ∘ e) (ι ∘ f))
    (h : ∀ x : S, χ.Eval (ι ∘ (x :> e)) (ι ∘ f) ↔ χ.Eval (x :> e) f) :
    (∃¹ χ).Eval (ι ∘ e) (ι ∘ f) ↔ (∃¹ χ).Eval e f := by
  simp only [eval_ex, Matrix.comp_vecCons''] at h ⊢
  constructor
  · intro h₁
    obtain ⟨x, hx⟩ := witness h₁
    use x
    exact (h x).mp hx
  · rintro ⟨x, hx⟩
    use ι x
    exact (h x).mpr hx

/-- The Tarski–Vaught test: bounded formulas are absolute along `ι`, and every prenex $\Pi_m$
formula, `m < s`, with parameters from `S` and a witness in `M` has a witness in `S`.
- [HP98, Lemma IV.1.19] -/
theorem sigmaElementary_of_tarskiVaught (s : ℕ)
    (bounded : ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ n}, ℬ[<, ℒₒᵣ].Closure φ →
      ∀ (e : Fin n → S) (f : ℕ → S), φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f)
    (witness : ∀ m < s, ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ (n + 1)},
      ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 m φ → ∀ (e : Fin n → S) (f : ℕ → S),
        (∃ x : M, φ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : S, φ.Eval (ι x :> ι ∘ e) (ι ∘ f)) :
    SigmaElementary ι s := by
  intro Γ m n φ hm hφ
  induction m generalizing Γ n φ with
  | zero => exact bounded (Bounding.PrenexHierarchy.zero_iff_bounded.mp hφ)
  | succ m ih =>
    intro e f
    rcases Γ
    · obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hφ
      exact eval_ex_iff_of_witness ι (witness m (by omega) hψ e f)
        fun x ↦ ih (by omega) hψ (x :> e) f
    · obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.pi_succ_iff.mp hφ
      simpa using (eval_ex_iff_of_witness ι (witness m (by omega) hψ.neg e f)
        fun x ↦ ih (by omega) hψ.neg (x :> e) f).not

/-- Bounded formulas are absolute along `ι` as soon as every bounded formula with parameters from
`S` and a witness in `M` has a witness in `S`. -/
lemma eval_iff_of_bounded_of_witness
    (witness : ∀ {n : ℕ} {φ : ArithmeticSemiformula ℕ (n + 1)}, ℬ[<, ℒₒᵣ].Closure φ →
      ∀ (e : Fin n → S) (f : ℕ → S),
        (∃ x : M, φ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : S, φ.Eval (ι x :> ι ∘ e) (ι ∘ f))
    {n : ℕ} {φ : ArithmeticSemiformula ℕ n} (hφ : ℬ[<, ℒₒᵣ].Closure φ)
    (e : Fin n → S) (f : ℕ → S) : φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f :=
  bounded_induction_open
    (P := fun n φ ↦ ∀ (e : Fin n → S) (f : ℕ → S), φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f)
    (fun _ _ hφ _ _ ↦ (eval_hom_iff_of_open ι hφ).symm)
    (fun _ _ _ _ _ ihφ ihψ e f ↦ by simp [ihφ e f, ihψ e f])
    (fun _ _ _ _ _ ihφ ihψ e f ↦ by simp [ihφ e f, ihψ e f])
    (fun _ t θ hθ ih e f ↦ by
      have hχ : ℬ[<, ℒₒᵣ].Closure (“#0 < !!(Rew.bShift t)” ⋏ ∼θ) :=
        .and (.of_open (by simp)) hθ.neg
      simpa [ball] using (eval_ex_iff_of_witness ι (witness hχ e f) fun x ↦ by
        simp [ih (x :> e) f, ← eval_hom_iff_of_open ι (φ := “#0 < !!(Rew.bShift t)”)]).not)
    (fun _ t θ hθ ih e f ↦ by
      have hχ : ℬ[<, ℒₒᵣ].Closure (“#0 < !!(Rew.bShift t)” ⋏ θ) := .and (.of_open (by simp)) hθ
      exact eval_ex_iff_of_witness ι (witness hχ e f) fun x ↦ by
        simp [ih (x :> e) f, ← eval_hom_iff_of_open ι (φ := “#0 < !!(Rew.bShift t)”)])
    n φ hφ e f

/-- A $\Sigma_0$-elementary substructure of a model of `𝗣𝗔⁻` is a model of `𝗣𝗔⁻`.
- [HP98, Remark IV.1.21(2)] -/
theorem SigmaElementary.models_peanoMinus {ι : S ↪ₛ[ℒₒᵣ] M} (hι : SigmaElementary ι 0)
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] : S↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
  have h {Γ : Polarity} {n : ℕ} {φ : ArithmeticSemiformula ℕ n}
      (hφ : ℬ[<, ℒₒᵣ].PrenexBlock Γ φ) (hΓ : Γ = 𝚷) (e : Fin n → S) (f : ℕ → S) :
      φ.Eval (ι ∘ e) (ι ∘ f) → φ.Eval e f := by
    induction hφ with
    | bounded h =>
      exact (hι (Γ := 𝚷) le_rfl (Bounding.PrenexHierarchy.zero_iff_bounded.mpr h) e f).mp
    | exs => simp at hΓ
    | all _ ih =>
      simp only [eval_all]
      intro h₁ x
      exact ih rfl (x :> e) (by simpa [Matrix.comp_vecCons''] using h₁ (ι x))
  apply models_theory_iff.mpr
  intro σ hσ
  have h₁ := models_theory_iff.mp (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻) σ hσ
  simpa [models_iff] using h ((PeanoMinus.prenexBlock σ hσ).rew Rew.emb) rfl ![] (fun _ ↦ 0)
    (by simpa [models_iff] using h₁)

/-- A $\Sigma_s$-elementary embedding preserves the truth of $\Sigma_s$ and $\Pi_s$ sentences
between models of $\mathsf{B}\Sigma_s$. -/
lemma SigmaElementary.models_iff_of_hierarchy {ι : S ↪ₛ[ℒₒᵣ] M} {s : ℕ} (hι : SigmaElementary ι s)
    [S↓[ℒₒᵣ] ⊧* 𝗕𝚺s] [M↓[ℒₒᵣ] ⊧* 𝗕𝚺s] {Γ : Polarity} {n : ℕ} {φ : ArithmeticSemisentence n}
    (hφ : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ) (v : Fin n → S) : M ⊧/(ι ∘ v) φ ↔ S ⊧/v φ := by
  obtain ⟨φ', hφ'⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) hφ
  rw [hφ' M, hφ' S]
  have := hι le_rfl (φ'.rew Rew.emb).val_prenexHierarchy v (fun _ ↦ 0)
  rwa [Bounding.Prenex.val_rew, eval_emb, eval_emb] at this

namespace Cut

variable {j : ℕ} [M↓[ℒₒᵣ] ⊧* 𝗜𝚺j] (I : Cut M) [I.Closed]

private lemma exists_bound_of_sigmaElementary (hI : ∃ c, c ∉ I.carrier)
    (hj : SigmaElementary I.endExtension.emb j) {ψ : ArithmeticSemiformula ℕ 3}
    (hψ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 j ψ) (e : ℕ → I.carrier) (a : I.carrier)
    (h : ∀ x < a, ∃ y z, ψ.Eval ![z, x, y] e) :
    ∃ b, ∀ x < a, ∃ y < b, ∃ z, ψ.Eval ![z, x, y] e := by
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺j)
  obtain ⟨c₀, hc₀⟩ := hI
  let _ : I.carrier ⊂ₑ M := { I.endExtension with
    not_surjective h := hc₀ <| by obtain ⟨x, rfl⟩ := h c₀; exact x.2 }
  have hψ' (x y z : I.carrier) :
      ψ.Eval ![z.1, x.1, y.1] (I.endExtension.emb ∘ e) ↔ ψ.Eval ![z, x, y] e := by
    simpa [Matrix.comp_vecCons''] using hj le_rfl hψ ![z, x, y] e
  have hlt {y c : M} (hy : y ∈ I.carrier) (hc : c ∉ I.carrier) : y < c := by
    by_contra! h₁
    exact hc <| h₁.lt_or_eq.elim (I.mem_of_lt · hy) (· ▸ hy)
  let Θ : ArithmeticSemiformula ℕ 1 :=
    ((((Rew.rewriteMap Nat.succ ▹ ψ) ⇜ ![#0, #2, #1]).bexsLT #2).bexsLT #1).ballLT &0
  let g : ℕ → M := a.1 :>ₙ (Subtype.val ∘ e)
  have hΘ (c : M) : Θ.Eval ![c] g ↔
      ∀ x < a.1, ∃ y < c, ∃ z < c, ψ.Eval ![z, x, y] fun i ↦ (e i).1 := by
    simp [Θ, g, eval_rewriteMap, Matrix.comp_vecCons'']
  have h₁ {c : M} (hc : c ∉ I.carrier) : Θ.Eval ![c] g := by
    apply (hΘ c).mpr
    intro x hx
    obtain ⟨y, z, h₂⟩ := h ⟨x, I.mem_of_lt hx a.2⟩ hx
    use y
    and_intros
    · exact hlt y.2 hc
    use z
    and_intros
    · exact hlt z.2 hc
    exact (hψ' _ y z).mpr h₂
  obtain ⟨b, hb, h₂⟩ : ∃ b ∈ I.carrier, Θ.Eval ![b] g := by
    by_contra! h₂
    obtain ⟨c, hc, h₃⟩ := overspill (M := I.carrier) 𝚺 j (φ := ∼Θ)
      (by simp [Θ, hψ.hierarchy]) g fun b ↦ by simpa using h₂ b.1 b.2
    have hc' : c ∉ I.carrier := fun h ↦ hc ⟨⟨c, h⟩, rfl⟩
    obtain ⟨d, rfl⟩ := eq_succ_of_pos (hlt Closed.zero_mem hc')
    exact absurd (h₁ fun h ↦ hc' (I.succ_mem h)) (by simpa using h₃ d (lt_add_one d))
  use ⟨b, hb⟩
  intro x hx
  obtain ⟨y, hy, z, hz, h₃⟩ := (hΘ b).mp h₂ x.1 hx
  use ⟨y, I.mem_of_lt hy hb⟩
  and_intros
  · exact hy
  use ⟨z, I.mem_of_lt hz hb⟩
  exact (hψ' x ⟨y, _⟩ ⟨z, _⟩).mp h₃

/-- A proper cut of a model of $\mathsf{I}\Sigma_j$ which is closed under the operations and
$\Sigma_j$-elementary satisfies $\mathsf{B}\Sigma_{j+1}$.
- [HP98, Lemma IV.1.22] -/
theorem models_BSigma_succ (hI : ∃ c, c ∉ I.carrier) (hj : SigmaElementary I.endExtension.emb j) :
    I.carrier↓[ℒₒᵣ] ⊧* 𝗕𝚺 (j + 1) := by
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := mod_ISigma_of_le (Nat.zero_le j)
  apply Semantics.ModelsSet.union_iff.mpr
  and_intros
  · exact I.endExtension.models_ISigma0
  · apply Semantics.ModelsSet.setOf_iff.mpr
    rintro _ ⟨φ, hφ, rfl⟩
    suffices ∀ (e : ℕ → I.carrier) (a : I.carrier), (∀ x < a, ∃ y, φ.Eval ![x, y] e) →
        ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] e by
      simpa [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
        Semiformula.eval_bexsLT, Semiformula.eval_substs] using this
    obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hφ
    simpa using I.exists_bound_of_sigmaElementary hI hj hψ

end Cut

end Elementary

end FFL.FirstOrder.Arithmetic
