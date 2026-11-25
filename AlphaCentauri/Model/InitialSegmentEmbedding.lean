module

public import AlphaCentauri.Model.Saturation
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Model
public import Mathlib.Order.Ideal

/-! # Initial segment embeddings

The embedding theorem for countable nonstandard models of `𝗣𝗔`, and Friedman's self-embedding
theorem.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping
open FFL.FirstOrder.Bounding (HierarchySymbol)
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M N : Type*} [ORingStructure M] [ORingStructure N] {n l : ℕ} {b : N}

/-! ## Tuples with the same $\Pi_n$ properties -/

/-- Every $\Pi_n$ formula with a witness in `M` for the parameters `u` has a witness in `N` below
`b` for the parameters `v`.
- [Kay91, Theorem 12.3] -/
def PiWitnessBelow (n : ℕ) (b : N) (u : Fin l → M) (v : Fin l → N) : Prop :=
  ∀ θ : ArithmeticSemisentence (l + 1), ℬ[<, ℒₒᵣ].Hierarchy 𝚷 n θ →
    (∃ x : M, M ⊧/(x :> u) θ) → ∃ x < b, N ⊧/(x :> v) θ

section

variable {Γ : Polarity} {ψ : ArithmeticSemisentence (l + 2)}
  (hψ : ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n ψ) (φ : ArithmeticSemisentence (l + 2)) (z x : M)
  (u : Fin l → M)

/-- `φ` with a dummy variable inserted after the first two. -/
private def insertThird : ArithmeticSemisentence (l + 3) :=
  φ ⇜ (#0 :> #1 :> fun i ↦ #i.succ.succ.succ)

@[simp]
private lemma hierarchy_insertThird_iff :
    ℬ[<, ℒₒᵣ].Hierarchy Γ n (insertThird φ) ↔ ℬ[<, ℒₒᵣ].Hierarchy Γ n φ := by
  simp [insertThird]

@[simp]
private lemma eval_insertThird (y : M) :
    M ⊧/(z :> x :> y :> u) (insertThird φ) ↔ M ⊧/(z :> x :> u) φ := by
  have h : Semiterm.val (z :> x :> y :> u) Empty.elim ∘ (#0 :> #1 :> fun i ↦ #i.succ.succ.succ :
      Fin (l + 2) → ClosedSemiterm ℒₒᵣ (l + 3)) = z :> x :> u := by
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases <;> simp
  rw [insertThird, Semiformula.eval_substs, h]

include hψ in
private lemma prenexFormulaSatisfied_adjoin_iff [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    PrenexFormulaSatisfied Γ n (z ∷ x ∷ matrixToVec u) ⌜ψ⌝ ↔ M ⊧/(z :> x :> u) ψ := by
  simpa using PrenexFormulaSatisfied.quote_iff hψ (z :> x :> u)

end

namespace PiWitnessBelow

variable {u : Fin l → M} {v : Fin l → N} (h : PiWitnessBelow n b u v)
include h

lemma comp {k : ℕ} (f : Fin k → Fin l) : PiWitnessBelow n b (u ∘ f) (v ∘ f) := by
  intro θ hθ
  simpa [Semiformula.eval_rew_q, Function.comp_def] using
    h ((Rew.subst fun i ↦ #(f i)).q ▹ θ) (by simpa using hθ)

lemma models {θ : ArithmeticSemisentence l} (hθ : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 n θ) (hu : M ⊧/u θ) :
    N ⊧/v θ := by
  obtain ⟨x, -, hx⟩ := h (Rew.bShift ▹ θ) (by simpa using hθ) <| by
    use 0
    simpa using hu
  simpa using hx

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [N↓[ℒₒᵣ] ⊧* 𝗣𝗔] [IsNonstandard M] [IsNonstandard N]
  (hSSy : standardSystem M = standardSystem N)
include hSSy

/-- [Kay91, Theorem 12.3] -/
lemma exists_forth (x : M) : ∃ y : N, PiWitnessBelow n b (x :> u) (y :> v) := by
  have hA := hSSy ▸ setOf_prenexHierarchy_mem_standardSystem 𝚷 n (l + 2) (m := n + 1)
    (P := fun e ↦ ∃ z, PrenexFormulaSatisfied 𝚷 n (z ∷ x ∷ matrixToVec u) e) (by definability)
  simp only [← and_assoc] at hA
  obtain ⟨y, hy⟩ := exists_forall_of_setOf_mem_standardSystem (m := n + 1) hA
    (R := fun y e ↦ ∃ z < b, PrenexFormulaSatisfied 𝚷 n (z ∷ y ∷ matrixToVec v) e)
    (by definability) <| by
      intro s hs
      choose! z hz using fun φ hφ ↦ (hs φ hφ).2
      let θ : ArithmeticSemisentence (l + 1) :=
        (⩕ φ ∈ s, (insertThird φ).bexsLTSucc #1).bexsLTSucc #0
      obtain ⟨w, hw, hθ⟩ : ∃ w < b, ∃ y ≤ w, ∀ φ ∈ s, ∃ z ≤ w, N ⊧/(z :> y :> v) φ := by
        simpa [θ, Semiformula.eval_bexsLTSucc, lt_succ_iff_le] using h θ
          (by simpa [θ] using fun φ hφ ↦ (hs φ hφ).1.hierarchy) <| by
            use x + ∑ φ ∈ s, z φ
            suffices ∃ y ≤ x + ∑ φ ∈ s, z φ, ∀ φ ∈ s, ∃ w ≤ x + ∑ φ ∈ s, z φ,
                M ⊧/(w :> y :> u) φ by
              simpa [θ, Semiformula.eval_bexsLTSucc, lt_succ_iff_le] using this
            use x
            and_intros
            · exact le_self_add
            · intro φ hφ
              use z φ
              and_intros
              · exact le_add_left (Finset.single_le_sum (by simp) hφ)
              · exact (prenexFormulaSatisfied_adjoin_iff (hs φ hφ).1 _ _ _).mp (hz φ hφ)
      obtain ⟨y, -, hy⟩ := hθ
      use y
      intro φ hφ
      obtain ⟨z, hz, hφz⟩ := hy φ hφ
      use z
      and_intros
      · exact hz.trans_lt hw
      · exact (prenexFormulaSatisfied_adjoin_iff (hs φ hφ).1 _ _ _).mpr hφz
  use y
  rintro θ hθ ⟨w, hw⟩
  obtain ⟨ψ, hψ, hθψ⟩ := exists_prenexHierarchy_of_hierarchy 𝗣𝗔 hθ
  obtain ⟨z, hz, h₁⟩ := hy ψ <| by
    and_intros
    · exact hψ
    · use w
      exact (prenexFormulaSatisfied_adjoin_iff hψ _ _ _).mpr <|
        (models_iff_of_provable_allClosure hθψ _).mp hw
  use z
  and_intros
  · exact hz
  · exact (models_iff_of_provable_allClosure hθψ _).mpr <|
      (prenexFormulaSatisfied_adjoin_iff hψ _ _ _).mp h₁

/-- [Kay91, Theorem 12.3] -/
lemma exists_back {y : N} {i : Fin l} (hy : y ≤ v i) :
    ∃ x : M, PiWitnessBelow n b (x :> u) (y :> v) := by
  have hB := hSSy.symm ▸ setOf_prenexHierarchy_mem_standardSystem 𝚺 n (l + 2) (m := n + 1)
    (P := fun e ↦ ∀ z < b, PrenexFormulaSatisfied 𝚺 n (z ∷ y ∷ matrixToVec v) e) (by definability)
  simp only [← and_assoc] at hB
  have hR : 𝚺ᴬ_[n + 4].DefinableRel fun x e : M ↦
      ∀ z, PrenexFormulaSatisfied 𝚺 n (z ∷ x ∷ matrixToVec u) e := by
    have : 𝚷ᴬ_[n + 3].DefinableRel (PrenexFormulaSatisfied 𝚺 n : M → M → Prop) :=
      (PrenexFormulaSatisfied.definable 𝚺 n).of_lt (by simp)
    apply HierarchySymbol.Definable.of_lt (C := 𝚷ᴬ_[n + 3]) _ (by simp)
    definability
  obtain ⟨x, hx⟩ := exists_forall_of_setOf_mem_standardSystem hB hR <| by
    intro s hs
    obtain ⟨x, -, hx⟩ : ∃ x ≤ u i, ∀ z, ∀ φ ∈ s, M ⊧/(z :> x :> u) φ := by
      by_contra! hc
      let χ : ArithmeticSemisentence (l + 2) := ⩖ φ ∈ s, ∼φ
      let θ : ArithmeticSemisentence (l + 1) :=
        ((insertThird χ).bexsLT #1).ballLTSucc #i.succ
      have hχ : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 n χ := by
        simpa [χ] using fun φ hφ ↦ (hs φ hφ).1.hierarchy
      have hχR : 𝚺ᴬ_[n + 1].DefinableRel fun x z : M ↦ M ⊧/(z :> x :> u) χ := by
        apply (Bounding.definableRel_of_hierarchy
          ((hχ.accum 𝚺).rew (Rew.bind (#1 :> #0 :> fun i ↦ &i) Empty.elim)) u).of_iff
        intro p
        have h₁ : Semiterm.val ![p 0, p 1] u ∘ (Rew.bind (#1 :> #0 :> fun i ↦ &i) Empty.elim :
            Rew ℒₒᵣ Empty (l + 2) (Fin l) 2) ∘ Semiterm.bvar = p 1 :> p 0 :> u := by
          funext j
          cases j using Fin.cases with
          | zero => simp
          | succ j => cases j using Fin.cases <;> simp
        simp only [Semiformula.eval_rew, h₁]
        rw [Subsingleton.elim (_ ∘ _ ∘ Semiterm.fvar) Empty.elim]
      obtain ⟨t, ht⟩ := IBroadSigma.collection hχR (u i + 1) <| by
        simpa [χ, lt_succ_iff_le] using hc
      obtain ⟨t, htb, ht⟩ : ∃ t < b, ∀ x ≤ v i, ∃ z < t, N ⊧/(z :> x :> v) χ := by
        simpa [θ, Semiformula.eval_ballLTSucc, lt_succ_iff_le] using h θ
          (by simpa [θ] using hχ) <| by
            use t
            simpa [θ, Semiformula.eval_ballLTSucc, lt_succ_iff_le] using ht
      obtain ⟨z, hz, hχz⟩ := ht y hy
      obtain ⟨φ, hφ, hφz⟩ : ∃ φ ∈ s, ¬N ⊧/(z :> y :> v) φ := by simpa [χ] using hχz
      exact hφz <| (prenexFormulaSatisfied_adjoin_iff (hs φ hφ).1 z y v).mp <|
        (hs φ hφ).2 z (hz.trans htb)
    use x
    intro φ hφ z
    exact (prenexFormulaSatisfied_adjoin_iff (hs φ hφ).1 _ _ _).mpr (hx z φ hφ)
  use x
  rintro θ hθ ⟨w, hw⟩
  by_contra! hc
  obtain ⟨ψ, hψ, hθψ⟩ := exists_prenexHierarchy_of_hierarchy (Γ := 𝚺) 𝗣𝗔 hθ.neg
  have h₁ : M ⊧/(w :> x :> u) (∼θ) := by
    apply (models_iff_of_provable_allClosure hθψ _).mpr
    apply (prenexFormulaSatisfied_adjoin_iff hψ _ _ _).mp
    apply hx ψ
    and_intros
    · exact hψ
    · intro z hz
      apply (prenexFormulaSatisfied_adjoin_iff hψ _ _ _).mpr
      apply (models_iff_of_provable_allClosure hθψ _).mp
      simpa using hc z hz
  simp [hw] at h₁

end PiWitnessBelow

/-! ## The embedding -/

variable (M n b) in
/-- A tuple of `M` and a tuple of `N` such that every $\Pi_n$ formula with a witness in `M` for the
former has a witness in `N` below `b` for the latter. -/
structure PartialInitialEmbedding where
  length : ℕ
  source : Fin length → M
  target : Fin length → N
  piWitnessBelow : PiWitnessBelow n b source target

namespace PartialInitialEmbedding

variable (p : PartialInitialEmbedding M n b)

/-- The graph of a partial embedding. -/
def graph : Set (M × N) := Set.range fun i ↦ (p.source i, p.target i)

instance : Preorder (PartialInitialEmbedding M n b) := Preorder.lift graph

lemma piWitnessBelow_of_mem_graph {u : Fin l → M} {v : Fin l → N}
    (h : ∀ i, (u i, v i) ∈ p.graph) : PiWitnessBelow n b u v := by
  choose f hf using h
  obtain ⟨rfl, rfl⟩ : p.source ∘ f = u ∧ p.target ∘ f = v := by
    and_intros <;> funext i
    · exact congrArg Prod.fst (hf i)
    · exact congrArg Prod.snd (hf i)
  exact p.piWitnessBelow.comp f

end PartialInitialEmbedding

section

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [N↓[ℒₒᵣ] ⊧* 𝗣𝗔] [Countable M] [Countable N] [IsNonstandard M]
  [IsNonstandard N]

/-- [Kay91, Theorem 12.3] -/
private lemma exists_piWitnessBelow_comp (hSSy : standardSystem M = standardSystem N) {c : M}
    {a : N} (h : PiWitnessBelow n b ![c] ![a]) :
    ∃ f : M → N, f c = a ∧ (∀ x y, y < f x → y ∈ Set.range f) ∧
      ∀ {l : ℕ} (u : Fin l → M), PiWitnessBelow n b u (f ∘ u) := by
  have := Encodable.ofCountable (M × N)
  let 𝒟 (e : M × N) : Order.Cofinal (PartialInitialEmbedding M n b) := {
    carrier := {p | ∃ y, (e.1, y) ∈ p.graph ∧ (e.2 < y → ∃ x, (x, e.2) ∈ p.graph)}
    isCofinal := by
      intro p
      have hle {x : M} {y : N} (q : PartialInitialEmbedding M n b)
          (hxy : PiWitnessBelow n b (x :> q.source) (y :> q.target)) :
          ∃ r, q ≤ r ∧ (x, y) ∈ r.graph := by
        use ⟨_, _, _, hxy⟩
        and_intros
        · rintro _ ⟨i, rfl⟩
          use i.succ
          simp
        · use 0
          simp
      obtain ⟨y, hy⟩ := p.piWitnessBelow.exists_forth hSSy e.1
      obtain ⟨q, hpq, hq⟩ := hle p hy
      by_cases hey : e.2 < y
      · obtain ⟨i, hi⟩ := hq
        have hi' : q.target i = y := congrArg Prod.snd hi
        obtain ⟨x, hx⟩ := q.piWitnessBelow.exists_back hSSy (hi' ▸ hey.le)
        obtain ⟨r, hqr, hr⟩ := hle q hx
        use r
        and_intros
        · use y
          and_intros
          · exact hqr ⟨i, hi⟩
          · intro _
            use x
        · exact hpq.trans hqr
      · use q
        and_intros
        · use y
          and_intros
          · exact hq
          · intro h
            exact (hey h).elim
        · exact hpq }
  let p₀ : PartialInitialEmbedding M n b := ⟨1, ![c], ![a], h⟩
  let G : Set (M × N) := ⋃ p ∈ Order.idealOfCofinals p₀ 𝒟, p.graph
  have hG {l : ℕ} {u : Fin l → M} {v : Fin l → N} (hu : ∀ i, (u i, v i) ∈ G) :
      PiWitnessBelow n b u v := by
    simp only [G, Set.mem_iUnion] at hu
    choose p hp hpu using hu
    choose k hk using hp
    obtain ⟨m, hm⟩ := (Set.finite_range k).bddAbove
    exact (Order.sequenceOfCofinals p₀ 𝒟 m).piWitnessBelow_of_mem_graph fun i ↦
      (hk i).trans (Order.sequenceOfCofinals.monotone p₀ 𝒟 (hm ⟨i, rfl⟩)) (hpu i)
  have hD (x : M) (y : N) : ∃ z, (x, z) ∈ G ∧ (y < z → ∃ x', (x', y) ∈ G) := by
    obtain ⟨p, ⟨z, hz, h⟩, hp⟩ := Order.cofinal_meets_idealOfCofinals p₀ 𝒟 (x, y)
    use z
    have : p.graph ⊆ G := Set.subset_biUnion_of_mem hp
    grind
  have huniq {x : M} {y y' : N} (hy : (x, y) ∈ G) (hy' : (x, y') ∈ G) : y = y' := by
    simpa using (hG (u := ![x, x]) (v := ![y, y']) (by simp [Fin.forall_fin_two, hy, hy'])).models
      (θ := “x y. x = y”) (by simp) (by simp)
  choose f hf using fun x ↦ (hD x 0).imp fun _ ↦ And.left
  use f
  and_intros
  · apply huniq (hf c)
    apply Set.mem_biUnion (Order.mem_idealOfCofinals p₀ 𝒟)
    use 0
    simp [p₀]
  · intro x y hy
    obtain ⟨z, hz, h⟩ := hD x y
    obtain ⟨x', hx'⟩ := h (huniq (hf x) hz ▸ hy)
    use x'
    exact huniq (hf x') hx'
  · intro l u
    exact hG fun i ↦ hf (u i)

variable (n)

/-- Let `M` and `N` be countable nonstandard models of `𝗣𝗔` with the same standard system. If every
$\Pi_n$ formula satisfiable in `M` with the parameter `c` is satisfiable in `N`, with the parameter
`a`, below `b`, then `M` embeds onto a $\Sigma_n$-elementary initial segment of `N` which does not
contain `b`, with `c` sent to `a`.
- [Kay91, Theorem 12.3] -/
theorem exists_initialSegmentEmbedding (a b : N) (c : M)
    (hSSy : standardSystem M = standardSystem N)
    (h : ∀ θ : ArithmeticSemisentence 2, ℬ[<, ℒₒᵣ].Hierarchy 𝚷 n θ →
      (∃ x : M, M ⊧/![x, c] θ) → ∃ x < b, N ⊧/![x, a] θ) :
    ∃ ι : M ↪ₛ[ℒₒᵣ] N, (∀ x y, y < ι x → y ∈ Set.range ι) ∧
      IsElementary (fun {_} φ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n φ) ι ∧ ι c = a ∧ b ∉ Set.range ι := by
  obtain ⟨f, hfc, hfi, hf⟩ := exists_piWitnessBelow_comp hSSy h
  have hΓ {l : ℕ} {θ : ArithmeticSemisentence l} (hθ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n θ)
      (u : Fin l → M) : N ⊧/(f ∘ u) θ ↔ M ⊧/u θ := by
    constructor
    · contrapose
      intro hu
      simpa using (hf u).models (θ := ∼θ) (by simpa using hθ) (by simpa using hu)
    · intro hu
      cases n with
      | zero =>
        exact (hf u).models (.bounded _ _ _ <| Bounding.Hierarchy.zero_iff_bounded.mp hθ) hu
      | succ n =>
        obtain ⟨_, hψ, hθψ⟩ := exists_prenexHierarchy_of_hierarchy 𝗣𝗔 hθ
        obtain ⟨ψ, hψ₁, rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hψ
        obtain ⟨x, -, hx⟩ := hf u ψ (hψ₁.hierarchy.accum 𝚷) <| by
          simpa using (models_iff_of_provable_allClosure hθψ u).mp hu
        apply (models_iff_of_provable_allClosure hθψ _).mpr
        suffices ∃ x, N ⊧/(x :> f ∘ u) ψ by simpa using this
        use x
  have heq (x y : M) : f x = f y ↔ x = y := by
    simpa using hΓ (θ := “x y. x = y”) (by simp) ![x, y]
  have hlt (x y : M) : f x < f y ↔ x < y := by
    simpa using hΓ (θ := “x y. x < y”) (by simp) ![x, y]
  let ι : M ↪ₛ[ℒₒᵣ] N := {
    toFun := f
    func' g w := by
      cases g with
      | zero =>
        change f 0 = 0
        simpa using (hΓ (θ := “x. x = 0”) (by simp) ![0]).mpr (by simp)
      | one =>
        change f 1 = 1
        simpa using (hΓ (θ := “x. x = 1”) (by simp) ![1]).mpr (by simp)
      | add =>
        change f (w 0 + w 1) = f (w 0) + f (w 1)
        simpa using (hΓ (θ := “z x y. z = x + y”) (by simp) ![w 0 + w 1, w 0, w 1]).mpr (by simp)
      | mul =>
        change f (w 0 * w 1) = f (w 0) * f (w 1)
        simpa using (hΓ (θ := “z x y. z = x * y”) (by simp) ![w 0 * w 1, w 0, w 1]).mpr (by simp)
    rel' r w := by
      cases r
      · exact (heq _ _).mpr
      · exact (hlt _ _).mpr
    toFun_inj x y := (heq x y).mp
    rel_inv' r w := by
      cases r
      · exact (heq _ _).mp
      · exact (hlt _ _).mp }
  use ι
  and_intros
  · exact hfi
  · apply IsElementary.of_rew
    intro k m φ hφ ω u
    exact hΓ (hφ.rew ω) u
  · exact hfc
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy, h₁⟩ := hf ![x] “y x. y = x” (by simp) ⟨x, by simp⟩
    obtain rfl : y = f x := by simpa using h₁
    exact lt_irrefl _ hy

variable (a : M)

/-- Friedman's theorem: every countable nonstandard model of `𝗣𝗔` embeds onto a proper
$\Sigma_n$-elementary initial segment of itself containing a given element.
- [Kay91, Theorem 12.4] -/
theorem exists_selfEmbedding_onto_properInitialSegment :
    ∃ ι : M ↪ₛ[ℒₒᵣ] M, (∀ x y, y < ι x → y ∈ Set.range ι) ∧ ¬Function.Surjective ι ∧
      IsElementary (fun {_} φ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n φ) ι ∧ a ∈ Set.range ι := by
  have hQ := setOf_prenexHierarchy_mem_standardSystem 𝚷 n 2 (m := n + 1)
    (P := fun e : M ↦ ∃ z, PrenexFormulaSatisfied 𝚷 n (z ∷ a ∷ matrixToVec ![]) e) (by definability)
  simp only [← and_assoc] at hQ
  obtain ⟨b, hb⟩ := exists_forall_of_setOf_mem_standardSystem (m := n + 1) hQ
    (R := fun b e ↦ ∃ z < b, PrenexFormulaSatisfied 𝚷 n (z ∷ a ∷ matrixToVec ![]) e)
    (by definability) <| by
      intro s hs
      choose! z hz using fun φ hφ ↦ (hs φ hφ).2
      use ∑ φ ∈ s, z φ + 1
      intro φ hφ
      use z φ
      and_intros
      · exact lt_succ_iff_le.mpr (Finset.single_le_sum (by simp) hφ)
      · exact hz φ hφ
  obtain ⟨ι, hι, hel, hιa, hιb⟩ := exists_initialSegmentEmbedding n a b a rfl <| by
    rintro θ hθ ⟨x, hx⟩
    obtain ⟨ψ, hψ, hθψ⟩ := exists_prenexHierarchy_of_hierarchy 𝗣𝗔 hθ
    obtain ⟨z, hz, h⟩ := hb ψ <| by
      and_intros
      · exact hψ
      · use x
        exact (prenexFormulaSatisfied_adjoin_iff hψ _ _ _).mpr <|
          (models_iff_of_provable_allClosure hθψ _).mp hx
    use z
    and_intros
    · exact hz
    · exact (models_iff_of_provable_allClosure hθψ _).mpr <|
        (prenexFormulaSatisfied_adjoin_iff hψ _ _ _).mp h
  use ι
  and_intros
  · exact hι
  · intro h
    exact hιb (h b)
  · exact hel
  · use a

/-- Friedman's theorem for cuts: every countable nonstandard model of `𝗣𝗔` is isomorphic to a proper
closed cut of itself which contains a given element and is a $\Sigma_n$-elementary substructure.
- [Kay91, Theorem 12.4] -/
theorem exists_proper_closedCut_iso : ∃ I : ClosedCut M, I.Proper ∧ a ∈ I.carrier ∧
      IsElementary (fun {_} φ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n φ) I.endExtension.emb ∧
      Nonempty (M ≃ₛ[ℒₒᵣ] I.carrier) := by
  obtain ⟨ι, hι, hsurj, hel, ha⟩ := exists_selfEmbedding_onto_properInitialSegment n a
  use .ofEmbedding ι hι
  and_intros
  · constructor
    · exact (ClosedCut.ofEmbedding ι hι).zero_mem
    · simpa [Function.Surjective] using hsurj
  · exact ha
  · exact hel.of_comp_iso (ClosedCut.isoOfEmbedding ι hι) <|
      ClosedCut.endExtension_isoOfEmbedding ι hι
  · exact ⟨ClosedCut.isoOfEmbedding ι hι⟩

end

end FFL.FirstOrder.Arithmetic
