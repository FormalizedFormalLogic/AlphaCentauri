module

public import AlphaCentauri.Bootstrapping.Proof.InductionAxiom
public import AlphaCentauri.Bootstrapping.Proof.PeanoMinusAxiom

/-!
# Replacing the axioms of $\mathsf{I}\Sigma_n$ by false blocks

Every axiom `p` of the internal $\mathsf{I}\Sigma_n$ has a replacement `q` such that `p` follows in
pure logic from the negation of `q`. For $n \le k$, in a model of $\mathsf{I}\Sigma^+_{k+1}$, the
negation of a replacement is a block of existential quantifiers over a closed matrix in
`IsReadable k 3` all of whose instances are false.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `q` is the replacement of the axiom `p` of `𝗜𝚺 n`: an axiom of $\mathsf{PA}^-$ is its own
replacement, and an induction axiom is replaced by the prenex form of the induction axiom of the
matrix it is built from. -/
def IsAxiomReplacement (n : ℕ) (p q : V) : Prop :=
  Derivable (∅ : Theory ℒₒᵣ) (insert (neg ℒₒᵣ q) ({p} : V)) ∧
    ((p ∈ (𝗣𝗔⁻ : ArithmeticTheory).Δ₁Class ∧ q = p) ∨
      ∃ m ≤ p, ∃ Z ≤ p, IsInductionMatrix n m Z ∧ q = prenexInductionAxiom m Z)

instance IsAxiomReplacement.definable (n : ℕ) :
    𝚺ᴬ₁-Relation (IsAxiomReplacement n : V → V → Prop) := by
  unfold IsAxiomReplacement
  definability

theorem exists_isAxiomReplacement {n : ℕ} {p : V} (hp : p ∈ (𝗜𝚺n).Δ₁Class) :
    ∃ q, IsAxiomReplacement n p q := by
  rcases InductionOnPrenexHierarchy.mem_Δ₁Class_iff.mp hp with h | h
  · exact ⟨p, derivable_of_mem_peanoMinus_Δ₁Class h, Or.inl ⟨h, rfl⟩⟩
  · obtain ⟨m, hm, Z, hZ, hM, hd⟩ := exists_derivable_prenexInductionAxiom h
    exact ⟨_, hd, Or.inr ⟨m, hm, Z, hZ, hM, rfl⟩⟩

theorem IsAxiomReplacement.isFalseBlock {n k : ℕ} [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)] (hn : n ≤ k)
    {p q : V} (h : IsAxiomReplacement n p q) : IsFalseBlock k 3 (neg ℒₒᵣ q) := by
  rcases h.2 with ⟨hp, rfl⟩ | ⟨m, -, Z, -, hM, rfl⟩
  · exact isFalseBlock_neg_of_mem_peanoMinus_Δ₁Class hp k 3
  · exact hM.isFalseBlock_neg_prenexInductionAxiom hn

end FFL.FirstOrder.Arithmetic.Bootstrapping
