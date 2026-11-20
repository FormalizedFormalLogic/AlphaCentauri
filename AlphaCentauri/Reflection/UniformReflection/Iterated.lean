module

public import AlphaCentauri.Reflection.Definability.UniformReflectionCode
public import AlphaCentauri.Reflection.Provability.IteratedConsistency

@[expose] public section
/-!
# Iterated uniform reflection

The tower of iterated uniform $\Pi_n$ reflection, $(T)^n_0 = T$ and
$(T)^n_{m + 1} = (T)^n_m + \mathrm{RFN}_{(T)^n_m}(\Pi_n)$, is $\Delta_1$ at every stage; for $n = 1$
it is the tower of iterated consistency.

- [Bek99, §5]
-/

open scoped FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁]

section

/-- The pair of the `m`-th stage of iterated uniform $\Pi_n$ reflection over `T` and its
$\Delta_1$ presentation. -/
noncomputable def _root_.FFL.FirstOrder.Theory.iterUniformReflectionSigma
    (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) : ℕ → Σ' U : ArithmeticTheory, U.Δ₁
  | 0 => ⟨T, ‹_›⟩
  | m + 1 =>
    match T.iterUniformReflectionSigma n m with
    | ⟨U, hU⟩ => letI := hU; ⟨U ∪ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 n] U, inferInstance⟩

/-- The `m`-th stage $(T)^n_m$ of iterated uniform $\Pi_n$ reflection over `T`: $(T)^n_0 = T$ and
$(T)^n_{m + 1} = (T)^n_m + \mathrm{RFN}_{(T)^n_m}(\Pi_n)$.
- [Bek99, §5] -/
noncomputable def _root_.FFL.FirstOrder.Theory.iterUniformReflection (T : ArithmeticTheory) [T.Δ₁]
    (n m : ℕ) : ArithmeticTheory :=
  (T.iterUniformReflectionSigma n m).1

variable (T) (n : ℕ)

noncomputable instance (m : ℕ) : (T.iterUniformReflection n m).Δ₁ :=
  (T.iterUniformReflectionSigma n m).2

@[simp] lemma iterUniformReflection_zero : T.iterUniformReflection n 0 = T := rfl

lemma iterUniformReflection_succ (m : ℕ) :
    T.iterUniformReflection n (m + 1) =
      T.iterUniformReflection n m ∪
        𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 n] (T.iterUniformReflection n m) := rfl

end

/-- Iterated uniform $\Pi_1$ reflection is iterated consistency. -/
axiom iterUniformReflection_one_equiv_iterCon [𝗜𝚺₁ ⪯ T] (m : ℕ) :
    T.iterUniformReflection 1 m ≊ T.iterCon m

end FFL.FirstOrder.Arithmetic
