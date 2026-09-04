module

public import AlphaCentauri.Bootstrapping.Prenex
public import AlphaCentauri.Bootstrapping.PartialTruth.SatZero

/-!
# Satisfaction for prenex `Σₙ` and `Πₙ` formulas

This module defines satisfaction predicates for the internally coded strict prenex hierarchy.
It states their definability, Tarski conditions, duality, monotonicity, and substitution laws.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

mutual
  /-- `SatSigma n z e` says that the strict prenex `Σₙ` formula `z` is satisfied by `e`.
  A positive level peels a block of existential quantifiers and prepends its witnesses to `e`.
  - [HP98, Definition I.1.74] -/
  def SatSigma : ℕ → V → V → Prop
    | 0 => SatZero
    | n + 1 => fun z e ↦
        ∃ k q, z = qqExss q k ∧ IsStrictPi n q ∧
          ∃ w, len w = k ∧ SatPi n q (vecAppend w e)

  /-- `SatPi n z e` says that the strict prenex `Πₙ` formula `z` is satisfied by `e`.
  At a positive level it is defined by duality through coded negation.
  - [HP98, Definition I.1.74] -/
  def SatPi : ℕ → V → V → Prop
    | 0 => SatZero
    | n + 1 => fun z e ↦
        IsStrictPi (n + 1) z ∧ IsUFormula ℒₒᵣ z ∧ ¬SatSigma (n + 1) (neg ℒₒᵣ z) e
end

/-- Builds the `𝚷ₘ₊₁` formula for `SatPi (m + 1)` from the `𝚺ₘ₊₁` formula for `SatSigma (m + 1)`:
`Πₘ₊₁` satisfaction is membership in the domain together with failure of `Σₘ₊₁` satisfaction of
the negation.
- [HP98, Definition I.1.74] -/
noncomputable def piOfSigma (m : ℕ) (σ : 𝚺-[m + 1].Semisentence 2) :
    𝚷-[m + 1].Semisentence 2 := .mkPi
  “z e. !(isStrictPi (m + 1)).pi z ∧ !(isUFormula ℒₒᵣ).pi z ∧
    ∀ nz, !(negGraph ℒₒᵣ).val nz z → ¬!σ.val nz e”
  (by
    have h1 : Hierarchy 𝚷 (m + 1) (isStrictPi (m + 1)).pi.val :=
      (isStrictPi (m + 1)).pi.pi_prop.mono (Nat.le_add_left 1 m)
    have h2 : Hierarchy 𝚷 (m + 1) (isUFormula ℒₒᵣ).pi.val :=
      (isUFormula ℒₒᵣ).pi.pi_prop.mono (Nat.le_add_left 1 m)
    have h3 : Hierarchy 𝚺 (m + 1) (negGraph ℒₒᵣ).val :=
      (negGraph ℒₒᵣ).sigma_prop.mono (Nat.le_add_left 1 m)
    have h4 : Hierarchy 𝚺 (m + 1) σ.val := σ.sigma_prop
    simp [h1, h2, h3, h4])

/-- Builds the `𝚺ₘ₊₂` formula for `SatSigma (m + 2)` from the `𝚷ₘ₊₁` formula for `SatPi (m + 1)`,
by peeling one block of existential quantifiers off a strict `Πₘ₊₁` matrix.
- [HP98, Definition I.1.74] -/
noncomputable def sigmaOfPi (m : ℕ) (π : 𝚷-[m + 1].Semisentence 2) :
    𝚺-[m + 2].Semisentence 2 := .mkSigma
  “z e. ∃ k q w e', !qqExssDef z q k ∧ !(isStrictPi (m + 1)).val q ∧ !lenDef k w ∧
    !vecAppendDef e' w e ∧ !π.val q e'”
  (by
    have h1 : Hierarchy 𝚺 (m + 2) qqExssDef.val :=
      qqExssDef.sigma_prop.mono (show 1 ≤ m + 2 by omega)
    have h2 : Hierarchy 𝚺 (m + 2) (isStrictPi (m + 1)).val :=
      (isStrictPi (m + 1)).sigma.sigma_prop.mono (show 1 ≤ m + 2 by omega)
    have h3 : Hierarchy 𝚺 (m + 2) lenDef.val :=
      lenDef.sigma_prop.mono (show 1 ≤ m + 2 by omega)
    have h4 : Hierarchy 𝚺 (m + 2) vecAppendDef.val :=
      vecAppendDef.sigma_prop.mono (show 1 ≤ m + 2 by omega)
    have h5 : Hierarchy 𝚺 (m + 2) π.val := π.pi_prop.accum 𝚺
    simp [h1, h2, h3, h4, h5])

/-- The `𝚺₁` formula for `satSigma 0`, i.e. for `SatSigma 1`: an existential block over a strict
`Π₀ = Δ₀` matrix, tested against `satZero` (since `SatPi 0` is definitionally `SatZero`).
- [HP98, Definition I.1.74] -/
noncomputable def sigmaZero : 𝚺-[1].Semisentence 2 := .mkSigma
  “z e. ∃ k q w e', !qqExssDef z q k ∧ !(isStrictPi 0).val q ∧ !lenDef k w ∧
    !vecAppendDef e' w e ∧ !satZero.val q e'”
  (by
    have h1 : Hierarchy 𝚺 1 qqExssDef.val := qqExssDef.sigma_prop
    have h2 : Hierarchy 𝚺 1 (isStrictPi 0).val := (isStrictPi 0).sigma.sigma_prop
    have h3 : Hierarchy 𝚺 1 lenDef.val := lenDef.sigma_prop
    have h4 : Hierarchy 𝚺 1 vecAppendDef.val := vecAppendDef.sigma_prop
    have h5 : Hierarchy 𝚺 1 satZero.val :=
      HierarchySymbol.Semiformula.val_sigma satZero ▸ satZero.sigma.sigma_prop
    simp [h1, h2, h3, h4, h5])

/-- The `𝚺ₙ₊₁` formula defining `SatSigma (n + 1)`, with arguments `(z, e)`, by recursion on `n`.
- [HP98, Definition I.1.74]
- [HP98, Theorem I.1.75(1)] -/
noncomputable def satSigma : (n : ℕ) → 𝚺-[n + 1].Semisentence 2
  | 0 => sigmaZero
  | n + 1 => sigmaOfPi n (piOfSigma n (satSigma n))

/-- The `𝚷ₙ₊₁` formula defining `SatPi (n + 1)`, with arguments `(z, e)`.
- [HP98, Definition I.1.74]
- [HP98, Theorem I.1.75(1)] -/
noncomputable def satPi (n : ℕ) : 𝚷-[n + 1].Semisentence 2 := piOfSigma n (satSigma n)

/-- `satPi` unfolds to `piOfSigma` applied to `satSigma` at the same level; recorded so `satSigma`'s
successor equation reads directly in terms of `satPi`.
- [HP98, Definition I.1.74] -/
private lemma satSigma_succ (n : ℕ) : satSigma (n + 1) = sigmaOfPi n (satPi n) := rfl

/-- Derives definedness of `piOfSigma m σ` for `SatPi (m + 1)` from definedness of `σ` for
`SatSigma (m + 1)`.
- [HP98, Theorem I.1.75(1)] -/
private lemma piDefined_of_sigmaDefined {m : ℕ} {σ : 𝚺-[m + 1].Semisentence 2}
    (hσ : 𝚺-[m + 1]-Relation (SatSigma (m + 1) : V → V → Prop) via σ) :
    𝚷-[m + 1]-Relation (SatPi (m + 1) : V → V → Prop) via piOfSigma m σ := .mk fun v ↦ by
  have := hσ
  simp [piOfSigma, SatPi]

/-- Derives definedness of `sigmaOfPi m π` for `SatSigma (m + 2)` from definedness of `π` for
`SatPi (m + 1)`.
- [HP98, Theorem I.1.75(1)] -/
private lemma sigmaDefined_of_piDefined {m : ℕ} {π : 𝚷-[m + 1].Semisentence 2}
    (hπ : 𝚷-[m + 1]-Relation (SatPi (m + 1) : V → V → Prop) via π) :
    𝚺-[m + 2]-Relation (SatSigma (m + 2) : V → V → Prop) via sigmaOfPi m π := .mk fun v ↦ by
  have := hπ
  simp [sigmaOfPi, SatSigma]

/-- Definedness of `sigmaZero` for `SatSigma 1`.
- [HP98, Theorem I.1.75(1)] -/
private lemma sigmaZero_defined :
    𝚺-[1]-Relation (SatSigma 1 : V → V → Prop) via sigmaZero := .mk fun v ↦ by
  simp [sigmaZero, SatSigma, SatPi]

/-- Definedness of `satSigma n` for `SatSigma (n + 1)`, by recursion on `n`, deriving definedness
of `satPi n` for `SatPi (n + 1)` along the way.
- [HP98, Theorem I.1.75(1)] -/
private lemma sigmaDefined : ∀ n : ℕ, 𝚺-[n + 1]-Relation (SatSigma (n + 1) : V → V → Prop) via satSigma n
  | 0 => sigmaZero_defined
  | n + 1 => by
    rw [satSigma_succ]
    exact sigmaDefined_of_piDefined (piDefined_of_sigmaDefined (sigmaDefined n))

/-- The formula `satSigma n` defines satisfaction for strict prenex `Σₙ₊₁` formulas.
- [HP98, Theorem I.1.75(1)] -/
instance SatSigma.defined (n : ℕ) :
    𝚺-[n + 1]-Relation (SatSigma (n + 1) : V → V → Prop) via satSigma n := sigmaDefined n

/-- The formula `satPi n` defines satisfaction for strict prenex `Πₙ₊₁` formulas.
- [HP98, Theorem I.1.75(1)] -/
instance SatPi.defined (n : ℕ) :
    𝚷-[n + 1]-Relation (SatPi (n + 1) : V → V → Prop) via satPi n :=
  piDefined_of_sigmaDefined (sigmaDefined n)

/-- Satisfaction for strict prenex `Σₙ₊₁` formulas is definable at level `Σₙ₊₁`.
- [HP98, Theorem I.1.75(1)] -/
instance SatSigma.definable (n : ℕ) :
    𝚺-[n + 1]-Relation (SatSigma (n + 1) : V → V → Prop) :=
  (SatSigma.defined n).to_definable

/-- Satisfaction for strict prenex `Πₙ₊₁` formulas is definable at level `Πₙ₊₁`.
- [HP98, Theorem I.1.75(1)] -/
instance SatPi.definable (n : ℕ) :
    𝚷-[n + 1]-Relation (SatPi (n + 1) : V → V → Prop) :=
  (SatPi.defined n).to_definable

/-- At level zero, strict `Σ` satisfaction is `Δ₀` satisfaction.
- [HP98, Definition I.1.74] -/
@[simp] lemma SatSigma.zero : SatSigma 0 = (SatZero : V → V → Prop) := by simp [SatSigma]

/-- At level zero, strict `Π` satisfaction is `Δ₀` satisfaction.
- [HP98, Definition I.1.74] -/
@[simp] lemma SatPi.zero : SatPi 0 = (SatZero : V → V → Prop) := by simp [SatPi]

/-! ## Tarski conditions -/

/-- Strict `Σₙ` satisfaction implies membership in its syntactic domain.
- [HP98, Theorem I.1.75(2)] -/
axiom SatSigma.dom {n : ℕ} {z e : V} :
    SatSigma n z e → IsStrictSigma n z ∧ IsUFormula ℒₒᵣ z

/-- Strict `Πₙ` satisfaction implies membership in its syntactic domain.
- [HP98, Theorem I.1.75(2)] -/
axiom SatPi.dom {n : ℕ} {z e : V} :
    SatPi n z e → IsStrictPi n z ∧ IsUFormula ℒₒᵣ z

/-- An empty existential block reads a strict `Πₙ` formula as a `Σₙ₊₁` formula.
- [HP98, Theorem I.1.75(2)(v)] -/
axiom SatSigma.of_pi {n : ℕ} {z e : V} (hz : IsStrictPi n z)
    (hz' : IsUFormula ℒₒᵣ z) : SatSigma (n + 1) z e ↔ SatPi n z e

/-- An empty universal block reads a strict `Σₙ` formula as a `Πₙ₊₁` formula.
- [HP98, Theorem I.1.75(2)(v′)] -/
axiom SatPi.of_sigma {n : ℕ} {z e : V} (hz : IsStrictSigma n z)
    (hz' : IsUFormula ℒₒᵣ z) : SatPi (n + 1) z e ↔ SatSigma n z e

/-- Satisfaction of an existential formula is existential satisfaction of its body.
- [HP98, Theorem I.1.75(2)(v)] -/
axiom SatSigma.exs_iff {n : ℕ} {p e : V} :
    SatSigma (n + 1) (^∃ p) e ↔ ∃ x, SatSigma (n + 1) p (x ∷ e)

/-- Satisfaction of a universal formula is universal satisfaction of its body.
- [HP98, Theorem I.1.75(2)(v′)] -/
axiom SatPi.all_iff {n : ℕ} {p e : V} :
    SatPi (n + 1) (^∀ p) e ↔ ∀ x, SatPi (n + 1) p (x ∷ e)

/-- Satisfaction of a strict `Σₘ` formula is stable when viewed at a higher `Σ` level.
- [HP98, Theorem I.1.75(2)(v)] -/
axiom SatSigma.mono {m n : ℕ} (h : m ≤ n) {z e : V} (hz : IsStrictSigma m z)
    (hz' : IsUFormula ℒₒᵣ z) : SatSigma m z e ↔ SatSigma n z e

/-- Satisfaction of a strict `Πₘ` formula is stable when viewed at a higher `Π` level.
- [HP98, Theorem I.1.75(2)(v′)] -/
axiom SatPi.mono {m n : ℕ} (h : m ≤ n) {z e : V} (hz : IsStrictPi m z)
    (hz' : IsUFormula ℒₒᵣ z) : SatPi m z e ↔ SatPi n z e

/-- `Πₙ` satisfaction of a negated strict `Σₙ` formula is failure of `Σₙ` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
axiom SatPi.neg_iff {n : ℕ} {z e : V} (hz : IsStrictSigma n z)
    (hz' : IsUFormula ℒₒᵣ z) : SatPi n (neg ℒₒᵣ z) e ↔ ¬SatSigma n z e

/-- `Σₙ` satisfaction of a negated strict `Πₙ` formula is failure of `Πₙ` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
axiom SatSigma.neg_iff {n : ℕ} {z e : V} (hz : IsStrictPi n z)
    (hz' : IsUFormula ℒₒᵣ z) : SatSigma n (neg ℒₒᵣ z) e ↔ ¬SatPi n z e

/-- Strict `Σₙ` satisfaction commutes with substitution of a coded vector of terms.
- [HP98, Theorem I.1.75(2)] -/
axiom SatSigma.subst {n : ℕ} {m l w p e : V} (hw : IsSemitermVec ℒₒᵣ m l w)
    (hp : IsSemiformula ℒₒᵣ m p) (hp' : IsStrictSigma n p) :
    SatSigma n (subst ℒₒᵣ w p) e ↔ SatSigma n p (termValVec e m w)

/-! ## Satisfaction under an externally supplied vector -/

/-- `satSigmaVec n k` defines `SatSigma (n + 1)` under the vector formed by its `k`
free variables. This is the formula used by the corresponding induction scheme.

- [HP98, Remark I.1.77]
- [HP98, Definition I.1.78(2)] -/
noncomputable def satSigmaVec (n k : ℕ) : 𝚺-[n + 1].Semisentence (k + 1) := .mkSigma
  “p. ∃ e, !lenDef ↑k e ∧
    (⋀ i, ∃ z, !nthDef z e ↑(i : Fin k).val ∧ z = #i.succ.succ.succ) ∧
    !(satSigma n).val p e”
  (by simp [lenDef.sigma_prop.mono (Nat.le_add_left 1 n),
    nthDef.sigma_prop.mono (Nat.le_add_left 1 n)])

/-- The formula `satSigmaVec n k` defines strict `Σₙ₊₁` satisfaction under its variables.
- [HP98, Remark I.1.77]
- [HP98, Definition I.1.78(2)] -/
theorem satSigmaVec.defined (n k : ℕ) :
    𝚺-[n + 1].Defined
      (fun v : Fin (k + 1) → V ↦ SatSigma (n + 1) (v 0) (matrixToVec (v ·.succ)))
      (satSigmaVec n k) := .mk fun v ↦ by
  simp only [satSigmaVec, Nat.succ_eq_add_one, Nat.reduceAdd, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_ex, LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp₂,
    Semiterm.val_operator, Matrix.comp₀, Structure.numeral_eq_numeral, numeral_eq_natCast_app, Semiterm.val_bvar,
    Matrix.cons_val_zero, HierarchySymbol.Defined.iff, Fin.isValue, Fin.Fin1.eq_one, Fin.succ_zero_eq_one,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.conj_hom_prop, Matrix.comp₃, Fin.succ_one_eq_two,
    Matrix.cons_app_two, Semiformula.eval_operator, Matrix.cons_val_succ, Structure.eq_iff_eq,
    LogicalConnective.Prop.and_eq, exists_eq_left]
  constructor
  · rintro ⟨x, hlen, hnth, hsat⟩
    have hx : x = matrixToVec (v ·.succ) := by
      apply nth_ext' (k : V) hlen.symm (by simp)
      intro i hi
      obtain ⟨j, rfl⟩ := lt_numeral_iff.mp (by simpa [← numeral_eq_natCast_app] using hi)
      simp [numeral_eq_natCast_app, hnth j]
    rwa [hx] at hsat
  · intro hsat
    exact ⟨matrixToVec (v ·.succ), by simp, fun i ↦ matrixToVec_nth _ i, hsat⟩

end LO.FirstOrder.Arithmetic.Bootstrapping
