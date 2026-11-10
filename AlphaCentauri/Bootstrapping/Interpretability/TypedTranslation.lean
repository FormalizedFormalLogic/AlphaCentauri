module

public import AlphaCentauri.Bootstrapping.Interpretability.Soundness
public import AlphaCentauri.Bootstrapping.Interpretability.RelativizedBlocks

/-!
# Typed translations along a table

The translation along a table of a typed formula is a typed formula, and the translation of a block
of quantifiers is a block of quantifiers relativized to the domain.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open _root_.FFL.Entailment


/-! ## Typed translations -/

section typed

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] {tbl : V} (hT : IsTable L₁ L₂ tbl)

/-- The translation along a table of a typed formula, as a typed formula. -/
noncomputable def IsTable.transT {n : ℕ} (φ : Semiformula V L₂ n) : Semiformula V L₁ n :=
  ⟨translate L₁ L₂ tbl φ.val, IsSemiformula.translate hT φ.isSemiformula⟩

namespace IsTable

@[simp] lemma transT_val {n : ℕ} (φ : Semiformula V L₂ n) :
    (hT.transT φ).val = translate L₁ L₂ tbl φ.val := rfl

@[simp] lemma transT_verum {n : ℕ} : hT.transT (⊤ : Semiformula V L₂ n) = ⊤ := by
  ext; simp

@[simp] lemma transT_falsum {n : ℕ} : hT.transT (⊥ : Semiformula V L₂ n) = ⊥ := by
  ext; simp

@[simp] lemma transT_and {n : ℕ} (φ ψ : Semiformula V L₂ n) :
    hT.transT (φ ⋏ ψ) = hT.transT φ ⋏ hT.transT ψ := by
  ext; simp [φ.isSemiformula.isUFormula, ψ.isSemiformula.isUFormula]

@[simp] lemma transT_or {n : ℕ} (φ ψ : Semiformula V L₂ n) :
    hT.transT (φ ⋎ ψ) = hT.transT φ ⋎ hT.transT ψ := by
  ext; simp [φ.isSemiformula.isUFormula, ψ.isSemiformula.isUFormula]

@[simp] lemma transT_neg {n : ℕ} (φ : Semiformula V L₂ n) :
    hT.transT (∼φ) = ∼hT.transT φ := by
  ext; simp [translate_neg hT φ.isSemiformula]

@[simp] lemma transT_imp {n : ℕ} (φ ψ : Semiformula V L₂ n) :
    hT.transT (φ 🡒 ψ) = hT.transT φ 🡒 hT.transT ψ := by
  simp [Semiformula.imp_def]

@[simp] lemma transT_iff {n : ℕ} (φ ψ : Semiformula V L₂ n) :
    hT.transT (φ 🡘 ψ) = hT.transT φ 🡘 hT.transT ψ := by
  simp [LogicalConnective.iff]

@[simp] lemma transT_conj {n m : ℕ} (v : Fin m → Semiformula V L₂ n) :
    hT.transT (Matrix.conj v) = Matrix.conj fun i ↦ hT.transT (v i) :=
  Matrix.conj_map hT.transT (transT_verum hT) (transT_and hT) v

lemma domainAt_zero_typed {n : ℕ} :
    domainAt L₁ tbl 0 = (hT.domT.subst ![Semiterm.bvar 0] : Semiformula V L₁ (n + 1)).val := by
  rw [Semiformula.val_substs, domT_val, domainAt]
  simp

@[simp] lemma transT_all {n : ℕ} (φ : Semiformula V L₂ (n + 1)) :
    hT.transT (∀¹ φ) = ∀¹ (hT.domT.subst ![Semiterm.bvar 0] 🡒 hT.transT φ) := by
  ext
  simp [φ.isSemiformula.isUFormula, domainAt_zero_typed hT (n := n)]

@[simp] lemma transT_exs {n : ℕ} (φ : Semiformula V L₂ (n + 1)) :
    hT.transT (∃¹ φ) = ∃¹ (hT.domT.subst ![Semiterm.bvar 0] ⋏ hT.transT φ) := by
  ext
  simp [φ.isSemiformula.isUFormula, domainAt_zero_typed hT (n := n)]

lemma transT_allItr {n : ℕ} : ∀ (k : ℕ) (φ : Semiformula V L₂ (n + k)),
    hT.transT (∀¹^[k] φ) = relAllItr hT.domT k (hT.transT φ)
  | 0, φ => rfl
  | k + 1, φ => by
    rw [allItr_succ, transT_allItr k, transT_all, relAllItr_succ]

lemma translate_qqAlls : ∀ {n : ℕ} (φ : Semiformula V L₂ n),
    translate L₁ L₂ tbl (qqAlls φ.val n) = (relAlls hT.domT (hT.transT φ)).val
  | 0, φ => by simp [relAlls]
  | n + 1, φ => by
    have h := translate_qqAlls (∀¹ φ)
    rw [Semiformula.val_all, ← qqAlls_succ', transT_all] at h
    rw [show ((n + 1 : ℕ) : V) = (n : V) + 1 by simp, h]
    rfl

lemma transT_shift {n : ℕ} (φ : Semiformula V L₂ n) :
    hT.transT φ.shift = (hT.transT φ).shift := by
  ext; simp [translate_shift hT φ.isSemiformula]

lemma transT_free (φ : Semiformula V L₂ 1) : hT.transT φ.free = (hT.transT φ).free := by
  ext
  simpa using translate_free hT (by simp)

end IsTable

/-- A vector of terms each of which is a variable. -/
def IsVarVec {L : Language} [L.Encodable] [L.LORDefinable] {n m : ℕ}
    (w : SemitermVec V L n m) : Prop :=
  ∀ i, (∃ z, w i = Semiterm.bvar z) ∨ (∃ x, w i = Semiterm.fvar x)

lemma IsTable.transT_subst {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {tbl : V}
    (hT : IsTable L L tbl) {n m : ℕ} (w : SemitermVec V L n m) (hw : IsVarVec w)
    (φ : Semiformula V L n) : hT.transT (φ.subst w) = (hT.transT φ).subst w := by
  ext
  simp only [IsTable.transT_val, Semiformula.val_substs]
  apply translate_subst hT w.isSemitermVec ?_ φ.isSemiformula
  intro i hi
  obtain ⟨i, rfl⟩ := eq_fin_of_lt_nat hi
  rw [SemitermVec.val_nth_eq]
  rcases hw i with ⟨z, hz⟩ | ⟨x, hx⟩
  · exact Or.inl ⟨z, by simp [hz]⟩
  · exact Or.inr ⟨x, by simp [hx]⟩

end typed

end FFL.FirstOrder.Arithmetic.Bootstrapping
