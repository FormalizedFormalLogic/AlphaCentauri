module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
public import Foundation.FirstOrder.Incompleteness.Consistency

/-!
# $\Delta_1$ numerations whose elements are sentences

$\Delta_1$ numerations of theories whose elements are sentences.
-/

set_option linter.style.repeatedBinder false

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every element of the numeration, in every model of $\mathsf{I}\Sigma_1$, is a sentence. -/
class Theory.Δ₁.Sentential (T : Theory L) [T.Δ₁] : Prop where
  isSentence {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {p : V}
    (h : p ∈ T.Δ₁Class) : L.IsSentence p

lemma Theory.Δ₁.Sentential.forall_isSentence (T : Theory L) [T.Δ₁]
    [Theory.Δ₁.Sentential T] {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    ∀ p ∈ T.Δ₁Class (V := V), L.IsSentence p := by
  have h : 𝗜𝚺₁ ⊢ (“∀ p, !T.Δ₁ch.sigma.val p →
      !(Arithmetic.Bootstrapping.isSentence L).sigma.val p” : ArithmeticSentence) :=
    Arithmetic.complete.{0} _ _ fun W _ _ ↦ by
      simpa [models_iff, Bounding.HierarchySymbol.Semiformula.val_sigma] using
        fun p hp ↦ isSentence (T := T) (V := W) (p := p) hp
  have h₁ : ∀ p : V, p ∈ T.Δ₁Class → L.IsSentence p := by
    simpa [models_iff, Bounding.HierarchySymbol.Semiformula.val_sigma] using
      models_of_provable (M := V) inferInstance h
  exact h₁

instance Theory.Δ₁.Sentential.union (T U : Theory L) [T.Δ₁] [U.Δ₁] [Theory.Δ₁.Sentential T]
    [Theory.Δ₁.Sentential U] : Theory.Δ₁.Sentential (T ∪ U) where
  isSentence h := by
    rcases Theory.Δ₁Class.mem_union.mp h with h | h
    · exact Theory.Δ₁.Sentential.isSentence h
    · exact Theory.Δ₁.Sentential.isSentence h

instance Theory.Δ₁.Sentential.singleton (σ : Sentence L) : Theory.Δ₁.Sentential {σ} where
  isSentence {V} _ _ p h := by
    have hp : p = ⌜σ⌝ := by
      change V ⊧/![p] ({σ} : Theory L).Δ₁ch.val at h
      rw [Theory.Δ₁.singleton_toTDef_ch_val] at h
      simpa [Sentence.quote_eq_encode, Arithmetic.numeral_eq_natCast] using h
    rw [hp]
    exact .quote σ

/-- The numeration of `T` restricted to the codes of sentences. -/
noncomputable abbrev Theory.Δ₁.sentential (T : Theory L) (d : T.Δ₁) : T.Δ₁ where
  ch := T.Δ₁ch ⋏ Arithmetic.Bootstrapping.isSentence L
  mem_iff φ := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
      Bounding.HierarchySymbol.Semiformula.val_and, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq]
    rw [d.mem_iff φ]
    constructor
    · intro h
      exact h.1
    · rintro ⟨σ, hσ, rfl⟩
      apply And.intro ⟨σ, hσ, rfl⟩
      change ℕ ⊧/![_] (Arithmetic.Bootstrapping.isSentence L).sigma.val
      rw [Arithmetic.Bootstrapping.isSentence_sigma_iff]
      exact .quote σ
  isDelta1 :=
    Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
      (fun V _ _ ↦
        Bounding.HierarchySymbol.Semiformula.ProperOn.and (by simp)
          Language.IsSentence.defined.proper)

lemma Theory.Δ₁.isSentence_of_sentential (T : Theory L) (d : T.Δ₁) {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {p : V} (h : V ⊧/![p] (Theory.Δ₁.sentential T d).ch.val) :
    L.IsSentence p :=
  (Arithmetic.Bootstrapping.isSentence_sigma_iff p).mp h.2

instance (T : Theory L) (d : T.Δ₁) : @Theory.Δ₁.Sentential L _ _ T (Theory.Δ₁.sentential T d) :=
  @Theory.Δ₁.Sentential.mk L _ _ T (Theory.Δ₁.sentential T d) fun h ↦
    Theory.Δ₁.isSentence_of_sentential T d h

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma Theory.Δ₁.sentential_subset (T : Theory L) (d : T.Δ₁) :
    @Theory.Δ₁Class V _ L _ _ T (Theory.Δ₁.sentential T d) ⊆ T.Δ₁Class := by
  intro p h
  change V ⊧/![p] T.Δ₁ch.val
  have h₁ := h.1
  rw [Bounding.HierarchySymbol.Semiformula.val_sigma] at h₁
  exact h₁

lemma Theory.Δ₁.sentential_consistent (T : Theory L) [d : T.Δ₁] (h : T.Consistent V) :
    letI := Theory.Δ₁.sentential T d
    T.Consistent V := by
  intro hp
  apply h
  have h₁ := (@Arithmetic.Bootstrapping.internal_provable_iff_internal_derivable V _ _ L _ _ T
    (Theory.Δ₁.sentential T d) _).mp hp
  have h₂ := @Arithmetic.Bootstrapping.Derivable.of_ss V _ _ L _ _ T T
    (Theory.Δ₁.sentential T d) d (Theory.Δ₁.sentential_subset T d) _ h₁
  exact (Arithmetic.Bootstrapping.internal_provable_iff_internal_derivable).mpr h₂

end FFL.FirstOrder
