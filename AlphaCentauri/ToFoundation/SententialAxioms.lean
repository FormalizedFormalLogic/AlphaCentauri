module

public import Foundation.FirstOrder.Incompleteness.Consistency

/-!
# $\Delta_1$ numerations whose elements are sentences

A $\Delta_1$ numeration of a theory in a nonstandard model may contain codes of formulas with free
variables. Restricting the numeration to the codes fixed by the shift of free variables gives a
numeration of the same theory whose elements are all sentences, and it has a weaker consistency
statement.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace Arithmetic.Bootstrapping

variable (L) in
/-- The codes fixed by the shift of free variables. -/
noncomputable def shiftFixed : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “x. !(shiftGraph L) x x”)
  (.mkPi “x. ∀ y, !(shiftGraph L) y x → y = x”)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma shiftFixed_sigma_iff (x : V) :
    V ⊧/![x] (shiftFixed L).sigma.val ↔ shift L x = x := by
  simp [shiftFixed, eq_comm]

lemma shiftFixed_pi_iff (x : V) :
    V ⊧/![x] (shiftFixed L).pi.val ↔ shift L x = x := by
  simp [shiftFixed]

lemma shiftFixed_properOn : (shiftFixed L).ProperOn V := by
  intro e
  rw [Matrix.fun_eq_vec_one e]
  simp [shiftFixed_sigma_iff, shiftFixed_pi_iff]

end Arithmetic.Bootstrapping

/-- Every element of the numeration, in every model of $\mathsf{I}\Sigma_1$, is a sentence. -/
class Theory.Δ₁.Sentential (T : Theory L) [T.Δ₁] : Prop where
  shift_eq {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {p : V}
    (h : p ∈ T.Δ₁Class) : Arithmetic.Bootstrapping.shift L p = p

lemma Theory.Δ₁.Sentential.forall_shift_eq (T : Theory L) [T.Δ₁] [Theory.Δ₁.Sentential T] {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    ∀ p ∈ T.Δ₁Class (V := V), Arithmetic.Bootstrapping.shift L p = p :=
  fun _ h ↦ shift_eq h

/-- The numeration of `T` restricted to the codes fixed by the shift of free variables. -/
noncomputable abbrev Theory.Δ₁.sentential (T : Theory L) (d : T.Δ₁) : T.Δ₁ where
  ch := T.Δ₁ch ⋏ Arithmetic.Bootstrapping.shiftFixed L
  mem_iff φ := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
      Bounding.HierarchySymbol.Semiformula.val_and, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq]
    rw [d.mem_iff φ]
    constructor
    · exact fun h ↦ h.1
    · rintro ⟨σ, hσ, rfl⟩
      apply And.intro ⟨σ, hσ, rfl⟩
      change ℕ ⊧/![_] (Arithmetic.Bootstrapping.shiftFixed L).sigma.val
      rw [Arithmetic.Bootstrapping.shiftFixed_sigma_iff, ← Semiformula.quote_shift]
      simp
  isDelta1 :=
    Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
      (fun V _ _ ↦
        Bounding.HierarchySymbol.Semiformula.ProperOn.and (by simp)
          Arithmetic.Bootstrapping.shiftFixed_properOn)

lemma Theory.Δ₁.sentential_shift_eq (T : Theory L) (d : T.Δ₁) {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {p : V} (h : V ⊧/![p] (Theory.Δ₁.sentential T d).ch.val) :
    Arithmetic.Bootstrapping.shift L p = p := by
  exact (Arithmetic.Bootstrapping.shiftFixed_sigma_iff p).mp h.2

instance (T : Theory L) (d : T.Δ₁) : @Theory.Δ₁.Sentential L _ _ T (Theory.Δ₁.sentential T d) :=
  @Theory.Δ₁.Sentential.mk L _ _ T (Theory.Δ₁.sentential T d) fun h ↦
    Theory.Δ₁.sentential_shift_eq T d h

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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
