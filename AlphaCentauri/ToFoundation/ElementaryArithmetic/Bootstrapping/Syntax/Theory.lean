module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.LocallyDelta0
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Theory

/-!
# Theories whose axioms are locally $\Delta_0$ in models of $\mathsf{EA}$

The class `LocallyDelta0Axioms T V` states that, in the model `V` of $\mathsf{EA}$, the $\Sigma$
and $\Pi$ parts of the $\Delta_1$ formula `T.Δ₁ch` of the axioms of `T` agree and the codes of
the axioms form a locally $\Delta_0$ set. Foundation obtains the first part from provability in
$\mathsf{I}\Sigma_1$; here it is checked theory by theory. The class is closed under the
constructions of Foundation's `Theory.Δ₁` instances: the empty theory, single sentences, finite
theories, unions and insertion.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic

open Bounding

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- In the model `V` of $\mathsf{EA}$, the $\Sigma$ and $\Pi$ parts of the $\Delta_1$ formula of
the axioms of `T` agree, and the codes of the axioms form a locally $\Delta_0$ set. -/
class LocallyDelta0Axioms (T : Theory L) [T.Δ₁] (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗘𝗔] : Prop where
  properOn : T.Δ₁ch.ProperOn V
  locallyDelta0 : LocallyDelta0Pred fun x : V ↦ x ∈ T.Δ₁Class

namespace LocallyDelta0Axioms

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔] {T U : Theory L}

instance empty : LocallyDelta0Axioms (∅ : Theory L) V where
  properOn := HierarchySymbol.Semiformula.ProperOn.falsum
  locallyDelta0 := (LocallyDelta0.of_definable (R := fun _ : Fin 1 → V ↦ False)
    (by definability)).of_iff fun v ↦ by
      change V ⊧/![v 0] (⊥ : 𝚫ᴬ₁.Semisentence 1).val ↔ False
      simp

instance singleton (φ : Sentence L) : LocallyDelta0Axioms ({φ} : Theory L) V where
  properOn := by intro e; rfl
  locallyDelta0 := (LocallyDelta0.of_definable
    (R := fun v : Fin 1 → V ↦ v 0 = (Encodable.encode φ : V)) (by definability)).of_iff
      fun v ↦ by simp [Theory.Δ₁Class, numeral_eq_natCast]

/-- The class is preserved by the union of the $\Delta_1$ formulas. -/
lemma add (dT : T.Δ₁) (dU : U.Δ₁) [hT : @LocallyDelta0Axioms L _ _ T dT V _ _]
    [hU : @LocallyDelta0Axioms L _ _ U dU V _ _] :
    @LocallyDelta0Axioms L _ _ (T ∪ U) (dT.add dU) V _ _ := by
  let := dT
  let := dU
  exact ⟨hT.properOn.or hU.properOn,
    (hT.locallyDelta0.or hU.locallyDelta0).of_iff fun _ ↦ Theory.Δ₁Class.mem_union⟩

instance union [T.Δ₁] [U.Δ₁] [LocallyDelta0Axioms T V] [LocallyDelta0Axioms U V] :
    LocallyDelta0Axioms (T ∪ U) V :=
  add inferInstance inferInstance

/-- The class is preserved by rewriting the theory along an equality. -/
lemma ofEq (dT : T.Δ₁) (h : T = U) [hT : @LocallyDelta0Axioms L _ _ T dT V _ _] :
    @LocallyDelta0Axioms L _ _ U (dT.ofEq h) V _ _ := by
  subst h
  exact hT

lemma ofList (l : List (Sentence L)) :
    @LocallyDelta0Axioms L _ _ {φ | φ ∈ l} (Theory.Δ₁.ofList l) V _ _ := by
  induction l with
  | nil => exact ofEq (V := V) Theory.Δ₁.empty _
  | cons φ l ih =>
    have := add (V := V) (Theory.Δ₁.singleton φ) (Theory.Δ₁.ofList l)
    exact ofEq (V := V) _ _

instance ofFinite (T : Theory L) (h : Set.Finite T) :
    @LocallyDelta0Axioms L _ _ T (Theory.Δ₁.ofFinite T h) V _ _ :=
  haveI := ofList (V := V) h.toFinset.toList
  ofEq (V := V) _ _

instance insert {φ : Sentence L} [T.Δ₁] [LocallyDelta0Axioms T V] :
    LocallyDelta0Axioms (insert φ T) V :=
  haveI := add (V := V) (T := T) inferInstance (Theory.Δ₁.singleton φ)
  ofEq (V := V) _ (by ext; simp)

end LocallyDelta0Axioms

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
