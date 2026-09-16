module

public import Mathlib.Computability.Primrec.List

/-!
# Primitive recursion for bounded quantification and vector encodings

Closure of `PrimrecRel`/`PrimrecPred` under bounded quantifiers, constant predicates, and the
correspondence between `Fin k → ℕ` and `List.Vector ℕ k` argument forms.
-/

@[expose] public section

section quantifier

variable {β : Type*} [Primcodable β] {R : ℕ → β → Prop}

theorem PrimrecRel.exists_lt' (h : PrimrecRel R) : PrimrecRel fun n y ↦ ∃ x < n, R x y :=
  (PrimrecRel.exists_mem_list h |>.comp (Primrec.list_range.comp .fst) .snd).of_eq (by simp)

theorem PrimrecRel.forall_lt' (h : PrimrecRel R) : PrimrecRel fun n y ↦ ∀ x < n, R x y :=
  (PrimrecRel.forall_mem_list h |>.comp (Primrec.list_range.comp .fst) .snd).of_eq (by simp)

end quantifier

theorem PrimrecPred.const {α : Type*} [Primcodable α] (p : Prop) : PrimrecPred fun _ : α ↦ p := by
  classical
  exact Primrec.primrecPred (Primrec.const (decide p))

section vector

variable {k : ℕ}

theorem Nat.Primrec'.comp_get_iff {f : (Fin k → ℕ) → ℕ} :
    Nat.Primrec' (fun v : List.Vector ℕ k ↦ f v.get) ↔ Primrec f := by
  rw [Nat.Primrec'.prim_iff]
  exact ⟨fun h ↦ (h.comp Primrec.vector_ofFn').of_eq fun v ↦ by
      rw [funext (List.Vector.get_ofFn v)], fun h ↦ h.comp Primrec.vector_get'⟩

theorem Nat.Primrec'.comp_ofFn_iff {f : List.Vector ℕ k → ℕ} :
    Primrec (fun v : Fin k → ℕ ↦ f (List.Vector.ofFn v)) ↔ Nat.Primrec' f := by
  rw [Nat.Primrec'.prim_iff]
  exact ⟨fun h ↦ (h.comp Primrec.vector_get').of_eq (by simp [List.Vector.ofFn_get]),
    fun h ↦ h.comp Primrec.vector_ofFn'⟩

theorem PrimrecPred.comp_get_iff {p : (Fin k → ℕ) → Prop} :
    PrimrecPred (fun v : List.Vector ℕ k ↦ p v.get) ↔ PrimrecPred p :=
  ⟨fun h ↦ (h.comp Primrec.vector_ofFn').of_eq fun v ↦ by
      rw [funext (List.Vector.get_ofFn v)], fun h ↦ h.comp Primrec.vector_get'⟩

end vector
