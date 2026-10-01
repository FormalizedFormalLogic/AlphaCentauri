module

public import AlphaCentauri.Tactic.Primrec

/-!
# Primitive recursion for bounded quantification and vector encodings

Bounded quantifiers whose bound is primitive recursive, constant predicates, and the
correspondence between `Fin k → ℕ` and `List.Vector ℕ k` argument forms.
-/

@[expose] public section

section quantifier

variable {β : Type*} [Primcodable β] {R : ℕ → β → Prop}

/-- `PrimrecRel.exists_lt`, with the parameter of the relation in any `Primcodable` type. -/
theorem PrimrecRel.exists_lt' (h : PrimrecRel R) : PrimrecRel fun n y ↦ ∃ x < n, R x y :=
  (PrimrecRel.exists_mem_list h |>.comp (Primrec.list_range.comp .fst) .snd).of_eq (by simp)

/-- `PrimrecRel.forall_lt`, with the parameter of the relation in any `Primcodable` type. -/
theorem PrimrecRel.forall_lt' (h : PrimrecRel R) : PrimrecRel fun n y ↦ ∀ x < n, R x y :=
  (PrimrecRel.forall_mem_list h |>.comp (Primrec.list_range.comp .fst) .snd).of_eq (by simp)

end quantifier

section pointwiseQuantifier

variable {α : Type*} [Primcodable α] {n : α → ℕ} {R : α → ℕ → Prop}

/-- A bounded existential whose bound is itself primitive recursive. -/
@[primrec]
theorem PrimrecPred.exists_lt' (hn : Primrec n) (hR : PrimrecRel R) :
    PrimrecPred fun a ↦ ∃ x < n a, R a x := by
  have h : PrimrecRel fun (m : ℕ) (a : α) ↦ ∃ x < m, R a x := PrimrecRel.exists_lt' hR.swap
  exact PrimrecRel.comp h hn Primrec.id

/-- A bounded universal whose bound is itself primitive recursive. -/
@[primrec]
theorem PrimrecPred.forall_lt' (hn : Primrec n) (hR : PrimrecRel R) :
    PrimrecPred fun a ↦ ∀ x < n a, R a x := by
  have h : PrimrecRel fun (m : ℕ) (a : α) ↦ ∀ x < m, R a x := PrimrecRel.forall_lt' hR.swap
  exact PrimrecRel.comp h hn Primrec.id

example {p : ℕ → ℕ → Prop} (hp : PrimrecRel p) :
    PrimrecPred fun a : ℕ ↦ ∀ x < a + 1, ∃ y < x, p x y := by primrec

end pointwiseQuantifier

@[primrec]
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
