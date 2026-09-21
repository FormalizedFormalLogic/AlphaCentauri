module

public import AlphaCentauri.Tactic.Primrec
public import AlphaCentauri.ToMathlib.Primrec
public import AlphaCentauri.Hierarchy.Bounded
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Primitive recursion for truth of $\Delta_0$ formulas

Truth of a $\Delta_0$ formula, evaluated in either `List.Vector` or `Fin k → ℕ` argument form, is
a primitive recursive predicate.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {ξ : Type*} (ε : ξ → ℕ)

/-- The truth of a $\Delta_0$ formula is primitive recursive in `List.Vector` form.
- [HP98, Theorem 0.35] -/
lemma bounded_primrec_vec :
    (k : ℕ) → (φ : ArithmeticSemiformula ξ k) → φ.Bounded →
      PrimrecPred fun v : List.Vector ℕ k ↦ φ.Eval v.get ε
  | _, _, Semiformula.Bounded.verum _ => by simpa using PrimrecPred.const True
  | _, _, Semiformula.Bounded.falsum _ => by simpa using PrimrecPred.const False
  | _, _, Semiformula.Bounded.rel Language.Eq.eq v => by
    simpa [← Matrix.fun_eq_vec_two]
      using Primrec.eq.comp (term_primrec (v 0)) (term_primrec (v 1))
  | _, _, Semiformula.Bounded.nrel Language.Eq.eq v => by
    simpa [← Matrix.fun_eq_vec_two]
      using (Primrec.eq.comp (term_primrec (v 0)) (term_primrec (v 1))).not
  | _, _, Semiformula.Bounded.rel Language.LT.lt v => by
    simpa [← Matrix.fun_eq_vec_two]
      using Primrec.nat_lt.comp (term_primrec (v 0)) (term_primrec (v 1))
  | _, _, Semiformula.Bounded.nrel Language.LT.lt v => by
    simpa [← Matrix.fun_eq_vec_two]
      using (Primrec.nat_lt.comp (term_primrec (v 0)) (term_primrec (v 1))).not
  | _, _, Semiformula.Bounded.and hφ hψ => by
    simpa using (bounded_primrec_vec _ _ hφ).and (bounded_primrec_vec _ _ hψ)
  | _, _, Semiformula.Bounded.or hφ hψ => by
    simpa using (bounded_primrec_vec _ _ hφ).or (bounded_primrec_vec _ _ hψ)
  | n, _, Semiformula.Bounded.ball (φ := φ) pt hφ => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    have h : PrimrecRel fun (x : ℕ) (v : List.Vector ℕ n) ↦ φ.Eval (x ::ᵥ v).get ε :=
      (bounded_primrec_vec _ _ hφ).comp Primrec.vector_cons
    simpa [List.Vector.cons_get] using (PrimrecRel.forall_lt' h).comp (term_primrec t) .id
  | n, _, Semiformula.Bounded.bexs (φ := φ) pt hφ => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    have h : PrimrecRel fun (x : ℕ) (v : List.Vector ℕ n) ↦ φ.Eval (x ::ᵥ v).get ε :=
      (bounded_primrec_vec _ _ hφ).comp Primrec.vector_cons
    simpa [List.Vector.cons_get] using (PrimrecRel.exists_lt' h).comp (term_primrec t) .id

/-- The truth of a $\Delta_0$ formula is primitive recursive in `Fin k → ℕ` form.
- [HP98, Theorem 0.35] -/
@[primrec]
lemma bounded_primrec {k} {φ : ArithmeticSemiformula ξ k} (hφ : φ.Bounded) :
    PrimrecPred fun v : Fin k → ℕ ↦ φ.Eval v ε :=
  PrimrecPred.comp_get_iff.mp (bounded_primrec_vec ε k φ hφ)

/-- The value of a term under an assignment read off a list is primitive recursive in the list.
- [HP98, Theorem 0.35] -/
@[primrec]
lemma primrec_termVal {α : Type*} [Primcodable α] {l : α → List ℕ} (hl : Primrec l) :
    (t : ArithmeticTerm ℕ) → Primrec fun a ↦ Semiterm.val ![] ((l a).getD · 0) t
  | #x => x.elim0
  | &x => by simpa using (Primrec.list_getD 0).comp hl (Primrec.const x)
  | .func Language.Zero.zero _ => by simpa using Primrec.const 0
  | .func Language.One.one _ => by simpa using Primrec.const 1
  | .func Language.Add.add v => by
    simpa [Semiterm.val_func] using
      Primrec.nat_add.comp (primrec_termVal hl (v 0)) (primrec_termVal hl (v 1))
  | .func Language.Mul.mul v => by
    simpa [Semiterm.val_func] using
      Primrec.nat_mul.comp (primrec_termVal hl (v 0)) (primrec_termVal hl (v 1))

end FFL.FirstOrder.Arithmetic
