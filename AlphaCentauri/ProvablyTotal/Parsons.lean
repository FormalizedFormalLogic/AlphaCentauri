module

public import AlphaCentauri.ProvablyTotal.Basic
public import AlphaCentauri.ToFoundation.Primrec
public import Mathlib.Computability.Ackermann

/-!
# Parsons' theorem

The `𝗜𝚺₁`-provably total functions are exactly the primitive recursive functions, and the
Ackermann function is therefore not `𝗜𝚺₁`-provably total.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- Every `𝗜𝚺₁`-provably total function is primitive recursive.
- [HP98, Corollary IV.3.7] -/
axiom primrec'_of_provablyTotal {k : ℕ} {f : List.Vector ℕ k → ℕ}
    (hf : 𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v))) : Nat.Primrec' f

/-- **Parsons' theorem**: the `𝗜𝚺₁`-provably total functions are exactly the primitive recursive
functions.
- [HP98, Corollary IV.3.7] -/
axiom parsons {k : ℕ} (f : List.Vector ℕ k → ℕ) :
    Nat.Primrec' f ↔ 𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v))

/-- **Parsons' theorem** in class form: the class of `𝗜𝚺₁`-provably total functions of arity `k`
is the class of primitive recursive functions of arity `k`.
- [HP98, Corollary IV.3.7] -/
theorem provablyTotalFunctions_ISigma1 (k : ℕ) :
    𝗜𝚺₁.provablyTotalFunctions k = {f | Nat.Primrec' fun v : List.Vector ℕ k ↦ f v.get} := by
  ext f
  have e : (fun v : Fin k → ℕ ↦ f (List.Vector.ofFn v).get) = f :=
    funext fun v ↦ congrArg f (funext (List.Vector.get_ofFn v))
  simpa [e] using (parsons fun v : List.Vector ℕ k ↦ f v.get).symm

/-- In Mathlib's `Primrec` form, the `𝗜𝚺₁`-provably total functions are exactly the primitive
recursive functions.
- [HP98, Corollary IV.3.7] -/
axiom parsons_primrec {k : ℕ} (f : List.Vector ℕ k → ℕ) :
    Primrec f ↔ 𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v))

/-- The Ackermann function is not `𝗜𝚺₁`-provably total.
- [HP98, Corollary IV.3.7] -/
theorem not_provablyTotal_ackermann :
    ¬𝗜𝚺₁.ProvablyTotal (fun v : Fin 2 → ℕ ↦ _root_.ack (v 0) (v 1)) := by
  intro h
  have hp : Primrec fun w : List.Vector ℕ 2 ↦ _root_.ack (w.get 0) (w.get 1) :=
    Nat.Primrec'.prim_iff.mp ((parsons _).mpr (by simpa using h))
  have hc : Primrec fun p : ℕ × ℕ ↦ (p.1 ::ᵥ p.2 ::ᵥ List.Vector.nil : List.Vector ℕ 2) :=
    Primrec.vector_cons.comp Primrec.fst (Primrec.vector_cons.comp Primrec.snd (Primrec.const _))
  exact not_primrec₂_ack ((hp.comp hc).of_eq (by intro p; rfl))

end FFL.FirstOrder.Arithmetic
