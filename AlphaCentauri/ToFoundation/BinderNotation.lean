module

public import Foundation.FirstOrder.Syntax.Classical.BinderNotation

/-!
# Notation for a power by a variable exponent

`t ^' n` in the term notation of `“…”`, where `n` is a natural number given by an identifier. It is
the power of `t` by the numeral `n`, as `t ^' 3` is for a numeral literal.
-/

@[expose] public section

namespace FFL.FirstOrder.BinderNotation

open Semiterm

syntax:70 first_order_term " ^' " ident : first_order_term

macro_rules
  | `(⤫term(lit)[ $binders* | $fbinders* | $e ^' $n:ident ]) =>
    `((Semiterm.Operator.npow _ $n).operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])

end FFL.FirstOrder.BinderNotation
