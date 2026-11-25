module

public import Lean.Attributes

/-!
# The record of open problems

The environment extension recording the declared open problems.
-/

@[expose] public section

open Lean

namespace AlphaCentauri

/-- The open problems of the library, declared by `open_problem`. -/
initialize openProblemAttr : TagAttribute ←
  registerTagAttribute `open_problem "an open problem, declared by the command `open_problem`"

end AlphaCentauri
