module

public import Lean.Attributes

/-!
# The record of open problems

The extension in which the command `open_problem` records the open problems it declares. It is
kept apart from the command, outside any `meta` section, so that the executable `open_problems`
can read it at run time.
-/

@[expose] public section

open Lean

namespace AlphaCentauri

/-- The open problems of the library, declared by `open_problem`. -/
initialize openProblemAttr : TagAttribute ←
  registerTagAttribute `open_problem "an open problem, declared by the command `open_problem`"

end AlphaCentauri
