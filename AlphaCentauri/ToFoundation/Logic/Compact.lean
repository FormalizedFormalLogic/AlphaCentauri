module

public import Foundation.Logic.Semantics

/-!
# Gaps in Foundation's `Logic.Semantics`: compactness along a cumulative sequence

The two directions of `FFL.Compact.compact_cumulative`.
-/

@[expose] public section

namespace FFL.Compact

alias ⟨satisfiable_of_satisfiable_iUnion, satisfiable_iUnion⟩ := compact_cumulative

end FFL.Compact
