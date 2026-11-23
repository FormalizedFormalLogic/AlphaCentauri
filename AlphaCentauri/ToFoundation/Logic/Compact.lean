module

public import Foundation.Logic.Semantics

/-!
# Compactness along a cumulative sequence

The two directions of `FFL.Compact.compact_cumulative`: a cumulative union is satisfiable if and
only if each member is.
-/

@[expose] public section

namespace FFL.Compact

alias ⟨satisfiable_of_satisfiable_iUnion, satisfiable_iUnion⟩ := compact_cumulative

end FFL.Compact
