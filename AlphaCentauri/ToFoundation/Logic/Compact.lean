module

public import Foundation.Logic.Semantics

/-!
# Compactness along a cumulative sequence

Compactness for cumulative unions of theories.
-/

@[expose] public section

namespace FFL.Compact

alias ⟨satisfiable_of_satisfiable_iUnion, satisfiable_iUnion⟩ := compact_cumulative

end FFL.Compact
