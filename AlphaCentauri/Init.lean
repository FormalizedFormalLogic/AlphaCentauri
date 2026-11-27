module

public meta import AlphaCentauri.Linter.InitImport
public meta import AlphaCentauri.Linter.RepeatedBinder

/-!
# The module imported by every module

Every module of the library imports this one, possibly through another module, so that the linters
of the library run in it.
-/
