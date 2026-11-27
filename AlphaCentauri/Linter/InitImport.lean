module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic

/-! # A linter for modules that do not import `AlphaCentauri.Init` -/

public meta section

open Lean Elab Command Linter

namespace AlphaCentauri.Linter

/--
The "initImport" linter warns, in the root module, about the modules of the library that do not
import `AlphaCentauri.Init`, not even through another module, so that its linters do not run there.
-/
register_option linter.style.initImport : Bool := {
  defValue := true
  descr := "enable the initImport linter"
}

namespace InitImport

/-- The module every module of the library imports. -/
def initModule : Name := `AlphaCentauri.Init

/-- The modules reachable from `todo`, themselves included. -/
partial def reachable (imports : NameMap (Array Import)) (todo : List Name) (seen : NameSet := {}) :
    NameSet :=
  match todo with
  | [] => seen
  | m :: todo =>
    if seen.contains m then reachable imports todo seen
    else
      let next := ((imports.find? m).getD #[]).toList.map (·.module)
      reachable imports (next ++ todo) (seen.insert m)

/-- The modules that pass on `AlphaCentauri.Init` to the modules importing them, given the modules
of the library, each preceded by its imports. -/
def exporting (modules : Array (Name × Array Import)) : NameSet :=
  modules.foldl (init := NameSet.empty.insert initModule) fun seen (m, imports) ↦
    if imports.any fun i ↦ i.isExported && seen.contains i.module then seen.insert m else seen

/-- The modules of the library that do not import `AlphaCentauri.Init`, other than those it imports
itself. -/
def missing (modules : Array (Name × Array Import)) : Array Name :=
  let imports : NameMap (Array Import) := modules.foldl (fun map (m, i) ↦ map.insert m i) {}
  let exempt := reachable imports [initModule]
  let exporting := exporting modules
  modules.filterMap fun (m, imports) ↦
    if exempt.contains m || imports.any (exporting.contains ·.module) then none else some m

@[inherit_doc linter.style.initImport]
def initImportLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.style.initImport (← getLinterOptions) do return
  unless Parser.isTerminalCommand stx do return
  let env ← getEnv
  let root := initModule.getRoot
  unless env.mainModule == root do return
  let modules := env.header.moduleNames.zip (env.header.moduleData.map (·.imports))
    |>.filter (root.isPrefixOf ·.1)
  for m in missing modules do
    logLint linter.style.initImport stx
      m!"The module `{m}` does not import `{initModule}`. Add `public import {initModule}` to it."

initialize addLinter initImportLinter

end InitImport

end AlphaCentauri.Linter
