module

public import AlphaCentauri.OpenProblem.Attribute
public import Lean

/-!
# The list of open problems

Executable collecting every open problem declared by `open_problem` in `AlphaCentauri` and writing
it to a JSON file, which `index.html` in this directory renders as the page published on the
project's GitHub Pages.

`AlphaCentauri` is imported at run time rather than by this module, as for the zoo: linking an
executable against it would force the whole of `Foundation` and `Mathlib` to be compiled to native
code. Only `AlphaCentauri.OpenProblem.Attribute`, which depends on nothing but `Lean`, is linked, for the
extension recording the open problems.
-/

@[expose] public section

open Lean

namespace AlphaCentauri.OpenProblems

/-- The repository the source links point to. -/
def repository : String := "FormalizedFormalLogic/AlphaCentauri"

/-- A citation `- [HP98, Theorem I.1.5]` of a docstring: the key and the locator after it. -/
structure Citation where
  key : String
  locator : Option String
deriving ToJson

/-- The citation written on `line`, if `line` is one. -/
def Citation.parse? (line : String) : Option Citation := do
  let line := line.trimAscii.toString
  guard <| line.startsWith "- [" && line.endsWith "]"
  let inner := ((line.drop 3).dropEnd 1).toString
  match inner.splitOn ", " with
  | [] => none
  | key :: rest =>
    let locator := ", ".intercalate rest
    return { key, locator := if locator.isEmpty then none else some locator }

/-- An open problem as listed on the page. -/
structure Entry where
  /-- The full name of the declaration. -/
  name : String
  module : String
  /-- The source file, relative to the root of the repository. -/
  path : String
  /-- The line the declaration, with its docstring, starts on. -/
  line : Nat
  url : String
  /-- The docstring without its citations, in Markdown with TeX. -/
  description : String
  citations : Array Citation
  /-- The declaration as written in the source, without its docstring. -/
  source : String
deriving ToJson

/-- The list written by the executable. -/
structure Output where
  repository : String
  revision : String
  problems : Array Entry
deriving ToJson

/-- The docstring `doc` split into its prose and the citations on its last lines. -/
def splitDocString (doc : String) : String × Array Citation := Id.run do
  let lines := (doc.trimAscii.toString.splitOn "\n").toArray
  let mut prose := lines.size
  let mut citations := #[]
  while prose > 0 do
    let some c := Citation.parse? lines[prose - 1]! | break
    citations := citations.push c
    prose := prose - 1
  return ("\n".intercalate (lines.extract 0 prose).toList |>.trimAscii.toString, citations.reverse)

/-- The path of the source file of `module`, relative to the root of the repository. -/
def modulePath (module : Name) : String :=
  "/".intercalate (module.components.map (·.toString)) ++ ".lean"

/-- The entry of the open problem `name`, declared in `module`. -/
def entry (revision : String) (module name : Name) : CoreM Entry := do
  let path := modulePath module
  let some ranges ← findDeclarationRanges? name
    | throwError "no declaration range is recorded for `{name}`"
  let doc := (← findDocString? (← getEnv) name).getD ""
  let (description, citations) := splitDocString doc
  -- The declaration starts on the line of its name: the lines above it hold the docstring.
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.toArray
  let source := "\n".intercalate
    (lines.extract (ranges.selectionRange.pos.line - 1) ranges.range.endPos.line).toList
  return {
    name := name.toString, module := module.toString, path
    line := ranges.range.pos.line
    url := s!"https://github.com/{repository}/blob/{revision}/{path}#L{ranges.range.pos.line}"
    description, citations
    source := source.trimAsciiEnd.toString }

/-- Every open problem of the environment, ordered by source file and line. -/
def collect (revision : String) : CoreM (Array Entry) := do
  let env ← getEnv
  let mut entries := #[]
  for h : i in [:env.header.moduleNames.size] do
    let module := env.header.moduleNames[i]
    for name in openProblemAttr.ext.getModuleEntries env i do
      entries := entries.push (← entry revision module name)
  return entries.qsort fun a b => a.path < b.path || (a.path == b.path && a.line < b.line)

end AlphaCentauri.OpenProblems

open AlphaCentauri.OpenProblems in
/--
`open_problems [output] [revision]` writes the open problems of `AlphaCentauri` to `output`, with
source links to `revision`, which defaults to `$GITHUB_SHA` and then to `main`. Run from the root of
the repository, after `lake build AlphaCentauri`.
-/
public def main (args : List String) : IO Unit := do
  let output : String := args[0]?.getD "pages/open-problems/open-problems.json"
  let revision ← match args[1]? with
    | some r => pure r
    | none => pure <| (← IO.getEnv "GITHUB_SHA").getD "main"
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules (loadExts := true) #[{ module := `AlphaCentauri }] {}
  let (problems, _) ← (collect revision).toIO { fileName := "<open_problems>", fileMap := default }
    { env }
  if problems.isEmpty then
    throw <| IO.userError "no open problem found; is the extension of `open_problem` loaded?"
  if let some dir := System.FilePath.parent output then IO.FS.createDirAll dir
  IO.FS.writeFile output (toJson { repository, revision, problems : Output }).pretty
  IO.println s!"open_problems: wrote {problems.size} open problems to {output}"
