import Lean

/-!
# The axiom audit

Reports the axioms transitively used by declarations under `AlphaCentauri`, subject to the
allowlist in `forgive.yml`.
-/

open Lean

namespace Audit

/-- The root module of the audited library. -/
def root : Name := `AlphaCentauri

/-- The axioms every declaration may use. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The allowlist, relative to the repository root. -/
def forgiveFile : System.FilePath := "forgive.yml"

/-- Where the reports go, relative to the repository root. -/
def jsonFile : System.FilePath := ".lake" / "audit.json"
def markdownFile : System.FilePath := ".lake" / "audit.md"

/-! ## A YAML subset reader

A reader for the YAML subset used by the allowlist. -/

namespace Yaml

/-- The parsed document. -/
inductive Value where
  | null
  | scalar (s : String)
  | seq (items : Array Value)
  | map (entries : Array (String × Value))
  deriving Repr, Inhabited

/-- A source line represented by its 1-based number, indentation, and trimmed uncommented text. -/
structure Line where
  no : Nat
  indent : Nat
  text : String
  deriving Repr

private def ofChars (cs : List Char) : String := cs.foldl (·.push ·) ""

private def trimChars (cs : List Char) : List Char :=
  (cs.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace |>.reverse

private def trim (s : String) : String := ofChars (trimChars s.toList)

/-- Drop a trailing comment: `#` at the start of the text or after whitespace. -/
private def stripComment (cs : List Char) : List Char :=
  go ' ' cs
where
  go (prev : Char) : List Char → List Char
    | [] => []
    | '#' :: rest => if prev.isWhitespace then [] else '#' :: go '#' rest
    | c :: rest => c :: go c rest

/-- Split a document into meaningful lines. Fails on a tab in the indentation. -/
private def toLines (s : String) : Except String (Array Line) := do
  let mut out := #[]
  let mut no := 0
  for raw in s.splitOn "\n" do
    no := no + 1
    let cs := stripComment raw.toList
    let leading := cs.takeWhile fun c => c == ' ' || c == '\t'
    if leading.contains '\t' then
      throw s!"line {no}: tabs are not allowed in indentation"
    let text := trimChars cs
    if !text.isEmpty then
      out := out.push { no, indent := leading.length, text := ofChars text }
  return out

/-- Remove one layer of matching `"` or `'` quotes. No escape sequences are interpreted. -/
private def unquote (s : String) : String :=
  match s.toList with
  | '"' :: rest => if rest.getLast? == some '"' then ofChars rest.dropLast else s
  | '\'' :: rest => if rest.getLast? == some '\'' then ofChars rest.dropLast else s
  | _ => s

/-- A scalar, or a flow sequence `[a, b]` of scalars. -/
private def parseInline (s : String) (no : Nat) : Except String Value :=
  match s.toList with
  | '[' :: rest =>
    if rest.getLast? != some ']' then
      throw s!"line {no}: unterminated flow sequence"
    else
      let inner := ofChars rest.dropLast
      let items := (inner.splitOn ",").map trim |>.filter (!·.isEmpty)
      return .seq (items.map (.scalar ∘ unquote)).toArray
  | _ => return .scalar (unquote s)

private def isSeqItem (t : String) : Bool := t == "-" || t.startsWith "- "

/-- Split `key: value` (or `key:`) at the first `:` followed by a space or the end of the line. -/
private def splitKey (t : String) (no : Nat) : Except String (String × String) :=
  match go [] t.toList with
  | some (k, v) =>
    let k := unquote (ofChars (trimChars k))
    if k.isEmpty then throw s!"line {no}: empty key" else return (k, ofChars (trimChars v))
  | none => throw s!"line {no}: expected `key: value` or `- item`, got `{t}`"
where
  go (acc : List Char) : List Char → Option (List Char × List Char)
    | ':' :: [] => some (acc.reverse, [])
    | ':' :: ' ' :: rest => some (acc.reverse, rest)
    | c :: rest => go (c :: acc) rest
    | [] => none

mutual

/-- Parse the block starting at line `i`; returns the value and the index of the first line after
it. -/
private partial def parseBlock (ls : Array Line) (i : Nat) : Except String (Value × Nat) := do
  let some l := ls[i]? | return (.null, i)
  if isSeqItem l.text then parseSeq ls i l.indent #[] else parseMap ls i l.indent #[]

private partial def parseSeq (ls : Array Line) (i indent : Nat) (acc : Array Value) :
    Except String (Value × Nat) := do
  let some l := ls[i]? | return (.seq acc, i)
  if l.indent < indent then return (.seq acc, i)
  if l.indent > indent then throw s!"line {l.no}: unexpected indentation"
  if !isSeqItem l.text then throw s!"line {l.no}: expected a `- item` in this sequence"
  let body := ofChars (trimChars (l.text.toList.drop 1))
  if body.isEmpty then throw s!"line {l.no}: a sequence item must be a scalar on the same line"
  parseSeq ls (i + 1) indent (acc.push (← parseInline body l.no))

private partial def parseMap (ls : Array Line) (i indent : Nat) (acc : Array (String × Value)) :
    Except String (Value × Nat) := do
  let some l := ls[i]? | return (.map acc, i)
  if l.indent < indent then return (.map acc, i)
  if l.indent > indent then throw s!"line {l.no}: unexpected indentation"
  if isSeqItem l.text then throw s!"line {l.no}: expected a `key:` in this mapping"
  let (key, rest) ← splitKey l.text l.no
  if acc.any (·.1 == key) then throw s!"line {l.no}: duplicate key `{key}`"
  if !rest.isEmpty then
    return ← parseMap ls (i + 1) indent (acc.push (key, ← parseInline rest l.no))
  match ls[i + 1]? with
  | some l' =>
    if l'.indent > indent then
      let (v, j) ← parseBlock ls (i + 1)
      parseMap ls j indent (acc.push (key, v))
    else
      parseMap ls (i + 1) indent (acc.push (key, .null))
  | none => return (.map (acc.push (key, .null)), i + 1)

end

/-- Parse a document. An empty document is `.null`. -/
def parse (s : String) : Except String Value := do
  let ls ← toLines s
  let (v, j) ← parseBlock ls 0
  if let some l := ls[j]? then
    throw s!"line {l.no}: unexpected indentation"
  return v

end Yaml

/-! ## The allowlist `forgive.yml`

```yaml
version: v0

LO.some_unproved_lemma:
  forgive:
    - LO.some_unproved_lemma
LO.uses_some_unproved_lemma:
  forgive:
    - LO.some_unproved_lemma
```

Each top-level declaration key lists the axioms or declarations through which its dependencies
may be forgiven. Every entry and forgiven name must be necessary. -/

/-- One entry of the allowlist: a declaration and the names it is allowed to depend on. -/
structure ForgiveEntry where
  decl : Name
  forgive : Array Name
  deriving Repr, Inhabited

/-- The parsed allowlist. -/
structure Forgiveness where
  entries : Array ForgiveEntry := #[]
  deriving Repr, Inhabited

namespace Forgiveness

/-- The only format version this reader accepts. -/
def version : String := "v0"

def find? (f : Forgiveness) (decl : Name) : Option ForgiveEntry :=
  f.entries.find? (·.decl == decl)

private def toName (s : String) (what : String) : Except String Name :=
  let n := s.toName
  if n.isAnonymous then throw s!"{what}: `{s}` is not a declaration name" else return n

private def parseEntry (key : String) (v : Yaml.Value) : Except String ForgiveEntry := do
  let decl ← toName key "top-level key"
  let .map fields := v
    | throw s!"`{key}`: expected a mapping with a `forgive` list"
  for (k, _) in fields do
    if k != "forgive" then throw s!"`{key}`: unknown field `{k}` (only `forgive` is allowed)"
  let some (_, forgive) := fields.find? (·.1 == "forgive")
    | throw s!"`{key}`: missing the `forgive` list"
  let .seq items := forgive
    | throw s!"`{key}`: `forgive` must be a list of names"
  if items.isEmpty then throw s!"`{key}`: `forgive` must not be empty"
  let names ← items.mapM fun
    | .scalar s => toName s s!"`{key}`: forgive"
    | _ => throw s!"`{key}`: `forgive` must be a list of names"
  return { decl, forgive := names }

/-- Parse and validate the shape of an allowlist document. -/
def parse (contents : String) : Except String Forgiveness := do
  let doc ← Yaml.parse contents
  let .map entries := doc
    | throw "expected a mapping with a `version` key"
  let some (_, ver) := entries.find? (·.1 == "version")
    | throw "missing `version`"
  let .scalar ver := ver
    | throw "`version` must be a scalar"
  if ver != version then throw s!"unsupported version `{ver}` (expected `{version}`)"
  let mut acc : Array ForgiveEntry := #[]
  for (key, v) in entries do
    if key == "version" then continue
    let e ← parseEntry key v
    if acc.any (·.decl == e.decl) then throw s!"`{key}`: duplicate entry"
    acc := acc.push e
  return { entries := acc }

end Forgiveness

/-! ## Collecting axioms -/

/-- The constants `c` refers to directly, in its type, its value, and (for an inductive type) its
constructors. -/
def directRefs (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.axiomInfo v) => v.type.getUsedConstants
  | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.quotInfo _) => #[]
  | some (.ctorInfo v) => v.type.getUsedConstants
  | some (.recInfo v) => v.type.getUsedConstants
  | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
  | none => #[]

def isAxiom (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.axiomInfo _) => true
  | _ => false

/-- A computation over an environment with a memo of each constant's transitive axioms. -/
abbrev AxiomM := ReaderT Environment (StateM (NameMap (Array Name)))

/-- The axioms transitively used by `c`. -/
partial def axiomsOf (c : Name) : AxiomM (Array Name) := do
  if let some s := (← get).find? c then return s
  -- Record `c` empty before recursing, so a cycle's back-edge into it contributes nothing.
  modify (·.insert c #[])
  let env ← read
  let mut used : NameSet := if isAxiom env c then ({} : NameSet).insert c else {}
  for d in directRefs env c do
    for a in (← axiomsOf d) do used := used.insert a
  let arr := used.toArray.qsort Name.lt
  modify (·.insert c arr)
  return arr

/-- The memo of an `axiomsOfCut` traversal. -/
structure CutMemo where
  map : NameMap (Array Name) := {}

/-- The axioms `c` reaches without passing through any name in `cut`. -/
partial def axiomsOfCut (allowed cut : NameSet) (c : Name) :
    StateT CutMemo AxiomM (Array Name) := do
  if cut.contains c then return #[]
  if let some s := (← get).map.find? c then return s
  let full ← axiomsOf c
  if full.all allowed.contains then
    modify fun m => { map := m.map.insert c full }
    return full
  modify fun m => { map := m.map.insert c #[] }
  let env ← read
  let mut used : NameSet := if isAxiom env c then ({} : NameSet).insert c else {}
  for d in directRefs env c do
    for a in (← axiomsOfCut allowed cut d) do used := used.insert a
  let arr := used.toArray.qsort Name.lt
  modify fun m => { map := m.map.insert c arr }
  return arr

/-! ## The audit -/

/-- Run `act` in the environment built from the given imported modules. -/
def withImportedEnv {α} (modules : Array Name) (act : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe Lean.withImportModules (modules.map (fun m => { module := m })) {} (trustLevel := 1024)
    fun env => Prod.fst <$> Core.CoreM.toIO act
      (ctx := { fileName := "<audit>", fileMap := default }) (s := { env := env })

/-- Is `mod` the audited root or one of its submodules? -/
def inAuditedLib (root : Name) (mod : Name) : Bool := mod == root || root.isPrefixOf mod

/-- A heap-owned string representation of a name. -/
def freshStr (n : Name) : String := (toString n).foldl (fun acc c => acc.push c) ""

/-- The result of an axiom audit. -/
structure Report where
  audited : Nat
  /-- Distinct axioms used anywhere under the root, sorted. -/
  axiomsUsed : Array String
  /-- `(axiom, how many other audited declarations reach it)` for each axiom outside the allowed
  three: the library's own unproved statements, most depended-on first. -/
  debt : Array (String × Nat)
  /-- `(declaration, the disallowed axioms it uses)` for each offending declaration. For a
  declaration with an allowlist entry, the axioms are those the entry does not forgive. -/
  violations : Array (String × Array String)
  /-- `(declaration, the disallowed axioms it uses)` for each declaration the allowlist forgives. -/
  forgiven : Array (String × Array String)
  /-- Problems with the allowlist: entries naming unknown or clean declarations, items forgiving
  nothing. -/
  forgiveErrors : Array String

/-- Whether the audit has no violations or allowlist errors. -/
def Report.ok (r : Report) : Bool := r.violations.isEmpty && r.forgiveErrors.isEmpty

/-- Intermediate data used to construct an audit report. -/
private structure Analysis where
  usedAll : NameSet := {}
  /-- How many audited declarations, other than the axiom itself, reach each disallowed axiom. -/
  debt : NameMap Nat := {}
  violations : Array (Name × Array Name) := #[]
  forgiven : Array (Name × Array Name) := #[]
  errors : Array String := #[]

/-- The disallowed axioms `d` still reaches when the names in `cut` are forgiven. -/
private def remaining (allowed cut : NameSet) (d : Name) : AxiomM (Array Name) := do
  let axs ← (axiomsOfCut allowed cut d).run' {}
  return axs.filter (!allowed.contains ·)

private def analyze (allowed : NameSet) (candidates : Array Name) (fg : Forgiveness) :
    AxiomM Analysis := do
  let env ← read
  let mut r : Analysis := {}
  let err (r : Analysis) (msg : String) : Analysis := { r with errors := r.errors.push msg }
  let candSet : NameSet := candidates.foldl (·.insert ·) {}
  for e in fg.entries do
    if !env.contains e.decl then
      r := err r s!"`{freshStr e.decl}` is not a declaration"
    else if !candSet.contains e.decl then
      r := err r s!"`{freshStr e.decl}` is not defined under `{freshStr root}`"
    for x in e.forgive do
      if !env.contains x then
        r := err r s!"`{freshStr e.decl}`: `{freshStr x}` is neither a declaration nor an axiom"
  for d in candidates do
    let axs ← axiomsOf d
    r := { r with usedAll := axs.foldl (·.insert ·) r.usedAll }
    let bad := axs.filter (!allowed.contains ·)
    -- An audited declaration that is itself a disallowed axiom is one of the library's own
    -- unproved statements: it belongs in the table even when nothing depends on it yet.
    if isAxiom env d && !allowed.contains d then
      r := { r with debt := r.debt.insert d ((r.debt.find? d).getD 0) }
    for a in bad do
      if a != d then r := { r with debt := r.debt.insert a ((r.debt.find? a).getD 0 + 1) }
    match fg.find? d with
    | none =>
      if !bad.isEmpty then r := { r with violations := r.violations.push (d, bad) }
    | some e =>
      if bad.isEmpty then
        r := err r s!"`{freshStr d}` uses no disallowed axiom; remove its entry"
        continue
      let cut : NameSet := e.forgive.foldl (·.insert ·) {}
      let left ← remaining allowed cut d
      if !left.isEmpty then
        r := { r with violations := r.violations.push (d, left) }
        continue
      r := { r with forgiven := r.forgiven.push (d, bad) }
      for x in e.forgive do
        if env.contains x && (← remaining allowed (cut.erase x) d).isEmpty then
          r := err r s!"`{freshStr d}`: `{freshStr x}` is redundant: the other forgiven names already cover it"
  return r

/-- Audit every declaration defined under `root`, against `allowed` and the allowlist `fg`. -/
def audit (allowed : List Name) (fg : Forgiveness) : CoreM Report := do
  let env ← getEnv
  let allowedSet : NameSet := allowed.foldl (·.insert ·) {}
  let modNames := env.allImportedModuleNames
  -- Candidates: declarations defined in a module under `root`.
  let candidates : Array Name := env.constants.fold (init := #[]) fun acc declName _ =>
    match env.getModuleIdxFor? declName with
    | some idx =>
      match modNames[idx.toNat]? with
      | some m => if inAuditedLib root m then acc.push declName else acc
      | none => acc
    | none => acc
  let candidates := candidates.qsort Name.lt
  let a := ((analyze allowedSet candidates fg).run env).run' {}
  let render (p : Name × Array Name) : String × Array String := (freshStr p.1, p.2.map freshStr)
  return {
    audited := candidates.size
    axiomsUsed := (a.usedAll.toArray.qsort Name.lt).map freshStr
    debt := (a.debt.toList.toArray.qsort fun x y =>
      x.2 > y.2 || (x.2 == y.2 && Name.lt x.1 y.1)).map fun (n, c) => (freshStr n, c)
    violations := a.violations.map render
    forgiven := a.forgiven.map render
    forgiveErrors := a.errors.map fun s => s.foldl (fun acc c => acc.push c) ""
  }

/-! ## Rendering -/

private def pair (p : String × Array String) : Json :=
  Json.mkObj [("decl", Json.str p.1), ("axioms", Lean.toJson p.2)]

/-- The machine-readable report. -/
def Report.toJson (r : Report) : Json :=
  Json.mkObj [
    ("root", Json.str (toString root)),
    ("allowed", Lean.toJson (allowedAxioms.map toString)),
    ("forgiveFile", Json.str forgiveFile.toString),
    ("audited", Lean.toJson r.audited),
    ("ok", Json.bool r.ok),
    ("axiomsUsed", Lean.toJson r.axiomsUsed),
    ("debt", Lean.toJson (r.debt.map fun (d, c) =>
      Json.mkObj [("axiom", Json.str d), ("dependents", Lean.toJson c)])),
    ("violations", Lean.toJson (r.violations.map pair)),
    ("forgiven", Lean.toJson (r.forgiven.map pair)),
    ("forgiveErrors", Lean.toJson r.forgiveErrors)
  ]

/-- A report that never got as far as the environment: the allowlist did not parse, or the
environment did not load. -/
def errorJson (msg : String) : Json :=
  Json.mkObj [("root", Json.str (toString root)), ("ok", Json.bool false), ("error", Json.str msg)]

private def code (s : String) : String := s!"`{s}`"

private def codes (xs : Array String) : String :=
  if xs.isEmpty then "none" else ", ".intercalate (xs.map code).toList

private def declTable (rows : Array (String × Array String)) : String :=
  "| Declaration | Disallowed axioms |\n|---|---|\n"
    ++ "".intercalate (rows.map fun (d, axs) => s!"| {code d} | {codes axs} |\n").toList

/-- The report as Markdown, for the pull-request comment. -/
def Report.toMarkdown (r : Report) : String := Id.run do
  let status :=
    if r.ok then "✅ clean"
    else ", ".intercalate <| List.filter (!·.isEmpty) [
      if r.violations.isEmpty then "" else s!"❌ {r.violations.size} violation(s)",
      if r.forgiveErrors.isEmpty then "" else s!"❌ {r.forgiveErrors.size} problem(s) in {code forgiveFile.toString}"]
  let mut md := s!"## Axiom audit\n\n| | |\n|---|---|\n"
  md := md ++ s!"| **Status** | {status} |\n"
  md := md ++ s!"| **Audited** | {r.audited} declaration(s) under {code (toString root)} |\n"
  md := md ++ s!"| **Allowed axioms** | {codes (allowedAxioms.map toString).toArray} |\n"
  md := md ++ s!"| **Unproved statements** | {r.debt.size} |\n"
  if !r.violations.isEmpty then
    md := md ++ s!"\n### Violations ({r.violations.size})\n\n" ++ declTable r.violations
  if !r.forgiveErrors.isEmpty then
    md := md ++ s!"\n### Problems in {code forgiveFile.toString} ({r.forgiveErrors.size})\n\n"
      ++ "".intercalate (r.forgiveErrors.map (s!"- {·}\n")).toList
  if !r.debt.isEmpty then
    md := md ++ s!"\n### Unproved statements ({r.debt.size})\n\n"
      ++ "The axioms this library declares in place of a proof, most depended-on first. "
      ++ "The count is how many other audited declarations reach the axiom, so it ranks the "
      ++ "statements by how much of the library rests on them.\n\n"
      ++ "| Statement | Dependent declarations |\n|---|---|\n"
      ++ "".intercalate (r.debt.map fun (d, c) => s!"| {code d} | {c} |\n").toList
  if !r.forgiven.isEmpty then
    -- Capped: the report is posted as one pull-request comment, and GitHub rejects a comment
    -- over 65536 characters. The uncapped list is the allowlist file itself.
    let shown := r.forgiven.take 150
    md := md ++ s!"\n<details><summary>Forgiven by {code forgiveFile.toString}"
    md := md ++ s!" ({r.forgiven.size} declaration(s))</summary>\n\n" ++ declTable shown
    if shown.size < r.forgiven.size then
      md := md ++ s!"\n… and {r.forgiven.size - shown.size} more;"
      md := md ++ s!" the full list is {code forgiveFile.toString}.\n"
    md := md ++ "\n</details>\n"
  return md

def errorMarkdown (msg : String) : String :=
  s!"## Axiom audit\n\n| | |\n|---|---|\n| **Status** | ❌ did not run |\n\n```\n{msg}\n```\n"

/-- Write both reports. -/
def writeReports (json : Json) (md : String) : IO Unit := do
  if let some dir := jsonFile.parent then IO.FS.createDirAll dir
  IO.FS.writeFile jsonFile (json.pretty ++ "\n")
  IO.FS.writeFile markdownFile md

end Audit

open Audit

def main : IO UInt32 := do
  let fg ← do
    if !(← forgiveFile.pathExists) then pure ({} : Forgiveness) else
    match Forgiveness.parse (← IO.FS.readFile forgiveFile) with
    | .ok fg => pure fg
    | .error e =>
      let msg := s!"{forgiveFile}: {e}"
      writeReports (errorJson msg) (errorMarkdown msg)
      IO.eprintln s!"audit: {msg}"
      return 1
  let result ← try
      pure (Except.ok (← withImportedEnv #[root] (audit allowedAxioms fg)))
    catch e => pure (Except.error (toString e))
  let r ← match result with
    | .ok r => pure r
    | .error msg =>
      let msg := s!"failed to load the environment: {msg}"
      writeReports (errorJson msg) (errorMarkdown msg)
      IO.eprintln s!"audit: {msg}"
      return 2
  writeReports r.toJson r.toMarkdown
  IO.println s!"audit: audited {r.audited} declaration(s) under `{root}`; \
    axioms used: {r.axiomsUsed.toList}"
  (← IO.getStdout).flush
  if !r.forgiven.isEmpty then
    IO.println s!"audit: {r.forgiven.size} declaration(s) forgiven by {forgiveFile}:"
    for (d, axs) in r.forgiven do
      IO.println s!"  {d} → {axs.toList}"
    (← IO.getStdout).flush
  if !r.forgiveErrors.isEmpty then
    IO.eprintln s!"audit: {r.forgiveErrors.size} problem(s) in {forgiveFile}:"
    for e in r.forgiveErrors do
      IO.eprintln s!"  {e}"
  if !r.violations.isEmpty then
    IO.eprintln s!"audit: {r.violations.size} declaration(s) under `{root}` use disallowed axioms:"
    for (d, axs) in r.violations do
      IO.eprintln s!"  {d} → {axs.toList}"
    IO.eprintln s!"allowed: {allowedAxioms}"
  IO.println s!"audit: reports written to {jsonFile} and {markdownFile}"
  if r.ok then
    IO.println "audit: ok"
    return 0
  return 1
