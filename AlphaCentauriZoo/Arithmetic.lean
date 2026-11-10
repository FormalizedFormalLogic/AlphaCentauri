module

public import AlphaCentauriZoo.Basic
public import Lean

/-!
# Arithmetic theory zoo

Executable collecting every `⪯`, `⪱` and `≊` between two `ArithmeticTheory`s stated by a constant
of `Foundation` or `AlphaCentauri`, and writing the resulting diagram to a JSON file.

A statement quantified over indices, such as `∀ n, 𝗜𝚺 n ⪱ 𝗕𝚺 (n + 1)`, is drawn through its
instances at the indices up to `maxIndex`.

`Foundation` is imported at run time rather than by this module: linking an executable against it
would force the whole of `Foundation` and `Mathlib` to be compiled to native code.
-/

@[expose] public section

open Lean Meta

namespace Zoo

/-- Classes stating a relation between two theories, and the relation each of them states. -/
def relationClasses : Array (Name × EdgeType) :=
  #[(`FFL.Entailment.WeakerThan, .sub),
    (`FFL.Entailment.StrictlyWeakerThan, .ssub),
    (`FFL.Entailment.Equiv, .eq)]

/--
The modules whose constants are scanned, and the type whose inhabitants are the vertices.
`AlphaCentauri` imports only the part of `Foundation` it needs, so `Foundation` is scanned too.
-/
def rootModules : Array Name := #[`Foundation, `AlphaCentauri]

/-- Type of the theories the zoo is about. -/
def vertexType : Name := `FFL.FirstOrder.ArithmeticTheory

/-- The largest index at which a statement quantified over `ℕ` is instantiated. -/
def maxIndex : Nat := 2

/-- Whether the decidable proposition `p` holds. -/
def holds (p : Expr) : MetaM Bool := do
  let some inst ← synthInstance? (mkApp (mkConst ``Decidable) p) | return false
  let b ← withDefault <| whnf (mkApp2 (mkConst ``Decidable.decide) p inst)
  return b.isConstOf ``Bool.true

/--
The instances of `type` obtained by instantiating each of its binders: a natural number by the
indices up to `maxIndex`, an instance by the one found by type class resolution, and a decidable
hypothesis by nothing if it holds. A binder of any other kind leaves no instance: a family over
anything but indices is drawn only where it is stated for a particular member.
-/
partial def instantiations (type : Expr) : MetaM (Array Expr) := do
  let .forallE _ d b bi := type | return #[type]
  if d.isConstOf ``Nat then
    return ← (Array.range (maxIndex + 1)).flatMapM fun i =>
      instantiations (b.instantiate1 (mkNatLit i))
  if bi.isInstImplicit then
    let some inst ← synthInstance? d | return #[]
    return ← instantiations (b.instantiate1 inst)
  if ← isProp d then
    if b.hasLooseBVar 0 || !(← holds d) then return #[]
    return ← instantiations (b.lowerLooseBVars 1 1)
  return #[]

/-- `e` with every closed arithmetic expression of type `ℕ`, such as `2 + 1`, evaluated. -/
def normalizeIndices (e : Expr) : MetaM Expr :=
  transform e (post := fun e => do
    unless e.isApp && e.getAppArgs[0]?.any (·.isConstOf ``Nat) do return .continue
    match ← (evalNat e).run with
    | some n => return .done (mkNatLit n)
    | none => return .continue)

/-- Whether `e` mentions a natural number exceeding `maxIndex`. -/
def exceedsMaxIndex (e : Expr) : Bool :=
  (e.find? fun e => e.rawNatLit?.any (· > maxIndex)).isSome

/-- The theories related by `type`, and how, if `type` relates two theories. -/
def relationOf? (vertex : Expr) (type : Expr) : MetaM (Option (Expr × Expr × EdgeType)) :=
  withNewMCtxDepth do
    let .const c _ := type.getAppFn | return none
    let some (_, edgeType) := relationClasses.find? (·.1 == c) | return none
    let args := type.getAppArgs
    unless args.size ≥ 2 do return none
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    unless ← isDefEq (← inferType a) vertex do return none
    unless ← isDefEq (← inferType b) vertex do return none
    return some (a, b, edgeType)

/-- A relation between two theories, and the constant stating it. -/
structure Relation where
  src : Expr
  dst : Expr
  type : EdgeType
  source : Name

/-- Every relation between two theories stated by a constant of the environment. -/
def relations : MetaM (Array Relation) := do
  let vertex ← mkConstWithLevelParams vertexType
  -- Report a renamed class instead of quietly producing a zoo with no edge of that kind.
  for (c, _) in relationClasses do discard <| getConstInfo c
  let mut found := #[]
  for (name, ci) in (← getEnv).constants do
    if ci.isUnsafe || name.isInternal then continue
    -- Most constants are discarded here, before anything is instantiated.
    let .const c _ := ci.type.getForallBody.getAppFn | continue
    unless relationClasses.any (·.1 == c) do continue
    let quantified := ci.type.isForall
    let types ← try instantiations ci.type catch _ => pure #[]
    for type in types do
      let some (a, b, t) ← try relationOf? vertex (← normalizeIndices type) catch _ => pure none
        | continue
      if quantified && (exceedsMaxIndex a || exceedsMaxIndex b) then continue
      found := found.push ⟨a, b, t, name⟩
  return found

/--
The theories of `relations`, identified up to unfolding of reducible definitions, so that `𝗜𝗡𝗗 𝚺 1`
and `𝗜𝚺₁` are one vertex.
-/
def vertices (relations : Array Relation) : MetaM (Array Expr) := do
  let mut vs : Array Expr := #[]
  for r in relations do
    for e in [r.src, r.dst] do
      unless ← vs.anyM (withReducible <| isDefEq e ·) do vs := vs.push e
  return vs

/-- `T` is weaker than `T ∪ U` and `U ∪ T`, whenever both theories are vertices. -/
def unionRelations (vs : Array Expr) : MetaM (Array Relation) := do
  let mut found := #[]
  for v in vs do
    let_expr Union.union _ _ a b := v | continue
    for e in [a, b] do
      if let some w ← vs.findM? (withReducible <| isDefEq e ·) then
        found := found.push ⟨w, v, .sub, `Set.subset_union_left⟩
  return found

/--
Theories drawn as no vertex, by their head symbol: the equality axioms below every theory, and the
ways of writing a theory that stand for another one, such as a finite axiomatization or the single
axiom of `𝗣𝗔⁻`. Relations through them still count.
-/
def omittedHeads : Array Name :=
  #[`FFL.FirstOrder.Theory.eqAxiom,
    `FFL.FirstOrder.Arithmetic.ISigma.finiteAxiomatization,
    ``Singleton.singleton,
    ``Insert.insert]

/--
The axioms recorded as open problems in the ledger `forgive.yml`: those whose entry carries a
comment `# An open problem`.
-/
def openProblems (ledger : String) : Std.HashSet Name := Id.run do
  let mut entry : Option Name := none
  let mut found : Std.HashSet Name := ∅
  for line in ledger.splitOn "\n" do
    -- An entry of the `declaration` section is a key indented by two spaces.
    if line.startsWith "  " && !line.startsWith "   " && line.endsWith ":" then
      entry := some (line.trimAscii.dropEnd 1).toString.toName
    else if line.trimAscii.startsWith "# An open problem" then
      if let some n := entry then found := found.insert n
  return found

/-- The classes of prenex formulas. -/
def prenexHierarchy : Name := `FFL.FirstOrder.Bounding.PrenexHierarchy

/-- The bounding `ℬ[<, L]` of the prenex hierarchy of arithmetic. -/
def boundingLt : Name := `FFL.FirstOrder.Bounding.lt

/--
The polarity and the level of `Γ`, if `Γ` is a class `ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 2` of prenex
formulas of every arity: an implicit binder over the arity, as in the uniform reflection schema
`𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 2] 𝗘𝗔`.
-/
def prenexClass? (Γ : Expr) : Option (Expr × Expr) := do
  let .lam _ _ body .implicit := Γ | none
  let body := body.eta
  guard <| body.isAppOf prenexHierarchy
  let args := body.getAppArgs
  let #[ℬ, p, s] := args.extract (args.size - 3) | none
  guard <| ℬ.isAppOf boundingLt && !p.hasLooseBVars && !s.hasLooseBVars
  return (p, s)

/--
The theory as pretty-printed, on one line since it names a vertex. A class of prenex formulas of
every arity, which Lean prints as `fun {k} => ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 2`, is named by its
polarity and level, so that `𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 2] 𝗘𝗔` is named `𝗥𝗙𝗡[𝚷 2] 𝗘𝗔`.
-/
partial def render (e : Expr) (depth : Nat := 0) : MetaM String := do
  let some Γ := e.find? (prenexClass? · |>.isSome) | return (← ppExpr e).pretty (width := 1000)
  let some (p, s) := prenexClass? Γ | unreachable!
  -- The class is printed as a local variable standing for it, whose name is then replaced.
  let placeholder := s!"zooClass{depth}_"
  withLocalDeclD (.mkSimple placeholder) (← inferType Γ) fun x => do
    let name ← render (e.replace fun f => if f == Γ then some x else none) (depth + 1)
    return name.replace placeholder s!"{(← ppExpr p).pretty} {(← ppExpr s).pretty}"

/-- The zoo of the environment, given the axioms that are open problems. -/
def diagram (openProblems : Std.HashSet Name) : MetaM Diagram := do
  for c in omittedHeads.push prenexHierarchy |>.push boundingLt do discard <| getConstInfo c
  let rels ← relations
  let vs ← vertices rels
  let rels := rels ++ (← unionRelations vs)
  let mut names : Array String := #[]
  for v in vs do names := names.push (← render v)
  let nameOf (e : Expr) : MetaM String := do
    for (v, n) in vs.zip names do
      if ← withReducible <| isDefEq e v then return n
    throwError "{e} is not a vertex"
  let mut proved : Edges := ∅
  let mut conjectured : Edges := ∅
  for r in rels do
    let (a, b) := (← nameOf r.src, ← nameOf r.dst)
    -- A theory strictly weaker than itself is kept, for `Edges.diagram` to report.
    if a == b && r.type != .ssub then continue
    if (← collectAxioms r.source).any openProblems.contains then
      conjectured := conjectured.insert ⟨a, b, r.type⟩
    else
      proved := proved.insert ⟨a, b, r.type⟩
  let omitted := (vs.zip names).filterMap fun (v, n) =>
    if omittedHeads.any v.isAppOf then some n else none
  match proved.diagram conjectured (!omitted.contains ·) with
  | .ok d => return d
  | .error msg => throwError msg

end Zoo

/--
`zoo_arithmetic [OUTPUT [LEDGER]]` writes the zoo to `OUTPUT`, reading the open problems from the
ledger `LEDGER`.
-/
public def main (args : List String) : IO Unit := do
  let output : String := args[0]?.getD "AlphaCentauriZoo/arithmetic.json"
  let ledger ← IO.FS.readFile (args[1]?.getD "forgive.yml" : String)
  initSearchPath (← findSysroot)
  -- Required by `importModules (loadExts := true)`, and by the delaborators naming the vertices.
  unsafe enableInitializersExecution
  let env ← importModules (loadExts := true) (Zoo.rootModules.map fun m => { module := m }) {}
  let (diagram, _, _) ← (Zoo.diagram (Zoo.openProblems ledger)).toIO
    { fileName := "<zoo>", fileMap := default } { env }
  IO.FS.writeFile output diagram.toJson.pretty
