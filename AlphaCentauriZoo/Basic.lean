module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Lean.Data.Json

/-!
# Zoo diagrams

A zoo is a directed graph whose vertices are theories and whose edges record how their
provability strengths compare. This module turns the edges collected from a Lean environment by
the executables rooted at the other modules of `Zoo` into a diagram: equivalent theories are
merged into one class, and only the edges between classes that do not follow from the others are
kept.
-/

@[expose] public section

open Lean

namespace Zoo

/-- How the two endpoints of an edge of a zoo compare in provability strength. -/
inductive EdgeType
  /-- `⪱`: the source is strictly weaker than the target. -/
  | ssub
  /-- `⪯`: the source is weaker than the target. -/
  | sub
  /-- `≊`: the two endpoints are equivalent. -/
  | eq
deriving BEq, Hashable, Repr, Inhabited

namespace EdgeType

instance : ToString EdgeType where
  toString
    | .ssub => "ssub"
    | .sub  => "sub"
    | .eq   => "eq"

/-- Relation witnessed by an edge of type `t` followed by an edge of type `u`. -/
def comp : (t u : EdgeType) → EdgeType
  | .eq,   u     => u
  | t,     .eq   => t
  | .sub,  .sub  => .sub
  | .ssub, _     => .ssub
  | _,     .ssub => .ssub

/-- Whether a relation of type `t` entails one of type `u`. -/
def entails : (t u : EdgeType) → Bool
  | .eq,   .eq   => true
  | .eq,   .sub  => true
  | .ssub, .ssub => true
  | .ssub, .sub  => true
  | .sub,  .sub  => true
  | _,     _     => false

/-- The strongest of a set of relations holding between two theories in distinct classes. -/
def strongest (ts : Std.HashSet EdgeType) : Option EdgeType :=
  if ts.contains .ssub then some .ssub
  else if ts.contains .sub || ts.contains .eq then some .sub
  else none

end EdgeType

/-- An edge `⟨a, b, t⟩` records that the theories `a` and `b` are related by `t`. -/
structure Edge where
  src : String
  dst : String
  type : EdgeType
deriving BEq, Hashable, Repr, Inhabited

abbrev Edges := Std.HashSet Edge

/-- An edge of a diagram, between the classes of the given indices. -/
structure Diagram.Edge where
  src : Nat
  dst : Nat
  type : EdgeType
  /-- Whether the relation is an open problem rather than a known fact. -/
  conjectural : Bool
deriving BEq, Inhabited

/--
A zoo ready to be drawn: the classes of equivalent theories, and the edges between them that do
not follow from the others.
-/
structure Diagram where
  classes : Array (Array String)
  edges : Array Diagram.Edge

namespace Edges

/--
Outgoing edges of each vertex. An `≊` edge is traversable in both directions, so that a `⪯`
already witnessed by an equivalence counts as redundant.
-/
def adjacency (es : Edges) : Std.HashMap String (Array (String × EdgeType)) :=
  es.fold (init := ∅) fun adj e =>
    let adj := adj.insert e.src ((adj.getD e.src #[]).push (e.dst, e.type))
    if e.type == .eq then adj.insert e.dst ((adj.getD e.dst #[]).push (e.src, .eq)) else adj

/--
For every vertex reachable from `src`, the relations witnessed by some path leading to it.
A vertex carries at most three relations, so the search visits each edge a bounded number of times.
-/
def relationsFrom (adj : Std.HashMap String (Array (String × EdgeType))) (src : String) :
    Std.HashMap String (Std.HashSet EdgeType) := Id.run do
  let mut found : Std.HashMap String (Std.HashSet EdgeType) := ∅
  let mut pending := adj.getD src #[]
  while !pending.isEmpty do
    let (v, t) := pending.back!
    pending := pending.pop
    let ts := found.getD v ∅
    if ts.contains t then continue
    found := found.insert v (ts.insert t)
    for (w, u) in adj.getD v #[] do
      pending := pending.push (w, t.comp u)
  return found

/-- Names are listed shortest first, so that a theory's own notation comes before an unfolding. -/
def nameLt (a b : String) : Bool := a.length < b.length || (a.length == b.length && a < b)

/--
The diagram of the theories satisfying `keep`, given the relations that are known, `proved`, and
those that are open problems, `conjectured`.

Theories are merged into one class when `proved` makes them equivalent, and an edge is drawn when
it does not follow from the others. Relations through theories failing `keep` still count: the
classes and edges are computed from the transitive closure of all of `proved`. A conjectured edge
is drawn unless `proved` already settles it or it follows from another conjectured edge. A class
left with no edge is not drawn.

Fails if `proved` makes a theory strictly weaker than itself.
-/
def diagram (proved conjectured : Edges) (keep : String → Bool) : Except String Diagram := do
  let adj := adjacency proved
  let vertices := (proved.toArray ++ conjectured.toArray).foldl (init := (∅ : Std.HashSet String))
    fun vs e => (vs.insert e.src).insert e.dst
  let closure : Std.HashMap String _ :=
    vertices.fold (init := ∅) fun m v => m.insert v (relationsFrom adj v)
  let rel (a b : String) : Std.HashSet EdgeType := (closure.getD a ∅).getD b ∅
  for v in vertices do
    if (rel v v).contains .ssub then
      throw s!"the edges prove `{v}` strictly weaker than itself"
  -- Two theories are equivalent when each is reachable from the other.
  let kept := vertices.toArray.filter keep |>.qsort nameLt
  let mut classes : Array (Array String) := #[]
  for v in kept do
    match classes.findIdx? fun c => !(rel v c[0]!).isEmpty && !(rel c[0]! v).isEmpty with
    | some i => classes := classes.modify i (·.push v)
    | none => classes := classes.push #[v]
  classes := classes.qsort fun c d => nameLt c[0]! d[0]!
  let classOf : Std.HashMap String Nat := classes.size.fold (init := ∅) fun i _ m =>
    classes[i]!.foldl (init := m) (·.insert · i)
  let classRel (i j : Nat) : Option EdgeType :=
    if i == j then some .eq else EdgeType.strongest (rel classes[i]![0]! classes[j]![0]!)
  let n := classes.size
  let mut edges : Array Diagram.Edge := #[]
  for i in [0:n] do
    for j in [0:n] do
      if i == j then continue
      let some t := classRel i j | continue
      let redundant := (List.range n).any fun k =>
        k != i && k != j && match classRel i k, classRel k j with
          | some t₁, some t₂ => (t₁.comp t₂).entails t
          | _, _ => false
      unless redundant do edges := edges.push ⟨i, j, t, false⟩
  -- The conjectured edges `proved` does not settle, read in both directions when symmetric.
  let conjectures : Array Diagram.Edge := conjectured.toArray.filterMap fun e => do
    let i ← classOf[e.src]?
    let j ← classOf[e.dst]?
    guard <| !(classRel i j).any (·.entails e.type)
    return ⟨i, j, e.type, true⟩
  let directed := conjectures ++
    (conjectures.filter (·.type == .eq)).map fun e => { e with src := e.dst, dst := e.src }
  let follows (e : Diagram.Edge) : Bool := directed.any fun f =>
    !(f.src == e.src && f.dst == e.dst && f.type == e.type) &&
      match classRel e.src f.src, classRel f.dst e.dst with
        | some t₁, some t₂ => ((t₁.comp f.type).comp t₂).entails e.type
        | _, _ => false
  for e in conjectures do
    unless follows e || edges.contains e do edges := edges.push e
  -- Drop the classes left with no edge, and renumber the others.
  let used := edges.foldl (init := (∅ : Std.HashSet Nat)) fun s e => (s.insert e.src).insert e.dst
  let drawn := (List.range n).filter used.contains
  let index : Std.HashMap Nat Nat := drawn.zipIdx.foldl (init := ∅) fun m (i, k) => m.insert i k
  return {
    classes := drawn.toArray.map (classes[·]!)
    edges := edges.map fun e => { e with src := index[e.src]!, dst := index[e.dst]! } }

end Edges

/-- The diagram as JSON. -/
def Diagram.toJson (d : Diagram) : Json :=
  Json.mkObj [
    ("classes", Lean.toJson d.classes),
    ("edges", .arr <| d.edges.map fun e =>
      Json.mkObj [("from", e.src), ("to", e.dst), ("type", toString e.type),
        ("conjectural", e.conjectural)])]

end Zoo
