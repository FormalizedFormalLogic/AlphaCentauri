#import "@preview/diagraph:0.3.5": *
#import "@preview/oxifmt:1.0.0": strfmt

#let Theory(T) = $upright(sans(#T))$

// Renders the JSON emitted by a `zoo_*` executable as a Graphviz digraph.
//
// An edge `a -> b` of the JSON says that `a` is weaker than `b`, so the arrows are drawn from `b`
// to `a`: solid for `⪱`, dashed for `⪯`, and as an undirected double line for `≊`.
//
// Theories listed in `omit` are dropped along with every edge touching them.
#let zoo(path, labels: (:), omit: (), width: 640pt) = {
  let data = json(path).filter(((from, to, ..)) => {
    not omit.contains(from) and not omit.contains(to)
  })

  // Equivalent theories are the same strength, so they belong on one row of the diagram.
  // The `≊` edges are merged into classes, each drawn as a `rank = same` subgraph.
  let classes = ()
  for e in data.filter(e => e.type == "eq") {
    let i = none
    let j = none
    for (k, c) in classes.enumerate() {
      if c.contains(e.from) { i = k }
      if c.contains(e.to) { j = k }
    }
    if i == none and j == none {
      classes.push((e.from, e.to))
    } else if i == none {
      classes.at(j) = classes.at(j) + (e.from,)
    } else if j == none {
      classes.at(i) = classes.at(i) + (e.to,)
    } else if i != j {
      let (keep, drop) = (calc.min(i, j), calc.max(i, j))
      classes.at(keep) = classes.at(keep) + classes.at(drop)
      classes.remove(drop)
    }
  }
  let ranks = classes
    .map(c => "{ rank = same; " + c.map(v => "\"" + v + "\"").join("; ") + " }")
    .join("\n        ")

  let edges = data.map(((from, to, type)) => {
    if type == "ssub" {
      strfmt("\"{}\" -> \"{}\"", to, from)
    } else if type == "sub" {
      strfmt("\"{}\" -> \"{}\" [style = dashed]", to, from)
    } else if type == "eq" {
      strfmt("\"{}\" -> \"{}\" [dir = none, color = \"black:black\"]", to, from)
    }
  })

  raw-render(
    raw(
      "digraph Zoo {
        rankdir = TB;

        node [
          shape = none
          margin = 0.05
          width = 0
          height = 0
        ]

        edge [
          style = solid
          arrowhead = vee
          arrowsize = 0.5
        ];

      " + ranks + "\n\n      " + edges.join("\n") + "}",
    ),
    labels: labels,
    width: width,
  )
}
