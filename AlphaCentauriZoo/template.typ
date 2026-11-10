#import "@preview/diagraph:0.3.5": *

#let Theory(T) = $upright(sans(#T))$

// Labels are derived from the theories as Lean pretty-prints them, so that a new theory needs no
// entry of its own. A word written in Lean's theory notation, such as `𝗜𝚺⁺₁`, `𝗕𝚷1` or `𝗜𝚫 2`, is
// read glyph by glyph: bold sans-serif letters are the name, bold Greek capitals the class, and
// the digits and super- and subscripts its attachments. `∪` becomes `+`, `∼` becomes `¬`, and a
// set of sentences is drawn as its elements. Any other word must be a key of `names`, the last
// component of its Lean name; a function there receives the word's arguments. A vertex whose name
// cannot be read this way stops the compilation, unless `labels` gives it a label.

#let superscripts = (
  "⁺": "+", "⁻": "−", "ᶠ": "f",
  "⁰": "0", "¹": "1", "²": "2", "³": "3", "⁴": "4",
  "⁵": "5", "⁶": "6", "⁷": "7", "⁸": "8", "⁹": "9",
)

#let subscripts = (
  "₀": "0", "₁": "1", "₂": "2", "₃": "3", "₄": "4",
  "₅": "5", "₆": "6", "₇": "7", "₈": "8", "₉": "9",
)

#let is-digits(s) = s.len() > 0 and s.codepoints().all(c => c in "0123456789")

// The glyphs of a word in theory notation, or `none` if it is not one.
#let theory-word(word) = {
  let letters = ""
  let greek = ""
  let sup = ""
  let sub = ""
  for c in word.codepoints() {
    let u = str.to-unicode(c)
    if 0x1D5D4 <= u and u <= 0x1D5ED and greek == "" and sup == "" and sub == "" {
      letters += str.from-unicode(u - 0x1D5D4 + 0x41)
    } else if 0x1D5EE <= u and u <= 0x1D607 and greek == "" and sup == "" and sub == "" {
      letters += str.from-unicode(u - 0x1D5EE + 0x61)
    } else if 0x1D6A8 <= u and u <= 0x1D6C0 and sup == "" and sub == "" {
      greek += str.from-unicode(u - 0x1D6A8 + 0x391)
    } else if 0x1D756 <= u and u <= 0x1D76E and sup == "" and sub == "" {
      greek += str.from-unicode(u - 0x1D756 + 0x391)
    } else if c in superscripts and sub == "" {
      sup += superscripts.at(c)
    } else if c in subscripts {
      sub += subscripts.at(c)
    } else if c in "0123456789" {
      sub += c
    } else {
      return none
    }
  }
  if letters == "" and greek == "" { return none }
  (letters: letters, greek: greek, sup: sup, sub: sub)
}

#let draw-theory(w) = {
  let body = if w.letters != "" { $Theory(#w.letters)$ } + w.greek
  let sup = if w.sup != "" { w.sup }
  let sub = if w.sub != "" { w.sub }
  if sup == none and sub == none { body } else { math.attach(body, t: sup, b: sub) }
}

// Splits a pretty-printed theory into words and delimiters, and parses the expression starting at
// token `pos`. Returns the parsed items of each operand of `∪`, and the position after them.
#let parse(tokens, pos) = {
  let operands = ()
  let items = ()
  while pos < tokens.len() and tokens.at(pos) not in (")", "}", ",") {
    let t = tokens.at(pos)
    if t == "∪" {
      operands.push(items)
      items = ()
      pos += 1
    } else if t == "(" {
      let (inner, next) = parse(tokens, pos + 1)
      items.push((kind: "group", operands: inner))
      pos = next + 1
    } else if t == "{" {
      let elements = ()
      pos += 1
      while pos < tokens.len() and tokens.at(pos) != "}" {
        let (inner, next) = parse(tokens, pos)
        elements.push(inner)
        pos = if tokens.at(next, default: "}") == "," { next + 1 } else { next }
      }
      items.push((kind: "set", elements: elements))
      pos += 1
    } else if t == "∼" {
      items.push((kind: "not"))
      pos += 1
    } else {
      items.push((kind: "word", text: t))
      pos += 1
    }
  }
  operands.push(items)
  (operands, pos)
}

// Draws the operands of a `∪`, as parsed by `parse`.
#let draw(operands, names, vertex) = {
  let fail(what) = panic(
    "the zoo has no label for `" + vertex + "`: " + what + "; add it to `labels` or `names`",
  )
  let draw-items(items) = {
    if items.len() == 0 { fail("an operand is empty") }
    let (first, ..rest) = items
    if first.kind == "not" { return $not#draw-items(rest)$ }
    if first.kind == "group" {
      if rest.len() > 0 { fail("a group is applied to arguments") }
      return draw(first.operands, names, vertex)
    }
    if first.kind == "set" {
      if rest.len() > 0 { fail("a set is applied to arguments") }
      return first.elements.map(e => draw(e, names, vertex)).join($,$)
    }
    let w = theory-word(first.text)
    if w != none {
      // Further words are the class and the index of a theory written with a space, `𝗜𝚫 2`.
      for item in rest {
        if item.kind == "word" and is-digits(item.text) {
          w.sub += item.text
          continue
        }
        let v = if item.kind == "word" { theory-word(item.text) }
        if v == none or v.letters != "" { fail("`" + first.text + "` is applied to an argument") }
        w.greek += v.greek
        w.sup += v.sup
        w.sub += v.sub
      }
      return draw-theory(w)
    }
    if is-digits(first.text) and rest.len() == 0 { return first.text }
    let key = first.text.split(".").last()
    if key not in names { fail("`" + first.text + "` is unknown") }
    let value = names.at(key)
    if type(value) == function {
      return value(..rest.map(item => draw-items((item,))))
    }
    if rest.len() > 0 { fail("`" + key + "` is applied to arguments") }
    value
  }
  operands.map(draw-items).join($+$)
}

#let label-of(vertex, labels, names) = {
  if vertex in labels { return labels.at(vertex) }
  let tokens = vertex.matches(regex("[(){},]|∪|∼|[^\s(){},∪∼]+")).map(m => m.text)
  let (operands, pos) = parse(tokens, 0)
  if pos != tokens.len() { panic("the zoo cannot parse `" + vertex + "`") }
  $#draw(operands, names, vertex)$
}

// Equivalent theories are listed by name, then class `𝚺`, `𝚷`, `𝚫`, the broad hierarchies last.
#let member-key(vertex) = (
  vertex.contains("⁺"),
  vertex.replace("𝚺", "\u{1}").replace("𝚷", "\u{2}").replace("𝚫", "\u{3}"),
)

// Renders the JSON emitted by a `zoo_*` executable as a Graphviz digraph.
//
// Each vertex is a class of equivalent theories. An edge from `a` to `b` says that `a` is weaker
// than `b`, so the arrows are drawn from `b` to `a`: solid for `⪱`, dashed for `⪯`. An edge that
// is an open problem is drawn in red, and leaves the layout to the known relations wherever both
// of its ends have one.
#let zoo(path, labels: (:), names: (:), columns: 3, width: 640pt) = {
  let data = json(path)
  let node(i) = "c" + str(i)

  let node-labels = (:)
  for (i, members) in data.classes.enumerate() {
    let drawn = members.sorted(key: member-key).map(m => label-of(m, labels, names))
    node-labels.insert(node(i), stack(
      dir: ttb,
      spacing: 0.5em,
      ..drawn.chunks(columns).map(row => row.join($space equiv space$)),
    ))
  }

  let known = data.edges.filter(e => not e.conjectural).map(e => (e.from, e.to)).flatten()
  let edges = data.edges.map(e => {
    let attributes = ()
    if e.type == "sub" { attributes.push("style = dashed") }
    if e.type == "eq" { attributes.push("dir = none") }
    if e.conjectural {
      attributes.push("color = \"#c0392b\"")
      if e.from in known and e.to in known { attributes.push("constraint = false") }
    }
    let edge = node(e.to) + " -> " + node(e.from)
    if attributes.len() > 0 { edge += " [" + attributes.join(", ") + "]" }
    edge + ";"
  })

  raw-render(
    raw(
      "digraph Zoo {
        rankdir = TB;
        ranksep = 0.3;

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

      " + edges.join("\n") + "}",
    ),
    labels: node-labels,
    width: width,
  )
}
