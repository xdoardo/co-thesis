#import "@preview/ctheorems:0.1.0": *
#import "@preview/tablex:0.0.5": tablex, rowspanx, colspanx

#let theorem = thmbox("theorem", "Theorem", inset: (x: 1.2em, top: 0.2em))

#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong
)

#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))
#let property = thmbox("property", "Property",  inset: (x: 1.2em, top: 10pt, bottom: 10pt), stroke: rgb("#000000"))

#let example = thmplain("example", "Example", numbering:none)
#let proof = thmplain(
  "proof",
  "Proof",
  base: "theorem",
  bodyfmt: body => [#body #h(1fr) $square$],
).with(numbering:none)
