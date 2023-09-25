#import "@preview/prooftrees:0.1.0"
#import "@preview/ctheorems:0.1.0": *
#import "@preview/tablex:0.0.5": tablex, rowspanx, colspanx
#import "@preview/cetz:0.1.1": *

#let print = false

//Function to insert TODO
#let todo(body, inline: false, big_text: 40pt, small_text: 15pt, gap: 2mm) = {
  if inline {
    set text(fill: red, size: small_text, weight: "bold")
    box([TODO: #body
      #place()[
        #set text(size: 0pt)
        #figure(kind: "todo", supplement: "", caption: body, [])
      ]])
  } else {
    set text(size: 0pt) //to hide default figure text, figures is only used for outline as only headings and figures can used for outlining at this point
    figure(kind: "todo", supplement: "", outlined: true, caption: body)[
      #block()[
        #v(20pt)
        #set text(fill: red, size: big_text, weight: "bold")
        ! TODO !
      ]
      #v(gap)
      #block[
        #set text(fill: red, size: small_text, weight: "bold")
        #body
      ]
      #v(gap)
    ]
  }
}

//Function to insert TODOs outline
#let todo_outline = outline(title: [TODOs], target: figure.where(kind: "todo"))

#let coderef(label) = thmref(label)[snippet]


#let __agdabox = thmbox(
  "code",
  none,
  fill: rgb("#dfebeb"),
  stroke: none,
  inset: 10pt,
  radius: 0.3em,
  breakable: false,
  padding: (top: 0pt, bottom: 0pt),
  namefmt: x => [],
  titlefmt: strong,
  bodyfmt: x => x,
  separator: [],
  numbering: "1.1",
  base: "heading",
  base_level: none,
).with(numbering: none)

#let agdacode(ref: none, url: none, body) = {

  let b(_, _) = {
    [#underline(text(font: "PragmataPro Mono Liga", size: 8pt, "see proof"))]
  }


  align(center, __agdabox[
    #body
    #align(center, [
      #if ref != none {
        text(font: "PragmataPro Mono Liga", size: 8pt, "snippet " + thmref(ref))
        h(5pt)
      }
      #text(font: "PragmataPro Mono Liga", size: 8pt, "from Agda's stdlib")
      #if url != none and (not print) {
        link(
          url,
          underline(text(font: "PragmataPro Mono Liga", size: 8pt, "see code")),
        )
      }
    ])

    #if ref != none {
      ref
    }
  ])
}

#let __codebox = thmbox(
  "code",
  none,
  fill: rgb(133, 144, 192, 10%),
  stroke: none,
  inset: 10pt,
  radius: 0.3em,
  breakable: false,
  padding: (top: 0pt, bottom: 0pt),
  namefmt: x => [],
  titlefmt: strong,
  bodyfmt: x => x,
  separator: [],
  numbering: "1.1",
  base: "heading",
  base_level: none,
).with(numbering: none)


#let code(ref: none, from: none, url: none, body) = {
  let b(_, _) = {
    [#underline(text(font: "PragmataPro Mono Liga", size: 8pt, "see proof"))]
  }

  align(center, __codebox[
    #body
    #align(center, [
      #if ref != none {
        text(font: "PragmataPro Mono Liga", size: 8pt, "snippet " + thmref(ref))
        h(5pt)
      }
      #if from != none {
        text(font: "PragmataPro Mono Liga", size: 8pt, "from " + from)
        h(5pt)
      }
      #if url != none and (not print) {
        link(
          url,
          underline(text(font: "PragmataPro Mono Liga", size: 8pt, "see code")),
        )
      }
    ])

    #if ref != none {
      ref
    }
  ])
}


#let __mycodebox = thmbox(
  "code",
  none,
  fill: rgb("#eeffee"),
  stroke: none,
  inset: 10pt,
  radius: 0.3em,
  breakable: false,
  padding: (top: 0pt, bottom: 0pt),
  namefmt: x => [],
  titlefmt: strong,
  bodyfmt: x => x,
  separator: [],
  numbering: "1.1",
  base: "heading",
  base_level: none,
).with(numbering: none)


#let mycode(ref: none, proof: none, url, body) = {
  let b(_, _) = {
    [#underline(text(font: "PragmataPro Mono Liga", size: 8pt, "see proof"))]
  }

  align(center, __mycodebox[
    #body
    #align(center, [
      #if ref != none {
        text(font: "PragmataPro Mono Liga", size: 8pt, "snippet " + thmref(ref))
        h(5pt)
      }
      #if not print {
        link(
          url,
          underline(text(font: "PragmataPro Mono Liga", size: 8pt, "see code")),
        )
      }
      #if proof != none and (not print) {
        h(5pt)
        thmref(proof, fmt: b, makelink: true)
      }
    ])

    #if ref != none {
      ref
    }
  ])
}

#let conv(c, v) = { $#c arrow.b.double #v$ }
#let div(c) = { $#c arrow.t.double$ }
#let fails(c) = { $#c arrow.zigzag$ }

#let theorem = thmbox("theorem", "Theorem", inset: (x: 1.2em, top: 0.2em), breakable: false)
#let lemma = thmbox("lemma", "Lemma", inset: (x: 1.2em, top: 0.2em), breakable: false)

#let corollary = thmplain("corollary", "Corollary", base: "theorem", titlefmt: strong)

#let definition = thmbox(
  "definition",
  "Definition",
  inset: (x: 1.2em, top: 10pt),
  breakable: false,
)
#let property = thmbox(
  "property",
  "Property",
  inset: (x: 1.2em, top: 10pt, bottom: 10pt),
  stroke: rgb("#000000"),
)

#let example = thmplain("example", "Example", numbering: none)
#let proof = thmplain(
  "proof",
  "Proof",
  base: "theorem",
  bodyfmt: body => [#body #h(1fr) $square$],
).with(numbering: none)
