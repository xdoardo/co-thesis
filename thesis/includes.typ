#import "@preview/prooftrees:0.1.0"
#import "@local/boxes:0.1.0": *
#import "@preview/tablex:0.0.5": tablex, rowspanx, colspanx
#import "@preview/cetz:0.1.1": *
#import "@preview/diagraph:0.1.0": *

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

#let __agdabox = boxenv(
  "code",
  "snippet",
  heading,
  2,
  fmt: (name, number, body, url: none, label: none) => rect(
    width: 100%,
    fill: rgb("#dfebeb"),
    radius: 0.3em,
    inset: 10pt,
    align(center, [
      #body
      #text(font: "PragmataPro Mono Liga", size: 8pt, "snippet " + number)
      #h(5pt)
      #text(font: "PragmataPro Mono Liga", size: 8pt, "from Agda's stdlib")
      #if url != none and (not print) {
        h(5pt)
        link(
          url,
          underline(text(font: "PragmataPro Mono Liga", size: 8pt, "see code")),
        )
      }
    ]),
  ),
)

#let agdacode(label: none, url: none, placement: none, body) = {
  align(center, __agdabox(body, label: label, url: url, placement: placement))
}

#let __codebox = boxenv(
  "code",
  "snippet",
  heading,
  2,
  fmt: (name, number, body, url: none) => rect(
    width: 100%,
    fill: rgb(133, 144, 192, 10%),
    radius: 0.3em,
    inset: 10pt,
    align(center, [
      #body

      #text(font: "PragmataPro Mono Liga", size: 8pt, "snippet " + number)
      #if url != none and (not print) {
        h(5pt)
        link(
          url,
          underline(text(font: "PragmataPro Mono Liga", size: 8pt, "see code")),
        )
      }
    ]),
  ),
)

#let code(label: none, from: none, url: none, placement: none, body) = {
  align(center, __codebox(body, label: label, url: url, placement: placement))
}

#let __mycodebox = boxenv(
  "code",
  "snippet",
  heading,
  2,
  fmt: (name, number, body, label: none, url: none, proof: none) => rect(
    width: 100%,
    fill: rgb("#eeffee"),
    radius: 0.3em,
    inset: 10pt,
    align(
      center,
      [
        #body

        #if not print {
          link(
            url,
            underline(text(font: "PragmataPro Mono Liga", size: 8pt, "see code")),
          )
        }
        #if label != none {
          text(font: "PragmataPro Mono Liga", size: 8pt, ref(label))
          h(5pt)
        }
        #if proof != none and (not print) {
          h(5pt)
          underline(
            lower(text(font: "PragmataPro Mono Liga", size: 8pt, "see " + ref(proof))),
          )
        }
        #if number != none {
          h(5pt)
          lower(text(font: "PragmataPro Mono Liga", size: 8pt, "snippet " + number))
        }
      ],
    ),
  ),
)

#let mycode(label: none, proof: none, placement: none, url, body) = {
  align(
    center,
    __mycodebox(body, label: label, url: url, proof: proof, placement: none),
  )
}

#let theorem = boxenv("theorem", "Theorem", heading, 2)
#let lemma = boxenv("lemma", "Lemma", heading, 2)
#let corollary = boxenv("corollary", "Corollary", heading, 2)
#let definition = boxenv("definition", "Definition", heading, 2)
#let postulate = boxenv("postulate", "Postulate", heading, 2)
#let proof = boxenv("proof", "Proof", heading, 2)
#let refproof = boxenv(
  "proof",
  "Proof",
  heading,
  2,
  fmt: (name, number, body, thmref: none) => {
    strong("Proof") + [ #number ]
    [(for #ref(thmref))]
    if name != none { [ (#name) ] }
    h(10pt)
    body
  },
)

/// ---
#let conv(c, v) = { $#c arrow.b.double #v$ }
#let div(c) = { $#c arrow.t.double$ }
#let fails(c) = { $#c arrow.zigzag$ }
#let now = "now"
#let nothing = "nothing"
#let just = "just"
#let ceval = "ceval"
#let skip = "skip"
#let assign = "assign"
#let cwhile = "while"
#let aeval = "aeval"
