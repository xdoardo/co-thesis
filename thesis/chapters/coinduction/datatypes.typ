#import "/includes.typ": *

== Recursive datatypes<section-induction_coinduction-recursive_datatypes>
The easiest and most intuitive inductive datatype is that of natural numbers. In
type theory, one may represent them as follows:
#figure(
  tablex(
    columns: 4,
    align: center + horizon,
    auto-vlines: false,
    auto-hlines: false,
    colspanx(
      2,
    )[#prooftrees.tree(
          prooftrees.axi[],
          prooftrees.uni(line_config: prooftrees.line_config(stroke: 2pt))[$NN : "Type"$],
        )],
    colspanx(2)[type formation],
    prooftrees.tree(prooftrees.axi[], prooftrees.uni[$0 : NN$]),
    [zero],
    prooftrees.tree(prooftrees.axi[$n : NN$], prooftrees.uni[$S space n : NN$]),
    [succ],
  ),
)
Or, in Agda:
#code()[
  ```hs
  data Nat : Set where
   zero : Nat
   succ : Nat -> Nat
  ```
]
We can imagine concrete instances of this datatype as trees reflecting the
structure of the constructors as shown in @fig-nat-tree. We might want to show
some properties of these inductive datatypes, and the tool to do so is the
_principle of induction_.
#figure(placement: auto, canvas({
  import draw: *

  tree.tree(
    ([...], ([succ succ zero], ([succ zero], [zero]))),
    spread: 2.5,
    grow: 1.5,
    draw-node: (node, _) => {
      circle((), radius: .45, stroke: none)
      content((), node.content)
    },
    draw-edge: (from, to, _) => {
      line(
        (a: from, number: .6, abs: true, b: to),
        (a: to, number: .6, abs: true, b: from),
        mark: (start: ">"),
      )
    },
    name: "tree",
  )
}), caption: "Structure of a natural number as tree of constructors")<fig-nat-tree>

