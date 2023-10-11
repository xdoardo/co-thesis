#import "@local/thesis:1.0.0": *

#import "./includes.typ": *
#set cite(style: "numerical")
#show bibliography: set text(13pt)

#show: thesis.with(
  title: "Program Transformations in the Delay Monad",
  subtitle: "A Case Study for Coinduction via Copatterns and Sized Types",
  author: "Edoardo Marangoni",
  figure: align(bottom, image("./figures/Minerva.png", width: 28%)),
  university: [University of Milan],
  department: [Department of Computer Science and Technology],
  degree: "Master of Science",
  msg: include "./msg.typ",
  supervisor: [Prof. Alberto Momigliano],
  year: [Academic Year 2022-2023], 
  number: [num. 973597], 
)

#pagebreak()
#pagebreak(to: "odd")
#include "./chapters/index.typ"

#pagebreak()
#pagebreak(to: "odd")
#appendix([#include "./appendices/index.typ"])


#set page(header: none)

#pagebreak()
#pagebreak(to: "odd")
#include "./thanks.typ"

#pagebreak(to: "odd")
#bibliography("./db.bib")
