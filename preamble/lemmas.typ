#import "@preview/lemmify:0.1.6": *
#import "@preview/showybox:2.0.1": showybox

// Define default theorem environments.
#let (theorem, lemma, corollary, remark, proposition, example, proof, definition, rules: thm-rules) = default-theorems(
  "thm-group",
  lang: "en",
  thm-numbering: thm-numbering-heading.with(max-heading-level: 1),
  thm-styling: (thm-type, name, number, body) => align(left)[*#thm-type #number* (#emph(name)) #body]
)

#show thm-selector("thm-group", subgroup: "proof"): it => box(
  it,
  stroke: red + 1pt,
  inset: 1em,
)

#let exercise(name, body) = showybox(frame: (
  border-color: silver,
))[
  #underline(smallcaps([Exercise #name:])) #body
]