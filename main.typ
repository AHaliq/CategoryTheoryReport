#import "preamble/style.typ"
#import "preamble/lemmas.typ": *

#show: style.setup.with(
  "Category Theory",
  "Abdul Haliq Abdul Latiff",
  authorid: "202303466",
  subtitle: "Projektarbejde i Datalogi 10ECTS (E24.520202U002.A)",
  preface: [This report is written for the course on Category Theory undertaken as a project module: "Projektarbejde i Datalogi 10ECTS (E24.520202U002.A)", under the supervision of Lars Birkedal and Alejandro Aguirre in Aarhus University as part of a MSc Computer Science program.],
  bibliography: bibliography("refs.bib"),
)

// ------------------------------------------------------------

#include "chapters/chapter1/index.typ"
#include "chapters/chapter2/index.typ"
#include "chapters/chapter3/index.typ"
#include "chapters/chapter4/index.typ"
#include "chapters/chapter5/index.typ"

#include "chapters/appendix.typ"