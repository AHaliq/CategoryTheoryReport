#let std-bibliography = bibliography

#let setup(
  title,
  author,
  authorid: "",
  subtitle: "",
  date: datetime.today(),
  preface: none,
  table-of-contents: outline(),
  bibliography: none,
  body,
) = {
  set text(lang: "en")
  set page(paper: "a4")
  set document(title: title, author: author)
  set text(font: ("Libertinus Serif", "Linux Libertine"), size: 11pt)
  // preamble
  
  page(align(left + horizon, block(width: 90%)[
      #let v-space = v(2em, weak: true)
      #text(3em)[*#title*]

      #v-space
      #text(1.6em, subtitle)

      #v-space
      #grid(
        columns: (auto, 1fr),
        text(size: 1.4em)[#upper[*Aarhus University* #h(0.15cm)]],
        image("../resources/au_logo_black.png", width: 0.7cm)
      )
      
      #text(1.4em)[#smallcaps[#author]]

      #if date != none {
        v-space
        // Display date as MMMM DD, YYYY
        text(date.display("[month repr:long] [day padding:zero], [year repr:full]"))
      }
  ]))
  // cover page

  if preface != none {
    page(
      align(center + horizon)[#preface]
    )
  }
  // preface page

  set outline(
    indent: auto,
    fill: box(width: 1fr, repeat[#text(silver)[-]])
  )
  if table-of-contents != none {
    table-of-contents
  }
  // table of contents


  set heading(numbering: "§1.1.1")
  set page(
    footer: context {
      // Get current page number.
      let i = counter(page).at(here()).first()

      // Align right for even pages and left for odd.
      let is-odd = calc.odd(i)
      let aln = if is-odd { right } else { left }

      // Are we on a page that starts a chapter?
      let target = heading.where(level: 1)
      if query(target).any(it => it.location().page() == i) {
        return align(aln)[#i]
      }

      // Find the chapter of the section we are currently in.
      let before = query(target.before(here()))
      if before.len() > 0 {
        let current = before.last()
        let gap = 1.75em
        let chapter = upper(text(size: 0.68em, current.body))
        if is-odd {
          align(aln)[#chapter #h(gap) #i]
        } else {
          align(aln)[#i #h(gap) #chapter]
        }
      }
    }
  )

  {
    // Start chapters on a new page.
    show heading.where(level: 1): it => {
      colbreak(weak: true)
      it
    }
    body
  }

  // Display bibliography.
  if bibliography != none {
    pagebreak()
    show std-bibliography: set text(0.85em)
    // Use default paragraph properties for bibliography.
    show std-bibliography: set par(leading: 0.65em, justify: false, linebreaks: auto)
    bibliography
  }
  // bibliography
}