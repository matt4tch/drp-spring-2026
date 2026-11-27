#import "@preview/touying:0.7.4": *
#import themes.university: *
#import "@preview/numbly:0.1.0": numbly
#import "../styles/slides.typ": *

#show: university-theme.with(
  aspect-ratio: "16-9",
  align: horizon,
  header: self => pad(
    top: header-title-inset,
    utils.display-current-heading(depth: self.slide-level, style: auto),
  ),
  header-right: self => pad(
    top: header-title-inset,
    context {
      set text(fill: theme-secondary)
      let current = utils.current-heading(depth: self.slide-level)
      let parent-level = if current != none and current.level == 3 { 2 } else { 1 }
      (
        box(utils.display-current-heading(
          level: parent-level,
          depth: self.slide-level,
        ))
          + h(0.3em)
          + self.info.logo
      )
    },
  ),
  config-common(slide-level: 3),
  config-page(
    margin: (top: 2em, bottom: 2em, x: 2em),
  ),
  config-colors(
    primary: theme-primary,
    secondary: theme-secondary,
    tertiary: theme-tertiary,
  ),
  config-info(
    title: [Iteration of linear differential operators 2.0],
    author: [Jake Edmonstone, Matthew Tchouikine],
    date: datetime.today(),
    institution: [
      #emph[Mentor: Paul Cusson]
      #linebreak()
      #emph[University of Waterloo, WiM Directed Research Program]
    ],
  ),
)

#set heading(numbering: numbly("{1}.", default: "1.1"))

#set text(size: 23pt)

#title-slide(authors: ([Matthew Tchouikine], [Jake Bradley Edmonstone]))

// Set to false to omit the optional counterexample slides.
#let include-counterexample = true

#include "sections/recap.typ"
#include "sections/directions.typ"
#include "sections/theorem.typ"
#if include-counterexample {
  include "sections/counterexample.typ"
}
#include "sections/closing.typ"
