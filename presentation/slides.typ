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
    title: [Iteration of linear differential operators],
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

#title-slide(authors: ([Jake Edmonstone], [Matthew Tchouikine]))

#include "sections/original-problem.typ"
#include "sections/l2.typ"
#include "sections/other-operators.typ"
#include "sections/x.typ"
#include "sections/x-squared.typ"
#include "sections/rest.typ"
