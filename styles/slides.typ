#import "@preview/thmbox:0.3.0": thmbox

#let nospace = $#h(0pt)$

#let thm = thmbox.with(
  color: rgb("#245EA8"),
  variant: [Theorem 1],
  fill: rgb("#F1F5FA"),
  numbering: none,
  sans: false,
  title-fonts: ("Libertinus Serif",),
)

#let theme-primary = rgb("#04364A")
#let theme-secondary = rgb("#176B87")
#let theme-tertiary = rgb("#448C95")
#let intro-paper = rgb("#F5F3EF")
#let intro-border = rgb("#D7DEE2")
#let header-title-inset = 0.4em

#let section-subtitle(body) = [
  #v(-0.8em)
  #set text(
    size: 0.65em,
    fill: theme-secondary,
    weight: "regular",
  )
  #align(center, body)
]
