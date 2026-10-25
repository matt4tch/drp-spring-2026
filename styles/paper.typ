#import "@preview/thmbox:0.3.0": *

// Document formatting
#let main-font = "Libertinus Serif"

#let preamble(doc) = {
  show link: text.with(fill: blue)
  set page(margin: (x: 1.5cm), numbering: "1")
  set text(14pt, font: main-font)
  set heading(numbering: "1.")
  show math.equation.where(block: false): box
  show figure.where(kind: "stareq"): it => grid(
    columns: (1fr, auto),
    column-gutter: 1em,
    align: (center + horizon, horizon),
    block(width: 100%)[#align(center, it.body)],
    context it.counter.display(it.numbering),
  )
  doc
}

#let notes-title(title) = {
  align(center, text(24pt, weight: "bold", title))
  v(1em)
}

// Numbered theorem environments
#let setup-shared-counters(level) = doc => {
  show: thmbox-init(counter-level: level)
  doc
}

#let problem = thmbox.with(
  color: colors.blue,
  variant: [Problem],
  fill: rgb("#eef7ff"),
  numbering: none,
  sans: false,
  title-fonts: (main-font,),
)

#let thm = thmbox.with(
  color: colors.dark-red,
  variant: [Theorem],
  fill: rgb("#fdf1f2"),
  sans: false,
  title-fonts: (main-font,),
)

#let prop = thmbox.with(
  color: colors.light-blue,
  variant: [Proposition],
  fill: rgb("#f4f6fd"),
  sans: false,
  title-fonts: (main-font,),
)

#let lemma = thmbox.with(
  color: colors.light-turquoise,
  variant: [Lemma],
  fill: rgb("#f0fbf8"),
  sans: false,
  title-fonts: (main-font,),
)

#let defn = thmbox.with(
  color: colors.orange,
  variant: [Definition],
  fill: rgb("#fff4e6"),
  sans: false,
  title-fonts: (main-font,),
)

#let remark = thmbox.with(
  color: colors.gray,
  variant: [Remark],
  fill: rgb("#f8f8f8"),
  sans: false,
  title-fonts: (main-font,),
)

// Proofs and claims
#let qed() = {
  h(1fr)
  $square$
}

#let pf(body) = block[
  #set text(style: "oblique", weight: "bold")
  Proof:
  #set text(style: "normal", weight: "regular")
  #body
  #qed()
]

#let claim(title, body) = {
  let claim-title = [Claim #title]
  show figure.where(kind: "claim"): set block(breakable: true)
  figure(
    kind: "claim",
    supplement: "Claim",
    numbering: (..numbers) => title,
    caption: none,
    outlined: false,
  )[
    #block(width: 100%)[
      #align(left)[
        #strong(underline[_#claim-title:_])
        #body
      ]
    ]
  ]
}

#let verifclaim(title, body) = {
  let claim-title = [Verification of Claim #title]
  show figure.where(kind: "claim"): set block(breakable: true)
  figure(
    kind: "claim",
    supplement: "Verification of Claim",
    numbering: (..numbers) => title,
    caption: none,
    outlined: false,
  )[
    #block(width: 100%)[
      #align(left)[
        #strong(underline[_#claim-title:_])
        #body
      ]
    ]
  ]
}

// Numbered display equations
#let stareq(symbol: none, ..args) = {
  let body = args.pos().first()
  figure(
    kind: "stareq",
    supplement: none,
    numbering: (..numbers) => [(#symbol)],
    outlined: false,
    body,
  )
}

// Math shorthands
#let nospace = $#h(0pt)$
#let nosp = $nospace$
#let st = $mid(|)$
#let subs = $subset.eq$
#let nin = $in.not$
#let em = $emptyset$
#let mapstoo = $mapsto.long$
#let toinf(index) = $limits(stretch(arrow.r))_(#index -> oo)$

// Running header and footer
#let project-header(doc) = {
  set page(
    margin: (top: 2.5cm, bottom: 2.5cm),
    header-ascent: 25pt,
    footer-descent: 25pt,
    header: [
      #smallcaps[Directed Research Program]
      #h(1fr)
      #smallcaps[J. Edmonstone and M. Tchouikine]
      #block(spacing: .65em, line(length: 100%, stroke: 1pt))
    ],
    footer: context {
      let found = query(selector(heading).before(here())).rev().find(
        heading => heading.level <= 2,
      )
      if found != none { emph(found.body) }
      h(1fr)
      counter(page).display()
    },
  )
  doc
}
