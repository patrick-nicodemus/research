#import "@preview/ctheorems:1.1.3": *
#show: thmrules
// Preamble file
#let theorem = thmbox("theorem", "Theorem", fill:rgb("#eeffee"))
#let corollary = thmplain("corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong
)

#let porism = thmplain("porism",
  "Porism",
  base: "theorem",
  titlefmt: strong
)

#let lemma = thmplain("lemma",
  "Lemma",
  base: "theorem",
  titlefmt: strong
)

#let definition = thmbox(
  "definition",
  "Definition",
  inset: (x : 1.2em, top:1em)
)

#let observation = thmbox(
  "observation",
  "Observation",
  inset: (x : 1.2em, top:1em)
)
#let proof = thmproof("proof", "Proof")
// #theorem[There are infinitely many prime numbers.]
// #corollary[There is a prime number greater than 9.]
// #definition[A natural number $n$ is said to be *prime* if it has no factors either than itself or 1.]
