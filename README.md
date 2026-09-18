# Euclid's Elements in Lean — Books I–V

A synthetic Lean 4 formalization of Euclid's *Elements*, containing all 48
propositions of Book I, all 14 propositions of Book II, all 37 propositions of
Book III, and all 16 propositions of Book IV and all 25 propositions of Book V as Lean theorems.

## Verified status

The project is pinned to Lean `v4.19.0`. The root `EuclidElements` module imports
`EuclidElements.Book1`, `EuclidElements.Book2`, `EuclidElements.Book3`, and
`EuclidElements.Book4`, and `EuclidElements.Book5`.

The geometry remains synthetic: no coordinates, vector spaces, trigonometry,
numerical angle measure, or real-valued distance is used in the Euclid theorem
chain.

## Foundational architecture

The source separates Euclid's definitions/postulates/Common Notions, Hilbert-style
background assumptions, explicit geometry-only construction/diagram interfaces,
abstract equal-figure/area magnitude semantics, and the numbered propositions in
historical order. Hilbert does not replace Euclid's theorem chain; in particular
I.29 remains the first numbered theorem requiring Euclid V.

Assumptions are typeclass parameters rather than global Lean `axiom`
declarations.

## Book I

Book I contains I.1–I.48. The area block I.35–I.45 is synthetic rather than
numerical; I.47 is a dissection proof and I.48 a comparison-triangle/SSS proof.

## Book II — geometric algebra

Book II contains II.1–II.14 using abstract rectangle/square magnitudes and
Common-Notion-style addition/cancellation. The historical dependency chain is
preserved, including II.11 from II.6 and I.47.

## Book III — circles

Book III contains III.1–III.37. Selected arcs are explicit, III.7–III.8 expose
Euclid's historical “nearer” gap as a central-angle-order issue, III.16–III.19
derive the radius/tangent perpendicular chain, and III.35–III.37 derive the
power-of-a-point results from Book-II magnitude identities and I.47.

## Book IV — inscribed and circumscribed figures

Book IV contains IV.1–IV.16 and its seven definitions specialized to the
triangle/square/pentagon/hexagon/15-gon constructions used by Euclid.

Important logical choices:

- **IV.1** exposes the missing continuity step noted in the historical proof as
  `ShortChordContinuityAxioms`: every segment strictly below a diameter can be
  realized as a chord. The theorem handles the equal/strict cases explicitly.
- **IV.2–IV.3** use construction frames plus a generic third-angle consequence
  of I.32 rather than assuming the full equiangular conclusion.
- **IV.4** and **IV.8/IV.13** construct circles from equal perpendicular
  distances and derive each side tangency with III.16.
- **IV.5**, **IV.9**, and **IV.14** construct circumcircles from explicit
  equidistant-center candidates using Postulate 3.
- **IV.10** derives the doubled base angles from Euclid's intermediate
  tangent/exterior-angle configuration and synthetic angle addition; the
  doubled-angle conclusion is not a construction-field axiom.
- **IV.11 → IV.12** is explicit in Lean: the circumscribed pentagon starts from
  the inscribed regular pentagon obtained in IV.11, and IV.11 itself invokes
  IV.10.
- **IV.15** includes Euclid's corollary that the hexagon side equals the radius.
- **IV.16** explicitly invokes IV.2, IV.11, and IV.1. Its finite 15-gon
  combinatorics use an abstract `EqualFifteenArcSteps` predicate and a generic
  regularity bridge, avoiding numerical angle measures.

As in earlier books, some straightedge/compass incidence and finite-polygon
construction facts remain explicit foundation interfaces. They are separated
from numbered conclusions so they can later be discharged from a deeper
Hilbert-style construction model.

## Book V — Eudoxian ratio theory

Book V contains V.1–V.25 and all 18 ratio definitions in a synthetic magnitude framework. Natural multiples are repeated addition, and equality of ratios is Definition 5 itself: every pair of positive natural equimultiples has the same comparison pattern. No real-valued magnitudes, division, or quotient representation is introduced.

The Archimedean content of Definition 4 is explicit. The basic additive/order layer proves V.1–V.15, while the stronger comparison uses needed in the advanced theory are isolated in named interfaces for cross-comparison, componendo, ex-aequali composition, perturbed composition, and additive antecedents. V.17 is derived directly from Definition 5 by additive cancellation, V.19 is derived from alternendo plus V.17, and V.25 is derived from V.17, inverse proportion, V.14, and magnitude differences.

## Layout

```text
EuclidElements/
  Basic.lean
  Foundations/
  Book1/ ... Proposition01.lean ... Proposition48.lean
  Book1.lean
  Book2/ ... Proposition01.lean ... Proposition14.lean
  Book2.lean
  Book3/ ... Proposition01.lean ... Proposition37.lean
  Book3.lean
  Book4/ ... Proposition01.lean ... Proposition16.lean
  Book4.lean
EuclidElements.lean
lakefile.toml
lean-toolchain
```

## Build

```bash
lake build
```

A successful root build checks all five completed books.
