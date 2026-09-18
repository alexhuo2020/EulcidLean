# Foundational notes

## Goal

This project is a **synthetic** Lean formalization of Euclid's *Elements*.
The Book I development does not identify points with pairs of real numbers and
does not define segment length or angle measure numerically.

A later analytic model may interpret the abstract language, but the Book I
proofs themselves remain synthetic.

## Logical architecture: Hilbert underneath, Euclid on top

The project deliberately separates two roles.

### Hilbert-style role

Hilbert-style incidence, order, congruence, continuity, and parallel classes are
an implementation layer for geometric facts that Euclid tacitly assumes.  They
are useful because they organize hidden assumptions into reusable categories
instead of accumulating proposition-specific folklore.

They do **not** replace the logical order of the *Elements*.

### Euclid-style role

Euclid's definitions, five postulates, Common Notions, constructions, and
numbered propositions remain the theorem-level development.  A proof of I.n may
use earlier Euclid propositions and the explicitly declared background
interfaces, but it may not use a later proposition merely because that result
is derivable in a Hilbert system.

Thus the intended architecture is:

```text
Hilbert-style background interfaces
  incidence / order / congruence / continuity
                  |
                  v
Euclid's explicit postulates + visible adapters for tacit assumptions
                  |
                  v
I.1 -> I.2 -> ... -> I.28
                  |
                  +---- neutral/absolute portion

Euclid V / EuclideanParallelAxiom
                  |
                  v
I.29 -> ... -> I.48
```

`Foundations/EuclidCompatible.lean` records this discipline directly in Lean.
`HilbertNeutralPlane` contains no parallel axiom; the Euclidean bundle adds the
parallel axiom separately.  In particular, I.28 remains on the neutral side,
and I.29 is the first numbered proposition whose formal theorem requires the
Euclidean parallel layer.

## Euclid's definitions

Some definitions are operational and become Lean predicates: circles,
diameters, right angles, triangles, squares, and parallel lines.

Definitions 1--7 are descriptions of primitives rather than modern recursive
definitions.  Statements such as "a point is that which has no part" are kept
as documentation of intended meaning rather than converted into artificial
predicates with no proof-theoretic role.

## The five explicit postulates

`Book1.Postulates` contains Euclid's five postulates.  The fifth is kept in its
original transversal/interior-angle form rather than silently replacing it with
Playfair's axiom.

The separate `EuclideanParallelAxiom` class exposes the same parallel content to
the Hilbert-style foundation layer; the compatibility instance from
`Postulates` keeps the two views synchronized.

## Hidden assumptions

Euclid repeatedly uses background facts that are not consequences of the five
postulates as literally stated.  These assumptions are kept explicit.  Examples
include:

- uniqueness of the line through two distinct points;
- strict betweenness/order facts;
- congruence equivalence laws;
- circle-circle and line-circle continuity;
- Pasch/plane-separation facts;
- superposition/congruence principles;
- synthetic area composition and cancellation.

The goal is not to erase those historical gaps, but to classify them and, where
possible, derive them from reusable Hilbert-style foundation classes.

## Why I.1 needs an extra intersection principle

Postulate 3 says that a circle with a given center and radius may be drawn.  It
does not itself guarantee that two such circles intersect.  Proposition I.1
nevertheless chooses their intersection.

The formalization therefore isolates exactly the needed continuity principle:
if `A ≠ B`, the circle centered at `A` through `B` and the circle centered at
`B` through `A` possess a common point off `AB`.

This principle lives in the continuity/background layer rather than being
silently folded into Postulate 3.

## Dependency objective

The research value of the formalization is not only theorem checking but an
audit of the *Elements*' logical structure.  For each proposition we want to
know:

- which explicit Euclid postulates are used;
- which Common Notions are used;
- which earlier propositions are used;
- which tacit geometric principles are required;
- whether those tacit principles can be derived from the Hilbert-style core.

The Hilbert layer is therefore a tool for **explaining Euclid's hidden logical
infrastructure**, not a license to rewrite Euclid's proofs in a different
logical order.
