# Euclid Book I formalization status

## Compiler status

A clean `lake build` succeeds for the root module `EuclidElements`, importing
all propositions I.1--I.48 and the Hilbert-style foundation bridge.

Current clean build: 86 targets, no build errors and no linter warnings.
There are no `sorry` or `admit` terms in the active Lean development.

## Hilbert-style foundation hierarchy

The project now contains a reusable foundation layer under
`EuclidElements/Foundations/`:

- `Incidence.lean` -- line existence/uniqueness and nontriviality of the plane.
- `Order.lean` -- strict betweenness, Pasch-style order, and plane separation.
- `Congruence.lean` -- segment/angle congruence equivalence, endpoint/arm
  reversal, same-ray invariance, and segment subtraction.
- `Continuity.lean` -- circle-circle and line-circle intersection principles.
- `Parallel.lean` -- the Euclidean parallel axiom, separated from construction
  postulates.
- `HilbertPlane.lean` -- `HilbertNeutralPlane` and `HilbertEuclideanPlane`
  bundles plus compatibility instances.
- `Book1Bridge.lean` -- compiler-checked demonstrations that I.1 and I.2 can be
  invoked from the new lower-level foundation classes.

Compatibility instances reconstruct the older `ImplicitAxioms`,
`Proposition2ImplicitAxioms`, and plane-separation interfaces from these lower
foundation classes.  An ordinary `Postulates G` instance automatically supplies
`EuclideanParallelAxiom G` from Euclid's fifth postulate.

## Material reductions completed in this foundational pass

### I.23

`proposition23_construction` now retains the noncollinearity of the copied
angle arm instead of discarding it.  The ordinary I.23 theorem remains as a
compatibility wrapper.

### I.24

The old `Proposition24ImplicitAxioms` schema directly assumed the decisive
angle inequality in the auxiliary triangle.  It is no longer used.

I.24 now depends on the generic `AngleRayConstructionAxioms`, which supplies
only the copied-angle/marked-ray construction and inside-angle data.  The key
comparison `∠EGF < ∠EFG` is proved from I.5 (the isosceles theorem), proper
subangle order, and transitivity.  Thus a substantive part of the former trust
boundary has become an ordinary Lean proof.

### I.27

The old `ParallelCriterionImplicitAxioms.meetingForcesAlternateOrder` field is
no longer used.  `meetingForcesAlternateOrder` is an ordinary theorem derived
from I.16 plus reusable plane-separation/order assumptions.

### I.28

The old corresponding-angle and supplementary-angle conversion assumptions
are no longer used.  They are derived directly from angle-congruence
transitivity and equal supplements.

### I.29

`Proposition29ImplicitAxioms` is no longer used.

The strict alternate-angle inequalities are converted directly into
Postulate-5 meeting conclusions using:

- `IncidenceAxioms` for line uniqueness,
- `OrderAxioms` for betweenness and half-plane companions,
- `CongruenceAxioms` for angle reversal/transitivity,
- `EuclideanParallelAxiom` for the actual Euclidean step.

The theorem statement was corrected to explicitly require the selected arms to
lie on opposite sides of the transversal.  The previous statement was too
strong because this orientation condition had been hidden in the old diagram
schema.

I.29 now requires the separated `EuclideanParallelAxiom G`, so its type records
precisely where Euclidean parallel geometry first enters Book I.

### I.31

`Proposition31ImplicitAxioms` is no longer used.

I.31 now explicitly performs Euclid's construction:

1. choose two distinct points on the given line using incidence;
2. join one to the external point;
3. copy the required alternate angle on the opposite side;
4. draw the new arm;
5. build the transversal configuration;
6. invoke I.27.

The remaining orientation choice is isolated as the generic
`OrientedAngleCopyAxioms`, rather than a proposition-specific parallel-line
construction schema.

## Legacy files no longer in the active proof chain

The following source files are retained only for comparison with the earlier
development and have no active references from the numbered theorem chain:

- `ParallelCriterionImplicitAxioms.lean`
- `Proposition24ImplicitAxioms.lean`
- `Proposition29ImplicitAxioms.lean`
- `Proposition31ImplicitAxioms.lean`

## Remaining strong local diagram schemas

The principal proposition-specific/local diagram interfaces still to reduce
are now:

- `Proposition30ImplicitAxioms`: common-transversal construction for I.30.
- `Proposition32ImplicitAxioms`: parallel-through-the-vertex diagram used for
  the exterior-angle/triangle-angle-sum theorem.
- `Proposition33ImplicitAxioms`: quadrilateral/diagonal incidence data.
- `Proposition34ImplicitAxioms`: diagonal data for parallelograms.
- `Proposition46ImplicitAxioms`: perpendicular/parallel square frame.

The generic construction interfaces still requiring a lower derivation are:

- `AngleRayConstructionAxioms`
- `OrientedAngleCopyAxioms`
- `TriangleConstructionImplicitAxioms`
- `Proposition16ImplicitAxioms`

These are substantially more reusable and less conclusion-shaped than the
schemas they replaced, but they remain part of the current trust boundary.

## Equal-figure / area block

I.35--I.45 and I.47--I.48 still use the synthetic equal-figure layer:

- `LaterAreaGeometry`
- `AreaDiagramGeometry`
- `AreaBookIImplicitAxioms`

No coordinates or real-valued area are introduced.  However,
`AreaBookIImplicitAxioms` contains strong region-composition schemas
corresponding to Euclid's cutting/adding/subtracting of figures.  Thus this
block remains compiler-verified relative to an explicit area calculus rather
than fully reduced to primitive incidence/order axioms.

## Recommended next reductions

1. Replace I.30's common-transversal schema with a generic three-line
   transversal/plane-order construction.
2. Use the now-explicit I.31 to reduce the I.32 vertex-parallel diagram to
   generic point-on-ray and side-selection lemmas plus I.29.
3. Strengthen the quadrilateral language with convexity/side-orientation data,
   then reduce I.33--I.34 directly via I.29 and congruence.
4. Replace the area schemas with a polygonal-region decomposition calculus and
   formal Common Notions 2--5.
5. Instantiate the hierarchy in the ordinary real Euclidean plane as an
   independent model/consistency theorem.
