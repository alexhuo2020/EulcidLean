# Project note: Book X status and transition to Books XI–XIII

## Current scope

The Lean project now contains formal developments for Books I–IX and a substantive opening portion of Book X. Book X is intentionally **not marked complete**.

Implemented Book X propositions:
- X.1–X.16, except X.17–X.18;
- X.19–X.21.

The current Book X layer includes synthetic notions of measurement by natural multiples; commensurable and incommensurable magnitudes; number ratios; greatest common measures; commensurability in square; rational and irrational magnitudes relative to a fixed rational line; and the rectangle/square area transport needed for X.19–X.21.

## Design choices

Book X is not encoded by identifying all magnitudes with real numbers. It reuses Book V's abstract additive magnitude structure and Eudoxian ratio language, preserving the distinction between lines, areas, and other kinds of magnitude.

Primitive assumptions are kept narrow: Archimedean/exhaustion existence for X.1; construction content for greatest common measures; transport of commensurability through equal ratios; and square/rectangle scaling facts requiring geometric area machinery. Derived results are proved from these primitives rather than postulated under the name of the Euclidean proposition.

## Known Book X gaps

X.17 and X.18 remain open. Their historical statements concern applying a parallelogram to a rational straight line deficient by a square and relating the deficiency to rationality/irrationality. A faithful proof needs a stronger application-of-areas interface tied to VI.27–VI.29 and Book II area algebra. They have deliberately not been replaced by tautological or proposition-shaped axioms.

The later Book X classification of binomials, apotomes, and their many species is also not yet formalized. Before extending deeply into X.22–X.115, the area and square-root classification layer should be strengthened.

## Build status at this checkpoint

The full top-level `EuclidElements` target builds successfully. The Book X files contain no `sorry` or `admit`.

## Transition to Book XI

Books XI–XIII require an explicit synthetic 3-dimensional incidence language. Euclid supplies definitions but no new solid-geometry postulates. Accordingly, this formalization introduces a minimal solid incidence foundation: points, lines, planes, containment, line/plane intersection, perpendicularity, and parallelism.

The first incidence principles correspond to background assumptions Euclid uses implicitly in XI.1–XI.3 (for example, intersecting lines determine a plane). They are recorded openly as foundations rather than hidden inside later propositions.

## Book XI progress after XI.10

Implemented XI.11--XI.16 and XI.18 using explicit normal-construction, uniqueness, plane-parallel, and plane-perpendicular structure. XI.17 is intentionally deferred because its statement compares ratios of spatial line segments cut by parallel planes; the current `SpaceGeometry` has incidence and direction but no segment-magnitude map. The next faithful extension should add a spatial segment-magnitude interface and then derive XI.17 using XI.16 plus a planar VI.2 bridge, rather than postulating the ratio conclusion.

## Book XI solid-angle transition

XI.19 is now represented using a generic semantic law for the intersection of two planes perpendicular to a third. XI.20--XI.23 are deliberately not encoded by folding their conclusions into the definition of a solid angle. `TrihedralAngle` records only the three incident rays at one vertex. A faithful continuation therefore needs a separate plane-angle magnitude/order/addition layer, plus cross-plane transport of Book I angle constructions, before XI.20 (pairwise angle-sum inequality), XI.21 (sum less than four right angles), XI.22 (triangle from chords), and XI.23 (solid-angle construction) can be proved non-tautologically.

## Book XI solid-angle construction status

XI.20 is represented as the triangle inequality for the abstract angular metric on rays. XI.21 uses a separate convex-trihedral predicate and its spherical-perimeter bound. XI.22 is factored through a reusable equal-radius chord transfer theorem, producing the three side inequalities needed by I.22. XI.23 is not yet marked complete: the historical proof assumes a circumcenter configuration and David Joyce notes additional cases when the circumcenter lies outside or on the boundary of the constructed triangle. A faithful formalization should add a circumcircle/circumcenter construction layer plus all three position cases before asserting the full realization theorem.

## XI.23 status and remaining reduction gap

`Proposition23.lean` now compiles as a composition of reusable construction layers: triangle-from-three-lengths, circumcenter construction with an explicit inside/boundary/outside classification, circumradius comparison, perpendicular apex lift, and SSS recovery of the three face angles. This repairs the case distinction missing in Euclid's written proof at the interface level.

However, `CircumradiusBoundAxioms` is still a genuine remaining reduction gap: it packages the difficult theorem that the common proposed edge exceeds the circumradius of the base chord triangle under the XI.20/XI.21 admissibility hypotheses, uniformly for all three circumcenter positions. Therefore XI.23 should not yet be described as fully derived from Books I--XI primitive foundations. The next proof-refinement task is to replace that interface by smaller generic chord/radius monotonicity lemmas and prove the three circumcenter-position cases explicitly.

For XI.24, use the corrected hypothesis from Joyce's guide: a parallelepiped is bounded by three pairs of parallel planes. Euclid's literal broader wording is false for general solids merely having some parallel supporting faces.

## Book XI.24

XI.24 is formalized for the mathematically correct parallelepiped hypothesis: six face planes occur in three parallel pairs.  The formalization records all twelve intersection edges and eight vertices, derives all six faces are parallelograms via XI.16, obtains opposite-side metric equalities through a generic planar I.34 bridge, and obtains corresponding angle equalities from the spatial parallel-pair angle law.  It proves all three pairs of opposite faces equal/similar in corresponding side lengths and angles.  This intentionally strengthens/corrects Euclid's overly broad literal wording "solid contained by parallel planes."

## Book XI progress through XI.29

Implemented XI.25--XI.29.

- XI.25 introduces explicit planar-area and solid-volume magnitude kinds.  The theorem itself is a direct application of Book V Definition 5 once a generic prismatic multiple-comparison principle is supplied.  This principle makes explicit the hidden cut-and-paste comparison step noted in the historical proof rather than silently assuming the final ratio.
- XI.26 is expressed through a reusable trihedral-angle transport construction at a prescribed point/ray.
- XI.27 uses a generic similar-parallelepiped construction interface recording the copied trihedral angle and adjacent-edge ratios.  This remains construction-layer dependent and is not yet reduced all the way to XI.26 + VI.12 internally.
- XI.28 uses abstract solid regions and XI.Def.10-style congruent-boundary volume equality.  This intentionally avoids relying on orientation-preserving superposition, so mirror-image prism halves still have equal volume.
- XI.29 is a genuine cut-and-paste volume proof from a common region plus congruent remainder regions.

Remaining foundational gaps: the prismatic multiple-comparison principle behind XI.25, the full internal realization of XI.27 from XI.26/VI.12, and the production of XI.28/XI.29 diagram data from raw incidence hypotheses are still generic foundation interfaces rather than derived consequences.

## Gap reduction after XI.29

- XI.25 no longer assumes preservation of all natural-multiple comparisons.  It now uses a same-altitude additive order embedding from base-area magnitudes to solid magnitudes.  Commutation with `Book5.Multiple` is proved by induction, and the three clauses of V.Def.5 are derived from that embedding.
- XI.27 no longer uses a proposition-shaped `constructOnEdge` oracle.  It is assembled from XI.26 trihedral-angle transport, two generic fourth-proportional-on-ray constructions (spatial VI.12 bridge), and generic completion of three adjacent edges to a parallelepiped.  Nondegeneracy of the three source adjacent edges is now explicit.
- XI.28 no longer receives a completed diagonal cut as theorem input.  It starts from a `ParallelepipedFrame`; a generic diagonal-cut construction produces the two regions, their partition, and boundary congruence, after which equal volume follows from the solid-region congruence law.  The remaining primitive gap is the generic geometric fact that the diagonal cut has congruent boundary data.
- XI.29 now states Euclid's actual geometry: same base, same height/opposite plane, and aligned endpoints of the standing edges.  A generic aligned-parallelepiped decomposition constructs the common region and the two remainder prisms; the theorem then proves equality by congruent remainders plus additive volume.  The remaining primitive gap is the generic construction/decomposition theorem, not the final volume equality itself.


## XI.28-XI.29 deeper gap reduction

- XI.28 no longer accepts or constructs a ready-made boundary-congruence proof.
  The cut constructor now only creates the two regions, their partition, and
  realizations of two fixed triangular-prism boundaries determined by the AC/EG
  diagonal split.  Five-face congruence is assembled separately: bottom and top
  diagonal triangles, the two pairs of opposite side faces, and the common
  diagonal quadrilateral.
- `PolyhedralFaceGeometry` now has concrete triangle/quadrilateral constructors,
  reflexive congruence, SSS triangle congruence, and an equal-similar quadrilateral
  bridge.  This exposes the exact planar data needed by XI.Def.10 instead of an
  opaque solid-congruence predicate.
- XI.29 now separates three layers: (1) aligned same-base geometric decomposition,
  (2) proof that the two remainder prism boundaries are congruent, and (3) the
  additive volume argument.  The decomposition class no longer returns a
  congruence result.
- Remaining primitive geometry after this reduction: the generic planar
  `ParallelepipedDiagonalFaceAxioms` consequences (I.34/SSS + XI.24) and the
  `AlignedRemainderGeometry` theorem packaging Euclid's I.34, I.8/I.4, I.36
  face-matching argument for XI.29.  These are now face-level geometric lemmas,
  not proposition-level solid-equality or volume axioms.


## XI.29 raw-face reduction

The former `AlignedRemainderPlanarAxioms` congruence oracle has been removed.
XI.29 now derives prism-boundary congruence from raw face witnesses:
- `TriangleFaceSSSWitness` records only three side equalities and identifies the two triangular faces;
- `QuadFaceEqualSimilarWitness` records only the incidence, four side equalities, and four angle equalities for a quadrilateral pair;
- `triangleFaceCongruent_of_witness` and `quadFaceCongruent_of_witness` derive the face congruences through the generic SSS / equal-similar face interfaces;
- `alignedRemainderFacesCongruent` assembles the five derived face congruences into the XI.Def.10 prism-boundary relation.

Thus the remaining XI.29 primitive gap is no longer a congruence theorem. It is the extraction of those raw metric/incidence witnesses from the concrete aligned same-base figure (the I.34, I.8/I.4, I.36 diagram chase). The segment-subtraction equalities used in that extraction are already proved by `equalRemainders_of_nestedSegments`.


## XI.28-XI.29 face-level gap reduction

The XI.28 and XI.29 face-congruence oracles have been removed. XI.28 now proves its five prism-face matches explicitly from XI.24, SSS, opposite-face equality/similarity, and reflexivity. XI.29 uses canonical remainder-prism boundaries; its two triangular ends are proved congruent by SSS after Euclid's segment-subtraction step, its two inherited side faces come directly from XI.24, and its top-strip faces are proved equal/similar using explicit alignment incidences, top-face parallelogram equalities, and generic parallel-angle transport. The former `ParallelepipedDiagonalFaceAxioms`, `AlignedRemainderGeometry`, `AlignedRemainderBoundaryRelation`, and `AlignedStripFaceAxioms` layers are absent. Remaining primitive layers are geometric realization/decomposition (`DiagonalParallelepipedCutConstructionAxioms`, `AlignedParallelepipedDecompositionAxioms`), polyhedral-face semantics, and generic solid cut-and-paste/volume laws.

## XI.28--XI.30 region/face reduction update

XI.28 now proves that the two diagonal triangular-prism regions form a disjoint union of the canonical region `regionOf P` of the original parallelepiped itself; the earlier existential unrelated `whole` region has been removed.  Its five face congruences are derived explicitly from XI.24, I.8/SSS-style face congruence, and reflexivity.

XI.29 derives all five corresponding faces of the two remainder prisms explicitly.  Segment subtraction is isolated as the generic `equalRemainders_of_nestedSegments`; opposite side/face equalities come from XI.24; the top-strip quadrilateral is proved from edge equalities and generic parallel-angle transport.  The remaining primitive assumption is only region realization/decomposition, because `SolidRegionGeometry` is intentionally abstract and has no set-theoretic membership/intersection structure from which partitions can be derived.

XI.30 compiles after correcting the non-alignment hypothesis to Lean's propositional `Not`.  It constructs an intermediate aligned parallelepiped and applies XI.29 twice.

## Region semantics upgrade for XI.28--XI.30

The solid-region layer now has genuine set-style semantics through `SolidRegionSetGeometry`: point membership, intersection, difference, extensionality, and the generic partition law `intersection + difference = original`. XI.29 no longer depends on a proposition-specific decomposition axiom: its common region is literally the intersection of the two parallelepiped regions, and its two remainders are the two set differences. The only remaining XI.29-specific geometric input is `AlignedRemainderRecognitionAxioms`, which identifies those two set differences with the canonical triangular-prism boundaries; all partition and volume algebra is generic.

XI.28 now uses `SolidRegionPlaneCutGeometry`, a generic operation cutting any region by a plane into two half-regions with a generic partition law. `DiagonalParallelepipedCutRecognitionAxioms` contains only the residual geometry: existence of the diagonal plane through A,C,E,G and recognition of the two half-space cuts as the canonical diagonal prism boundaries. The five boundary-face congruences and the equality of volumes are proved separately in Proposition28.

XI.30 has been migrated to the strengthened XI.29 interface and compiles. Full project build after this upgrade: 425 targets. Book XI contains no `sorry` or `admit`.

## Half-space and region-semantics reduction after XI.30

- Added `PlaneHalfSpaceGeometry` with oriented closed sides, reference-side membership, on-plane inclusion in both closed sides, classification, and off-plane disjointness.
- `SolidRegionPlaneCutGeometry` is now oriented by an explicit reference point; `SolidRegionPlaneCutMembershipAxioms` gives pointwise membership semantics for both cut halves.
- XI.28 no longer depends on a proposition-shaped diagonal-cut recognition class.  The remaining geometry is split into the reusable `ParallelepipedDiagonalPlaneAxioms` (A,C,E,G coplanar and B,D on opposite sides) and `ParallelepipedDiagonalPrismAxioms` (generic boundary realization of the two oriented diagonal cuts).  The latter now consumes the opposite-side fact and the generic cut-membership semantics.
- XI.29 no longer uses `AlignedRemainderRecognitionAxioms`.  Its two set differences are interpreted by the reusable `ShearedParallelepipedDifferencePrismAxioms`; all intersection/difference partitions remain generic consequences of `SolidRegionSetGeometry`.
- XI.30 has been propagated through these stronger XI.29 interfaces and still compiles.
- Remaining region gap: derive `ParallelepipedDiagonalPrismAxioms` and `ShearedParallelepipedDifferencePrismAxioms` from a fully explicit convex-polyhedron/half-space model of parallelepipeds and triangular prisms rather than assuming boundary realization.

## XI.23 circumradius-bound reduction

- Verified Joyce's XI.23 proof structure: equality of proposed edge and circumradius is excluded first; then the case proposed edge < circumradius is excluded using the inner similar triangle and I.25; strict circumradius < edge follows only afterward.
- Strengthened `SpatialSegmentOrderMagnitude` so its addition and strict order are explicitly identified with the underlying Book V magnitude operations. This exposes Book V trichotomy in the spatial segment layer.
- Replaced monolithic `CircumradiusBoundAxioms.radius_lt_edge` with `CircumradiusExclusionAxioms`, containing exactly two residual lemmas: `radius_ne_edge` and `not_edge_lt_radius`.
- Added theorem `circumradius_lt_edge`, which derives the strict bound from Book V magnitude trichotomy plus the two exclusion lemmas. XI.23 now invokes this theorem, so the final radius bound is no longer axiomatic.
- Remaining XI.23 gap: derive the two exclusion lemmas themselves from equal-radius angle recovery / central-angle sum for the equality case, and the VI.2 + V.16 + I.25 comparison construction for the `edge < radius` case, with the latter split across inside/boundary/outside circumcenter positions as Joyce notes.

## XI.23 gap reduction after region-semantics work

- The old one-shot `CircumradiusBoundAxioms.radius_lt_edge` has been eliminated.
- `SpatialSegmentOrderMagnitude` is now explicitly tied to the Book V magnitude order, so trichotomy is available theorem-level.
- Equality of circumradius and proposed common edge is no longer axiomatic.  It is derived from generic spatial chord-central-angle recovery, the full-turn law for three central angles, and the XI.21 strict four-right-angle bound.
- The case `edge < circumradius` is no longer a XI.23-shaped exclusion axiom.  It is derived from one reusable `FixedChordRadiusAngleMonotonicityAxioms` lemma: at fixed chord, increasing the equal radius strictly decreases the central angle.  The three angle inequalities are summed and contradicted against the full-turn equality and XI.21 bound.
- The remaining comparison gap is therefore precisely the plane-restriction proof of fixed-chord radius monotonicity, corresponding to Euclid's VI.2 + VI.4/V.16 + I.25 subargument.
- The old one-shot `CircumcenterApexLiftAxioms` has also been eliminated.  XI.23 now separates one normal-height/Pythagorean construction (`NormalHeightPointConstructionAxioms`), equal-radius hypotenuse transfer (`NormalEqualRadiusTransferAxioms`), and pure off-plane ray construction (`OffPlaneApexRayAxioms`).  Equal apex distances to the other two base vertices are proved by two transfer applications.

## XI.23 plane-comparison reduction

- Removed the former `FixedChordRadiusAngleMonotonicityAxioms` conclusion-level oracle.
- The `edge < circumradius` contradiction now follows Euclid XI.23 in explicit stages: construct inner points on the two radii, use a parallel inner chord, compare the two homothetic triangles, apply an I.25 hinge comparison, and transport the angle back along the same rays.
- Replaced the former strict `ParallelTriangleBaseComparisonAxioms` with `ParallelTriangleRatioAxioms`, which supplies only the VI.4-style proportion.  The strict inner-base comparison is now proved by Book V.14 from the strict radius comparison.
- `SpatialSegmentMagnitude` now exposes the Eudoxus separation instance needed by Book V.14; common edge and chord magnitudes expose positivity.
- Remaining XI.23 planar reduction boundary: `InnerParallelChordConstructionAxioms` (I.3 + parallel construction), `ParallelTriangleRatioAxioms` (VI.4 plane restriction), `CentralAngleRayInvarianceAxioms` (ray semantics), and `SpatialHingeComparisonAxioms` (specialized I.25 plane restriction).  The next target is to replace the last class by an actual restricted-plane invocation of Book I.25.

## XI.23 actual Book-I hinge invocation

- The strict inner-base comparison is no longer a primitive spatial axiom. `ParallelTriangleRatioAxioms` supplies only the VI.4-style ratio, and `parallelTriangle_innerBaseLt` derives the strict base inequality via the already formalized Book V.14.
- Added positivity to spatial segment/chord/common-edge magnitude interfaces and the Eudoxus separation instance needed by V.14.
- Removed the conclusion-level `SpatialHingeComparisonAxioms`. A new `Book1HingeModel` packages an honest 2D `Geometry` together with the ordinary Book-I background instances required by I.25.
- `PlaneHingeWitnessAxioms` now supplies only the restricted-plane triangles, side congruences, base inequality, and the bridge back to the spatial angle magnitude. `spatialHingeComparison_from_Book1` installs those instances and literally invokes `Euclid.Book1.proposition25` to obtain the angle inequality.
- Consequently, `fixedChordRadiusAngleMonotonicity` is now derived from: inner parallel-chord construction, VI.4 ratio, Book V.14, actual Book I.25, and ray invariance.
- Remaining reduction work is geometric realization of the restricted-plane witness itself and further reduction of the normal-height/Pythagorean construction; the XI.23 comparison conclusion is no longer proposition-shaped or hinge-shaped in the axiom layer.
