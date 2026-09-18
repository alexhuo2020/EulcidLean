import EuclidElements.Book3.TangentChordAngleFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.32: the angles made by a tangent and a chord equal the angles
    in the alternate circular segments. -/
theorem proposition32
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [AngleSumGeometry G]
    [AngleAdditionGeometry G]
    [AngleArcGeometry G]
    [AI : AngleImplicitAxioms G]
    [AA : AngleAdditionImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    [P32 : Proposition32ImplicitAxioms G]
    [C0 : CircleBasicAxioms G]
    [CA : InscribedAngleCaseAxioms G]
    [ALG : AngleSumAlgebraFoundations G]
    [SA : SemicircleAngleArithmeticFoundations G]
    [TR : TwoRightAngleAlgebraFoundations G]
    [CQ : CyclicQuadrilateralFoundations G]
    [TC : TangentChordAngleAlgebraFoundations G]
    [TD : TangentChordDiagramAxioms G]
    {c : G.Circle} {O B D : G.Point} {tangent : G.Line}
    (hO : G.isCenter c O)
    (htan : TangentAt G c tangent B)
    (hD : G.onCircle D c)
    (hBD : B ≠ D) :
    exists A C E F : G.Point,
      G.onCircle A c ∧ G.onCircle C c ∧
      G.onLine E tangent ∧ G.onLine F tangent ∧
      G.angleCongruent ⟨F, B, D⟩ ⟨B, A, D⟩ ∧
      G.angleCongruent ⟨E, B, D⟩ ⟨D, C, B⟩ := by
  obtain ⟨A, C, E, F, semi,
    hA, hC, hdiam, hArc, hStand, hADBtri,
    hEt, hFt, hEBF, hrightABF, hInside,
    hnoncol, hquad⟩ := TD.diagram hO htan hD hBD

  have hB : G.onCircle B c := htan.1
  have hrightADB : RightAngle G ⟨A, D, B⟩ :=
    proposition31_semicircle G hdiam hO hArc hStand hD hA hB hADBtri

  obtain ⟨X, hDBX⟩ := P.postulate2 D B (Ne.symm hBD)
  have hsum : ThreeAnglesTwoRight G
      ⟨D, A, B⟩ ⟨A, D, B⟩ ⟨D, B, A⟩ :=
    (Euclid.Book1.proposition32 G hADBtri hDBX).2

  have hsplit0 : AngleSumEq G ⟨A, B, D⟩ ⟨D, B, F⟩ ⟨A, B, F⟩ :=
    AA.splitInside hInside
  have hDBA_ABD : G.angleCongruent ⟨D, B, A⟩ ⟨A, B, D⟩ :=
    L.angleReverse D B A
  have hsplit : AngleSumEq G ⟨D, B, A⟩ ⟨D, B, F⟩ ⟨A, B, F⟩ :=
    AA.sumCongr hDBA_ABD (I.angleRefl ⟨D, B, F⟩) hsplit0
  have hDBF_DAB : G.angleCongruent ⟨D, B, F⟩ ⟨D, A, B⟩ :=
    TC.complementOfRight hsum hrightADB hrightABF hsplit
  have hFBD_DBF : G.angleCongruent ⟨F, B, D⟩ ⟨D, B, F⟩ :=
    L.angleReverse F B D
  have hDAB_BAD : G.angleCongruent ⟨D, A, B⟩ ⟨B, A, D⟩ :=
    L.angleReverse D A B
  have hDBF_BAD : G.angleCongruent ⟨D, B, F⟩ ⟨B, A, D⟩ :=
    I.angleTrans hDBF_DAB hDAB_BAD
  have hFBD_BAD : G.angleCongruent ⟨F, B, D⟩ ⟨B, A, D⟩ :=
    I.angleTrans hFBD_DBF hDBF_BAD

  have hsuppTan0 : Supplementary G ⟨E, B, D⟩ ⟨D, B, F⟩ :=
    AI.linearPairSupplementary hEBF hnoncol
  have hsuppTan : Supplementary G ⟨D, B, F⟩ ⟨E, B, D⟩ :=
    AI.supplementarySymm hsuppTan0

  have hsuppC : Supplementary G ⟨B, A, D⟩ ⟨B, C, D⟩ :=
    proposition22 G hB hA hD hC hquad
  have hsuppBAD_EBD : Supplementary G ⟨B, A, D⟩ ⟨E, B, D⟩ :=
    AI.supplementaryCongrLeft hDBF_BAD hsuppTan
  have hEBD_BCD : G.angleCongruent ⟨E, B, D⟩ ⟨B, C, D⟩ :=
    AI.equalSupplements hsuppBAD_EBD hsuppC
  have hBCD_DCB : G.angleCongruent ⟨B, C, D⟩ ⟨D, C, B⟩ :=
    L.angleReverse B C D
  have hEBD_DCB : G.angleCongruent ⟨E, B, D⟩ ⟨D, C, B⟩ :=
    I.angleTrans hEBD_BCD hBCD_DCB

  exact ⟨A, C, E, F, hA, hC, hEt, hFt, hFBD_BAD, hEBD_DCB⟩

end Euclid.Book3
