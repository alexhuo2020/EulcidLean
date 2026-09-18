import EuclidElements.Book3.CircleAngleFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.20: the angle at the center is double the angle at the
    circumference standing on the same chord/arc.  `AngleSumEq α α β` is the
    synthetic meaning of “β is double α”. -/
theorem proposition20
    (G : Geometry)
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleInteriorGeometry G]
    [AngleSumGeometry G]
    [AngleAdditionGeometry G]
    [AngleArcGeometry G]
    [AI : AngleImplicitAxioms G]
    [AA : AngleAdditionImplicitAxioms G]
    [P32 : Proposition32ImplicitAxioms G]
    [C : CircleBasicAxioms G]
    [CA : InscribedAngleCaseAxioms G]
    [ALG : AngleSumAlgebraFoundations G]
    {s : ArcRef G} {c : G.Circle} {O P B Cpt : G.Point}
    (hArc : ArcOn G s c B Cpt)
    (hStand : StandsOnArc G ⟨B, P, Cpt⟩ s)
    (hcenter : G.isCenter c O)
    (hP : G.onCircle P c)
    (hB : G.onCircle B c)
    (hC : G.onCircle Cpt c)
    (htri : IsTriangle G B P Cpt) :
    AngleSumEq G ⟨B, P, Cpt⟩ ⟨B, P, Cpt⟩ ⟨B, O, Cpt⟩ := by
  have hOP_OB : G.segmentCongruent O P O B := C.radiiCongruent hcenter hP hB
  have hOP_OC : G.segmentCongruent O P O Cpt := C.radiiCongruent hcenter hP hC

  rcases CA.cases hArc hStand hcenter hP hB hC htri with hinside | houtside
  · obtain ⟨D, hPOD, hBPO, hCPO, hPin, hOin⟩ := hinside

    have hOBP : IsTriangle G O B P := L.triangleCycle (L.triangleCycle hBPO)
    have hOPB : IsTriangle G O P B := L.triangleSwap23 hOBP
    have hbaseB0 : G.angleCongruent ⟨O, P, B⟩ ⟨P, B, O⟩ :=
      proposition5_baseAngles G hOPB hOP_OB
    have hrevB : G.angleCongruent ⟨O, P, B⟩ ⟨B, P, O⟩ := L.angleReverse O P B
    have hPBO_BPO : G.angleCongruent ⟨P, B, O⟩ ⟨B, P, O⟩ :=
      I.angleTrans (I.angleSymm hbaseB0) hrevB
    have hextB := (proposition32 G hBPO hPOD).1
    have hdoubleB : AngleSumEq G ⟨B, P, O⟩ ⟨B, P, O⟩ ⟨B, O, D⟩ :=
      AA.sumCongr (I.angleSymm hPBO_BPO) (I.angleRefl ⟨B, P, O⟩) hextB

    have hOCP : IsTriangle G O Cpt P := L.triangleCycle (L.triangleCycle hCPO)
    have hOPC : IsTriangle G O P Cpt := L.triangleSwap23 hOCP
    have hbaseC0 : G.angleCongruent ⟨O, P, Cpt⟩ ⟨P, Cpt, O⟩ :=
      proposition5_baseAngles G hOPC hOP_OC
    have hrevC : G.angleCongruent ⟨O, P, Cpt⟩ ⟨Cpt, P, O⟩ :=
      L.angleReverse O P Cpt
    have hPCO_CPO : G.angleCongruent ⟨P, Cpt, O⟩ ⟨Cpt, P, O⟩ :=
      I.angleTrans (I.angleSymm hbaseC0) hrevC
    have hextC := (proposition32 G hCPO hPOD).1
    have hdoubleC0 : AngleSumEq G ⟨Cpt, P, O⟩ ⟨Cpt, P, O⟩ ⟨Cpt, O, D⟩ :=
      AA.sumCongr (I.angleSymm hPCO_CPO) (I.angleRefl ⟨Cpt, P, O⟩) hextC
    have hCPO_OPC : G.angleCongruent ⟨Cpt, P, O⟩ ⟨O, P, Cpt⟩ :=
      L.angleReverse Cpt P O
    have hCOD_DOC : G.angleCongruent ⟨Cpt, O, D⟩ ⟨D, O, Cpt⟩ :=
      L.angleReverse Cpt O D
    have hdoubleC1 : AngleSumEq G ⟨O, P, Cpt⟩ ⟨O, P, Cpt⟩ ⟨Cpt, O, D⟩ :=
      AA.sumCongr (I.angleSymm hCPO_OPC) (I.angleSymm hCPO_OPC) hdoubleC0
    have hdoubleC : AngleSumEq G ⟨O, P, Cpt⟩ ⟨O, P, Cpt⟩ ⟨D, O, Cpt⟩ :=
      ALG.resultCongr hdoubleC1 hCOD_DOC

    have hinscribed : AngleSumEq G ⟨B, P, O⟩ ⟨O, P, Cpt⟩ ⟨B, P, Cpt⟩ :=
      AA.splitInside hPin
    have hcentral : AngleSumEq G ⟨B, O, D⟩ ⟨D, O, Cpt⟩ ⟨B, O, Cpt⟩ :=
      AA.splitInside hOin
    exact ALG.doubleAdd hdoubleB hdoubleC hinscribed hcentral

  · obtain ⟨D, hPOD, hBPO, hCPO, hPin, hOin⟩ := houtside

    have hOBP : IsTriangle G O B P := L.triangleCycle (L.triangleCycle hBPO)
    have hOPB : IsTriangle G O P B := L.triangleSwap23 hOBP
    have hbaseB0 : G.angleCongruent ⟨O, P, B⟩ ⟨P, B, O⟩ :=
      proposition5_baseAngles G hOPB hOP_OB
    have hrevB : G.angleCongruent ⟨O, P, B⟩ ⟨B, P, O⟩ := L.angleReverse O P B
    have hPBO_BPO : G.angleCongruent ⟨P, B, O⟩ ⟨B, P, O⟩ :=
      I.angleTrans (I.angleSymm hbaseB0) hrevB
    have hextB := (proposition32 G hBPO hPOD).1
    have hdoubleB0 : AngleSumEq G ⟨B, P, O⟩ ⟨B, P, O⟩ ⟨B, O, D⟩ :=
      AA.sumCongr (I.angleSymm hPBO_BPO) (I.angleRefl ⟨B, P, O⟩) hextB
    have hBPO_OPB : G.angleCongruent ⟨B, P, O⟩ ⟨O, P, B⟩ :=
      L.angleReverse B P O
    have hBOD_DOB : G.angleCongruent ⟨B, O, D⟩ ⟨D, O, B⟩ :=
      L.angleReverse B O D
    have hdoubleB1 : AngleSumEq G ⟨O, P, B⟩ ⟨O, P, B⟩ ⟨B, O, D⟩ :=
      AA.sumCongr (I.angleSymm hBPO_OPB) (I.angleSymm hBPO_OPB) hdoubleB0
    have hdoubleB : AngleSumEq G ⟨O, P, B⟩ ⟨O, P, B⟩ ⟨D, O, B⟩ :=
      ALG.resultCongr hdoubleB1 hBOD_DOB

    have hOCP : IsTriangle G O Cpt P := L.triangleCycle (L.triangleCycle hCPO)
    have hOPC : IsTriangle G O P Cpt := L.triangleSwap23 hOCP
    have hbaseC0 : G.angleCongruent ⟨O, P, Cpt⟩ ⟨P, Cpt, O⟩ :=
      proposition5_baseAngles G hOPC hOP_OC
    have hrevC : G.angleCongruent ⟨O, P, Cpt⟩ ⟨Cpt, P, O⟩ :=
      L.angleReverse O P Cpt
    have hPCO_CPO : G.angleCongruent ⟨P, Cpt, O⟩ ⟨Cpt, P, O⟩ :=
      I.angleTrans (I.angleSymm hbaseC0) hrevC
    have hextC := (proposition32 G hCPO hPOD).1
    have hdoubleC0 : AngleSumEq G ⟨Cpt, P, O⟩ ⟨Cpt, P, O⟩ ⟨Cpt, O, D⟩ :=
      AA.sumCongr (I.angleSymm hPCO_CPO) (I.angleRefl ⟨Cpt, P, O⟩) hextC
    have hCPO_OPC : G.angleCongruent ⟨Cpt, P, O⟩ ⟨O, P, Cpt⟩ :=
      L.angleReverse Cpt P O
    have hCOD_DOC : G.angleCongruent ⟨Cpt, O, D⟩ ⟨D, O, Cpt⟩ :=
      L.angleReverse Cpt O D
    have hdoubleC1 : AngleSumEq G ⟨O, P, Cpt⟩ ⟨O, P, Cpt⟩ ⟨Cpt, O, D⟩ :=
      AA.sumCongr (I.angleSymm hCPO_OPC) (I.angleSymm hCPO_OPC) hdoubleC0
    have hdoubleC : AngleSumEq G ⟨O, P, Cpt⟩ ⟨O, P, Cpt⟩ ⟨D, O, Cpt⟩ :=
      ALG.resultCongr hdoubleC1 hCOD_DOC

    have hinscribed : AngleSumEq G ⟨O, P, B⟩ ⟨B, P, Cpt⟩ ⟨O, P, Cpt⟩ :=
      AA.splitInside hPin
    have hcentral : AngleSumEq G ⟨D, O, B⟩ ⟨B, O, Cpt⟩ ⟨D, O, Cpt⟩ :=
      AA.splitInside hOin
    exact ALG.doubleSubtract hdoubleC hdoubleB hinscribed hcentral

end Euclid.Book3
