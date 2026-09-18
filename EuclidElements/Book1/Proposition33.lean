import EuclidElements.Book1.Proposition04
import EuclidElements.Book1.Proposition27
import EuclidElements.Book1.Proposition33ImplicitAxioms

/-!
# Euclid I.33 -- joins of equal parallel segments are equal and parallel
-/

namespace Euclid.Book1

open Euclid

theorem proposition33
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [AI : AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    [S : PlaneSeparationAxioms G]
    [D33 : Proposition33ImplicitAxioms G]
    {A B C D : G.Point} {lAB lCD lAC lBD : G.Line}
    (hAAB : G.onLine A lAB) (hBAB : G.onLine B lAB)
    (hCCD : G.onLine C lCD) (hDCD : G.onLine D lCD)
    (hpar : Parallel G lAB lCD)
    (hAAC : G.onLine A lAC) (hCAC : G.onLine C lAC)
    (hBBD : G.onLine B lBD) (hDBD : G.onLine D lBD)
    (hAB_CD : G.segmentCongruent A B C D) :
    G.segmentCongruent A C B D ∧ Parallel G lAC lBD := by
  obtain ⟨s, hABC, hDCB, hABC_DCB, hsl, hsm, hlne,
    hopp, hconvert⟩ :=
    D33.diagram hAAB hBAB hCCD hDCD hpar hAAC hCAC hBBD hDBD

  have hBAC : IsTriangle G B A C := L.triangleSwap23 (L.triangleCycle hABC)
  have hCDB : IsTriangle G C D B := L.triangleSwap23 (L.triangleCycle hDCB)
  have hBA_CD : G.segmentCongruent B A C D :=
    I.segmentTrans (I.segmentReverse B A) hAB_CD
  have hBC_CB : G.segmentCongruent B C C B := I.segmentReverse B C
  have hsas := proposition4 G hBAC hCDB hBA_CD hBC_CB hABC_DCB

  have hAC_DB : G.segmentCongruent A C D B := hsas.1
  have hAC_BD : G.segmentCongruent A C B D :=
    I.segmentTrans hAC_DB (I.segmentReverse D B)

  have hBCA_CBD : G.angleCongruent ⟨B, C, A⟩ ⟨C, B, D⟩ := hsas.2.2.1
  have hACB_BCA : G.angleCongruent ⟨A, C, B⟩ ⟨B, C, A⟩ :=
    L.angleReverse A C B
  have hACB_CBD : G.angleCongruent ⟨A, C, B⟩ ⟨C, B, D⟩ :=
    I.angleTrans hACB_BCA hBCA_CBD
  have halt : G.angleCongruent s.angleAtP s.angleAtQ := hconvert hACB_CBD
  have hslm : s.l ≠ s.m := by
    intro h
    apply hlne
    calc
      lAC = s.l := hsl.symm
      _ = s.m := h
      _ = lBD := hsm
  have hp : Parallel G s.l s.m := proposition27 G s hslm hopp halt
  rw [hsl, hsm] at hp
  exact ⟨hAC_BD, hp⟩

end Euclid.Book1
