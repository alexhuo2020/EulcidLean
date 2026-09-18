import EuclidElements.Book1.Proposition27
import EuclidElements.Book1.OrientedAngleCopyAxioms
import EuclidElements.Foundations.Incidence

/-!
# Euclid I.31 -- through a given point draw a line parallel to a given line

This proof now performs Euclid's construction explicitly: choose two points on
the given line, join one to the external point, copy the alternate angle on the
opposite side, draw its new arm, and apply I.27.
-/

namespace Euclid.Book1

open Euclid
open Euclid.Foundations

theorem proposition31
    (G : Geometry)
    [P : Postulates G]
    [IA : IncidenceAxioms G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AI : AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    [S : PlaneSeparationAxioms G]
    [OC : OrientedAngleCopyAxioms G]
    {l : G.Line} {A : G.Point}
    (hA : ¬ G.onLine A l) :
    ∃ m : G.Line, G.onLine A m ∧ Parallel G l m := by
  obtain ⟨D, C, hDC, hDl, hCl⟩ := IA.lineHasTwoPoints l
  have hAD : A ≠ D := by
    intro h
    subst A
    exact hA hDl
  obtain ⟨t, hAt, hDt⟩ := P.postulate1 A D hAD

  have hCnotT : ¬ G.onLine C t := by
    intro hCt
    have htl : t = l := IA.lineUnique hDC hDt hCt hDl hCl
    exact hA (by simpa [htl] using hAt)

  have hvalid : ValidAngle G ⟨A, D, C⟩ := by
    refine ⟨hAD, Ne.symm hDC, ?_⟩
    intro hcol
    rcases hcol with ⟨u, hAu, hDu, hCu⟩
    have hul : u = l := IA.lineUnique hDC hDu hCu hDl hCl
    exact hA (by simpa [hul] using hAu)

  obtain ⟨F, hFA, hFnotT, hopposite, hcopy⟩ :=
    OC.copyOppositeSide hAD hAt hDt hCnotT hvalid
  obtain ⟨m, hAm, hFm⟩ := P.postulate1 A F (Ne.symm hFA)

  have hml : m ≠ l := by
    intro h
    exact hA (by simpa [h] using hAm)

  let s : TransversalSetup G := {
    l := m
    m := l
    t := t
    p := A
    q := D
    a := F
    b := C
    hpq := hAD
    hpl := hAm
    hpt := hAt
    hqm := hDl
    hqt := hDt
    hal := hFm
    hbm := hCl
    hap := hFA
    hbq := Ne.symm hDC
    hat := hFnotT
    hbt := hCnotT
  }

  have hparML : Parallel G m l := proposition27 G s hml hopposite hcopy
  have hparLM : Parallel G l m := by
    refine ⟨Ne.symm hparML.1, ?_⟩
    intro hmeet
    rcases hmeet with ⟨X, hXl, hXm⟩
    exact hparML.2 ⟨X, hXm, hXl⟩
  exact ⟨m, hAm, hparLM⟩

end Euclid.Book1
