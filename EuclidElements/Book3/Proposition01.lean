import EuclidElements.Book3.CircleFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.1, construction-strength form.  Because `Geometry.Circle` is a
    primitive sort, the actual straightedge/compass trace is carried by
    `CenterConstructionAxioms` rather than silently identifying circles with
    center-radius pairs. -/
theorem proposition1
    (G : Geometry)
    [CenterConstructionAxioms G]
    (c : G.Circle) :
    ∃ F : G.Point, G.isCenter c F := by
  obtain ⟨A, B, D, C, E, F, _hchord, _hmid,
    _hC, _hE, _hCFE, _hCF_FE, hcenter⟩ :=
    CenterConstructionAxioms.construct c
  exact ⟨F, hcenter⟩

/-- Euclid III.1 corollary in the form used later: the center exists as part
    of the semantic content of `Circle`. -/
theorem proposition1_center_exists
    (G : Geometry) [CircleBasicAxioms G] (c : G.Circle) :
    ∃ O : G.Point, G.isCenter c O :=
  CircleBasicAxioms.centerExists c

end Euclid.Book3
