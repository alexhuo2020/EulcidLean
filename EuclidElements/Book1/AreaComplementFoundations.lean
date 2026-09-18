import EuclidElements.Book1.AreaDiagramGeometry

namespace Euclid.Book1

open Euclid

/-- Common-Notion area cancellation for complement diagrams. -/
class AreaComplementFoundations
    (G : Geometry)
    [TriangleAreaGeometry G]
    [LaterAreaGeometry G]
    [AreaDiagramGeometry G] : Prop where
  equalComplements : ∀
    {A B C D E F H I : G.Point},
    ComplementsAboutDiagonal G A B C D E F H I →
    QuadAreaEq G A B C D E F H I

end Euclid.Book1
