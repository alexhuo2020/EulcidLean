import EuclidElements.Book1

/-!
# Euclid Book II: synthetic geometric algebra

A rectangle is still "contained by" two segments and a square is described on
one segment. Their areas inhabit an abstract additive magnitude type; no real
number multiplication or coordinate length is used.
-/

namespace Euclid.Book2

open Euclid
open Euclid.Book1

class AreaGeometry (G : Geometry) where
  Area : Type
  zero : Area
  add : Area → Area → Area
  rect : G.Point → G.Point → G.Point → G.Point → Area
  square : G.Point → G.Point → Area
  quad : G.Point → G.Point → G.Point → G.Point → Area
  polygon : Polygon G.Point → Area

abbrev Area (G : Geometry) [A : AreaGeometry G] := A.Area

def Zero (G : Geometry) [A : AreaGeometry G] : Area G := A.zero

def Add (G : Geometry) [A : AreaGeometry G] (x y : Area G) : Area G := A.add x y

def Rect (G : Geometry) [A : AreaGeometry G]
    (P Q R S : G.Point) : Area G := A.rect P Q R S

def Sq (G : Geometry) [A : AreaGeometry G] (P Q : G.Point) : Area G := A.square P Q

def QuadArea (G : Geometry) [A : AreaGeometry G]
    (P Q R S : G.Point) : Area G := A.quad P Q R S

def PolygonArea (G : Geometry) [A : AreaGeometry G]
    (p : Polygon G.Point) : Area G := A.polygon p

/-- A finite decomposition of segment `AB` into consecutive subsegments. -/
inductive SegmentChain (G : Geometry) :
    G.Point → G.Point → List (G.Point × G.Point) → Prop
  | single (A B : G.Point) : SegmentChain G A B [(A, B)]
  | split {A C B : G.Point} {rest : List (G.Point × G.Point)} :
      G.between A C B →
      SegmentChain G C B rest →
      SegmentChain G A B ((A, C) :: rest)

def RectanglesOnChain
    (G : Geometry) [A : AreaGeometry G]
    (P Q : G.Point) (parts : List (G.Point × G.Point)) : List (Area G) :=
  parts.map (fun s => Rect G P Q s.1 s.2)

def AreaSum (G : Geometry) [A : AreaGeometry G] : List (Area G) → Area G
  | [] => Zero G
  | x :: xs => Add G x (AreaSum G xs)

end Euclid.Book2
