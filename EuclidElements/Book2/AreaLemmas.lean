import EuclidElements.Book2.Proposition04

namespace Euclid.Book2

open Euclid

variable (G : Geometry) [AreaGeometry G] [A : AreaAxioms G]

theorem addCongrLeft {x y : Area G} (h : x = y) (z : Area G) :
    Add G x z = Add G y z := congrArg (fun t => Add G t z) h

theorem addCongrRight (x : Area G) {y z : Area G} (h : y = z) :
    Add G x y = Add G x z := congrArg (fun t => Add G x t) h

theorem addThreePerm (x y z : Area G) :
    Add G (Add G x y) z = Add G (Add G z y) x := by
  calc
    Add G (Add G x y) z = Add G x (Add G y z) := A.addAssoc x y z
    _ = Add G x (Add G z y) := addCongrRight G x (A.addComm y z)
    _ = Add G (Add G z y) x := by rw [A.addComm x (Add G z y)]

theorem addSwapMiddle (x y z : Area G) :
    Add G (Add G x y) z = Add G (Add G x z) y := by
  calc
    Add G (Add G x y) z = Add G x (Add G y z) := A.addAssoc x y z
    _ = Add G x (Add G z y) := addCongrRight G x (A.addComm y z)
    _ = Add G (Add G x z) y := (A.addAssoc x z y).symm

theorem addFourPerm (a b c d : Area G) :
    Add G (Add G a b) (Add G c d) =
      Add G (Add G a c) (Add G b d) := by
  calc
    Add G (Add G a b) (Add G c d)
        = Add G a (Add G b (Add G c d)) := A.addAssoc a b (Add G c d)
    _ = Add G a (Add G (Add G b c) d) := by rw [← A.addAssoc b c d]
    _ = Add G a (Add G (Add G c b) d) := by rw [A.addComm b c]
    _ = Add G a (Add G c (Add G b d)) := by rw [A.addAssoc c b d]
    _ = Add G (Add G a c) (Add G b d) := (A.addAssoc a c (Add G b d)).symm

theorem addFourNestedRotate (a b c d : Area G) :
    Add G (Add G (Add G a b) c) d =
      Add G (Add G d a) (Add G b c) := by
  calc
    Add G (Add G (Add G a b) c) d
        = Add G (Add G a b) (Add G c d) := A.addAssoc (Add G a b) c d
    _ = Add G (Add G c d) (Add G a b) := A.addComm _ _
    _ = Add G (Add G d c) (Add G a b) := by rw [A.addComm c d]
    _ = Add G (Add G d a) (Add G c b) := addFourPerm G d c a b
    _ = Add G (Add G d a) (Add G b c) := by rw [A.addComm c b]

theorem pairPairNormalize (x y : Area G) :
    Add G (Add G x y) (Add G x y) =
      Add G x (Add G x (Add G y y)) := by
  calc
    Add G (Add G x y) (Add G x y)
        = Add G x (Add G y (Add G x y)) := A.addAssoc x y (Add G x y)
    _ = Add G x (Add G (Add G y x) y) := by rw [← A.addAssoc y x y]
    _ = Add G x (Add G (Add G x y) y) := by rw [A.addComm y x]
    _ = Add G x (Add G x (Add G y y)) := by rw [A.addAssoc x y y]

theorem addPattern7 (s x y : Area G) :
    Add G (Add G (Add G s x) (Add G x y)) y =
      Add G (Add G (Add G x y) (Add G x y)) s := by
  calc
    Add G (Add G (Add G s x) (Add G x y)) y
        = Add G (Add G s x) (Add G (Add G x y) y) :=
            A.addAssoc (Add G s x) (Add G x y) y
    _ = Add G s (Add G x (Add G (Add G x y) y)) :=
          A.addAssoc s x (Add G (Add G x y) y)
    _ = Add G s (Add G x (Add G x (Add G y y))) := by
          rw [A.addAssoc x y y, ← A.addAssoc x x (Add G y y)]
    _ = Add G (Add G x (Add G x (Add G y y))) s := A.addComm _ _
    _ = Add G (Add G (Add G x y) (Add G x y)) s := by
          rw [pairPairNormalize G x y]

theorem addPattern12 (da r ac db : Area G) :
    Add G (Add G (Add G da r) (Add G r ac)) db =
      Add G (Add G da db) (Add G ac (Add G r r)) := by
  calc
    Add G (Add G (Add G da r) (Add G r ac)) db
        = Add G (Add G (Add G da r) (Add G ac r)) db := by
            rw [A.addComm r ac]
    _ = Add G (Add G (Add G da ac) (Add G r r)) db := by
            rw [addFourPerm G da r ac r]
    _ = Add G (Add G db da) (Add G ac (Add G r r)) :=
            addFourNestedRotate G da ac (Add G r r) db
    _ = Add G (Add G da db) (Add G ac (Add G r r)) := by
            rw [A.addComm db da]

end Euclid.Book2
