import EuclidElements.Book3.ChordMetricFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1
open Euclid.Book2

/-- Euclid III.14: equal chords are equally distant from the center, and
    chords equally distant from the center are equal. -/
theorem proposition14
    (G : Geometry)
    [I : ImplicitAxioms G]
    [AreaGeometry G]
    [AA : AreaAxioms G]
    [PY : PythagoreanMagnitudeGeometry G]
    [CM : ChordMetricFoundations G]
    {c : G.Circle} {O A B C D M N : G.Point}
    (hAB : ChordFoot G c O A B M)
    (hCD : ChordFoot G c O C D N) :
    (G.segmentCongruent A B C D -> G.segmentCongruent O M O N) ∧
    (G.segmentCongruent O M O N -> G.segmentCongruent A B C D) := by
  obtain ⟨hMmid, hMOA, hMright⟩ := CM.footGeometry hAB
  obtain ⟨hNmid, hNOC, hNright⟩ := CM.footGeometry hCD
  have hAon : G.onCircle A c := hAB.2.1.2.1
  have hCon : G.onCircle C c := hCD.2.1.2.1
  have hrad : G.segmentCongruent O A O C :=
    CM.sameCircleRadii hAB.1 hAon hCon
  have hsrad : Sq G O A = Sq G O C := CM.squareEqOfCongruent hrad

  have hpyM : Add G (Sq G M O) (Sq G M A) = Sq G O A :=
    PY.pythagorean hMOA hMright
  have hpyN : Add G (Sq G N O) (Sq G N C) = Sq G O C :=
    PY.pythagorean hNOC hNright

  constructor
  · intro hchord
    have hhalf : G.segmentCongruent M A N C :=
      CM.equalWholesGiveEqualHalves hMmid hNmid hchord
    have hshalf : Sq G M A = Sq G N C := CM.squareEqOfCongruent hhalf
    have hsum : Add G (Sq G M A) (Sq G M O) =
        Add G (Sq G M A) (Sq G N O) := by
      calc
        Add G (Sq G M A) (Sq G M O)
            = Add G (Sq G M O) (Sq G M A) := AA.addComm _ _
        _ = Sq G O A := hpyM
        _ = Sq G O C := hsrad
        _ = Add G (Sq G N O) (Sq G N C) := hpyN.symm
        _ = Add G (Sq G N C) (Sq G N O) := AA.addComm _ _
        _ = Add G (Sq G M A) (Sq G N O) := by rw [hshalf]
    have hsfoot : Sq G M O = Sq G N O :=
      AA.addCancelLeft (Sq G M A) (Sq G M O) (Sq G N O) hsum
    have hfoot : G.segmentCongruent M O N O := CM.congruentOfSquareEq hsfoot
    exact I.segmentTrans (I.segmentReverse O M)
      (I.segmentTrans hfoot (I.segmentReverse N O))

  · intro hdist
    have hdist' : G.segmentCongruent M O N O :=
      I.segmentTrans (I.segmentReverse M O)
        (I.segmentTrans hdist (I.segmentReverse O N))
    have hsdist : Sq G M O = Sq G N O := CM.squareEqOfCongruent hdist'
    have hsum : Add G (Sq G M O) (Sq G M A) =
        Add G (Sq G M O) (Sq G N C) := by
      calc
        Add G (Sq G M O) (Sq G M A) = Sq G O A := hpyM
        _ = Sq G O C := hsrad
        _ = Add G (Sq G N O) (Sq G N C) := hpyN.symm
        _ = Add G (Sq G M O) (Sq G N C) := by rw [hsdist]
    have hshalf : Sq G M A = Sq G N C :=
      AA.addCancelLeft (Sq G M O) (Sq G M A) (Sq G N C) hsum
    have hhalf : G.segmentCongruent M A N C := CM.congruentOfSquareEq hshalf
    exact CM.equalHalvesGiveEqualWholes hMmid hNmid hhalf

end Euclid.Book3
