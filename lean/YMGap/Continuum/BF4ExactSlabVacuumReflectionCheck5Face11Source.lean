import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5TailCanonical

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

/- The original source-to-canonical decision exceeded the mandatory 20-GiB
worker cap.  Check eight raw source blocks independently, assemble them, and
then check their literal canonical form. -/

private def face5source11 : RatPoly :=
  (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 5 11)).scalar

private def face5raw11_0 : RawPoly :=
  [([216, 1, 224, 1, 424, 1, 428, 1], 1),
   ([217, 1, 224, 1, 424, 1, 429, 1], -1),
   ([218, 1, 224, 1, 424, 1, 430, 1], -1),
   ([219, 1, 224, 1, 424, 1, 431, 1], -1),
   ([216, 1, 224, 1, 425, 1, 429, 1], 1),
   ([217, 1, 224, 1, 425, 1, 428, 1], 1),
   ([218, 1, 224, 1, 425, 1, 431, 1], 1),
   ([219, 1, 224, 1, 425, 1, 430, 1], -1)]

private theorem face5raw11_0_checked :
    fastCompactReflectRaw ((face5source11.drop 0).take 8) = face5raw11_0 := by
  decide

private def face5raw11_1 : RawPoly :=
  [([216, 1, 224, 1, 426, 1, 430, 1], 1),
   ([218, 1, 224, 1, 426, 1, 428, 1], 1),
   ([219, 1, 224, 1, 426, 1, 429, 1], 1),
   ([217, 1, 224, 1, 426, 1, 431, 1], -1),
   ([216, 1, 224, 1, 427, 1, 431, 1], 1),
   ([219, 1, 224, 1, 427, 1, 428, 1], 1),
   ([217, 1, 224, 1, 427, 1, 430, 1], 1),
   ([218, 1, 224, 1, 427, 1, 429, 1], -1)]

private theorem face5raw11_1_checked :
    fastCompactReflectRaw ((face5source11.drop 8).take 8) = face5raw11_1 := by
  decide

private def face5raw11_2 : RawPoly :=
  [([216, 1, 225, 1, 425, 1, 428, 1], -1),
   ([217, 1, 225, 1, 425, 1, 429, 1], 1),
   ([218, 1, 225, 1, 425, 1, 430, 1], 1),
   ([219, 1, 225, 1, 425, 1, 431, 1], 1),
   ([216, 1, 225, 1, 424, 1, 429, 1], 1),
   ([217, 1, 225, 1, 424, 1, 428, 1], 1),
   ([218, 1, 225, 1, 424, 1, 431, 1], 1),
   ([219, 1, 225, 1, 424, 1, 430, 1], -1)]

private theorem face5raw11_2_checked :
    fastCompactReflectRaw ((face5source11.drop 16).take 8) = face5raw11_2 := by
  decide

private def face5raw11_3 : RawPoly :=
  [([216, 1, 225, 1, 427, 1, 430, 1], -1),
   ([218, 1, 225, 1, 427, 1, 428, 1], -1),
   ([219, 1, 225, 1, 427, 1, 429, 1], -1),
   ([217, 1, 225, 1, 427, 1, 431, 1], 1),
   ([216, 1, 225, 1, 426, 1, 431, 1], 1),
   ([219, 1, 225, 1, 426, 1, 428, 1], 1),
   ([217, 1, 225, 1, 426, 1, 430, 1], 1),
   ([218, 1, 225, 1, 426, 1, 429, 1], -1)]

private theorem face5raw11_3_checked :
    fastCompactReflectRaw ((face5source11.drop 24).take 8) = face5raw11_3 := by
  decide

private def face5raw11_4 : RawPoly :=
  [([216, 1, 226, 1, 426, 1, 428, 1], -1),
   ([217, 1, 226, 1, 426, 1, 429, 1], 1),
   ([218, 1, 226, 1, 426, 1, 430, 1], 1),
   ([219, 1, 226, 1, 426, 1, 431, 1], 1),
   ([216, 1, 226, 1, 424, 1, 430, 1], 1),
   ([218, 1, 226, 1, 424, 1, 428, 1], 1),
   ([219, 1, 226, 1, 424, 1, 429, 1], 1),
   ([217, 1, 226, 1, 424, 1, 431, 1], -1)]

private theorem face5raw11_4_checked :
    fastCompactReflectRaw ((face5source11.drop 32).take 8) = face5raw11_4 := by
  decide

private def face5raw11_5 : RawPoly :=
  [([216, 1, 226, 1, 425, 1, 431, 1], -1),
   ([219, 1, 226, 1, 425, 1, 428, 1], -1),
   ([217, 1, 226, 1, 425, 1, 430, 1], -1),
   ([218, 1, 226, 1, 425, 1, 429, 1], 1),
   ([216, 1, 226, 1, 427, 1, 429, 1], 1),
   ([217, 1, 226, 1, 427, 1, 428, 1], 1),
   ([218, 1, 226, 1, 427, 1, 431, 1], 1),
   ([219, 1, 226, 1, 427, 1, 430, 1], -1)]

private theorem face5raw11_5_checked :
    fastCompactReflectRaw ((face5source11.drop 40).take 8) = face5raw11_5 := by
  decide

private def face5raw11_6 : RawPoly :=
  [([216, 1, 227, 1, 427, 1, 428, 1], -1),
   ([217, 1, 227, 1, 427, 1, 429, 1], 1),
   ([218, 1, 227, 1, 427, 1, 430, 1], 1),
   ([219, 1, 227, 1, 427, 1, 431, 1], 1),
   ([216, 1, 227, 1, 424, 1, 431, 1], 1),
   ([219, 1, 227, 1, 424, 1, 428, 1], 1),
   ([217, 1, 227, 1, 424, 1, 430, 1], 1),
   ([218, 1, 227, 1, 424, 1, 429, 1], -1)]

private theorem face5raw11_6_checked :
    fastCompactReflectRaw ((face5source11.drop 48).take 8) = face5raw11_6 := by
  decide

private def face5raw11_7 : RawPoly :=
  [([216, 1, 227, 1, 426, 1, 429, 1], -1),
   ([217, 1, 227, 1, 426, 1, 428, 1], -1),
   ([218, 1, 227, 1, 426, 1, 431, 1], -1),
   ([219, 1, 227, 1, 426, 1, 430, 1], 1),
   ([216, 1, 227, 1, 425, 1, 430, 1], 1),
   ([218, 1, 227, 1, 425, 1, 428, 1], 1),
   ([219, 1, 227, 1, 425, 1, 429, 1], 1),
   ([217, 1, 227, 1, 425, 1, 431, 1], -1)]

private theorem face5raw11_7_checked :
    fastCompactReflectRaw ((face5source11.drop 56).take 8) = face5raw11_7 := by
  decide

private theorem splitRaw (p : RatPoly) (n : Nat) :
    fastCompactReflectRaw (p.drop n) =
      fastCompactReflectRaw ((p.drop n).take 8) ++
        fastCompactReflectRaw (p.drop (n + 8)) := by
  have h := congrArg fastCompactReflectRaw (List.take_append_drop 8 (p.drop n)).symm
  simpa only [fastCompactReflectRaw, List.map_append, List.drop_drop] using h

private theorem face5source11_tail : face5source11.drop 64 = [] := by
  decide

private theorem face5raw11_checked :
    fastCompactReflectRaw face5source11 =
      face5raw11_0 ++ face5raw11_1 ++ face5raw11_2 ++ face5raw11_3 ++
        face5raw11_4 ++ face5raw11_5 ++ face5raw11_6 ++ face5raw11_7 := by
  change fastCompactReflectRaw (face5source11.drop 0) = _
  rw [splitRaw face5source11 0, face5raw11_0_checked]
  rw [splitRaw face5source11 8, face5raw11_1_checked]
  rw [splitRaw face5source11 16, face5raw11_2_checked]
  rw [splitRaw face5source11 24, face5raw11_3_checked]
  rw [splitRaw face5source11 32, face5raw11_4_checked]
  rw [splitRaw face5source11 40, face5raw11_5_checked]
  rw [splitRaw face5source11 48, face5raw11_6_checked]
  rw [splitRaw face5source11 56, face5raw11_7_checked]
  rw [face5source11_tail]
  rfl

private theorem face5canonical11_checked :
    canon (face5raw11_0 ++ face5raw11_1 ++ face5raw11_2 ++ face5raw11_3 ++
      face5raw11_4 ++ face5raw11_5 ++ face5raw11_6 ++ face5raw11_7) =
        faceSlice5Normal11Canonical := by
  decide

theorem faceSlice5_normal11_source :
    canon (fastCompactReflectRaw
      (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 5 11)).scalar) =
        faceSlice5Normal11Canonical := by
  change canon (fastCompactReflectRaw face5source11) = _
  rw [face5raw11_checked, face5canonical11_checked]
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal11_source
