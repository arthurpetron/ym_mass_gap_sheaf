import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1Face1

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

/- The original single decision exceeded the recovery worker's memory cap.
Check eight eight-term raw blocks independently, then assemble the unchanged
covariance statement. These literals are untrusted candidate data: every
entry is checked against the actual source by ordinary kernel reduction. -/

private def face1source2 : RatPoly :=
  (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 1 2)).scalar

private def face1raw2_0 : RawPoly :=
  [([60, 1, 96, 1, 124, 1, 128, 1], 1),
   ([60, 1, 96, 1, 125, 1, 129, 1], 1),
   ([60, 1, 96, 1, 126, 1, 130, 1], 1),
   ([60, 1, 96, 1, 127, 1, 131, 1], 1),
   ([60, 1, 97, 1, 124, 1, 129, 1], -1),
   ([60, 1, 97, 1, 125, 1, 128, 1], 1),
   ([60, 1, 97, 1, 126, 1, 131, 1], -1),
   ([60, 1, 97, 1, 127, 1, 130, 1], 1)]

private theorem face1raw2_0_checked :
    fastCompactReflectRaw ((face1source2.drop 0).take 8) = face1raw2_0 := by
  decide

private def face1raw2_1 : RawPoly :=
  [([60, 1, 98, 1, 124, 1, 130, 1], -1),
   ([60, 1, 98, 1, 126, 1, 128, 1], 1),
   ([60, 1, 98, 1, 127, 1, 129, 1], -1),
   ([60, 1, 98, 1, 125, 1, 131, 1], 1),
   ([60, 1, 99, 1, 124, 1, 131, 1], -1),
   ([60, 1, 99, 1, 127, 1, 128, 1], 1),
   ([60, 1, 99, 1, 125, 1, 130, 1], -1),
   ([60, 1, 99, 1, 126, 1, 129, 1], 1)]

private theorem face1raw2_1_checked :
    fastCompactReflectRaw ((face1source2.drop 8).take 8) = face1raw2_1 := by
  decide

private def face1raw2_2 : RawPoly :=
  [([61, 1, 97, 1, 124, 1, 128, 1], 1),
   ([61, 1, 97, 1, 125, 1, 129, 1], 1),
   ([61, 1, 97, 1, 126, 1, 130, 1], 1),
   ([61, 1, 97, 1, 127, 1, 131, 1], 1),
   ([61, 1, 96, 1, 124, 1, 129, 1], 1),
   ([61, 1, 96, 1, 125, 1, 128, 1], -1),
   ([61, 1, 96, 1, 126, 1, 131, 1], 1),
   ([61, 1, 96, 1, 127, 1, 130, 1], -1)]

private theorem face1raw2_2_checked :
    fastCompactReflectRaw ((face1source2.drop 16).take 8) = face1raw2_2 := by
  decide

private def face1raw2_3 : RawPoly :=
  [([61, 1, 99, 1, 124, 1, 130, 1], -1),
   ([61, 1, 99, 1, 126, 1, 128, 1], 1),
   ([61, 1, 99, 1, 127, 1, 129, 1], -1),
   ([61, 1, 99, 1, 125, 1, 131, 1], 1),
   ([61, 1, 98, 1, 124, 1, 131, 1], 1),
   ([61, 1, 98, 1, 127, 1, 128, 1], -1),
   ([61, 1, 98, 1, 125, 1, 130, 1], 1),
   ([61, 1, 98, 1, 126, 1, 129, 1], -1)]

private theorem face1raw2_3_checked :
    fastCompactReflectRaw ((face1source2.drop 24).take 8) = face1raw2_3 := by
  decide

private def face1raw2_4 : RawPoly :=
  [([62, 1, 98, 1, 124, 1, 128, 1], 1),
   ([62, 1, 98, 1, 125, 1, 129, 1], 1),
   ([62, 1, 98, 1, 126, 1, 130, 1], 1),
   ([62, 1, 98, 1, 127, 1, 131, 1], 1),
   ([62, 1, 96, 1, 124, 1, 130, 1], 1),
   ([62, 1, 96, 1, 126, 1, 128, 1], -1),
   ([62, 1, 96, 1, 127, 1, 129, 1], 1),
   ([62, 1, 96, 1, 125, 1, 131, 1], -1)]

private theorem face1raw2_4_checked :
    fastCompactReflectRaw ((face1source2.drop 32).take 8) = face1raw2_4 := by
  decide

private def face1raw2_5 : RawPoly :=
  [([62, 1, 97, 1, 124, 1, 131, 1], -1),
   ([62, 1, 97, 1, 127, 1, 128, 1], 1),
   ([62, 1, 97, 1, 125, 1, 130, 1], -1),
   ([62, 1, 97, 1, 126, 1, 129, 1], 1),
   ([62, 1, 99, 1, 124, 1, 129, 1], 1),
   ([62, 1, 99, 1, 125, 1, 128, 1], -1),
   ([62, 1, 99, 1, 126, 1, 131, 1], 1),
   ([62, 1, 99, 1, 127, 1, 130, 1], -1)]

private theorem face1raw2_5_checked :
    fastCompactReflectRaw ((face1source2.drop 40).take 8) = face1raw2_5 := by
  decide

private def face1raw2_6 : RawPoly :=
  [([63, 1, 99, 1, 124, 1, 128, 1], 1),
   ([63, 1, 99, 1, 125, 1, 129, 1], 1),
   ([63, 1, 99, 1, 126, 1, 130, 1], 1),
   ([63, 1, 99, 1, 127, 1, 131, 1], 1),
   ([63, 1, 96, 1, 124, 1, 131, 1], 1),
   ([63, 1, 96, 1, 127, 1, 128, 1], -1),
   ([63, 1, 96, 1, 125, 1, 130, 1], 1),
   ([63, 1, 96, 1, 126, 1, 129, 1], -1)]

private theorem face1raw2_6_checked :
    fastCompactReflectRaw ((face1source2.drop 48).take 8) = face1raw2_6 := by
  decide

private def face1raw2_7 : RawPoly :=
  [([63, 1, 98, 1, 124, 1, 129, 1], -1),
   ([63, 1, 98, 1, 125, 1, 128, 1], 1),
   ([63, 1, 98, 1, 126, 1, 131, 1], -1),
   ([63, 1, 98, 1, 127, 1, 130, 1], 1),
   ([63, 1, 97, 1, 124, 1, 130, 1], 1),
   ([63, 1, 97, 1, 126, 1, 128, 1], -1),
   ([63, 1, 97, 1, 127, 1, 129, 1], 1),
   ([63, 1, 97, 1, 125, 1, 131, 1], -1)]

private theorem face1raw2_7_checked :
    fastCompactReflectRaw ((face1source2.drop 56).take 8) = face1raw2_7 := by
  decide

private theorem splitRaw (p : RatPoly) (n : Nat) :
    fastCompactReflectRaw (p.drop n) =
      fastCompactReflectRaw ((p.drop n).take 8) ++
        fastCompactReflectRaw (p.drop (n + 8)) := by
  have h := congrArg fastCompactReflectRaw (List.take_append_drop 8 (p.drop n)).symm
  simpa only [fastCompactReflectRaw, List.map_append, List.drop_drop] using h

private theorem face1source2_tail : face1source2.drop 64 = [] := by decide

private theorem face1raw2_checked :
    fastCompactReflectRaw face1source2 = face1raw2_0 ++ face1raw2_1 ++ face1raw2_2 ++ face1raw2_3 ++ face1raw2_4 ++ face1raw2_5 ++ face1raw2_6 ++ face1raw2_7 := by
  change fastCompactReflectRaw (face1source2.drop 0) = _
  rw [splitRaw face1source2 0, face1raw2_0_checked]
  rw [splitRaw face1source2 8, face1raw2_1_checked]
  rw [splitRaw face1source2 16, face1raw2_2_checked]
  rw [splitRaw face1source2 24, face1raw2_3_checked]
  rw [splitRaw face1source2 32, face1raw2_4_checked]
  rw [splitRaw face1source2 40, face1raw2_5_checked]
  rw [splitRaw face1source2 48, face1raw2_6_checked]
  rw [splitRaw face1source2 56, face1raw2_7_checked]
  rw [face1source2_tail]
  rfl

private theorem face1target2_checked :
    canon (sparseRaw
      (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 (faceSliceEntry 1 2))).scalar) =
      canon (face1raw2_0 ++ face1raw2_1 ++ face1raw2_2 ++ face1raw2_3 ++ face1raw2_4 ++ face1raw2_5 ++ face1raw2_6 ++ face1raw2_7) := by
  decide

theorem faceSlice1_normal2 :
    compactCovarianceCheck (faceSliceEntry 1 2) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  unfold fastCompactCovarianceCheck
  change (canon (fastCompactReflectRaw face1source2) == _) = true
  rw [face1raw2_checked, face1target2_checked]
  decide

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice1_normal2
