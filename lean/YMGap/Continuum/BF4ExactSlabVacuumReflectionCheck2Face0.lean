import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

/- The original single decision exceeded the mandatory 20-GiB worker cap.
Check eight eight-term raw blocks independently, then assemble the unchanged
covariance statement.  These literals are untrusted candidate data: every
entry is checked against the actual source by ordinary kernel reduction. -/

private def face2source0 : RatPoly :=
  (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 2 0)).scalar

private def face2raw0_0 : RawPoly :=
  [([8, 1, 156, 1, 160, 1, 164, 1], 1),
   ([9, 1, 156, 1, 160, 1, 165, 1], -1),
   ([10, 1, 156, 1, 160, 1, 166, 1], -1),
   ([11, 1, 156, 1, 160, 1, 167, 1], -1),
   ([8, 1, 156, 1, 161, 1, 165, 1], 1),
   ([9, 1, 156, 1, 161, 1, 164, 1], 1),
   ([10, 1, 156, 1, 161, 1, 167, 1], 1),
   ([11, 1, 156, 1, 161, 1, 166, 1], -1)]

private theorem face2raw0_0_checked :
    fastCompactReflectRaw ((face2source0.drop 0).take 8) = face2raw0_0 := by
  decide

private def face2raw0_1 : RawPoly :=
  [([8, 1, 156, 1, 162, 1, 166, 1], 1),
   ([10, 1, 156, 1, 162, 1, 164, 1], 1),
   ([11, 1, 156, 1, 162, 1, 165, 1], 1),
   ([9, 1, 156, 1, 162, 1, 167, 1], -1),
   ([8, 1, 156, 1, 163, 1, 167, 1], 1),
   ([11, 1, 156, 1, 163, 1, 164, 1], 1),
   ([9, 1, 156, 1, 163, 1, 166, 1], 1),
   ([10, 1, 156, 1, 163, 1, 165, 1], -1)]

private theorem face2raw0_1_checked :
    fastCompactReflectRaw ((face2source0.drop 8).take 8) = face2raw0_1 := by
  decide

private def face2raw0_2 : RawPoly :=
  [([8, 1, 157, 1, 161, 1, 164, 1], -1),
   ([9, 1, 157, 1, 161, 1, 165, 1], 1),
   ([10, 1, 157, 1, 161, 1, 166, 1], 1),
   ([11, 1, 157, 1, 161, 1, 167, 1], 1),
   ([8, 1, 157, 1, 160, 1, 165, 1], 1),
   ([9, 1, 157, 1, 160, 1, 164, 1], 1),
   ([10, 1, 157, 1, 160, 1, 167, 1], 1),
   ([11, 1, 157, 1, 160, 1, 166, 1], -1)]

private theorem face2raw0_2_checked :
    fastCompactReflectRaw ((face2source0.drop 16).take 8) = face2raw0_2 := by
  decide

private def face2raw0_3 : RawPoly :=
  [([8, 1, 157, 1, 163, 1, 166, 1], -1),
   ([10, 1, 157, 1, 163, 1, 164, 1], -1),
   ([11, 1, 157, 1, 163, 1, 165, 1], -1),
   ([9, 1, 157, 1, 163, 1, 167, 1], 1),
   ([8, 1, 157, 1, 162, 1, 167, 1], 1),
   ([11, 1, 157, 1, 162, 1, 164, 1], 1),
   ([9, 1, 157, 1, 162, 1, 166, 1], 1),
   ([10, 1, 157, 1, 162, 1, 165, 1], -1)]

private theorem face2raw0_3_checked :
    fastCompactReflectRaw ((face2source0.drop 24).take 8) = face2raw0_3 := by
  decide

private def face2raw0_4 : RawPoly :=
  [([8, 1, 158, 1, 162, 1, 164, 1], -1),
   ([9, 1, 158, 1, 162, 1, 165, 1], 1),
   ([10, 1, 158, 1, 162, 1, 166, 1], 1),
   ([11, 1, 158, 1, 162, 1, 167, 1], 1),
   ([8, 1, 158, 1, 160, 1, 166, 1], 1),
   ([10, 1, 158, 1, 160, 1, 164, 1], 1),
   ([11, 1, 158, 1, 160, 1, 165, 1], 1),
   ([9, 1, 158, 1, 160, 1, 167, 1], -1)]

private theorem face2raw0_4_checked :
    fastCompactReflectRaw ((face2source0.drop 32).take 8) = face2raw0_4 := by
  decide

private def face2raw0_5 : RawPoly :=
  [([8, 1, 158, 1, 161, 1, 167, 1], -1),
   ([11, 1, 158, 1, 161, 1, 164, 1], -1),
   ([9, 1, 158, 1, 161, 1, 166, 1], -1),
   ([10, 1, 158, 1, 161, 1, 165, 1], 1),
   ([8, 1, 158, 1, 163, 1, 165, 1], 1),
   ([9, 1, 158, 1, 163, 1, 164, 1], 1),
   ([10, 1, 158, 1, 163, 1, 167, 1], 1),
   ([11, 1, 158, 1, 163, 1, 166, 1], -1)]

private theorem face2raw0_5_checked :
    fastCompactReflectRaw ((face2source0.drop 40).take 8) = face2raw0_5 := by
  decide

private def face2raw0_6 : RawPoly :=
  [([8, 1, 159, 1, 163, 1, 164, 1], -1),
   ([9, 1, 159, 1, 163, 1, 165, 1], 1),
   ([10, 1, 159, 1, 163, 1, 166, 1], 1),
   ([11, 1, 159, 1, 163, 1, 167, 1], 1),
   ([8, 1, 159, 1, 160, 1, 167, 1], 1),
   ([11, 1, 159, 1, 160, 1, 164, 1], 1),
   ([9, 1, 159, 1, 160, 1, 166, 1], 1),
   ([10, 1, 159, 1, 160, 1, 165, 1], -1)]

private theorem face2raw0_6_checked :
    fastCompactReflectRaw ((face2source0.drop 48).take 8) = face2raw0_6 := by
  decide

private def face2raw0_7 : RawPoly :=
  [([8, 1, 159, 1, 162, 1, 165, 1], -1),
   ([9, 1, 159, 1, 162, 1, 164, 1], -1),
   ([10, 1, 159, 1, 162, 1, 167, 1], -1),
   ([11, 1, 159, 1, 162, 1, 166, 1], 1),
   ([8, 1, 159, 1, 161, 1, 166, 1], 1),
   ([10, 1, 159, 1, 161, 1, 164, 1], 1),
   ([11, 1, 159, 1, 161, 1, 165, 1], 1),
   ([9, 1, 159, 1, 161, 1, 167, 1], -1)]

private theorem face2raw0_7_checked :
    fastCompactReflectRaw ((face2source0.drop 56).take 8) = face2raw0_7 := by
  decide

private theorem splitRaw (p : RatPoly) (n : Nat) :
    fastCompactReflectRaw (p.drop n) =
      fastCompactReflectRaw ((p.drop n).take 8) ++
        fastCompactReflectRaw (p.drop (n + 8)) := by
  have h := congrArg fastCompactReflectRaw (List.take_append_drop 8 (p.drop n)).symm
  simpa only [fastCompactReflectRaw, List.map_append, List.drop_drop] using h

private theorem face2source0_tail : face2source0.drop 64 = [] := by
  decide

private theorem face2raw0_checked :
    fastCompactReflectRaw face2source0 =
      face2raw0_0 ++ face2raw0_1 ++ face2raw0_2 ++ face2raw0_3 ++
        face2raw0_4 ++ face2raw0_5 ++ face2raw0_6 ++ face2raw0_7 := by
  change fastCompactReflectRaw (face2source0.drop 0) = _
  rw [splitRaw face2source0 0, face2raw0_0_checked]
  rw [splitRaw face2source0 8, face2raw0_1_checked]
  rw [splitRaw face2source0 16, face2raw0_2_checked]
  rw [splitRaw face2source0 24, face2raw0_3_checked]
  rw [splitRaw face2source0 32, face2raw0_4_checked]
  rw [splitRaw face2source0 40, face2raw0_5_checked]
  rw [splitRaw face2source0 48, face2raw0_6_checked]
  rw [splitRaw face2source0 56, face2raw0_7_checked]
  rw [face2source0_tail]
  rfl

private theorem face2target0_checked :
    canon (sparseRaw
      (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 (faceSliceEntry 2 0))).scalar) =
      canon (face2raw0_0 ++ face2raw0_1 ++ face2raw0_2 ++ face2raw0_3 ++
        face2raw0_4 ++ face2raw0_5 ++ face2raw0_6 ++ face2raw0_7) := by
  decide

theorem faceSlice2_normal0 :
    compactCovarianceCheck (faceSliceEntry 2 0) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  unfold fastCompactCovarianceCheck
  change (canon (fastCompactReflectRaw face2source0) == _) = true
  rw [face2raw0_checked, face2target0_checked]
  decide

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice2_normal0
