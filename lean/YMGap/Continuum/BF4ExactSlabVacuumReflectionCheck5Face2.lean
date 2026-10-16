import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5Face1

namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

/- The original single decision exceeded the mandatory 20-GiB worker cap.
The retained raw literals are candidate data only; each eight-term block and
the final target canonicalization are checked by the Lean kernel. -/

private def face5source2 : RatPoly :=
  (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 5 2)).scalar

private def face5raw2_0 : RawPoly :=
  [([164, 1, 168, 1, 216, 1, 380, 1], 1),
   ([165, 1, 168, 1, 216, 1, 381, 1], -1),
   ([166, 1, 168, 1, 216, 1, 382, 1], -1),
   ([167, 1, 168, 1, 216, 1, 383, 1], -1),
   ([164, 1, 168, 1, 217, 1, 381, 1], 1),
   ([165, 1, 168, 1, 217, 1, 380, 1], 1),
   ([166, 1, 168, 1, 217, 1, 383, 1], 1),
   ([167, 1, 168, 1, 217, 1, 382, 1], -1)]

private theorem face5raw2_0_checked :
    fastCompactReflectRaw ((face5source2.drop 0).take 8) = face5raw2_0 := by
  decide

private def face5raw2_1 : RawPoly :=
  [([164, 1, 168, 1, 218, 1, 382, 1], 1),
   ([166, 1, 168, 1, 218, 1, 380, 1], 1),
   ([167, 1, 168, 1, 218, 1, 381, 1], 1),
   ([165, 1, 168, 1, 218, 1, 383, 1], -1),
   ([164, 1, 168, 1, 219, 1, 383, 1], 1),
   ([167, 1, 168, 1, 219, 1, 380, 1], 1),
   ([165, 1, 168, 1, 219, 1, 382, 1], 1),
   ([166, 1, 168, 1, 219, 1, 381, 1], -1)]

private theorem face5raw2_1_checked :
    fastCompactReflectRaw ((face5source2.drop 8).take 8) = face5raw2_1 := by
  decide

private def face5raw2_2 : RawPoly :=
  [([164, 1, 169, 1, 217, 1, 380, 1], -1),
   ([165, 1, 169, 1, 217, 1, 381, 1], 1),
   ([166, 1, 169, 1, 217, 1, 382, 1], 1),
   ([167, 1, 169, 1, 217, 1, 383, 1], 1),
   ([164, 1, 169, 1, 216, 1, 381, 1], 1),
   ([165, 1, 169, 1, 216, 1, 380, 1], 1),
   ([166, 1, 169, 1, 216, 1, 383, 1], 1),
   ([167, 1, 169, 1, 216, 1, 382, 1], -1)]

private theorem face5raw2_2_checked :
    fastCompactReflectRaw ((face5source2.drop 16).take 8) = face5raw2_2 := by
  decide

private def face5raw2_3 : RawPoly :=
  [([164, 1, 169, 1, 219, 1, 382, 1], -1),
   ([166, 1, 169, 1, 219, 1, 380, 1], -1),
   ([167, 1, 169, 1, 219, 1, 381, 1], -1),
   ([165, 1, 169, 1, 219, 1, 383, 1], 1),
   ([164, 1, 169, 1, 218, 1, 383, 1], 1),
   ([167, 1, 169, 1, 218, 1, 380, 1], 1),
   ([165, 1, 169, 1, 218, 1, 382, 1], 1),
   ([166, 1, 169, 1, 218, 1, 381, 1], -1)]

private theorem face5raw2_3_checked :
    fastCompactReflectRaw ((face5source2.drop 24).take 8) = face5raw2_3 := by
  decide

private def face5raw2_4 : RawPoly :=
  [([164, 1, 170, 1, 218, 1, 380, 1], -1),
   ([165, 1, 170, 1, 218, 1, 381, 1], 1),
   ([166, 1, 170, 1, 218, 1, 382, 1], 1),
   ([167, 1, 170, 1, 218, 1, 383, 1], 1),
   ([164, 1, 170, 1, 216, 1, 382, 1], 1),
   ([166, 1, 170, 1, 216, 1, 380, 1], 1),
   ([167, 1, 170, 1, 216, 1, 381, 1], 1),
   ([165, 1, 170, 1, 216, 1, 383, 1], -1)]

private theorem face5raw2_4_checked :
    fastCompactReflectRaw ((face5source2.drop 32).take 8) = face5raw2_4 := by
  decide

private def face5raw2_5 : RawPoly :=
  [([164, 1, 170, 1, 217, 1, 383, 1], -1),
   ([167, 1, 170, 1, 217, 1, 380, 1], -1),
   ([165, 1, 170, 1, 217, 1, 382, 1], -1),
   ([166, 1, 170, 1, 217, 1, 381, 1], 1),
   ([164, 1, 170, 1, 219, 1, 381, 1], 1),
   ([165, 1, 170, 1, 219, 1, 380, 1], 1),
   ([166, 1, 170, 1, 219, 1, 383, 1], 1),
   ([167, 1, 170, 1, 219, 1, 382, 1], -1)]

private theorem face5raw2_5_checked :
    fastCompactReflectRaw ((face5source2.drop 40).take 8) = face5raw2_5 := by
  decide

private def face5raw2_6 : RawPoly :=
  [([164, 1, 171, 1, 219, 1, 380, 1], -1),
   ([165, 1, 171, 1, 219, 1, 381, 1], 1),
   ([166, 1, 171, 1, 219, 1, 382, 1], 1),
   ([167, 1, 171, 1, 219, 1, 383, 1], 1),
   ([164, 1, 171, 1, 216, 1, 383, 1], 1),
   ([167, 1, 171, 1, 216, 1, 380, 1], 1),
   ([165, 1, 171, 1, 216, 1, 382, 1], 1),
   ([166, 1, 171, 1, 216, 1, 381, 1], -1)]

private theorem face5raw2_6_checked :
    fastCompactReflectRaw ((face5source2.drop 48).take 8) = face5raw2_6 := by
  decide

private def face5raw2_7 : RawPoly :=
  [([164, 1, 171, 1, 218, 1, 381, 1], -1),
   ([165, 1, 171, 1, 218, 1, 380, 1], -1),
   ([166, 1, 171, 1, 218, 1, 383, 1], -1),
   ([167, 1, 171, 1, 218, 1, 382, 1], 1),
   ([164, 1, 171, 1, 217, 1, 382, 1], 1),
   ([166, 1, 171, 1, 217, 1, 380, 1], 1),
   ([167, 1, 171, 1, 217, 1, 381, 1], 1),
   ([165, 1, 171, 1, 217, 1, 383, 1], -1)]

private theorem face5raw2_7_checked :
    fastCompactReflectRaw ((face5source2.drop 56).take 8) = face5raw2_7 := by
  decide

private theorem splitRaw (p : RatPoly) (n : Nat) :
    fastCompactReflectRaw (p.drop n) =
      fastCompactReflectRaw ((p.drop n).take 8) ++
        fastCompactReflectRaw (p.drop (n + 8)) := by
  have h := congrArg fastCompactReflectRaw (List.take_append_drop 8 (p.drop n)).symm
  simpa only [fastCompactReflectRaw, List.map_append, List.drop_drop] using h

private theorem face5source2_tail : face5source2.drop 64 = [] := by
  decide

private theorem face5raw2_checked :
    fastCompactReflectRaw face5source2 =
      face5raw2_0 ++ face5raw2_1 ++ face5raw2_2 ++ face5raw2_3 ++
        face5raw2_4 ++ face5raw2_5 ++ face5raw2_6 ++ face5raw2_7 := by
  change fastCompactReflectRaw (face5source2.drop 0) = _
  rw [splitRaw face5source2 0, face5raw2_0_checked]
  rw [splitRaw face5source2 8, face5raw2_1_checked]
  rw [splitRaw face5source2 16, face5raw2_2_checked]
  rw [splitRaw face5source2 24, face5raw2_3_checked]
  rw [splitRaw face5source2 32, face5raw2_4_checked]
  rw [splitRaw face5source2 40, face5raw2_5_checked]
  rw [splitRaw face5source2 48, face5raw2_6_checked]
  rw [splitRaw face5source2 56, face5raw2_7_checked]
  rw [face5source2_tail]
  rfl

private theorem face5target2_checked :
    canon (sparseRaw
      (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 (faceSliceEntry 5 2))).scalar) =
      canon (face5raw2_0 ++ face5raw2_1 ++ face5raw2_2 ++ face5raw2_3 ++
        face5raw2_4 ++ face5raw2_5 ++ face5raw2_6 ++ face5raw2_7) := by
  decide

theorem faceSlice5_normal2 :
    compactCovarianceCheck (faceSliceEntry 5 2) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  unfold fastCompactCovarianceCheck
  change (canon (fastCompactReflectRaw face5source2) == _) = true
  rw [face5raw2_checked, face5target2_checked]
  decide

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal2
