import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

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

private def face3source0 : RatPoly :=
  (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 3 0)).scalar

private def face3raw0_0 : RawPoly :=
  [([68, 1, 292, 1, 300, 1, 304, 1], 1),
   ([68, 1, 293, 1, 300, 1, 305, 1], -1),
   ([68, 1, 294, 1, 300, 1, 306, 1], -1),
   ([68, 1, 295, 1, 300, 1, 307, 1], -1),
   ([68, 1, 292, 1, 301, 1, 305, 1], 1),
   ([68, 1, 293, 1, 301, 1, 304, 1], 1),
   ([68, 1, 294, 1, 301, 1, 307, 1], 1),
   ([68, 1, 295, 1, 301, 1, 306, 1], -1)]

private theorem face3raw0_0_checked :
    fastCompactReflectRaw ((face3source0.drop 0).take 8) = face3raw0_0 := by
  decide

private def face3raw0_1 : RawPoly :=
  [([68, 1, 292, 1, 302, 1, 306, 1], 1),
   ([68, 1, 294, 1, 302, 1, 304, 1], 1),
   ([68, 1, 295, 1, 302, 1, 305, 1], 1),
   ([68, 1, 293, 1, 302, 1, 307, 1], -1),
   ([68, 1, 292, 1, 303, 1, 307, 1], 1),
   ([68, 1, 295, 1, 303, 1, 304, 1], 1),
   ([68, 1, 293, 1, 303, 1, 306, 1], 1),
   ([68, 1, 294, 1, 303, 1, 305, 1], -1)]

private theorem face3raw0_1_checked :
    fastCompactReflectRaw ((face3source0.drop 8).take 8) = face3raw0_1 := by
  decide

private def face3raw0_2 : RawPoly :=
  [([69, 1, 292, 1, 301, 1, 304, 1], -1),
   ([69, 1, 293, 1, 301, 1, 305, 1], 1),
   ([69, 1, 294, 1, 301, 1, 306, 1], 1),
   ([69, 1, 295, 1, 301, 1, 307, 1], 1),
   ([69, 1, 292, 1, 300, 1, 305, 1], 1),
   ([69, 1, 293, 1, 300, 1, 304, 1], 1),
   ([69, 1, 294, 1, 300, 1, 307, 1], 1),
   ([69, 1, 295, 1, 300, 1, 306, 1], -1)]

private theorem face3raw0_2_checked :
    fastCompactReflectRaw ((face3source0.drop 16).take 8) = face3raw0_2 := by
  decide

private def face3raw0_3 : RawPoly :=
  [([69, 1, 292, 1, 303, 1, 306, 1], -1),
   ([69, 1, 294, 1, 303, 1, 304, 1], -1),
   ([69, 1, 295, 1, 303, 1, 305, 1], -1),
   ([69, 1, 293, 1, 303, 1, 307, 1], 1),
   ([69, 1, 292, 1, 302, 1, 307, 1], 1),
   ([69, 1, 295, 1, 302, 1, 304, 1], 1),
   ([69, 1, 293, 1, 302, 1, 306, 1], 1),
   ([69, 1, 294, 1, 302, 1, 305, 1], -1)]

private theorem face3raw0_3_checked :
    fastCompactReflectRaw ((face3source0.drop 24).take 8) = face3raw0_3 := by
  decide

private def face3raw0_4 : RawPoly :=
  [([70, 1, 292, 1, 302, 1, 304, 1], -1),
   ([70, 1, 293, 1, 302, 1, 305, 1], 1),
   ([70, 1, 294, 1, 302, 1, 306, 1], 1),
   ([70, 1, 295, 1, 302, 1, 307, 1], 1),
   ([70, 1, 292, 1, 300, 1, 306, 1], 1),
   ([70, 1, 294, 1, 300, 1, 304, 1], 1),
   ([70, 1, 295, 1, 300, 1, 305, 1], 1),
   ([70, 1, 293, 1, 300, 1, 307, 1], -1)]

private theorem face3raw0_4_checked :
    fastCompactReflectRaw ((face3source0.drop 32).take 8) = face3raw0_4 := by
  decide

private def face3raw0_5 : RawPoly :=
  [([70, 1, 292, 1, 301, 1, 307, 1], -1),
   ([70, 1, 295, 1, 301, 1, 304, 1], -1),
   ([70, 1, 293, 1, 301, 1, 306, 1], -1),
   ([70, 1, 294, 1, 301, 1, 305, 1], 1),
   ([70, 1, 292, 1, 303, 1, 305, 1], 1),
   ([70, 1, 293, 1, 303, 1, 304, 1], 1),
   ([70, 1, 294, 1, 303, 1, 307, 1], 1),
   ([70, 1, 295, 1, 303, 1, 306, 1], -1)]

private theorem face3raw0_5_checked :
    fastCompactReflectRaw ((face3source0.drop 40).take 8) = face3raw0_5 := by
  decide

private def face3raw0_6 : RawPoly :=
  [([71, 1, 292, 1, 303, 1, 304, 1], -1),
   ([71, 1, 293, 1, 303, 1, 305, 1], 1),
   ([71, 1, 294, 1, 303, 1, 306, 1], 1),
   ([71, 1, 295, 1, 303, 1, 307, 1], 1),
   ([71, 1, 292, 1, 300, 1, 307, 1], 1),
   ([71, 1, 295, 1, 300, 1, 304, 1], 1),
   ([71, 1, 293, 1, 300, 1, 306, 1], 1),
   ([71, 1, 294, 1, 300, 1, 305, 1], -1)]

private theorem face3raw0_6_checked :
    fastCompactReflectRaw ((face3source0.drop 48).take 8) = face3raw0_6 := by
  decide

private def face3raw0_7 : RawPoly :=
  [([71, 1, 292, 1, 302, 1, 305, 1], -1),
   ([71, 1, 293, 1, 302, 1, 304, 1], -1),
   ([71, 1, 294, 1, 302, 1, 307, 1], -1),
   ([71, 1, 295, 1, 302, 1, 306, 1], 1),
   ([71, 1, 292, 1, 301, 1, 306, 1], 1),
   ([71, 1, 294, 1, 301, 1, 304, 1], 1),
   ([71, 1, 295, 1, 301, 1, 305, 1], 1),
   ([71, 1, 293, 1, 301, 1, 307, 1], -1)]

private theorem face3raw0_7_checked :
    fastCompactReflectRaw ((face3source0.drop 56).take 8) = face3raw0_7 := by
  decide

private theorem splitRaw (p : RatPoly) (n : Nat) :
    fastCompactReflectRaw (p.drop n) =
      fastCompactReflectRaw ((p.drop n).take 8) ++
        fastCompactReflectRaw (p.drop (n + 8)) := by
  have h := congrArg fastCompactReflectRaw (List.take_append_drop 8 (p.drop n)).symm
  simpa only [fastCompactReflectRaw, List.map_append, List.drop_drop] using h

private theorem face3source0_tail : face3source0.drop 64 = [] := by
  decide

private theorem face3raw0_checked :
    fastCompactReflectRaw face3source0 =
      face3raw0_0 ++ face3raw0_1 ++ face3raw0_2 ++ face3raw0_3 ++
        face3raw0_4 ++ face3raw0_5 ++ face3raw0_6 ++ face3raw0_7 := by
  change fastCompactReflectRaw (face3source0.drop 0) = _
  rw [splitRaw face3source0 0, face3raw0_0_checked]
  rw [splitRaw face3source0 8, face3raw0_1_checked]
  rw [splitRaw face3source0 16, face3raw0_2_checked]
  rw [splitRaw face3source0 24, face3raw0_3_checked]
  rw [splitRaw face3source0 32, face3raw0_4_checked]
  rw [splitRaw face3source0 40, face3raw0_5_checked]
  rw [splitRaw face3source0 48, face3raw0_6_checked]
  rw [splitRaw face3source0 56, face3raw0_7_checked]
  rw [face3source0_tail]
  rfl

private theorem face3target0_checked :
    canon (sparseRaw
      (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 (faceSliceEntry 3 0))).scalar) =
      canon (face3raw0_0 ++ face3raw0_1 ++ face3raw0_2 ++ face3raw0_3 ++
        face3raw0_4 ++ face3raw0_5 ++ face3raw0_6 ++ face3raw0_7) := by
  decide

theorem faceSlice3_normal0 :
    compactCovarianceCheck (faceSliceEntry 3 0) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  unfold fastCompactCovarianceCheck
  change (canon (fastCompactReflectRaw face3source0) == _) = true
  rw [face3raw0_checked, face3target0_checked]
  decide

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice3_normal0
