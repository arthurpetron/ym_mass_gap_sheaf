import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4Face5

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

private def face4source6 : RatPoly :=
  (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 4 6)).scalar

private def face4raw6_0 : RawPoly :=
  [([196, 1, 300, 1, 388, 1, 392, 1], 1),
   ([196, 1, 301, 1, 388, 1, 393, 1], -1),
   ([196, 1, 302, 1, 388, 1, 394, 1], -1),
   ([196, 1, 303, 1, 388, 1, 395, 1], -1),
   ([196, 1, 300, 1, 389, 1, 393, 1], 1),
   ([196, 1, 301, 1, 389, 1, 392, 1], 1),
   ([196, 1, 302, 1, 389, 1, 395, 1], 1),
   ([196, 1, 303, 1, 389, 1, 394, 1], -1)]

private theorem face4raw6_0_checked :
    fastCompactReflectRaw ((face4source6.drop 0).take 8) = face4raw6_0 := by
  decide

private def face4raw6_1 : RawPoly :=
  [([196, 1, 300, 1, 390, 1, 394, 1], 1),
   ([196, 1, 302, 1, 390, 1, 392, 1], 1),
   ([196, 1, 303, 1, 390, 1, 393, 1], 1),
   ([196, 1, 301, 1, 390, 1, 395, 1], -1),
   ([196, 1, 300, 1, 391, 1, 395, 1], 1),
   ([196, 1, 303, 1, 391, 1, 392, 1], 1),
   ([196, 1, 301, 1, 391, 1, 394, 1], 1),
   ([196, 1, 302, 1, 391, 1, 393, 1], -1)]

private theorem face4raw6_1_checked :
    fastCompactReflectRaw ((face4source6.drop 8).take 8) = face4raw6_1 := by
  decide

private def face4raw6_2 : RawPoly :=
  [([197, 1, 300, 1, 389, 1, 392, 1], -1),
   ([197, 1, 301, 1, 389, 1, 393, 1], 1),
   ([197, 1, 302, 1, 389, 1, 394, 1], 1),
   ([197, 1, 303, 1, 389, 1, 395, 1], 1),
   ([197, 1, 300, 1, 388, 1, 393, 1], 1),
   ([197, 1, 301, 1, 388, 1, 392, 1], 1),
   ([197, 1, 302, 1, 388, 1, 395, 1], 1),
   ([197, 1, 303, 1, 388, 1, 394, 1], -1)]

private theorem face4raw6_2_checked :
    fastCompactReflectRaw ((face4source6.drop 16).take 8) = face4raw6_2 := by
  decide

private def face4raw6_3 : RawPoly :=
  [([197, 1, 300, 1, 391, 1, 394, 1], -1),
   ([197, 1, 302, 1, 391, 1, 392, 1], -1),
   ([197, 1, 303, 1, 391, 1, 393, 1], -1),
   ([197, 1, 301, 1, 391, 1, 395, 1], 1),
   ([197, 1, 300, 1, 390, 1, 395, 1], 1),
   ([197, 1, 303, 1, 390, 1, 392, 1], 1),
   ([197, 1, 301, 1, 390, 1, 394, 1], 1),
   ([197, 1, 302, 1, 390, 1, 393, 1], -1)]

private theorem face4raw6_3_checked :
    fastCompactReflectRaw ((face4source6.drop 24).take 8) = face4raw6_3 := by
  decide

private def face4raw6_4 : RawPoly :=
  [([198, 1, 300, 1, 390, 1, 392, 1], -1),
   ([198, 1, 301, 1, 390, 1, 393, 1], 1),
   ([198, 1, 302, 1, 390, 1, 394, 1], 1),
   ([198, 1, 303, 1, 390, 1, 395, 1], 1),
   ([198, 1, 300, 1, 388, 1, 394, 1], 1),
   ([198, 1, 302, 1, 388, 1, 392, 1], 1),
   ([198, 1, 303, 1, 388, 1, 393, 1], 1),
   ([198, 1, 301, 1, 388, 1, 395, 1], -1)]

private theorem face4raw6_4_checked :
    fastCompactReflectRaw ((face4source6.drop 32).take 8) = face4raw6_4 := by
  decide

private def face4raw6_5 : RawPoly :=
  [([198, 1, 300, 1, 389, 1, 395, 1], -1),
   ([198, 1, 303, 1, 389, 1, 392, 1], -1),
   ([198, 1, 301, 1, 389, 1, 394, 1], -1),
   ([198, 1, 302, 1, 389, 1, 393, 1], 1),
   ([198, 1, 300, 1, 391, 1, 393, 1], 1),
   ([198, 1, 301, 1, 391, 1, 392, 1], 1),
   ([198, 1, 302, 1, 391, 1, 395, 1], 1),
   ([198, 1, 303, 1, 391, 1, 394, 1], -1)]

private theorem face4raw6_5_checked :
    fastCompactReflectRaw ((face4source6.drop 40).take 8) = face4raw6_5 := by
  decide

private def face4raw6_6 : RawPoly :=
  [([199, 1, 300, 1, 391, 1, 392, 1], -1),
   ([199, 1, 301, 1, 391, 1, 393, 1], 1),
   ([199, 1, 302, 1, 391, 1, 394, 1], 1),
   ([199, 1, 303, 1, 391, 1, 395, 1], 1),
   ([199, 1, 300, 1, 388, 1, 395, 1], 1),
   ([199, 1, 303, 1, 388, 1, 392, 1], 1),
   ([199, 1, 301, 1, 388, 1, 394, 1], 1),
   ([199, 1, 302, 1, 388, 1, 393, 1], -1)]

private theorem face4raw6_6_checked :
    fastCompactReflectRaw ((face4source6.drop 48).take 8) = face4raw6_6 := by
  decide

private def face4raw6_7 : RawPoly :=
  [([199, 1, 300, 1, 390, 1, 393, 1], -1),
   ([199, 1, 301, 1, 390, 1, 392, 1], -1),
   ([199, 1, 302, 1, 390, 1, 395, 1], -1),
   ([199, 1, 303, 1, 390, 1, 394, 1], 1),
   ([199, 1, 300, 1, 389, 1, 394, 1], 1),
   ([199, 1, 302, 1, 389, 1, 392, 1], 1),
   ([199, 1, 303, 1, 389, 1, 393, 1], 1),
   ([199, 1, 301, 1, 389, 1, 395, 1], -1)]

private theorem face4raw6_7_checked :
    fastCompactReflectRaw ((face4source6.drop 56).take 8) = face4raw6_7 := by
  decide

private theorem splitRaw (p : RatPoly) (n : Nat) :
    fastCompactReflectRaw (p.drop n) =
      fastCompactReflectRaw ((p.drop n).take 8) ++
        fastCompactReflectRaw (p.drop (n + 8)) := by
  have h := congrArg fastCompactReflectRaw (List.take_append_drop 8 (p.drop n)).symm
  simpa only [fastCompactReflectRaw, List.map_append, List.drop_drop] using h

private theorem face4source6_tail : face4source6.drop 64 = [] := by
  decide

private theorem face4raw6_checked :
    fastCompactReflectRaw face4source6 =
      face4raw6_0 ++ face4raw6_1 ++ face4raw6_2 ++ face4raw6_3 ++
        face4raw6_4 ++ face4raw6_5 ++ face4raw6_6 ++ face4raw6_7 := by
  change fastCompactReflectRaw (face4source6.drop 0) = _
  rw [splitRaw face4source6 0, face4raw6_0_checked]
  rw [splitRaw face4source6 8, face4raw6_1_checked]
  rw [splitRaw face4source6 16, face4raw6_2_checked]
  rw [splitRaw face4source6 24, face4raw6_3_checked]
  rw [splitRaw face4source6 32, face4raw6_4_checked]
  rw [splitRaw face4source6 40, face4raw6_5_checked]
  rw [splitRaw face4source6 48, face4raw6_6_checked]
  rw [splitRaw face4source6 56, face4raw6_7_checked]
  rw [face4source6_tail]
  rfl

private theorem face4target6_checked :
    canon (sparseRaw
      (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 (faceSliceEntry 4 6))).scalar) =
      canon (face4raw6_0 ++ face4raw6_1 ++ face4raw6_2 ++ face4raw6_3 ++
        face4raw6_4 ++ face4raw6_5 ++ face4raw6_6 ++ face4raw6_7) := by
  decide

theorem faceSlice4_normal6 :
    compactCovarianceCheck (faceSliceEntry 4 6) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  unfold fastCompactCovarianceCheck
  change (canon (fastCompactReflectRaw face4source6) == _) = true
  rw [face4raw6_checked, face4target6_checked]
  decide

end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice4_normal6
