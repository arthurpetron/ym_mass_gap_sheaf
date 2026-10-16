import YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3Face0
namespace YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

private def r0 : RawPoly :=
  [([76, 1, 292, 1, 308, 1, 312, 1], 1),
   ([76, 1, 293, 1, 308, 1, 313, 1], -1),
   ([76, 1, 294, 1, 308, 1, 314, 1], -1),
   ([76, 1, 295, 1, 308, 1, 315, 1], -1),
   ([76, 1, 292, 1, 309, 1, 313, 1], 1),
   ([76, 1, 293, 1, 309, 1, 312, 1], 1),
   ([76, 1, 294, 1, 309, 1, 315, 1], 1),
   ([76, 1, 295, 1, 309, 1, 314, 1], -1)]

private def r1 : RawPoly :=
  [([76, 1, 292, 1, 310, 1, 314, 1], 1),
   ([76, 1, 294, 1, 310, 1, 312, 1], 1),
   ([76, 1, 295, 1, 310, 1, 313, 1], 1),
   ([76, 1, 293, 1, 310, 1, 315, 1], -1),
   ([76, 1, 292, 1, 311, 1, 315, 1], 1),
   ([76, 1, 295, 1, 311, 1, 312, 1], 1),
   ([76, 1, 293, 1, 311, 1, 314, 1], 1),
   ([76, 1, 294, 1, 311, 1, 313, 1], -1)]

private def r2 : RawPoly :=
  [([77, 1, 292, 1, 309, 1, 312, 1], -1),
   ([77, 1, 293, 1, 309, 1, 313, 1], 1),
   ([77, 1, 294, 1, 309, 1, 314, 1], 1),
   ([77, 1, 295, 1, 309, 1, 315, 1], 1),
   ([77, 1, 292, 1, 308, 1, 313, 1], 1),
   ([77, 1, 293, 1, 308, 1, 312, 1], 1),
   ([77, 1, 294, 1, 308, 1, 315, 1], 1),
   ([77, 1, 295, 1, 308, 1, 314, 1], -1)]

private def r3 : RawPoly :=
  [([77, 1, 292, 1, 311, 1, 314, 1], -1),
   ([77, 1, 294, 1, 311, 1, 312, 1], -1),
   ([77, 1, 295, 1, 311, 1, 313, 1], -1),
   ([77, 1, 293, 1, 311, 1, 315, 1], 1),
   ([77, 1, 292, 1, 310, 1, 315, 1], 1),
   ([77, 1, 295, 1, 310, 1, 312, 1], 1),
   ([77, 1, 293, 1, 310, 1, 314, 1], 1),
   ([77, 1, 294, 1, 310, 1, 313, 1], -1)]

private def r4 : RawPoly :=
  [([78, 1, 292, 1, 310, 1, 312, 1], -1),
   ([78, 1, 293, 1, 310, 1, 313, 1], 1),
   ([78, 1, 294, 1, 310, 1, 314, 1], 1),
   ([78, 1, 295, 1, 310, 1, 315, 1], 1),
   ([78, 1, 292, 1, 308, 1, 314, 1], 1),
   ([78, 1, 294, 1, 308, 1, 312, 1], 1),
   ([78, 1, 295, 1, 308, 1, 313, 1], 1),
   ([78, 1, 293, 1, 308, 1, 315, 1], -1)]

private def r5 : RawPoly :=
  [([78, 1, 292, 1, 309, 1, 315, 1], -1),
   ([78, 1, 295, 1, 309, 1, 312, 1], -1),
   ([78, 1, 293, 1, 309, 1, 314, 1], -1),
   ([78, 1, 294, 1, 309, 1, 313, 1], 1),
   ([78, 1, 292, 1, 311, 1, 313, 1], 1),
   ([78, 1, 293, 1, 311, 1, 312, 1], 1),
   ([78, 1, 294, 1, 311, 1, 315, 1], 1),
   ([78, 1, 295, 1, 311, 1, 314, 1], -1)]

private def r6 : RawPoly :=
  [([79, 1, 292, 1, 311, 1, 312, 1], -1),
   ([79, 1, 293, 1, 311, 1, 313, 1], 1),
   ([79, 1, 294, 1, 311, 1, 314, 1], 1),
   ([79, 1, 295, 1, 311, 1, 315, 1], 1),
   ([79, 1, 292, 1, 308, 1, 315, 1], 1),
   ([79, 1, 295, 1, 308, 1, 312, 1], 1),
   ([79, 1, 293, 1, 308, 1, 314, 1], 1),
   ([79, 1, 294, 1, 308, 1, 313, 1], -1)]

private def r7 : RawPoly :=
  [([79, 1, 292, 1, 310, 1, 313, 1], -1),
   ([79, 1, 293, 1, 310, 1, 312, 1], -1),
   ([79, 1, 294, 1, 310, 1, 315, 1], -1),
   ([79, 1, 295, 1, 310, 1, 314, 1], 1),
   ([79, 1, 292, 1, 309, 1, 314, 1], 1),
   ([79, 1, 294, 1, 309, 1, 312, 1], 1),
   ([79, 1, 295, 1, 309, 1, 313, 1], 1),
   ([79, 1, 293, 1, 309, 1, 315, 1], -1)]

private def source : RatPoly :=
  (correctedSlabPlaquettePolynomial 1 (faceSliceEntry 3 1)).scalar

private theorem h0 : fastCompactReflectRaw ((source.drop 0).take 8) = r0 := by decide
private theorem h1 : fastCompactReflectRaw ((source.drop 8).take 8) = r1 := by decide
private theorem h2 : fastCompactReflectRaw ((source.drop 16).take 8) = r2 := by decide
private theorem h3 : fastCompactReflectRaw ((source.drop 24).take 8) = r3 := by decide
private theorem h4 : fastCompactReflectRaw ((source.drop 32).take 8) = r4 := by decide
private theorem h5 : fastCompactReflectRaw ((source.drop 40).take 8) = r5 := by decide
private theorem h6 : fastCompactReflectRaw ((source.drop 48).take 8) = r6 := by decide
private theorem h7 : fastCompactReflectRaw ((source.drop 56).take 8) = r7 := by decide

private theorem splitRaw (p : RatPoly) (n : Nat) :
    fastCompactReflectRaw (p.drop n) =
      fastCompactReflectRaw ((p.drop n).take 8) ++ fastCompactReflectRaw (p.drop (n + 8)) := by
  have h := congrArg fastCompactReflectRaw (List.take_append_drop 8 (p.drop n)).symm
  simpa only [fastCompactReflectRaw, List.map_append, List.drop_drop] using h

private theorem source_tail : source.drop 64 = [] := by decide

private theorem raw_checked :
    fastCompactReflectRaw source = r0 ++ r1 ++ r2 ++ r3 ++ r4 ++ r5 ++ r6 ++ r7 := by
  change fastCompactReflectRaw (source.drop 0) = _
  rw [splitRaw source 0, h0]
  rw [splitRaw source 8, h1]
  rw [splitRaw source 16, h2]
  rw [splitRaw source 24, h3]
  rw [splitRaw source 32, h4]
  rw [splitRaw source 40, h5]
  rw [splitRaw source 48, h6]
  rw [splitRaw source 56, h7]
  rw [source_tail]
  rfl

private theorem target_checked :
    canon (sparseRaw
      (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 (faceSliceEntry 3 1))).scalar) =
      canon (r0 ++ r1 ++ r2 ++ r3 ++ r4 ++ r5 ++ r6 ++ r7) := by decide

theorem faceSlice3_normal1 :
    compactCovarianceCheck (faceSliceEntry 3 1) = true := by
  rw [← fastCompactCovarianceCheck_eq]
  unfold fastCompactCovarianceCheck
  change (canon (fastCompactReflectRaw source) == _) = true
  rw [raw_checked, target_checked]
  decide
end YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice3_normal1
