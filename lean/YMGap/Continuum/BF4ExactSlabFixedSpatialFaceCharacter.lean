/-
# An arbitrary actual spatial-face character in the common chart

A supplied member of the fixed spatial face list gives a radius-zero
physical presentation. Its first and second chart moments are pinned to
the literal original ambient plaquette character, with identical extent,
selected-chain action, cutoff stage and original partition. The face is
not restricted to the spatial origin. No bare-Haar moment, variance floor,
limiting nontriviality or continuum assertion is included here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (placeProbes)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe (placeWindowProbes)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (Physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
  (DistanceSpan radius encodeChart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit (unitSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)

local infix:50 " ≈ " => Q'.eqv

/-- The literal original fundamental character, not a source-slice surrogate. -/
def faceCharacter (extent : Nat) (p : Z4Plaq) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial extent p).scalar 1

/-- One fundamental character (integer representation label one) at distance zero. -/
def facePresentation (p : Z4Plaq) : DistanceSpan :=
  [(1, [(0, [(p, [(1, 1)])])])]

theorem facePresentation_physical {width : Nat} (p : Z4Plaq)
    (hp : p ∈ spatialFaces width) : Physical width (facePresentation p) := by
  intro x hx e he f hf
  have hx' := List.mem_singleton.mp hx
  subst x
  have he' := List.mem_singleton.mp he
  subst e
  have hf' := List.mem_singleton.mp hf
  subst f
  exact hp

def faceSpan (width : Nat) (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    PhysicalSpan width :=
  ⟨facePresentation p, facePresentation_physical p hp⟩

theorem faceSpan_radius (width : Nat) (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    radius (faceSpan width p hp).val = 0 := rfl

private theorem singleton_sum (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul 1 p) polyZero) p :=
  ((RatPolyCoeffEqv.one_smul p).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero p)

private theorem singleton_ledger (p : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polySmul 1
        (polyMul (polyAdd (polySmul 1 p) polyZero) polyOne)) polyZero) p := by
  have hf : RatPolyCoeffEqv
      (polyMul (polyAdd (polySmul 1 p) polyZero) polyOne) p :=
    ((singleton_sum p).mul (RatPolyCoeffEqv.refl polyOne)).trans
      (RatPolyCoeffEqv.mul_one _)
  exact ((hf.smul 1).add (RatPolyCoeffEqv.refl polyZero)).trans (singleton_sum _)

-- Only singleton/empty-product bookkeeping is reduced, never the coordinate word.
attribute [local irreducible] correctedSlabPlaquettePolynomial

/-- Place the face literally in the ambient slab; no physical guard is needed
for this polynomial identity. -/
theorem placedSpan_character (extent time : Nat) (p : Z4Plaq) :
    RatPolyCoeffEqv (placedSpan extent time (facePresentation p))
      (faceCharacter extent (timeShiftPlaquette time p)) := by
  change RatPolyCoeffEqv
    (polyAdd (polySmul 1
      (polyMul (polyAdd (polySmul 1
        (sweptCharacter extent 0 (timeShiftPlaquette time p) 1)) polyZero) polyOne)) polyZero) _
  have hchar : sweptCharacter extent 0 (timeShiftPlaquette time p) 1 =
      faceCharacter extent (timeShiftPlaquette time p) := by
    simp only [sweptCharacter, if_neg (not_swept_zero _), faceCharacter]
  rw [hchar]
  exact singleton_ledger _

private theorem placedSpan_unit (extent time : Nat) :
    RatPolyCoeffEqv (placedSpan extent time unitSpan) polyOne := by
  change RatPolyCoeffEqv (polyAdd (polySmul 1 polyOne) polyZero) polyOne
  exact singleton_sum _

private theorem finite_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (stage : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    finiteValue w hw0 hw1 extent ids hids p stage ≈
      finiteValue w hw0 hw1 extent ids hids q stage := by
  unfold finiteValue numerator
  exact Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (h.mul_right _))

/-- The first moment has the original character insertion and the original
partition at exactly the same cutoff stage and selected action as the square. -/
theorem chartScalar_mean_finiteValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (p : Z4Plaq) (hp : p ∈ spatialFaces width) (stage t : Nat) :
    chartScalar hw0 hw1 width stage 0 (faceSpan width p hp) (unit width) t ≈
      finiteValue w hw0 hw1 (adjacentEvenExtent (width+t))
        (chainIds (adjacentEvenExtent (width+t)) width (width+1) (t+t))
        (fun _ hi => chainIds_physical hi)
        (faceCharacter (adjacentEvenExtent (width+t))
          (timeShiftPlaquette ((width+1)+t) p)) stage := by
  unfold chartScalar
  simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add]
  apply finite_congr hw0 hw1 _ _ _ stage
  change RatPolyCoeffEqv
    (polyMul
      (placedSpan (adjacentEvenExtent (width+t)) ((width+1)+t) (facePresentation p))
      (placedSpan (adjacentEvenExtent (width+t)) ((width+1)+t) unitSpan)) _
  exact ((placedSpan_character _ _ p).mul (placedSpan_unit _ _)).trans
    (RatPolyCoeffEqv.mul_one _)

/-- Reflection fixes distance zero. The second moment therefore inserts the
literal square of the same original face character, without changing action/Z. -/
theorem chartScalar_square_finiteValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (p : Z4Plaq) (hp : p ∈ spatialFaces width) (stage t : Nat) :
    chartScalar hw0 hw1 width stage 0 (faceSpan width p hp) (faceSpan width p hp) t ≈
      finiteValue w hw0 hw1 (adjacentEvenExtent (width+t))
        (chainIds (adjacentEvenExtent (width+t)) width (width+1) (t+t))
        (fun _ hi => chainIds_physical hi)
        (polyMul
          (faceCharacter (adjacentEvenExtent (width+t))
            (timeShiftPlaquette ((width+1)+t) p))
          (faceCharacter (adjacentEvenExtent (width+t))
            (timeShiftPlaquette ((width+1)+t) p))) stage := by
  unfold chartScalar
  simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add]
  apply finite_congr hw0 hw1 _ _ _ stage
  change RatPolyCoeffEqv
    (polyMul
      (placedSpan (adjacentEvenExtent (width+t)) ((width+1)+t) (facePresentation p))
      (placedSpan (adjacentEvenExtent (width+t)) ((width+1)+t) (facePresentation p))) _
  exact (placedSpan_character _ _ p).mul (placedSpan_character _ _ p)

#print axioms facePresentation_physical
#print axioms faceSpan_radius
#print axioms placedSpan_character
#print axioms chartScalar_mean_finiteValue
#print axioms chartScalar_square_finiteValue

end YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter
