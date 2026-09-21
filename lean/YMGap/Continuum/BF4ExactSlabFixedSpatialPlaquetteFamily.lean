/-
# Signed spatial plaquette families in the common radius-zero chart

A finite signed family of actual spatial plaquettes defines a literal
radius-zero physical span.  Its first and diagonal second chart moments are
identified with the same signed family placed in the original selected slab,
at the same extent, cutoff stage, selected chain and partition.

No duplicate-free hypothesis, coefficient positivity, variance estimate,
limit passage or Osterwalder--Schrader norm identification is used here.
The radius-zero fact is retained explicitly for the later reflected-form
consumer.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter
import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamily

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
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
  (adjacentEvenExtent)

local infix:50 " ≈ " => Q'.eqv

/-- The literal signed distance-zero presentation.  Repetitions are retained. -/
def familyPresentation (qs : List Z4Plaq) (c : Z4Plaq → Q') : DistanceSpan :=
  qs.map (fun p => (c p, [(0, [(p, [(1, 1)])])]))

theorem familyPresentation_physical {width : Nat} (qs : List Z4Plaq)
    (c : Z4Plaq → Q') (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    Physical width (familyPresentation qs c) := by
  intro x hx e he f hf
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have he' := List.mem_singleton.mp he
  subst e
  have hf' := List.mem_singleton.mp hf
  subst f
  exact hqs p hp

/-- The signed family as a physical vector before completion. -/
def familySpan (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) : PhysicalSpan width :=
  ⟨familyPresentation qs c, familyPresentation_physical qs c hqs⟩

/-- Every member is at intrinsic distance zero, including the empty family. -/
theorem familySpan_radius (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    radius (familySpan width qs c hqs).val = 0 := by
  have h : radius (familyPresentation qs c) = 0 := by
    induction qs with
    | nil => rfl
    | cons p qs ih =>
        simp only [familyPresentation, List.map_cons, radius]
        change max
          (BF4ExactSlabFixedSpatialIntrinsicReflectedForm.scheduleRadius
            [(0, [(p, [(1, 1)])])])
          (radius (familyPresentation qs c)) = 0
        rw [ih (fun q hq => hqs q (List.mem_cons_of_mem p hq))]
        rfl
  exact h

/-- The literal ambient labels and unchanged coefficients at the chart time. -/
def placedTerms (width t : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q') :
    List (Q' × Z4Plaq) :=
  qs.map (fun p => (c p, timeShiftPlaquette ((width+1)+t) p))

private theorem singleton_product (C : Z4Plaq → Nat → RatPoly) (p : Z4Plaq) :
    RatPolyCoeffEqv (product C [(p, [(1, 1)])]) (C p 1) :=
  ((((RatPolyCoeffEqv.one_smul (C p 1)).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero (C p 1))).mul (RatPolyCoeffEqv.refl polyOne)).trans
      (RatPolyCoeffEqv.mul_one _)

private theorem single_placed (extent time : Nat) (p : Z4Plaq) :
    RatPolyCoeffEqv
      (sweptProduct extent 0
        (placeWindowProbes time [(0, [(p, [(1, 1)])])]))
      (BF4ExactSlabSelectedStarVariance.faceCharacter extent
        (timeShiftPlaquette time p)) := by
  rw [swept_zero]
  exact singleton_product
    (fun f spin => characterPolynomial
      (correctedSlabPlaquettePolynomial extent f).scalar spin)
    (timeShiftPlaquette time p)

/-- Placing the radius-zero presentation gives exactly the boundary-dual
signed face span. -/
theorem placedSpan_family (extent time : Nat) (qs : List Z4Plaq)
    (c : Z4Plaq → Q') :
    RatPolyCoeffEqv (placedSpan extent time (familyPresentation qs c))
      (BF4ExactSlabPlaquetteBoundaryDualPairing.faceSpan extent
        (qs.map (fun p => (c p, timeShiftPlaquette time p)))) := by
  induction qs with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons p qs ih =>
      change RatPolyCoeffEqv
        (polyAdd (polySmul (c p)
          (sweptProduct extent 0
            (placeWindowProbes time [(0, [(p, [(1, 1)])])])))
          (placedSpan extent time (familyPresentation qs c)))
        (polyAdd (polySmul (c p)
          (BF4ExactSlabSelectedStarVariance.faceCharacter extent
            (timeShiftPlaquette time p)))
          (BF4ExactSlabPlaquetteBoundaryDualPairing.faceSpan extent
            (qs.map (fun p => (c p, timeShiftPlaquette time p)))))
      exact ((single_placed extent time p).smul (c p)).add ih

private theorem singleton_sum (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul 1 p) polyZero) p :=
  ((RatPolyCoeffEqv.one_smul p).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero p)

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

private theorem encodeChart_zero (qs : List Z4Plaq) (c : Z4Plaq → Q') :
    encodeChart 0 (familyPresentation qs c) = familyPresentation qs c := by
  simp [encodeChart, familyPresentation,
    BF4ExactSlabFixedSpatialIntrinsicReflectedForm.encodeSchedule]

private theorem mirrorSpan_zero (qs : List Z4Plaq) (c : Z4Plaq → Q') :
    mirrorSpan 0 (familyPresentation qs c) = familyPresentation qs c := by
  simp [mirrorSpan, familyPresentation,
    BF4ExactSlabFixedSpatialWindowReflection.mirrorSchedule]

/-- The common-chart first moment is the literal selected-action finite value
of the placed signed family. -/
theorem chartScalar_mean_finiteValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) (stage t : Nat) :
    chartScalar hw0 hw1 width stage 0 (familySpan width qs c hqs) (unit width) t ≈
      finiteValue w hw0 hw1 (adjacentEvenExtent (width+t))
        (chainIds (adjacentEvenExtent (width+t)) width (width+1) (t+t))
        (fun _ hi => chainIds_physical hi)
        (BF4ExactSlabPlaquetteBoundaryDualPairing.faceSpan
          (adjacentEvenExtent (width+t)) (placedTerms width t qs c)) stage := by
  unfold chartScalar
  simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add]
  simp only [familySpan]
  rw [encodeChart_zero, mirrorSpan_zero]
  apply finite_congr hw0 hw1 _ _ _ stage
  change RatPolyCoeffEqv
    (polyMul
      (placedSpan (adjacentEvenExtent (width+t)) ((width+1)+t)
        (familyPresentation qs c))
      (placedSpan (adjacentEvenExtent (width+t)) ((width+1)+t) unitSpan)) _
  exact ((placedSpan_family _ _ qs c).mul (placedSpan_unit _ _)).trans
    (RatPolyCoeffEqv.mul_one _)

/-- At radius zero reflection fixes the family, so the diagonal chart moment
is the literal square with the same selected action and partition. -/
theorem chartScalar_square_finiteValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) (stage t : Nat) :
    chartScalar hw0 hw1 width stage 0
        (familySpan width qs c hqs) (familySpan width qs c hqs) t ≈
      finiteValue w hw0 hw1 (adjacentEvenExtent (width+t))
        (chainIds (adjacentEvenExtent (width+t)) width (width+1) (t+t))
        (fun _ hi => chainIds_physical hi)
        (polyMul
          (BF4ExactSlabPlaquetteBoundaryDualPairing.faceSpan
            (adjacentEvenExtent (width+t)) (placedTerms width t qs c))
          (BF4ExactSlabPlaquetteBoundaryDualPairing.faceSpan
            (adjacentEvenExtent (width+t)) (placedTerms width t qs c))) stage := by
  unfold chartScalar
  simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add]
  simp only [familySpan]
  rw [encodeChart_zero, mirrorSpan_zero]
  apply finite_congr hw0 hw1 _ _ _ stage
  exact (placedSpan_family _ _ qs c).mul (placedSpan_family _ _ qs c)

#print axioms familyPresentation_physical
#print axioms familySpan_radius
#print axioms placedSpan_family
#print axioms chartScalar_mean_finiteValue
#print axioms chartScalar_square_finiteValue

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamily
