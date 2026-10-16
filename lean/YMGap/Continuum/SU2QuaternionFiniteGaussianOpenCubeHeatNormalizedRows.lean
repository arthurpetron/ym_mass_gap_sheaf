/-
# Heat-normalized open-cube rows and complete quadratic action

The finite heat Gaussian uses covariance `(2L)^{-1}`, where `L` is the
complete spatial-curl plus temporal-difference quadratic matrix.  This leaf
rebuilds the literal directed link and plaquette rows, the weighted bulk
source, and the complete spatial-plus-kinetic quadratic action with the
heat-normalized Heron transform.

The exact Cayley and kinetic coefficient identities are then re-run on these
rows, proving that the complete quadratic part of the fourth heat-action
coefficient remains `-(2/3) S0`.  This replaces no ORIGINAL-law object and
does not yet rebuild the complete OWN/OLD response, bound the finite Heron
residual, prove a neighboring-time sign, or establish a continuum theory or
physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatAction

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant

local infix:50 " ≈ " => Q'.eqv

/-- Three-color heat-normalized row of one directed gauge-fixed link. -/
def combGaugeHeatFreeHistoryHeronDirectedLinkRows
    (timeBonds width stage time : Nat) (sign : Q') (link : Z4Link)
    (component coordinate : Nat) : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  sign *
    threeColorRows coordinateCount
      (pulledRow coordinateCount
        (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
        (combGaugeFreeHistoryLinkRow width time link))
      component coordinate

/-- Four heat-normalized directed link triples in plaquette word order. -/
def combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    Nat → Nat → Nat → Q'
  | 0 => combGaugeHeatFreeHistoryHeronDirectedLinkRows
      timeBonds width stage time 1 (faceLinkA face)
  | 1 => combGaugeHeatFreeHistoryHeronDirectedLinkRows
      timeBonds width stage time 1 (faceLinkB face)
  | 2 => combGaugeHeatFreeHistoryHeronDirectedLinkRows
      timeBonds width stage time (-1) (faceLinkC face)
  | _ => combGaugeHeatFreeHistoryHeronDirectedLinkRows
      timeBonds width stage time (-1) (faceLinkD face)

/-- Heat-normalized three-color curl row for the explicit bulk source. -/
def bulkSourceHeatHeronColorCurlRow
    (timeBonds s stage time rowIndex coordinate : Nat) : Q' :=
  combGaugeHeatFreeHistoryHeronColorCurlRow
    timeBonds (bulkSourceWidth s) stage
    (fun _ => time) (bulkSourceInternalFaceIndex s) rowIndex coordinate

/-- Heat-normalized weighted bulk-source quadratic at one history time. -/
def bulkSourceHeatHeronRadialSquare
    (timeBonds s : Nat) (sidePositive : 0 < s)
    (stage time : Nat) : RatPoly :=
  combGaugeHeatFreeHistoryHeronWeightedCurlRadialSquare
    timeBonds (bulkSourceWidth s) stage (bulkSourceFaces s).length
    (bulkSourceIndexWeight s sidePositive) (fun _ => time)
    (bulkSourceInternalFaceIndex s)

/-- Heat-normalized trace-deficit quadratic coefficient `A2=4|B|^2`. -/
def openCubeHeatBulkCayleyTraceA2
    (timeBonds s : Nat) (sidePositive : 0 < s)
    (stage time : Nat) : RatPoly :=
  polySmul 4
    (bulkSourceHeatHeronRadialSquare
      timeBonds s sidePositive stage time)

/-- Positive heat-normalized spatial action `F2/4=|B|^2` on one face. -/
def openCubeHeatPlaquetteGaussianActionPolynomial
    (timeBonds width stage time : Nat) (face : Z4Plaq) : RatPoly :=
  let rows := combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianRowDot
    (combGaugePlaquetteNoiseCount timeBonds width) 3
    (gaussianCayleyTotalRows
      (gaussianCayleySlot (rows 0) (rows 1) (rows 2) (rows 3)))
    (gaussianCayleyTotalRows
      (gaussianCayleySlot (rows 0) (rows 1) (rows 2) (rows 3)))

/-- Literal heat-normalized spatial `-F2/6` coefficient on one face. -/
def openCubeHeatPlaquetteSpatialActionQuadraticPolynomial
    (timeBonds width stage time : Nat) (face : Z4Plaq) : RatPoly :=
  let rows := combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianCayleyH2ActionPolynomial
    (combGaugePlaquetteNoiseCount timeBonds width)
    (rows 0) (rows 1) (rows 2) (rows 3)

theorem openCubeHeatPlaquetteSpatialActionQuadratic_coeffEqv
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (openCubeHeatPlaquetteSpatialActionQuadraticPolynomial
        timeBonds width stage time face)
      (polySmul spatialHeatNegTwoThird
        (openCubeHeatPlaquetteGaussianActionPolynomial
          timeBonds width stage time face)) := by
  unfold openCubeHeatPlaquetteSpatialActionQuadraticPolynomial
    openCubeHeatPlaquetteGaussianActionPolynomial
  exact (finiteGaussianCayleyH2ActionPolynomial_coeffEqv
    (combGaugePlaquetteNoiseCount timeBonds width)
    ((combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage time face) 0)
    ((combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage time face) 1)
    ((combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage time face) 2)
    ((combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage time face) 3)).symm

/-- Heat-normalized three-color rows of one comb-gauge link on one slice. -/
def combGaugeHeatFreeHistoryHeronKineticSliceRows
    (timeBonds width stage time : Nat) (link : Z4Link) :
    Nat → Nat → Q' :=
  combGaugeHeatFreeHistoryHeronDirectedLinkRows
    timeBonds width stage time 1 link

/-- Heat-normalized forward-difference rows on one temporal bond. -/
def combGaugeHeatFreeHistoryHeronKineticDifferenceRows
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    Nat → Nat → Q' :=
  finiteGaussianKineticDifferenceRows
    (combGaugeHeatFreeHistoryHeronKineticSliceRows
      timeBonds width stage bond link)
    (combGaugeHeatFreeHistoryHeronKineticSliceRows
      timeBonds width stage (bond + 1) link)

/-- Positive heat-normalized temporal action on one bond/link. -/
def openCubeHeatKineticGaussianActionPolynomial
    (timeBonds width stage bond : Nat) (link : Z4Link) : RatPoly :=
  finiteGaussianRowDot
    (combGaugePlaquetteNoiseCount timeBonds width) 3
    (combGaugeHeatFreeHistoryHeronKineticDifferenceRows
      timeBonds width stage bond link)
    (combGaugeHeatFreeHistoryHeronKineticDifferenceRows
      timeBonds width stage bond link)

/-- Literal heat-normalized kinetic quadratic fourth-action coefficient. -/
def openCubeHeatKineticActionQuadraticPolynomial
    (timeBonds width stage bond : Nat) (link : Z4Link) : RatPoly :=
  finiteGaussianKineticFourthActionQuadraticPolynomial
    (combGaugePlaquetteNoiseCount timeBonds width)
    (combGaugeHeatFreeHistoryHeronKineticSliceRows
      timeBonds width stage bond link)
    (combGaugeHeatFreeHistoryHeronKineticSliceRows
      timeBonds width stage (bond + 1) link)

theorem openCubeHeatKineticActionQuadratic_coeffEqv
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    RatPolyCoeffEqv
      (openCubeHeatKineticActionQuadraticPolynomial
        timeBonds width stage bond link)
      (polySmul spatialHeatNegTwoThird
        (openCubeHeatKineticGaussianActionPolynomial
          timeBonds width stage bond link)) := by
  unfold openCubeHeatKineticActionQuadraticPolynomial
    openCubeHeatKineticGaussianActionPolynomial
    combGaugeHeatFreeHistoryHeronKineticDifferenceRows
  exact (finiteGaussianKineticFourthActionQuadraticPolynomial_coeffEqv
    (combGaugePlaquetteNoiseCount timeBonds width)
    (combGaugeHeatFreeHistoryHeronKineticSliceRows
      timeBonds width stage bond link)
    (combGaugeHeatFreeHistoryHeronKineticSliceRows
      timeBonds width stage (bond + 1) link)).symm

/-- Complete heat-normalized positive spatial quadratic action. -/
def completeOpenCubeHeatSpatialGaussianActionPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polySum ((completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds width).map fun insertion =>
      polySmul insertion.weight
        (openCubeHeatPlaquetteGaussianActionPolynomial
          timeBonds width stage insertion.time insertion.face))

/-- Complete heat-normalized literal spatial quadratic fourth-action part. -/
def completeOpenCubeHeatSpatialActionQuadraticPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polySum ((completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds width).map fun insertion =>
      polySmul insertion.weight
        (openCubeHeatPlaquetteSpatialActionQuadraticPolynomial
          timeBonds width stage insertion.time insertion.face))

/-- Complete heat-normalized positive kinetic quadratic action. -/
def completeOpenCubeHeatKineticGaussianActionPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polySum ((completeOpenCubeKineticFourthActionInsertions
    timeBonds width).map fun insertion =>
      polySmul insertion.weight
        (openCubeHeatKineticGaussianActionPolynomial
          timeBonds width stage insertion.bond insertion.link))

/-- Complete heat-normalized literal kinetic quadratic fourth-action part. -/
def completeOpenCubeHeatKineticActionQuadraticPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polySum ((completeOpenCubeKineticFourthActionInsertions
    timeBonds width).map fun insertion =>
      polySmul insertion.weight
        (openCubeHeatKineticActionQuadraticPolynomial
          timeBonds width stage insertion.bond insertion.link))

/-- Complete heat-normalized positive FREE action `S0`. -/
def completeOpenCubeHeatGaussianActionPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polyAdd
    (completeOpenCubeHeatSpatialGaussianActionPolynomial
      timeBonds width stage)
    (completeOpenCubeHeatKineticGaussianActionPolynomial
      timeBonds width stage)

/-- Complete heat-normalized quadratic part of spatial plus kinetic `V4`. -/
def completeOpenCubeHeatActionQuadraticPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polyAdd
    (completeOpenCubeHeatSpatialActionQuadraticPolynomial
      timeBonds width stage)
    (completeOpenCubeHeatKineticActionQuadraticPolynomial
      timeBonds width stage)

private theorem polySmul_polySum (scale : Q') : ∀ polynomials : List RatPoly,
    RatPolyCoeffEqv
      (polySmul scale (polySum polynomials))
      (polySum (polynomials.map (polySmul scale)))
  | [] => RatPolyCoeffEqv.zero_smul polyZero
  | polynomial :: polynomials =>
      (RatPolyCoeffEqv.smul_add scale polynomial (polySum polynomials)).trans
        ((RatPolyCoeffEqv.refl _).add
          (polySmul_polySum scale polynomials))

private theorem polySum_congr {Index : Type}
    (left right : Index → RatPoly) : ∀ items : List Index,
    (∀ item, item ∈ items → RatPolyCoeffEqv (left item) (right item)) →
    RatPolyCoeffEqv (polySum (items.map left)) (polySum (items.map right))
  | [], _ => RatPolyCoeffEqv.refl _
  | item :: items, hypothesis =>
      (hypothesis item List.mem_cons_self).add
        (polySum_congr left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

private theorem weighted_scaled_term
    (weight scale : Q') {actual base : RatPoly}
    (hypothesis : RatPolyCoeffEqv actual (polySmul scale base)) :
    RatPolyCoeffEqv
      (polySmul weight actual)
      (polySmul scale (polySmul weight base)) := by
  exact (hypothesis.smul weight).trans
    ((RatPolyCoeffEqv.smul_assoc weight scale base).trans
      ((RatPolyCoeffEqv.smul_coefficient
          (Q'.mul_comm_eqv weight scale) base).trans
        (RatPolyCoeffEqv.smul_assoc scale weight base).symm))

theorem completeOpenCubeHeatSpatialActionQuadratic_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeHeatSpatialActionQuadraticPolynomial
        timeBonds width stage)
      (polySmul spatialHeatNegTwoThird
        (completeOpenCubeHeatSpatialGaussianActionPolynomial
          timeBonds width stage)) := by
  let insertions := completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds width
  let actual := fun insertion : OpenCubeSpatialHeatActionFourthInsertion =>
    polySmul insertion.weight
      (openCubeHeatPlaquetteSpatialActionQuadraticPolynomial
        timeBonds width stage insertion.time insertion.face)
  let base := fun insertion : OpenCubeSpatialHeatActionFourthInsertion =>
    polySmul insertion.weight
      (openCubeHeatPlaquetteGaussianActionPolynomial
        timeBonds width stage insertion.time insertion.face)
  have hterms : RatPolyCoeffEqv
      (polySum (insertions.map actual))
      (polySum (insertions.map fun insertion =>
        polySmul spatialHeatNegTwoThird (base insertion))) :=
    polySum_congr actual
      (fun insertion => polySmul spatialHeatNegTwoThird (base insertion))
      insertions (fun insertion _ =>
        weighted_scaled_term insertion.weight spatialHeatNegTwoThird
          (openCubeHeatPlaquetteSpatialActionQuadratic_coeffEqv
            timeBonds width stage insertion.time insertion.face))
  have hfactor : RatPolyCoeffEqv
      (polySmul spatialHeatNegTwoThird (polySum (insertions.map base)))
      (polySum (insertions.map fun insertion =>
        polySmul spatialHeatNegTwoThird (base insertion))) := by
    simpa only [List.map_map, Function.comp_apply] using
      polySmul_polySum spatialHeatNegTwoThird (insertions.map base)
  unfold completeOpenCubeHeatSpatialActionQuadraticPolynomial
    completeOpenCubeHeatSpatialGaussianActionPolynomial
  exact hterms.trans hfactor.symm

theorem completeOpenCubeHeatKineticActionQuadratic_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeHeatKineticActionQuadraticPolynomial
        timeBonds width stage)
      (polySmul spatialHeatNegTwoThird
        (completeOpenCubeHeatKineticGaussianActionPolynomial
          timeBonds width stage)) := by
  let insertions := completeOpenCubeKineticFourthActionInsertions
    timeBonds width
  let actual := fun insertion : OpenCubeKineticFourthActionInsertion =>
    polySmul insertion.weight
      (openCubeHeatKineticActionQuadraticPolynomial
        timeBonds width stage insertion.bond insertion.link)
  let base := fun insertion : OpenCubeKineticFourthActionInsertion =>
    polySmul insertion.weight
      (openCubeHeatKineticGaussianActionPolynomial
        timeBonds width stage insertion.bond insertion.link)
  have hterms : RatPolyCoeffEqv
      (polySum (insertions.map actual))
      (polySum (insertions.map fun insertion =>
        polySmul spatialHeatNegTwoThird (base insertion))) :=
    polySum_congr actual
      (fun insertion => polySmul spatialHeatNegTwoThird (base insertion))
      insertions (fun insertion _ =>
        weighted_scaled_term insertion.weight spatialHeatNegTwoThird
          (openCubeHeatKineticActionQuadratic_coeffEqv
            timeBonds width stage insertion.bond insertion.link))
  have hfactor : RatPolyCoeffEqv
      (polySmul spatialHeatNegTwoThird (polySum (insertions.map base)))
      (polySum (insertions.map fun insertion =>
        polySmul spatialHeatNegTwoThird (base insertion))) := by
    simpa only [List.map_map, Function.comp_apply] using
      polySmul_polySum spatialHeatNegTwoThird (insertions.map base)
  unfold completeOpenCubeHeatKineticActionQuadraticPolynomial
    completeOpenCubeHeatKineticGaussianActionPolynomial
  exact hterms.trans hfactor.symm

/-- The actual complete heat-normalized quadratic fourth-action coefficient
is exactly `-(2/3) S0`. -/
theorem completeOpenCubeHeatActionQuadratic_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeHeatActionQuadraticPolynomial
        timeBonds width stage)
      (polySmul spatialHeatNegTwoThird
        (completeOpenCubeHeatGaussianActionPolynomial
          timeBonds width stage)) := by
  unfold completeOpenCubeHeatActionQuadraticPolynomial
    completeOpenCubeHeatGaussianActionPolynomial
  exact (completeOpenCubeHeatSpatialActionQuadratic_coeffEqv
      timeBonds width stage).add
        (completeOpenCubeHeatKineticActionQuadratic_coeffEqv
          timeBonds width stage) |>.trans
    (RatPolyCoeffEqv.smul_add spatialHeatNegTwoThird
      (completeOpenCubeHeatSpatialGaussianActionPolynomial
        timeBonds width stage)
      (completeOpenCubeHeatKineticGaussianActionPolynomial
        timeBonds width stage)).symm

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows.bulkSourceHeatHeronRadialSquare
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows.openCubeHeatBulkCayleyTraceA2
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows.openCubeHeatPlaquetteSpatialActionQuadratic_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows.openCubeHeatKineticActionQuadratic_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows.completeOpenCubeHeatActionQuadratic_coeffEqv
