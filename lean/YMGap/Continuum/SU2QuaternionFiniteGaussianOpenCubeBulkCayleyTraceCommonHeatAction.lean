/-
# Common quadratic heat action and the exact P6 scaling residual

The quadratic part of every spatial and kinetic fourth heat-action insertion
has the universal coefficient `-2/3` multiplying the complete pulled-back
FREE quadratic action.  This leaf identifies that statement on the literal
open-cube Heron carrier, including every terminal spatial slice and every
temporal bond.

The carrier imported here factors `L^{-1}` for the unscaled precision `L`.
The standard product Gaussian has covariance one, whereas the heat density
`exp(-S0)` requires covariance `(2L)^{-1}`.  Thus this module is now retained
as an exact normalization diagnostic on the older inverse-of-`L` branch; its
scaling residual is not merely a finite-Heron approximation error.  The
complete OLD-centered `P6` contribution of the density term
`-V4_quadratic` is split exactly into

  * the universal `(4/3) * P4` term,
  * the fixed-OLD-center residual from the audited formula, and
  * an explicit connected/one-point Gaussian-action scaling residual.

The universal term cancels in every denominator-cleared comparison on this
literal carrier.  The corrected heat covariance and Heron transform are
constructed separately in
`SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite`.
This file does not prove a physical heat-law cancellation, neighboring-scale
sign, ORIGINAL-law comparison, higher-remainder estimate, continuum
Hamiltonian, or physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanCompleteWick

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanCompleteWick

local infix:50 " ≈ " => Q'.eqv

/-- Positive density coefficient `2/3 = -(-2/3)`. -/
def heatActionTwoThird : Q' := Q'.mkPos 2 3 (by decide)

/-- The universal response coefficient `4/3 = 2*(2/3)`. -/
def heatActionFourThird : Q' := 2 * heatActionTwoThird

theorem heatActionTwoThird_eq_neg_spatialHeatNegTwoThird :
    heatActionTwoThird ≈ -spatialHeatNegTwoThird := by
  decide

theorem heatActionFourThird_eq_four_thirds :
    heatActionFourThird ≈ Q'.mkPos 4 3 (by decide) := by
  unfold heatActionFourThird heatActionTwoThird
  decide

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem polySum_congr {Index : Type}
    (left right : Index → RatPoly) : ∀ items : List Index,
    (∀ item, item ∈ items → RatPolyCoeffEqv (left item) (right item)) →
      RatPolyCoeffEqv
        (polySum (items.map left))
        (polySum (items.map right))
  | [], _ => RatPolyCoeffEqv.refl _
  | item :: items, hypothesis =>
      (hypothesis item List.mem_cons_self).add
        (polySum_congr left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

private theorem polySmul_polySum (scale : Q') : ∀ polynomials : List RatPoly,
    RatPolyCoeffEqv
      (polySmul scale (polySum polynomials))
      (polySum (polynomials.map (polySmul scale)))
  | [] => RatPolyCoeffEqv.zero_smul polyZero
  | polynomial :: polynomials =>
      (RatPolyCoeffEqv.smul_add scale polynomial (polySum polynomials)).trans
        ((RatPolyCoeffEqv.refl _).add
          (polySmul_polySum scale polynomials))

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

/-- Positive quadratic action `F2/4 = |B|^2` on one spatial plaquette after
the actual comb-gauge Heron pullback. -/
def openCubePlaquetteGaussianActionPolynomial
    (timeBonds width stage time : Nat) (face : Z4Plaq) : RatPoly :=
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianRowDot
    (combGaugePlaquetteNoiseCount timeBonds width) 3
    (gaussianCayleyTotalRows
      (gaussianCayleySlot (rows 0) (rows 1) (rows 2) (rows 3)))
    (gaussianCayleyTotalRows
      (gaussianCayleySlot (rows 0) (rows 1) (rows 2) (rows 3)))

/-- Literal quadratic `-F2/6` part of one spatial fourth heat-action
coefficient. -/
def openCubePlaquetteSpatialHeatActionQuadraticPolynomial
    (timeBonds width stage time : Nat) (face : Z4Plaq) : RatPoly :=
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianCayleyH2ActionPolynomial
    (combGaugePlaquetteNoiseCount timeBonds width)
    (rows 0) (rows 1) (rows 2) (rows 3)

theorem openCubePlaquetteSpatialHeatActionQuadratic_coeffEqv
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (openCubePlaquetteSpatialHeatActionQuadraticPolynomial
        timeBonds width stage time face)
      (polySmul spatialHeatNegTwoThird
        (openCubePlaquetteGaussianActionPolynomial
          timeBonds width stage time face)) := by
  unfold openCubePlaquetteSpatialHeatActionQuadraticPolynomial
    openCubePlaquetteGaussianActionPolynomial
  exact (finiteGaussianCayleyH2ActionPolynomial_coeffEqv
    (combGaugePlaquetteNoiseCount timeBonds width)
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage time face) 0)
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage time face) 1)
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage time face) 2)
    ((combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds width stage time face) 3)).symm

/-- Positive quadratic action `|a_(t+1)-a_t|^2` on one temporal bond and
comb-gauge link after the actual Heron pullback. -/
def openCubeKineticGaussianActionPolynomial
    (timeBonds width stage bond : Nat) (link : Z4Link) : RatPoly :=
  let difference := combGaugeFreeHistoryHeronKineticDifferenceRows
    timeBonds width stage bond link
  finiteGaussianRowDot
    (combGaugePlaquetteNoiseCount timeBonds width) 3 difference difference

/-- Literal quadratic `-2|a_(t+1)-a_t|^2/3` part of one kinetic fourth
heat-action coefficient. -/
def openCubeKineticHeatActionQuadraticPolynomial
    (timeBonds width stage bond : Nat) (link : Z4Link) : RatPoly :=
  finiteGaussianKineticFourthActionQuadraticPolynomial
    (combGaugePlaquetteNoiseCount timeBonds width)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage bond link)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage (bond + 1) link)

theorem openCubeKineticHeatActionQuadratic_coeffEqv
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    RatPolyCoeffEqv
      (openCubeKineticHeatActionQuadraticPolynomial
        timeBonds width stage bond link)
      (polySmul spatialHeatNegTwoThird
        (openCubeKineticGaussianActionPolynomial
          timeBonds width stage bond link)) := by
  unfold openCubeKineticHeatActionQuadraticPolynomial
    openCubeKineticGaussianActionPolynomial
    combGaugeFreeHistoryHeronKineticDifferenceRows
  exact (finiteGaussianKineticFourthActionQuadraticPolynomial_coeffEqv
    (combGaugePlaquetteNoiseCount timeBonds width)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage bond link)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage (bond + 1) link)).symm

/-- Every spatial `F2/4` action term, including both terminal slices. -/
def completeOpenCubeSpatialGaussianActionPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polySum ((completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds width).map fun insertion =>
      polySmul insertion.weight
        (openCubePlaquetteGaussianActionPolynomial
          timeBonds width stage insertion.time insertion.face))

/-- Every literal spatial quadratic fourth-action term `-F2/6`. -/
def completeOpenCubeSpatialHeatActionQuadraticPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polySum ((completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds width).map fun insertion =>
      polySmul insertion.weight
        (openCubePlaquetteSpatialHeatActionQuadraticPolynomial
          timeBonds width stage insertion.time insertion.face))

theorem completeOpenCubeSpatialHeatActionQuadratic_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeSpatialHeatActionQuadraticPolynomial
        timeBonds width stage)
      (polySmul spatialHeatNegTwoThird
        (completeOpenCubeSpatialGaussianActionPolynomial
          timeBonds width stage)) := by
  let insertions := completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds width
  let actual := fun insertion : OpenCubeSpatialHeatActionFourthInsertion =>
    polySmul insertion.weight
      (openCubePlaquetteSpatialHeatActionQuadraticPolynomial
        timeBonds width stage insertion.time insertion.face)
  let base := fun insertion : OpenCubeSpatialHeatActionFourthInsertion =>
    polySmul insertion.weight
      (openCubePlaquetteGaussianActionPolynomial
        timeBonds width stage insertion.time insertion.face)
  have hterms : RatPolyCoeffEqv
      (polySum (insertions.map actual))
      (polySum (insertions.map fun insertion =>
        polySmul spatialHeatNegTwoThird (base insertion))) :=
    polySum_congr actual
      (fun insertion => polySmul spatialHeatNegTwoThird (base insertion))
      insertions (fun insertion _ =>
        weighted_scaled_term insertion.weight spatialHeatNegTwoThird
          (openCubePlaquetteSpatialHeatActionQuadratic_coeffEqv
            timeBonds width stage insertion.time insertion.face))
  have hfactor : RatPolyCoeffEqv
      (polySmul spatialHeatNegTwoThird (polySum (insertions.map base)))
      (polySum (insertions.map fun insertion =>
        polySmul spatialHeatNegTwoThird (base insertion))) := by
    simpa only [List.map_map, Function.comp_apply] using
      polySmul_polySum spatialHeatNegTwoThird (insertions.map base)
  unfold completeOpenCubeSpatialHeatActionQuadraticPolynomial
    completeOpenCubeSpatialGaussianActionPolynomial
  exact hterms.trans hfactor.symm

/-- Every positive temporal-bond quadratic action term. -/
def completeOpenCubeKineticGaussianActionPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polySum ((completeOpenCubeKineticFourthActionInsertions
    timeBonds width).map fun insertion =>
      polySmul insertion.weight
        (openCubeKineticGaussianActionPolynomial
          timeBonds width stage insertion.bond insertion.link))

/-- Every literal kinetic quadratic fourth-action term. -/
def completeOpenCubeKineticHeatActionQuadraticPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polySum ((completeOpenCubeKineticFourthActionInsertions
    timeBonds width).map fun insertion =>
      polySmul insertion.weight
        (openCubeKineticHeatActionQuadraticPolynomial
          timeBonds width stage insertion.bond insertion.link))

theorem completeOpenCubeKineticHeatActionQuadratic_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeKineticHeatActionQuadraticPolynomial
        timeBonds width stage)
      (polySmul spatialHeatNegTwoThird
        (completeOpenCubeKineticGaussianActionPolynomial
          timeBonds width stage)) := by
  let insertions := completeOpenCubeKineticFourthActionInsertions
    timeBonds width
  let actual := fun insertion : OpenCubeKineticFourthActionInsertion =>
    polySmul insertion.weight
      (openCubeKineticHeatActionQuadraticPolynomial
        timeBonds width stage insertion.bond insertion.link)
  let base := fun insertion : OpenCubeKineticFourthActionInsertion =>
    polySmul insertion.weight
      (openCubeKineticGaussianActionPolynomial
        timeBonds width stage insertion.bond insertion.link)
  have hterms : RatPolyCoeffEqv
      (polySum (insertions.map actual))
      (polySum (insertions.map fun insertion =>
        polySmul spatialHeatNegTwoThird (base insertion))) :=
    polySum_congr actual
      (fun insertion => polySmul spatialHeatNegTwoThird (base insertion))
      insertions (fun insertion _ =>
        weighted_scaled_term insertion.weight spatialHeatNegTwoThird
          (openCubeKineticHeatActionQuadratic_coeffEqv
            timeBonds width stage insertion.bond insertion.link))
  have hfactor : RatPolyCoeffEqv
      (polySmul spatialHeatNegTwoThird (polySum (insertions.map base)))
      (polySum (insertions.map fun insertion =>
        polySmul spatialHeatNegTwoThird (base insertion))) := by
    simpa only [List.map_map, Function.comp_apply] using
      polySmul_polySum spatialHeatNegTwoThird (insertions.map base)
  unfold completeOpenCubeKineticHeatActionQuadraticPolynomial
    completeOpenCubeKineticGaussianActionPolynomial
  exact hterms.trans hfactor.symm

/-- Complete pulled-back finite FREE quadratic action `S0`. -/
def completeOpenCubeGaussianActionPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polyAdd
    (completeOpenCubeSpatialGaussianActionPolynomial
      timeBonds width stage)
    (completeOpenCubeKineticGaussianActionPolynomial
      timeBonds width stage)

/-- Complete quadratic part of `V4_spatial + V4_kinetic`. -/
def completeOpenCubeHeatActionQuadraticPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polyAdd
    (completeOpenCubeSpatialHeatActionQuadraticPolynomial
      timeBonds width stage)
    (completeOpenCubeKineticHeatActionQuadraticPolynomial
      timeBonds width stage)

/-- Exact common-nome identity `V4_quadratic = -(2/3) S0` on the literal
finite open-cube Heron carrier. -/
theorem completeOpenCubeHeatActionQuadratic_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeHeatActionQuadraticPolynomial
        timeBonds width stage)
      (polySmul spatialHeatNegTwoThird
        (completeOpenCubeGaussianActionPolynomial
          timeBonds width stage)) := by
  unfold completeOpenCubeHeatActionQuadraticPolynomial
    completeOpenCubeGaussianActionPolynomial
  exact (completeOpenCubeSpatialHeatActionQuadratic_coeffEqv
      timeBonds width stage).add
        (completeOpenCubeKineticHeatActionQuadratic_coeffEqv
          timeBonds width stage) |>.trans
    (RatPolyCoeffEqv.smul_add spatialHeatNegTwoThird
      (completeOpenCubeSpatialGaussianActionPolynomial
        timeBonds width stage)
      (completeOpenCubeKineticGaussianActionPolynomial
        timeBonds width stage)).symm

/-- The density sign changes the complete quadratic action coefficient from
`-2/3` to `+2/3`. -/
theorem completeOpenCubeNegativeHeatActionQuadratic_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (polySmul (-1)
        (completeOpenCubeHeatActionQuadraticPolynomial
          timeBonds width stage))
      (polySmul heatActionTwoThird
        (completeOpenCubeGaussianActionPolynomial
          timeBonds width stage)) := by
  let action := completeOpenCubeGaussianActionPolynomial
    timeBonds width stage
  exact ((completeOpenCubeHeatActionQuadratic_coeffEqv
      timeBonds width stage).smul (-1)).trans
    ((RatPolyCoeffEqv.smul_assoc (-1) spatialHeatNegTwoThird action).trans
      (RatPolyCoeffEqv.smul_coefficient (by decide) action))

/-- Defect of the one-point quadratic Gaussian-action scaling identity
`Cov(A2,S0)=E[A2]` on the finite Heron carrier. -/
def openCubeBulkCayleyTraceHeatMeanScalingDefect
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  let N := bulkSourceNoiseCount timeBonds side
  let A2 := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage time
  let S0 := completeOpenCubeGaussianActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  finiteGaussianCovariance N A2 S0 -
    openCubeBulkCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage time

/-- Defect of the connected quadratic Gaussian-action scaling identity
`kappa(A2,B2,S0)=2*R4` on the finite Heron carrier. -/
def openCubeBulkCayleyTraceHeatConnectedScalingDefect
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  let N := bulkSourceNoiseCount timeBonds side
  let left := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage leftTime
  let right := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage rightTime
  let S0 := completeOpenCubeGaussianActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  finiteGaussianThirdCumulant N left right S0 -
    2 * openCubeBulkCayleyTraceConnectedR4
      timeBonds side sidePositive stage leftTime rightTime

/-- Complete scaling residual left after extracting the universal heat-action
piece from OLD-centered `P6`. -/
def openCubeBulkCayleyTraceHeatP6ScalingResidual
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  let leftMean := openCubeBulkCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage leftTime
  let rightMean := openCubeBulkCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage rightTime
  (openCubeBulkCayleyTraceHeatConnectedScalingDefect
      timeBonds side sidePositive stage leftTime rightTime +
    (leftMean - oldCenter.c2) *
      openCubeBulkCayleyTraceHeatMeanScalingDefect
        timeBonds side sidePositive stage rightTime) +
  openCubeBulkCayleyTraceHeatMeanScalingDefect
      timeBonds side sidePositive stage leftTime *
    (rightMean - oldCenter.c2)

/-- Literal additive contribution of the actual density polynomial
`-V4_quadratic` to the connected and two OWN-mean slots of `P6`. -/
def openCubeBulkCayleyTraceNegativeHeatQuadraticP6Contribution
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  let N := bulkSourceNoiseCount timeBonds side
  let left := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage leftTime
  let right := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage rightTime
  let densityQuadratic := polySmul (-1)
    (completeOpenCubeHeatActionQuadraticPolynomial
      timeBonds (bulkSourceWidth side) stage)
  let leftMean := openCubeBulkCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage leftTime
  let rightMean := openCubeBulkCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage rightTime
  (finiteGaussianThirdCumulant N left right densityQuadratic +
    (leftMean - oldCenter.c2) *
      finiteGaussianCovariance N right densityQuadratic) +
  finiteGaussianCovariance N left densityQuadratic *
    (rightMean - oldCenter.c2)

/-- The same contribution after replacing `-V4_quadratic` by the checked
`(2/3)S0` coefficient. -/
def openCubeBulkCayleyTraceGaussianActionP6Contribution
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  let N := bulkSourceNoiseCount timeBonds side
  let left := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage leftTime
  let right := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage rightTime
  let S0 := completeOpenCubeGaussianActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  let leftMean := openCubeBulkCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage leftTime
  let rightMean := openCubeBulkCayleyTraceOwnA2Mean
    timeBonds side sidePositive stage rightTime
  (heatActionTwoThird * finiteGaussianThirdCumulant N left right S0 +
    (leftMean - oldCenter.c2) *
      (heatActionTwoThird * finiteGaussianCovariance N right S0)) +
  (heatActionTwoThird * finiteGaussianCovariance N left S0) *
    (rightMean - oldCenter.c2)

theorem openCubeBulkCayleyTraceNegativeHeatQuadraticP6Contribution_action
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeBulkCayleyTraceNegativeHeatQuadraticP6Contribution
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeBulkCayleyTraceGaussianActionP6Contribution
        timeBonds side sidePositive stage leftTime rightTime oldCenter := by
  let N := bulkSourceNoiseCount timeBonds side
  let left := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage leftTime
  let right := openCubeBulkCayleyTraceA2
    timeBonds side sidePositive stage rightTime
  let densityQuadratic := polySmul (-1)
    (completeOpenCubeHeatActionQuadraticPolynomial
      timeBonds (bulkSourceWidth side) stage)
  let S0 := completeOpenCubeGaussianActionPolynomial
    timeBonds (bulkSourceWidth side) stage
  have hdensity : RatPolyCoeffEqv densityQuadratic
      (polySmul heatActionTwoThird S0) :=
    completeOpenCubeNegativeHeatActionQuadratic_coeffEqv
      timeBonds (bulkSourceWidth side) stage
  have hconnected : finiteGaussianThirdCumulant N left right densityQuadratic ≈
      heatActionTwoThird * finiteGaussianThirdCumulant N left right S0 :=
    Q'.eqv_trans _ _ _
      (finiteGaussianThirdCumulant_coeffEqv N
        (RatPolyCoeffEqv.refl left) (RatPolyCoeffEqv.refl right) hdensity)
      (finiteGaussianThirdCumulant_smul_right
        N heatActionTwoThird left right S0)
  have hleft : finiteGaussianCovariance N left densityQuadratic ≈
      heatActionTwoThird * finiteGaussianCovariance N left S0 :=
    Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_coeffEqv N
        (RatPolyCoeffEqv.refl left) hdensity)
      (finiteGaussianCovariance_smul_right
        N heatActionTwoThird left S0)
  have hright : finiteGaussianCovariance N right densityQuadratic ≈
      heatActionTwoThird * finiteGaussianCovariance N right S0 :=
    Q'.eqv_trans _ _ _
      (finiteGaussianCovariance_coeffEqv N
        (RatPolyCoeffEqv.refl right) hdensity)
      (finiteGaussianCovariance_smul_right
        N heatActionTwoThird right S0)
  unfold openCubeBulkCayleyTraceNegativeHeatQuadraticP6Contribution
    openCubeBulkCayleyTraceGaussianActionP6Contribution
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr' hconnected
      (Q'.mul_eqv_congr_left _ _ _ hright))
    (Q'.mul_eqv_congr_right _ _ _ hleft)

private theorem heatP6_decomposition_scalar
    (scale connected third leftMean rightMean leftAction rightAction old : Q') :
    ((scale * third +
          (leftMean - old) * (scale * rightAction)) +
        (scale * leftAction) * (rightMean - old)) ≈
      (((2 * scale) *
            (connected + (leftMean - old) * (rightMean - old)) +
          (scale * old) *
            ((leftMean - old) + (rightMean - old))) +
        scale *
          (((third - 2 * connected) +
              (leftMean - old) * (rightAction - rightMean)) +
            (leftAction - leftMean) * (rightMean - old))) := by
  let S : PolyExpr := .var 0
  let R : PolyExpr := .var 1
  let K : PolyExpr := .var 2
  let A : PolyExpr := .var 3
  let B : PolyExpr := .var 4
  let X : PolyExpr := .var 5
  let Y : PolyExpr := .var 6
  let C : PolyExpr := .var 7
  exact poly_identity_of_normal_eq
    (.add
      (.add (.mul S K)
        (.mul (.add A (.neg C)) (.mul S Y)))
      (.mul (.mul S X) (.add B (.neg C))))
    (.add
      (.add
        (.mul (.mul (.const 2) S)
          (.add R (.mul (.add A (.neg C)) (.add B (.neg C)))))
        (.mul (.mul S C)
          (.add (.add A (.neg C)) (.add B (.neg C)))))
      (.mul S
        (.add
          (.add
            (.add K (.neg (.mul (.const 2) R)))
            (.mul (.add A (.neg C)) (.add Y (.neg B))))
          (.mul (.add X (.neg A)) (.add B (.neg C))))))
    (by decide) (fun
      | 0 => scale
      | 1 => connected
      | 2 => third
      | 3 => leftMean
      | 4 => rightMean
      | 5 => leftAction
      | 6 => rightAction
      | _ => old)

/-- Exact finite common-action split for the actual `-V4_quadratic`
contribution to OLD-centered `P6`.  The first term is `(4/3)P4`; the second
is the retained fixed-OLD-center residue; the third is the honest Heron
scaling residual. -/
theorem openCubeBulkCayleyTraceNegativeHeatQuadraticP6Contribution_decomposition
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeBulkCayleyTraceNegativeHeatQuadraticP6Contribution
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      ((heatActionFourThird *
            openCubeBulkCayleyTraceP4
              timeBonds side sidePositive stage leftTime rightTime oldCenter +
          (heatActionTwoThird * oldCenter.c2) *
            ((openCubeBulkCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage leftTime - oldCenter.c2) +
              (openCubeBulkCayleyTraceOwnA2Mean
                timeBonds side sidePositive stage rightTime - oldCenter.c2))) +
        heatActionTwoThird *
          openCubeBulkCayleyTraceHeatP6ScalingResidual
            timeBonds side sidePositive stage leftTime rightTime oldCenter) := by
  refine Q'.eqv_trans _ _ _
    (openCubeBulkCayleyTraceNegativeHeatQuadraticP6Contribution_action
      timeBonds side sidePositive stage leftTime rightTime oldCenter) ?_
  unfold openCubeBulkCayleyTraceGaussianActionP6Contribution
    openCubeBulkCayleyTraceHeatP6ScalingResidual
    openCubeBulkCayleyTraceHeatConnectedScalingDefect
    openCubeBulkCayleyTraceHeatMeanScalingDefect
    openCubeBulkCayleyTraceP4 heatActionFourThird
  exact heatP6_decomposition_scalar
    heatActionTwoThird
    (openCubeBulkCayleyTraceConnectedR4
      timeBonds side sidePositive stage leftTime rightTime)
    (finiteGaussianThirdCumulant
      (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA2
        timeBonds side sidePositive stage leftTime)
      (openCubeBulkCayleyTraceA2
        timeBonds side sidePositive stage rightTime)
      (completeOpenCubeGaussianActionPolynomial
        timeBonds (bulkSourceWidth side) stage))
    (openCubeBulkCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage leftTime)
    (openCubeBulkCayleyTraceOwnA2Mean
      timeBonds side sidePositive stage rightTime)
    (finiteGaussianCovariance
      (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA2
        timeBonds side sidePositive stage leftTime)
      (completeOpenCubeGaussianActionPolynomial
        timeBonds (bulkSourceWidth side) stage))
    (finiteGaussianCovariance
      (bulkSourceNoiseCount timeBonds side)
      (openCubeBulkCayleyTraceA2
        timeBonds side sidePositive stage rightTime)
      (completeOpenCubeGaussianActionPolynomial
        timeBonds (bulkSourceWidth side) stage))
    oldCenter.c2

/-- The universal `(4/3)P4` heat-action piece cancels identically in a
denominator-cleared comparison of any two finite responses. -/
theorem openCubeBulkCayleyTraceCommonHeatP4_cleared_zero
    (first second : Q') :
    second * (heatActionFourThird * first) -
        first * (heatActionFourThird * second) ≈ 0 := by
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.var 1) (.mul (.var 2) (.var 0)))
      (.neg (.mul (.var 0) (.mul (.var 2) (.var 1)))))
    (.const 0) (by decide) (fun
      | 0 => first
      | 1 => second
      | _ => heatActionFourThird)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatAction

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatAction.completeOpenCubeHeatActionQuadratic_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatAction.completeOpenCubeNegativeHeatActionQuadratic_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatAction.openCubeBulkCayleyTraceNegativeHeatQuadraticP6Contribution_action
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatAction.openCubeBulkCayleyTraceNegativeHeatQuadraticP6Contribution_decomposition
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceCommonHeatAction.openCubeBulkCayleyTraceCommonHeatP4_cleared_zero
