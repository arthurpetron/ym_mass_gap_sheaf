/-
# Relative angular bound for ORIGINAL unweighted heat prefixes

The positive Jacobi product supplies a relative derivative estimate. Explicit
value and derivative deficit cutoffs remove its finite weights. The existing
one-factor heat floor absorbs the two errors, so it enters the late-cutoff
modulus but not the final relative derivative constant.

Every strict nome is quantified. The explicit constant is nome-dependent;
no near-one-nome energy estimate or physical mass calibration is claimed.
-/

import YMGap.Continuum.JacobiHeatRelativeAngularBound
import YMGap.Continuum.QuaternionHaarHeatAngularDeficit

namespace YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
open YMGap.Continuum.JacobiHeatRelativeAngularBound (relativeCost weightedHeatBound)

/-- No global heat-floor reciprocal occurs in this constant. -/
def relativeCap (w d : Q') : Q' := relativeCost w d + 1

/-- The original positive floor controls only the required precision. -/
def errorTolerance (w d : Q') : Q' := HKConv.divPos (headFloor w) (relativeCap w d)

def relativeCutoff (w d : Q') : Nat :=
  headCutoff w + BF4ExactSlabJacobiDeficitInterval.deficitCutoff w (errorTolerance w d) +
    QuaternionHaarHeatAngularDeficit.deficitCutoff w d (errorTolerance w d)

theorem relativeCap_positive {w d : Q'} (hw0 : (0 : Q') < w) (hd : (0 : Q') ≤ d) :
    (0 : Q') < relativeCap w d :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg 1 _
        (Q'.mul_nonneg _ _ hd (JacobiShiftedRelativeSlope.budget_nonnegative hw0)))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

theorem errorTolerance_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (d : Q') : (0 : Q') < errorTolerance w d :=
  HKConv.divPos_pos (CReal.num_pos_of_pos (headFloor_positive hw0 hw1))

theorem error_budget {w d : Q'} (hw0 : (0 : Q') < w) (hd : (0 : Q') ≤ d) :
    Q'.eqv (relativeCost w d * errorTolerance w d + errorTolerance w d) (headFloor w) :=
  Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.mul (.var 0) (.var 1)) (.var 1))
      (.mul (.var 1) (.add (.var 0) (.const 1))) (by decide)
      (fun | 0 => relativeCost w d | _ => errorTolerance w d))
    (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (relativeCap_positive hw0 hd)))

theorem headCutoff_le_relativeCutoff (w d : Q') : headCutoff w ≤ relativeCutoff w d := by
  unfold relativeCutoff
  omega

/-- SAME original unweighted prefix, at every sufficiently late cutoff,
with one relative angular constant independent of the carrier and cutoff.
The supplied scalar derivative cap and nome remain explicit parameters. -/
def heatPrefixRelativeBoundAt {blocks i j : Nat} {p : PolyQuaternion} {w d : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (hp : Supported blocks p) (hu : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne)
    (DX : Interval blocks (angularDerivative i j p.scalar) d)
    (K : Nat) (hK : relativeCutoff w d ≤ K) :
    RelativeBound blocks i j (heatPrefix w K p.scalar) (relativeCap w d) := by
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w d) hK
  have hv : BF4ExactSlabJacobiDeficitInterval.deficitCutoff w (errorTolerance w d) ≤ K+1 := by
    unfold relativeCutoff at hK
    omega
  have hd : QuaternionHaarHeatAngularDeficit.deficitCutoff w d (errorTolerance w d) ≤ K+1 := by
    unfold relativeCutoff at hK
    omega
  let F := weightedHeatBound hw0 hw1 hi hj hp hu DX (K+1)
  let E := deficitInterval hw0 hw1 (SquareBound.scalar hp hu) (errorTolerance w d)
    (errorTolerance_positive hw0 hw1 d) (K+1) hv
  let DE := QuaternionHaarHeatAngularDeficit.angularDeficitInterval hi hj hw0 hw1
    (SquareBound.scalar hp hu) DX (errorTolerance_positive hw0 hw1 d) (K+1) hd
  have floor : Certificate blocks (polyAdd (heatPrefix w K p.scalar)
      (polyNeg (cap (relativeCost w d * errorTolerance w d + errorTolerance w d)))) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg
      (RatPolyCoeffEqv.smul_coefficient (error_budget hw0 DX.nonnegative) polyOne)))
      (prefixFloorCertificate hw0 hw1 hp hu K hhead)
  exact RelativeBound.ofApproximation (prefixCertificate hw0 hw1 hp hu K hhead)
    (prefix_eq_weighted_add_deficit w K p.scalar) F E DE floor

end YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound

#print axioms YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound.relativeCap
#print axioms YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound.errorTolerance
#print axioms YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound.relativeCutoff
#print axioms YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound.relativeCap_positive
#print axioms YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound.errorTolerance_positive
#print axioms YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound.error_budget
#print axioms YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound.headCutoff_le_relativeCutoff
#print axioms YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound.heatPrefixRelativeBoundAt
