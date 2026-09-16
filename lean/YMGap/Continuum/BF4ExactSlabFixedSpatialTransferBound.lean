/-
# A cutoff-independent Haar norm bound for the original weighted step

The kernel is the actual K(x,y)V(x), on the same two-slice source carrier.
Its square certificate and interval cap come from the literal original
kinetic and spatial factors. No factor is integrated away or normalized
independently. Weighted Cauchy--Schwarz gives a bound for the actual T.

The constant is explicit in nome and the two width-only face counts, and
does not depend on the heat cutoff. Positivity uses the existing late-cutoff
threshold. This is ordinary product-Haar L2 control, not an OS quotient
estimate, stationarity, a strict contraction, or a physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
import YMGap.Continuum.SU2QuaternionHaarKernelBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces temporalFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- Explicit width/nome cap; K is deliberately not a parameter. -/
def stepCap (w : Q') (width : Nat) : Q' :=
  (prefixCap w)^(temporalFaces width).length *
    (prefixCap w)^(spatialFaces width).length

/-- The actual kernel includes the head spatial weight exactly once. -/
def stepWeight (w : Q') (K width : Nat) : RatPoly :=
  polyMul (kineticWeight w K width) (spatialWeight w K width)

def stepWeightCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    Certificate (N width+N width) (stepWeight w K width) :=
  (kineticCertificate hw0 hw1 K width hK).mul
    (spatialCertificate hw0 hw1 K width (N width+N width) (by omega) hK)

def stepWeightInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) : Interval (N width+N width) (stepWeight w K width) (stepCap w width) :=
  (kineticInterval hw0 hw1 K width).mul
    (spatialInterval hw0 hw1 K width (N width+N width) (by omega))

theorem stepCap_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : (0 : Q') ≤ stepCap w width :=
  (stepWeightInterval hw0 hw1 0 width).nonnegative

/-- Only reassociation connects the bounded kernel map to the original T. -/
theorem transferStep_kernelMap (w : Q') (K width : Nat) (f : RatPoly) :
    RatPolyCoeffEqv (transferStep w K width f)
      (kernelMap (N width) (stepWeight w K width) f) :=
  partialHaarHeads_congr (N width)
    (RatPolyCoeffEqv.mul_assoc (kineticWeight w K width) (spatialWeight w K width) f).symm

theorem transferStep_add (w : Q') (K width : Nat) (f g : RatPoly) :
    RatPolyCoeffEqv (transferStep w K width (polyAdd f g))
      (polyAdd (transferStep w K width f) (transferStep w K width g)) :=
  (transferStep_kernelMap w K width _).trans
    ((kernelMap_add (N width) (stepWeight w K width) f g).trans
      ((transferStep_kernelMap w K width f).symm.add
        (transferStep_kernelMap w K width g).symm))

theorem transferStep_smul (w : Q') (K width : Nat) (c : Q') (f : RatPoly) :
    RatPolyCoeffEqv (transferStep w K width (polySmul c f))
      (polySmul c (transferStep w K width f)) :=
  (transferStep_kernelMap w K width _).trans
    ((kernelMap_smul (N width) (stepWeight w K width) c f).trans
      ((transferStep_kernelMap w K width f).symm.smul c))

/-- Bound the SAME original finite step in ordinary product-Haar squared norm. -/
theorem transferStep_square_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width) (polyMul (transferStep w K width f) (transferStep w K width f)) ≤
      (stepCap w width * stepCap w width) * quaternionHaar (N width) (polyMul f f) := by
  have h := transferStep_kernelMap w K width f
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (h.mul h)))
    (kernelMap_square_bound (stepWeightCertificate hw0 hw1 K width hK)
      (stepWeightInterval hw0 hw1 K width) hf)

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound.stepCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound.stepWeight
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound.stepWeightCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound.stepWeightInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound.stepCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound.transferStep_kernelMap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound.transferStep_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound.transferStep_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound.transferStep_square_bound
