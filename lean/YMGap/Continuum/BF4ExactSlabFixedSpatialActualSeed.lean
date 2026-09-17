/-
# Constructed exactly centered seeds on the original odd marginal

The finite polynomial J approximates 1/(nu*P_i nu). For a conditionally
Haar-centered piece tau the chosen seed is J*tau and its weighted residual
q is exactly centered against nu at EVERY finite degree. The cleared error
(P_i nu)*(nu*q-tau) has a certified geometric interval, with all original
parameter dependence retained. No inverse observable or stationary law is
introduced. This is a finite approximation producer, not a uniform signed
cost bound or a physical spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow
import YMGap.Continuum.QuaternionHaarPositiveWindowInverse
import YMGap.Continuum.SU2QuaternionWeightedResidualApproximation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockCertificate
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering
open YMGap.Continuum.SU2QuaternionWeightedResidualApproximation
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (negInterval)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact hp r hr

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

include hw0 hw1 hK in
private theorem upperSquare_positive : (0 : Q') < upper w K width n * upper w K width n :=
  Q'.mul_pos (upper_positive hw0 hw1 K width hK n) (upper_positive hw0 hw1 K width hK n)

include hw0 hw1 hK in
private theorem lowerSquare_le_upperSquare :
    lower w K width n * lower w K width n ≤ upper w K width n * upper w K width n :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (lower_le_upper w K width n)
      (Q'.le_of_lt (lower_positive hw0 hw1 K width hK n)))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (lower_le_upper w K width n)
      (Q'.le_of_lt (upper_positive hw0 hw1 K width hK n)))

def inverse (i k : Nat) : RatPoly :=
  QuaternionHaarPositiveWindowInverse.reciprocal (denominator w K width n i)
    (upper w K width n * upper w K width n) (upperSquare_positive hw0 hw1 K width hK n) k

theorem inverse_supported (i k : Nat) : SupportedQuaternionBlocks (N width)
    (inverse hw0 hw1 K width hK n i k) :=
  QuaternionHaarPositiveWindowInverse.reciprocal_supported (denominator_supported w K width n i)
    _ (upperSquare_positive hw0 hw1 K width hK n) k

/-- An auxiliary approximation rate, NOT a physical time-decay rate. -/
def rate : Q' := QuaternionHaarPositiveWindowInverse.radius
  (lower w K width n * lower w K width n) (upper w K width n * upper w K width n)
  (upperSquare_positive hw0 hw1 K width hK n)

theorem rate_nonnegative : (0 : Q') ≤ rate hw0 hw1 K width hK n :=
  QuaternionHaarPositiveWindowInverse.radius_nonnegative
    (upperSquare_positive hw0 hw1 K width hK n) (lowerSquare_le_upperSquare hw0 hw1 K width hK n)

theorem rate_lt_one : rate hw0 hw1 K width hK n < (1 : Q') :=
  QuaternionHaarPositiveWindowInverse.radius_lt_one
    (Q'.mul_pos (lower_positive hw0 hw1 K width hK n) (lower_positive hw0 hw1 K width hK n))
    (upperSquare_positive hw0 hw1 K width hK n)

def inverseError (i k : Nat) : RatPoly :=
  polyAdd polyOne (polyNeg (polyMul (denominator w K width n i) (inverse hw0 hw1 K width hK n i k)))

def inverseErrorInterval (i : Nat) (hi : i < N width) (k : Nat) :
    Interval (N width) (inverseError hw0 hw1 K width hK n i k) ((rate hw0 hw1 K width hK n)^k) := by
  have P := QuaternionHaarPositiveWindowInverse.multiplierErrorInterval
    (denominator_supported w K width n i) (upperSquare_positive hw0 hw1 K width hK n)
    (lowerSquare_le_upperSquare hw0 hw1 K width hK n)
    (denominatorLowerCertificate hw0 hw1 K width hK n i hi)
    (denominatorUpperCertificate hw0 hw1 K width hK n i hi) k
  exact .ofCoeff (supported_add (supported_one _)
    (support_neg (supported_polyMul (denominator_supported w K width n i)
      (inverse_supported hw0 hw1 K width hK n i k))))
    (coeffEvalExpr_eqv_of_normalize_eq (.add (.const 1) (.neg (.var 0)))
      (.neg (.add (.var 0) (.neg (.const 1)))) (by decide)
      (fun _ => polyMul (denominator w K width n i) (inverse hw0 hw1 K width hK n i k)))
    (negInterval P)

def seed (i k : Nat) (tau : RatPoly) : RatPoly :=
  polyMul (inverse hw0 hw1 K width hK n i k) tau

theorem seed_supported (i k : Nat) {tau : RatPoly} (ht : SupportedQuaternionBlocks (N width) tau) :
    SupportedQuaternionBlocks (N width) (seed hw0 hw1 K width hK n i k tau) :=
  supported_polyMul (inverse_supported hw0 hw1 K width hK n i k) ht

def test (i k : Nat) (tau : RatPoly) : RatPoly :=
  weightedResidual i (marginalWeight w K width n) (seed hw0 hw1 K width hK n i k tau)

theorem test_supported (i k : Nat) {tau : RatPoly} (ht : SupportedQuaternionBlocks (N width) tau) :
    SupportedQuaternionBlocks (N width) (test hw0 hw1 K width hK n i k tau) :=
  weightedResidual_supported i (marginalWeight_supported w K width n)
    (seed_supported hw0 hw1 K width hK n i k ht)

/-- This exact condition includes ALL other coordinates, not a smaller filtration. -/
theorem test_centered (i k : Nat) (tau : RatPoly) :
    RatPolyCoeffEqv (project i (polyMul (marginalWeight w K width n)
      (test hw0 hw1 K width hK n i k tau))) polyZero :=
  project_weightedResidual_zero i _ _

def defect (i k : Nat) (tau : RatPoly) : RatPoly :=
  polyAdd (polyMul (marginalWeight w K width n) (test hw0 hw1 K width hK n i k tau)) (polyNeg tau)

theorem defect_supported (i k : Nat) {tau : RatPoly} (ht : SupportedQuaternionBlocks (N width) tau) :
    SupportedQuaternionBlocks (N width) (defect hw0 hw1 K width hK n i k tau) :=
  supported_add (supported_polyMul (marginalWeight_supported w K width n)
    (test_supported hw0 hw1 K width hK n i k ht)) (support_neg ht)

def marginalInterval : Interval (N width) (marginalWeight w K width n) (upper w K width n) where
  support := marginalWeight_supported w K width n
  nonnegative := Q'.le_of_lt (upper_positive hw0 hw1 K width hK n)
  upper := upperCertificate hw0 hw1 K width hK n
  lower := .add (.constant (N width) _ (Q'.le_of_lt (upper_positive hw0 hw1 K width hK n)))
    (marginalCertificate hw0 hw1 K width hK n)

/-- A vanishing interval, retaining the actual finite polynomial tau cap. -/
def clearedDefectInterval (i : Nat) (hi : i < N width) (k : Nat)
    {tau : RatPoly} {B : Q'} (P : Interval (N width) tau B)
    (hc : RatPolyCoeffEqv (project i tau) polyZero) :
    Interval (N width)
      (polyMul (project i (marginalWeight w K width n)) (defect hw0 hw1 K width hK n i k tau))
      (upper w K width n * ((rate hw0 hw1 K width hK n)^k * B) +
        (upper w K width n * (rate hw0 hw1 K width hK n)^k) * B) :=
  .ofCoeff (supported_polyMul (project_supported i (marginalWeight_supported w K width n))
    (defect_supported hw0 hw1 K width hK n i k P.support))
    (weightedResidual_seed_error i (marginalWeight w K width n)
      (inverse hw0 hw1 K width hK n i k) tau hc)
    (((marginalInterval hw0 hw1 K width hK n).mul
      (project_interval (N width) i hi ((inverseErrorInterval hw0 hw1 K width hK n i hi k).mul P))).add
      (negInterval (((project_interval (N width) i hi (marginalInterval hw0 hw1 K width hK n)).mul
        (inverseErrorInterval hw0 hw1 K width hK n i hi k)).mul P)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.inverse
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.inverse_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.rate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.rate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.rate_lt_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.inverseErrorInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.seed_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.test_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.test_centered
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.defect_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.marginalInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed.clearedDefectInterval
