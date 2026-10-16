/-
# Lag control for the finite ORIGINAL bulk-deficit remainder budget

The full weighted trace deficit has the same explicit cap

  B = 4 * sum(coefficients)

as the scalar-square remainder cap used by the diagonal estimate.  The sharp
fundamental-character interval gives this cap directly, before any
expectation is taken.  Existing endpoint mixing then replaces the arbitrary
lagged deficit first moment in the remainder budget by the actual finite OWN
mean plus one explicit finite-boundary error.

The rate remains the existing width-dependent `mixRate`.  This file does not
claim a width-uniform rate, a small OWN deficit mean, an ORIGINAL-to-FREE
comparison, cutoff removal, a continuum Hamiltonian, or a Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonal
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitLagControl

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws
  (middleRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (middleRatio_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost
  (plaquetteCharacterInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl
  (endpoint_mean_lags_commonTail lower_endpoint_mean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.OSReconstructionProgress (le_of_le_eqv)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarAngularCarrier (intervalNeg)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonal
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] windowRatio middleRatio mixRate

private theorem supported_smul_local {blocks : Nat} {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks blocks polynomial) (scale : Q') :
    SupportedQuaternionBlocks blocks (polySmul scale polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hpolynomial source hsource

private theorem supported_neg_local {blocks : Nat} {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (polyNeg polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hpolynomial source hsource

private theorem smul_neg_local (polynomial : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) polynomial) (polyNeg polynomial) :=
  (cap_mul_left (-1) polynomial).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => polynomial))

private def plaquetteTraceDeficitCanonicalInterval
    (width : Nat) (face : Z4Plaq) :
    Interval (N width)
      (polyAdd (cap 2)
        (polyNeg (characterPolynomial (plaquette width face).scalar 1))) 4 := by
  let character := characterPolynomial (plaquette width face).scalar 1
  let I := plaquetteCharacterInterval width face
  refine
    { support := supported_add
        (supported_smul_local (supported_one (N width)) 2)
        (supported_neg_local I.support)
      nonnegative := by decide
      upper := ?_
      lower := ?_ }
  · apply Certificate.ofCoeff ?_ I.lower
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.const 4)
        (.neg (.add (.const 2) (.neg (.var 0)))))
      (.add (.const 2) (.var 0))
      (by decide) (fun _ => character)
  · have hraw := I.upper.add
      (Certificate.constant (N width) 4 (by decide))
    apply Certificate.ofCoeff ?_ hraw
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.const 4)
        (.add (.const 2) (.neg (.var 0))))
      (.add
        (.add (.const 2) (.neg (.var 0)))
        (.const 4))
      (by decide) (fun _ => character)

/-- Every literal fundamental plaquette trace deficit lies in `[0,4]` on
the unchanged one-slice Haar carrier. -/
def plaquetteTraceDeficit_interval (width : Nat) (face : Z4Plaq) :
    Interval (N width) (plaquetteTraceDeficit width face) 4 := by
  let character := characterPolynomial (plaquette width face).scalar 1
  have hsupport : SupportedQuaternionBlocks (N width)
      (plaquetteTraceDeficit width face) := by
    unfold plaquetteTraceDeficit
    exact supported_add
      (supported_smul_local (supported_one (N width)) 2)
      (supported_smul_local
        (plaquetteCharacterInterval width face).support (-1))
  have hcoeff : RatPolyCoeffEqv
      (plaquetteTraceDeficit width face)
      (polyAdd (cap 2) (polyNeg character)) := by
    unfold plaquetteTraceDeficit cap
    exact (RatPolyCoeffEqv.refl _).add (smul_neg_local character)
  exact Interval.ofCoeff hsupport hcoeff
    (plaquetteTraceDeficitCanonicalInterval width face)

private def weightedTraceDeficitInterval
    (s : Nat) (hs : 0 < s) (face : Z4Plaq)
    (hface : face ∈ bulkSourceFaces s) :
    Interval (N (s * s))
      (polySmul (bulkSourceCoefficient s hs face)
        (plaquetteTraceDeficit (s * s) face))
      (4 * bulkSourceCoefficient s hs face) := by
  exact Interval.changeCap
    (Q'.mul_comm_eqv (bulkSourceCoefficient s hs face) 4)
    (Interval.smul (bulkSourceCoefficient s hs face)
      (Q'.le_of_lt (bulkSourceCoefficient_pos hs hface))
      (plaquetteTraceDeficit_interval (s * s) face))

private def finiteTraceDeficitInterval (s : Nat) (hs : 0 < s) :
    ∀ items : List Z4Plaq,
      (∀ face, face ∈ items → face ∈ bulkSourceFaces s) →
      Interval (N (s * s))
        (finitePolySum
          (fun face => polySmul (bulkSourceCoefficient s hs face)
            (plaquetteTraceDeficit (s * s) face)) items)
        (listQSum (fun face => 4 * bulkSourceCoefficient s hs face) items)
  | [], _ => Interval.zero _
  | face :: items, hitems =>
      (weightedTraceDeficitInterval s hs face
        (hitems face List.mem_cons_self)).add
        (finiteTraceDeficitInterval s hs items
          (fun next hnext => hitems next (List.mem_cons_of_mem face hnext)))

private theorem listQSum_four {Index : Type} (coefficient : Index → Q')
    (items : List Index) :
    listQSum (fun index => 4 * coefficient index) items ≈
      4 * listQSum coefficient items := by
  induction items with
  | nil => exact Q'.eqv_symm (Q'.mul_zero_eqv 4)
  | cons index items induction =>
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) induction)
        (Q'.eqv_symm
          (Q'.mul_add_eqv 4 (coefficient index) (listQSum coefficient items)))

/-- The complete positively weighted trace deficit has exactly the same cap
as the scalar-square remainder budget. -/
def originalBulkTraceDeficit_interval (s : Nat) (hs : 0 < s) :
    Interval (N (s * s)) (originalBulkTraceDeficit s hs)
      (originalBulkScalarSquareRemainderCap s hs) := by
  unfold originalBulkTraceDeficit originalBulkScalarSquareRemainderCap
  exact Interval.changeCap
    (listQSum_four (bulkSourceCoefficient s hs) (bulkSourceFaces s))
    (finiteTraceDeficitInterval s hs (bulkSourceFaces s)
      (fun _ hface => hface))

/-- The already compiled bounded deficit source inherits the literal global
trace-deficit interval without changing its carrier. -/
def originalBulkDeficit_interval (s : Nat) (hs : 0 < s) :
    Interval (N (s * s))
      (sourcePolynomial (originalBulkDeficitExpression s hs))
      (originalBulkScalarSquareRemainderCap s hs) := by
  have hsupport : SupportedQuaternionBlocks (N (s * s))
      (sourcePolynomial (originalBulkDeficitExpression s hs)) := by
    simpa only [Nat.zero_add, Nat.one_mul] using
      (source_supported 0 (originalBulkDeficitExpression s hs)
        (originalBulkDeficitExpression_within s hs))
  exact Interval.ofCoeff hsupport
    (originalBulkDeficitExpression_jet_source_pin s hs)
    (originalBulkTraceDeficit_interval s hs)

/-- The actual finite OWN deficit center is nonnegative because both terms in
its global jet--remainder split are certified nonnegative. -/
theorem originalBulkDeficitOwnMean_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    (0 : Q') ≤ originalBulkDeficitOwnMean hw0 hw1 s hs stage n := by
  unfold originalBulkDeficitOwnMean
    YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.expressionOwnMean
  let K := headCutoff w + stage
  let hK : headCutoff w ≤ K := Nat.le_add_right _ _
  let jet := middleRatio hw0 hw1 K (s * s) hK (n + 1) n
    (originalBulkVectorQuadraticJet s hs)
  let remainder := middleRatio hw0 hw1 K (s * s) hK (n + 1) n
    (originalBulkScalarSquareRemainder s hs)
  have hsum : (0 : Q') ≤ jet + remainder :=
    Q'.zero_le_add _ _
      (originalBulkVectorQuadraticJet_middleRatio_nonnegative
        hw0 hw1 s hs K hK (n + 1) n)
      (originalBulkScalarSquareRemainder_middleRatio_nonnegative
        hw0 hw1 s hs K hK (n + 1) n)
  have hsplit := Q'.eqv_trans _ _ _
    (middleRatio_congr hw0 hw1 K (s * s) hK (n + 1) n
      (originalBulkDeficitExpression_jet_source_pin s hs))
    (originalBulkTraceDeficit_middleRatio_split
      hw0 hw1 s hs K hK (n + 1) n)
  exact le_of_le_eqv hsum (Q'.eqv_symm hsplit)

/-- The actual finite OWN center is exactly the lower endpoint mean of the
one-step window used by the lag comparison. -/
theorem originalBulkDeficitOwnMean_endpoint_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    originalBulkDeficitOwnMean hw0 hw1 s hs stage n ≈
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n 1 n
        (sourcePolynomial (originalBulkDeficitExpression s hs)) := by
  unfold originalBulkDeficitOwnMean
    YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.expressionOwnMean
  have hsupport := (originalBulkDeficit_interval s hs).support
  exact Q'.eqv_trans _ _ _
    (middleRatio_swap hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) (n + 1) n
      (sourcePolynomial (originalBulkDeficitExpression s hs)))
    (Q'.eqv_symm
      (lower_endpoint_mean hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n 1 hsupport))

/-- Explicit endpoint-mixing payment for replacing an arbitrary lagged
deficit mean by the actual finite OWN mean. -/
def originalBulkDeficitLagError {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) : Q' :=
  mixRate hw0 hw1 (s * s) ^ n *
    (originalBulkScalarSquareRemainderCap s hs +
      originalBulkScalarSquareRemainderCap s hs)

/-- The arbitrary-lag full-deficit first moment is controlled by the actual
OWN mean plus the explicit finite-boundary error. -/
theorem originalBulkDeficit_windowRatio_le_ownMean_add_lagError {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (sourcePolynomial (originalBulkDeficitExpression s hs)) ≤
      originalBulkDeficitOwnMean hw0 hw1 s hs stage n +
        originalBulkDeficitLagError hw0 hw1 s hs n := by
  let K := headCutoff w + stage
  let hK : headCutoff w ≤ K := Nat.le_add_right _ _
  let deficit := sourcePolynomial (originalBulkDeficitExpression s hs)
  let bound := originalBulkScalarSquareRemainderCap s hs
  have hlag := (endpoint_mean_lags_commonTail hw0 hw1 K (s * s) hK
    n L 1 (originalBulkDeficit_interval s hs)).1
  have hone := originalBulkDeficitOwnMean_endpoint_one
    hw0 hw1 s hs stage n
  exact Q'.le_trans' _ _ _ hlag
    (Q'.le_of_eqv
      (Q'.add_eqv_congr'
        (Q'.eqv_symm hone) (Q'.eqv_refl _)))

/-- The lower remainder diagonal now depends only on the actual deficit OWN
mean and the explicit lag-mixing payment. -/
theorem originalBulkScalarSquareRemainder_leftDiagonal_le_ownMeanLag {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let remainder := originalBulkScalarSquareRemainder s hs
    let center := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
    let bound := originalBulkScalarSquareRemainderCap s hs
    let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage n
    let lagError := originalBulkDeficitLagError hw0 hw1 s hs n
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (shifted remainder center) (shifted remainder center)) ≤
      bound * ((own + lagError) + own) := by
  dsimp only
  let bound := originalBulkScalarSquareRemainderCap s hs
  let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage n
  let lagError := originalBulkDeficitLagError hw0 hw1 s hs n
  have hbase :=
    originalBulkScalarSquareRemainder_leftDiagonal_le_deficitMeans
      hw0 hw1 s hs stage n L
  have hlag := originalBulkDeficit_windowRatio_le_ownMean_add_lagError
    hw0 hw1 s hs stage n L
  have hsum := Q'.add_le_add_right _ _ own hlag
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ bound hsum
    (originalBulkScalarSquareRemainderCap_nonnegative s hs)
  exact Q'.le_trans' _ _ _ hbase hscaled

/-- The lifted upper remainder diagonal obeys the same OWN-mean/mixing
budget, so the two Cauchy factors now share one explicit scalar bound. -/
theorem originalBulkScalarSquareRemainder_rightDiagonal_le_ownMeanLag {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let remainder := originalBulkScalarSquareRemainder s hs
    let center := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
    let bound := originalBulkScalarSquareRemainderCap s hs
    let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage n
    let lagError := originalBulkDeficitLagError hw0 hw1 s hs n
    let lifted := liftBoundary (L * N (s * s)) (shifted remainder center)
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul lifted lifted) ≤
      bound * ((own + lagError) + own) := by
  dsimp only
  let bound := originalBulkScalarSquareRemainderCap s hs
  let own := originalBulkDeficitOwnMean hw0 hw1 s hs stage n
  let lagError := originalBulkDeficitLagError hw0 hw1 s hs n
  have hbase :=
    originalBulkScalarSquareRemainder_rightDiagonal_le_deficitMeans
      hw0 hw1 s hs stage n L
  have hlag := originalBulkDeficit_windowRatio_le_ownMean_add_lagError
    hw0 hw1 s hs stage n L
  have hsum := Q'.add_le_add_right _ _ own hlag
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ bound hsum
    (originalBulkScalarSquareRemainderCap_nonnegative s hs)
  exact Q'.le_trans' _ _ _ hbase hscaled

#print axioms plaquetteTraceDeficit_interval
#print axioms originalBulkTraceDeficit_interval
#print axioms originalBulkDeficit_interval
#print axioms originalBulkDeficitOwnMean_nonnegative
#print axioms originalBulkDeficitOwnMean_endpoint_one
#print axioms originalBulkDeficit_windowRatio_le_ownMean_add_lagError
#print axioms originalBulkScalarSquareRemainder_leftDiagonal_le_ownMeanLag
#print axioms originalBulkScalarSquareRemainder_rightDiagonal_le_ownMeanLag

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitLagControl
