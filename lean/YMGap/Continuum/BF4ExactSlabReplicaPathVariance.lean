/-
# Full-action replica path variance bound

The original finite-cutoff slab weight is kept intact in both copies. Its
global unnormalized variance determinant is bounded by the finite sum of
adjacent replica-prefix squares, with exactly one factor for the number of
original link blocks. This is an algebraic path starting bound, not a
conditional edge-flow, coercivity, or continuum theorem. The prefix order
has not been identified with time-layer cut geometry.
-/

import YMGap.Continuum.BF4ExactSlabReplicaCutComparison
import YMGap.Continuum.SU2QuaternionReplicaPathTelescope
import YMGap.Continuum.SU2QuaternionGlobalVarianceReplica

namespace YMGap.Continuum.BF4ExactSlabReplicaPathVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabReplicaCutComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionReplicaPairBounds
open YMGap.Continuum.SU2QuaternionReplicaPathTelescope
open YMGap.Continuum.SU2QuaternionGlobalVarianceReplica
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder (haar_order)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local notation:max "faces" extent:arg => slabPhysicalFaceEdges extent
local infix:50 " ≈ " => Q'.eqv

/-- The actual shared-link finite-cutoff action on one original slab. -/
def fullWeight (w : Q') (K extent : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (faces extent)

def pathSquareSum (extent : Nat) (f : RatPoly) : RatPoly :=
  polySum ((increments (replicaPrefix (blocks extent) · f) (blocks extent)).map
    (fun q => polyMul q q))

theorem fullWeight_supported (w : Q') (K extent : Nat) :
    SupportedQuaternionBlocks (blocks extent) (fullWeight w K extent) :=
  heatProduct_supported w K extent (faces extent)

def fullWeight_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) :
    Certificate (blocks extent) (fullWeight w K extent) :=
  headProduct_certificate hw0 hw1 K extent hK (faces extent) (fun _ h => h)

private theorem haar_smul_left (n : Nat) (c : Q') (p r : RatPoly) :
    Q'.eqv (quaternionHaar n (polyMul (polySmul c p) r))
      (c * quaternionHaar n (polyMul p r)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p r))
    (quaternionHaar_polySmul n c (polyMul p r))

/-- The full original finite-cutoff variance numerator is paid by the
actual adjacent replica-prefix increments. No partition reciprocal occurs. -/
theorem original_path_variance_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (hK : headCutoff w ≤ K)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f) :
    2 * (quaternionHaar (blocks extent) (fullWeight w K extent) *
        quaternionHaar (blocks extent)
          (polyMul (fullWeight w K extent) (polyMul f f)) +
      -(quaternionHaar (blocks extent) (polyMul (fullWeight w K extent) f) *
        quaternionHaar (blocks extent) (polyMul (fullWeight w K extent) f))) ≤
      (Q'.ofNat (blocks extent)) *
        quaternionHaar (blocks extent + blocks extent)
          (polyMul (originalPair w K extent) (pathSquareSum extent f)) := by
  let n := blocks extent
  let W := fullWeight w K extent
  let d := difference f (liftBoundary n f)
  let S := pathSquareSum extent f
  have hW : SupportedQuaternionBlocks n W := fullWeight_supported w K extent
  have P : Certificate n W := fullWeight_certificate hw0 hw1 K extent hK
  have R : Certificate (n+n) (originalPair w K extent) :=
    pairCertificate n hW P
  have C := replica_path_cauchy_certificate n f hf
  have horder := haar_order C R
  have hleft : quaternionHaar (n+n)
      (polyMul (polyMul d d) (originalPair w K extent)) ≈
      quaternionHaar (n+n) (polyMul (originalPair w K extent) (polyMul d d)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hright : quaternionHaar (n+n)
      (polyMul (polySmul (Q'.ofNat n) S) (originalPair w K extent)) ≈
      (Q'.ofNat n) * quaternionHaar (n+n) (polyMul (originalPair w K extent) S) :=
    Q'.eqv_trans _ _ _ (haar_smul_left _ _ _ _)
      (Q'.mul_eqv_congr_left _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
  have hvar := global_variance_identity n W f hW hf
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hvar)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ horder (Q'.le_of_eqv hright)))

#print axioms fullWeight
#print axioms pathSquareSum
#print axioms fullWeight_supported
#print axioms fullWeight_certificate
#print axioms original_path_variance_bound

end YMGap.Continuum.BF4ExactSlabReplicaPathVariance
