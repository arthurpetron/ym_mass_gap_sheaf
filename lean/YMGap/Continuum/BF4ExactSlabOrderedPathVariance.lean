/-
# Original variance along any full permutation of physical blocks

The original two-copy variance identity and the finite Cauchy certificate
are unchanged by choosing a different explicit replacement order. This
supplies the path-sum consumer for chronological cut and energy bounds.
-/

import YMGap.Continuum.BF4ExactSlabReplicaPathVariance
import YMGap.Continuum.SU2QuaternionOrderedReplicaPath

namespace YMGap.Continuum.BF4ExactSlabOrderedPathVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabReplicaCutComparison
open YMGap.Continuum.BF4ExactSlabReplicaPathVariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionReplicaPairBounds
open YMGap.Continuum.SU2QuaternionReplicaPathTelescope
open YMGap.Continuum.SU2QuaternionOrderedReplicaPath
open YMGap.Continuum.SU2QuaternionGlobalVarianceReplica
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder (haar_order)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

def orderedSquareSum (extent : Nat) (order : List Nat) (f : RatPoly) : RatPoly :=
  polySum ((increments (orderedPrefix (blocks extent) order · f) (blocks extent)).map
    (fun q => polyMul q q))

/-- Unnormalized ORIGINAL variance determinant, with the same partition
and observable in every factor. -/
def varianceDeterminant (w : Q') (K extent : Nat) (f : RatPoly) : Q' :=
  quaternionHaar (blocks extent) (fullWeight w K extent) *
      quaternionHaar (blocks extent) (polyMul (fullWeight w K extent) (polyMul f f)) +
    -(quaternionHaar (blocks extent) (polyMul (fullWeight w K extent) f) *
      quaternionHaar (blocks extent) (polyMul (fullWeight w K extent) f))

private theorem haar_smul_left (n : Nat) (c : Q') (p r : RatPoly) :
    quaternionHaar n (polyMul (polySmul c p) r) ≈
      c * quaternionHaar n (polyMul p r) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p r))
    (quaternionHaar_polySmul n c (polyMul p r))

/-- Every permutation of the actual blocks gives the same length-N path
bound for the ORIGINAL weighted variance determinant. -/
theorem original_ordered_path_variance_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (hK : headCutoff w ≤ K)
    (order : List Nat) (hperm : order.Perm (List.range (blocks extent)))
    (f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f) :
    2 * varianceDeterminant w K extent f ≤ Q'.ofNat (blocks extent) *
      quaternionHaar (blocks extent + blocks extent)
        (polyMul (originalPair w K extent) (orderedSquareSum extent order f)) := by
  let n := blocks extent
  let W := fullWeight w K extent
  let d := difference f (liftBoundary n f)
  let S := orderedSquareSum extent order f
  have hW : SupportedQuaternionBlocks n W := fullWeight_supported w K extent
  have R : Certificate (n+n) (originalPair w K extent) :=
    pairCertificate n hW (fullWeight_certificate hw0 hw1 K extent hK)
  have C := ordered_path_cauchy_certificate n order hperm f hf
  have horder := haar_order C R
  have hleft : quaternionHaar (n+n)
      (polyMul (polyMul d d) (originalPair w K extent)) ≈
      quaternionHaar (n+n) (polyMul (originalPair w K extent) (polyMul d d)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hright : quaternionHaar (n+n)
      (polyMul (polySmul (Q'.ofNat n) S) (originalPair w K extent)) ≈
      Q'.ofNat n * quaternionHaar (n+n) (polyMul (originalPair w K extent) S) :=
    Q'.eqv_trans _ _ _ (haar_smul_left _ _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
  have hvar := global_variance_identity n W f hW hf
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hvar)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ horder (Q'.le_of_eqv hright)))

#print axioms original_ordered_path_variance_bound

end YMGap.Continuum.BF4ExactSlabOrderedPathVariance
