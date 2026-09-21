/-
# Original normalized coupling response in a varying heat background

The actual heterogeneous partition square cancels in the connected bound.
The existing centered score, its explicit interval and four-link support
then give distance decay for changing one heat factor against that SAME
background. No homogeneous replacement or unproved mixing input enters.

The background nomes lie below an explicit guarded ceiling; the two local
defect nomes have their own explicit cap and late cutoff. These are finite
original expectations, not a continuum or Hamiltonian statement.
-/
import YMGap.Continuum.BF4ExactSlabHeterogeneousDistanceDecay
import YMGap.Continuum.BF4ExactSlabCouplingSpatialResponse

namespace YMGap.Continuum.BF4ExactSlabHeterogeneousCouplingResponse

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison
open YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion
open YMGap.Continuum.BF4ExactSlabHeterogeneousDistanceDecay
open YMGap.Continuum.BF4ExactSlabCouplingSpatialResponse (faceScore_local)
open YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse
open YMGap.Continuum.BF4ExactSlabCouplingScoreBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability (faceMass faceMoment faceMass_positive)
open YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison (ratio_difference_bound)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay (distanceBudget)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

private theorem normalized_numerator (w : Nat → Q') (J : Nat → Nat) (extent : Nat) (ids : List Nat)
    (hZ : (0 : Q') < partition w J extent ids) (p : RatPoly) :
    normalizedMoment (blocks extent) (polynomialProduct (factor w J extent) ids) p hZ ≈
      moment w J extent ids p * Q'.recipPos (partition w J extent ids) hZ :=
  Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ p))

private theorem raw_zero_of_normalized_zero {a Z : Q'} (hZ : (0 : Q') < Z)
    (ha : a*Q'.recipPos Z hZ ≈ 0) : a ≈ 0 := by
  let r := Q'.recipPos Z hZ
  have hr : r*Z ≈ 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv Z hZ)
  have he : (a*r)*Z ≈ a := Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) (Q'.mul_one_eqv _))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm he)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.zero_mul_eqv _))

variable (w : Nat → Q') (J : Nat → Nat) (extent : Nat) {W : Q'}
  (hW0 : (0 : Q') ≤ W) (hW1 : W ≤ (1 : Q'))
  (hw0 : ∀ id, id ∈ slabPhysicalFaceEdges extent → (0 : Q') ≤ w id)
  (hwW : ∀ id, id ∈ slabPhysicalFaceEdges extent → w id ≤ W)
  (hsmall : heatRatio W ≤ HalfPow.half) (hd : heatRemainderBound W < 1)
  (hs : entropyRate 625 (adjustedCoreRate W hd) < 1)

include hW0 hW1 hw0 hwW hsmall hd hs in
/-- A centered local polynomial may depend on the current cutoffs and all
scalar background normalizations. Its actual pairing is bounded here. -/
theorem centered_distance_bound (ids : List Nat) (hn : ids.Nodup)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hZ : (0 : Q') < partition w J extent ids)
    (p q : RatPoly) (c d : Q') (Ip : Interval (blocks extent) p c) (Iq : Interval (blocks extent) q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hp : LinkLocal extent left p) (hq : LinkLocal extent right q)
    (hq0 : normalizedMoment (blocks extent) (polynomialProduct (factor w J extent) ids) q hZ ≈ 0) :
    Q'.abs (normalizedMoment (blocks extent) (polynomialProduct (factor w J extent) ids) (polyMul p q) hZ) ≤
      distanceBudget P Q W hd hs c d := by
  let Z := partition w J extent ids
  let M := fun f => moment w J extent ids f
  let cap := distanceBudget P Q W hd hs c d
  have hzero : M q ≈ 0 := raw_zero_of_normalized_zero hZ
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (normalized_numerator w J extent ids hZ q)) hq0)
  have hconn : connectedNumerator w J extent ids p q ≈ M (polyMul p q)*Z :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hzero)))
      (poly_identity_of_normal_eq (.add (.var 0) (.neg (.mul (.var 1) (.const 0))))
        (.var 0) (by decide) (fun | 0 => M (polyMul p q)*Z | _ => M p))
  have hraw : Q'.abs (M (polyMul p q)*Z) ≤ cap*(Z*Z) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hconn))
      (connectedNumerator_distance_bound w J extent hW0 hW1 hw0 hwW hsmall hd hs p q c d
        Ip Iq left right P Q hp hq ids hn hids)
  have hc : M (polyMul p q)*Z + -(0*Z) ≈ M (polyMul p q)*Z :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.mul (.const 0) (.var 1))))
      (.var 0) (by decide) (fun | 0 => M (polyMul p q)*Z | _ => Z)
  have hrat := ratio_difference_bound (M (polyMul p q)) 0 Z Z cap hZ hZ
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hc)) hraw)
  have hpure : M (polyMul p q)*Q'.recipPos Z hZ + -(0*Q'.recipPos Z hZ) ≈
      M (polyMul p q)*Q'.recipPos Z hZ :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.mul (.const 0) (.var 1))))
      (.var 0) (by decide) (fun | 0 => M (polyMul p q)*Q'.recipPos Z hZ | _ => Q'.recipPos Z hZ)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_trans _ _ _
      (normalized_numerator w J extent ids hZ (polyMul p q)) (Q'.eqv_symm hpure)))) hrat

include hW0 hW1 hw0 hwW hsmall hd hs in
/-- Actual one-face change in the varying original background. The background
positivity and the centered score are constructed, not supplied as analytic inputs. -/
theorem background_response_bound {u v V : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v)
    (hvV : v ≤ V) (hV1 : V < (1 : Q')) (K id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent)
    (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) :
    let hv0 := Q'.pos_of_lt_of_le hu0 huv
    let hv1 := Q'.lt_of_le_of_lt hvV hV1
    let hu1 := Q'.lt_of_le_of_lt huv hv1
    let B := polynomialProduct (factor w J extent) ids
    let HB := productCertificate w J extent hw0 hwW hW1 hsmall (Q'.le_of_lt hd) ids hids
    let hB := partition_positive w J extent hw0 hwW hW1 hsmall hd ids hids
    let hOld := faceMass_positive hu0 hu1 extent id hi HB K hKu hB
    let hNew := faceMass_positive hv0 hv1 extent id hi HB K hKv hB
    Q'.abs (faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B) hNew +
      -(faceMoment u K extent id B p * Q'.recipPos (faceMass u K extent id B) hOld)) ≤
        distanceBudget P (singletonCarrier (slabPlaquetteAt extent id)) W hd hs c (scoreCap V u v) := by
  dsimp only
  let hv0 := Q'.pos_of_lt_of_le hu0 huv
  let hv1 := Q'.lt_of_le_of_lt hvV hV1
  let hu1 := Q'.lt_of_le_of_lt huv hv1
  let HB := productCertificate w J extent hw0 hwW hW1 hsmall (Q'.le_of_lt hd) ids hids
  let hB := partition_positive w J extent hw0 hwW hW1 hsmall hd ids hids
  let s := faceScore hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB
  have I := scoreInterval hu0 huv hvV hV1 K extent id hi hKu hKv HB hB
  have hpin := face_response_pin hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB p
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hpin))
    (centered_distance_bound w J extent hW0 hW1 hw0 hwW hsmall hd hs ids hn hids hB p s c (scoreCap V u v)
      Ip I left _ P (singletonCarrier (slabPlaquetteAt extent id)) hp
      (faceScore_local hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB)
      (faceScore_centered hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB))

end YMGap.Continuum.BF4ExactSlabHeterogeneousCouplingResponse

#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousCouplingResponse.centered_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousCouplingResponse.background_response_bound
