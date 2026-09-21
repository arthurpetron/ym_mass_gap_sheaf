/-
# Distance decay of an ORIGINAL local coupling response

The normalized two-nome score has zero mean in its actual retained background,
an explicit O(|v-u|) polynomial interval, and the literal changed plaquette's
four-link support. Feed precisely this score to the existing original-action
connected-distance theorem and cancel the SAME background partition square.

The background has one homogeneous nome w satisfying the displayed small-nome
spatial guards; the changed factor may have any 0<u<=v<=W<1. The two cutoff
indices are independent. No heterogeneous-background mixing estimate, sum over
changed faces, changing-score limit, scaling trajectory, OS gap or continuum
conclusion is asserted. This is an actual one-defect spatial response, not an
assumed influence bound or a replacement probability law.
-/
import YMGap.Continuum.BF4ExactSlabCouplingScoreBound
import YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay
import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap

namespace YMGap.Continuum.BF4ExactSlabCouplingSpatialResponse

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison (ratio_difference_bound)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabCouplingScoreBound
open YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse
open YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability (faceMass faceMoment faceMass_positive)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarCenteredResponse
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm mem_of_mem_erase)
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

private theorem normalized_numerator (w : Q') (J extent : Nat) (ids : List Nat)
    (hZ : (0 : Q') < heatProductHaar w (blocks extent) extent ids J) (p : RatPoly) :
    normalizedMoment (blocks extent) (polynomialProduct (faceHeatPolynomial w J extent) ids) p hZ ≈
      numerator w (blocks extent) extent ids p J *
        Q'.recipPos (heatProductHaar w (blocks extent) extent ids J) hZ :=
  Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ p))

private theorem raw_zero_of_normalized_zero {a Z : Q'} (hZ : (0 : Q') < Z)
    (ha : a*Q'.recipPos Z hZ ≈ 0) : a ≈ 0 := by
  let r := Q'.recipPos Z hZ
  have hr : r*Z ≈ 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv Z hZ)
  have he : (a*r)*Z ≈ a := Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) (Q'.mul_one_eqv _))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm he)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.zero_mul_eqv _))

/-- The existing connected numerator controls the actual normalized pairing
with any centered local polynomial, even one depending on both cutoff indices.
No fixed-observable limiting argument is used. -/
theorem centered_distance_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (J extent : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hZ : (0 : Q') < heatProductHaar w (blocks extent) extent ids J)
    (p q : RatPoly) (c d : Q') (Ip : Interval (blocks extent) p c) (Iq : Interval (blocks extent) q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hp : LinkLocal extent left p) (hq : LinkLocal extent right q)
    (hq0 : normalizedMoment (blocks extent)
      (polynomialProduct (faceHeatPolynomial w J extent) ids) q hZ ≈ 0) :
    Q'.abs (normalizedMoment (blocks extent)
      (polynomialProduct (faceHeatPolynomial w J extent) ids) (polyMul p q) hZ) ≤
        distanceBudget P Q w hd hs c d := by
  let Z := heatProductHaar w (blocks extent) extent ids J
  let M := fun f => numerator w (blocks extent) extent ids f J
  let cap := distanceBudget P Q w hd hs c d
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
      (connectedNumerator_distance_bound hw0 hw1 hsmall hd hs J extent p q c d
        Ip Iq left right P Q hp hq ids hn hids)
  have hc : M (polyMul p q)*Z + -(0*Z) ≈ M (polyMul p q)*Z :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.mul (.const 0) (.var 1))))
      (.var 0) (by decide) (fun | 0 => M (polyMul p q)*Z | _ => Z)
  have hrat := ratio_difference_bound (M (polyMul p q)) 0 Z Z cap hZ hZ
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hc)) hraw)
  have hpure : M (polyMul p q)*Q'.recipPos Z hZ + -(0*Q'.recipPos Z hZ) ≈
      M (polyMul p q)*Q'.recipPos Z hZ :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.mul (.const 0) (.var 1))))
      (.var 0) (by decide)
      (fun | 0 => M (polyMul p q)*Q'.recipPos Z hZ | _ => Q'.recipPos Z hZ)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_trans _ _ _
      (normalized_numerator w J extent ids hZ (polyMul p q)) (Q'.eqv_symm hpure)))) hrat

/-- Scalar normalization depends on the whole background, but does not add
any quaternion variable to the score's four-link support. -/
theorem faceScore_local {u v : Q'} (hu0 : (0 : Q') < u) (hu1 : u < (1 : Q'))
    (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q')) (K extent id : Nat)
    (hi : id ∈ slabPhysicalFaceEdges extent) (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
    {B : RatPoly} (HB : Certificate (blocks extent) B) (hB : (0 : Q') < quaternionHaar (blocks extent) B) :
    LinkLocal extent (edgesOf (slabPlaquetteAt extent id))
      (faceScore hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB) :=
  ((heatFace_local v K extent id).smul _).add (((heatFace_local u K extent id).smul _).smul (-1))

section OriginalBackground

variable {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v) (hvW : v ≤ W) (hW1 : W < (1 : Q'))
  (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent)
  (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
  {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  (J : Nat) (hJ : headCutoff w ≤ J) (ids : List Nat) (hn : ids.Nodup)
  (hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)

local notation "hv0" => Q'.pos_of_lt_of_le hu0 huv
local notation "hv1" => Q'.lt_of_le_of_lt hvW hW1
local notation "hu1" => Q'.lt_of_le_of_lt huv hv1
local notation "B" => polynomialProduct (faceHeatPolynomial w J extent) ids
local notation "HB" => headProduct_certificate hw0 hw1 J extent hJ ids hids
local notation "hB" => Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
  (partition_floor hw0 hw1 extent ids hids J hJ)

include hsmall hn in
/-- A genuine spatial bound for changing one original face. The coefficient
has no cutoff or ambient-volume factor. Spatial guards constrain only the
retained background nome w, not the two local defect nomes u,v. -/
theorem original_background_distance_bound {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) :
    let hOld := faceMass_positive hu0 hu1 extent id hi HB K hKu hB
    let hNew := faceMass_positive hv0 hv1 extent id hi HB K hKv hB
    Q'.abs (faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B) hNew +
      -(faceMoment u K extent id B p * Q'.recipPos (faceMass u K extent id B) hOld)) ≤
        distanceBudget P (singletonCarrier (slabPlaquetteAt extent id)) w hd hs c (scoreCap W u v) := by
  let s := faceScore hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB
  have I := scoreInterval hu0 huv hvW hW1 K extent id hi hKu hKv HB hB
  have hpins := face_response_pin hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB p
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr hpins))
    (centered_distance_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hd hs
      J extent ids hn hids hB p s c (scoreCap W u v) Ip I left _ P
      (singletonCarrier (slabPlaquetteAt extent id)) hp
      (faceScore_local hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB)
      (faceScore_centered hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB))

end OriginalBackground

set_option maxHeartbeats 800000 in
/-- Replace exactly one factor of the FULL original slab. The old endpoint
is pinned to the unmodified full heat-product expectation; the spectator list
and its positivity are constructed, not supplied as a mixing hypothesis. -/
theorem full_slab_single_defect_bound {w v W : Q'} (hw0 : (0 : Q') < w)
    (hwv : w ≤ v) (hvW : v ≤ W) (hW1 : W < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent)
    (hKw : headCutoff w ≤ K) (hKv : headCutoff v ≤ K)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) :
    let hw1 := Q'.lt_of_le_of_lt hwv (Q'.lt_of_le_of_lt hvW hW1)
    let hv0 := Q'.pos_of_lt_of_le hw0 hwv
    let hv1 := Q'.lt_of_le_of_lt hvW hW1
    let ids := eraseIndex id (slabPhysicalFaceEdges extent)
    let hids := fun j (hj : j ∈ ids) => mem_of_mem_erase id hj
    let B := polynomialProduct (faceHeatPolynomial w K extent) ids
    let HB := headProduct_certificate hw0 hw1 K extent hKw ids hids
    let hB := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
      (partition_floor hw0 hw1 extent ids hids K hKw)
    let hNew := faceMass_positive hv0 hv1 extent id hi HB K hKv hB
    let hFull := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 (slabPhysicalFaceEdges extent))
      (partition_floor hw0 hw1 extent (slabPhysicalFaceEdges extent) (fun _ hj => hj) K hKw)
    Q'.abs (faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B) hNew +
      -(normalizedMoment (blocks extent)
        (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)) p hFull)) ≤
      distanceBudget P (singletonCarrier (slabPlaquetteAt extent id)) w hd hs c (scoreCap W w v) := by
  dsimp only
  let hw1 := Q'.lt_of_le_of_lt hwv (Q'.lt_of_le_of_lt hvW hW1)
  let ids := eraseIndex id (slabPhysicalFaceEdges extent)
  have hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent := fun _ hj => mem_of_mem_erase id hj
  have hn : ids.Nodup := (List.nodup_cons.mp
    ((select_perm id hi).nodup (CayleyParentInj.range_nodup _))).2
  let B := polynomialProduct (faceHeatPolynomial w K extent) ids
  let HB := headProduct_certificate hw0 hw1 K extent hKw ids hids
  have hB : (0 : Q') < quaternionHaar (blocks extent) B :=
    Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
      (partition_floor hw0 hw1 extent ids hids K hKw)
  let hOld := faceMass_positive hw0 hw1 extent id hi HB K hKw hB
  let F := polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)
  have hF : (0 : Q') < quaternionHaar (blocks extent) F :=
    Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 (slabPhysicalFaceEdges extent))
      (partition_floor hw0 hw1 extent (slabPhysicalFaceEdges extent) (fun _ hj => hj) K hKw)
  have hrec : RatPolyCoeffEqv F (polyMul B (faceHeatPolynomial w K extent id)) :=
    (polynomialProduct_perm _ (select_perm id hi)).trans (RatPolyCoeffEqv.mul_comm _ _)
  have hpin : normalizedMoment (blocks extent) F p hF ≈
      faceMoment w K extent id B p * Q'.recipPos (faceMass w K extent id B) hOld :=
    Q'.eqv_trans _ _ _ (normalizedMoment_congr hF hOld hrec (RatPolyCoeffEqv.refl p))
      (Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff
        ((RatPolyCoeffEqv.mul_comm _ p).trans (RatPolyCoeffEqv.mul_assoc p B _).symm)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hpin))))
    (original_background_distance_bound hw0 hwv hvW hW1 K extent id hi hKw hKv
      hw0 hw1 hsmall hd hs K hKw ids hn hids Ip left P hp)

end YMGap.Continuum.BF4ExactSlabCouplingSpatialResponse

#print axioms YMGap.Continuum.BF4ExactSlabCouplingSpatialResponse.centered_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabCouplingSpatialResponse.faceScore_local
#print axioms YMGap.Continuum.BF4ExactSlabCouplingSpatialResponse.original_background_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabCouplingSpatialResponse.full_slab_single_defect_bound
