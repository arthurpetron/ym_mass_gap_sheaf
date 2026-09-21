/-
# Volume-independent sum of isolated ORIGINAL coupling defects

For each physical face separately, replace its heat factor in the SAME
homogeneous original slab and subtract that slab's unchanged expectation.
The sum of the absolute responses is bounded independently of cutoff and
slab extent. Spatial tails have the computed blocked geometric budget.

These are isolated changes, each starting from the original homogeneous
law. They are NOT successive steps of a heterogeneous coupling path and
are not asserted to add up to a simultaneous many-face change. All coupling,
probe and small-nome spatial guards remain explicit. No continuum or OS
conclusion is obtained here.
-/
import YMGap.Continuum.BF4ExactSlabCouplingSpatialResponse
import YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance
import YMGap.Continuum.Z4LinfGeometricSum

namespace YMGap.Continuum.BF4ExactSlabSummedCouplingDefects

set_option autoImplicit false
set_option maxHeartbeats 1000000
open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabCouplingVariationInterval
open YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability
open YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability (faceMass faceMoment faceMass_positive)
open YMGap.Continuum.BF4ExactSlabCouplingScoreBound
open YMGap.Continuum.BF4ExactSlabCouplingSpatialResponse
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay
open YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance (distanceBudget_factor)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex mem_of_mem_erase)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf (linfDist)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSelectionMobius (sum_map)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.Z4LinfGeometricSum

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

/-- The singleton face contributes four links and one carrier plaquette.
Its position does not occur in this explicit amplitude. -/
def amplitude {left : List Z4Link} (P : ProbeCarrier left) (w : Q')
    (hd : heatRemainderBound w < 1) (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (c b : Q') : Q' :=
  (((c*b+c*b)*probePrefactor w hd (left.length+4)) *
    Q'.ofNat (2^(P.animal.support.length+1)*625^(P.animal.support.length+1))) *
    Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd)) (HKPos.one_sub_pos hs)

theorem singleton_budget {left : List Z4Link} (P : ProbeCarrier left) (face : Z4Plaq)
    (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (c b : Q') :
    distanceBudget P (singletonCarrier face) w hd hs c b ≈
      amplitude P w hd hs c b *
        (entropyRate 625 (adjustedCoreRate w hd))^(linfDist P.animal.root face-P.animal.support.length) := by
  simpa only [amplitude, singletonCarrier, countPrefactor, totalProbeSize,
    List.length_append, edgesOf, List.length_cons, List.length_nil, Nat.add_zero,
    Nat.add_sub_add_right] using (distanceBudget_factor P (singletonCarrier face) w hd hs c b)

private theorem amplitude_nonnegative {left : List Z4Link} (P : ProbeCarrier left) (w : Q')
    (hd : heatRemainderBound w < 1) (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {c b : Q'} (hc : (0 : Q') ≤ c) (hb : (0 : Q') ≤ b) : (0 : Q') ≤ amplitude P w hd hs c b :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hc hb) (Q'.mul_nonneg _ _ hc hb))
      (probePrefactor_nonnegative w hd _)) (ClusterCount.ofNat_nonneg _))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

variable {w v W : Q'} (hw0 : (0 : Q') < w) (hwv : w ≤ v) (hvW : v ≤ W) (hW1 : W < (1 : Q'))

local notation "hw1" => Q'.lt_of_le_of_lt hwv (Q'.lt_of_le_of_lt hvW hW1)
local notation "hv0" => Q'.pos_of_lt_of_le hw0 hwv
local notation "hv1" => Q'.lt_of_le_of_lt hvW hW1

/-- An actual finite expectation difference. The zero extension outside the
physical face list is never used by the physical sums below. -/
def singleDefectChange (K extent : Nat) (hKw : headCutoff w ≤ K) (hKv : headCutoff v ≤ K)
    (p : RatPoly) (id : Nat) : Q' :=
  if hi : id ∈ slabPhysicalFaceEdges extent then
    let ids := eraseIndex id (slabPhysicalFaceEdges extent)
    let hids := fun j (hj : j ∈ ids) => mem_of_mem_erase id hj
    let B := polynomialProduct (faceHeatPolynomial w K extent) ids
    let HB := headProduct_certificate hw0 hw1 K extent hKw ids hids
    let hB := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
      (partition_floor hw0 hw1 extent ids hids K hKw)
    let hNew := faceMass_positive hv0 hv1 extent id hi HB K hKv hB
    let hFull := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 (slabPhysicalFaceEdges extent))
      (partition_floor hw0 hw1 extent (slabPhysicalFaceEdges extent) (fun _ hj => hj) K hKw)
    faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B) hNew +
      -(normalizedMoment (blocks extent)
        (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)) p hFull)
  else 0

include hw0 hwv hvW in
private theorem cap_nonnegative : (0 : Q') ≤ scoreCap W w v :=
  Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (inverseHead_nonnegative v)
      (variationCap_nonnegative (Q'.pos_of_lt_of_le hv0 hvW) w v))
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _
      (relativeVariation_nonnegative (Q'.pos_of_lt_of_le hv0 hvW) w v)
      (inverseHead_nonnegative w)) (prefixCap_nonnegative hw0))

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

include hsmall in
theorem singleDefectChange_bound (K extent : Nat) (hKw : headCutoff w ≤ K) (hKv : headCutoff v ≤ K)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p)
    (id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (singleDefectChange hw0 hwv hvW hW1 K extent hKw hKv p id) ≤
      amplitude P w hd hs c (scoreCap W w v) *
        (entropyRate 625 (adjustedCoreRate w hd))^
          (linfDist P.animal.root (slabPlaquetteAt extent id)-P.animal.support.length) := by
  unfold singleDefectChange
  rw [dif_pos hi]
  exact Q'.le_trans' _ _ _
    (full_slab_single_defect_bound hw0 hwv hvW hW1 hsmall hd hs K extent id hi hKw hKv Ip left P hp)
    (Q'.le_of_eqv (singleton_budget P _ w hd hs c (scoreCap W w v)))

include hw0 in
private theorem rate_nonnegative : (0 : Q') ≤ entropyRate 625 (adjustedCoreRate w hd) :=
  Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg _) (adjustedCoreRate_nonnegative (Q'.le_of_lt hw0) hd)

/-- Explicit cutoff- and volume-independent budget for isolated defects.
The d parameter is a lower BLOCK distance, not physical continuum time. -/
def responseBudget {left : List Z4Link} (P : ProbeCarrier left) (c : Q') (d : Nat) : Q' :=
  amplitude P w hd hs c (scoreCap W w v) *
    tailCap (rate_nonnegative hw0 hd) hs P.animal.support.length d

include hwv hvW hW1 hsmall in
/-- Sum of the absolute changes, each made separately in the SAME full
original slab. A finite spatial tail has the same volume-free budget. -/
theorem isolated_defect_tail_bound (K extent : Nat) (hKw : headCutoff w ≤ K) (hKv : headCutoff v ≤ K)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (d : Nat) (hfar : ∀ id, id ∈ ids → d ≤ blockIndex P.animal.root
      (entropyRate 625 (adjustedCoreRate w hd)) P.animal.support.length (slabPlaquetteAt extent id)) :
    listQSum (fun id => Q'.abs (singleDefectChange hw0 hwv hvW hW1 K extent hKw hKv p id)) ids ≤
      responseBudget (v := v) (W := W) hw0 hd hs P c d := by
  let r := entropyRate 625 (adjustedCoreRate w hd)
  let A := amplitude P w hd hs c (scoreCap W w v)
  let f := fun face => r^(linfDist P.animal.root face-P.animal.support.length)
  have hA : (0 : Q') ≤ A := amplitude_nonnegative P w hd hs Ip.nonnegative (cap_nonnegative hw0 hwv hvW)
  have hm := CayleyPruferInjection.nodup_map_of_injOn (slabPlaquetteAt extent) ids hn
    (fun i hi j hj he => slabPlaquetteAt_injective_on_physical (hids i hi) (hids j hj) he)
  have ht := finite_tail_bound (rate_nonnegative hw0 hd) hs P.animal.root P.animal.support.length d
    (ids.map (slabPlaquetteAt extent)) hm (by
      intro face hf
      obtain ⟨id, hi, rfl⟩ := List.mem_map.mp hf
      exact hfar id hi)
  rw [sum_map] at ht
  exact Q'.le_trans' _ _ _ (sum_le_on _ _ ids (fun id hi =>
    singleDefectChange_bound hw0 hwv hvW hW1 hsmall hd hs K extent hKw hKv Ip left P hp id (hids id hi)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (listQSum_mul_left A (fun id => f (slabPlaquetteAt extent id)) ids))
      (Q'.mul_le_mul_of_nonneg_left _ _ A ht hA))

include hwv hvW hW1 hsmall in
/-- The entire finite slab, with NO factor proportional to its number of faces. -/
theorem full_isolated_defect_sum_bound (K extent : Nat) (hKw : headCutoff w ≤ K) (hKv : headCutoff v ≤ K)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) :
    listQSum (fun id => Q'.abs (singleDefectChange hw0 hwv hvW hW1 K extent hKw hKv p id))
      (slabPhysicalFaceEdges extent) ≤ responseBudget (v := v) (W := W) hw0 hd hs P c 0 :=
  isolated_defect_tail_bound hw0 hwv hvW hW1 hsmall hd hs K extent hKw hKv Ip left P hp
    (slabPhysicalFaceEdges extent) (CayleyParentInj.range_nodup _) (fun _ hi => hi) 0 (fun _ _ => Nat.zero_le _)

/-- Computed location cutoff for the sum of actual isolated responses. -/
def responseRadius {left : List Z4Link} (P : ProbeCarrier left) (c epsilon : Q') : Nat :=
  radiusCutoff (rate_nonnegative hw0 hd) hs P.animal.support.length
    (amplitude P w hd hs c (scoreCap W w v)) epsilon

include hwv hvW hW1 hsmall in
/-- All defects outside the computed radius have total absolute response at
most epsilon, uniformly in slab extent and the allowed heat cutoff. -/
theorem isolated_defect_tail_small (K extent : Nat) (hKw : headCutoff w ≤ K) (hKv : headCutoff v ≤ K)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (hfar : ∀ id, id ∈ ids → responseRadius (v := v) (W := W) hw0 hd hs P c epsilon ≤
      linfDist P.animal.root (slabPlaquetteAt extent id)) :
    listQSum (fun id => Q'.abs (singleDefectChange hw0 hwv hvW hW1 K extent hKw hKv p id)) ids ≤ epsilon := by
  let A := amplitude P w hd hs c (scoreCap W w v)
  let d := blockCutoff (rate_nonnegative hw0 hd) hs P.animal.support.length A epsilon
  have hf := fun id (hi : id ∈ ids) =>
    radiusCutoff_block_le (rate_nonnegative hw0 hd) hs P.animal.root (slabPlaquetteAt extent id)
      P.animal.support.length A epsilon (hfar id hi)
  exact Q'.le_trans' _ _ _
    (isolated_defect_tail_bound hw0 hwv hvW hW1 hsmall hd hs K extent hKw hKv Ip left P hp ids hn hids d hf)
    (scaled_tailCap_small (rate_nonnegative hw0 hd) hs
      (amplitude_nonnegative P w hd hs Ip.nonnegative (cap_nonnegative hw0 hwv hvW)) he
      P.animal.support.length d (Nat.le_refl _))

end YMGap.Continuum.BF4ExactSlabSummedCouplingDefects

#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingDefects.amplitude
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingDefects.singleton_budget
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingDefects.singleDefectChange
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingDefects.singleDefectChange_bound
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingDefects.responseBudget
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingDefects.isolated_defect_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingDefects.full_isolated_defect_sum_bound
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingDefects.responseRadius
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingDefects.isolated_defect_tail_small
