/-
# A volume-free comparison along an actual original-action coupling path

The same-measure normalized score estimate is telescoped through the actual
intermediate two-nome products. The proved four-dimensional geometric sum
then bounds this ONE simultaneous change, with no face-count loss. An
explicit radius makes all selected far-away changes collectively small.

All nomes remain under the displayed guarded ceiling W. The result retains
the two endpoint nomes, probe bounds and support, and the late-cutoff guards.
It proves neither a weak-coupling trajectory nor continuum survival or QFT.
-/
import YMGap.Continuum.BF4ExactSlabSpatialCouplingPath
import YMGap.Continuum.BF4ExactSlabSummedCouplingDefects

namespace YMGap.Continuum.BF4ExactSlabSummedCouplingPath

set_option autoImplicit false
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
open YMGap.Continuum.BF4ExactSlabCouplingScoreBound
open YMGap.Continuum.BF4ExactSlabSpatialCouplingPath
open YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule
open YMGap.Continuum.BF4ExactSlabSummedCouplingDefects (amplitude singleton_budget)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
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

variable {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v) (hvW : v ≤ W) (hW1 : W < (1 : Q'))
  (hsmall : heatRatio W ≤ HalfPow.half) (hd : heatRemainderBound W < 1)
  (hs : entropyRate 625 (adjustedCoreRate W hd) < 1)

local notation "hv0" => Q'.pos_of_lt_of_le hu0 huv
local notation "hW0" => Q'.pos_of_lt_of_le hv0 hvW
local notation "hu1" => Q'.lt_of_le_of_lt huv (Q'.lt_of_le_of_lt hvW hW1)
local notation "hv1" => Q'.lt_of_le_of_lt hvW hW1

include hu0 huv hvW in
private theorem cap_nonnegative : (0 : Q') ≤ scoreCap W u v :=
  Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (inverseHead_nonnegative v) (variationCap_nonnegative hW0 u v))
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (relativeVariation_nonnegative hW0 u v)
      (inverseHead_nonnegative u)) (prefixCap_nonnegative hu0))

include hu0 huv hvW in
private theorem rate_nonnegative : (0 : Q') ≤ entropyRate 625 (adjustedCoreRate W hd) :=
  Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg _) (adjustedCoreRate_nonnegative (Q'.le_of_lt hW0) hd)

include hu0 huv hvW in
private theorem amplitude_nonnegative {left : List Z4Link} (P : ProbeCarrier left)
    {c : Q'} (hc : (0 : Q') ≤ c) : (0 : Q') ≤ amplitude P W hd hs c (scoreCap W u v) := by
  have hb := cap_nonnegative hu0 huv hvW
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hc hb) (Q'.mul_nonneg _ _ hc hb))
      (probePrefactor_nonnegative W hd _)) (ClusterCount.ofNat_nonneg _))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- Explicit budget for the ONE simultaneous change. No extent, heat cutoff
or chosen-face count occurs. The index d is a block-distance lower bound. -/
def pathBudget {left : List Z4Link} (P : ProbeCarrier left) (c : Q') (d : Nat) : Q' :=
  amplitude P W hd hs c (scoreCap W u v) *
    tailCap (rate_nonnegative hu0 huv hvW hd) hs P.animal.support.length d

include hW1 hsmall in
/-- All selected faces are changed in a single normalized original law.
The spatial costs of its successive changes are summed with a volume-free bound. -/
theorem path_tail_bound (K extent : Nat) (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p)
    (chosen : List Nat) (hc : chosen.Nodup) (hsub : ∀ id, id ∈ chosen → id ∈ ambient)
    (d : Nat) (hfar : ∀ id, id ∈ chosen → d ≤ blockIndex P.animal.root
      (entropyRate 625 (adjustedCoreRate W hd)) P.animal.support.length (slabPlaquetteAt extent id)) :
    Q'.abs (value hu0 huv hvW hW1 hsmall hd K extent chosen ambient hphys p +
      -(value hu0 huv hvW hW1 hsmall hd K extent [] ambient hphys p)) ≤
      pathBudget hu0 huv hvW hd hs P c d := by
  let r := entropyRate 625 (adjustedCoreRate W hd)
  let A := amplitude P W hd hs c (scoreCap W u v)
  let f := fun face => r^(linfDist P.animal.root face-P.animal.support.length)
  have hA : (0 : Q') ≤ A := amplitude_nonnegative hu0 huv hvW hd hs P Ip.nonnegative
  have hm := CayleyPruferInjection.nodup_map_of_injOn (slabPlaquetteAt extent) chosen hc
    (fun i hi j hj he => slabPlaquetteAt_injective_on_physical
      (hphys i (hsub i hi)) (hphys j (hsub j hj)) he)
  have ht := finite_tail_bound (rate_nonnegative hu0 huv hvW hd) hs P.animal.root P.animal.support.length d
    (chosen.map (slabPlaquetteAt extent)) hm (by
      intro face hf
      obtain ⟨id, hi, rfl⟩ := List.mem_map.mp hf
      exact hfar id hi)
  rw [sum_map] at ht
  have hpw := path_bound hu0 huv hvW hW1 hsmall hd hs K extent hKu hKv ambient hn hphys Ip left P hp chosen hc hsub
  exact Q'.le_trans' _ _ _ hpw
    (Q'.le_trans' _ _ _ (sum_le_on _ _ chosen (fun id _ =>
      Q'.le_of_eqv (singleton_budget P _ W hd hs c (scoreCap W u v))))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (listQSum_mul_left A (fun id => f (slabPlaquetteAt extent id)) chosen))
        (Q'.mul_le_mul_of_nonneg_left _ _ A ht hA)))

include hW1 hsmall in
/-- Changing every factor of the ambient original action costs the same
volume-free budget, not the budget multiplied by its number of faces. -/
theorem all_faces_bound (K extent : Nat) (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) :
    Q'.abs (value hu0 huv hvW hW1 hsmall hd K extent ambient ambient hphys p +
      -(value hu0 huv hvW hW1 hsmall hd K extent [] ambient hphys p)) ≤
      pathBudget hu0 huv hvW hd hs P c 0 :=
  path_tail_bound hu0 huv hvW hW1 hsmall hd hs K extent hKu hKv ambient hn hphys Ip left P hp
    ambient hn (fun _ hi => hi) 0 (fun _ _ => Nat.zero_le _)

/-- Computed radius for a simultaneous finite set of distant changes. -/
def pathRadius {left : List Z4Link} (P : ProbeCarrier left) (c epsilon : Q') : Nat :=
  radiusCutoff (rate_nonnegative hu0 huv hvW hd) hs P.animal.support.length
    (amplitude P W hd hs c (scoreCap W u v)) epsilon

include hW1 hsmall in
/-- One explicit radius controls all selected changes together, uniformly in
ambient slab extent and every heat cutoff above both endpoint thresholds. -/
theorem path_tail_small (K extent : Nat) (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p)
    (chosen : List Nat) (hc : chosen.Nodup) (hsub : ∀ id, id ∈ chosen → id ∈ ambient)
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (hfar : ∀ id, id ∈ chosen → pathRadius hu0 huv hvW hd hs P c epsilon ≤
      linfDist P.animal.root (slabPlaquetteAt extent id)) :
    Q'.abs (value hu0 huv hvW hW1 hsmall hd K extent chosen ambient hphys p +
      -(value hu0 huv hvW hW1 hsmall hd K extent [] ambient hphys p)) ≤ epsilon := by
  let A := amplitude P W hd hs c (scoreCap W u v)
  let d := blockCutoff (rate_nonnegative hu0 huv hvW hd) hs P.animal.support.length A epsilon
  have hf := fun id (hi : id ∈ chosen) =>
    radiusCutoff_block_le (rate_nonnegative hu0 huv hvW hd) hs P.animal.root (slabPlaquetteAt extent id)
      P.animal.support.length A epsilon (hfar id hi)
  exact Q'.le_trans' _ _ _
    (path_tail_bound hu0 huv hvW hW1 hsmall hd hs K extent hKu hKv ambient hn hphys Ip left P hp chosen hc hsub d hf)
    (scaled_tailCap_small (rate_nonnegative hu0 huv hvW hd) hs
      (amplitude_nonnegative hu0 huv hvW hd hs P Ip.nonnegative) he P.animal.support.length d (Nat.le_refl _))

include hsmall in
/-- Endpoints are literally the original homogeneous full-slab heat products.
Their positive masses are constructed by the existing retained-head theorem. -/
theorem full_slab_original_change_bound (K extent : Nat) (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) :
    let ids := slabPhysicalFaceEdges extent
    let hU := Q'.pos_of_lt_of_le (partitionFloor_pos hu0 hu1 ids)
      (partition_floor hu0 hu1 extent ids (fun _ hi => hi) K hKu)
    let hV := Q'.pos_of_lt_of_le (partitionFloor_pos hv0 hv1 ids)
      (partition_floor hv0 hv1 extent ids (fun _ hi => hi) K hKv)
    Q'.abs (normalizedMoment (blocks extent) (polynomialProduct (faceHeatPolynomial v K extent) ids) p hV +
      -(normalizedMoment (blocks extent) (polynomialProduct (faceHeatPolynomial u K extent) ids) p hU)) ≤
      pathBudget hu0 huv hvW hd hs P c 0 := by
  dsimp only
  let ids := slabPhysicalFaceEdges extent
  let hU := Q'.pos_of_lt_of_le (partitionFloor_pos hu0 hu1 ids)
    (partition_floor hu0 hu1 extent ids (fun _ hi => hi) K hKu)
  let hV := Q'.pos_of_lt_of_le (partitionFloor_pos hv0 hv1 ids)
    (partition_floor hv0 hv1 extent ids (fun _ hi => hi) K hKv)
  have hOld : value hu0 huv hvW hW1 hsmall hd K extent [] ids (fun _ hi => hi) p ≈
      normalizedMoment (blocks extent) (polynomialProduct (faceHeatPolynomial u K extent) ids) p hU :=
    normalizedMoment_congr _ hU (density_nil u v K extent ids) (RatPolyCoeffEqv.refl p)
  have hNew : value hu0 huv hvW hW1 hsmall hd K extent ids ids (fun _ hi => hi) p ≈
      normalizedMoment (blocks extent) (polynomialProduct (faceHeatPolynomial v K extent) ids) p hV :=
    normalizedMoment_congr _ hV (density_all u v K extent ids) (RatPolyCoeffEqv.refl p)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr
    (Q'.add_eqv_congr' hNew (Q'.neg_eqv_congr _ _ hOld))))
    (all_faces_bound hu0 huv hvW hW1 hsmall hd hs K extent hKu hKv ids
      (CayleyParentInj.range_nodup _) (fun _ hi => hi) Ip left P hp)

end YMGap.Continuum.BF4ExactSlabSummedCouplingPath

#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingPath.pathBudget
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingPath.path_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingPath.all_faces_bound
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingPath.pathRadius
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingPath.path_tail_small
#print axioms YMGap.Continuum.BF4ExactSlabSummedCouplingPath.full_slab_original_change_bound
