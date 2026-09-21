/-
# A spatially weighted path through the original two-nome actions

Each selected face is changed once, from u to v. The other selected faces
already at v remain in the actual intermediate background; all remaining
faces stay at u. Positivity and normalized endpoint identities are constructed
at every step. The telescope pays the individual distance budgets, not one
constant times the number of faces.

The common explicit small-nome ceiling W and the two late-cutoff thresholds
are retained. This is a finite original-action path, not continuum control.
-/
import YMGap.Continuum.BF4ExactSlabHeterogeneousCouplingResponse
import YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule
import YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence

namespace YMGap.Continuum.BF4ExactSlabSpatialCouplingPath

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison
open YMGap.Continuum.BF4ExactSlabHeterogeneousCouplingResponse
open YMGap.Continuum.BF4ExactSlabTwoNomeFaceSchedule
open YMGap.Continuum.BF4ExactSlabCouplingScoreBound (scoreCap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability (faceMass faceMoment faceMass_positive)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay (distanceBudget)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm mem_of_mem_erase)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

variable {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v) (hvW : v ≤ W) (hW1 : W < (1 : Q'))
  (hsmall : heatRatio W ≤ HalfPow.half) (hd : heatRemainderBound W < 1)

local notation "hu1" => Q'.lt_of_le_of_lt huv (Q'.lt_of_le_of_lt hvW hW1)
local notation "hv0" => Q'.pos_of_lt_of_le hu0 huv
local notation "hv1" => Q'.lt_of_le_of_lt hvW hW1
local notation "hW0" => Q'.le_of_lt (Q'.pos_of_lt_of_le hv0 hvW)

/-- Every intermediate value is the normalized original varying heat product. -/
def value (K extent : Nat) (chosen ambient : List Nat)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) (p : RatPoly) : Q' :=
  normalizedMoment (blocks extent) (density u v K extent chosen ambient) p
    (partition_positive (nomeAt u v chosen) (fun _ => K) extent
      (fun id _ => nomeAt_nonnegative (Q'.le_of_lt hu0) (Q'.le_of_lt hv0) chosen id)
      (fun id _ => nomeAt_le (Q'.le_trans' _ _ _ huv hvW) hvW chosen id)
      (Q'.le_of_lt hW1) hsmall hd ambient hphys)

private theorem normalized_face_pin (w : Q') (K extent id : Nat) (B p : RatPoly)
    (h : (0 : Q') < faceMass w K extent id B) :
    normalizedMoment (blocks extent) (polyMul B (faceHeatPolynomial w K extent id)) p h ≈
      faceMoment w K extent id B p * Q'.recipPos (faceMass w K extent id B) h :=
  Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff
    ((RatPolyCoeffEqv.mul_comm _ p).trans (RatPolyCoeffEqv.mul_assoc p B _).symm))

include hu0 huv hvW hW1 hsmall hd in
/-- One selected face changes in the same intermediate law at both endpoints. -/
theorem add_face_bound (hs : entropyRate 625 (adjustedCoreRate W hd) < 1)
    (K extent : Nat) (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
    (chosen ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hi : id ∈ ambient) (hnot : id ∉ chosen)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) :
    Q'.abs (value hu0 huv hvW hW1 hsmall hd K extent (id::chosen) ambient hphys p +
      -(value hu0 huv hvW hW1 hsmall hd K extent chosen ambient hphys p)) ≤
      distanceBudget P (singletonCarrier (slabPlaquetteAt extent id)) W hd hs c (scoreCap W u v) := by
  let w := nomeAt u v chosen
  let ids := eraseIndex id ambient
  have hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent := fun j hj => hphys j (mem_of_mem_erase id hj)
  have hnids : ids.Nodup := (List.nodup_cons.mp ((select_perm id hi).nodup hn)).2
  have hw0 : ∀ j, j ∈ slabPhysicalFaceEdges extent → (0 : Q') ≤ w j :=
    fun j _ => nomeAt_nonnegative (Q'.le_of_lt hu0) (Q'.le_of_lt hv0) chosen j
  have hwW : ∀ j, j ∈ slabPhysicalFaceEdges extent → w j ≤ W :=
    fun j _ => nomeAt_le (Q'.le_trans' _ _ _ huv hvW) hvW chosen j
  let B := density u v K extent chosen ids
  let HB := productCertificate w (fun _ => K) extent hw0 hwW (Q'.le_of_lt hW1) hsmall (Q'.le_of_lt hd) ids hids
  let hB := partition_positive w (fun _ => K) extent hw0 hwW (Q'.le_of_lt hW1) hsmall hd ids hids
  let hOld := faceMass_positive hu0 hu1 extent id (hphys id hi) HB K hKu hB
  let hNew := faceMass_positive hv0 hv1 extent id (hphys id hi) HB K hKv hB
  have hOldPin : value hu0 huv hvW hW1 hsmall hd K extent chosen ambient hphys p ≈
      faceMoment u K extent id B p * Q'.recipPos (faceMass u K extent id B) hOld :=
    Q'.eqv_trans _ _ _ (normalizedMoment_congr _ hOld
      (density_old_pin u v K extent chosen ambient id hi hnot) (RatPolyCoeffEqv.refl p))
      (normalized_face_pin u K extent id B p hOld)
  have hNewPin : value hu0 huv hvW hW1 hsmall hd K extent (id::chosen) ambient hphys p ≈
      faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B) hNew :=
    Q'.eqv_trans _ _ _ (normalizedMoment_congr _ hNew
      (density_add_pin u v K extent chosen ambient id hn hi) (RatPolyCoeffEqv.refl p))
      (normalized_face_pin v K extent id B p hNew)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
    (Q'.add_eqv_congr' hNewPin (Q'.neg_eqv_congr _ _ hOldPin))))
    (background_response_bound w (fun _ => K) extent hW0 (Q'.le_of_lt hW1) hw0 hwW hsmall hd hs
      hu0 huv hvW hW1 K id (hphys id hi) hKu hKv ids hnids hids Ip left P hp)

private theorem abs_chain {a b c x y : Q'} (hab : Q'.abs (a + -b) ≤ x) (hbc : Q'.abs (b + -c) ≤ y) :
    Q'.abs (a + -c) ≤ x+y := by
  have ht : a + -c ≈ (a + -b)+(b + -c) :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2)))) (by decide)
      (fun | 0 => a | 1 => b | _ => c)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr ht))
    (Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.add_le_add hab hbc))

include hu0 huv hvW hW1 hsmall hd in
/-- A genuine simultaneous finite change, bounded by the sum of spatial costs
of its actual successive changes. No derivative or linearization is assumed. -/
theorem path_bound (hs : entropyRate 625 (adjustedCoreRate W hd) < 1)
    (K extent : Nat) (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (Ip : Interval (blocks extent) p c)
    (left : List Z4Link) (P : ProbeCarrier left) (hp : LinkLocal extent left p) :
    ∀ chosen : List Nat, chosen.Nodup → (∀ id, id ∈ chosen → id ∈ ambient) →
    Q'.abs (value hu0 huv hvW hW1 hsmall hd K extent chosen ambient hphys p +
      -(value hu0 huv hvW hW1 hsmall hd K extent [] ambient hphys p)) ≤
        listQSum (fun id => distanceBudget P (singletonCarrier (slabPlaquetteAt extent id)) W hd hs c (scoreCap W u v)) chosen
  | [], _, _ => Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_neg_self_eqv _))
  | id::chosen, hchosen, hsub =>
      abs_chain
        (add_face_bound hu0 huv hvW hW1 hsmall hd hs K extent hKu hKv chosen ambient hn hphys id
          (hsub id List.mem_cons_self) (List.nodup_cons.mp hchosen).1 Ip left P hp)
        (path_bound hs K extent hKu hKv ambient hn hphys Ip left P hp chosen (List.nodup_cons.mp hchosen).2
          (fun j hj => hsub j (List.mem_cons_of_mem id hj)))

end YMGap.Continuum.BF4ExactSlabSpatialCouplingPath

#print axioms YMGap.Continuum.BF4ExactSlabSpatialCouplingPath.value
#print axioms YMGap.Continuum.BF4ExactSlabSpatialCouplingPath.add_face_bound
#print axioms YMGap.Continuum.BF4ExactSlabSpatialCouplingPath.path_bound
