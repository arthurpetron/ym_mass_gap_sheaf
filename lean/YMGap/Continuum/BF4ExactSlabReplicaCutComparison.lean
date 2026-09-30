/-
# Original two-copy action comparison pays only for crossing faces

For a selected physical link set, partial replica exchange changes only
plaquettes meeting both sides. A constructed square certificate gives
  ell^(2b) W(x)W(y) <= U^(2b) W(z)W(eta),
under every certified nonnegative insertion, with the SAME original action.
Here b is the actual crossing-face count, ell=headFloor(w), U=prefixCap(w).
The bound is uniform in late cutoff, not in nome or the size of the cut.
The conditional edge-flow/normalizer and path-variance joins are not proved
here. In particular this is not a coercivity, physical-time or gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabReplicaCutLocality
import YMGap.Continuum.BF4ExactSlabReplicaCutArea
import YMGap.Continuum.SU2QuaternionReplicaPairBounds
import YMGap.Continuum.QuaternionHaarChangedProductComparison
import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
import YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder

namespace YMGap.Continuum.BF4ExactSlabReplicaCutComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabReplicaCutLocality
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionReplicaPairBounds
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarChangedProductComparison
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder (haar_order)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local notation:max "faces" extent:arg => slabPhysicalFaceEdges extent

/-- Actual crossing-face count, not the total volume face count. -/
def crossingCount (extent : Nat) (selected : List Z4Link) : Nat :=
  ((faces extent).filter (crossingMask extent selected)).length

/-- The count actually consumed by the action comparison is bounded by the
two-layer spatial area for a time-ordered link selection. -/
theorem crossingCount_le_area (extent time : Nat) (selected : List Z4Link)
    (hbelow : ∀ link, link ∈ boundaryCompleteSlabLinks extent →
      link.1.2.2.2 < time → link ∈ selected)
    (habove : ∀ link, link ∈ boundaryCompleteSlabLinks extent →
      time < link.1.2.2.2 → link ∉ selected) :
    crossingCount extent selected ≤ 12 * (extent+1)^3 := by
  rw [crossingCount, BF4ExactSlabReplicaCutArea.crossingMask_length_pin]
  exact BF4ExactSlabReplicaCutArea.cutCrossingFaces_length_le_area
    extent time selected hbelow habove

def originalPair (w : Q') (K extent : Nat) : RatPoly :=
  let W := polynomialProduct (faceHeatPolynomial w K extent) (faces extent)
  polyMul W (liftBoundary (blocks extent) W)

def swappedPair (w : Q') (K extent : Nat) (selected : List Z4Link) : RatPoly :=
  reindexQuaternionPolynomial (cutSwap extent selected) (originalPair w K extent)

private theorem factorProduct_map {A : Type} (f : A → RatPoly) : ∀ ids : List A,
    factorProduct (ids.map f) = polynomialProduct f ids
  | [] => rfl
  | i::ids => by
      change polyMul (f i) (factorProduct (ids.map f)) = _
      rw [factorProduct_map f ids]
      rfl

private theorem changedCount_map {A B : Type} (f : A → B) (mask : B → Bool) :
    ∀ ids : List A, changedCount mask (ids.map f) = changedCount (fun i => mask (f i)) ids
  | [] => rfl
  | i::ids => by
      simp only [List.map_cons, changedCount, changedCount_map f mask ids]

private theorem map_attach {A B : Type} (ids : List A) (f : A → B) :
    ids.attach.map (fun i => f i.val) = ids.map f := by
  change ids.attach.map (f ∘ Subtype.val) = ids.map f
  rw [← List.map_map, List.attach_map_subtype_val]

private theorem reindex_product {A : Type} {n : Nat} (s : QuaternionBlockInvolution n)
    (f : A → RatPoly) : ∀ ids : List A,
    HaarCarrierEqv n (polynomialProduct (fun i => reindexQuaternionPolynomial s (f i)) ids)
      (reindexQuaternionPolynomial s (polynomialProduct f ids))
  | [] => (carrierOfPrefix (reindex_supported s polyOne) (supported_one n)
      (reindexQuaternionPolynomial_character_prefix s polyZero 0)).symm
  | i::ids => by
      change HaarCarrierEqv n (polyMul (reindexQuaternionPolynomial s (f i))
        (polynomialProduct (fun i => reindexQuaternionPolynomial s (f i)) ids))
        (reindexQuaternionPolynomial s (polyMul (f i) (polynomialProduct f ids)))
      rw [reindexQuaternionPolynomial_mul]
      exact HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _) (reindex_product s f ids)

private theorem pairProduct_supported (w : Q') (K extent : Nat) : ∀ ids : List Nat,
    SupportedQuaternionBlocks (blocks extent + blocks extent)
      (polynomialProduct (facePair w K extent) ids)
  | [] => supported_one _
  | i::ids => supported_polyMul (pair_supported _ (heatFace_supported w K extent i))
      (pairProduct_supported w K extent ids)

theorem originalPair_pin (w : Q') (K extent : Nat) :
    HaarCarrierEqv (blocks extent + blocks extent)
      (polynomialProduct (facePair w K extent) (faces extent)) (originalPair w K extent) :=
  facePair_product_pin w K extent (faces extent)

theorem swappedPair_pin (w : Q') (K extent : Nat) (selected : List Z4Link) :
    HaarCarrierEqv (blocks extent + blocks extent)
      (polynomialProduct (swappedFacePair w K extent selected) (faces extent))
      (swappedPair w K extent selected) :=
  (reindex_product (cutSwap extent selected) (facePair w K extent) (faces extent)).trans
    (reindex_carrier (cutSwap extent selected) (pairProduct_supported w K extent _)
      (pair_supported _ (heatProduct_supported w K extent _)) (originalPair_pin w K extent))

/-- Replica exchange preserves the full original pair partition, not just
the individual face integrals. -/
theorem swappedPair_mass_pin (w : Q') (K extent : Nat) (selected : List Z4Link) :
    Q'.eqv (quaternionHaar (blocks extent + blocks extent) (swappedPair w K extent selected))
      (quaternionHaar (blocks extent + blocks extent) (originalPair w K extent)) :=
  quaternionHaar_reindex (cutSwap extent selected) _
    (pair_supported _ (heatProduct_supported w K extent _))

private def factorComparison {n : Nat} {p q : RatPoly} (ell U : Q')
    (hell : (0 : Q') ≤ ell) (hU : (0 : Q') ≤ U)
    (Q : Certificate n (polyAdd q (polyNeg (cap ell))))
    (P : Certificate n (polyAdd (cap U) (polyNeg p))) :
    Certificate n (polyAdd (polyMul (cap U) q) (polyNeg (polyMul (cap ell) p))) :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2))))
    (.add (.mul (.var 0) (.add (.var 3) (.neg (.var 1))))
      (.mul (.var 1) (.add (.var 0) (.neg (.var 2)))))
    (by decide) (fun | 0 => cap U | 1 => cap ell | 2 => p | _ => q))
    (((Certificate.constant n U hU).mul Q).add ((Certificate.constant n ell hell).mul P))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

/-- The one-face comparison is constructed from the ACTUAL finite-prefix
floor and cap. It does not assume positivity of the unknown action ratio. -/
def facePairComparison (selected : List Z4Link) (id : Nat) (hi : id ∈ faces extent) :
    Certificate (blocks extent + blocks extent)
      (polyAdd (polyMul (cap (prefixCap w * prefixCap w)) (swappedFacePair w K extent selected id))
        (polyNeg (polyMul (cap (headFloor w * headFloor w)) (facePair w K extent id)))) :=
  factorComparison _ _
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (headFloor_positive hw0 hw1))
      (Q'.le_of_lt (headFloor_positive hw0 hw1)))
    (Q'.mul_nonneg _ _ (prefixCap_nonnegative hw0) (prefixCap_nonnegative hw0))
    (reindexedPairFloorCertificate _ (heatFace_supported w K extent id)
      (faceHead_certificate hw0 hw1 K extent id hi hK) _
      (Q'.le_of_lt (headFloor_positive hw0 hw1))
      (faceHead_floorCertificate hw0 hw1 K extent id hi hK) (cutSwap extent selected))
    (pairCapCertificate _ (heatFace_supported w K extent id)
      (faceHead_certificate hw0 hw1 K extent id hi hK) _ (prefixCap_nonnegative hw0)
      (facePrefixInterval hw0 hw1 K extent id hi).upper)

set_option maxHeartbeats 800000 in
/-- Only crossing faces incur a scalar comparison loss. All uncrossed
factors, including every bulk spectator, cancel by exact carrier equality. -/
def cutComparisonCertificate (selected : List Z4Link) :
    Certificate (blocks extent + blocks extent)
      (polyAdd
        (polySmul ((prefixCap w * prefixCap w)^crossingCount extent selected)
          (swappedPair w K extent selected))
        (polyNeg (polySmul ((headFloor w * headFloor w)^crossingCount extent selected)
          (originalPair w K extent)))) := by
  let fs := (faces extent).attach
  let mask := fun i : {id : Nat // id ∈ faces extent} => crossingMask extent selected i.val
  have hcount : changedCount mask fs = crossingCount extent selected := by
    rw [← changedCount_map Subtype.val (crossingMask extent selected), List.attach_map_subtype_val,
      changedCount_eq_filter_length]
    rfl
  have H := masked_product_gap_certificate_cap fs mask
    (fun i => facePair w K extent i.val) (fun i => swappedFacePair w K extent selected i.val)
    (headFloor w * headFloor w) (prefixCap w * prefixCap w)
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (headFloor_positive hw0 hw1))
      (Q'.le_of_lt (headFloor_positive hw0 hw1)))
    (Q'.mul_nonneg _ _ (prefixCap_nonnegative hw0) (prefixCap_nonnegative hw0))
    (fun i => pairCertificate _ (heatFace_supported w K extent i.val)
      (faceHead_certificate hw0 hw1 K extent i.val i.property hK))
    (fun i => reindexedPairCertificate _ (heatFace_supported w K extent i.val)
      (faceHead_certificate hw0 hw1 K extent i.val i.property hK) (cutSwap extent selected))
    (fun i _ => facePairComparison hw0 hw1 K extent hK selected i.val i.property)
    (fun i hi => (uncrossed_face_pair w K extent selected i.val hi).symm)
  dsimp only [fs] at H
  rw [map_attach, map_attach, factorProduct_map, factorProduct_map, hcount] at H
  exact .transport (HaarCarrierEqv.add
    (HaarCarrierEqv.smul _ (swappedPair_pin w K extent selected).symm)
    (HaarCarrierEqv.neg (HaarCarrierEqv.smul _ (originalPair_pin w K extent).symm))) H

private theorem haar_smul_left (n : Nat) (c : Q') (p r : RatPoly) :
    Q'.eqv (quaternionHaar n (polyMul (polySmul c p) r))
      (c * quaternionHaar n (polyMul p r)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p r))
    (quaternionHaar_polySmul n c (polyMul p r))

include hw0 hw1 hK in
/-- Quantitative comparison under every certified nonnegative insertion;
in particular the test may depend jointly on both copies. -/
theorem weighted_cut_comparison (selected : List Z4Link) {r : RatPoly}
    (R : Certificate (blocks extent + blocks extent) r) :
    (headFloor w * headFloor w)^crossingCount extent selected *
        quaternionHaar (blocks extent + blocks extent) (polyMul (originalPair w K extent) r) ≤
      (prefixCap w * prefixCap w)^crossingCount extent selected *
        quaternionHaar (blocks extent + blocks extent) (polyMul (swappedPair w K extent selected) r) :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_smul_left _ _ _ _))
    (Q'.le_trans' _ _ _ (haar_order (cutComparisonCertificate hw0 hw1 K extent hK selected) R)
      (Q'.le_of_eqv (haar_smul_left _ _ _ _)))

#print axioms crossingCount
#print axioms crossingCount_le_area
#print axioms originalPair
#print axioms swappedPair
#print axioms originalPair_pin
#print axioms swappedPair_pin
#print axioms swappedPair_mass_pin
#print axioms facePairComparison
#print axioms cutComparisonCertificate
#print axioms weighted_cut_comparison

end YMGap.Continuum.BF4ExactSlabReplicaCutComparison
