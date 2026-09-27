/-
# Signed original-action comparison charging only shared faces

Retain EVERY face not touching both selected link lists. The original full
weight is exactly this retained weight times the shared-face weight. The
proved positive floor/cap of each shared heat factor yields a comparison
for arbitrary certified positive tests, hence every supported square.
Polarization then gives a signed mixed-form estimate for arbitrary tests,
including tests depending on all spectator links.

The exponent is the actual shared-face count, not the union collar size.
The retained reference omits shared factors and is NOT the original action;
their coefficient identity and comparison are proved explicitly. No product
conditional projection, signed conditional-residual bound, useful scaling
rate, reflected OS operator or mass gap is inferred from these form bounds.
-/

import YMGap.Continuum.BF4ExactSlabSharedFaceRegion
import YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
import YMGap.Continuum.QuaternionHaarSignedFormComparison

namespace YMGap.Continuum.BF4ExactSlabSharedFaceComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabSharedFaceRegion
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarSignedFormComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

def sharedHeat (w : Q') (K extent : Nat) (A B : List Z4Link) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (sharedIds extent A B)

def retainedHeat (w : Q') (K extent : Nat) (A B : List Z4Link) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (retainedIds extent A B)

def sharedLower (w : Q') (extent : Nat) (A B : List Z4Link) : Q' :=
  (headFloor w) ^ sharedCount extent A B

def sharedUpper (w : Q') (extent : Nat) (A B : List Z4Link) : Q' :=
  (prefixCap w) ^ sharedCount extent A B

theorem sharedLower_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (A B : List Z4Link) : (0 : Q') < sharedLower w extent A B :=
  HKPos.pow_pos (headFloor_positive hw0 hw1) _

/-- No original factor is lost: only the partition into retained/shared changes. -/
theorem fullWeight_split (w : Q') (K extent : Nat) (A B : List Z4Link) :
    RatPolyCoeffEqv (fullWeight w K extent)
      (polyMul (retainedHeat w K extent A B) (sharedHeat w K extent A B)) :=
  (polynomialProduct_perm _ (shared_partition extent A B).symm).trans
    ((polynomialProduct_append _ (sharedIds extent A B) (retainedIds extent A B)).trans
      (RatPolyCoeffEqv.mul_comm _ _))

def retainedHeat_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (A B : List Z4Link) :
    Certificate (blocks extent) (retainedHeat w K extent A B) :=
  headProduct_certificate hw0 hw1 K extent hK _ (fun _ hi => retained_physical hi)

private theorem weighted_split (w : Q') (K extent : Nat) (A B : List Z4Link)
    (q : RatPoly) :
    quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ≈
      quaternionHaar (blocks extent)
        (polyMul (polyMul q (retainedHeat w K extent A B)) (sharedHeat w K extent A B)) :=
  haar_of_coeff (((RatPolyCoeffEqv.refl q).mul (fullWeight_split w K extent A B)).trans
    (RatPolyCoeffEqv.mul_assoc _ _ _).symm)

/-- Cost depends on actual shared faces only. Every spectator-dependent
certificate is admitted; no independent-face assumption occurs. -/
theorem shared_weighted_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (A B : List Z4Link)
    {q : RatPoly} (P : Certificate (blocks extent) q) :
    sharedLower w extent A B *
        quaternionHaar (blocks extent) (polyMul q (retainedHeat w K extent A B)) ≤
      quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ∧
    quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ≤
      sharedUpper w extent A B *
        quaternionHaar (blocks extent) (polyMul q (retainedHeat w K extent A B)) := by
  have R := P.mul (retainedHeat_certificate hw0 hw1 K extent hK A B)
  have hlo := headProduct_weighted_floor hw0 hw1 K extent hK R
    (sharedIds extent A B) (fun _ hi => shared_physical hi)
  have hhi := headProduct_weighted_upper hw0 hw1 K extent R
    (sharedIds extent A B) (fun _ hi => shared_physical hi)
  have he := weighted_split w K extent A B q
  exact ⟨Q'.le_trans' _ _ _ hlo (Q'.ge_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hhi⟩

/-- A coarser extent-independent cost paid by the LEFT block size only,
while the reference still retains every nonshared face. -/
theorem shared_weighted_bounds_by_left {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (hK : headCutoff w ≤ K)
    (A B : List Z4Link) {q : RatPoly} (P : Certificate (blocks extent) q) :
    blockLower w A.length *
        quaternionHaar (blocks extent) (polyMul q (retainedHeat w K extent A B)) ≤
      quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ∧
    quaternionHaar (blocks extent) (polyMul q (fullWeight w K extent)) ≤
      blockUpper w A.length *
        quaternionHaar (blocks extent) (polyMul q (retainedHeat w K extent A B)) := by
  have h := atMostBlockFaces_bounds hw0 hw1 K extent hK A.length
    (P.mul (retainedHeat_certificate hw0 hw1 K extent hK A B))
    (sharedIds extent A B) (fun _ hi => shared_physical hi)
    (sharedCount_le_left extent A B)
  have he := weighted_split w K extent A B q
  exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) h.2⟩

/-- Universal signed polynomial-form comparison, not a finite selection of
tests. This is NOT yet a comparison of actual conditional residuals. -/
theorem shared_signed_pair {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (A B : List Z4Link)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hq : SupportedQuaternionBlocks (blocks extent) q) :
    let W := fullWeight w K extent;
    let R := retainedHeat w K extent A B;
    let L := sharedLower w extent A B;
    let U := sharedUpper w extent A B;
    -((U + -L) * (weightedPair (blocks extent) R p p + weightedPair (blocks extent) R q q)) ≤
      4 * weightedPair (blocks extent) W p q +
        -(2 * (L + U) * weightedPair (blocks extent) R p q) ∧
    4 * weightedPair (blocks extent) W p q +
        -(2 * (L + U) * weightedPair (blocks extent) R p q) ≤
      (U + -L) * (weightedPair (blocks extent) R p p + weightedPair (blocks extent) R q q) := by
  apply centered_polarization (fullWeight w K extent) (retainedHeat w K extent A B)
    (sharedLower w extent A B) (sharedUpper w extent A B)
  · intro z hz
    exact shared_weighted_bounds hw0 hw1 K extent hK A B (Certificate.square z hz)
  · exact hp
  · exact hq

#print axioms sharedHeat
#print axioms retainedHeat
#print axioms sharedLower
#print axioms sharedUpper
#print axioms sharedLower_positive
#print axioms fullWeight_split
#print axioms retainedHeat_certificate
#print axioms shared_weighted_bounds
#print axioms shared_weighted_bounds_by_left
#print axioms shared_signed_pair

end YMGap.Continuum.BF4ExactSlabSharedFaceComparison
