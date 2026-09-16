/-
# Relative cutoff comparison against an ACTUAL retained heat head

The Jacobi constant coefficient supplies a strict square-certificate floor.
Removing its finite weights in original Haar order transfers half that
floor to every sufficiently late UNWEIGHTED original character prefix.
Thus those prefixes, and arbitrary products of them with shared links,
are constructed positive backgrounds at every rational 0<w<1.

The omitted tail is then small relative to the SAME background times
the retained head. The computed cutoff depends on w and relative error,
not extent, placement, background size or later tail length. No full-volume
partition lower bound or independent-face replacement enters the estimate.

This controls representation truncation, NOT the head's spatial interaction.
It does not supply thermodynamic decay, a scaling family or a physical gap.
-/

import YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval

namespace YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin
open YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval (faceDeficit faceHeat_eq_weighted_add_deficit)
open YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

def headFloor (w : Q') : Q' := HalfPow.half * SU2PointwiseHeatStrictFloor.floor w

theorem headFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < headFloor w := ExpNeg.half_mul_pos _ (SU2PointwiseHeatStrictFloor.floor_pos hw0 hw1)

def headCutoff (w : Q') : Nat := deficitCutoff w (headFloor w)

/-- A strict lower square certificate, not just an integrated Jacobi floor. -/
def weightedFace_floorCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N extent id : Nat) (hN : 1 ≤ N) (hi : id ∈ slabPhysicalFaceEdges extent) :
    Certificate (blocks extent)
      (polyAdd (weightedFace w N extent id) (polyNeg (cap (SU2PointwiseHeatStrictFloor.floor w)))) :=
  .ofCoeff (((face_coeffEqv hw0 hw1 N extent id).symm).add (RatPolyCoeffEqv.refl _))
    (QPolyHaarPositiveSubstitution.certificate_sub_constant
      (slab_oneAddScalar_certificate (slabPlaquetteAt_mem hi))
      (JacobiShiftedPositiveCoefficients.heat w N)
      (JacobiShiftedPositiveCoefficients.heat_nonnegative hw0 hw1 N)
      (SU2PointwiseHeatStrictFloor.floor w)
      (JacobiShiftedPositiveCoefficients.floor_le_heat_constant hw0 hw1 N hN))

/-- The old UNWEIGHTED heat prefix has half the Jacobi floor, at every later K. -/
def faceHead_floorCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (hK : headCutoff w ≤ K) :
    Certificate (blocks extent) (polyAdd (faceHeatPolynomial w K extent id) (polyNeg (cap (headFloor w)))) := by
  let H := cap (headFloor w)
  let W := weightedFace w (K+1) extent id
  let D := faceDeficit w (K+1) extent id
  have hc : RatPolyCoeffEqv (polyAdd H H) (cap (SU2PointwiseHeatStrictFloor.floor w)) :=
    (cap_add _ _).trans (RatPolyCoeffEqv.smul_coefficient
      (ExpNeg.two_halves (SU2PointwiseHeatStrictFloor.floor w)) polyOne)
  let C : Certificate (blocks extent) (polyAdd W (polyNeg (polyAdd H H))) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hc))
      (weightedFace_floorCertificate hw0 hw1 (K+1) extent id (Nat.succ_le_succ (Nat.zero_le _)) hi)
  let R := faceDeficitInterval hw0 hw1 extent id hi (headFloor w) (headFloor_positive hw0 hw1)
    (K+1) (Nat.le_trans hK (Nat.le_succ K))
  exact .ofCoeff (((faceHeat_eq_weighted_add_deficit w K extent id).add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.add (.var 2) (.var 2)))) (.add (.var 2) (.var 1)))
      (by decide) (fun | 0 => W | 1 => D | _ => H))) (C.add R.lower)

def faceHead_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (hK : headCutoff w ≤ K) :
    Certificate (blocks extent) (faceHeatPolynomial w K extent id) :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
    (fun | 0 => faceHeatPolynomial w K extent id | _ => cap (headFloor w)))
    ((faceHead_floorCertificate hw0 hw1 K extent id hi hK).add
      (.constant _ (headFloor w) (Q'.le_of_lt (headFloor_positive hw0 hw1))))

/-- One nome-dependent cutoff certifies any finite original shared-link background. -/
def headProduct_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) : (ids : List Nat) →
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    Certificate (blocks extent) (polynomialProduct (faceHeatPolynomial w K extent) ids)
  | [], _ => .one _
  | id::ids, hi => (faceHead_certificate hw0 hw1 K extent id (hi id List.mem_cons_self) hK).mul
      (headProduct_certificate hw0 hw1 K extent hK ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

private theorem haar_neg (n : Nat) : ∀ p : RatPoly, quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1)) (haar_neg n rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem weighted_floor {n : Nat} {p h : RatPoly} {c : Q'}
    (P : Certificate n p) (C : Certificate n (polyAdd h (polyNeg (cap c)))) :
    c*quaternionHaar n p ≤ quaternionHaar n (polyMul p h) := by
  have hpos := (P.mul C).haar_nonnegative
  have hc : quaternionHaar n (polyMul p (cap c)) ≈ c*quaternionHaar n p :=
    Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans (cap_mul_left c p)))
      (quaternionHaar_polySmul n c p)
  have he : quaternionHaar n (polyMul p (polyAdd h (polyNeg (cap c)))) ≈
      quaternionHaar n (polyMul p h) + -(c*quaternionHaar n p) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => p | 1 => h | _ => cap c)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (haar_neg n _) (Q'.neg_eqv_congr _ _ hc))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))

theorem faceHead_weighted_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (hK : headCutoff w ≤ K)
    {p : RatPoly} (P : Certificate (blocks extent) p) :
    headFloor w * quaternionHaar (blocks extent) p ≤
      quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial w K extent id)) :=
  weighted_floor P (faceHead_floorCertificate hw0 hw1 K extent id hi hK)

def relativeCutoff (w eta : Q') : Nat := max (headCutoff w) (tailCutoff w (eta * headFloor w))

theorem relativeTail_weighted_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (eta : Q') (he : (0 : Q') < eta) (K L extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent)
    (hK : relativeCutoff w eta ≤ K) {p : RatPoly} (P : Certificate (blocks extent) p) :
    Q'.abs (quaternionHaar (blocks extent) (polyMul p (faceHeatTail w extent id (K+1) L))) ≤
      eta * quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial w K extent id)) := by
  have hhead : headCutoff w ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
  have htail : tailCutoff w (eta*headFloor w) ≤ K := Nat.le_trans (Nat.le_max_right _ _) hK
  have R := faceTailInterval hw0 hw1 extent id hi (eta*headFloor w)
    (HKPos.q_mul_pos he (headFloor_positive hw0 hw1)) K L htail
  exact Q'.le_trans' _ _ _ (R.weighted_haar_bound P)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (faceHead_weighted_floor hw0 hw1 K extent id hi hhead P)
        (Q'.le_of_lt he)))

/-- The literal later-minus-retained prefix, not a new action or auxiliary law. -/
theorem prefixDifference_pin (w : Q') (K L extent id : Nat) :
    RatPolyCoeffEqv (polyAdd (faceHeatPolynomial w (K+L) extent id) (polyNeg (faceHeatPolynomial w K extent id)))
      (faceHeatTail w extent id (K+1) L) := by
  rw [faceHeatPolynomial_cutoff_append]
  exact coeffEvalExpr_eqv_of_normalize_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
    (by decide) (fun | 0 => faceHeatPolynomial w K extent id | _ => faceHeatTail w extent id (K+1) L)

theorem relativePrefix_weighted_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (eta : Q') (he : (0 : Q') < eta) (K L extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent)
    (hK : relativeCutoff w eta ≤ K) {p : RatPoly} (P : Certificate (blocks extent) p) :
    Q'.abs (quaternionHaar (blocks extent) (polyMul p
      (polyAdd (faceHeatPolynomial w (K+L) extent id) (polyNeg (faceHeatPolynomial w K extent id))))) ≤
      eta * quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial w K extent id)) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (RatPolyCoeffEqv.haarCarrier (prefixDifference_pin w K L extent id) p)))
    (relativeTail_weighted_bound hw0 hw1 eta he K L extent id hi hK P)

/-- Fully constructed ORIGINAL background; every shared link and face retained. -/
theorem originalBackground_relative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (eta : Q') (he : (0 : Q') < eta) (K L extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent)
    (hK : relativeCutoff w eta ≤ K) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent) :
    let p := polynomialProduct (faceHeatPolynomial w K extent) ids
    Q'.abs (quaternionHaar (blocks extent) (polyMul p
      (polyAdd (faceHeatPolynomial w (K+L) extent id) (polyNeg (faceHeatPolynomial w K extent id))))) ≤
      eta * quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial w K extent id)) :=
  relativePrefix_weighted_bound hw0 hw1 eta he K L extent id hi hK
    (headProduct_certificate hw0 hw1 K extent (Nat.le_trans (Nat.le_max_left _ _) hK) ids hids)

/-- Inserting a selected finite set pays only for those faces, with every
shared variable retained in the arbitrary positive background. -/
theorem headProduct_weighted_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) {p : RatPoly} (P : Certificate (blocks extent) p) :
    ∀ ids : List Nat, (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
      (headFloor w)^ids.length * quaternionHaar (blocks extent) p ≤
        quaternionHaar (blocks extent) (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) ids))
  | [], _ => Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_one p)))
  | id::ids, hi => by
      have ht : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent :=
        fun j hj => hi j (List.mem_cons_of_mem id hj)
      have h := faceHead_weighted_floor hw0 hw1 K extent id (hi id List.mem_cons_self) hK
        (P.mul (headProduct_certificate hw0 hw1 K extent hK ids ht))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
          (headProduct_weighted_floor hw0 hw1 K extent hK P ids ht) (Q'.le_of_lt (headFloor_positive hw0 hw1)))
          (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff
            ((RatPolyCoeffEqv.mul_assoc _ _ _).trans ((RatPolyCoeffEqv.refl p).mul (RatPolyCoeffEqv.mul_comm _ _)))))))

/-- Original product upper bound; the cost counts inserted faces only. -/
theorem headProduct_weighted_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) {p : RatPoly} (P : Certificate (blocks extent) p)
    (ids : List Nat) (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    quaternionHaar (blocks extent) (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) ids)) ≤
      (prefixCap w)^ids.length * quaternionHaar (blocks extent) p :=
  Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    ((Interval.productUniform (faceHeatPolynomial w K extent) (prefixCap w) ids
      (fun id hid => facePrefixInterval hw0 hw1 K extent id (hi id hid))).weighted_haar_bound P)

end YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison

#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.headFloor
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.headFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.headCutoff
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.weightedFace_floorCertificate
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.faceHead_floorCertificate
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.faceHead_certificate
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.headProduct_certificate
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.faceHead_weighted_floor
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.relativeCutoff
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.relativeTail_weighted_bound
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.prefixDifference_pin
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.relativePrefix_weighted_bound
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.originalBackground_relative
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.headProduct_weighted_floor
#print axioms YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.headProduct_weighted_upper
