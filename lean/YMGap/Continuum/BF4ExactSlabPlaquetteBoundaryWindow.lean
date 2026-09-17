/-
# A local positive window for the original four-link plaquette star

Only selected action factors touching one of the chosen plaquette's four
boundary links occur in this window. There are at most twenty-four such
factors. Both certificates retain their actual shared coordinates; no
terminal message is declared independent and no full-action inverse is used.

The positive constants depend on nome, not extent, placement, selected
volume or late cutoff. They construct the local finite polynomial dual
tests; neither spatial susceptibility nor a physical spectral gap follows.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure
import YMGap.Continuum.BF4ExactSlabLocalStarComparison
import YMGap.Continuum.QuaternionHaarPositiveWindowInverse

namespace YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

def lower (w : Q') : Q' := (localFloor w)^24
def upper (w : Q') : Q' := (localCap w)^24

theorem lower_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < lower w := HKPos.pow_pos (localFloor_positive hw0 hw1) 24

theorem upper_positive {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < upper w :=
  HKPos.pow_pos (Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) (one_le_localCap hw0)) 24

private theorem pow_mono {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ n : Nat, x^n ≤ y^n
  | 0 => Q'.le_refl' 1
  | n+1 => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hxy (Q'.pow_nonneg x hx n))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_mono hx hxy n) (Q'.le_trans' _ _ _ hx hxy))

private theorem pow_exponent_mono {x : Q'} (hx : (1 : Q') ≤ x) {m n : Nat}
    (hmn : m ≤ n) : x^m ≤ x^n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      exact Q'.le_trans' _ _ _ ih (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hx
          (Q'.pow_nonneg x (Q'.le_trans' _ _ _ Q'.zero_le_one hx) (m+d))))

theorem lower_le_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    lower w ≤ upper w :=
  pow_mono (Q'.le_of_lt (localFloor_positive hw0 hw1))
    (Q'.le_trans' _ _ _ Q'.min_le_right (one_le_localCap hw0)) 24

private def lowerMul {blocks : Nat} {p q : RatPoly} {a b : Q'}
    (ha : (0 : Q') ≤ a) (Q : Certificate blocks q)
    (Plo : Certificate blocks (polyAdd p (polyNeg (cap a))))
    (Qlo : Certificate blocks (polyAdd q (polyNeg (cap b)))) :
    Certificate blocks (polyAdd (polyMul p q) (polyNeg (cap (a*b)))) :=
  .ofCoeff (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul a b).symm)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
      (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 1))
        (.mul (.var 2) (.add (.var 1) (.neg (.var 3)))))
      (by decide) (fun | 0 => p | 1 => q | 2 => cap a | _ => cap b)))
    ((Plo.mul Q).add ((Certificate.constant blocks a ha).mul Qlo))

private theorem cap_neg (a : Q') : RatPolyCoeffEqv (polyNeg (cap a)) (cap (-a)) := by
  intro weight
  change (-(a*1))*weight []+0 ≈ ((-a)*1)*weight []+0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv a 1))) (Q'.eqv_refl _)

private def weakenLower {blocks : Nat} {p : RatPoly} {a b : Q'}
    (P : Certificate blocks (polyAdd p (polyNeg (cap a)))) (h : b ≤ a) :
    Certificate blocks (polyAdd p (polyNeg (cap b))) := by
  have he : RatPolyCoeffEqv (polyAdd (polyAdd p (polyNeg (cap a))) (cap (a + -b)))
      (polyAdd p (polyNeg (cap b))) :=
    ((RatPolyCoeffEqv.refl _).add ((cap_add a (-b)).symm.trans
      ((RatPolyCoeffEqv.refl _).add (cap_neg b).symm))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
        (.add (.var 0) (.neg (.var 2))) (by decide)
        (fun | 0 => p | 1 => cap a | _ => cap b))
  exact .ofCoeff he.symm (P.add (.constant blocks (a + -b) (Q'.sub_nonneg_of_le h)))

private def productLower {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) : (ids : List Nat) →
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    Certificate (B extent) (polyAdd (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polyNeg (cap ((headFloor w)^ids.length))))
  | [], _ => .ofCoeff
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.one_smul polyOne))).trans
        (coeffEvalExpr_eqv_of_normalize_eq (.add (.const 1) (.neg (.const 1)))
          (.const 0) (by decide) (fun _ => polyZero)))
      (.constant (B extent) 0 (Q'.le_refl' _))
  | id::ids, hi =>
      lowerMul (Q'.le_of_lt (headFloor_positive hw0 hw1))
        (headProduct_certificate hw0 hw1 K extent hK ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))
        (faceHead_floorCertificate hw0 hw1 K extent id (hi id List.mem_cons_self) hK)
        (productLower hw0 hw1 K extent hK ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

/-- A local lower certificate on the literal selected twenty-four-factor star. -/
def starLowerCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (face : Z4Plaq) :
    Certificate (B extent) (polyAdd (starHeat w K extent ids face) (polyNeg (cap (lower w)))) := by
  have hlen := boundaryStar_length_le_twentyFour extent ids hids hnodup face
  have hfloor : lower w ≤ (headFloor w)^(boundaryStar extent ids face).length :=
    Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt (localFloor_positive hw0 hw1)) Q'.min_le_right hlen)
      (pow_mono (Q'.le_of_lt (localFloor_positive hw0 hw1)) Q'.min_le_left _)
  exact weakenLower (productLower hw0 hw1 K extent hK _
    (fun id hi => hids id (boundaryStar_mem hi).1)) hfloor

/-- The upper certificate also counts only the local selected star. -/
def starUpperCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (face : Z4Plaq) :
    Certificate (B extent) (polyAdd (cap (upper w)) (polyNeg (starHeat w K extent ids face))) := by
  have hlen := boundaryStar_length_le_twentyFour extent ids hids hnodup face
  have hcap : (prefixCap w)^(boundaryStar extent ids face).length ≤ upper w :=
    Q'.le_trans' _ _ _ (pow_mono (prefixCap_nonnegative hw0)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _))) _)
      (pow_exponent_mono (one_le_localCap hw0) hlen)
  exact ((Interval.productUniform (faceHeatPolynomial w K extent) (prefixCap w)
    (boundaryStar extent ids face)
    (fun id hi => facePrefixInterval hw0 hw1 K extent id (hids id (boundaryStar_mem hi).1))).weaken hcap).upper

end YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow.lower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow.upper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow.lower_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow.upper_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow.lower_le_upper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow.starLowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow.starUpperCertificate
