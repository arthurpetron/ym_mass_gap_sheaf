/-
# Polynomial localization below the ORIGINAL corrected-slab heat factor

Every premise of the scalar localization estimate is produced here for the
literal original plaquette and original finite character coefficients. The
positive floor is finiteFloor(w)/H_K(1), the normalized Casimir moment is
C_(K+1)(w)/H_K(1), and the linear cost is 1+(32/3)*that moment. Computed degree
D*n depends on these quantities, not on the number of faces in the action.

The four kernel bases use the SAME assigned link units, original inverses,
and original identity fallback. This is a pointwise finite factor bound.
Incidence counting, integration of the entire localized original action,
entropy/logarithmic identification and signed response-relative payment
are not supplied by this module.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteDeficit
import YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds
import YMGap.Continuum.SU2HeatFiniteCasimirDeficit
import YMGap.Continuum.PolynomialHeatLocalization
import YMGap.RepTheory.RationalQuaternionFourKernelProduct

namespace YMGap.Continuum.BF4ExactSlabPolynomialHeatLocalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Constructive.HalfPow (half)
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.RepTheory.RationalQuaternionFourKernelProduct
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.BondMovingStep (coeffW_nonneg)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (standardPointwiseHeatPartial)
open YMGap.Continuum.SU2HeatFiniteCasimirDeficit
open YMGap.Continuum.SU2PointwiseHeatStrictFloor (finiteFloor finiteFloor_pos finiteCutoff)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds (identityHeat identityHeat_positive)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail (faceScalar)
open YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor
open YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder (faceScalar_box)
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit (linkValue plaquetteValue plaquette_scalar_pin)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (evalRatPoly)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.ClusterCount4DProgress (addE dirsOf)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabPlaquetteAt)
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem qr (a b : PE) (h :
    RingNormaliser.normalize a = RingNormaliser.normalize b) (rho : Nat → Q') :
    RingNormaliser.eval rho a ≈ RingNormaliser.eval rho b :=
  poly_identity_of_normal_eq a b h rho

/-- Computed reciprocal of the original identity value, not of a partition. -/
def reciprocal (w : Q') (hw0 : (0 : Q') < w) (K : Nat) : Q' :=
  Q'.recipPos (identityHeat w K) (identityHeat_positive (Q'.le_of_lt hw0) K)

private theorem reciprocal_pos {w : Q'} (hw0 : (0 : Q') < w) (K : Nat) :
    (0 : Q') < reciprocal w hw0 K := Q'.recipPos_pos _ _

private theorem reciprocal_cancel {w : Q'} (hw0 : (0 : Q') < w) (K : Nat) :
    reciprocal w hw0 K*identityHeat w K ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)

/-- The one-factor original positive floor, with the inclusive cutoff retained. -/
def eta (w : Q') (hw0 : (0 : Q') < w) (K : Nat) : Q' :=
  reciprocal w hw0 K*finiteFloor w

theorem eta_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    (0 : Q') < eta w hw0 K :=
  Q'.mul_pos (reciprocal_pos hw0 K) (finiteFloor_pos hw0 hw1)

/-- Literal finite Casimir moment divided by the original identity heat. -/
def mu (w : Q') (hw0 : (0 : Q') < w) (K : Nat) : Q' :=
  reciprocal w hw0 K*casimirMoment w (K+1)

private theorem moment_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w) :
    ∀ N, (0 : Q') ≤ casimirMoment w N
  | 0 => Q'.le_refl' 0
  | N+1 => by
      have hn : (0 : Q') ≤ Q'.ofNat N := HeatKernelRGStep.zero_le_ofNat N
      have hs : (0 : Q') ≤ casimirSlope N := Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ hn (Q'.zero_le_add _ _ hn (by decide)))
        (Q'.zero_le_add _ _ hn (by decide))
      exact Q'.zero_le_add _ _ (moment_nonnegative hw0 N)
        (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 N) hs)

theorem mu_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (K : Nat) :
    (0 : Q') ≤ mu w hw0 K :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (reciprocal_pos hw0 K))
    (moment_nonnegative (Q'.le_of_lt hw0) (K+1))

/-- Explicit linear localization cost; no parameter dependence is hidden. -/
def cost (w : Q') (hw0 : (0 : Q') < w) (K : Nat) : Q' :=
  1 + Q'.mkPos 32 3 (by decide)*mu w hw0 K

theorem cost_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (K : Nat) :
    (0 : Q') ≤ cost w hw0 K :=
  Q'.zero_le_add _ _ (by decide)
    (Q'.mul_nonneg _ _ (by decide) (mu_nonnegative hw0 K))

/-- The original finite face polynomial at its SAME shared-link environment. -/
def normalizedFace (w : Q') (hw0 : (0 : Q') < w) (K extent id : Nat)
    (qs : Nat → UnitNorm) : Q' :=
  reciprocal w hw0 K*evalRatPoly (environment qs) (faceHeatPolynomial w K extent id)

theorem normalizedFace_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent id : Nat) (qs : Nat → UnitNorm) (hK : finiteCutoff w ≤ K+1) :
    eta w hw0 K ≤ normalizedFace w hw0 K extent id qs :=
  Q'.mul_le_mul_of_nonneg_left _ _ _
    (finiteFloor_le_eval_faceHeatPolynomial hw0 hw1 K extent id (environment qs) hK
      (faceScalar_box extent id qs).1 (faceScalar_box extent id qs).2)
    (Q'.le_of_lt (reciprocal_pos hw0 K))

theorem normalizedFace_upper {w : Q'} (hw0 : (0 : Q') < w)
    (K extent id : Nat) (qs : Nat → UnitNorm) :
    normalizedFace w hw0 K extent id qs ≤ (1 : Q') :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (BF4ExactSlabNormalizedHeatBounds.faceHeatPolynomial_le_identityHeat
        (Q'.le_of_lt hw0) K extent id qs) (Q'.le_of_lt (reciprocal_pos hw0 K)))
    (Q'.le_of_eqv (reciprocal_cancel hw0 K))

/-- Product of the four original link kernel bases, with reversal retained. -/
def faceKernelProduct (extent id : Nat) (qs : Nat → UnitNorm) : Q' :=
  let face := slabPlaquetteAt extent id
  let a := (dirsOf face.2).1
  let b := (dirsOf face.2).2
  product (linkValue extent qs (face.1,a)) (linkValue extent qs (addE face.1 a,b))
    (UnitNorm.inv (linkValue extent qs (addE face.1 b,a)))
    (UnitNorm.inv (linkValue extent qs (face.1,b)))

theorem faceKernelProduct_bounds (extent id : Nat) (qs : Nat → UnitNorm) :
    (0 : Q') ≤ faceKernelProduct extent id qs ∧ faceKernelProduct extent id qs ≤ (1 : Q') :=
  product_bounds _ _ _ _

private theorem face_deficit (extent id : Nat) (qs : Nat → UnitNorm) :
    (1 : Q') + -evalRatPoly (environment qs) (faceScalar extent id) ≤
      32*((1 : Q') + -faceKernelProduct extent id qs) := by
  have h := four_word_deficit
    (linkValue extent qs ((slabPlaquetteAt extent id).1,(dirsOf (slabPlaquetteAt extent id).2).1))
    (linkValue extent qs (addE (slabPlaquetteAt extent id).1 (dirsOf (slabPlaquetteAt extent id).2).1,
      (dirsOf (slabPlaquetteAt extent id).2).2))
    (UnitNorm.inv (linkValue extent qs
      (addE (slabPlaquetteAt extent id).1 (dirsOf (slabPlaquetteAt extent id).2).2,
        (dirsOf (slabPlaquetteAt extent id).2).1)))
    (UnitNorm.inv (linkValue extent qs
      ((slabPlaquetteAt extent id).1,(dirsOf (slabPlaquetteAt extent id).2).2)))
  have hp := Q'.add_eqv_congr_left 1 _ _ (Q'.neg_eqv_congr _ _
    (plaquette_scalar_pin extent qs (slabPlaquetteAt extent id)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) h

private theorem normalized_deficit {w : Q'} (hw0 : (0 : Q') < w)
    (K extent id : Nat) (qs : Nat → UnitNorm) :
    3*((1 : Q') + -normalizedFace w hw0 K extent id qs) ≤
      mu w hw0 K*((1 : Q') + -evalRatPoly (environment qs) (faceScalar extent id)) := by
  let r := reciprocal w hw0 K
  let B := identityHeat w K
  let H := standardPointwiseHeatPartial w
    (evalRatPoly (environment qs) (faceScalar extent id)) (K+1)
  let F := evalRatPoly (environment qs) (faceHeatPolynomial w K extent id)
  have hp : H ≈ F := Q'.eqv_symm (eval_faceHeatPolynomial_eqv w K extent id (environment qs))
  have hl : r*(3*(B + -H)) ≈ 3*((1 : Q') + -(r*F)) :=
    Q'.eqv_trans _ _ _
      (qr (.var 0*(3*(.var 1 + -(.var 2)))) (3*(.var 0*.var 1 + -(.var 0*.var 2)))
        (by decide) (fun | 0 => r | 1 => B | _ => H))
      (Q'.mul_eqv_congr_left 3 _ _ (Q'.add_eqv_congr'
        (reciprocal_cancel hw0 K) (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left r _ _ hp))))
  have hd := Q'.mul_le_mul_of_nonneg_left _ _ r
    (heat_deficit (Q'.le_of_lt hw0) _ (faceScalar_box extent id qs).2
      (faceScalar_box extent id qs).1 (K+1)) (Q'.le_of_lt (reciprocal_pos hw0 K))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hd (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)))

theorem normalizedFace_linear_deficit {w : Q'} (hw0 : (0 : Q') < w)
    (K extent id : Nat) (qs : Nat → UnitNorm) :
    (1 : Q') + -normalizedFace w hw0 K extent id qs ≤
      cost w hw0 K*((1 : Q') + -faceKernelProduct extent id qs) := by
  let delta := (1 : Q') + -faceKernelProduct extent id qs
  have hd0 : (0 : Q') ≤ delta := Q'.sub_nonneg_of_le (faceKernelProduct_bounds extent id qs).2
  have hw := Q'.mul_le_mul_of_nonneg_left _ _ (mu w hw0 K)
    (face_deficit extent id qs) (mu_nonnegative hw0 K)
  have hpaid : 3*((1 : Q') + -normalizedFace w hw0 K extent id qs) ≤
      (32*mu w hw0 K)*delta :=
    Q'.le_trans' _ _ _ (normalized_deficit hw0 K extent id qs)
      (Q'.le_trans' _ _ _ hw (Q'.le_of_eqv
        (qr (.var 0*(32*.var 1)) ((32*.var 0)*.var 1) (by decide)
          (fun | 0 => mu w hw0 K | _ => delta))))
  have hcost : (32*mu w hw0 K) ≤ 3*cost w hw0 K := by
    have hp : 3*cost w hw0 K ≈ 3 + 32*mu w hw0 K :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
        (Q'.add_eqv_congr' (Q'.mul_one_eqv 3)
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
            (Q'.mul_eqv_congr_right _ _ _ (by decide : (3 : Q')*Q'.mkPos 32 3 (by decide) ≈ 32))))
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ 3 (by decide))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _))) (Q'.ge_of_eqv hp)
  apply Q'.le_of_mul_le_mul_left (c := 3) _ (by decide)
  exact Q'.le_trans' _ _ _ hpaid
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ delta hcost hd0)
      (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)))

/-- Positive, value-based polynomial degree for the literal original heat factor. -/
def localizationDegree (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) : Nat :=
  PolynomialHeatLocalization.degree (cost w hw0 K) (eta w hw0 K) (eta_positive hw0 hw1 K)

theorem localizationDegree_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) : 0 < localizationDegree w hw0 hw1 K :=
  PolynomialHeatLocalization.degree_positive _ _ _

/-- No analytic floor/deficit is supplied: both are PRODUCED above from the
original finite heat and original ordered nonabelian word on the SAME links. -/
theorem original_face_localization {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent id : Nat) (qs : Nat → UnitNorm) (hK : finiteCutoff w ≤ K+1) :
    half*qpow (faceKernelProduct extent id qs) (localizationDegree w hw0 hw1 K) ≤
      normalizedFace w hw0 K extent id qs :=
  PolynomialHeatLocalization.half_mul_power_le (eta_positive hw0 hw1 K)
    (cost_nonnegative hw0 K) (faceKernelProduct_bounds extent id qs).1
    (faceKernelProduct_bounds extent id qs).2 (normalizedFace_floor hw0 hw1 K extent id qs hK)
    (normalizedFace_linear_deficit hw0 K extent id qs)

#print axioms reciprocal
#print axioms eta
#print axioms eta_positive
#print axioms mu
#print axioms mu_nonnegative
#print axioms cost
#print axioms cost_nonnegative
#print axioms normalizedFace
#print axioms normalizedFace_floor
#print axioms normalizedFace_upper
#print axioms faceKernelProduct
#print axioms faceKernelProduct_bounds
#print axioms normalizedFace_linear_deficit
#print axioms localizationDegree
#print axioms localizationDegree_positive
#print axioms original_face_localization

end YMGap.Continuum.BF4ExactSlabPolynomialHeatLocalization
