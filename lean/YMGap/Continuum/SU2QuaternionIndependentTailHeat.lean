/-
# Exact quadratic heat of a quaternion with an independent tail

The full selected-link heat acts on the squared scalar of coordinate*tail.
Its trace is the ORIGINAL polynomial norm of that same tail. Only an
arbitrary-insertion Haar-unit relation can subsequently replace this norm
by one. No multiplicativity of the heat map or pointwise unit substitution
is assumed. This is the one-link input for growing-word spin-two removal.
-/

import YMGap.Continuum.SU2QuaternionSelectedLinearHeatProduct
import YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
import YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
import YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
import YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare
import YMGap.Continuum.QuaternionHaarWordDifference

namespace YMGap.Continuum.SU2QuaternionIndependentTailHeat

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
  (four gram linear_pair four_pair quarter)
open YMGap.Continuum.SU2QuaternionSelectedLinearHeatProduct
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare (first_character_square)
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum (pair_vacuum)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private def coefficients (p : PolyQuaternion) (i : Fin 4) : RatPoly :=
  match i.val with
  | 0 => p.scalar
  | 1 => polyNeg p.iPart
  | 2 => polyNeg p.jPart
  | _ => polyNeg p.kPart

private theorem signed_supported {n : Nat} {p : PolyQuaternion}
    (hp : QuaternionSupported n p) (i : Fin 4) :
    SupportedQuaternionBlocks n (coefficients p i) := by
  unfold coefficients
  split
  · exact hp.scalar
  · exact support_neg hp.iPart
  · exact support_neg hp.jPart
  · exact support_neg hp.kPart

private theorem signed_degree {a : Nat} {p : PolyQuaternion}
    (hp : HasPolyQuaternionBlockDegree a 0 p) (i : Fin 4) :
    HasQuaternionBlockDegree a 0 (coefficients p i) := by
  unfold coefficients
  split
  · exact hp.scalar
  · exact hp.iPart.neg
  · exact hp.jPart.neg
  · exact hp.kPart.neg

private theorem four_member {P : RatPoly → Prop} (c : Fin 4 → RatPoly)
    (h : ∀ i, P (c i)) (x : Fin 4 × RatPoly) (hx : x ∈ four c) : P x.2 := by
  simp only [four, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3

private theorem scalar_linear (block : Nat) (p : PolyQuaternion) :
    RatPolyCoeffEqv (linearAt block (four (coefficients p)))
      (PolyQuaternion.coordinateVariable block ⋄ p).scalar := by
  have hs : RatPolyCoeffEqv (linearAt block (four (coefficients p)))
      (polyAdd (polyMul (polyVar (4*block)) p.scalar)
        (polyAdd (polyMul (polyVar (4*block+1)) (polyNeg p.iPart))
          (polyAdd (polyMul (polyVar (4*block+2)) (polyNeg p.jPart))
            (polyMul (polyVar (4*block+3)) (polyNeg p.kPart))))) :=
    (RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)))
  refine hs.trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 1)) (.add (.mul (.var 2) (.neg (.var 3)))
      (.add (.mul (.var 4) (.neg (.var 5))) (.mul (.var 6) (.neg (.var 7))))))
    (.add (.mul (.var 0) (.var 1)) (.neg (.add (.mul (.var 2) (.var 3))
      (.add (.mul (.var 4) (.var 5)) (.mul (.var 6) (.var 7))))))
    (by decide) (fun
      | 0 => polyVar (4*block) | 1 => p.scalar
      | 2 => polyVar (4*block+1) | 3 => p.iPart
      | 4 => polyVar (4*block+2) | 5 => p.jPart
      | 6 => polyVar (4*block+3) | _ => p.kPart)

private theorem gram_norm (p : PolyQuaternion) :
    RatPolyCoeffEqv (gram (four (coefficients p)) (four (coefficients p)))
      (polySmul quarter (polyQuaternionNorm p)) := by
  refine ((linear_pair _ _).symm.trans (four_pair _ _)).trans ?_
  apply RatPolyCoeffEqv.smul
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 0)) (.add (.mul (.neg (.var 1)) (.neg (.var 1)))
      (.add (.mul (.neg (.var 2)) (.neg (.var 2))) (.mul (.neg (.var 3)) (.neg (.var 3))))))
    (.add (.mul (.var 0) (.var 0)) (.add (.mul (.var 1) (.var 1))
      (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
    (by decide) (fun | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | _ => p.kPart)

/-- The complete quadratic image, including the actual tail norm. The tail
and insertion may both depend on the target block and on each other. -/
theorem scalar_square_transmission (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (p : PolyQuaternion)
    (hp : QuaternionSupported (tailBlocks+1) p)
    (hdp : HasPolyQuaternionBlockDegree a.val 0 p) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    let sa := (PolyQuaternion.coordinateVariable a.val ⋄ p).scalar
    let sb := (PolyQuaternion.coordinateVariable b.val ⋄ p).scalar
    quaternionHaar (tailBlocks+1)
      (polyMul (polyMul (heatAt a.val b.val w K) (polyMul sa sa)) r) ≈
      qpow w 8 * quaternionHaar (tailBlocks+1) (polyMul (polyMul sb sb) r) +
        (1 + -(qpow w 8)) *
          (quarter * quaternionHaar (tailBlocks+1) (polyMul (polyQuaternionNorm p) r)) := by
  let cs := four (coefficients p)
  have hs := four_member (coefficients p) (signed_supported hp)
  have hd := four_member (coefficients p) (signed_degree hdp)
  have h := linear_product_transmission tailBlocks hb a b hab w K hK cs cs r
    hs hd hs hd hr hdr
  have ha := scalar_linear a.val p
  have hb' := scalar_linear b.val p
  have hn := Q'.eqv_trans _ _ _ (haar_of_coeff ((gram_norm p).mul_right r))
    (Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left quarter (polyQuaternionNorm p) r))
      (quaternionHaar_polySmul (tailBlocks+1) quarter _))
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (((ha.symm.mul ha.symm).mul_left (heatAt a.val b.val w K)).mul_right r))
    (Q'.eqv_trans _ _ _ h
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff ((hb'.mul hb').mul_right r)))
        (Q'.mul_eqv_congr_left _ _ _ hn)))

private theorem character_two_coeff (s : RatPoly) :
    RatPolyCoeffEqv (characterPolynomial s 2)
      (polyAdd (polySmul 4 (polyMul s s)) (polySmul (-1) polyOne)) := by
  have hfirst := first_character_square s
  have hchi1 : RatPolyCoeffEqv (characterPolynomial s 1) (polySmul 2 s) :=
    RatPolyCoeffEqv.refl _
  have hs : RatPolyCoeffEqv
      (polyMul (characterPolynomial s 1) (characterPolynomial s 1))
      (polySmul 4 (polyMul s s)) :=
    (hchi1.mul hchi1).trans
      ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).smul 2).trans
        (twice_twice_smul _)))
  have hcancelLeft : RatPolyCoeffEqv (characterPolynomial s 2)
      (polyAdd (polySmul (-1) polyOne)
        (polyAdd polyOne (characterPolynomial s 2))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.var 0) (.add (.mul (.const (-1)) (.var 1)) (.add (.var 1) (.var 0)))
      (by decide) (fun | 0 => characterPolynomial s 2 | _ => polyOne)
  have hcancelRight : RatPolyCoeffEqv
      (polyAdd (polySmul (-1) polyOne) (polySmul 4 (polyMul s s)))
      (polyAdd (polySmul 4 (polyMul s s)) (polySmul (-1) polyOne)) :=
    RatPolyCoeffEqv.add_comm _ _
  exact hcancelLeft.trans
    ((((RatPolyCoeffEqv.refl (polySmul (-1) polyOne)).add hfirst.symm).trans
      ((RatPolyCoeffEqv.refl _).add hs)).trans hcancelRight)

private theorem character_two_pairing (blocks : Nat) (s r : RatPoly) :
    quaternionHaar blocks (polyMul (characterPolynomial s 2) r) ≈
      4 * quaternionHaar blocks (polyMul (polyMul s s) r) +
        (-1) * quaternionHaar blocks r := by
  refine Q'.eqv_trans _ _ _ (haar_of_coeff ((character_two_coeff s).mul_right r)) ?_
  rw [polyMul_add_left_exact]
  refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left 4 (polyMul s s) r))
      (quaternionHaar_polySmul blocks 4 _)
  · exact Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.polyMul_smul_left (-1) polyOne r).trans
        ((RatPolyCoeffEqv.one_mul r).smul (-1))))
      (quaternionHaar_polySmul blocks (-1) r)

private theorem rearrange (mu f r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul mu f) r) (polyMul f (polyMul mu r)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => mu | 1 => f | _ => r)

private theorem four_quarter (z : Q') :
    (4 : Q') * (quarter * z) ≈ z :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 4 quarter z))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (show (4 : Q') * quarter ≈ 1 by decide))
      (Q'.one_mul_eqv z))

private theorem spinTwo_balance (l x z : Q') :
    (4 : Q') * (l*x + (1 + -l)*(quarter*z)) + (-1)*z ≈
      l * ((4 : Q')*x + (-1)*z) := by
  have h := poly_identity_of_normal_eq
    (.add (.mul (.const 4) (.add (.mul (.var 0) (.var 1))
      (.mul (.add (.const 1) (.neg (.var 0))) (.var 2))))
      (.mul (.const (-1)) (.var 3)))
    (.add (.mul (.var 0) (.add (.mul (.const 4) (.var 1))
      (.mul (.const (-1)) (.var 3))))
      (.mul (.add (.const 1) (.neg (.var 0)))
        (.add (.mul (.const 4) (.var 2)) (.mul (.const (-1)) (.var 3)))))
    (by decide) (fun
      | 0 => l
      | 1 => x
      | 2 => quarter*z
      | _ => z)
  have hz : (4 : Q')*(quarter*z)+(-1)*z ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (four_quarter z))
      (poly_identity_of_normal_eq
        (.add (.var 0) (.mul (.const (-1)) (.var 0))) (.const 0)
        (by decide) (fun _ => z))
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
        (QPoly.q_add_zero_eqv _)))

/-- With the tail's ORIGINAL arbitrary-insertion Haar-unit certificate,
the label-two character is transmitted purely by w^8. -/
theorem spinTwo_transmission (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (p : PolyQuaternion)
    (hp : QuaternionSupported (tailBlocks+1) p)
    (hdp : HasPolyQuaternionBlockDegree a.val 0 p)
    (hnorm : HaarCarrierEqv (tailBlocks+1) (polyQuaternionNorm p) polyOne)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    quaternionHaar (tailBlocks+1) (polyMul (polyMul (heatAt a.val b.val w K)
      (characterPolynomial (PolyQuaternion.coordinateVariable a.val ⋄ p).scalar 2)) r) ≈
      qpow w 8 * quaternionHaar (tailBlocks+1)
        (polyMul (characterPolynomial (PolyQuaternion.coordinateVariable b.val ⋄ p).scalar 2) r) := by
  let n := tailBlocks+1
  let mu := heatAt a.val b.val w K
  let sa := (PolyQuaternion.coordinateVariable a.val ⋄ p).scalar
  let sb := (PolyQuaternion.coordinateVariable b.val ⋄ p).scalar
  have hn : quaternionHaar n (polyMul (polyQuaternionNorm p) r) ≈ quaternionHaar n r :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ r))
      (Q'.eqv_trans _ _ _ (hnorm r) (haar_of_coeff (RatPolyCoeffEqv.mul_one r)))
  have hs := Q'.eqv_trans _ _ _
    (scalar_square_transmission tailBlocks hb a b hab w K hK p hp hdp r hr hdr)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hn)))
  have hi := Q'.eqv_trans _ _ _
    (haar_of_coeff (rearrange mu (characterPolynomial sa 2) r))
    (character_two_pairing n sa (polyMul mu r))
  have hsq : quaternionHaar n (polyMul (polyMul sa sa) (polyMul mu r)) ≈
      qpow w 8 * quaternionHaar n (polyMul (polyMul sb sb) r) +
        (1 + -(qpow w 8)) * (quarter * quaternionHaar n r) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (rearrange mu (polyMul sa sa) r).symm) hs
  refine Q'.eqv_trans _ _ _ hi ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left 4 _ _ hsq)
      (Q'.mul_eqv_congr_left (-1) _ _ (pair_vacuum tailBlocks hb a b hab w K r hr hdr))) ?_
  refine Q'.eqv_trans _ _ _
    (spinTwo_balance (qpow w 8)
      (quaternionHaar n (polyMul (polyMul sb sb) r)) (quaternionHaar n r)) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (character_two_pairing n sb r))

#print axioms support_neg
#print axioms signed_supported
#print axioms signed_degree
#print axioms four_member
#print axioms scalar_linear
#print axioms gram_norm
#print axioms scalar_square_transmission
#print axioms spinTwo_transmission

end YMGap.Continuum.SU2QuaternionIndependentTailHeat
