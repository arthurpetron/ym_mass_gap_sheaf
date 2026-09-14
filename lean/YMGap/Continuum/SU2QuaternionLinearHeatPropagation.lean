/-
# Linearity and independent multiplication of exact heat propagation

These are algebraic closure rules for the displayed original Haar identity.
The base case is the proved arbitrary-pair coordinate transmission, not an
assumed analytic estimate. Independent factors keep their actual shared
coordinates and are multiplied into the same insertion.
-/

import YMGap.Continuum.SU2QuaternionSelectedPairHeatTransmission

namespace YMGap.Continuum.SU2QuaternionLinearHeatPropagation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- A precisely stated identity, not a frontier assumption or a gap claim. -/
structure Propagates (blocks a b : Nat) (w : Q') (K : Nat) (p q : RatPoly) : Prop where
  pairing : ∀ r : RatPoly, SupportedQuaternionBlocks blocks r → HasQuaternionBlockDegree a 0 r →
    quaternionHaar blocks (polyMul (heatAt a b w K) (polyMul p r)) ≈
      qpow w 3 * quaternionHaar blocks (polyMul q r)

namespace Propagates

variable {blocks a b : Nat} {w : Q'} {K : Nat} {p p' q q' : RatPoly}

theorem coordinate (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val) (w : Q') (K : Nat) (hK : 1 ≤ K) (i : Fin 4) :
    Propagates (tailBlocks+1) a.val b.val w K (polyVar (4*a.val+i.val)) (polyVar (4*b.val+i.val)) := by
  constructor
  intro r hr hd
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc _ _ _ _))
    (SU2QuaternionSelectedPairHeatTransmission.coordinate_transmission tailBlocks hb a b hab w K hK i r hr hd)

theorem recode (hp : RatPolyCoeffEqv p p') (hq : RatPolyCoeffEqv q' q)
    (h : Propagates blocks a b w K p' q') : Propagates blocks a b w K p q := by
  constructor
  intro r hr hd
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((hp.mul_right r).mul_left _))
    (Q'.eqv_trans _ _ _ (h.pairing r hr hd) (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (hq.mul_right r))))

theorem add (hp : Propagates blocks a b w K p p') (hq : Propagates blocks a b w K q q') :
    Propagates blocks a b w K (polyAdd p q) (polyAdd p' q') := by
  constructor
  intro r hr hd
  simp only [polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (hp.pairing r hr hd) (hq.pairing r hr hd))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (quaternionHaar_append _ _ _)))))

private theorem swap_scalars (c d v : Q') : c * (d * v) ≈ d * (c * v) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv c d)) (Q'.mul_assoc_eqv _ _ _))

theorem smul (c : Q') (h : Propagates blocks a b w K p q) :
    Propagates blocks a b w K (polySmul c p) (polySmul c q) := by
  constructor
  intro r hr hd
  have hs := Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.polyMul_smul_left c p r).mul_left (heatAt a b w K)))
    (quaternionHaar_polyMul_smul_right blocks c (heatAt a b w K) (polyMul p r))
  have ht := Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c q r))
    (quaternionHaar_polySmul blocks c (polyMul q r))
  exact Q'.eqv_trans _ _ _ hs
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (h.pairing r hr hd))
      (Q'.eqv_trans _ _ _ (swap_scalars _ _ _)
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm ht))))

private theorem neg_smul : ∀ p : RatPoly, RatPolyCoeffEqv (polyNeg p) (polySmul (-1) p)
  | [] => .refl _
  | t::p => by
    intro weight
    change (-t.2) * weight t.1 + ratWeightedSum weight (polyNeg p) ≈
      ((-1)*t.2) * weight t.1 + ratWeightedSum weight (polySmul (-1) p)
    have hc : (-t.2) ≈ (-1)*t.2 := Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.neg_mul_eqv 1 t.2) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv t.2)))
    exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hc) (neg_smul p weight)

theorem neg (h : Propagates blocks a b w K p q) : Propagates blocks a b w K (polyNeg p) (polyNeg q) :=
  recode (neg_smul p) (neg_smul q).symm (smul (-1) h)

theorem mul_right (f : RatPoly) (hf : SupportedQuaternionBlocks blocks f) (hd : HasQuaternionBlockDegree a 0 f)
    (h : Propagates blocks a b w K p q) : Propagates blocks a b w K (polyMul p f) (polyMul q f) := by
  constructor
  intro r hr hdr
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_assoc p f r).mul_left _))
    (Q'.eqv_trans _ _ _ (h.pairing (polyMul f r) (supported_polyMul hf hr) (hd.mul hdr))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc blocks q f r))))

theorem mul_left (f : RatPoly) (hf : SupportedQuaternionBlocks blocks f) (hd : HasQuaternionBlockDegree a 0 f)
    (h : Propagates blocks a b w K p q) : Propagates blocks a b w K (polyMul f p) (polyMul f q) :=
  recode (RatPolyCoeffEqv.mul_comm f p) (RatPolyCoeffEqv.mul_comm q f) (mul_right f hf hd h)

end Propagates
end YMGap.Continuum.SU2QuaternionLinearHeatPropagation

#print axioms YMGap.Continuum.SU2QuaternionLinearHeatPropagation.Propagates
#print axioms YMGap.Continuum.SU2QuaternionLinearHeatPropagation.Propagates.coordinate
#print axioms YMGap.Continuum.SU2QuaternionLinearHeatPropagation.Propagates.recode
#print axioms YMGap.Continuum.SU2QuaternionLinearHeatPropagation.Propagates.add
#print axioms YMGap.Continuum.SU2QuaternionLinearHeatPropagation.Propagates.smul
#print axioms YMGap.Continuum.SU2QuaternionLinearHeatPropagation.Propagates.neg
#print axioms YMGap.Continuum.SU2QuaternionLinearHeatPropagation.Propagates.mul_right
#print axioms YMGap.Continuum.SU2QuaternionLinearHeatPropagation.Propagates.mul_left
