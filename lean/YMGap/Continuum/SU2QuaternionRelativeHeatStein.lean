/-
# Finite relative-heat defects as actual source-gradient pairings

The original cutoff heat kernel times x_i-w^3*y_i has zero CONDITIONAL
head mean, for every cutoff containing spin one. Compute its head Green
polynomial and use angular integration by parts on the SAME full carrier.
The complete source may depend on the selected link and every spectator.
Only explicitly head-independent surrounding factors are left undifferentiated.

No infinitesimal Ward identity is substituted for a finite heat defect.
The signed pairing is represented exactly, not assigned a favorable sign
or a uniform bound. Full-word quantitative control is still required.
-/

import YMGap.Continuum.SU2QuaternionHeadCasimirInverse
import YMGap.Continuum.SU2QuaternionRelativeHeatVacuum

namespace YMGap.Continuum.SU2QuaternionRelativeHeatStein

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
open YMGap.Continuum.SU2QuaternionRelativeHeatVacuum
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadCasimirInverse
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Literal finite kinetic kernel times a selected fundamental difference. -/
def coordinateDefect (w : Q') (K : Nat) (i : Fin 4) : RatPoly :=
  polyMul (relativeHeat w K)
    (polyAdd (polyVar i.val) (polySmul (-(qpow w 3)) (polyVar (4+i.val))))

private theorem supported_var {blocks coordinate : Nat} (hc : coordinate < 4*blocks) :
    SupportedQuaternionBlocks blocks (polyVar coordinate) := by
  intro term ht
  have he := List.mem_singleton.mp ht
  subst term
  change (varMono coordinate).length ≤ 4*blocks
  simp only [varMono, List.length_append, List.length_replicate, List.length_singleton]
  omega

theorem coordinateDefect_supported {tail : Nat} (hb : 0 < tail)
    (w : Q') (K : Nat) (i : Fin 4) :
    SupportedQuaternionBlocks (tail+1) (coordinateDefect w K i) :=
  supported_polyMul (heat_supported (by omega) (by omega) w K)
    (supported_add (supported_var (by have := i.isLt; omega))
      (polySmul_supported (supported_var (by have := i.isLt; omega)) _))

private theorem retained_coordinate_independent (i : Fin 4) :
    HeadQuaternionIndependent (polyVar (4+i.val)) := by
  intro t ht
  have ht' := List.mem_singleton.mp ht
  subst t
  change exponentAt (varMono (4+i.val)) 0 + exponentAt (varMono (4+i.val)) 1 +
    exponentAt (varMono (4+i.val)) 2 + exponentAt (varMono (4+i.val)) 3 = 0
  rw [exponentAt_varMono, exponentAt_varMono, exponentAt_varMono, exponentAt_varMono]
  simp only [if_neg (show 0 ≠ 4+i.val by omega), if_neg (show 1 ≠ 4+i.val by omega),
    if_neg (show 2 ≠ 4+i.val by omega), if_neg (show 3 ≠ 4+i.val by omega)]

private theorem defect_pair_zero (tail : Nat) (hb : 0 < tail)
    (w : Q') (K : Nat) (hK : 1 ≤ K) (i : Fin 4) (r : RatPoly)
    (hr : HeadQuaternionIndependent r) :
    H (tail+1) (polyMul (coordinateDefect w K i) r) ≈ 0 := by
  let a := qpow w 3
  let y := polyVar (4+i.val)
  have hyd : HasQuaternionBlockDegree 0 0 y := retained_coordinate_independent i
  have hrd : HasQuaternionBlockDegree 0 0 r := hr
  have hy : HeadQuaternionIndependent (polyMul y r) :=
    hyd.mul hrd
  have ht := coordinate_transmission_same_carrier tail hb w K hK i r hr
  have hv : H (tail+1) (polyMul (polyMul (relativeHeat w K) y) r) ≈
      H (tail+1) (polyMul y r) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_assoc _ _ _ _)
      (heat_vacuum tail hb w K (polyMul y r) hy)
  have he : RatPolyCoeffEqv (polyMul (coordinateDefect w K i) r)
      (polyAdd (polyMul (polyMul (relativeHeat w K) (polyVar i.val)) r)
        (polySmul (-a) (polyMul (polyMul (relativeHeat w K) y) r))) :=
    ((RatPolyCoeffEqv.mul_add_right _ _ _).mul_right r).trans (by
      rw [polyMul_add_left_exact]
      exact (RatPolyCoeffEqv.refl _).add
        (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).mul_right r).trans
          (RatPolyCoeffEqv.polyMul_smul_left _ _ _)))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' ht (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ (-a) _)
          (Q'.mul_eqv_congr_left _ _ _ hv)))
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 0)) (.var 1)))
          (.const 0) (by decide)
          (fun | 0 => a | _ => H (tail+1) (polyMul y r)))))

/-- Conditional head centering is PROVED for the literal finite heat defect;
global centering alone is not used to invert a head Casimir. -/
theorem coordinateDefect_conditional_zero (tail : Nat) (hb : 0 < tail)
    (w : Q') (K : Nat) (hK : 1 ≤ K) (i : Fin 4) :
    HaarCarrierEqv tail (partialHaarHead (coordinateDefect w K i)) polyZero := by
  intro insertion
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (head_pairing tail 1 _ insertion).symm
      (Q'.eqv_trans _ _ _
        (defect_pair_zero tail hb w K hK i (liftBoundary 1 insertion)
          (lifted_independent insertion))
        (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right insertion)).symm))

/-- Every source derivative is literal; the source need not be independent
of the integrated link, positive, or an eigenfunction. -/
theorem coordinateDefect_source_gradient (tail : Nat) (hb : 0 < tail)
    (w : Q') (K : Nat) (hK : 1 ≤ K) (i : Fin 4) (q : RatPoly) :
    H (tail+1) (polyMul q (coordinateDefect w K i)) ≈
      sourceGradientPair tail q (coordinateDefect w K i) := by
  have hz : HaarCarrierEqv (tail+1)
      (liftBoundary 1 (partialHaarHead (coordinateDefect w K i))) polyZero :=
    lift_carrier 1 (coordinateDefect_conditional_zero tail hb w K hK i)
  have hc : HaarCarrierEqv (tail+1)
      (polyAdd (coordinateDefect w K i)
        (polyNeg (liftBoundary 1 (partialHaarHead (coordinateDefect w K i)))))
      (coordinateDefect w K i) :=
    (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _) (HaarCarrierEqv.neg hz)).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_zero _))
  exact Q'.eqv_trans _ _ _ (hc q).symm
    (source_gradient_identity tail q _ (coordinateDefect_supported hb w K i))

private theorem derivative_independent {i j : Nat} (hi : i < 4) (hj : j < 4)
    (r : RatPoly) (hr : HasQuaternionBlockDegree 0 0 r) :
    RatPolyCoeffEqv (angularDerivative i j r) polyZero := by
  unfold angularDerivative
  have hl := ((ratDerivative_eq_zero_of_headDegree_zero j hj r hr).mul_left (polyVar i)).trans
    (RatPolyCoeffEqv.mul_zero_right _)
  have hr' := ((((ratDerivative_eq_zero_of_headDegree_zero i hi r hr).mul_left (polyVar j)).trans
    (RatPolyCoeffEqv.mul_zero_right _)).smul (-1)).trans (RatPolyCoeffEqv.smul_zero _)
  exact hl.add hr'

/-- Other action/kernel factors can be kept as actual spectators only when
their selected-head independence is supplied. The full q stays differentiated. -/
theorem coordinateDefect_retained_source_gradient (tail : Nat) (hb : 0 < tail)
    (w : Q') (K : Nat) (hK : 1 ≤ K) (i : Fin 4) (q r : RatPoly)
    (hr : HasQuaternionBlockDegree 0 0 r) :
    H (tail+1) (polyMul (polyMul q r) (coordinateDefect w K i)) ≈
      sixValue (fun j k => H (tail+1)
        (polyMul (polyMul (angularDerivative j k q) r)
          (angularDerivative j k (potential tail (coordinateDefect w K i))))) := by
  refine Q'.eqv_trans _ _ _ (coordinateDefect_source_gradient tail hb w K hK i (polyMul q r)) ?_
  exact sixValue_congr _ _ (fun j k hj hk => haar_of_coeff
    ((((angularDerivative_mul j k q r).trans
      (((RatPolyCoeffEqv.refl _).add
        ((derivative_independent hj hk r hr).mul_left q)).trans
        (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.mul_zero_right q)).trans
          (RatPolyCoeffEqv.add_zero _)))).mul_right _)))

end YMGap.Continuum.SU2QuaternionRelativeHeatStein

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatStein.coordinateDefect_supported
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatStein.coordinateDefect_conditional_zero
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatStein.coordinateDefect_source_gradient
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatStein.coordinateDefect_retained_source_gradient
