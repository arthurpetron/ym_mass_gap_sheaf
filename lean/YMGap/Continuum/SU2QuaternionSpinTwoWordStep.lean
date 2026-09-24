/-
# Spin-two one-step transmission inside an ordered word

The independent-tail spin-two identity is consumed after cyclically moving a
prefix past the selected coordinate and tail.  Both prefix and tail remain
actual supported quaternion polynomials; only their Haar-unit certificates
are used to form the combined tail.  This is a finite product-heat identity,
not an interacting eigenvector or continuum statement.
-/

import YMGap.Continuum.SU2QuaternionIndependentTailHeat
import YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
import YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace

namespace YMGap.Continuum.SU2QuaternionSpinTwoWordStep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionIndependentTailHeat
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul

private theorem scalar_prefix_tail_recode
    (a : Nat) (p q : PolyQuaternion) (spin : Nat) :
    RatPolyCoeffEqv
      (characterPolynomial (p ⋄ (PolyQuaternion.coordinateVariable a ⋄ q)).scalar spin)
      (characterPolynomial
        (PolyQuaternion.coordinateVariable a ⋄ (q ⋄ p)).scalar spin) := by
  apply characterPolynomial_coeffEqv
  exact (polyQuaternion_mul_scalar_cyclic p
      (PolyQuaternion.coordinateVariable a ⋄ q)).trans
    (PolyQuaternionCoeffEqv.mul_assoc
      (PolyQuaternion.coordinateVariable a) q p).scalar

private theorem scalar_conj_comm (p q : PolyQuaternion) :
    RatPolyCoeffEqv (p ⋄ (PolyQuaternion.conj q)).scalar
      (q ⋄ (PolyQuaternion.conj p)).scalar := by
  let environment : Nat → RatPoly := fun
    | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
    | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | _ => q.kPart
  simpa only [PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
    PolyQuaternionExpr.coordinate, coeffEvalExpr, environment,
    PolyQuaternion.mul, PolyQuaternion.conj] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 4))).scalar
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 4)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))).scalar
      (by decide) environment)

private theorem combined_tail_supported {n : Nat} {p q : PolyQuaternion}
    (hp : QuaternionSupported n p) (hq : QuaternionSupported n q) :
    QuaternionSupported n (q ⋄ p) :=
  hq.mul hp

private theorem combined_tail_degree_zero {block : Nat} {p q : PolyQuaternion}
    (hp : HasPolyQuaternionBlockDegree block 0 p)
    (hq : HasPolyQuaternionBlockDegree block 0 q) :
    HasPolyQuaternionBlockDegree block 0 (q ⋄ p) := by
  simpa using hq.mul hp

private theorem combined_tail_norm {n : Nat} {p q : PolyQuaternion}
    (hp : HaarCarrierEqv n (polyQuaternionNorm p) polyOne)
    (hq : HaarCarrierEqv n (polyQuaternionNorm q) polyOne) :
    HaarCarrierEqv n (polyQuaternionNorm (q ⋄ p)) polyOne := by
  exact haarNorm_mul hq hp

/-- One selected coordinate transmits the spin-two character through an
arbitrarily ordered prefix/tail word.  The final supported source is retained
unchanged and only needs degree zero at the selected block. -/
theorem spinTwo_word_step (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (hK : 2 ≤ K)
    (p q : PolyQuaternion)
    (hp : QuaternionSupported (tailBlocks+1) p)
    (hdp : HasPolyQuaternionBlockDegree a.val 0 p)
    (hnormp : HaarCarrierEqv (tailBlocks+1) (polyQuaternionNorm p) polyOne)
    (hq : QuaternionSupported (tailBlocks+1) q)
    (hdq : HasPolyQuaternionBlockDegree a.val 0 q)
    (hnormq : HaarCarrierEqv (tailBlocks+1) (polyQuaternionNorm q) polyOne)
    (reverse : Bool)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    quaternionHaar (tailBlocks+1)
        (polyMul (polyMul (heatAt a.val b.val w K)
          (characterPolynomial
            (p ⋄ (orientedCoordinateQuaternion a.val reverse ⋄ q)).scalar 2)) r) ≈
      qpow w 8 * quaternionHaar (tailBlocks+1)
        (polyMul (characterPolynomial
          (p ⋄ (orientedCoordinateQuaternion b.val reverse ⋄ q)).scalar 2) r) := by
  cases reverse with
  | false =>
      let tail := q ⋄ p
      have htail : QuaternionSupported (tailBlocks+1) tail :=
        combined_tail_supported hp hq
      have hdegree : HasPolyQuaternionBlockDegree a.val 0 tail :=
        combined_tail_degree_zero hdp hdq
      have hnorm : HaarCarrierEqv (tailBlocks+1) (polyQuaternionNorm tail) polyOne :=
        combined_tail_norm hnormp hnormq
      have hbase := spinTwo_transmission tailBlocks hb a b hab w K hK tail
        htail hdegree hnorm r hr hdr
      have hleft := scalar_prefix_tail_recode a.val p q 2
      have hright := scalar_prefix_tail_recode b.val p q 2
      have hrewrite : RatPolyCoeffEqv
          (polyMul (polyMul (heatAt a.val b.val w K)
            (characterPolynomial
              (p ⋄ (PolyQuaternion.coordinateVariable a.val ⋄ q)).scalar 2)) r)
          (polyMul (polyMul (heatAt a.val b.val w K)
            (characterPolynomial
              (PolyQuaternion.coordinateVariable a.val ⋄ tail).scalar 2)) r) := by
        exact (hleft.mul_left (heatAt a.val b.val w K)).mul_right r
      have hrewrite' : RatPolyCoeffEqv
          (polyMul (characterPolynomial
            (p ⋄ (PolyQuaternion.coordinateVariable b.val ⋄ q)).scalar 2) r)
          (polyMul (characterPolynomial
            (PolyQuaternion.coordinateVariable b.val ⋄ tail).scalar 2) r) :=
        hright.mul_right r
      exact Q'.eqv_trans _ _ _ (haar_of_coeff hrewrite)
        (Q'.eqv_trans _ _ _ hbase
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (haar_of_coeff hrewrite'))))
  | true =>
      let rawTail := q ⋄ p
      let tail := PolyQuaternion.conj rawTail
      have hraw : QuaternionSupported (tailBlocks+1) rawTail :=
        combined_tail_supported hp hq
      have htail : QuaternionSupported (tailBlocks+1) tail := hraw.conj
      have hdegreeRaw : HasPolyQuaternionBlockDegree a.val 0 rawTail :=
        combined_tail_degree_zero hdp hdq
      have hdegree : HasPolyQuaternionBlockDegree a.val 0 tail := hdegreeRaw.conj
      have hnormRaw : HaarCarrierEqv (tailBlocks+1)
          (polyQuaternionNorm rawTail) polyOne :=
        combined_tail_norm hnormp hnormq
      have hnorm : HaarCarrierEqv (tailBlocks+1)
          (polyQuaternionNorm tail) polyOne := by
        exact HaarCarrierEqv.trans
          (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj rawTail)) hnormRaw
      have hbase := spinTwo_transmission tailBlocks hb a b hab w K hK tail
        htail hdegree hnorm r hr hdr
      have recode (z : Nat) : RatPolyCoeffEqv
          (characterPolynomial
            (p ⋄ (PolyQuaternion.conj (PolyQuaternion.coordinateVariable z) ⋄ q)).scalar 2)
          (characterPolynomial
            (PolyQuaternion.coordinateVariable z ⋄ tail).scalar 2) := by
        apply characterPolynomial_coeffEqv
        exact (polyQuaternion_mul_scalar_cyclic p
            (PolyQuaternion.conj (PolyQuaternion.coordinateVariable z) ⋄ q)).trans
          ((PolyQuaternionCoeffEqv.mul_assoc
            (PolyQuaternion.conj (PolyQuaternion.coordinateVariable z)) q p).scalar.trans
            ((polyQuaternion_mul_scalar_cyclic
              (PolyQuaternion.conj (PolyQuaternion.coordinateVariable z)) rawTail).trans
              (scalar_conj_comm rawTail
                (PolyQuaternion.coordinateVariable z))))
      have hleft := recode a.val
      have hright := recode b.val
      have hrewrite : RatPolyCoeffEqv
          (polyMul (polyMul (heatAt a.val b.val w K)
            (characterPolynomial
              (p ⋄ (PolyQuaternion.conj (PolyQuaternion.coordinateVariable a.val) ⋄ q)).scalar 2)) r)
          (polyMul (polyMul (heatAt a.val b.val w K)
            (characterPolynomial
              (PolyQuaternion.coordinateVariable a.val ⋄ tail).scalar 2)) r) := by
        exact (hleft.mul_left (heatAt a.val b.val w K)).mul_right r
      have hrewrite' : RatPolyCoeffEqv
          (polyMul (characterPolynomial
            (p ⋄ (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b.val) ⋄ q)).scalar 2) r)
          (polyMul (characterPolynomial
            (PolyQuaternion.coordinateVariable b.val ⋄ tail).scalar 2) r) :=
        hright.mul_right r
      exact Q'.eqv_trans _ _ _ (haar_of_coeff hrewrite)
        (Q'.eqv_trans _ _ _ hbase
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (haar_of_coeff hrewrite'))))

#print axioms spinTwo_word_step

end YMGap.Continuum.SU2QuaternionSpinTwoWordStep
