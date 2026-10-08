/-
# Conditional signed Fisher order from two actual head copies

The local cleared curvature certificate is transported through two heads
sharing the SAME surviving tail. A square identity clears the two positive
kernel factors; existing positive-window order reflection removes them only
inside Haar integration. The result is integrated order, not a polynomial
positivity certificate, a marginal derivative pin, or an interacting estimate.
No marginal or source is inverted; zero heads and zero tail are included.
-/

import YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder

namespace YMGap.Continuum.SU2QuaternionConditionalFisherOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product lift_add lift_supported)
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (head_pairing partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionHaarTailDerivative (partialHaarHeads_add partialHaarHeads_neg)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
open YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow
open YMGap.Continuum.QuaternionHaarCertifiedPositiveWindowProduct
open YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection (haar_nonnegative_of_positive_multiplier)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarClearedThreeGram (centeredFisher)
open YMGap.Continuum.SU2QuaternionConditionalSignedGramReplica (momentA momentD momentG)
open YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder (conditionalFisher)

private theorem neg_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact hp r hr

private def twoFisher (P1 P2 d1 d2 dd1 dd2 : RatPoly) : RatPoly :=
  polyAdd (polyAdd (polyMul P1 dd2) (polyMul P2 dd1))
    (polyNeg (polyAdd (polyMul d1 d2) (polyMul d1 d2)))

private theorem two_integral_pin (heads : Nat) (q P d dd : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (heads+heads)
        (polyMul (polyMul (copy heads q) (liftBoundary heads q))
          (twoFisher (copy heads P) (liftBoundary heads P)
            (copy heads d) (liftBoundary heads d) (copy heads dd) (liftBoundary heads dd))))
      (polyAdd (conditionalFisher heads q P d dd) (conditionalFisher heads q P d dd)) := by
  let tensor := fun p r => polyMul (copy heads (polyMul q p)) (liftBoundary heads (polyMul q r))
  have hraw : RatPolyCoeffEqv
      (polyMul (polyMul (copy heads q) (liftBoundary heads q))
        (twoFisher (copy heads P) (liftBoundary heads P)
          (copy heads d) (liftBoundary heads d) (copy heads dd) (liftBoundary heads dd)))
      (polyAdd (polyAdd (tensor P dd) (tensor dd P))
        (polyNeg (polyAdd (tensor d d) (tensor d d)))) := by
    simp only [tensor, copy_mul, lift_product, twoFisher]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1))
        (.add (.add (.mul (.var 2) (.var 7)) (.mul (.var 3) (.var 6)))
          (.neg (.add (.mul (.var 4) (.var 5)) (.mul (.var 4) (.var 5))))))
      (.add (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 7)))
        (.mul (.mul (.var 0) (.var 6)) (.mul (.var 1) (.var 3))))
        (.neg (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))
          (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5))))))
      (by decide) (fun
        | 0 => copy heads q | 1 => liftBoundary heads q
        | 2 => copy heads P | 3 => liftBoundary heads P | 4 => copy heads d
        | 5 => liftBoundary heads d | 6 => copy heads dd | _ => liftBoundary heads dd)
  refine (partialHaarHeads_congr (heads+heads) hraw).trans ?_
  rw [partialHaarHeads_add, partialHaarHeads_add]
  have ht (p r : RatPoly) := replica_product heads (polyMul q p) (polyMul q r)
  have hn := (partialHaarHeads_neg (heads+heads) (polyAdd (tensor d d) (tensor d d))).trans
    (RatPolyCoeffEqv.neg (by
      rw [partialHaarHeads_add]
      exact (ht d d).add (ht d d)))
  refine (((ht P dd).add (ht dd P)).add hn).trans ?_
  unfold conditionalFisher centeredFisher momentA momentD momentG
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.var 0) (.var 2)) (.mul (.var 2) (.var 0)))
      (.neg (.add (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1)))))
    (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1))))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))
    (by decide) (fun
      | 0 => partialHaarHeads heads (polyMul q P)
      | 1 => partialHaarHeads heads (polyMul q d) | _ => partialHaarHeads heads (polyMul q dd))

/-- The complete signed Fisher moment is nonnegative under every certified
surviving insertion. Only positive local kernel windows are reflected; q may
vanish, and d/dd remain precomputed signed jets rather than marginal derivatives. -/
theorem conditional_fisher_nonnegative (tail heads : Nat) (q P d dd R : RatPoly)
    {ell upper : Q'}
    (hq : SupportedQuaternionBlocks (tail+heads) q)
    (hP : SupportedQuaternionBlocks (tail+heads) P)
    (hd : SupportedQuaternionBlocks (tail+heads) d)
    (hdd : SupportedQuaternionBlocks (tail+heads) dd)
    (Qcert : Certificate (tail+heads) q)
    (Ccert : Certificate (tail+heads) (polyAdd (polyMul P dd) (polyNeg (polyMul d d))))
    (Rcert : Certificate tail R)
    (hell : (0 : Q') < ell) (hupper : (0 : Q') < upper) (hle : ell ≤ upper)
    (L : Certificate (tail+heads) (polyAdd P (polyNeg (cap ell))))
    (U : Certificate (tail+heads) (polyAdd (cap upper) (polyNeg P))) :
    (0 : Q') ≤ quaternionHaar tail (polyMul R (conditionalFisher heads q P d dd)) := by
  let H := heads+heads
  let P1 := copy heads P
  let P2 := liftBoundary heads P
  let d1 := copy heads d
  let d2 := liftBoundary heads d
  let dd1 := copy heads dd
  let dd2 := liftBoundary heads dd
  let T := twoFisher P1 P2 d1 d2 dd1 dd2
  have hp1 := copySupported tail heads hP
  have hp2 : SupportedQuaternionBlocks (tail+H) P2 := by
    simpa only [P2, H, Nat.add_assoc] using lift_supported hP heads
  have hd1 := copySupported tail heads hd
  have hd2 : SupportedQuaternionBlocks (tail+H) d2 := by
    simpa only [d2, H, Nat.add_assoc] using lift_supported hd heads
  have hdd1 := copySupported tail heads hdd
  have hdd2 : SupportedQuaternionBlocks (tail+H) dd2 := by
    simpa only [dd2, H, Nat.add_assoc] using lift_supported hdd heads
  have hT : SupportedQuaternionBlocks (tail+H) T :=
    supported_add (supported_add (supported_polyMul hp1 hdd2) (supported_polyMul hp2 hdd1))
      (neg_supported (supported_add (supported_polyMul hd1 hd2) (supported_polyMul hd1 hd2)))
  have hC := supported_add (supported_polyMul hP hdd) (neg_supported (supported_polyMul hd hd))
  have C1 : Certificate (tail+H) (polyAdd (polyMul P1 dd1) (polyNeg (polyMul d1 d1))) := by
    simpa only [P1, dd1, d1, H, copy_add, copy_mul, copy_neg] using
      copyCertificate tail heads _ hC Ccert
  have C2 : Certificate (tail+H) (polyAdd (polyMul P2 dd2) (polyNeg (polyMul d2 d2))) := by
    simpa only [P2, dd2, d2, H, Nat.add_assoc, lift_add, lift_product, lift_neg] using
      lift_certificate heads Ccert
  let wedge := polyAdd (polyMul P2 d1) (polyNeg (polyMul P1 d2))
  have hwedge : SupportedQuaternionBlocks (tail+H) wedge :=
    supported_add (supported_polyMul hp2 hd1) (neg_supported (supported_polyMul hp1 hd2))
  let cleared := ((Certificate.square P2 hp2).mul C1).add
    (((Certificate.square P1 hp1).mul C2).add (Certificate.square wedge hwedge))
  have hcleared : RatPolyCoeffEqv (polyMul (polyMul P1 P2) T)
      (polyAdd (polyMul (polyMul P2 P2) (polyAdd (polyMul P1 dd1) (polyNeg (polyMul d1 d1))))
        (polyAdd (polyMul (polyMul P1 P1) (polyAdd (polyMul P2 dd2) (polyNeg (polyMul d2 d2))))
          (polyMul wedge wedge))) := by
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1))
        (.add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4)))
          (.neg (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))))))
      (.add (.mul (.mul (.var 1) (.var 1)) (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 2) (.var 2)))))
        (.add (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 3) (.var 3)))))
          (.mul (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 0) (.var 3))))
            (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 0) (.var 3)))))))
      (by decide) (fun | 0 => P1 | 1 => P2 | 2 => d1 | 3 => d2 | 4 => dd1 | _ => dd2)
  let W := multiplyPositiveWindows hp1 hp2 hell hupper hell hupper hle hle
    (copyLowerCertificate tail heads hP L) (copyUpperCertificate tail heads hP U)
    (by simpa only [Nat.add_assoc] using liftLowerCertificate (tail+heads) heads L)
    (by simpa only [Nat.add_assoc] using liftUpperCertificate (tail+heads) heads U)
  let background := polyMul (polyMul (copy heads q) (liftBoundary heads q)) (liftBoundary H R)
  have Q2 : Certificate (tail+H) (liftBoundary heads q) := by
    simpa only [H, Nat.add_assoc] using lift_certificate heads Qcert
  have B : Certificate (tail+H) background :=
    ((copyCertificate tail heads q hq Qcert).mul Q2).mul (lift_certificate H Rcert)
  have h := haar_nonnegative_of_positive_multiplier W.support hT
    W.lowerPositive W.upperPositive W.endpointsOrdered W.lowerCertificate W.upperCertificate
    B (Certificate.ofCoeff hcleared cleared)
  have hmove : RatPolyCoeffEqv (polyMul background T)
      (polyMul (polyMul (polyMul (copy heads q) (liftBoundary heads q)) T) (liftBoundary H R)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun
        | 0 => polyMul (copy heads q) (liftBoundary heads q)
        | 1 => liftBoundary H R | _ => T)
  have hint : Q'.eqv (quaternionHaar (tail+H) (polyMul background T))
      (2*quaternionHaar tail (polyMul R (conditionalFisher heads q P d dd))) := by
    refine Q'.eqv_trans _ _ _ (haar_of_coeff hmove)
      (Q'.eqv_trans _ _ _ (head_pairing tail H _ R) ?_)
    refine Q'.eqv_trans _ _ _
      (haar_of_coeff ((two_integral_pin heads q P d dd).mul_right R)) ?_
    have hscale : RatPolyCoeffEqv
        (polyMul (polyAdd (conditionalFisher heads q P d dd)
          (conditionalFisher heads q P d dd)) R)
        (polySmul 2 (polyMul R (conditionalFisher heads q P d dd))) := by
      exact (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.var 0) (.var 0)) (.var 1))
        (.mul (.const 2) (.mul (.var 1) (.var 0)))
        (by decide) (fun | 0 => conditionalFisher heads q P d dd | _ => R)).trans
          (QuaternionHaarPolynomialSquareBound.cap_mul_left 2 _)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hscale) (quaternionHaar_polySmul tail 2 _)
  have hn := Q'.le_trans' _ _ _ h (Q'.le_of_eqv hint)
  have hs : (2 : Q')*0 ≤ 2*quaternionHaar tail (polyMul R (conditionalFisher heads q P d dd)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv 2)) hn
  exact Q'.le_of_mul_le_mul_left hs (by decide : (0 : Q') < 2)

#print axioms conditional_fisher_nonnegative

end YMGap.Continuum.SU2QuaternionConditionalFisherOrder
