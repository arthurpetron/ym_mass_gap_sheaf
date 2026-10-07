/-
# Positive unital residual completion of a finite reciprocal prediction

Keep the actual shared-tail density W and its head moments a,b,H.  Positive
finite reciprocal G and its residual r=1-a*G give the auxiliary prediction
G*b+r*u.  Its Jensen gap is G^2*det(W,p) plus G*r times the ORIGINAL window
difference square.  Neither the density nor its conditional mass is inverted;
only the supplied positive rational upper cap enters the finite reciprocal.

This does not replace the original action/transfer by this auxiliary map.
No invariant density, OS-norm identification, RG map, strict contraction,
changing-action estimate or continuum gap is supplied here.
-/

import YMGap.Continuum.QuaternionHaarPositiveWindowInverse
import YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
import YMGap.Continuum.SU2QuaternionHaarTailDerivative

namespace YMGap.Continuum.QuaternionHaarUnitalReciprocalPrediction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant determinant_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse

local notation "I" heads:arg p:arg => partialHaarHeads heads p

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Positivity of the finite corrector is constructed, including degree zero. -/
def corrector_certificate {blocks : Nat} {R : RatPoly}
    (P : Certificate blocks (polyNeg R)) :
    (k : Nat) → Certificate blocks (corrector R k)
  | 0 => Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (Certificate.constant blocks 0 (Q'.le_refl' _))
  | k+1 => (Certificate.one blocks).add (P.mul (corrector_certificate P k))

/-- Only the actual upper-window certificate is needed for positivity. -/
def reciprocal_certificate {blocks : Nat} {a : RatPoly} {upper : Q'}
    (_ha : SupportedQuaternionBlocks blocks a) (hupper : (0 : Q') < upper)
    (U : Certificate blocks (polyAdd
      (QuaternionHaarPolynomialSquareBound.cap upper) (polyNeg a))) (k : Nat) :
    Certificate blocks (reciprocal a upper hupper k) :=
  (corrector_certificate (remainderNegative hupper U) k).smul _
    (Q'.le_of_lt (scale_positive upper hupper))

/-- Literal finite residual; not a limiting reciprocal error. -/
def reciprocalResidual (a : RatPoly) (upper : Q') (hupper : (0 : Q') < upper)
    (k : Nat) : RatPoly :=
  polyAdd polyOne (polyNeg (polyMul a (reciprocal a upper hupper k)))

theorem reciprocalResidual_supported {blocks : Nat} {a : RatPoly}
    (ha : SupportedQuaternionBlocks blocks a) (upper : Q')
    (hupper : (0 : Q') < upper) (k : Nat) :
    SupportedQuaternionBlocks blocks (reciprocalResidual a upper hupper k) :=
  supported_add (supported_one blocks)
    (support_neg (supported_polyMul ha (reciprocal_supported ha upper hupper k)))

/-- Structural cancellation on every surviving insertion. -/
theorem reciprocalResidual_cancellation (a : RatPoly) (upper : Q')
    (hupper : (0 : Q') < upper) (k : Nat) :
    RatPolyCoeffEqv
      (polyAdd (polyMul a (reciprocal a upper hupper k))
        (reciprocalResidual a upper hupper k)) polyOne :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.add (.const 1) (.neg (.var 0)))) (.const 1)
    (by decide) (fun _ => polyMul a (reciprocal a upper hupper k))

/-- The residual sign is produced from the finite positive-window expansion. -/
def reciprocalResidual_certificate {blocks : Nat} {a : RatPoly} {upper : Q'}
    (hupper : (0 : Q') < upper)
    (U : Certificate blocks (polyAdd
      (QuaternionHaarPolynomialSquareBound.cap upper) (polyNeg a))) (k : Nat) :
    Certificate blocks (reciprocalResidual a upper hupper k) := by
  let G := reciprocal a upper hupper k
  let R := remainder a upper hupper
  have he : RatPolyCoeffEqv (reciprocalResidual a upper hupper k) (residual R k) :=
    ((reciprocal_cancellation a upper hupper k).symm.add
      (RatPolyCoeffEqv.refl (polyNeg (polyMul a G)))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
        (by decide) (fun | 0 => polyMul a G | _ => residual R k))
  exact Certificate.ofCoeff he (residualCertificate (remainderNegative hupper U) k)

/-- Auxiliary prediction with the literal output polynomial retained. -/
def prediction (heads : Nat) (W p out G r : RatPoly) : RatPoly :=
  polyAdd (polyMul G (I heads (polyMul W p))) (polyMul r out)

def predictionSecondMoment (heads : Nat) (W p out G r : RatPoly) : RatPoly :=
  polyAdd (polyMul G (I heads (polyMul W (polyMul p p))))
    (polyMul r (polyMul out out))

theorem prediction_supported {tail heads : Nat} {W p out G r : RatPoly}
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hp : SupportedQuaternionBlocks (tail+heads) p)
    (hout : SupportedQuaternionBlocks tail out)
    (hG : SupportedQuaternionBlocks tail G) (hr : SupportedQuaternionBlocks tail r) :
    SupportedQuaternionBlocks tail (prediction heads W p out G r) :=
  supported_add
    (supported_polyMul hG (partialHaarHeads_supported tail heads _ (supported_polyMul hW hp)))
    (supported_polyMul hr hout)

/-- Positive inputs give a positive prediction under the same density. -/
def prediction_certificate (tail heads : Nat) (W p out G r : RatPoly)
    (PW : Certificate (tail+heads) W) (Pp : Certificate (tail+heads) p)
    (Pout : Certificate tail out) (PG : Certificate tail G) (PR : Certificate tail r) :
    Certificate tail (prediction heads W p out G r) :=
  (PG.mul (partialHaarHeads_certificate tail heads (PW.mul Pp))).add (PR.mul Pout)

/-- Unit preservation uses only structural cancellation, not unit mass. -/
theorem prediction_one (heads : Nat) (W G r : RatPoly)
    (hunit : RatPolyCoeffEqv (polyAdd (polyMul (I heads W) G) r) polyOne) :
    RatPolyCoeffEqv (prediction heads W polyOne polyOne G r) polyOne :=
  (((partialHaarHeads_congr heads (RatPolyCoeffEqv.mul_one W)).mul_left G).add
    (RatPolyCoeffEqv.mul_one r)).trans
    (((RatPolyCoeffEqv.mul_comm G (I heads W)).add (RatPolyCoeffEqv.refl r)).trans hunit)

private def difference (heads : Nat) (p out : RatPoly) : RatPoly :=
  polyAdd p (polyNeg (liftBoundary heads out))

private theorem difference_square_pin (heads : Nat) (W p out : RatPoly) :
    RatPolyCoeffEqv (I heads (polyMul W
      (polyMul (difference heads p out) (difference heads p out))))
      (polyAdd (I heads (polyMul W (polyMul p p)))
        (polyAdd (polyNeg (polyMul (I heads (polyMul W p)) out))
          (polyAdd (polyNeg (polyMul (I heads (polyMul W p)) out))
            (polyMul (I heads W) (polyMul out out))))) := by
  let cross := polyMul (polyMul W p) (liftBoundary heads out)
  have he : RatPolyCoeffEqv (polyMul W
      (polyMul (difference heads p out) (difference heads p out)))
      (polyAdd (polyMul W (polyMul p p))
        (polyAdd (polyNeg cross) (polyAdd (polyNeg cross)
          (polyMul W (liftBoundary heads (polyMul out out)))))) := by
    unfold difference
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2)))
        (.add (.var 1) (.neg (.var 2)))))
      (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.add (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))
          (.add (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))
            (.mul (.var 0) (.mul (.var 2) (.var 2))))))
      (by decide) (fun | 0 => W | 1 => p | _ => liftBoundary heads out)
  have hc := partialHaarHeads_mul_lift heads (polyMul W p) out
  have hu := partialHaarHeads_mul_lift heads W (polyMul out out)
  have h := partialHaarHeads_congr heads he
  rw [partialHaarHeads_add, partialHaarHeads_add, partialHaarHeads_add] at h
  exact h.trans ((RatPolyCoeffEqv.refl _).add
    (((partialHaarHeads_neg heads cross).trans (RatPolyCoeffEqv.neg hc)).add
      (((partialHaarHeads_neg heads cross).trans (RatPolyCoeffEqv.neg hc)).add hu)))

/-- Exact Jensen decomposition, preserving the complete original density
and the initial-versus-output difference square. -/
theorem jensen_pin (heads : Nat) (W p out G r : RatPoly)
    (hunit : RatPolyCoeffEqv (polyAdd (polyMul (I heads W) G) r) polyOne) :
    RatPolyCoeffEqv
      (polyAdd (predictionSecondMoment heads W p out G r)
        (polyNeg (polyMul (prediction heads W p out G r)
          (prediction heads W p out G r))))
      (polyAdd (polyMul (polyMul G G) (determinant heads W p))
        (polyMul (polyMul G r) (I heads (polyMul W
          (polyMul (difference heads p out) (difference heads p out)))))) := by
  let a := I heads W
  let b := I heads (polyMul W p)
  let H := I heads (polyMul W (polyMul p p))
  let F := predictionSecondMoment heads W p out G r
  have hF : RatPolyCoeffEqv (polyMul (polyAdd (polyMul a G) r) F) F :=
    ((hunit.mul (RatPolyCoeffEqv.refl F)).trans (RatPolyCoeffEqv.one_mul F))
  have hring : RatPolyCoeffEqv
      (polyAdd (polyMul (polyAdd (polyMul a G) r) F)
        (polyNeg (polyMul (prediction heads W p out G r)
          (prediction heads W p out G r))))
      (polyAdd (polyMul (polyMul G G) (determinant heads W p))
        (polyMul (polyMul G r)
          (polyAdd H (polyAdd (polyNeg (polyMul b out))
            (polyAdd (polyNeg (polyMul b out)) (polyMul a (polyMul out out))))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.mul (.add (.mul (.var 0) (.var 1)) (.var 2))
          (.add (.mul (.var 1) (.var 3)) (.mul (.var 2) (.mul (.var 5) (.var 5)))))
        (.neg (.mul (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 5)))
          (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 5))))))
      (.add
        (.mul (.mul (.var 1) (.var 1))
          (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 4) (.var 4)))))
        (.mul (.mul (.var 1) (.var 2))
          (.add (.var 3) (.add (.neg (.mul (.var 4) (.var 5)))
            (.add (.neg (.mul (.var 4) (.var 5)))
              (.mul (.var 0) (.mul (.var 5) (.var 5))))))))
      (by decide) (fun | 0 => a | 1 => G | 2 => r | 3 => H | 4 => b | _ => out)
  exact (hF.symm.add (RatPolyCoeffEqv.refl _)).trans
    (hring.trans ((RatPolyCoeffEqv.refl _).add
      ((difference_square_pin heads W p out).symm.mul_left (polyMul G r))))

/-- The positive-cone Jensen witness is constructed from the full window
replica and difference square. The structural mass relation is algebraic;
no analytic Jensen conclusion or conditional unit mass is an input. -/
def jensen_certificate (tail heads : Nat) (W p out G r : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hp : SupportedQuaternionBlocks (tail+heads) p)
    (hout : SupportedQuaternionBlocks tail out)
    (hG : SupportedQuaternionBlocks tail G)
    (_hr : SupportedQuaternionBlocks tail r)
    (PW : Certificate (tail+heads) W) (PG : Certificate tail G) (PR : Certificate tail r)
    (hunit : RatPolyCoeffEqv (polyAdd (polyMul (I heads W) G) r) polyOne) :
    Certificate tail
      (polyAdd (predictionSecondMoment heads W p out G r)
        (polyNeg (polyMul (prediction heads W p out G r)
          (prediction heads W p out G r)))) := by
  have hd : SupportedQuaternionBlocks (tail+heads) (difference heads p out) :=
    supported_add hp (support_neg (lift_supported hout heads))
  have PD := determinant_certificate tail heads W p hW hp PW
  have PS := partialHaarHeads_certificate tail heads
    (PW.mul (Certificate.square (difference heads p out) hd))
  exact Certificate.ofCoeff (jensen_pin heads W p out G r hunit)
    (((Certificate.square G hG).mul PD).add ((PG.mul PR).mul PS))

#print axioms corrector_certificate
#print axioms reciprocal_certificate
#print axioms reciprocalResidual
#print axioms reciprocalResidual_supported
#print axioms reciprocalResidual_cancellation
#print axioms reciprocalResidual_certificate
#print axioms prediction
#print axioms predictionSecondMoment
#print axioms prediction_supported
#print axioms prediction_certificate
#print axioms prediction_one
#print axioms jensen_pin
#print axioms jensen_certificate

end YMGap.Continuum.QuaternionHaarUnitalReciprocalPrediction
