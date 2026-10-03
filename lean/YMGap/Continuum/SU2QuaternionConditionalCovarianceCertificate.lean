/-
# Actual conditional covariance from a two-copy wedge square

Only the Haar head is copied. Every other coordinate is shared. Two
arbitrary signed observables and the complete supplied positive weight
remain literal throughout. The conditional Gram determinant receives an
ORIGINAL Haar Certificate by integrating the two actual weight copies
times an explicit wedge square. No pointwise positivity-to-certificate
rule, reciprocal normalizer, covariance premise, or independence of the
weight is used.

For normalized conditional heat this can be applied to the two computed
conditionally centered observables. This module does not identify a source
heat loss with interacting OWN variance or prove a changing-family budget.
-/

import YMGap.Continuum.SU2QuaternionConditionalVarianceReplica

namespace YMGap.Continuum.SU2QuaternionConditionalCovarianceCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionSpareHeadCopy
open YMGap.Continuum.SU2QuaternionSharedHeadGramPairing
open YMGap.Continuum.SU2QuaternionConditionalVarianceReplica (replica_product)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier

local notation "A" => partialHaarHead

/-- The actual polynomial-valued weighted two-observable Gram determinant.
For normalized W, centering its inputs gives the covariance determinant. -/
def conditionalGram (W p q : RatPoly) : RatPoly :=
  polyAdd
    (polyMul (A (polyMul W (polyMul p p))) (A (polyMul W (polyMul q q))))
    (polyNeg (polyMul (A (polyMul W (polyMul p q))) (A (polyMul W (polyMul p q)))))

/-- Both copies share every original spectator variable. -/
def covarianceWedge (p q : RatPoly) : RatPoly :=
  polyAdd (polyMul (copy p) (liftHead q))
    (polyNeg (polyMul (copy q) (liftHead p)))

def covarianceReplica (W p q : RatPoly) : RatPoly :=
  polyMul (polyMul (copy W) (liftHead W))
    (polyMul (covarianceWedge p q) (covarianceWedge p q))

private def expansion (W p q : RatPoly) : RatPoly :=
  let P := polyMul W (polyMul p p)
  let Q := polyMul W (polyMul q q)
  let C := polyMul W (polyMul p q)
  polyAdd (polyAdd (polyMul (copy P) (liftHead Q)) (polyMul (copy Q) (liftHead P)))
    (polyAdd (polyNeg (polyMul (copy C) (liftHead C)))
      (polyNeg (polyMul (copy C) (liftHead C))))

private theorem weighted_copy_product (tail : Nat) (W p q : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    HaarCarrierEqv (tail+2) (copy (polyMul W (polyMul p q)))
      (polyMul (copy W) (polyMul (copy p) (copy q))) :=
  (copy_mul_carrier (by omega) hW (supported_polyMul hp hq)).trans
    (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _) (copy_mul_carrier (by omega) hp hq))

private theorem replica_expansion (tail : Nat) (W p q : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    HaarCarrierEqv (tail+2) (covarianceReplica W p q) (expansion W p q) := by
  have hP := weighted_copy_product tail W p p hW hp hp
  have hQ := weighted_copy_product tail W q q hW hq hq
  have hC := weighted_copy_product tail W p q hW hp hq
  have hexp : HaarCarrierEqv (tail+2) (expansion W p q)
      (polyAdd
        (polyAdd
          (polyMul (polyMul (copy W) (polyMul (copy p) (copy p)))
            (polyMul (liftHead W) (polyMul (liftHead q) (liftHead q))))
          (polyMul (polyMul (copy W) (polyMul (copy q) (copy q)))
            (polyMul (liftHead W) (polyMul (liftHead p) (liftHead p)))))
        (polyAdd
          (polyNeg (polyMul (polyMul (copy W) (polyMul (copy p) (copy q)))
            (polyMul (liftHead W) (polyMul (liftHead p) (liftHead q)))))
          (polyNeg (polyMul (polyMul (copy W) (polyMul (copy p) (copy q)))
            (polyMul (liftHead W) (polyMul (liftHead p) (liftHead q))))))) := by
    dsimp only [expansion]
    simp only [liftHead_mul]
    exact HaarCarrierEqv.add
      (HaarCarrierEqv.add (HaarCarrierEqv.mul hP (HaarCarrierEqv.refl _ _))
        (HaarCarrierEqv.mul hQ (HaarCarrierEqv.refl _ _)))
      (HaarCarrierEqv.add (HaarCarrierEqv.neg (HaarCarrierEqv.mul hC (HaarCarrierEqv.refl _ _)))
        (HaarCarrierEqv.neg (HaarCarrierEqv.mul hC (HaarCarrierEqv.refl _ _))))
  refine (RatPolyCoeffEqv.haarCarrier ?_).trans hexp.symm
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 3))
      (.mul (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4))))
        (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4))))))
    (.add
      (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
          (.mul (.var 3) (.mul (.var 5) (.var 5))))
        (.mul (.mul (.var 0) (.mul (.var 2) (.var 2)))
          (.mul (.var 3) (.mul (.var 4) (.var 4)))))
      (.add (.neg (.mul (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 3) (.mul (.var 4) (.var 5)))))
        (.neg (.mul (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 3) (.mul (.var 4) (.var 5)))))))
    (by decide) (fun
      | 0 => copy W | 1 => copy p | 2 => copy q
      | 3 => liftHead W | 4 => liftHead p | _ => liftHead q)

private theorem partial_neg (p : RatPoly) :
    RatPolyCoeffEqv (A (polyNeg p)) (polyNeg (A p)) := by
  have ht : RatPolyTermwiseEqv (A (polyNeg p)) (polyNeg (A p)) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih => exact ⟨rfl, Q'.neg_mul_eqv _ _, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem twice_neg (p : RatPoly) :
    RatPolyCoeffEqv (A (A (polyNeg p))) (polyNeg (A (A p))) :=
  (partialHaarHead_congr (partial_neg p)).trans (partial_neg (A p))

/-- Exact two-copy covariance expansion under EVERY surviving insertion. -/
theorem covarianceReplica_identity (tail : Nat) (W p q : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    HaarCarrierEqv tail (A (A (covarianceReplica W p q)))
      (polyAdd (conditionalGram W p q) (conditionalGram W p q)) := by
  have h := partialHaarHead_carrier (partialHaarHead_carrier (replica_expansion tail W p q hW hp hq))
  refine h.trans (RatPolyCoeffEqv.haarCarrier ?_)
  dsimp only [expansion, conditionalGram]
  simp only [partialHaarHead_add]
  have hc := (twice_neg _).trans
    (RatPolyCoeffEqv.neg (replica_product (polyMul W (polyMul p q)) (polyMul W (polyMul p q))))
  refine (RatPolyCoeffEqv.add
    (RatPolyCoeffEqv.add
      (replica_product (polyMul W (polyMul p p)) (polyMul W (polyMul q q)))
      (replica_product (polyMul W (polyMul q q)) (polyMul W (polyMul p p))))
    (RatPolyCoeffEqv.add hc hc)).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 0)))
      (.add (.neg (.mul (.var 2) (.var 2))) (.neg (.mul (.var 2) (.var 2)))))
    (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2)))))
    (by decide) (fun
      | 0 => A (polyMul W (polyMul p p))
      | 1 => A (polyMul W (polyMul q q)) | _ => A (polyMul W (polyMul p q)))

private def copiedCertificate (tail : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W) (P : Certificate (tail+1) W) :
    Certificate (tail+2) (copy W) :=
  let s := spareSwap (tail+1) (by omega)
  .transport
    (carrierOfPrefix (reindex_supported s (liftHead W)) (copy_supported (by omega) hW)
      (copy_reindex_prefix (tail+1) (by omega) W)).symm
    (reindex_certificate s (lift_supported hW 1) (lift_certificate 1 P))

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- The witness is the literal positive weight copies times a wedge square. -/
def covarianceReplica_certificate (tail : Nat) (W p q : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) (P : Certificate (tail+1) W) :
    Certificate (tail+2) (covarianceReplica W p q) :=
  (Certificate.mul (copiedCertificate tail W hW P) (lift_certificate 1 P)).mul
    (.square (covarianceWedge p q)
      (supported_add (supported_polyMul (copy_supported (by omega) hp) (lift_supported hq 1))
        (supported_neg (supported_polyMul (copy_supported (by omega) hq) (lift_supported hp 1)))))

private theorem half_double (p : RatPoly) :
    RatPolyCoeffEqv (polySmul HalfPow.half (polyAdd p p)) p := by
  intro weight
  exact Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ratWeightedSum_add weight p p))
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) (ExpNeg.two_halves _)))

/-- Constructed polynomial-valued conditional Cauchy--Schwarz on the original
shared-spectator carrier. No covariance inequality is supplied as input. -/
def conditionalGram_certificate (tail : Nat) (W p q : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) (P : Certificate (tail+1) W) :
    Certificate tail (conditionalGram W p q) :=
  .ofCoeff (half_double _).symm
    (.smul HalfPow.half (by decide)
      (.transport (covarianceReplica_identity tail W p q hW hp hq).symm
        (partialHaarHead_certificate tail
          (partialHaarHead_certificate (tail+1) (covarianceReplica_certificate tail W p q hW hp hq P)))))

/-- Any certified original surrounding action may be inserted without
averaging or replacing the shared spectators. -/
theorem spectator_nonnegative (tail : Nat) (W p q R : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (P : Certificate (tail+1) W) (PR : Certificate tail R) :
    (0 : Q') ≤ quaternionHaar tail (polyMul R (conditionalGram W p q)) :=
  (PR.mul (conditionalGram_certificate tail W p q hW hp hq P)).haar_nonnegative

end YMGap.Continuum.SU2QuaternionConditionalCovarianceCertificate

#print axioms YMGap.Continuum.SU2QuaternionConditionalCovarianceCertificate.conditionalGram
#print axioms YMGap.Continuum.SU2QuaternionConditionalCovarianceCertificate.covarianceWedge
#print axioms YMGap.Continuum.SU2QuaternionConditionalCovarianceCertificate.covarianceReplica
#print axioms YMGap.Continuum.SU2QuaternionConditionalCovarianceCertificate.covarianceReplica_identity
#print axioms YMGap.Continuum.SU2QuaternionConditionalCovarianceCertificate.covarianceReplica_certificate
#print axioms YMGap.Continuum.SU2QuaternionConditionalCovarianceCertificate.conditionalGram_certificate
#print axioms YMGap.Continuum.SU2QuaternionConditionalCovarianceCertificate.spectator_nonnegative
