/-
# Full two-input conditional Gram on the ORIGINAL shared-tail carrier

Both head copies retain the same surviving variables. Their complete
positive weight copies multiply the literal signed wedge square. The
two-head integral is coefficient-equivalent to twice the unnormalized
Gram determinant, giving a constructed Certificate without any inverse.
Only W is positive: both inputs a,c may be signed. Zero heads and zero
tail are included. No useful relative norm or scaling bound is claimed.
-/

import YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
import YMGap.Continuum.SU2QuaternionHaarTailDerivative

namespace YMGap.Continuum.SU2QuaternionMultiHeadConditionalGram

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
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product lift_supported)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
  (partialHaarHeads_add partialHaarHeads_neg)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
  (copy copy_mul copySupported copyCertificate replica_product)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation "I" heads:arg p:arg => partialHaarHeads heads p
local infix:50 " ≈ " => Q'.eqv

/-- The actual polynomial-valued two-input Gram, with its normalizer absent. -/
def conditionalGram (heads : Nat) (W a c : RatPoly) : RatPoly :=
  polyAdd
    (polyMul (I heads (polyMul W (polyMul a a)))
      (I heads (polyMul W (polyMul c c))))
    (polyNeg (polyMul (I heads (polyMul W (polyMul a c)))
      (I heads (polyMul W (polyMul a c)))))

/-- The surviving tail is shared in BOTH factors of each signed term. -/
def conditionalWedge (heads : Nat) (a c : RatPoly) : RatPoly :=
  polyAdd (polyMul (copy heads a) (liftBoundary heads c))
    (polyNeg (polyMul (copy heads c) (liftBoundary heads a)))

def conditionalReplica (heads : Nat) (W a c : RatPoly) : RatPoly :=
  polyMul (polyMul (copy heads W) (liftBoundary heads W))
    (polyMul (conditionalWedge heads a c) (conditionalWedge heads a c))

private def expansion (heads : Nat) (W a c : RatPoly) : RatPoly :=
  let AA := polyMul W (polyMul a a)
  let CC := polyMul W (polyMul c c)
  let AC := polyMul W (polyMul a c)
  let cross := polyMul (copy heads AC) (liftBoundary heads AC)
  polyAdd
    (polyAdd (polyMul (copy heads AA) (liftBoundary heads CC))
      (polyMul (copy heads CC) (liftBoundary heads AA)))
    (polyAdd (polyNeg cross) (polyNeg cross))

private theorem replica_expansion (heads : Nat) (W a c : RatPoly) :
    RatPolyCoeffEqv (conditionalReplica heads W a c) (expansion heads W a c) := by
  dsimp only [conditionalReplica, conditionalWedge, expansion]
  simp only [copy_mul, lift_product]
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
      | 0 => copy heads W
      | 1 => copy heads a
      | 2 => copy heads c
      | 3 => liftBoundary heads W
      | 4 => liftBoundary heads a
      | _ => liftBoundary heads c)

/-- Exact coefficient identity after integrating ONLY the two head slices.
Every surviving insertion is preserved; no bare-Haar replacement is made. -/
theorem conditionalReplica_identity (heads : Nat) (W a c : RatPoly) :
    RatPolyCoeffEqv (I (heads+heads) (conditionalReplica heads W a c))
      (polyAdd (conditionalGram heads W a c) (conditionalGram heads W a c)) := by
  refine (partialHaarHeads_congr (heads+heads) (replica_expansion heads W a c)).trans ?_
  dsimp only [expansion]
  simp only [partialHaarHeads_add]
  have hc := (partialHaarHeads_neg (heads+heads) _).trans
    (RatPolyCoeffEqv.neg
      (replica_product heads (polyMul W (polyMul a c)) (polyMul W (polyMul a c))))
  refine (RatPolyCoeffEqv.add
    (RatPolyCoeffEqv.add
      (replica_product heads (polyMul W (polyMul a a)) (polyMul W (polyMul c c)))
      (replica_product heads (polyMul W (polyMul c c)) (polyMul W (polyMul a a))))
    (RatPolyCoeffEqv.add hc hc)).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 0)))
      (.add (.neg (.mul (.var 2) (.var 2))) (.neg (.mul (.var 2) (.var 2)))))
    (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2)))))
    (by decide) (fun
      | 0 => I heads (polyMul W (polyMul a a))
      | 1 => I heads (polyMul W (polyMul c c))
      | _ => I heads (polyMul W (polyMul a c)))

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Actual positive two-copy witness; neither signed input needs positivity. -/
def conditionalReplica_certificate (tail heads : Nat) (W a c : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (ha : SupportedQuaternionBlocks (tail+heads) a)
    (hc : SupportedQuaternionBlocks (tail+heads) c)
    (P : Certificate (tail+heads) W) :
    Certificate (tail+(heads+heads)) (conditionalReplica heads W a c) := by
  have PL : Certificate (tail+(heads+heads)) (liftBoundary heads W) := by
    simpa only [Nat.add_assoc] using lift_certificate heads P
  have haL : SupportedQuaternionBlocks (tail+(heads+heads)) (liftBoundary heads a) := by
    simpa only [Nat.add_assoc] using lift_supported ha heads
  have hcL : SupportedQuaternionBlocks (tail+(heads+heads)) (liftBoundary heads c) := by
    simpa only [Nat.add_assoc] using lift_supported hc heads
  exact ((copyCertificate tail heads W hW P).mul PL).mul
    (Certificate.square _
      (supported_add (supported_polyMul (copySupported tail heads ha) hcL)
        (supported_neg (supported_polyMul (copySupported tail heads hc) haL))))

private theorem half_double (p : RatPoly) :
    RatPolyCoeffEqv (polySmul HalfPow.half (polyAdd p p)) p := by
  intro weight
  exact Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ratWeightedSum_add weight p p))
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) (ExpNeg.two_halves _)))

/-- Full multi-head conditional Gram Certificate from its original replica.
No source-sign, positive normalizer, division or assumed Gram bound is used. -/
def conditionalGram_certificate (tail heads : Nat) (W a c : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (ha : SupportedQuaternionBlocks (tail+heads) a)
    (hc : SupportedQuaternionBlocks (tail+heads) c)
    (P : Certificate (tail+heads) W) :
    Certificate tail (conditionalGram heads W a c) :=
  .ofCoeff (half_double _).symm
    (.smul HalfPow.half (by decide)
      (.ofCoeff (conditionalReplica_identity heads W a c).symm
        (partialHaarHeads_certificate tail (heads+heads)
          (conditionalReplica_certificate tail heads W a c hW ha hc P))))

/-- Any certified surrounding tail action remains literal and shared. -/
theorem spectator_nonnegative (tail heads : Nat) (W a c R : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (ha : SupportedQuaternionBlocks (tail+heads) a)
    (hc : SupportedQuaternionBlocks (tail+heads) c)
    (P : Certificate (tail+heads) W) (PR : Certificate tail R) :
    (0 : Q') ≤ quaternionHaar tail (polyMul R (conditionalGram heads W a c)) :=
  (PR.mul (conditionalGram_certificate tail heads W a c hW ha hc P)).haar_nonnegative

#print axioms conditionalGram
#print axioms conditionalWedge
#print axioms conditionalReplica
#print axioms conditionalReplica_identity
#print axioms conditionalReplica_certificate
#print axioms conditionalGram_certificate
#print axioms spectator_nonnegative

end YMGap.Continuum.SU2QuaternionMultiHeadConditionalGram
