/-
# Weighted conditional variance with shared spectators

For the ACTUAL head Haar average A and any supported weight W and input f,
integrating W(x,z) W(y,z) (f(x,z)-f(y,z))^2 over x,y gives twice
  A(W) A(W f^2) - A(W f)^2.
The spectators z are shared, not independently averaged. Equality holds
under every remaining polynomial insertion. An existing positive certificate
for W constructs a positive certificate for this determinant.

There is no division by a worst-case normalizer floor, replacement of W,
small-perturbation premise, or assertion of a strict lower bound. This is
the finite numerator of weighted conditional variance, not a mixing rate,
physical-time gap, or continuum result.
-/

import YMGap.Continuum.SU2QuaternionSharedHeadGramPairing
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

namespace YMGap.Continuum.SU2QuaternionConditionalVarianceReplica

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
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier

local infix:50 " ≈ " => Q'.eqv
local notation "A" => partialHaarHead

/-- The normalizer is retained as a polynomial, not replaced by a scalar. -/
def determinant (W f : RatPoly) : RatPoly :=
  polyAdd (polyMul (A W) (A (polyMul W (polyMul f f))))
    (polyNeg (polyMul (A (polyMul W f)) (A (polyMul W f))))

def replicaDifference (f : RatPoly) : RatPoly :=
  polyAdd (copy f) (polyNeg (liftHead f))

/-- Only the selected link is copied; all other variables remain shared. -/
def replicaEnergy (W f : RatPoly) : RatPoly :=
  polyMul (polyMul (copy W) (liftHead W))
    (polyMul (replicaDifference f) (replicaDifference f))

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

/-- The two replicas are independent only in their selected head variables. -/
theorem replica_product (p q : RatPoly) :
    RatPolyCoeffEqv (A (A (polyMul (copy p) (liftHead q))))
      (polyMul (A p) (A q)) := by
  have h := partialHaarHead_congr (partialHaarHead_mul_lift (copy p) q)
  rw [partial_copy] at h
  exact h.trans ((partialHaarHead_congr (RatPolyCoeffEqv.mul_comm _ _)).trans
    ((partialHaarHead_mul_lift q (A p)).trans (RatPolyCoeffEqv.mul_comm _ _)))

private def expansion (W f : RatPoly) : RatPoly :=
  let diagonal := polyMul W (polyMul f f)
  let cross := polyMul (copy (polyMul W f)) (liftHead (polyMul W f))
  polyAdd
    (polyAdd (polyMul (copy diagonal) (liftHead W))
      (polyMul (copy W) (liftHead diagonal)))
    (polyAdd (polyNeg cross) (polyNeg cross))

private theorem energy_expansion (tail : Nat) (W f : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    HaarCarrierEqv (tail+2) (replicaEnergy W f) (expansion W f) := by
  have hdiag : HaarCarrierEqv (tail+2) (copy (polyMul W (polyMul f f)))
      (polyMul (copy W) (polyMul (copy f) (copy f))) :=
    (copy_mul_carrier (by omega) hW (supported_polyMul hf hf)).trans
      (HaarCarrierEqv.mul (.refl _ _) (copy_mul_carrier (by omega) hf hf))
  have hcross := copy_mul_carrier (by omega : 0 < tail+1) hW hf
  have hexp : HaarCarrierEqv (tail+2) (expansion W f)
      (polyAdd
        (polyAdd
          (polyMul (polyMul (copy W) (polyMul (copy f) (copy f))) (liftHead W))
          (polyMul (copy W) (polyMul (liftHead W) (polyMul (liftHead f) (liftHead f)))))
        (polyAdd
          (polyNeg (polyMul (polyMul (copy W) (copy f)) (polyMul (liftHead W) (liftHead f))))
          (polyNeg (polyMul (polyMul (copy W) (copy f)) (polyMul (liftHead W) (liftHead f)))))) := by
    dsimp only [expansion]
    rw [liftHead_mul, liftHead_mul, liftHead_mul]
    exact HaarCarrierEqv.add
      (HaarCarrierEqv.add (HaarCarrierEqv.mul hdiag (.refl _ _)) (.refl _ _))
      (HaarCarrierEqv.add (HaarCarrierEqv.neg (HaarCarrierEqv.mul hcross (.refl _ _)))
        (HaarCarrierEqv.neg (HaarCarrierEqv.mul hcross (.refl _ _))))
  refine (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1))
      (.mul (.add (.var 2) (.neg (.var 3))) (.add (.var 2) (.neg (.var 3)))))
    (.add
      (.add (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1))
        (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3)))))
      (.add (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
        (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))))
    (by decide) (fun | 0 => copy W | 1 => liftHead W | 2 => copy f | _ => liftHead f))).trans hexp.symm

/-- Exact polynomial-valued two-copy identity under EVERY spectator insertion. -/
theorem replica_identity (tail : Nat) (W f : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    HaarCarrierEqv tail (A (A (replicaEnergy W f)))
      (polyAdd (determinant W f) (determinant W f)) := by
  have h := partialHaarHead_carrier (partialHaarHead_carrier (energy_expansion tail W f hW hf))
  refine h.trans (RatPolyCoeffEqv.haarCarrier ?_)
  dsimp only [expansion]
  simp only [partialHaarHead_add]
  have hc := (twice_neg _).trans (RatPolyCoeffEqv.neg (replica_product (polyMul W f) (polyMul W f)))
  refine (RatPolyCoeffEqv.add
    (RatPolyCoeffEqv.add (replica_product (polyMul W (polyMul f f)) W)
      (replica_product W (polyMul W (polyMul f f))))
    (RatPolyCoeffEqv.add hc hc)).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1)))
      (.add (.neg (.mul (.var 2) (.var 2))) (.neg (.mul (.var 2) (.var 2)))))
    (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2)))))
    (by decide) (fun | 0 => A W | 1 => A (polyMul W (polyMul f f)) | _ => A (polyMul W f))

private def copy_certificate (tail : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W) (P : Certificate (tail+1) W) :
    Certificate (tail+2) (copy W) :=
  let s := spareSwap (tail+1) (by omega)
  .transport
    (carrierOfPrefix (reindex_supported s (liftHead W)) (copy_supported (by omega) hW)
      (copy_reindex_prefix (tail+1) (by omega) W)).symm
    (reindex_certificate s (lift_supported hW 1) (lift_certificate 1 P))

private theorem supported_neg {blocks : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) : SupportedQuaternionBlocks blocks (polyNeg f) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hf s hs

/-- An explicit positive certificate for the actual weighted replica square. -/
def replica_certificate (tail : Nat) (W f : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hf : SupportedQuaternionBlocks (tail+1) f) (P : Certificate (tail+1) W) :
    Certificate (tail+2) (replicaEnergy W f) :=
  Certificate.mul (Certificate.mul (copy_certificate tail W hW P) (lift_certificate 1 P))
    (.square (replicaDifference f)
      (supported_add (copy_supported (by omega) hf) (supported_neg (lift_supported hf 1))))

private theorem half_double (p : RatPoly) :
    RatPolyCoeffEqv (polySmul HalfPow.half (polyAdd p p)) p := by
  intro weight
  exact Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ratWeightedSum_add weight p p))
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) (ExpNeg.two_halves _)))

/-- Weighted conditional Cauchy--Schwarz as a constructed polynomial cone
witness, retaining arbitrary surrounding action factors. -/
def determinant_certificate (tail : Nat) (W f : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hf : SupportedQuaternionBlocks (tail+1) f) (P : Certificate (tail+1) W) :
    Certificate tail (determinant W f) :=
  .ofCoeff (half_double _).symm
    (.smul HalfPow.half (by decide)
      (.transport (replica_identity tail W f hW hf).symm
        (partialHaarHead_certificate tail
          (partialHaarHead_certificate (tail+1) (replica_certificate tail W f hW hf P)))))

/-- Any positive spectator certificate may be inserted WITHOUT a new
independence premise or replacement of the retained law. -/
theorem spectator_nonnegative (tail : Nat) (W f B : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+1) W)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (P : Certificate (tail+1) W) (PB : Certificate tail B) :
    (0 : Q') ≤ quaternionHaar tail (polyMul B (determinant W f)) :=
  (Certificate.mul PB (determinant_certificate tail W f hW hf P)).haar_nonnegative

#print axioms replica_product
#print axioms replica_identity
#print axioms replica_certificate
#print axioms determinant_certificate
#print axioms spectator_nonnegative

end YMGap.Continuum.SU2QuaternionConditionalVarianceReplica
