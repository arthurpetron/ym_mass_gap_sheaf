/-
# Positive certificates survive actual partial quaternion-Haar integration

The concrete polynomial-valued square certificate supplies the square
constructor. Addition, nonnegative rational scaling and arbitrary-insertion
Haar transport are then preserved by exact Fubini and polynomial algebra.
Iteration integrates any declared number of ordered head coordinates.

The transport proof retains an arbitrary polynomial in all surviving
variables by lifting it before integration. No pointwise positivity rule,
independent-spectator assumption, stationary law, Markov normalization, or
OS identification is used.
-/

import YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate
import YMGap.Continuum.SU2QuaternionHeadChainComposition

namespace YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Integration distributes literally over the polynomial list sum. -/
theorem partialHaarHead_add (p q : RatPoly) :
    partialHaarHead (polyAdd p q) = polyAdd (partialHaarHead p) (partialHaarHead q) :=
  List.map_append

/-- Rational scaling commutes with integration coefficientwise. -/
theorem partialHaarHead_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polySmul c p)) (polySmul c (partialHaarHead p)) := by
  have ht : RatPolyTermwiseEqv (partialHaarHead (polySmul c p))
      (polySmul c (partialHaarHead p)) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih => exact ⟨rfl, Q'.mul_assoc_eqv _ _ _, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem insertion_pairing (tailBlocks headBlocks : Nat) (p r : RatPoly) :
    quaternionHaar tailBlocks (polyMul r (partialHaarHeads headBlocks p)) ≈
      quaternionHaar (tailBlocks+headBlocks) (polyMul (liftBoundary headBlocks r) p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (head_pairing tailBlocks headBlocks p r))
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))

/-- Every surviving insertion is retained. This is stronger than equality
of the bare total integrals and needs no support premise. -/
theorem partialHaarHeads_carrier {tailBlocks headBlocks : Nat} {p q : RatPoly}
    (h : HaarCarrierEqv (tailBlocks+headBlocks) p q) :
    HaarCarrierEqv tailBlocks (partialHaarHeads headBlocks p) (partialHaarHeads headBlocks q) := by
  intro r
  exact Q'.eqv_trans _ _ _ (insertion_pairing tailBlocks headBlocks p r)
    (Q'.eqv_trans _ _ _ (h (liftBoundary headBlocks r))
      (Q'.eqv_symm (insertion_pairing tailBlocks headBlocks q r)))

theorem partialHaarHead_carrier {tailBlocks : Nat} {p q : RatPoly}
    (h : HaarCarrierEqv (tailBlocks+1) p q) :
    HaarCarrierEqv tailBlocks (partialHaarHead p) (partialHaarHead q) :=
  partialHaarHeads_carrier (headBlocks := 1) h

/-- Integrate the actual certificate recursively. The only square case is
the concrete head-Haar square producer, not an additional analytic premise. -/
def partialHaarHead_certificate (tailBlocks : Nat) :
    {p : RatPoly} → Certificate (tailBlocks+1) p → Certificate tailBlocks (partialHaarHead p)
  | _, .square p hp => partialHaarHead_square_certificate tailBlocks p hp
  | _, .add P Q => by
      rw [partialHaarHead_add]
      exact .add (partialHaarHead_certificate tailBlocks P) (partialHaarHead_certificate tailBlocks Q)
  | _, .smul c hc P =>
      .ofCoeff (partialHaarHead_smul c _)
        (.smul c hc (partialHaarHead_certificate tailBlocks P))
  | _, .transport h P =>
      .transport (partialHaarHead_carrier h) (partialHaarHead_certificate tailBlocks P)

/-- Repeated ordered-head integration preserves the witness-bearing positive
cone on exactly the surviving carrier, including zero integrated blocks. -/
def partialHaarHeads_certificate (tailBlocks : Nat) :
    (headBlocks : Nat) → {p : RatPoly} → Certificate (tailBlocks+headBlocks) p →
      Certificate tailBlocks (partialHaarHeads headBlocks p)
  | 0, _, P => P
  | headBlocks+1, _, P =>
      partialHaarHeads_certificate tailBlocks headBlocks
        (partialHaarHead_certificate (tailBlocks+headBlocks) P)

end YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateIntegration.partialHaarHead_add
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateIntegration.partialHaarHead_smul
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateIntegration.partialHaarHeads_carrier
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateIntegration.partialHaarHead_carrier
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateIntegration.partialHaarHead_certificate
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateIntegration.partialHaarHeads_certificate
