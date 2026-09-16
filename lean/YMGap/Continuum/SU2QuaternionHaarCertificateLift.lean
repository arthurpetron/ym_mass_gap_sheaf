/-
# Lifting certificates past an explicit quaternion-Haar head

The actual liftBoundary operation shifts every polynomial coordinate by the
specified number of quaternion blocks. Ordered-head Fubini shows that it
preserves arbitrary-insertion Haar carrier equality on the enlarged carrier:
the insertion is partially integrated, not discarded or assumed independent.
In particular, this transport does not require support hypotheses on either
side of the equality or on the insertion.

Recursion on an existing square certificate then shifts its supported square
generators, rational weights, sums and Haar transports. Zero shift and zero
source blocks are included. This is the positivity-preserving placement
needed by full-window relative brackets, not a general block-embedding
extension, physical OS identification, stationary law or spectral claim.
-/

import YMGap.Continuum.SU2QuaternionHeadChainComposition

namespace YMGap.Continuum.SU2QuaternionHaarCertificateLift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.QuaternionHaarSquareCertificate

/-- Shifting all coordinates preserves equality under every insertion on the
enlarged Haar carrier. The inserted polynomial may have arbitrary support. -/
theorem lift_carrier (shift : Nat) {blocks : Nat} {p q : RatPoly}
    (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv (blocks + shift) (liftBoundary shift p) (liftBoundary shift q) := by
  intro insertion
  exact Q'.eqv_trans _ _ _ (head_pairing blocks shift insertion p)
    (Q'.eqv_trans _ _ _ (h (partialHaarHeads shift insertion))
      (Q'.eqv_symm (head_pairing blocks shift insertion q)))

/-- Computed certificate transport for the literal coordinate shift.
Support is required only at square generators, where the existing proof is
shifted explicitly; no support premise is added to transport nodes. -/
def lift_certificate (shift : Nat) {blocks : Nat} :
    {p : RatPoly} → Certificate blocks p →
      Certificate (blocks + shift) (liftBoundary shift p)
  | _, .square p hp => by
      rw [lift_product]
      exact .square (liftBoundary shift p) (lift_supported hp shift)
  | _, .add P Q => by
      rw [lift_add]
      exact .add (lift_certificate shift P) (lift_certificate shift Q)
  | _, .smul c hc P => by
      rw [lift_smul]
      exact .smul c hc (lift_certificate shift P)
  | _, .transport h P =>
      .transport (lift_carrier shift h) (lift_certificate shift P)

end YMGap.Continuum.SU2QuaternionHaarCertificateLift

#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateLift.lift_carrier
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateLift.lift_certificate
