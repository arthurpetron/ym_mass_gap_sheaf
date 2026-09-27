/-
# Certificates under finite original-coordinate Haar integration

Iterating the checked one-coordinate positive integration preserves a
certificate or two-sided interval on the same quaternion Haar carrier.
Repeated coordinate indices are permitted. No weighted spectral estimate is
asserted here.
-/

import YMGap.Continuum.SU2QuaternionHaarFamilyProjection
import YMGap.Continuum.SU2QuaternionHaarBlockCertificate

namespace YMGap.Continuum.SU2QuaternionHaarFamilyCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockCertificate
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

/-- Positive certificates survive the existing finite family projection,
with every unselected spectator coordinate retained. -/
def familyProject_certificate (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (P : Certificate blocks p) :
    Certificate blocks (familyProject ids p) :=
  match ids with
  | [] => P
  | i :: tail =>
      familyProject_certificate blocks tail
        (fun j hj => hids j (List.mem_cons_of_mem i hj))
        (project_supported i hp)
        (project_certificate blocks i (hids i List.mem_cons_self) hp P)

/-- The same rational two-sided interval survives each in-range conditional
Haar integration in the existing list order. -/
def familyProject_interval (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) {p : RatPoly} {c : Q'}
    (P : Interval blocks p c) : Interval blocks (familyProject ids p) c :=
  match ids with
  | [] => P
  | i :: tail =>
      familyProject_interval blocks tail
        (fun j hj => hids j (List.mem_cons_of_mem i hj))
        (project_interval blocks i (hids i List.mem_cons_self) P)

/-- The existing finite-family projection is self-adjoint for the original
Haar pairing, even when both inputs depend on all selected coordinates. -/
theorem familyProject_selfAdjoint (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) (f g : RatPoly) :
    Q'.eqv
      (quaternionHaar blocks (polyMul (familyProject ids f) g))
      (quaternionHaar blocks (polyMul f (familyProject ids g))) := by
  have hleft := quaternionHaar_polyMul_eq_after_integratingBlocks blocks ids
    (familyProject ids f) g hids (familyProject_independent ids f)
  have hright : Q'.eqv
      (quaternionHaar blocks (polyMul f (familyProject ids g)))
      (quaternionHaar blocks (polyMul (familyProject ids f) (familyProject ids g))) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_eq_after_integratingBlocks blocks ids
          (familyProject ids g) f hids (familyProject_independent ids g))
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

#print axioms familyProject_certificate
#print axioms familyProject_interval
#print axioms familyProject_selfAdjoint

end YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
