/-
# Haar-carrier congruence under the existing conditional projections

The original one-block and finite-family conditional integrations respect
both unrestricted Haar-carrier equality and its supported-insertion variant.
This is congruence of equalities, not a claim that a polynomial equals its
conditional projection.
-/

import YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingSupportedEquality

namespace YMGap.Continuum.SU2QuaternionHaarCarrierProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- One in-range conditional integration preserves unrestricted Haar-carrier
equality, by self-adjointness and testing the source equality against the
projected insertion. -/
theorem project_preserves_haarCarrierEqv (blocks selected : Nat)
    (hselected : selected < blocks) {p q : RatPoly}
    (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (project selected p) (project selected q) := by
  intro r
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (project_selfAdjoint blocks selected hselected r p))
    (Q'.eqv_trans _ _ _ (h (project selected r))
      (project_selfAdjoint blocks selected hselected r q))

/-- The same congruence for supported insertions. The projection preserves
support, so the tested insertion remains within the original finite carrier. -/
theorem project_preserves_supportedHaarEqv (blocks selected : Nat)
    (hselected : selected < blocks) {p q : RatPoly}
    (h : SupportedHaarEqv blocks p q) :
    SupportedHaarEqv blocks (project selected p) (project selected q) := by
  intro r hr
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (project_selfAdjoint blocks selected hselected r p))
    (Q'.eqv_trans _ _ _ (h (project selected r) (project_supported selected hr))
      (project_selfAdjoint blocks selected hselected r q))

/-- A finite in-range schedule preserves unrestricted Haar-carrier equality. -/
theorem familyProject_preserves_haarCarrierEqv (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) {p q : RatPoly}
    (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (familyProject ids p) (familyProject ids q) := by
  intro r
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (familyProject_selfAdjoint blocks ids hids r p))
    (Q'.eqv_trans _ _ _ (h (familyProject ids r))
      (familyProject_selfAdjoint blocks ids hids r q))

/-- A finite in-range schedule preserves equality tested on supported
insertions; repeated schedule indices are allowed. -/
theorem familyProject_preserves_supportedHaarEqv (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) {p q : RatPoly}
    (h : SupportedHaarEqv blocks p q) :
    SupportedHaarEqv blocks (familyProject ids p) (familyProject ids q) := by
  intro r hr
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (familyProject_selfAdjoint blocks ids hids r p))
    (Q'.eqv_trans _ _ _ (h (familyProject ids r) (familyProject_supported ids hr))
      (familyProject_selfAdjoint blocks ids hids r q))

#print axioms project_preserves_haarCarrierEqv
#print axioms project_preserves_supportedHaarEqv
#print axioms familyProject_preserves_haarCarrierEqv
#print axioms familyProject_preserves_supportedHaarEqv

end YMGap.Continuum.SU2QuaternionHaarCarrierProjection
