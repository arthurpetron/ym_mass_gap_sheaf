/-
# Reflection positivity of the ORIGINAL signed law at every odd slab extent

The complete original bilinear has its proved spatial-Gram Haar form. Its
upper observable is now the literal reflection of its lower observable, and
the latter is proved lower-local. The existing finite interface expansion
therefore gives an explicit weighted sum of rational squares for the SAME
original quadratic, every finite cutoff and odd extent, whenever w >= 0.

This is finite-slab reflection positivity. No compatibility between slabs,
larger-slab cutoff limit, physical time operator, vacuum stationarity, strict
spectral estimate, continuum limit or Clay closure is claimed.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection

namespace YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabLowerChannelLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Every factor of the actual lower observable uses only lower links;
the original signed coefficient functions have no link-coordinate dependence. -/
theorem lowerObservable_local (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    LowerLocal half (lowerObservable w K half c) := by
  apply BlockLocal.finiteSum
  intro state _
  apply BlockLocal.smul
  apply BlockLocal.fold
  intro id hi
  apply BlockLocal.smul
  exact lower_plaquette_character_local (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1)
    (mem_centralLowerFaceIds.mp hi).2 (state id)

/-- Full original bilinear, now with the literal reflected upper observable.
All support proofs are present before removing the common polynomial padding. -/
theorem exact_bilinear_eq_reflectedHaar {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K half) left right (exactCorrectedSlabReflectedKernel w K half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
        (polyMul (lowerObservable w K half left)
          (polyMul (interfacePolynomial w K half)
            (reflectCorrectedSlabPolynomial (centralExtent half) (lowerObservable w K half right)))) := by
  have hl := lowerObservable_support w K half left
  have hh := (interfaceExpansion hw K half).polynomialSupported
  have hu := upperObservable_support w K half right
  have ht := reflectCorrectedSlabPolynomial_support (centralExtent half) (lowerObservable w K half right)
  have h := (PaddedPolynomialCoeffEqv.refl _ (lowerObservable w K half left)).mul
    ((PaddedPolynomialCoeffEqv.refl _ (interfacePolynomial w K half)).mul (lowerObservable_reflection w K half right))
  exact Q'.eqv_trans _ _ _ (exact_bilinear_eq_spatialGramHaar w K half left right)
    (Q'.eqv_symm (h.haar (supported_polyMul hl (supported_polyMul hh ht))
      (supported_polyMul hl (supported_polyMul hh hu))))

/-- Executable original-observable square channels, not a supplied
positivity hypothesis or a replacement positive law. -/
def originalQuadraticExpansion {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) (c : EdgeLabelling → Q') :
    LocalSquareExpansion half (reflectedInterfacePolynomial w K half (lowerObservable w K half c)) :=
  reflectedInterfaceExpansion hw K half (lowerObservable w K half c)
    (lowerObservable_support w K half c) (lowerObservable_local w K half c)

theorem exact_quadratic_eq_reflectedInterfaceHaar {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (c : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K half) c c (exactCorrectedSlabReflectedKernel w K half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
        (reflectedInterfacePolynomial w K half (lowerObservable w K half c)) := by
  refine Q'.eqv_trans _ _ _ (exact_bilinear_eq_reflectedHaar hw K half c c) ?_
  apply haar_of_coeff_eqv
  exact ((RatPolyCoeffEqv.mul_comm _ _).mul_left _).trans
    ((RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans ((RatPolyCoeffEqv.mul_comm _ _).mul_right _))

/-- The witnessing rational value is the finite sum of the actual channel
Haar integrals squared, with their original nonnegative weights. -/
def exactQuadraticSquareValue {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) (c : EdgeLabelling → Q') : Q' :=
  (originalQuadraticExpansion hw K half c).squareValue

theorem exact_quadratic_eq_squareValue {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (c : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K half) c c (exactCorrectedSlabReflectedKernel w K half) ≈
      exactQuadraticSquareValue hw K half c :=
  Q'.eqv_trans _ _ _ (exact_quadratic_eq_reflectedInterfaceHaar hw K half c)
    (originalQuadraticExpansion hw K half c).haar_eq_squareValue

/-- Reflection positivity of the SAME original signed SU(2) slab law:
every odd extent, every finite character cutoff and arbitrary signed boundary
coefficients. This is nonnegativity, not a strict spectral or mass-gap bound. -/
theorem exact_quadratic_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (c : EdgeLabelling → Q') :
    (0 : Q') ≤ finiteJointBilinear (centralHalfStates K half) c c (exactCorrectedSlabReflectedKernel w K half) :=
  Q'.le_trans' _ _ _ (originalQuadraticExpansion hw K half c).haar_nonnegative
    (Q'.le_of_eqv (Q'.eqv_symm (exact_quadratic_eq_reflectedInterfaceHaar hw K half c)))

end YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity.lowerObservable_local
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity.exact_bilinear_eq_reflectedHaar
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity.originalQuadraticExpansion
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity.exact_quadratic_eq_reflectedInterfaceHaar
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity.exactQuadraticSquareValue
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity.exact_quadratic_eq_squareValue
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity.exact_quadratic_nonnegative
