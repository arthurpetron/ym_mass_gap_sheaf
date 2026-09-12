/-
# The full original bilinear has explicit mixed Gram channels

At every odd extent, the ORIGINAL signed two-observable pairing equals a
finite weighted sum of products of the observables' own lower-channel Haar
values. Both observables and all spatial interactions remain in the formula.
Commuting those rational values proves symmetry of this original bilinear.

This is stronger than its diagonal positivity statement; it supplies the
missing symmetry law for a common cutoff-limit GNS form. It is not a
transfer construction, strict gap, or compatibility between slab extents.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
import YMGap.Continuum.BF4ExactSlabLocalBilinearChannels

namespace YMGap.Continuum.BF4ExactSlabAllExtentBilinearGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
open YMGap.Continuum.BF4ExactSlabLocalBilinearChannels
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Mixed channel values for the very same original observables and heat law. -/
def originalBilinearChannelValue {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (left right : EdgeLabelling → Q') : Q' :=
  channelBilinearValue (boundaryCompleteSlabLinks (centralExtent half)).length
    (lowerObservable w K half right) (lowerObservable w K half left) (interfaceExpansion hw K half).tree

theorem exact_bilinear_eq_channelProducts {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K half) left right (exactCorrectedSlabReflectedKernel w K half) ≈
      originalBilinearChannelValue hw K half left right := by
  refine Q'.eqv_trans _ _ _ (exact_bilinear_eq_reflectedHaar hw K half left right) ?_
  let a := lowerObservable w K half left
  let h := interfacePolynomial w K half
  let t := reflectCorrectedSlabPolynomial (centralExtent half) (lowerObservable w K half right)
  have hr := ((RatPolyCoeffEqv.mul_comm h t).mul_left a).trans
    ((RatPolyCoeffEqv.mul_assoc a t h).symm.trans ((RatPolyCoeffEqv.mul_comm a t).mul_right h))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ hr)
    (expansion_mixed_pairing (interfaceExpansion hw K half)
      (lowerObservable w K half right) (lowerObservable w K half left)
      (lowerObservable_support w K half right) (lowerObservable_support w K half left)
      (lowerObservable_local w K half right) (lowerObservable_local w K half left))

/-- Symmetry is proved from the full mixed pairing, not inferred from positivity. -/
theorem exact_bilinear_symmetric {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K half) left right (exactCorrectedSlabReflectedKernel w K half) ≈
      finiteJointBilinear (centralHalfStates K half) right left (exactCorrectedSlabReflectedKernel w K half) :=
  Q'.eqv_trans _ _ _ (exact_bilinear_eq_channelProducts hw K half left right)
    (Q'.eqv_trans _ _ _ (channelBilinearValue_symm _ _ _ _)
      (Q'.eqv_symm (exact_bilinear_eq_channelProducts hw K half right left)))

end YMGap.Continuum.BF4ExactSlabAllExtentBilinearGram

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBilinearGram.originalBilinearChannelValue
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBilinearGram.exact_bilinear_eq_channelProducts
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBilinearGram.exact_bilinear_symmetric
