/-
# Original signed boundary-pairing cutoff limits at every odd extent

The full bilinear of the existing reflected kernel, evaluated on fixed
finite boundary observables via the existing zero extension, stabilizes
exactly. Both original heat-dressed boundary polynomials are retained.
The common stage is the maximum of their anchor and the explicit interface
degree bound. Its rational value supplies a CReal and exact modulus.

For w >= 0, original reflection positivity gives nonnegativity of the
limiting diagonal. No compatibility between slab extents, physical time,
stationary vacuum, strict gap, or continuum construction is asserted.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding
import YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit

namespace YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding
open YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection
open YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit
open YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Both ORIGINAL boundary polynomials at the fixed anchor. -/
def boundaryMultiplier (w : Q') (anchor half : Nat) (a b : EdgeLabelling → Q') : RatPoly :=
  polyMul (lowerObservable w anchor half a) (upperObservable w anchor half b)

theorem boundaryMultiplier_support (w : Q') (anchor half : Nat) (a b : EdgeLabelling → Q') :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length
      (boundaryMultiplier w anchor half a b) :=
  supported_polyMul (lowerObservable_support w anchor half a) (upperObservable_support w anchor half b)

theorem anchoredIntegrand_haar_eq_interfacePairing (w : Q') (anchor later half : Nat)
    (a b : EdgeLabelling → Q') :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (anchoredIntegrand w anchor later half a b) ≈
      interfacePairing w later half (boundaryMultiplier w anchor half a b) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_middle_comm _ _ _ _)
    (Q'.eqv_symm (quaternionHaar_polyMul_assoc _ _ _ _))

/-- The existing signed reflected kernel, not a replacement limit model. -/
def exactCutoffPairing (w : Q') (anchor later half : Nat) (a b : EdgeLabelling → Q') : Q' :=
  finiteJointBilinear (centralHalfStates later half) (boundaryExtension anchor half a) (boundaryExtension anchor half b)
    (exactCorrectedSlabReflectedKernel w later half)

/-- Both representation-carrier inclusion and interface stabilization are required. -/
def exactCutoffPairingModulus (w : Q') (anchor half : Nat) (a b : EdgeLabelling → Q') : Nat :=
  max anchor (interfaceBound half (boundaryMultiplier w anchor half a b))

def exactCutoffPairingValue (w : Q') (anchor half : Nat) (a b : EdgeLabelling → Q') : Q' :=
  interfacePairing w (interfaceBound half (boundaryMultiplier w anchor half a b)) half
    (boundaryMultiplier w anchor half a b)

/-- Every sufficiently large cutoff agrees EXACTLY on these same finite observables. -/
theorem exactCutoffPairing_stable (w : Q') (anchor later half : Nat) (a b : EdgeLabelling → Q')
    (hlater : exactCutoffPairingModulus w anchor half a b ≤ later) :
    exactCutoffPairing w anchor later half a b ≈ exactCutoffPairingValue w anchor half a b := by
  have ha : anchor ≤ later := Nat.le_trans (Nat.le_max_left _ _) hlater
  have hi : interfaceBound half (boundaryMultiplier w anchor half a b) ≤ later :=
    Nat.le_trans (Nat.le_max_right _ _) hlater
  exact Q'.eqv_trans _ _ _ (exact_bilinear_anchored w ha half a b)
    (Q'.eqv_trans _ _ _ (anchoredIntegrand_haar_eq_interfacePairing w anchor later half a b)
      (interfacePairing_stable w later half _ (boundaryMultiplier_support w anchor half a b) hi))

/-- Computable CReal value; its named modulus carries the cutoff witness. -/
def exactCutoffPairingLimit (w : Q') (anchor half : Nat) (a b : EdgeLabelling → Q') : CReal :=
  CReal.ofQ' (exactCutoffPairingValue w anchor half a b)

theorem exactCutoffPairingLimit_exact (w : Q') (anchor later half : Nat) (a b : EdgeLabelling → Q')
    (hlater : exactCutoffPairingModulus w anchor half a b ≤ later) (precision : Nat) :
    exactCutoffPairing w anchor later half a b ≈ (exactCutoffPairingLimit w anchor half a b).approx precision := by
  unfold exactCutoffPairingLimit
  rw [CReal.ofQ'_approx]
  exact exactCutoffPairing_stable w anchor later half a b hlater

/-- Positivity is transported from the actual original form at the computed stage. -/
theorem exactCutoffPairingValue_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (anchor half : Nat) (c : EdgeLabelling → Q') :
    (0 : Q') ≤ exactCutoffPairingValue w anchor half c c :=
  Q'.le_trans' _ _ _ (exact_quadratic_nonnegative hw (exactCutoffPairingModulus w anchor half c c) half
    (boundaryExtension anchor half c))
    (Q'.le_of_eqv (exactCutoffPairing_stable w anchor _ half c c (Nat.le_refl _)))

end YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit.boundaryMultiplier
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit.boundaryMultiplier_support
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit.anchoredIntegrand_haar_eq_interfacePairing
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit.exactCutoffPairing
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit.exactCutoffPairingModulus
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit.exactCutoffPairingValue
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit.exactCutoffPairing_stable
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit.exactCutoffPairingLimit
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit.exactCutoffPairingLimit_exact
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit.exactCutoffPairingValue_nonnegative
