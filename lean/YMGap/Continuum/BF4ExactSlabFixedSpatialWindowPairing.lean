/-
# Actual multi-time window pairing and unchanged normalization

An arbitrary supported polynomial on L+1 consecutive slices is retained
inside the chronological K/V chain. Integrate its first L slices with the
left message u_m, leaving the final spatial V for ell. The resulting F_m
pairs with u_n; the comparison denominator is ell(u_(m+L)*u_n).
The finite chain identity uses the actual original kernels and weights,
not a new conditional action. Original ambient-lattice window placement
still needs its own geometric pin; no stationary cylinder or OS claim is made.
-/

import YMGap.Continuum.SU2QuaternionHeadWindowContraction
import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add chain_partition_pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (massRatio_congr)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

def observedMessage (w : Q') (K width m L : Nat) (p : RatPoly) : RatPoly :=
  windowMessage (N width) (kineticWeight w K width) (spatialWeight w K width)
    L (terminalMessage w K width m) p

theorem observedMessage_supported (w : Q') (K width m L : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    SupportedQuaternionBlocks (N width) (observedMessage w K width m L p) :=
  windowMessage_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
    L (terminalMessage_supported w K width m) hp

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

/-- Exact original unobserved iterate; no new partition or message division. -/
theorem window_unobserved_pin (w : Q') (K width m L : Nat) :
    RatPolyCoeffEqv (observedMessage w K width m L polyOne) (terminalMessage w K width (m+L)) := by
  have h := windowMessage_one (N width) (kineticWeight w K width) (spatialWeight w K width)
    L (terminalMessage w K width m)
  change RatPolyCoeffEqv (observedMessage w K width m L polyOne)
    (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) L
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) m polyOne)) at h
  rw [← iterateStep_add] at h
  exact h

private theorem iterate_congr (blocks : Nat) (kernel weight : RatPoly) :
    (n : Nat) → {p q : RatPoly} → RatPolyCoeffEqv p q →
      RatPolyCoeffEqv (iterateStep blocks kernel weight n p) (iterateStep blocks kernel weight n q)
  | 0, _, _, h => h
  | n+1, _, _, h => iterate_congr blocks kernel weight n
      (partialHaarHeads_congr blocks ((h.mul_left weight).mul_left kernel))

private theorem terminal_weight (w : Q') (K width : Nat) (p : RatPoly) :
    quaternionHaar (N width) (polyMul p (polyMul (spatialWeight w K width) polyOne)) ≈
      weightedMass w K width p := by
  unfold weightedMass
  exact haar_of_coeff (((RatPolyCoeffEqv.refl p).mul (RatPolyCoeffEqv.mul_one _)).trans
    (RatPolyCoeffEqv.mul_comm _ _))

private theorem terminal_pair_mass (w : Q') (K width n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    weightedMass w K width (polyMul p (terminalMessage w K width n)) ≈
      weightedMass w K width
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n p) :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (iterateStep_weighted_symmetric w K width n hp (supported_one (N width))))
    (weightedMass_congr w K width (RatPolyCoeffEqv.one_mul _))

/-- Whole chronological numerator with P retained over L+1 slices. Both
external boundary messages and the final spatial weight are the original ones. -/
theorem window_pairing (w : Q') (K width m L n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    quaternionHaar ((m+(L+n)+1)*(N width))
      (polyMul (liftBoundary (m*(N width)) p)
        (chain (N width) (kineticWeight w K width) (spatialWeight w K width) (m+(L+n)) polyOne)) ≈
      weightedMass w K width
        (polyMul (observedMessage w K width m L p) (terminalMessage w K width n)) := by
  have hchain := chain_middle_pairing (N width) (kineticWeight w K width)
    (spatialWeight w K width) m (L+n) polyOne p polyOne
  have hstart := haar_of_coeff (blocks := (m+(L+n)+1)*(N width))
    ((RatPolyCoeffEqv.one_mul (liftBoundary (m*(N width)) p)).mul_right
      (chain (N width) (kineticWeight w K width) (spatialWeight w K width) (m+(L+n)) polyOne))
  have htime : RatPolyCoeffEqv
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) (L+n)
        (polyMul (terminalMessage w K width m) p))
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
        (observedMessage w K width m L p)) := by
    rw [iterateStep_add]
    exact iterate_congr (N width) (kineticWeight w K width) (spatialWeight w K width) n
      (windowMessage_iterate (N width) (kineticWeight w K width) (spatialWeight w K width)
        L (terminalMessage w K width m) p).symm
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hstart)
    (Q'.eqv_trans _ _ _ hchain
      (Q'.eqv_trans _ _ _ (haar_of_coeff (htime.mul_right (polyMul (spatialWeight w K width) polyOne)))
        (Q'.eqv_trans _ _ _ (terminal_weight w K width _)
          (Q'.eqv_symm (terminal_pair_mass w K width n (observedMessage_supported w K width m L hp))))))

/-- The denominator retains all m+L+n transition factors of that SAME chain. -/
theorem window_partition_pairing (w : Q') (K width m L n : Nat) :
    quaternionHaar ((m+(L+n)+1)*(N width))
      (chain (N width) (kineticWeight w K width) (spatialWeight w K width) (m+(L+n)) polyOne) ≈
      weightedMass w K width
        (polyMul (terminalMessage w K width (m+L)) (terminalMessage w K width n)) := by
  simpa only [Nat.add_assoc] using chain_partition_pairing w K width (m+L) n

/-- Actual normalized window ratio with a constructed positive original partition. -/
def windowRatio {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) (p : RatPoly) : Q' :=
  massRatio w K width
    (polyMul (observedMessage w K width m L p) (terminalMessage w K width n))
    (polyMul (terminalMessage w K width (m+L)) (terminalMessage w K width n))
    (terminalPair_positive hw0 hw1 K width hK (m+L) n)

/-- Exact pin to the iterated relative-bracket ratio. Its positive comparison
mass follows from the actual terminal-message certificate, not a new premise. -/
theorem windowRatio_iterate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    windowRatio hw0 hw1 K width hK m L n p ≈
      massRatio w K width
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
          (observedMessage w K width m L p))
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
          (terminalMessage w K width (m+L)))
        (iterateWeightedMass_positive hw0 hw1 K width hK n
          (terminalMessage_supported w K width (m+L))
          (terminalMessage_certificate hw0 hw1 K width hK (m+L))
          (terminalMessage_mass_positive hw0 hw1 K width hK (m+L))) :=
  massRatio_congr w K width (terminalPair_positive hw0 hw1 K width hK (m+L) n)
    (iterateWeightedMass_positive hw0 hw1 K width hK n
      (terminalMessage_supported w K width (m+L))
      (terminalMessage_certificate hw0 hw1 K width hK (m+L))
      (terminalMessage_mass_positive hw0 hw1 K width hK (m+L)))
    (terminal_pair_mass w K width n (observedMessage_supported w K width m L hp))
    (terminal_pair_mass w K width n (terminalMessage_supported w K width (m+L)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing.observedMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing.observedMessage_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing.window_unobserved_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing.window_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing.window_partition_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing.windowRatio
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing.windowRatio_iterate
