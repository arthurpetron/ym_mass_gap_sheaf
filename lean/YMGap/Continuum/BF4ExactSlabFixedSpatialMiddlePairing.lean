/-
# Actual finite middle-slice pairing and its positive normalization

The original chronological chain with a probe at slice m contracts to
ell((T^m 1)*p*(T^n 1)). Weighted symmetry moves the last n steps to the
right message; the spatial weight at the insertion occurs exactly once,
inside ell. The chain without an insertion has the SAME product denominator.

These are actual finite K/V polynomial identities, including zero lengths.
Original ambient-lattice geometric placement is a separate remaining pin.
No two-sided limit, stationary law, physical OS or mass-gap claim is made.
-/

import YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- Exact composition in the existing tail-recursive step convention. -/
theorem iterateStep_add (blocks : Nat) (kernel weight : RatPoly) (m n : Nat) (f : RatPoly) :
    iterateStep blocks kernel weight (m+n) f =
      iterateStep blocks kernel weight n (iterateStep blocks kernel weight m f) := by
  induction m generalizing f with
  | zero => simp only [Nat.zero_add, iterateStep]
  | succ m ih =>
      simp only [Nat.succ_add, iterateStep]
      exact ih (step blocks kernel weight f)

private theorem terminal_weight (w : Q') (K width : Nat) (p : RatPoly) :
    quaternionHaar (N width) (polyMul p (polyMul (spatialWeight w K width) polyOne)) ≈
      weightedMass w K width p :=
  haar_of_coeff (((RatPolyCoeffEqv.refl p).mul (RatPolyCoeffEqv.mul_one _)).trans
    (RatPolyCoeffEqv.mul_comm _ _))

/-- The actual two-message denominator is the mass of the full finite chain. -/
theorem terminalPair_total (w : Q') (K width m n : Nat) :
    weightedMass w K width (polyMul (terminalMessage w K width m) (terminalMessage w K width n)) ≈
      weightedMass w K width (terminalMessage w K width (m+n)) := by
  have hs := iterateStep_weighted_symmetric w K width n
    (terminalMessage_supported w K width m) (supported_one (N width))
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm hs)
    (weightedMass_congr w K width (RatPolyCoeffEqv.one_mul _))
  change weightedMass w K width
      (polyMul (terminalMessage w K width m) (terminalMessage w K width n)) ≈
    weightedMass w K width
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) m polyOne)) at he
  rw [← iterateStep_add] at he
  exact he

/-- A supported middle probe is retained between the two actual messages.
The chronological action still has m+n+1 spatial factors. -/
theorem middle_pairing (w : Q') (K width m n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    quaternionHaar ((m+n+1)*(N width))
        (polyMul (liftBoundary (m*(N width)) p)
          (chain (N width) (kineticWeight w K width) (spatialWeight w K width) (m+n) polyOne)) ≈
      weightedMass w K width
        (polyMul (polyMul (terminalMessage w K width m) p) (terminalMessage w K width n)) := by
  have hchain := chain_middle_pairing (N width) (kineticWeight w K width)
    (spatialWeight w K width) m n polyOne p polyOne
  have hstart := haar_of_coeff (blocks := (m+n+1)*(N width))
    ((RatPolyCoeffEqv.one_mul (liftBoundary (m*(N width)) p)).mul_right
      (chain (N width) (kineticWeight w K width) (spatialWeight w K width) (m+n) polyOne))
  have hs := iterateStep_weighted_symmetric w K width n
    (supported_polyMul (terminalMessage_supported w K width m) hp) (supported_one (N width))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hstart)
    (Q'.eqv_trans _ _ _ hchain
      (Q'.eqv_trans _ _ _ (terminal_weight w K width _)
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm (weightedMass_congr w K width (RatPolyCoeffEqv.one_mul _))) hs)))

/-- No insertion: this is the same chronological partition, not a replacement
normalization. All temporal and spatial factors are retained. -/
theorem chain_partition_pairing (w : Q') (K width m n : Nat) :
    quaternionHaar ((m+n+1)*(N width))
        (chain (N width) (kineticWeight w K width) (spatialWeight w K width) (m+n) polyOne) ≈
      weightedMass w K width
        (polyMul (terminalMessage w K width m) (terminalMessage w K width n)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul _)))
    (Q'.eqv_trans _ _ _
      (chain_pairing (N width) (kineticWeight w K width) (spatialWeight w K width)
        (m+n) polyOne polyOne)
      (Q'.eqv_trans _ _ _ (terminal_weight w K width _)
        (Q'.eqv_symm (terminalPair_total w K width m n))))

/-- Strict positivity of the actual finite chronological partition follows
from the already constructed terminal-message floor. -/
theorem chain_partition_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) :
    (0 : Q') < quaternionHaar ((m+n+1)*(N width))
      (chain (N width) (kineticWeight w K width) (spatialWeight w K width) (m+n) polyOne) :=
  HeatKernelRGStep.lt_of_lt_of_le (terminalPair_positive hw0 hw1 K width hK m n)
    (Q'.ge_of_eqv (chain_partition_pairing w K width m n))

/-- The actual interior ratio, distinguished from the evolved endpoint-probe
ratio. This definition supplies its positive denominator, not a vacuum. -/
def middleRatio {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) (p : RatPoly) : Q' :=
  massRatio w K width
    (polyMul (polyMul (terminalMessage w K width m) p) (terminalMessage w K width n))
    (polyMul (terminalMessage w K width m) (terminalMessage w K width n))
    (terminalPair_positive hw0 hw1 K width hK m n)

end YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing.iterateStep_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing.terminalPair_total
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing.middle_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing.chain_partition_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing.chain_partition_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing.middleRatio
