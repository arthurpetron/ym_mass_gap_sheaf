/-
# Positive original finite-window energy, with its SAME marginal and partition

Take the actual boundary message u_n=T^n 1. The edge density from
DirichletForm is the original central one-step window with n steps on
each side. Its normalization is m(u_(n+1)*u_n), exactly the original
compact partition with 2*n+1 transitions, and is strictly positive.

Twice the normalized energy is the existing windowRatio of the squared
adjacent-slice difference. Its diagonal moments are the existing
middleRatio with depths n+1 and n. No new probability law, stationary
vector or desired coercivity is assumed. A positive uniform fraction
of this SAME marginal variance is still OPEN. The old even-chain
centralVariance has a different density and is not used here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindowPairing
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit (compactPartition)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

/-- The actual successor, respecting the existing tail-recursive convention. -/
theorem terminalMessage_next (w : Q') (K width n : Nat) :
    transferStep w K width (terminalMessage w K width n) =
      terminalMessage w K width (n+1) := by
  symm
  exact iterateStep_add (N width) (kineticWeight w K width)
    (spatialWeight w K width) n 1 polyOne

/-- The denominator already used by windowRatio n 1 n. -/
def oddMass (w : Q') (K width n : Nat) : Q' :=
  weightedMass w K width
    (polyMul (terminalMessage w K width (n+1)) (terminalMessage w K width n))

theorem oddMass_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < oddMass w K width n :=
  terminalPair_positive hw0 hw1 K width hK (n+1) n

/-- SAME original finite partition, with 2*n+1 temporal transitions. -/
theorem oddMass_compactPartition (w : Q') (K width n : Nat) :
    oddMass w K width n ≈ compactPartition w K width (2*n+1) := by
  have h := Q'.eqv_trans _ _ _ (terminalPair_total w K width (n+1) n)
    (weightedMass_iterate_compactPartition w K width ((n+1)+n))
  have hn : (n+1)+n = 2*n+1 := by omega
  rw [hn] at h
  exact h

/-- The original central edge's total mass is that same positive denominator. -/
theorem edge_total_mass (w : Q') (K width n : Nat) :
    quaternionHaar (N width+N width)
      (edgeDensity w K width (terminalMessage w K width n)) ≈ oddMass w K width n :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one _)))
    (Q'.eqv_trans _ _ _ (edge_window_pairing w K width n (supported_one _))
      (weightedMass_congr w K width
        ((window_unobserved_pin w K width n 1).mul_right (terminalMessage w K width n))))

def normalizedEnergy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  energy w K width (terminalMessage w K width n) f *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

theorem normalizedEnergy_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    (0 : Q') ≤ normalizedEnergy hw0 hw1 K width hK n f :=
  Q'.mul_nonneg _ _
    (energy_nonnegative hw0 hw1 K width hK
      (terminalMessage_supported w K width n) hf
      (terminalMessage_certificate hw0 hw1 K width hK n))
    (Q'.le_of_lt (Q'.recipPos_pos _ (oddMass_positive hw0 hw1 K width hK n)))

/-- Exact normalized squared-difference identity in the EXISTING original window. -/
theorem normalizedEnergy_window {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    (2 : Q') * normalizedEnergy hw0 hw1 K width hK n f ≈
      windowRatio hw0 hw1 K width hK n 1 n (polyMul (jump width f) (jump width f)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (energy_identity w K width (terminalMessage_supported w K width n) hf)
        (edge_window_pairing w K width n
          (supported_polyMul (jump_supported width hf) (jump_supported width hf)))))

private theorem marginal_reorder (g h p : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul g h) p) (polyMul (polyMul h p) g) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 1) (.var 2)) (.var 0)) (by decide)
    (fun | 0 => g | 1 => h | _ => p)

/-- The marginal moments are those of the existing ODD chain, not u_n squared. -/
theorem marginal_middleRatio {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (p : RatPoly) :
    weightedMass w K width
        (polyMul (polyMul (terminalMessage w K width n)
          (transferStep w K width (terminalMessage w K width n))) p) *
        Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n) ≈
      middleRatio hw0 hw1 K width hK (n+1) n p := by
  rw [terminalMessage_next]
  exact Q'.mul_eqv_congr_right _ _ _
    (weightedMass_congr w K width
      (marginal_reorder (terminalMessage w K width n) (terminalMessage w K width (n+1)) p))

end YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow.terminalMessage_next
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow.oddMass
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow.oddMass_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow.oddMass_compactPartition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow.edge_total_mass
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow.normalizedEnergy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow.normalizedEnergy_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow.normalizedEnergy_window
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow.marginal_middleRatio
