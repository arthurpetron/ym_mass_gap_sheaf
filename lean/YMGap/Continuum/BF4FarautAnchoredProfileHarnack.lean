/-
# Faraut/Perron remainder to calibrated BF4 profile Harnack

The positive-kernel profile layer asks for a squared projective spread at
most `65/64`.  The AF/Faraut depth layer produces the exact remainder

    C_b^2 q^(m-2) <= 1/64

at depth `m >= 46 b + 5`.  This file joins those two statements.

The only analytic comparison retained as a premise is the mathematically
meaningful Perron estimate

    spread^2 <= 1 + C_b^2 q^(m-2).

Once the grouped physical kernel supplies that estimate and the two exact
kernel-action identifications, both calibrated cross-zero `1/64` profile
windows follow constructively.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack
import YMGap.Continuum.BF4FarautJointCarrierAFBudget

namespace YMGap.Continuum.BF4FarautAnchoredProfileHarnack

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack
open YMGap.Continuum.BF4CalibratedEmptyProfileWindow
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- The Faraut tolerance is exactly the additive part of the anchored
projective ceiling. -/
theorem one_add_farautHarnackTolerance_eqv_anchoredProjectiveCeiling :
    (1 : Q') + farautHarnackTolerance ≈
      anchoredProjectiveCeiling := by
  unfold farautHarnackTolerance anchoredProjectiveCeiling
  decide

/-- A Perron remainder below `1/64` turns the natural
`spread^2 <= 1 + remainder` estimate into the exact anchored-projective
spread cap. -/
theorem spreadSquare_le_anchoredProjectiveCeiling_of_remainder
    {spread remainder : Q'}
    (spreadSquare_le :
      spread * spread ≤ (1 : Q') + remainder)
    (remainder_le :
      remainder ≤ farautHarnackTolerance) :
    spread * spread ≤ anchoredProjectiveCeiling := by
  have hadd :
      (1 : Q') + remainder ≤
        (1 : Q') + farautHarnackTolerance :=
    Q'.add_le_add_left 1 remainder
      farautHarnackTolerance remainder_le
  exact Q'.le_trans' _ _ _ spreadSquare_le
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        one_add_farautHarnackTolerance_eqv_anchoredProjectiveCeiling))

/-- The sharpened AF/Faraut depth discharges the squared-spread premise
from a quantitative Perron comparison. -/
theorem spreadSquare_le_anchoredProjectiveCeiling_of_farautPerron
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sources targets)
    (bits : Nat) (qS : Q') (m : Nat)
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautHarnackRequiredDepth bits ≤ m)
    (projectivePerron :
      certificate.spread * certificate.spread ≤
        (1 : Q') +
          farautPerronSquare bits * qS ^ (m - 2)) :
    certificate.spread * certificate.spread ≤
      anchoredProjectiveCeiling :=
  spreadSquare_le_anchoredProjectiveCeiling_of_remainder
    projectivePerron
    (faraut_perron_harnack_of_available_depth
      bits qS m qS_nonnegative qS_le_quarter
      depth_available)

/-- **AF/Faraut common-kernel BF4 Harnack theorem.**

At the sharpened physical depth, a Perron comparison for the same grouped
positive kernel that realizes the calibrated and physical activities
inhabits both cross-zero `1/64` BF4 profile windows. -/
def calibratedEmptyCrossZeroProfileHarnackData_of_farautKernelActions
    {Source : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat)
    (kernel : Source → EdgeLabelling → Q')
    (sources : List Source)
    (candidate physical : Source → Q')
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sources
        (BF4RetainedProfileStates
          w hw K halfExtent))
    (candidateActivity :
      FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
        sources candidate)
    (physicalActivity :
      FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
        sources physical)
    (bits : Nat) (qS : Q') (m : Nat)
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautHarnackRequiredDepth bits ≤ m)
    (projectivePerron :
      certificate.spread * certificate.spread ≤
        (1 : Q') +
          farautPerronSquare bits * qS ^ (m - 2))
    (candidate_identification :
      ∀ state,
        state ∈
            BF4RetainedProfileStates
              w hw K halfExtent →
          BF4CalibratedRightProfile
              w hw K halfExtent diagonalOrder state ≈
            FiniteCrossRatioDiameterCertificate.finiteKernelAction
              kernel sources candidate state)
    (physical_identification :
      ∀ state,
        state ∈
            BF4RetainedProfileStates
              w hw K halfExtent →
          BF4PhysicalProfile
              w hw K halfExtent state ≈
            FiniteCrossRatioDiameterCertificate.finiteKernelAction
              kernel sources physical state) :
    CalibratedEmptyProfileHarnackData
      w hw K halfExtent diagonalOrder 0 :=
  calibratedEmptyCrossZeroProfileHarnackData_of_kernelActions
    w hw K halfExtent diagonalOrder
    kernel sources candidate physical
    certificate candidateActivity physicalActivity
    (spreadSquare_le_anchoredProjectiveCeiling_of_farautPerron
      certificate bits qS m
      qS_nonnegative qS_le_quarter
      depth_available projectivePerron)
    candidate_identification physical_identification

end YMGap.Continuum.BF4FarautAnchoredProfileHarnack

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4FarautAnchoredProfileHarnack.spreadSquare_le_anchoredProjectiveCeiling_of_remainder
#print axioms YMGap.Continuum.BF4FarautAnchoredProfileHarnack.spreadSquare_le_anchoredProjectiveCeiling_of_farautPerron
#print axioms YMGap.Continuum.BF4FarautAnchoredProfileHarnack.calibratedEmptyCrossZeroProfileHarnackData_of_farautKernelActions
