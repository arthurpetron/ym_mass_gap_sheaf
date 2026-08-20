/-
# Finite-prefix / cross-tail closure for physical boundary self-smoothing

The physical boundary reduction fixes the abstract terminal factorization to

  ideal_k = A_k P_k

on the literal boundary carrier.  The only entrywise defect is therefore
`|A_k - A_k P_k|`.  This file connects a scalar majorant for that defect to
the existing finite-prefix plus division-free cross-tail theorem.

Exact prefix values may be proposed by an external Rust, C, or Python
program.  The emitted rational inequalities are still rechecked by Lean, and
the infinite tail remains a theorem-level cross-product inequality.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail
import YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction

namespace YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingCrossTail

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail
open YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## 1. The literal self-smoothing floor stream -/

/-- The automatically computed minimum of `A_k P_k` on the retained physical
source-by-boundary rectangle. -/
def centralBoundaryActionFiniteFloor
    {family : MatchedBlockFamily}
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (terminal : ∀ _scale, EdgeLabelling → EdgeLabelling → Q')
    (terminalCertificate : ∀ scale,
      FiniteCrossRatioDiameterCertificate
        (terminal scale)
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)))
    (scale : Nat) : Q' :=
  (terminalSmoothedFiniteFloor
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (centralBoundaryChannels
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale))
    (centralHalfAmplitude
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale))
    (terminal scale)
    ((physicalHalfAmplitudePositiveCoordinateRows
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)).toPositivePrefixRows)
    (terminalCertificate scale)).floor

/-- The literal self-smoothing floor is positive at every scale. -/
theorem centralBoundaryActionFiniteFloor_pos
    {family : MatchedBlockFamily}
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (terminal : ∀ _scale, EdgeLabelling → EdgeLabelling → Q')
    (terminalCertificate : ∀ scale,
      FiniteCrossRatioDiameterCertificate
        (terminal scale)
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)))
    (scale : Nat) :
    (0 : Q') <
      centralBoundaryActionFiniteFloor
        coupling halfExtent terminal
        terminalCertificate scale := by
  exact
    (terminalSmoothedFiniteFloor
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
      (centralBoundaryChannels
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale))
      (centralHalfAmplitude
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale))
      (terminal scale)
      ((physicalHalfAmplitudePositiveCoordinateRows
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)).toPositivePrefixRows)
      (terminalCertificate scale)).floor_pos

/-! ## 2. Physical action defect with finite-prefix/cross-tail closure -/

/-- All theorem-side physical boundary data plus a scalar action-defect
majorant and its finite-prefix/cross-tail certificate. -/
structure MatchedPhysicalBoundarySelfSmoothingCrossTailRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) (diagonalOrder scale) 0
  terminal :
    ∀ _scale, EdgeLabelling → EdgeLabelling → Q'
  terminalCertificate :
    ∀ scale,
      FiniteCrossRatioDiameterCertificate
        (terminal scale)
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
  terminal_spread_square_le_split :
    ∀ scale,
      (terminalCertificate scale).spread *
          (terminalCertificate scale).spread ≤
        splitProjectiveCeiling
  errorMajorant : Nat → Q'
  action_defect_le :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ boundary,
          boundary ∈
              centralBoundaryChannels
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            centralHalfAmplitudeBoundaryActionDefect
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale)
                (terminal scale) source boundary ≤
              errorMajorant scale
  errorTail :
    PositiveFloorErrorCrossTail
      errorMajorant
      (centralBoundaryActionFiniteFloor
        coupling halfExtent terminal terminalCertificate)
      physicalRelativeErrorTolerance

namespace MatchedPhysicalBoundarySelfSmoothingCrossTailRows

/-- The finite-prefix/cross-tail package constructs the direct physical
boundary self-smoothing interface. -/
def toSelfSmoothingRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBoundarySelfSmoothingCrossTailRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicalBoundarySelfSmoothingRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  terminal := data.terminal
  terminalCertificate := data.terminalCertificate
  terminal_spread_square_le_split :=
    data.terminal_spread_square_le_split
  action_defect := by
    intro scale source source_mem boundary boundary_mem
    exact Q'.le_trans' _ _ _
      (data.action_defect_le
        scale source source_mem boundary boundary_mem)
      (data.errorTail.error_le_tolerance_mul_floor scale)

/-- Consequently finite exact prefix checks plus the analytic cross-tail
produce the generic computed-floor physical-error rows. -/
def toComputedFloorErrorRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBoundarySelfSmoothingCrossTailRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
      (fun _ => EdgeLabelling)
      family law spacing coupling
      halfExtent diagonalOrder :=
  data.toSelfSmoothingRows.toComputedFloorErrorRows

end MatchedPhysicalBoundarySelfSmoothingCrossTailRows

end YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingCrossTail

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingCrossTail.centralBoundaryActionFiniteFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingCrossTail.MatchedPhysicalBoundarySelfSmoothingCrossTailRows.toSelfSmoothingRows
#print axioms YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingCrossTail.MatchedPhysicalBoundarySelfSmoothingCrossTailRows.toComputedFloorErrorRows
