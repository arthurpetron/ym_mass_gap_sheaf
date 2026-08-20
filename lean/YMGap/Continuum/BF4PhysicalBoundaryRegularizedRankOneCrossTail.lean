/-
# Finite-prefix/cross-tail closure for the canonical rank-one boundary kernel

`BF4PhysicalBoundaryRegularizedRankOne` constructs a row-normalized positive
boundary kernel directly from the physical amplitude.  Its projective spread
is exactly one, and its action is the explicit normalized aggregate-column
rank-one projection.

This file makes that construction scale-uniform and connects its literal
rank-one defect to the existing finite-prefix/cross-tail machinery.  No
terminal kernel, terminal certificate, terminal Perron estimate, arbitrary
profile, or separate spread budget remains in the input contract.  The only
new physical estimate is

  |A_k(source,boundary)
      - rowMass_k(source) * aggregateProfile_k(boundary)| <= E_k,

together with exact prefix checks and a division-free cross inequality for
`E_k / computedFloor_k` in the analytic tail.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne

namespace YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneCrossTail

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail
open YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingCrossTail
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## 1. The fully determined scale-indexed terminal -/

/-- Canonical normalized aggregate-column terminal at one matched scale. -/
def matchedRegularizedBoundaryRankOneTerminal
    {family : MatchedBlockFamily}
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (scale : Nat) : EdgeLabelling → EdgeLabelling → Q' :=
  centralRegularizedBoundaryRankOneKernel
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (pseudocount scale)
    (pseudocount_pos scale)

/-- Its exact spread-one finite certificate. -/
def matchedRegularizedBoundaryRankOneCertificate
    {family : MatchedBlockFamily}
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (scale : Nat) :
    FiniteCrossRatioDiameterCertificate
      (matchedRegularizedBoundaryRankOneTerminal
        (family := family)
        coupling halfExtent pseudocount pseudocount_pos scale)
      (centralBoundaryChannels
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale))
      (centralBoundaryChannels
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)) :=
  centralRegularizedBoundaryRankOneCertificate
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (pseudocount_pos scale)

/-- The exact finite minimum of the canonical rank-one projection. -/
def matchedRegularizedBoundaryRankOneFloor
    {family : MatchedBlockFamily}
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (scale : Nat) : Q' :=
  centralBoundaryActionFiniteFloor
    (family := family)
    coupling halfExtent
    (matchedRegularizedBoundaryRankOneTerminal
      (family := family)
      coupling halfExtent pseudocount pseudocount_pos)
    (matchedRegularizedBoundaryRankOneCertificate
      (family := family)
      coupling halfExtent pseudocount pseudocount_pos)
    scale

theorem matchedRegularizedBoundaryRankOneFloor_pos
    {family : MatchedBlockFamily}
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (scale : Nat) :
    (0 : Q') <
      matchedRegularizedBoundaryRankOneFloor
        (family := family)
        coupling halfExtent pseudocount pseudocount_pos scale := by
  exact centralBoundaryActionFiniteFloor_pos
    (family := family)
    coupling halfExtent
    (matchedRegularizedBoundaryRankOneTerminal
      (family := family)
      coupling halfExtent pseudocount pseudocount_pos)
    (matchedRegularizedBoundaryRankOneCertificate
      (family := family)
      coupling halfExtent pseudocount pseudocount_pos)
    scale

/-! ## 2. Minimal physical rank-one cross-tail contract -/

/-- Scale-uniform canonical rank-one reduction.  The smoothing terminal and
its projective certificate are computed theorem-side; the sole quantitative
physical input is the explicit defect majorant and its prefix/tail proof. -/
structure MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat)
    (pseudocount : Nat → Q') : Type where
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
  pseudocount_pos :
    ∀ scale, (0 : Q') < pseudocount scale
  errorMajorant : Nat → Q'
  rank_one_defect_le :
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
            centralHalfAmplitudeRegularizedRankOneDefect
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinWeight_nonnegative family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale)
                (pseudocount scale)
                (pseudocount_pos scale)
                source boundary ≤
              errorMajorant scale
  errorTail :
    PositiveFloorErrorCrossTail
      errorMajorant
      (matchedRegularizedBoundaryRankOneFloor
        (family := family)
        coupling halfExtent pseudocount pseudocount_pos)
      physicalRelativeErrorTolerance

namespace MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows

/-- The canonical rank-one data constructs the direct physical
self-smoothing cross-tail interface. -/
def toSelfSmoothingCrossTailRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalBoundarySelfSmoothingCrossTailRows
      family law spacing coupling halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  terminal :=
    matchedRegularizedBoundaryRankOneTerminal
      (family := family)
      coupling halfExtent pseudocount data.pseudocount_pos
  terminalCertificate :=
    matchedRegularizedBoundaryRankOneCertificate
      (family := family)
      coupling halfExtent pseudocount data.pseudocount_pos
  terminal_spread_square_le_split := by
    intro scale
    exact
      centralRegularizedBoundaryRankOneCertificate_spread_square_le_split
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (data.pseudocount_pos scale)
  errorMajorant := data.errorMajorant
  action_defect_le := by
    intro scale source source_mem boundary boundary_mem
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (centralHalfAmplitudeBoundaryActionDefect_eqv_regularizedRankOne
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          (data.pseudocount_pos scale)
          source boundary))
      (data.rank_one_defect_le
        scale source source_mem boundary boundary_mem)
  errorTail := data.errorTail

/-- Therefore the explicit regularized aggregate-column defect reaches the
generic computed-floor physical-error interface. -/
def toComputedFloorErrorRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
      (fun _ => EdgeLabelling)
      family law spacing coupling halfExtent diagonalOrder :=
  data.toSelfSmoothingCrossTailRows.toComputedFloorErrorRows

end MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows

end YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneCrossTail

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneCrossTail.matchedRegularizedBoundaryRankOneFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneCrossTail.MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows.toSelfSmoothingCrossTailRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneCrossTail.MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows.toComputedFloorErrorRows
