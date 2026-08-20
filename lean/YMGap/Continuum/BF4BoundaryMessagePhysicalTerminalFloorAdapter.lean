/-
# Physical terminal-floor data directly supplies boundary-message contraction

The existing physical terminal-floor/error interface already constructs a
cross-ratio estimate for the literal BF4 half-amplitude with squared spread at
most `65/64`.  This is stronger than the `4/3` gate needed for a quarter-rate
boundary-message refresh.

This file packages that observation without changing the physical carrier:
the sources are the selected positive half-states, the targets are the central
boundary channels, and the raw kernel is the genuine `centralHalfAmplitude`.
The remaining analytic inputs are exactly those in
`MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows`: a positive pointwise
floor for the ideal terminal-smoothed kernel and a physical entry error at
most `1/2048` of that floor.
-/

import YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh
import YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation

namespace YMGap.Continuum.BF4BoundaryMessagePhysicalTerminalFloorAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## 1. The literal scale-indexed physical kernel -/

abbrev PhysicalEdgeLabelling :=
  YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling

/-- The fixed rational spread used uniformly across every physical scale. -/
def physicalBoundaryMessageUniformSpread : Q' :=
  Q'.mkPos 33 32 (by decide)

theorem physicalBoundaryMessageUniformSpread_one_le :
    (1 : Q') <= physicalBoundaryMessageUniformSpread := by
  decide

theorem anchoredProjectiveCeiling_le_uniformSpread_square :
    anchoredProjectiveCeiling <=
      physicalBoundaryMessageUniformSpread *
        physicalBoundaryMessageUniformSpread := by
  decide

theorem physicalBoundaryMessageUniformSpread_square_le_fourThirds :
    physicalBoundaryMessageUniformSpread *
        physicalBoundaryMessageUniformSpread <=
      fourThirdsSpreadSquare := by
  decide

theorem physicalBoundaryMessageUniformCommonMass_lt_one :
    Q'.divPos 1
        (physicalBoundaryMessageUniformSpread *
          physicalBoundaryMessageUniformSpread)
        (Q'.mul_pos (by decide) (by decide)) < (1 : Q') := by
  decide

def physicalBoundaryMessageKernel
    (family : MatchedBlockFamily)
    (coupling : Nat -> Q')
    (halfExtent : Nat -> Nat)
    (scale : Nat) (source target : PhysicalEdgeLabelling) : Q' :=
  centralHalfAmplitude
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale) source target

def physicalBoundaryMessageSources
    (family : MatchedBlockFamily)
    (coupling : Nat -> Q')
    (halfExtent : Nat -> Nat)
    (scale : Nat) : List PhysicalEdgeLabelling :=
  centralPositiveHalfStates
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)

def physicalBoundaryMessageTargets
    (family : MatchedBlockFamily)
    (coupling : Nat -> Q')
    (halfExtent : Nat -> Nat)
    (scale : Nat) : List PhysicalEdgeLabelling :=
  centralBoundaryChannels
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)

/-! ## 2. Direct adapter from the physical terminal-floor/error interface -/

namespace MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows

/-- The literal physical half-amplitude family has one fixed cross-ratio
spread `33/32` at every regulator. -/
def toUniformPhysicalCrossRatioCertificate
    {Middle : Nat -> Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {halfExtent diagonalOrder : Nat -> Nat}
    (data :
      MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows
        Middle family law spacing coupling
        halfExtent diagonalOrder) :
    UniformCrossRatioDiameterCertificate
      Nat (fun _ => PhysicalEdgeLabelling) (fun _ => PhysicalEdgeLabelling)
      (physicalBoundaryMessageKernel family coupling halfExtent)
      (physicalBoundaryMessageSources family coupling halfExtent)
      (physicalBoundaryMessageTargets family coupling halfExtent) where
  spread := physicalBoundaryMessageUniformSpread
  one_le_spread := physicalBoundaryMessageUniformSpread_one_le
  strictlyPositive := by
    intro scale source source_mem target target_mem
    exact data.physical_entry_pos
      scale source target source_mem target_mem
  crossRatioBound := by
    intro scale first first_mem second second_mem
      left left_mem right right_mem
    let projective :=
      data.toApproxTerminalSmoothingRows.toHalfAmplitudeProjectiveRows
    have hphysical :=
      projective.half_amplitude_cross_ratio
        scale first first_mem second second_mem
        left left_mem right right_mem
    have hspread :
        projective.spread scale * projective.spread scale <=
          physicalBoundaryMessageUniformSpread *
            physicalBoundaryMessageUniformSpread :=
      Q'.le_trans' _ _ _
        (projective.spread_square_le scale)
        anchoredProjectiveCeiling_le_uniformSpread_square
    have hreverse_nonnegative :
        (0 : Q') <=
          physicalBoundaryMessageKernel family coupling halfExtent
              scale first right *
            physicalBoundaryMessageKernel family coupling halfExtent
              scale second left :=
      Q'.mul_nonneg _ _
        (centralHalfAmplitude_nonnegative
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale) first right)
        (centralHalfAmplitude_nonnegative
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale) second left)
    exact Q'.le_trans' _ _ _ hphysical
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        hspread hreverse_nonnegative)

/-- The physical terminal-floor/error package directly constructs the
terminal-independent quarter-contraction certificate. -/
def toUniformBoundaryMessageQuarterCertificate
    {Middle : Nat -> Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {halfExtent diagonalOrder : Nat -> Nat}
    (data :
      MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows
        Middle family law spacing coupling
        halfExtent diagonalOrder) :
    UniformBoundaryMessageQuarterCertificate
      Nat (fun _ => PhysicalEdgeLabelling) (fun _ => PhysicalEdgeLabelling)
      (physicalBoundaryMessageKernel family coupling halfExtent)
      (physicalBoundaryMessageSources family coupling halfExtent)
      (physicalBoundaryMessageTargets family coupling halfExtent) where
  crossRatio := toUniformPhysicalCrossRatioCertificate data
  spreadSquare_le :=
    physicalBoundaryMessageUniformSpread_square_le_fourThirds
  commonMass_lt_one := by
    intro scale
    unfold commonMass
    change Q'.divPos 1
      (physicalBoundaryMessageUniformSpread *
        physicalBoundaryMessageUniformSpread) _ < (1 : Q')
    exact physicalBoundaryMessageUniformCommonMass_lt_one
  reference := fun _ =>
    YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  reference_mem := by
    intro scale
    exact zeroEdgeLabelling_mem_centralPositiveHalfStates
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)

end MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows

end YMGap.Continuum.BF4BoundaryMessagePhysicalTerminalFloorAdapter

#print axioms YMGap.Continuum.BF4BoundaryMessagePhysicalTerminalFloorAdapter.MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows.toUniformPhysicalCrossRatioCertificate
#print axioms YMGap.Continuum.BF4BoundaryMessagePhysicalTerminalFloorAdapter.MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows.toUniformBoundaryMessageQuarterCertificate
