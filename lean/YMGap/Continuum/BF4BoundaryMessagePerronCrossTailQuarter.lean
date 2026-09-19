/-
# Perron/cross-tail data reaches the physical quarter consumer

The terminal Perron/cross-tail interface already contains the analytic
entrywise estimate needed by the computed-floor physical half-amplitude
route.  The downstream completed-carrier consumer, however, is phrased in
the rowwise-eighth interface.  This module records that exact
forward/backward join in one declaration:

  terminal Perron/cross-tail data
      -> computed finite floor
      -> physical rowwise eighths
      -> completed physical quarter contraction.

No field is synthesized here.  In particular, the terminal certificate,
cross-tail error tail, AF chart, and spacing envelope remain explicit inputs.
This is a compiler for an existing certificate, not an inhabitant of the
analytic producer and not a thermodynamic, continuum, or Clay result.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4BoundaryMessageComputedFloorQuarter
import YMGap.Continuum.BF4BoundaryMessageQuarterLimitTransfer
import YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingPerronCrossTail
import YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth

namespace YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4BoundaryMessageComputedFloorQuarter
open YMGap.Continuum.BF4BoundaryMessagePhysicalTerminalFloorAdapter
open YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh
open YMGap.Continuum.BF4BoundaryMessageQuarterLimitTransfer
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingPerronCrossTail
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

namespace MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows

/-- The same producer also reaches the uniform finite boundary-message
quarter certificate used by the local refresh route. -/
def toUniformBoundaryMessageQuarterCertificate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (data :
      MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows
        family law spacing coupling halfExtent diagonalOrder bits depth
        nonlinearRate) :=
  YMGap.Continuum.BF4BoundaryMessageComputedFloorQuarter.MatchedPhysicalHalfAmplitudeComputedFloorErrorRows.toUniformBoundaryMessageQuarterCertificate
    data.toComputedFloorErrorRows

/-! ## A canonical terminal positivity compiler -/

/-- The existing Perron terminal certificate supplies a canonical positive
terminal message by fixing the distinguished zero boundary channel as its
source.  This discharges the terminal-positivity half of the generic limit
interface; denominator positivity remains a separate source-wise obligation.
-/
def physicalTerminal
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (producer :
      MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows
        family law spacing coupling halfExtent diagonalOrder bits depth
        nonlinearRate) : Nat → PhysicalEdgeLabelling → Q' :=
  fun scale target => producer.terminal scale zeroEdgeLabelling target

theorem physicalTerminal_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (producer :
      MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows
        family law spacing coupling halfExtent diagonalOrder bits depth
        nonlinearRate) :
    ∀ scale target,
      target ∈ physicalBoundaryMessageTargets family coupling halfExtent scale →
        (0 : Q') < physicalTerminal producer scale target := by
  intro scale target target_mem
  change target ∈
    centralBoundaryChannels
      (matchedAllSpinCutoff family coupling scale) (halfExtent scale) at target_mem
  change (0 : Q') < producer.terminal scale zeroEdgeLabelling target
  exact (producer.terminalCertificate scale).strictlyPositive
    zeroEdgeLabelling
    (zeroEdgeLabelling_mem_centralBoundaryChannels
      (matchedAllSpinCutoff family coupling scale) (halfExtent scale))
    target target_mem

/-! ## The backward limit-input bundle -/

/-
The finite producer and the cutoff-removal theorem meet here.  The fields
below are deliberately the complete backward interface: positivity of the
terminal message and its denominators, equal source mass, and effective
Cauchy moduli for the input and refreshed output distances.  No field is
constructed from boundedness or from a numerical limit.
-/

structure QuarterLimitInputs
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (producer :
      MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows
        family law spacing coupling halfExtent diagonalOrder bits depth
        nonlinearRate) : Type 1 where
  limitInputs :
    UniformBoundaryMessageQuarterLimitInputs
      (fun _ => PhysicalEdgeLabelling)
      (fun _ => PhysicalEdgeLabelling)
      (physicalBoundaryMessageKernel family coupling halfExtent)
      (physicalBoundaryMessageSources family coupling halfExtent)
      (physicalBoundaryMessageTargets family coupling halfExtent)
      (toUniformBoundaryMessageQuarterCertificate producer)

/-
This is the exact backward-to-forward compiler: the generic limit theorem is
applied to the certificate generated by the physical producer, so the output
is a completed `CReal` contraction for the same finite distance streams.
-/
def QuarterLimitInputs.toQuarterContractionLimitData
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    {producer :
      MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows
        family law spacing coupling halfExtent diagonalOrder bits depth
        nonlinearRate}
    (inputs : QuarterLimitInputs producer) :=
  inputs.limitInputs.toQuarterContractionLimitData

theorem QuarterLimitInputs.continuum_l1_quarter_contraction
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    {producer :
      MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows
        family law spacing coupling halfExtent diagonalOrder bits depth
        nonlinearRate}
    (inputs : QuarterLimitInputs producer) :
    let data := inputs.toQuarterContractionLimitData
    CReal.leEv data.outputLimit
      (CReal.mul (CReal.ofQ' quarterRate) data.inputLimit) := by
  dsimp only [QuarterLimitInputs.toQuarterContractionLimitData]
  exact inputs.limitInputs.continuum_l1_quarter_contraction

/-- The Perron/cross-tail producer reaches the literal physical rowwise
eighth interface after the finite positive floor is computed. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (data :
      MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows
        family law spacing coupling halfExtent diagonalOrder bits depth
        nonlinearRate) :
  MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling halfExtent diagonalOrder (fun _ => 0) :=
  data.toComputedFloorErrorRows.toTerminalFloorErrorRows.toRowwiseEighthEstimates

/-- The same join exposes the completed physical quarter contraction at every
matched scale, with the observable and mean-zero witness unchanged. -/
theorem physical_quarter_uniform
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (data :
      MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows
        family law spacing coupling halfExtent diagonalOrder bits depth
        nonlinearRate)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (mean_zero :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable := by
  exact
    (MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows.toRowwiseEighthEstimates
      data).physical_quarter_uniform
      scale observable mean_zero

end MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows

end YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter

#print axioms
  YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter.MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows.toUniformBoundaryMessageQuarterCertificate
#print axioms
  YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter.MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows.physicalTerminal
#print axioms
  YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter.MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows.physicalTerminal_pos
#print axioms
  YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter.MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows.QuarterLimitInputs.toQuarterContractionLimitData
#print axioms
  YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter.MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows.QuarterLimitInputs.continuum_l1_quarter_contraction
#print axioms
  YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter.MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows.toRowwiseEighthEstimates
#print axioms
  YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter.MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows.physical_quarter_uniform
