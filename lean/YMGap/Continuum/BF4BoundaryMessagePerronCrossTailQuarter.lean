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
import YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingPerronCrossTail
import YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth

namespace YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4BoundaryMessageComputedFloorQuarter
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingPerronCrossTail
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

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
  YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter.MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows.toRowwiseEighthEstimates
#print axioms
  YMGap.Continuum.BF4BoundaryMessagePerronCrossTailQuarter.MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows.physical_quarter_uniform
