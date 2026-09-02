/-
# Positivity interface for retained boundary totals

A nonnegative finite half-amplitude sum is strictly positive whenever one
retained state has strictly positive amplitude.  Keeping this theorem generic
prevents downstream concrete certificates from unfolding very large carriers.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
import YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
import YMGap.Continuum.FiniteChannelTotalAmplitudePositivity

namespace YMGap.Continuum.BF4PositiveBoundaryTotalPositivity

set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteChannelTotalAmplitudePositivity
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-- One positive retained half-amplitude makes the complete retained boundary
total strictly positive. -/
theorem centralPositiveBoundaryTotalHalfAmplitude_pos_of_mem
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    {state boundary : EdgeLabelling}
    (hstate : state ∈ centralPositiveHalfStates w hw K half)
    (hpositive : (0 : Q') <
      centralHalfAmplitude w K half state boundary) :
    (0 : Q') <
      centralPositiveBoundaryTotalHalfAmplitude
        w hw K half boundary := by
  unfold centralPositiveBoundaryTotalHalfAmplitude
  exact finiteChannelTotalAmplitude_pos_of_mem
    (centralPositiveHalfStates w hw K half)
    (centralHalfAmplitude w K half)
    hstate
    (fun candidate => centralHalfAmplitude_nonnegative
      hw K half candidate boundary)
    hpositive

end YMGap.Continuum.BF4PositiveBoundaryTotalPositivity

#print axioms
  YMGap.Continuum.BF4PositiveBoundaryTotalPositivity.centralPositiveBoundaryTotalHalfAmplitude_pos_of_mem
