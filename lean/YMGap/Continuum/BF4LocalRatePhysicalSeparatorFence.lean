/-
M2 -- a type-level fence separating the auxiliary BF4 local-gluing rate from
the microscopic physical separator.

The local-gluing certificate has a scale-uniform auxiliary rate at most one
quarter.  A physical separator with a linear margin along a spacing tending to
zero is eventually at least one half.  Consequently the two rates cannot be
identified at every scale.

This is a no-go theorem, not a construction of the missing physical transfer
operator or its separator.  Its purpose is to prevent finite BF4 contraction
checks from being mistaken for the M2 physical-time estimate.
-/

import YMGap.Continuum.BF4PhysicalSeparatorProducer
import YMGap.Continuum.PhysicalSeparatorLinearTail

namespace YMGap.Continuum.BF4LocalRatePhysicalSeparatorFence

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLinearTail

local infix:50 " ≈ " => Q'.eqv

/-- The auxiliary local-gluing rate cannot be the physical separator on every
scale of a vanishing-spacing trajectory satisfying the required linear
physical-margin estimate. -/
theorem localRate_ne_physicalSeparator_of_linearMargin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer :
      BF4QuarterPhysicalSeparatorProducer family law spacing coupling P)
    (linear : LinearMarginTail P producer.physicalSpacing)
    (toZero : SpacingToZero producer.physicalSpacing)
    (identify : ∀ scale, P.sep scale ≈ producer.bf4.localRate scale) :
    False := by
  let scale := linear.eventualStart toZero
  have hhalf : HalfPow.half ≤ P.sep scale :=
    (linear.toEventualHalfWindow toZero).sep_ge_half scale (Nat.le_refl _)
  have hquarter : P.sep scale ≤ FiveHolonomyPerronCutoff.quarter :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (identify scale))
      (producer.bf4.localRate_le_quarter scale)
  have himpossible :
      ¬ HalfPow.half ≤ FiveHolonomyPerronCutoff.quarter := by decide
  exact himpossible (Q'.le_trans' _ _ _ hhalf hquarter)

end YMGap.Continuum.BF4LocalRatePhysicalSeparatorFence

#print axioms YMGap.Continuum.BF4LocalRatePhysicalSeparatorFence.localRate_ne_physicalSeparator_of_linearMargin
