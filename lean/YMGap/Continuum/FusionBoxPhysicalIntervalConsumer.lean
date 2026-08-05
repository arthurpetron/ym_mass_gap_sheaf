/-
`FusionBoxPhysicalIntervalConsumer` -- the exact typed consumer from the
post-boundary integer reserve to uniform box log-concavity on the physical
coupling interval.

The existing Bernstein reconstruction asks for two inputs:

* the all-cutoff physical prefix reserve;
* the strong-coupling scalar bound `coeffW w 1 ^ 2 <= 3`.

The first is supplied constructively by
`allCutoffPhysicalPrefixReserve_of_postBoundary`.  The second follows with
ample room from the proved physical-interval estimate
`coeffW w 1 <= 1/4`.  This module performs only that composition and exposes
both the pointwise constructor and its dependent all-coupling family.

Honest scope: `PostBoundaryEvenOddPrefixReserve` remains an explicit input.
Nothing here inhabits that reserve or any `FrontierDAG` field.
-/

import YMGap.Continuum.FusionBoxShellReserve

namespace YMGap.Continuum.FusionBoxPhysicalIntervalConsumer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionBoxPrefixReserve
open YMGap.Continuum.FusionBoxShellReserve

/-- On the full physical interval `0 <= w <= 1/2`, the scalar
strong-coupling premise required by `UniformBoxLogConcave` holds.

The proved estimate `coeffW w 1 <= 1/4` bounds the square by `1/16`, and
closed rational arithmetic gives `1/16 <= 3`. -/
theorem coeffW1_sq_le_three_physical {w : Q'}
    (hw0 : (0 : Q') <= w) (hwH : w <= wH) :
    coeffW w 1 * coeffW w 1 <= (3 : Q') := by
  have hc : coeffW w 1 <= Q'.mkPos 1 4 (by decide) :=
    coeffW1_le_quarter hw0 hwH
  have hc0 : (0 : Q') <= coeffW w 1 := coeffW_nonneg hw0 1
  have hfirst : coeffW w 1 * coeffW w 1 <=
      Q'.mkPos 1 4 (by decide) * coeffW w 1 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hc hc0
  have hsecond : Q'.mkPos 1 4 (by decide) * coeffW w 1 <=
      Q'.mkPos 1 4 (by decide) * Q'.mkPos 1 4 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hc (by decide)
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond (by decide))

/-- Pointwise physical-interval constructor.  A single post-boundary
even/odd prefix reserve supplies `UniformBoxLogConcave w` at any
`0 <= w <= 1/2`. -/
def uniformBoxLogConcave_of_postBoundary
    (reserve : PostBoundaryEvenOddPrefixReserve) {w : Q'}
    (hw0 : (0 : Q') <= w) (hwH : w <= wH) :
    UniformBoxLogConcave w :=
  uniformBoxLogConcave_of_physical_prefix_reserve hw0 hwH
    (coeffW1_sq_le_three_physical hw0 hwH)
    (allCutoffPhysicalPrefixReserve_of_postBoundary reserve)

/-- The same constructor exposed as one dependent family over the whole
physical interval. -/
def uniformBoxLogConcave_physical_interval
    (reserve : PostBoundaryEvenOddPrefixReserve) :
    forall w, (0 : Q') <= w -> w <= wH -> UniformBoxLogConcave w :=
  fun _w hw0 hwH => uniformBoxLogConcave_of_postBoundary reserve hw0 hwH

#print axioms YMGap.Continuum.FusionBoxPhysicalIntervalConsumer.coeffW1_sq_le_three_physical
#print axioms YMGap.Continuum.FusionBoxPhysicalIntervalConsumer.uniformBoxLogConcave_of_postBoundary
#print axioms YMGap.Continuum.FusionBoxPhysicalIntervalConsumer.uniformBoxLogConcave_physical_interval

end YMGap.Continuum.FusionBoxPhysicalIntervalConsumer
