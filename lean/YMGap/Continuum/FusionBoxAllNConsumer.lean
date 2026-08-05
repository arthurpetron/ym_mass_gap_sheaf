/-
`FusionBoxAllNConsumer` -- close the elementary first-excited edge at the
physical endpoint and fire the proved uniform box consumer for every cutoff.

`FusionBoxShellReserve.uniformBoxLogConcave_half` proves the full all-cutoff
box log-concavity theorem at `w = 1/2`.  The existing consumer into
`S1Dominance N w 2` additionally asks for the boundary comparison

    bondMovedCoeff N w 2 2 <= bondMovedCoeff N w 2 1.

At the endpoint this comparison is not a new local-CLT input.  The even strand
ceiling at mode two gives

    boxSum (1/2) N 2 <= (13/8) * coeffW(1)^2,

while the two central odd terms give

    2 * coeffW(0) * coeffW(1) <= boxSum (1/2) N 1.

The intervening scalar inequality is closed rational arithmetic.  This closes
the edge for every `N` (with the empty cutoff handled separately), and hence
inhabits the entire endpoint family `S1Dominance N (1/2) 2`.

Honest scope: this module supplies `S1Dominance`, the exact consumer of the box
theorem.  It does not identify that datum with either spectral-localization
carrier and does not inhabit a `FrontierDAG` field.
-/

import YMGap.Continuum.FusionBoxShellReserve

namespace YMGap.Continuum.FusionBoxAllNConsumer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionBoxStrandCeilings
open YMGap.Continuum.FusionBoxShellReserve

/-- A local unambiguous name for the physical endpoint `w = 1/2`. -/
private abbrev halfW : Q' := YMGap.Continuum.FusionCoreStepRoundA.wH

/-- The elementary first-excited edge at `w = 1/2`, uniformly in the cutoff.

For a nonempty cutoff, mode two is bounded by the proved even-strand ceiling
and mode one contains the two central `(0,1)` and `(1,0)` channels.  At `N = 0`
both excited channels vanish, which is closed computation. -/
theorem firstExcitedEdge_allN_half (N : Nat) :
    bondMovedCoeff N halfW 2 2 <= bondMovedCoeff N halfW 2 1 := by
  cases N with
  | zero => decide
  | succ n =>
      have htwo : boxSum halfW (n + 1) 2 <=
          Q'.mkPos 13 8 (by decide) *
            (coeffW halfW 1 * coeffW halfW 1) := by
        simpa only [Nat.reduceMul] using boxSum_even_ceiling (n + 1) 1
      have hone :
          coeffW halfW 0 * coeffW halfW 1 +
              coeffW halfW 0 * coeffW halfW 1 <=
            boxSum halfW (n + 1) 1 := by
        simpa only [Nat.zero_add, Nat.zero_mul] using
          boxSum_odd_central_lower (n + 1) 0 (by omega)
      have hscalar :
          Q'.mkPos 13 8 (by decide) *
              (coeffW halfW 1 * coeffW halfW 1) <=
            coeffW halfW 0 * coeffW halfW 1 +
              coeffW halfW 0 * coeffW halfW 1 := by
        decide
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (bondMovedCoeff_eq_boxSum (n + 1) 2))
        (Q'.le_trans' _ _ _ htwo
          (Q'.le_trans' _ _ _ hscalar
            (Q'.le_trans' _ _ _ hone
              (Q'.ge_of_eqv (bondMovedCoeff_eq_boxSum (n + 1) 1)))))

/-- The complete all-cutoff endpoint consumer: the uniformly log-concave
`p = 2` fusion tower is maximized on its excited range at mode one. -/
def s1Dominance_allN_half (N : Nat) :
    YMGap.Continuum.S1Dominance.S1Dominance N halfW 2 :=
  YMGap.Continuum.FusionCoreStepRoundA.s1DominanceOfUniform
    (by decide) (by decide) uniformBoxLogConcave_half N
      (firstExcitedEdge_allN_half N)

/-- The same result exposed as one dependent all-`N` family. -/
def s1Dominance_family_half :
    forall N, YMGap.Continuum.S1Dominance.S1Dominance N halfW 2 :=
  fun N => s1Dominance_allN_half N

#print axioms YMGap.Continuum.FusionBoxAllNConsumer.firstExcitedEdge_allN_half
#print axioms YMGap.Continuum.FusionBoxAllNConsumer.s1Dominance_allN_half
#print axioms YMGap.Continuum.FusionBoxAllNConsumer.s1Dominance_family_half

end YMGap.Continuum.FusionBoxAllNConsumer
