/-
# Unconditional fixed-carrier BF4 same-object gap

The canonical-path edge floor is now constructed.  This module applies the
uniform finite Poincare compiler and its exact Bishop-real limit contraction
to that explicit witness.  The result has no remaining edge-floor or rate
certificate argument: one rational rate, constructively proved below one,
works for every coefficient on the fixed cutoff-two pulled vacuum carrier.

This is not yet a completed vacuum-complement gap.  The fixed 65-state carrier
has not been proved dense or cofinal in the cutoff-removed physical carrier.
No thermodynamic or continuum limit is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformCRealGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledConstructedUniformCRealGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformCRealGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap

/-- One sealed package carries the constructed rational rate, its strictness,
the entire finite tail estimate, and the same-object Bishop-real estimate.
Keeping these dependent fields together prevents downstream elaboration from
normalizing the explicit 65 by 65 finite minimum. -/
structure CutoffTwoConstructedUniformGapData : Type 1 where
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  moving_abs_gap : ∀ later : Nat,
    cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later →
    ∀ coefficient : Nat → Q',
      Q'.abs
          (cutoffTwoPulledMatrixAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)) ≤
        rate *
          cutoffTwoPulledDiagonalAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)
  cutoffLimit_gap : ∀ coefficient : Nat → Q',
    CReal.leEv
      (cutoffTwoMovingMatrixLimit coefficient)
      (CReal.mul
        (CReal.ofQ' rate)
        (cutoffTwoMovingDiagonalLimit coefficient))

/-- **Unconditional fixed-carrier same-object gap data.**  The body is fully
kernel checked and sealed only as a presentation boundary for the explicit
finite certificate. -/
opaque cutoffTwoConstructedUniformGapData :
    CutoffTwoConstructedUniformGapData :=
  { rate :=
      CutoffTwoPulledUniformBasePositiveEdgeFloor.uniformPoincareRate
        cutoffTwoPulledUniformBasePositiveEdgeFloor
    rate_nonnegative :=
      CutoffTwoPulledUniformBasePositiveEdgeFloor.uniformPoincareRate_nonnegative
        cutoffTwoPulledUniformBasePositiveEdgeFloor
    rate_lt_one :=
      CutoffTwoPulledUniformBasePositiveEdgeFloor.uniformPoincareRate_lt_one
        cutoffTwoPulledUniformBasePositiveEdgeFloor
    moving_abs_gap := by
      intro later hlater coefficient
      exact
        CutoffTwoPulledUniformBasePositiveEdgeFloor.moving_abs_gap_at_uniformPoincareRate
          cutoffTwoPulledUniformBasePositiveEdgeFloor later hlater coefficient
    cutoffLimit_gap := by
      intro coefficient
      exact centeredMatrixCutoffLimit_leEv_uniformPoincareRate_mul_diagonal
        cutoffTwoPulledUniformBasePositiveEdgeFloor coefficient }

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledConstructedUniformCRealGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledConstructedUniformCRealGap.cutoffTwoConstructedUniformGapData
