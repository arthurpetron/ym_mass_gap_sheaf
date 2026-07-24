import YMGap.Rubric.FrontierDAG
import YMGap.Continuum.CoreBConsumerOrigin
import YMGap.Continuum.CoreBBernsteinConsumer

/-!
# The guarded physical Core-B bridge

`FrontierDAG.CoreBBridge w` is the legacy pointwise bridge signature.  It is
kept unchanged for compatibility and for the exact endpoint inhabitants, but
its type does not record the physical hypotheses `0 ≤ w` and `w ≤ wH`.
Consequently, every use of that legacy signature away from a certified
endpoint needs those bounds supplied externally.  This is a load-bearing
restriction: the mode-zero cross-ratio inequality already fails at couplings
above `wH` (for example at `9 / 16`).

This module supplies the nonbreaking guarded surface.  It does not inhabit a
Core-B bridge, the remaining analytic quotient certificate, or a `FrontierDAG`.
It packages the interval assumptions needed by the physical theorem, records
the exact Type-level analytic input left by the origin-consumer reduction, and
provides the final typed composition from that input to the guarded bridge.
-/

namespace YMGap.Rubric.CoreBPhysicalBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CoreBConsumerOrigin
open YMGap.Continuum.CoreBBernsteinConsumer

/--
The physical Core-B bridge is the legacy pointwise bridge, uniformly over the
certified coupling interval `0 ≤ w ≤ wH`.
-/
abbrev PhysicalCoreBBridge : Type :=
  ∀ (w : Q'), (0 : Q') ≤ w → w ≤ wH →
    YMGap.Rubric.FrontierDAG.CoreBBridge w

/--
The guarded analytic target for Core B: cross-ratio monotonicity throughout
the certified physical coupling interval.
-/
abbrev PhysicalCrossRatioMonotonicity : Type :=
  ∀ (w : Q'), (0 : Q') ≤ w → w ≤ wH →
    FiniteSMarginWorstcase.CrossRatioMonotone w

/-! ## The remaining analytic Core-B input -/

/--
The uniform physical row-one quotient certificate.  This is the remaining
analytic input after the structural recurrence, worst-endpoint base row, and
origin-consumer reductions: for every certified physical coupling, the
explicit row-one-origin universal square-gap quotient is nonnegative at every
length.

The field lives in `Type`, so the family of pointwise certificates is retained
as data.  This module deliberately supplies no inhabitant; constructing one is
the unresolved analytic Core-B obligation.
-/
structure PhysicalRowOneOriginSquareGapQuotientNonnegative : Type where
  certificate : ∀ (w : Q'), (0 : Q') ≤ w → w ≤ wH →
    RowOneOriginSquareGapQuotientNonnegative w

/-- The uniform row-one quotient certificate discharges physical cross-ratio
monotonicity by the origin-consumer adapter, pointwise on `0 ≤ w ≤ wH`. -/
def physicalCrossRatioMonotonicityOfRowOneOriginSquareGapQuotient
    (H : PhysicalRowOneOriginSquareGapQuotientNonnegative) :
    PhysicalCrossRatioMonotonicity :=
  fun w hw0 hwH =>
    crossRatioMonotoneOfRowOneOriginSquareGapQuotient
      hw0 hwH (H.certificate w hw0 hwH)

/--
Guarded cross-ratio monotonicity yields the physical Core-B bridge.  The
pointwise `FiniteSMargin` input is intentionally unused: after cross-ratio
monotonicity has been proved on the physical interval, it is already the
conclusion required by the legacy bridge.
-/
def physicalCoreBBridgeOfCrossRatio
    (H : PhysicalCrossRatioMonotonicity) : PhysicalCoreBBridge :=
  fun w hw0 hwH _ => H w hw0 hwH

/-- Final typed Core-B composition: the sole uniform quotient certificate
produces the guarded legacy bridge throughout the physical coupling interval. -/
def physicalCoreBBridgeOfRowOneOriginSquareGapQuotient
    (H : PhysicalRowOneOriginSquareGapQuotientNonnegative) :
    PhysicalCoreBBridge :=
  physicalCoreBBridgeOfCrossRatio
    (physicalCrossRatioMonotonicityOfRowOneOriginSquareGapQuotient H)

/-! ## The direct Bernstein-family closure interface -/

/-- An all-coupling family of actual canonical-cell Bernstein certificates
inhabits the sole uniform quotient input of the guarded physical bridge. -/
def physicalRowOneOriginSquareGapQuotientOfBernstein
    (H : ∀ (w : Q'), (0 : Q') ≤ w → w ≤ wH →
      PhysicalCanonicalBernsteinFamily w) :
    PhysicalRowOneOriginSquareGapQuotientNonnegative where
  certificate := fun w hw0 hwH =>
    rowOneOriginSquareGapQuotientNonnegativeOfBernstein
      hw0 hwH (H w hw0 hwH)

/-- Final direct composition for the Bernstein route: the all-index
coefficient/reconstruction family produces the guarded physical Core-B
bridge with no further analytic premise. -/
def physicalCoreBBridgeOfBernstein
    (H : ∀ (w : Q'), (0 : Q') ≤ w → w ≤ wH →
      PhysicalCanonicalBernsteinFamily w) :
    PhysicalCoreBBridge :=
  physicalCoreBBridgeOfRowOneOriginSquareGapQuotient
    (physicalRowOneOriginSquareGapQuotientOfBernstein H)

/-- Specialize a physical bridge to a legacy bridge at certified `w`. -/
def legacyCoreBBridgeAt
    (H : PhysicalCoreBBridge) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    YMGap.Rubric.FrontierDAG.CoreBBridge w :=
  H w hw0 hwH

/--
Consume the Core-B component of a `FrontierDAG` only after the coupling has
been certified to lie in the physical interval.
-/
def coreBToCrossRatioPhysical
    {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {D : GNSData} {G : SpectralGapData D.gnsComplete}
    {L : AdditiveTransferOperator D} {N pΓ : Nat}
    (br : PhysicalCoreBBridge)
    (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH)
    (F : YMGap.Rubric.FrontierDAG.FrontierDAG p w G L N pΓ) :
    FiniteSMarginWorstcase.CrossRatioMonotone w :=
  YMGap.Rubric.FrontierDAG.coreBToCrossRatio
    (legacyCoreBBridgeAt br hw0 hwH) F

#print axioms PhysicalCoreBBridge
#print axioms PhysicalCrossRatioMonotonicity
#print axioms PhysicalRowOneOriginSquareGapQuotientNonnegative
#print axioms physicalCrossRatioMonotonicityOfRowOneOriginSquareGapQuotient
#print axioms physicalCoreBBridgeOfCrossRatio
#print axioms physicalCoreBBridgeOfRowOneOriginSquareGapQuotient
#print axioms physicalRowOneOriginSquareGapQuotientOfBernstein
#print axioms physicalCoreBBridgeOfBernstein
#print axioms legacyCoreBBridgeAt
#print axioms coreBToCrossRatioPhysical

end YMGap.Rubric.CoreBPhysicalBridge
