/-
# Conditional canonical rankwise trajectory-gluing reduction

All analytic and carrier choices in the adjacent-even reflection problem are
now fixed: one symbolic incidence-field carrier contains every mixed
trajectory field, its production fixed-face kernel has a constructive Gram,
and the terminal endpoint product is preserved by the same outgoing field.

This leaf isolates a strong sufficient theorem as canonical rankwise
shared-glue data.  An inhabitant transports mechanically to the reachable
Gram, the literal physical Gram, physical positive semidefiniteness, and the
equivalent active-reachable positivity statement.  No inhabitant is asserted
here.

The fixed-original-rank counterfence proves that a literal termwise
interpretation of this datum is false: an individual adjacent-face rank
contribution can be nonsymmetric.  Thus this remains a valid conditional
adapter only if ranks are first reorganized into an actually symmetric
factorization.  The production route should instead target the direct active
quadratic SOS, where all face ranks and Haar features may mix.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFeatureTrajectoryGluing
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTrajectoryTerminalField
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableScaledQuadratic

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCanonicalTrajectoryGluingReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFeatureTrajectoryGluing
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceChannelCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSandwichReduction
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableScaledQuadratic
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTrajectoryFieldRealization

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A strong conditional canonical datum -/

/-- A strong sufficient constructive datum.  Its middle carrier and local
Gram are no longer arbitrary: they are the canonical symbolic incidence
carrier and its proved production Gram.  A finite shared-glue carrier, its
rank-aware half amplitude, and the global entrywise factorization remain.
The datum is not claimed to arise by keeping each original Gram rank fixed. -/
structure AdjacentEvenCanonicalRankwiseTrajectoryGluingData
    (K radius : Nat) : Type where
  glueCount : Nat
  halfAmplitude : Nat → Nat → Nat → Nat → Q'
  factorization : ∀ left right,
    adjacentEvenReachableFixedInterfaceMatrix K radius left right ≈
      rankAwareSharedGlueKernel
        (adjacentEvenCanonicalFixedIncidenceGramRep K radius)
        halfAmplitude
        (adjacentEvenFixedIncidenceMiddleCount K radius)
        glueCount left right

/-! ## 2. Mechanical transport to every current positivity target -/

def AdjacentEvenCanonicalRankwiseTrajectoryGluingData.toFeatureData
    {K radius : Nat}
    (data : AdjacentEvenCanonicalRankwiseTrajectoryGluingData K radius) :
    AdjacentEvenReachableFeatureTrajectoryGluingData K radius where
  middleCount := adjacentEvenFixedIncidenceMiddleCount K radius
  middleField := adjacentEvenFixedIncidenceMiddleField K radius
  middleField_le := adjacentEvenFixedIncidenceMiddleField_le K radius
  glueCount := data.glueCount
  halfAmplitude := data.halfAmplitude
  factorization := by
    intro left right
    simpa [adjacentEvenCanonicalFixedIncidenceGramRep] using
      data.factorization left right

def AdjacentEvenCanonicalRankwiseTrajectoryGluingData.toReachableGramRep
    {K radius : Nat}
    (data : AdjacentEvenCanonicalRankwiseTrajectoryGluingData K radius) :
    AdjacentEvenReachableFixedInterfaceGramWitness K radius :=
  data.toFeatureData.toGramRep

def AdjacentEvenCanonicalRankwiseTrajectoryGluingData.toPhysicalGramRep
    {K radius : Nat}
    (data : AdjacentEvenCanonicalRankwiseTrajectoryGluingData K radius) :
    AdjacentEvenPhysicalAnchorGramWitness K radius :=
  adjacentEvenPhysicalAnchorGramWitness_of_reachable
    K radius data.toReachableGramRep

theorem AdjacentEvenCanonicalRankwiseTrajectoryGluingData.toPhysicalPSD
    {K radius : Nat}
    (data : AdjacentEvenCanonicalRankwiseTrajectoryGluingData K radius) :
    AdjacentEvenPhysicalAnchorPSD K radius :=
  adjacentEvenPhysicalAnchorPSD_of_reachable
    K radius data.toReachableGramRep

theorem AdjacentEvenCanonicalRankwiseTrajectoryGluingData.toReachableScaledPSD
    {K radius : Nat}
    (data : AdjacentEvenCanonicalRankwiseTrajectoryGluingData K radius) :
    AdjacentEvenReachableScaledPSD K radius :=
  (adjacentEvenReachableScaledPSD_iff_physical K radius).mpr
    data.toPhysicalPSD

#print axioms AdjacentEvenCanonicalRankwiseTrajectoryGluingData.toFeatureData
#print axioms AdjacentEvenCanonicalRankwiseTrajectoryGluingData.toReachableGramRep
#print axioms AdjacentEvenCanonicalRankwiseTrajectoryGluingData.toPhysicalGramRep
#print axioms AdjacentEvenCanonicalRankwiseTrajectoryGluingData.toPhysicalPSD
#print axioms AdjacentEvenCanonicalRankwiseTrajectoryGluingData.toReachableScaledPSD

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCanonicalTrajectoryGluingReduction
