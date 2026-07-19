/-
# Rank-aware shared-glue transport for adjacent-even trajectories

The production fixed-face kernel already has a constructive Gram
representation.  A literal trajectory gluing may nevertheless have to retain
both a shared gluing coordinate and the rank of that fixed-face Gram: the
half-trajectory amplitude can depend on the local Gram feature being carried
through the cut.

This file supplies the purely algebraic transport needed for that situation.
The old fixed-face weights are repeated over the finite glue carrier but are
never changed, signed, divided, or square-rooted.  The pair `(rank, glue)` is
flattened constructively with the existing finite-sum reindexing theorem.

The final structure is honest residual data.  It records the exact entrywise
trajectory factorization required to apply the transport, but no inhabitant is
asserted here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointTrajectoryNormalForm

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFeatureTrajectoryGluing

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.HeatKernelGramSOS
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointTrajectoryNormalForm
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic rank-aware shared-glue Gram transport -/

/-- The one-sided feature obtained by summing middle coordinates of one fixed
Gram rank.  The amplitude may depend on the rank and on an additional shared
gluing coordinate:

`rank -> glue -> configuration -> middle -> amplitude`.
-/
def rankAwareSharedGlueFeature
    (feature : Nat → Nat → Q')
    (amplitude : Nat → Nat → Nat → Nat → Q')
    (middleCount rank glue configuration : Nat) : Q' :=
  finSum (fun middle =>
    amplitude rank glue configuration middle * feature rank middle)
    middleCount

/-- The kernel produced by pairing the same rank-aware half feature on both
sides and then summing over the shared glue coordinate and the original Gram
rank.  The original nonnegative weight `rep.d rank` is retained literally. -/
def rankAwareSharedGlueKernel
    {kernel : Nat → Nat → Q'} (rep : GramRep kernel)
    (amplitude : Nat → Nat → Nat → Nat → Q')
    (middleCount glueCount left right : Nat) : Q' :=
  finSum (fun rank =>
    finSum (fun glue =>
      rep.d rank *
        (rankAwareSharedGlueFeature rep.v amplitude middleCount
            rank glue left *
          rankAwareSharedGlueFeature rep.v amplitude middleCount
            rank glue right))
      glueCount)
    rep.r

/-- A rank-aware shared-glue contraction is constructively Gram.  Its flattened
rank is `glueCount * rep.r`; the packed coordinate `(rank, glue)` carries the
unchanged weight `rep.d rank` and the corresponding one-sided transformed
feature.  No positivity condition is imposed on the half amplitudes because
they occur as the same coordinate vector on both sides. -/
def rankAwareSharedGlueGramRep
    {kernel : Nat → Nat → Q'} (rep : GramRep kernel)
    (amplitude : Nat → Nat → Nat → Nat → Q')
    (middleCount glueCount : Nat) :
    GramRep (rankAwareSharedGlueKernel rep amplitude
      middleCount glueCount) where
  r := glueCount * rep.r
  d := fun packed => rep.d (packed / glueCount)
  hd := fun packed => rep.hd (packed / glueCount)
  v := fun packed configuration =>
    rankAwareSharedGlueFeature rep.v amplitude middleCount
      (packed / glueCount) (packed % glueCount) configuration
  hM := by
    intro left right
    unfold rankAwareSharedGlueKernel
    exact Q'.eqv_symm
      (finSum_flatten
        (fun rank glue =>
          rep.d rank *
            (rankAwareSharedGlueFeature rep.v amplitude middleCount
                rank glue left *
              rankAwareSharedGlueFeature rep.v amplitude middleCount
                rank glue right))
        glueCount rep.r)

/-! ## 2. Adjacent-even production residual and adapter -/

/-- Sufficient constructive data for the reachable endpoint kernel when a
two-sided trajectory gluing must retain both a common middle field and the
local feature rank of the production fixed-face Gram.

Compared with `AdjacentEvenReachableCommonMiddleData`, the half amplitude has
two additional leading indices: the fixed-face Gram rank and a finite shared
glue coordinate.  This strictly contains the rank-independent one-glue case
while preserving the already proved production weights exactly. -/
structure AdjacentEvenReachableFeatureTrajectoryGluingData
    (K radius : Nat) : Type where
  /-- Number of fixed-face channel fields in the symbolic middle carrier. -/
  middleCount : Nat
  /-- Fixed-face channel field represented by each middle index. -/
  middleField : Nat → FixedFaceChannelField
  /-- Every middle channel lies in the production auxiliary window. -/
  middleField_le : ∀ middle id link,
    middleField middle id link ≤ linkAuxiliaryCutoff K
  /-- Number of shared trajectory-gluing coordinates. -/
  glueCount : Nat
  /-- Rank-aware one-sided amplitude:
  `rank -> glue -> physical configuration -> middle -> amplitude`. -/
  halfAmplitude : Nat → Nat → Nat → Nat → Q'
  /-- Exact factorization of the reachable endpoint matrix through the
  rank-aware shared-glue features of the production fixed-face Gram. -/
  factorization : ∀ left right,
    adjacentEvenReachableFixedInterfaceMatrix K radius left right ≈
      rankAwareSharedGlueKernel
        (adjacentEvenProductionDependentFixedFaceChannelGramRep
          K radius middleField middleField_le)
        halfAmplitude middleCount glueCount left right

/-- Once rank-aware, weight-preserving trajectory-gluing data are supplied,
the reachable adjacent-even endpoint matrix has an explicit constructive Gram
representation. -/
def AdjacentEvenReachableFeatureTrajectoryGluingData.toGramRep
    {K radius : Nat}
    (data : AdjacentEvenReachableFeatureTrajectoryGluingData K radius) :
    AdjacentEvenReachableFixedInterfaceGramWitness K radius :=
  gramRep_of_eqv
    (rankAwareSharedGlueGramRep
      (adjacentEvenProductionDependentFixedFaceChannelGramRep
        K radius data.middleField data.middleField_le)
      data.halfAmplitude data.middleCount data.glueCount)
    data.factorization

#print axioms rankAwareSharedGlueGramRep
#print axioms AdjacentEvenReachableFeatureTrajectoryGluingData.toGramRep

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFeatureTrajectoryGluing
