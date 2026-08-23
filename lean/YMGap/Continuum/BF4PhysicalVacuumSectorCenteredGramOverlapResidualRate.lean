/-
# One exact residual-rate scalar for BF4 vacuum-sector posterior mixing

The finite target and source overlap floors can be contracted one step
further.  Their support-compatible `L1` rates are

    targetRate_K = 2 * (1 - targetFloor_K),
    sourceRate_K = 2 * (1 - sourceFloor_K),

and the centered Gram consumes only their product.  This module defines that
single exact finite scalar, proves the actual centered-Gram row majorant at
that scalar, and shows that a constructively cofinal upper bound `rate < 1`
compiles to the completed same-object vacuum-sector gap.

Thus the remaining finite analytic obligation is no longer a family of
pointwise posterior inequalities or even two separate floor bounds.  It is a
uniform cofinal upper bound below one for one explicitly defined rational
sequence.  No such bound is inhabited here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProfiles
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite residual rates -/

def centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  (2 : Q') *
    (1 +
      (-centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor
        w hw cutoff half))

def centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  (2 : Q') *
    (1 +
      (-centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor
        w hw cutoff half))

/-- The one scalar consumed by the centered-Gram row estimate. -/
def centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
      w hw cutoff half *
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
      w hw cutoff half

theorem centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.sub_nonneg_of_le
      (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_le_one
        w hw cutoff half))

theorem centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.sub_nonneg_of_le
      (centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_le_one
        w hw cutoff half))

theorem centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
  exact Q'.mul_nonneg _ _
    (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate_nonnegative
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate_nonnegative
      w hw cutoff half)

/-! ## 2. The exact finite scalar bounds both posterior layers -/

theorem centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_overlapResidualRate
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels cutoff half)
    (channelTotal_pos :
      (0 : Q') <
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary) :
    centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1
        w hw cutoff half boundary channelTotal_pos ≤
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
  exact centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_of_overlap
    channelTotal_pos
    (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_le
      hboundary channelTotal_pos)

theorem centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_overlapResidualRate
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1
        w hw cutoff half source hsource ≤
      centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
  exact centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_of_overlap
    hsource
    (centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_le
      hsource)

theorem centralPhysicalFiniteVacuumSectorTargetProfileDeviation_le_overlapResidualRate
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels cutoff half) :
    centralPhysicalFiniteVacuumSectorTargetProfileDeviation
        w hw cutoff half boundary ≤
      centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
          w hw cutoff half *
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary := by
  exact centralPhysicalFiniteVacuumSectorTargetProfileDeviation_le_of_posteriorL1
    (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate_nonnegative
      w hw cutoff half)
    (fun channelTotal_pos =>
      centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_overlapResidualRate
        hboundary channelTotal_pos)

theorem centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_le_overlapResidualRate
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation
        w hw cutoff half source ≤
      centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
          w hw cutoff half *
        centralPhysicalFiniteWeight w hw cutoff half source := by
  exact centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_le_of_posteriorL1
    hsource
    (centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_overlapResidualRate
      hsource)

/-- The one exact finite residual-rate scalar bounds the literal actual
centered-Gram row majorant. -/
theorem centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_overlapResidualRate_mul_weight
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
        w hw cutoff half source ≤
      centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
          w hw cutoff half *
        centralPhysicalFiniteWeight w hw cutoff half source := by
  unfold centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
  exact
    centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_rateProduct_mul_weight
      (centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate_nonnegative
        w hw cutoff half)
      (fun boundary hboundary =>
        centralPhysicalFiniteVacuumSectorTargetProfileDeviation_le_overlapResidualRate
          hboundary)
      (centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_le_overlapResidualRate
        hsource)

/-! ## 3. One cofinal scalar bound compiles to the completed gap -/

/-- A constructively cofinal upper bound below one for the exact finite
posterior-overlap residual-rate sequence. -/
structure FixedNomeCofinalVacuumSectorPosteriorOverlapResidualRateBound
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  residualRateBound : ∀ base threshold,
    centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
        w hw (anchor base threshold) half ≤ rate

namespace FixedNomeCofinalVacuumSectorPosteriorOverlapResidualRateBound

/-- A uniform scalar residual-rate bound produces the actual centered-Gram
majorant certificate. -/
def toCenteredGramMajorant
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family :
      FixedNomeCofinalVacuumSectorPosteriorOverlapResidualRateBound
        w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredGramMajorant
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  majorantBound := by
    intro base threshold source hsource
    refine Q'.le_trans' _ _ _
      (centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_overlapResidualRate_mul_weight
        hsource) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (family.residualRateBound base threshold)
      (Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource))

/-- The sole cofinal scalar estimate reaches the completed same-object
vacuum-sector strict gap. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family :
      FixedNomeCofinalVacuumSectorPosteriorOverlapResidualRateBound
        w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  family.toCenteredGramMajorant.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorPosteriorOverlapResidualRateBound

end YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate.centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate.centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_overlapResidualRate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate.centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_overlapResidualRate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate.centralPhysicalFiniteVacuumSectorTargetProfileDeviation_le_overlapResidualRate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate.centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_le_overlapResidualRate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate.centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_overlapResidualRate_mul_weight
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate.FixedNomeCofinalVacuumSectorPosteriorOverlapResidualRateBound.toVacuumSectorCenteredStrictGap
