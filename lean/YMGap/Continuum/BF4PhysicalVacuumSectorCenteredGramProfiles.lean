/-
# Profile factorization of the BF4 vacuum-sector centered Gram

The exact sector-centered physical Gram has one literal Tonelli majorant.
This file splits that majorant at the genuine fixed-time boundary into two
independently meaningful deviations:

* the total centered target profile seen from one boundary channel; and
* the total centered boundary profile seen from one source state.

A target profile rate times a source profile rate therefore bounds the
whole physical row.  A constructively cofinal family of such bounds compiles
directly to the completed same-object vacuum-sector gap.  No profile bound
is assumed to exist here; the next module will normalize both profiles as
conditional-probability distances.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProfiles

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. The two literal boundary profiles -/

/-- Total absolute component-centered target profile visible through one
fixed-time boundary channel. -/
def centralPhysicalFiniteVacuumSectorTargetProfileDeviation
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      Q'.abs
        (centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
          w hw cutoff half target boundary))
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)

/-- Total absolute component-centered boundary profile visible from one
source state, including the exact channel weight and target-channel total. -/
def centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half source : Nat) : Q' :=
  listQSum
    (fun boundary =>
      Q'.abs
          (centralPhysicalFiniteVacuumSectorGramWeight
              w hw cutoff half boundary *
            centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
              w hw cutoff half source boundary) *
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary)
    (centralBoundaryChannels cutoff half)

/-! ## 2. Exact majorant factorization -/

/-- A uniform target-profile bound factors the actual centered-Gram row
majorant into the same scalar times the source-boundary deviation. -/
theorem centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_profile_mul_sourceDeviation
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half source : Nat} (targetRate : Q')
    (htarget :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels cutoff half →
          centralPhysicalFiniteVacuumSectorTargetProfileDeviation
              w hw cutoff half boundary ≤
            targetRate *
              centralPhysicalFiniteVacuumSectorChannelTotal
                w hw cutoff half boundary) :
    centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
        w hw cutoff half source ≤
      targetRate *
        centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation
          w hw cutoff half source := by
  unfold centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
    finiteWeightedGramCenteredRowMajorant
    centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation
  refine Q'.le_trans' _ _ _
    (listQSum_mono _ _
      (centralBoundaryChannels cutoff half)
      (fun boundary hboundary => by
        have h := htarget boundary hboundary
        unfold centralPhysicalFiniteVacuumSectorTargetProfileDeviation at h
        exact Q'.mul_le_mul_of_nonneg_left _ _ _ h
          (Q'.abs_nonneg
            (centralPhysicalFiniteVacuumSectorGramWeight
                w hw cutoff half boundary *
              centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
                w hw cutoff half source boundary)))) ?_
  refine Q'.le_of_eqv
    (Q'.eqv_trans _
      (listQSum
        (fun boundary =>
          targetRate *
            (Q'.abs
                (centralPhysicalFiniteVacuumSectorGramWeight
                    w hw cutoff half boundary *
                  centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
                    w hw cutoff half source boundary) *
              centralPhysicalFiniteVacuumSectorChannelTotal
                w hw cutoff half boundary))
        (centralBoundaryChannels cutoff half)) _ ?_ ?_)
  · apply listQSum_congr
    intro boundary
    q_ring
  exact listQSum_mul_left
    targetRate
    (fun boundary =>
      Q'.abs
          (centralPhysicalFiniteVacuumSectorGramWeight
              w hw cutoff half boundary *
            centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
              w hw cutoff half source boundary) *
        centralPhysicalFiniteVacuumSectorChannelTotal
          w hw cutoff half boundary)
    (centralBoundaryChannels cutoff half)

/-- The product of a target-profile rate and a source-profile rate bounds
the literal actual Gram majorant by the unconditioned stationary source
weight. -/
theorem centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_rateProduct_mul_weight
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half source : Nat} {targetRate sourceRate : Q'}
    (targetRate_nonnegative : (0 : Q') ≤ targetRate)
    (htarget :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels cutoff half →
          centralPhysicalFiniteVacuumSectorTargetProfileDeviation
              w hw cutoff half boundary ≤
            targetRate *
              centralPhysicalFiniteVacuumSectorChannelTotal
                w hw cutoff half boundary)
    (hsource :
      centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation
          w hw cutoff half source ≤
        sourceRate *
          centralPhysicalFiniteWeight w hw cutoff half source) :
    centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant
        w hw cutoff half source ≤
      (targetRate * sourceRate) *
        centralPhysicalFiniteWeight w hw cutoff half source := by
  refine Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_profile_mul_sourceDeviation
      targetRate htarget) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hsource targetRate_nonnegative) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv targetRate sourceRate
        (centralPhysicalFiniteWeight w hw cutoff half source)))

/-! ## 3. Cofinal two-profile compiler -/

/-- A constructively cofinal family of target and source profile bounds whose
product is uniformly strict.  The fields are the precise remaining finite
analytic obligations before posterior normalization. -/
structure FixedNomeCofinalVacuumSectorCenteredGramProfileBounds
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat)
    (targetRate sourceRate : Q') : Type 1 where
  targetRate_nonnegative : (0 : Q') ≤ targetRate
  sourceRate_nonnegative : (0 : Q') ≤ sourceRate
  rateProduct_lt_one : targetRate * sourceRate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  targetProfileBound : ∀ base threshold boundary,
    boundary ∈ centralBoundaryChannels (anchor base threshold) half →
      centralPhysicalFiniteVacuumSectorTargetProfileDeviation
          w hw (anchor base threshold) half boundary ≤
        targetRate *
          centralPhysicalFiniteVacuumSectorChannelTotal
            w hw (anchor base threshold) half boundary
  sourceProfileBound : ∀ base threshold source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w hw (anchor base threshold) half →
      centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation
          w hw (anchor base threshold) half source ≤
        sourceRate *
          centralPhysicalFiniteWeight
            w hw (anchor base threshold) half source

namespace FixedNomeCofinalVacuumSectorCenteredGramProfileBounds

/-- Two cofinal profile estimates inhabit the actual centered-Gram
majorant compiler at their product rate. -/
def toCenteredGramMajorant
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    {targetRate sourceRate : Q'}
    (family : FixedNomeCofinalVacuumSectorCenteredGramProfileBounds
      w hw half targetRate sourceRate) :
    FixedNomeCofinalVacuumSectorCenteredGramMajorant
      w hw half (targetRate * sourceRate) where
  rate_nonnegative := Q'.mul_nonneg _ _
    family.targetRate_nonnegative family.sourceRate_nonnegative
  rate_lt_one := family.rateProduct_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  majorantBound := by
    intro base threshold source hsource
    exact
      centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_rateProduct_mul_weight
        family.targetRate_nonnegative
        (family.targetProfileBound base threshold)
        (family.sourceProfileBound base threshold source hsource)

/-- The two cofinal physical boundary-profile estimates reach the completed
same-object vacuum-sector strict gap at their product rate. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    {targetRate sourceRate : Q'}
    (family : FixedNomeCofinalVacuumSectorCenteredGramProfileBounds
      w hw half targetRate sourceRate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half (targetRate * sourceRate) :=
  family.toCenteredGramMajorant.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorCenteredGramProfileBounds

end YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProfiles

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProfiles.centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_profile_mul_sourceDeviation
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProfiles.centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_rateProduct_mul_weight
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProfiles.FixedNomeCofinalVacuumSectorCenteredGramProfileBounds.toCenteredGramMajorant
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramProfiles.FixedNomeCofinalVacuumSectorCenteredGramProfileBounds.toVacuumSectorCenteredStrictGap
