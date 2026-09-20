/-
# Canonical conditioned-entry bridge

The indexed canonical one-step is a component-conditioned density.  After
the target component weight is restored, its entry is exactly the physical
conditional transition on the same finite carrier.  This is the narrow
forward/backward bridge needed before any finite row estimate can be read as
a statement about the actual physical Markov object.

This file proves only the finite entry identity.  It constructs no strict
contraction, cofinal family, thermodynamic limit, continuum theory, or Clay
mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalWeightedEntryBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower
open YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.ofInt, Q'.ofNat, Q'.neg,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try simp;
             try omega;
             try ac_rfl))

/-! ## 1. The weighted canonical entry is the physical transition -/

/-- Restoring the target component mass to the canonical conditioned
one-step density recovers the literal physical conditional transition. -/
theorem canonicalConditionedWeightedEntry_eqv_conditionalKernel
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half target *
        centralPhysicalFiniteVacuumSectorConditionedTimeStep
          w hw cutoff half
          (canonicalFullDensityOneStepIndex w hw cutoff half)
          source target ≈
      centralPhysicalConditionalKernel w hw cutoff half
        (centralPhysicalFiniteStateAt w hw cutoff half source)
        (centralPhysicalFiniteStateAt w hw cutoff half target) := by
  have hstep :=
    finiteComponentConditionedKernelExtension_eqv_of_mem
      (sector := centralPhysicalFiniteVacuumSectorIndices
        w hw cutoff half)
      (mass := centralPhysicalFiniteVacuumSectorMass
        w hw cutoff half)
      (fullKernel := canonicalFullDensityOneStepIndex
        w hw cutoff half)
      hsource htarget
  have hmassWeight :=
    finiteCarrierMassNormalizedWeight_mul_mass_eqv_weight
      (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorWeightSum_pos
        w hw cutoff half)
      (centralPhysicalFiniteWeight w hw cutoff half)
      target
  have htargetState :=
    centralPhysicalFiniteStateAt_mem_positive
      w hw cutoff half
      (centralPhysicalFiniteVacuumSectorIndex_lt
        w hw cutoff half htarget)
  have htargetDensity :=
    targetMarginal_mul_density_eq_conditional
      (w := w) (hw := hw) (K := cutoff) (half := half)
      (source := centralPhysicalFiniteStateAt
        w hw cutoff half source)
      (target := centralPhysicalFiniteStateAt
        w hw cutoff half target)
      htargetState
  refine Q'.eqv_trans _
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half target *
      (centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
        canonicalFullDensityOneStepIndex
          w hw cutoff half source target)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ hstep
  refine Q'.eqv_trans _
    ((centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half target *
      centralPhysicalFiniteVacuumSectorMass w hw cutoff half) *
      canonicalFullDensityOneStepIndex w hw cutoff half source target) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv _ _ _)
  refine Q'.eqv_trans _
    (centralPhysicalFiniteWeight w hw cutoff half target *
      canonicalFullDensityOneStepIndex w hw cutoff half source target) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hmassWeight
  unfold canonicalFullDensityOneStepIndex
    centralPhysicalFiniteFullDensity
    centralPhysicalFiniteWeight
  exact htargetDensity

/-! ## 2. The centered-entry residual is the Markov residual -/

/-- The weighted centered entry of the canonical conditioned density is the
physical conditional transition minus the conditioned stationary weight.
This is an entrywise identity; no norm estimate is hidden in it. -/
theorem canonicalConditionedCenteredTransition_eqv_conditionalKernel_sub_weight
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    finiteWeightedCenteredTransition
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorConditionedTimeStep
          w hw cutoff half
          (canonicalFullDensityOneStepIndex w hw cutoff half))
        source target ≈
      centralPhysicalConditionalKernel w hw cutoff half
        (centralPhysicalFiniteStateAt w hw cutoff half source)
        (centralPhysicalFiniteStateAt w hw cutoff half target) +
        (-(centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half target)) := by
  unfold finiteWeightedCenteredTransition finiteCenteredDensity
  refine Q'.eqv_trans _
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half target *
      centralPhysicalFiniteVacuumSectorConditionedTimeStep
        w hw cutoff half
        (canonicalFullDensityOneStepIndex w hw cutoff half)
        source target +
      (-(centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w hw cutoff half target))) _ ?_ ?_
  · q_ring
  exact Q'.add_eqv_congr_right _ _ _
    (canonicalConditionedWeightedEntry_eqv_conditionalKernel
      hsource htarget)

end YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalWeightedEntryBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalWeightedEntryBridge.canonicalConditionedWeightedEntry_eqv_conditionalKernel
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalWeightedEntryBridge.canonicalConditionedCenteredTransition_eqv_conditionalKernel_sub_weight
