/-
# Rebase accepted expanded states to an explicit heat coupling

The accepted physical and fine-intertwiner carriers depend on the cutoff and
slab geometry, but not on the heat coupling.  This module makes that fact a
typed map: an accepted entry or pair may be transported to a new nonnegative
coupling without changing any physical label or SU(2) fusion witness.

When the source datum has coupling one, the transported weight is exactly the
source weight multiplied by the new coupling to the total face-Casimir power.
Thus later connected-component estimates can apply the arbitrary-coupling
peeling telescope at a named comparison rate without hiding beta dependence
inside a carrier conversion.

Constructive contract: definitional carrier transport and exact rational
factorization only; no classical choice, proof hole, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
import YMGap.Continuum.CompactDualSlabExpandedEntryFaceWeight
import YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation

namespace YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedEntryFaceWeight
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local
    {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem mul_four_regroup_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-! ## 1. Coupling-independent carrier transport -/

/-- Replace only the heat coupling of a corrected slab datum. -/
def slabPhysicalDataAtCoupling
    (D : SlabPhysicalData) (coupling : Q')
    (hcoupling : (0 : Q') ≤ coupling) : SlabPhysicalData where
  coupling := coupling
  coupling_nonnegative := hcoupling
  cutoff := D.cutoff
  half := D.half

theorem slabPhysicalDataAtCoupling_extent
    (D : SlabPhysicalData) (coupling : Q')
    (hcoupling : (0 : Q') ≤ coupling) :
    (slabPhysicalDataAtCoupling D coupling hcoupling).extent = D.extent := rfl

/-- Transport one accepted expanded entry after changing only its coupling.
The physical labelling and complete fusion assignment are definitionally
preserved. -/
def slabExpandedFineSourceEntryAtCoupling
    (D : SlabPhysicalData) (coupling : Q')
    (hcoupling : (0 : Q') ≤ coupling)
    (entry : SlabExpandedFineSourceEntry D) :
    SlabExpandedFineSourceEntry
      (slabPhysicalDataAtCoupling D coupling hcoupling) :=
  ⟨entry.1, by
    apply mem_slabExpandedFineSources_iff.mpr
    have hentry := mem_slabExpandedFineSources_iff.mp entry.2
    constructor
    · simpa only [slabPhysicalDataAtCoupling,
        SlabPhysicalData.physicalLabellings,
        SlabPhysicalData.faceEdges,
        SlabPhysicalData.extent] using hentry.1
    · simpa only [slabPhysicalDataAtCoupling,
        slabFineFusionWitnesses,
        SlabPhysicalData.extent] using hentry.2⟩

theorem slabExpandedFineSourceEntryAtCoupling_value
    (D : SlabPhysicalData) (coupling : Q')
    (hcoupling : (0 : Q') ≤ coupling)
    (entry : SlabExpandedFineSourceEntry D) :
    (slabExpandedFineSourceEntryAtCoupling
      D coupling hcoupling entry).1 = entry.1 := rfl

theorem slabExpandedFineSourceEntryAtCoupling_injective
    (D : SlabPhysicalData) (coupling : Q')
    (hcoupling : (0 : Q') ≤ coupling) :
    Function.Injective
      (slabExpandedFineSourceEntryAtCoupling D coupling hcoupling) := by
  intro left right heq
  apply Subtype.ext
  exact congrArg Subtype.val heq

/-- Transport both replicas of an accepted state to the same new coupling. -/
def slabAcceptedTwoReplicaStateAtCoupling
    (D : SlabPhysicalData) (coupling : Q')
    (hcoupling : (0 : Q') ≤ coupling)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabAcceptedTwoReplicaState
      (slabPhysicalDataAtCoupling D coupling hcoupling) :=
  (slabExpandedFineSourceEntryAtCoupling
      D coupling hcoupling state.1,
    slabExpandedFineSourceEntryAtCoupling
      D coupling hcoupling state.2)

theorem slabAcceptedTwoReplicaStateAtCoupling_injective
    (D : SlabPhysicalData) (coupling : Q')
    (hcoupling : (0 : Q') ≤ coupling) :
    Function.Injective
      (slabAcceptedTwoReplicaStateAtCoupling D coupling hcoupling) := by
  intro left right heq
  have hleft := congrArg Prod.fst heq
  have hright := congrArg Prod.snd heq
  exact Prod.ext
    (slabExpandedFineSourceEntryAtCoupling_injective
      D coupling hcoupling hleft)
    (slabExpandedFineSourceEntryAtCoupling_injective
      D coupling hcoupling hright)

/-! ## 2. Exact weight carried by the transport -/

/-- One transported entry from a unit-coupling source gains exactly the heat
power determined by its total face Casimir. -/
theorem slabExpandedFineSourceEntryAtCoupling_weight_eqv
    (D : SlabPhysicalData) (hunit : D.coupling = 1)
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (entry : SlabExpandedFineSourceEntry D) :
    slabExpandedFineEntryWeight
        (slabPhysicalDataAtCoupling D coupling hcoupling)
        (slabExpandedFineSourceEntryAtCoupling
          D coupling hcoupling entry) ≈
      qpow coupling
          (slabPhysicalCasimirExponent D.extent entry.1.1) *
        slabExpandedFineEntryWeight D entry := by
  have hphysical : entry.1.1 ∈ boundedEdgeLabellings D.cutoff
      (slabPhysicalFaceEdges D.extent) := by
    have hentry := (mem_slabExpandedFineSources_iff.mp entry.2).1
    simpa only [SlabPhysicalData.physicalLabellings,
      SlabPhysicalData.faceEdges] using hentry
  have htarget := slabExpandedFineEntryWeight_eqv_physicalFaceFactor
    (slabPhysicalDataAtCoupling D coupling hcoupling)
    (slabExpandedFineSourceEntryAtCoupling
      D coupling hcoupling entry)
  have hfactor :=
    slabParametricKPhysicalFaceFactor_eqv_power_mul_atOne
      coupling D.cutoff D.extent entry.1.1 hphysical
  have hsource := slabExpandedFineEntryWeight_eqv_physicalFaceFactor D entry
  rw [hunit] at hsource
  refine Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor
      coupling D.cutoff D.extent entry.1.1) _ ?_ ?_
  · simpa only [slabPhysicalDataAtCoupling,
      SlabPhysicalData.extent] using htarget
  · exact Q'.eqv_trans _ _ _ hfactor
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hsource))

/-- Total face Casimir carried by an accepted two-replica state. -/
def slabAcceptedTwoReplicaStateCasimirExponent
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) : Nat :=
  slabPhysicalCasimirExponent D.extent state.1.1.1 +
    slabPhysicalCasimirExponent D.extent state.2.1.1

/-- The pair transport combines the two exact entry identities into one
power whose exponent is the sum of both face Casimirs. -/
theorem slabAcceptedTwoReplicaStateAtCoupling_weight_eqv
    (D : SlabPhysicalData) (hunit : D.coupling = 1)
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (state : SlabAcceptedTwoReplicaState D) :
    slabAcceptedTwoReplicaStateWeight
        (slabPhysicalDataAtCoupling D coupling hcoupling)
        (slabAcceptedTwoReplicaStateAtCoupling
          D coupling hcoupling state) ≈
      qpow coupling
          (slabAcceptedTwoReplicaStateCasimirExponent D state) *
        slabAcceptedTwoReplicaStateWeight D state := by
  have hleft := slabExpandedFineSourceEntryAtCoupling_weight_eqv
    D hunit coupling hcoupling state.1
  have hright := slabExpandedFineSourceEntryAtCoupling_weight_eqv
    D hunit coupling hcoupling state.2
  unfold slabAcceptedTwoReplicaStateWeight
    slabAcceptedTwoReplicaStateAtCoupling
    slabAcceptedTwoReplicaStateCasimirExponent
  refine Q'.eqv_trans _
    ((qpow coupling
          (slabPhysicalCasimirExponent D.extent state.1.1.1) *
        slabExpandedFineEntryWeight D state.1) *
      (qpow coupling
          (slabPhysicalCasimirExponent D.extent state.2.1.1) *
        slabExpandedFineEntryWeight D state.2)) _
    (qmul_congr_local hleft hright) ?_
  refine Q'.eqv_trans _
    ((qpow coupling
          (slabPhysicalCasimirExponent D.extent state.1.1.1) *
        qpow coupling
          (slabPhysicalCasimirExponent D.extent state.2.1.1)) *
      (slabExpandedFineEntryWeight D state.1 *
        slabExpandedFineEntryWeight D state.2)) _
    (mul_four_regroup_local _ _ _ _) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (YMGap.Continuum.HeatKernelRGStep.qpow_add coupling
        (slabPhysicalCasimirExponent D.extent state.1.1.1)
        (slabPhysicalCasimirExponent D.extent state.2.1.1)))

#print axioms slabPhysicalDataAtCoupling
#print axioms slabExpandedFineSourceEntryAtCoupling
#print axioms slabExpandedFineSourceEntryAtCoupling_injective
#print axioms slabAcceptedTwoReplicaStateAtCoupling
#print axioms slabAcceptedTwoReplicaStateAtCoupling_injective
#print axioms slabExpandedFineSourceEntryAtCoupling_weight_eqv
#print axioms slabAcceptedTwoReplicaStateCasimirExponent
#print axioms slabAcceptedTwoReplicaStateAtCoupling_weight_eqv

end YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
