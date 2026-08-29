/-
# Constant repair into one positive connected channel

At a fixed finite corrected slab, one executable good source is enough to
inhabit the weighted physical-repair interface.  Send every connected source
to that good target.  The repair ratio is the capped minimum, over the finite
source carrier, of

`targetWeight / sourceWeight`.

Positive coupling makes every denominator and the target numerator strictly
positive.  The finite minimum is therefore positive and at most one, and its
defining lower bound gives the required weight comparison source by source.
The complete source-carrier length bounds the fiber of the constant repair.

This construction is deliberately fixed-datum and non-uniform: its minimum
may shrink and its congestion may grow with cutoff or volume.  Its purpose is
to prove that the repair compiler is constructively inhabited as soon as one
good channel exists, and to isolate the uniform frontier in those two explicit
quantities.

Constructive contract: finite lists, positive `Q'` division, and explicit
witnesses only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableCanonicalGoodSourceRouting
import YMGap.Continuum.CompactDualSlabObservableGoodSourceRepairContraction

namespace YMGap.Continuum.CompactDualSlabObservableConstantGoodSourceRepair

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.CompactDualSlabObservableCanonicalGoodSourceRouting
open YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
open YMGap.Continuum.CompactDualSlabObservableGoodSourceRepairContraction
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabRetainedContraction

/-! ## 1. The finite weight-ratio floor -/

/-- Weight ratio associated to the constant arrow from `source` to one fixed
good target. -/
def slabObservablePairedConnectedConstantRepairRatio
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    (target : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) : Q' :=
  Q'.divPos
    (slabObservableTwoReplicaPairWeight D target.1.1)
    (slabObservableTwoReplicaPairWeight D source.1)
    (slabObservablePairedConnectedStrandSourceWeight_pos_of_coupling_pos
      D hcoupling rootFaceId targetFaceId source)

theorem slabObservablePairedConnectedConstantRepairRatio_pos
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    (target : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    (0 : Q') < slabObservablePairedConnectedConstantRepairRatio
      D hcoupling rootFaceId targetFaceId target source :=
  Q'.divPos_pos _ _ _
    (slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
      D hcoupling target.1.1)

/-- Capped minimum of the exact constant-repair ratios on the complete finite
connected source carrier. -/
def slabObservablePairedConnectedConstantRepairLambda
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    (target : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB) : Q' :=
  listPositiveMinOne
    (slabObservablePairedConnectedConstantRepairRatio
      D hcoupling rootFaceId targetFaceId target)
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId)

theorem slabObservablePairedConnectedConstantRepairLambda_pos
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    (target : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB) :
    (0 : Q') < slabObservablePairedConnectedConstantRepairLambda
      D hcoupling rootFaceId targetFaceId target := by
  unfold slabObservablePairedConnectedConstantRepairLambda
  apply listPositiveMinOne_pos
  intro source _
  exact slabObservablePairedConnectedConstantRepairRatio_pos
    D hcoupling rootFaceId targetFaceId target source

private theorem listPositiveMinOne_le_one_local
    {A : Type} (value : A → Q') : ∀ items : List A,
    listPositiveMinOne value items ≤ (1 : Q')
  | [] => Q'.le_refl' 1
  | _ :: rest =>
      Q'.le_trans' _ _ _ (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one_local value rest)

theorem slabObservablePairedConnectedConstantRepairLambda_le_one
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    (target : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB) :
    slabObservablePairedConnectedConstantRepairLambda
        D hcoupling rootFaceId targetFaceId target ≤ (1 : Q') := by
  unfold slabObservablePairedConnectedConstantRepairLambda
  exact listPositiveMinOne_le_one_local _ _

/-! ## 2. The constant repair certificate -/

def slabObservablePairedConnectedConstantRepairCongestion
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Nat :=
  (slabObservablePairedConnectedStrandSources
    D rootFaceId targetFaceId).length

/-- Every fixed finite good target induces an explicit weighted repair of the
complete connected source carrier. -/
def slabObservablePairedConnectedConstantGoodSourceRepair
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    (target : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB) :
    SlabObservablePairedConnectedGoodSourceRepair
      D rootFaceId targetFaceId goodB
        (slabObservablePairedConnectedConstantRepairLambda
          D hcoupling rootFaceId targetFaceId target)
        (slabObservablePairedConnectedConstantRepairCongestion
          D rootFaceId targetFaceId) where
  lambda_pos := slabObservablePairedConnectedConstantRepairLambda_pos
    D hcoupling rootFaceId targetFaceId target
  lambda_le_one := slabObservablePairedConnectedConstantRepairLambda_le_one
    D hcoupling rootFaceId targetFaceId target
  repair := fun _ => target
  repair_weight_floor := by
    intro source
    have hsourcePos :=
      slabObservablePairedConnectedStrandSourceWeight_pos_of_coupling_pos
        D hcoupling rootFaceId targetFaceId source
    have hfloor :
        slabObservablePairedConnectedConstantRepairLambda
            D hcoupling rootFaceId targetFaceId target ≤
          slabObservablePairedConnectedConstantRepairRatio
            D hcoupling rootFaceId targetFaceId target source := by
      unfold slabObservablePairedConnectedConstantRepairLambda
      exact listPositiveMinOne_le_of_mem _ _ source
        (List.mem_attach _ source)
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hfloor
      (Q'.le_of_lt hsourcePos)
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.divPos_mul_eqv
        (slabObservableTwoReplicaPairWeight D target.1.1)
        (slabObservableTwoReplicaPairWeight D source.1)
        hsourcePos))
  repair_fiber_count_le := by
    intro targetSource
    unfold selectedTargetFiber
      slabObservablePairedConnectedConstantRepairCongestion
    exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_succ _)

/-! ## 3. Canonical and concrete inhabitants -/

/-- One positive channel supplies the fixed good target required by the
constant repair. -/
def slabObservablePairedConnectedCanonicalConstantGoodSourceRepair
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) :
    SlabObservablePairedConnectedGoodSourceRepair
      D rootFaceId targetFaceId
        (slabObservablePairedConnectedCanonicalGoodB
          D rootFaceId targetFaceId)
        (slabObservablePairedConnectedConstantRepairLambda
          D hcoupling rootFaceId targetFaceId
            (canonicalGoodSourceOfPositiveChannel witness))
        (slabObservablePairedConnectedConstantRepairCongestion
          D rootFaceId targetFaceId) :=
  slabObservablePairedConnectedConstantGoodSourceRepair
    D hcoupling rootFaceId targetFaceId
      (canonicalGoodSourceOfPositiveChannel witness)

/-- The existing reflected-bent positive channel therefore inhabits the full
physical-repair interface, not only the direct fixed-datum density quotient. -/
def reflectedBentCanonicalConstantGoodSourceRepair :=
  slabObservablePairedConnectedCanonicalConstantGoodSourceRepair
    reflectedBentPhysicalData reflectedBentPhysicalData_coupling_pos
      reflectedBentRootFaceId reflectedBentTargetFaceId
        reflectedBentPositiveChannelWitness

/-- Constant physical repair followed by the canonical same-label SU(2)
routing reaches the retained face-contraction object. -/
def slabObservablePairedConnectedCanonicalConstantRepairRetainedContraction
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) :
    SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId :=
  (slabObservablePairedConnectedCanonicalConstantGoodSourceRepair
    D hcoupling rootFaceId targetFaceId witness).toRetainedContraction
      (slabObservablePairedConnectedCanonicalGoodRouting
        D rootFaceId targetFaceId htarget)

/-- The reflected-bent datum inhabits the entire factored path
`constant physical repair -> canonical row routing -> retained contraction`. -/
def reflectedBentCanonicalConstantRepairRetainedContraction :
    SlabObservablePairedSplitRetainedContraction
      reflectedBentPhysicalData reflectedBentRootFaceId
        reflectedBentTargetFaceId :=
  slabObservablePairedConnectedCanonicalConstantRepairRetainedContraction
    reflectedBentPhysicalData reflectedBentPhysicalData_coupling_pos
      reflectedBentRootFaceId reflectedBentTargetFaceId
        reflectedBentTargetFaceId_physical reflectedBentPositiveChannelWitness

#print axioms slabObservablePairedConnectedConstantRepairRatio_pos
#print axioms slabObservablePairedConnectedConstantRepairLambda_pos
#print axioms slabObservablePairedConnectedConstantRepairLambda_le_one
#print axioms slabObservablePairedConnectedConstantGoodSourceRepair
#print axioms slabObservablePairedConnectedCanonicalConstantGoodSourceRepair
#print axioms reflectedBentCanonicalConstantGoodSourceRepair
#print axioms slabObservablePairedConnectedCanonicalConstantRepairRetainedContraction
#print axioms reflectedBentCanonicalConstantRepairRetainedContraction

end YMGap.Continuum.CompactDualSlabObservableConstantGoodSourceRepair
