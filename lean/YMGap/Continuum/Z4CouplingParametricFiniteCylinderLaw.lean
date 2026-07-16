/-
# Exact finite cylinder laws at arbitrary nonnegative coupling

The physical spin-foam event numerator was already coupling-parametric, but
the normalized family law used by the strong-coupling cylinder construction
was exposed only at the fixed anchor.  The vacuum term gives a constructive
unit floor for the partition at every nonnegative coupling, so the normalized
finite law exists without any additional assumption.

Specializing this law to the anchor is proved equivalent to the existing
spin-summed compatible-family law.  We then put the coarse and refined
unit-cube events at two genuinely different couplings and expose the exact
activity-matched defect obtained from `w_coarse = 2*w_fine^4`.
-/

import YMGap.Continuum.Z4DyadicUnitCubeBlockCylinderIntertwining
import YMGap.Continuum.Z4SpinSummedCutoffEventBridge
import YMGap.Continuum.Z4UnitCubeBareCouplingShift

namespace YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockCylinderIntertwining
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCutoffEventBridge
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The vacuum-normalized law at arbitrary coupling -/

/-- The literal vacuum labelling gives a unit floor for every nonnegative
coupling, including cutoff zero. -/
theorem couplingKPhysicalPartition_one_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) :
    (1 : Q') ≤ parametricKPhysicalPartition coupling cutoff n := by
  unfold parametricKPhysicalPartition
  have hmember := listQSum_member_le
    (parametricKPhysicalTerm coupling cutoff n)
    (parametricKPhysicalTerm_nonnegative hcoupling cutoff n)
    (boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount n)))
    (zeroEdgeLabelling_mem_bounded cutoff n)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm
      (parametricKPhysicalTerm_zero_eqv_one
        coupling cutoff n))) hmember

theorem couplingKPhysicalPartition_pos
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) :
    (0 : Q') < parametricKPhysicalPartition coupling cutoff n :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (by decide)
    (couplingKPhysicalPartition_one_le hcoupling cutoff n)

/-- The exact finite probability of an arbitrary Boolean predicate of the
canonical connected-support family induced by a physical spin labelling. -/
def couplingKFamilyEventProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (parametricKEventNumerator coupling cutoff n
      (cutoffOneLiftedFamilyEvent n event))
    (parametricKPhysicalPartition coupling cutoff n)
    (couplingKPhysicalPartition_pos hcoupling cutoff n)

theorem couplingKFamilyEventProbability_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    (0 : Q') ≤
      couplingKFamilyEventProbability coupling hcoupling
        cutoff n event := by
  unfold couplingKFamilyEventProbability Q'.divPos
  exact Q'.mul_nonneg _ _
    (parametricKEventNumerator_nonnegative hcoupling cutoff n _)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (couplingKPhysicalPartition_pos hcoupling cutoff n)))

theorem couplingKFamilyEventProbability_le_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    couplingKFamilyEventProbability coupling hcoupling cutoff n event ≤
      (1 : Q') := by
  unfold couplingKFamilyEventProbability
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (parametricKEventNumerator_le_partition
      hcoupling cutoff n (cutoffOneLiftedFamilyEvent n event))
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (parametricKPhysicalPartition coupling cutoff n)))

/-- At the derived strong-coupling anchor the new physical-law presentation
is exactly the existing compatible-family law. -/
theorem couplingKFamilyEventProbability_anchor_eqv_compatible
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    couplingKFamilyEventProbability anchorCoupling (by decide)
        cutoff n event ≈
      parametricKCompatibleSupportEventProbability cutoff n event := by
  unfold couplingKFamilyEventProbability
    parametricKCompatibleSupportEventProbability
  exact
    YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder.divPos_eqv_congr
      (couplingKPhysicalPartition_pos (by decide) cutoff n)
      (parametricKCompatibleSupportGasPartition_pos cutoff n)
      (anchorParametricKEventNumerator_eqv_compatibleEventNumerator
        cutoff n event)
      (parametricKPhysicalPartition_eqv_compatibleSupportGas cutoff n)

/-! ## 2. Two-coupling coarse/refined block coordinates -/

def couplingKUnitCubeBlockCoarseProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) : Q' :=
  couplingKFamilyEventProbability coupling hcoupling cutoff volume
    (targetCylinderEvent 4 volume unitCubeBlockCylinderRoots
      unitCubeBlockCoarseOccurrencePredicate)

def couplingKUnitCubeBlockRefinedProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) : Q' :=
  couplingKFamilyEventProbability coupling hcoupling cutoff volume
    (targetCylinderEvent 4 volume unitCubeBlockCylinderRoots
      unitCubeBlockRefinedOccurrencePredicate)

theorem couplingKUnitCubeBlockCoarseProbability_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    (0 : Q') ≤ couplingKUnitCubeBlockCoarseProbability
      coupling hcoupling cutoff volume :=
  couplingKFamilyEventProbability_nonnegative
    coupling hcoupling cutoff volume _

theorem couplingKUnitCubeBlockCoarseProbability_le_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    couplingKUnitCubeBlockCoarseProbability
        coupling hcoupling cutoff volume ≤ (1 : Q') :=
  couplingKFamilyEventProbability_le_one
    coupling hcoupling cutoff volume _

theorem couplingKUnitCubeBlockRefinedProbability_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    (0 : Q') ≤ couplingKUnitCubeBlockRefinedProbability
      coupling hcoupling cutoff volume :=
  couplingKFamilyEventProbability_nonnegative
    coupling hcoupling cutoff volume _

theorem couplingKUnitCubeBlockRefinedProbability_le_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    couplingKUnitCubeBlockRefinedProbability
        coupling hcoupling cutoff volume ≤ (1 : Q') :=
  couplingKFamilyEventProbability_le_one
    coupling hcoupling cutoff volume _

/-- Exact finite-volume discrepancy between the coarse coordinate at one
coupling and the refined coordinate at another. -/
def couplingKUnitCubeBlockDefect
    (coarseCoupling : Q') (hcoarse : (0 : Q') ≤ coarseCoupling)
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) : Q' :=
  Q'.abs
    (couplingKUnitCubeBlockCoarseProbability
        coarseCoupling hcoarse cutoff volume +
      (-couplingKUnitCubeBlockRefinedProbability
        fineCoupling hfine cutoff volume))

theorem couplingKUnitCubeBlockDefect_nonnegative
    (coarseCoupling : Q') (hcoarse : (0 : Q') ≤ coarseCoupling)
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    (0 : Q') ≤ couplingKUnitCubeBlockDefect
      coarseCoupling hcoarse fineCoupling hfine cutoff volume :=
  Q'.abs_nonneg _

private theorem neg_nonpos_local {value : Q'}
    (hvalue : (0 : Q') ≤ value) : -value ≤ (0 : Q') := by
  have hneg := Q'.neg_le_neg hvalue
  change -value ≤ (0 : Q') at hneg
  exact hneg

/-- The universal probability bound.  This is only a sanity bound; the RG
task is to replace `1` by a summable coupling-dependent defect. -/
theorem couplingKUnitCubeBlockDefect_le_one
    (coarseCoupling : Q') (hcoarse : (0 : Q') ≤ coarseCoupling)
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    couplingKUnitCubeBlockDefect
        coarseCoupling hcoarse fineCoupling hfine cutoff volume ≤
      (1 : Q') := by
  let coarse := couplingKUnitCubeBlockCoarseProbability
    coarseCoupling hcoarse cutoff volume
  let refined := couplingKUnitCubeBlockRefinedProbability
    fineCoupling hfine cutoff volume
  have hcoarse0 : (0 : Q') ≤ coarse := by
    dsimp only [coarse]
    exact couplingKUnitCubeBlockCoarseProbability_nonnegative
      coarseCoupling hcoarse cutoff volume
  have hcoarse1 : coarse ≤ (1 : Q') := by
    dsimp only [coarse]
    exact couplingKUnitCubeBlockCoarseProbability_le_one
      coarseCoupling hcoarse cutoff volume
  have hrefined0 : (0 : Q') ≤ refined := by
    dsimp only [refined]
    exact couplingKUnitCubeBlockRefinedProbability_nonnegative
      fineCoupling hfine cutoff volume
  have hrefined1 : refined ≤ (1 : Q') := by
    dsimp only [refined]
    exact couplingKUnitCubeBlockRefinedProbability_le_one
      fineCoupling hfine cutoff volume
  have hlowerNeg : (-(1 : Q')) ≤ -refined :=
    Q'.neg_le_neg hrefined1
  have hlowerAdd : -refined ≤ coarse + (-refined) := by
    have hadd := Q'.add_le_add_right
      (0 : Q') coarse (-refined) hcoarse0
    rw [Q'.zero_add'] at hadd
    exact hadd
  have hupperAdd : coarse + (-refined) ≤ coarse := by
    have hadd := Q'.add_le_add_left coarse (-refined) 0
      (neg_nonpos_local hrefined0)
    rw [Q'.add_zero'] at hadd
    exact hadd
  unfold couplingKUnitCubeBlockDefect
  dsimp only [coarse, refined] at hlowerNeg hlowerAdd hupperAdd
  exact Q'.abs_le
    (Q'.le_trans' _ _ _ hlowerNeg hlowerAdd)
    (Q'.le_trans' _ _ _ hupperAdd hcoarse1)

/-! ## 3. Anchor compatibility and the activity-matched shifted defect -/

theorem couplingKUnitCubeBlockDefect_anchor_eqv
    (cutoff volume : Nat) :
    couplingKUnitCubeBlockDefect
        anchorCoupling (by decide) anchorCoupling (by decide)
        cutoff volume ≈
      anchorSameCouplingUnitCubeBlockDefect cutoff volume := by
  have hcoarse :=
    couplingKFamilyEventProbability_anchor_eqv_compatible
      cutoff volume
      (targetCylinderEvent 4 volume unitCubeBlockCylinderRoots
        unitCubeBlockCoarseOccurrencePredicate)
  have hrefined :=
    couplingKFamilyEventProbability_anchor_eqv_compatible
      cutoff volume
      (targetCylinderEvent 4 volume unitCubeBlockCylinderRoots
        unitCubeBlockRefinedOccurrencePredicate)
  unfold couplingKUnitCubeBlockDefect
    couplingKUnitCubeBlockCoarseProbability
    couplingKUnitCubeBlockRefinedProbability
    anchorSameCouplingUnitCubeBlockDefect
  exact Q'.abs_eqv_congr
    (Q'.add_eqv_congr' hcoarse
      (Q'.neg_eqv_congr _ _ hrefined))

/-- The first exact finite defect whose two laws use the activity-matching
coarse/fine coupling shift. -/
def activityMatchedUnitCubeBlockDefect
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) : Q' :=
  couplingKUnitCubeBlockDefect
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine)
    fineCoupling hfine cutoff volume

theorem activityMatchedUnitCubeBlockDefect_nonnegative
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    (0 : Q') ≤ activityMatchedUnitCubeBlockDefect
      fineCoupling hfine cutoff volume :=
  couplingKUnitCubeBlockDefect_nonnegative _ _ _ _ _ _

theorem activityMatchedUnitCubeBlockDefect_le_one
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    activityMatchedUnitCubeBlockDefect
        fineCoupling hfine cutoff volume ≤ (1 : Q') :=
  couplingKUnitCubeBlockDefect_le_one _ _ _ _ _ _

/-- The two bare roots underlying `activityMatchedUnitCubeBlockDefect` have
exactly equal derived activity. -/
theorem activityMatchedUnitCubeBlockDefect_rootActivities_eqv
    (fineCoupling : Q') :
    canonicalSurfaceActivity (unitCubeBlockCoupling fineCoupling) 2
        coarseUnitCubeSupportIds ≈
      canonicalSurfaceActivity fineCoupling 4
        dyadicUnitCubeSupportIds :=
  coarse_shifted_activity_eqv_dyadic_activity fineCoupling

#print axioms couplingKPhysicalPartition_one_le
#print axioms couplingKPhysicalPartition_pos
#print axioms couplingKFamilyEventProbability_nonnegative
#print axioms couplingKFamilyEventProbability_le_one
#print axioms couplingKFamilyEventProbability_anchor_eqv_compatible
#print axioms couplingKUnitCubeBlockDefect_le_one
#print axioms couplingKUnitCubeBlockDefect_anchor_eqv
#print axioms activityMatchedUnitCubeBlockDefect_rootActivities_eqv

end YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
