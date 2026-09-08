/-
# Two-replica four-cell form of the actual pushed covariance

The actual physical block kernel's cubic raw covariance numerator is already
written as a positive-fine-row sum of literal recoupling event-weight ratios.
This module exposes the exact two-replica determinant hidden in that formula.

For any finite slab kernel, its unnormalized pushed target mass has total mass
equal to the fine physical partition.  The pushed covariance numerator then
factors exactly as

  (TT * FF - FT * TF) * Z_fine.

Specializing to the production kernel identifies every one of the four cells
with the previously proved positive-row raw-ratio recursion.  The same
determinant is also the difference between two literal Cartesian pair sums on
the *coarse target* carrier.  This pins the receiver-column frontier exactly:
the existing successful-event switch acts on a same-datum fine source-pair
carrier, while the block-transport determinant here acts on coarse output
pairs.  A carrier-respecting source/target/receiver comparison is still
required; no contraction or `O(a)` estimate is asserted here.

Constructive contract: finite rational sums, Boolean filters, and the actual
globally glued kernel only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
import YMGap.Continuum.FiniteWeightedBooleanCovariance

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualPhysicalConnectedObservableRawCross
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem rawCovarianceNumerator_eqv_of_eqv_local
    {joint joint' root root' target target' partition : Q'}
    (hjoint : joint ≈ joint') (hroot : root ≈ root')
    (htarget : target ≈ target') :
    rawCovarianceNumerator joint root target partition ≈
      rawCovarianceNumerator joint' root' target' partition := by
  unfold rawCovarianceNumerator
  exact sub_eqv_both_local
    (Q'.mul_eqv_congr_right _ _ (partition * partition) hjoint)
    (Q'.mul_eqv_congr_right _ _ partition
      (mul_eqv_both_local hroot htarget))

private theorem fourCellCross_eqv_jointCross_local
    (tt tf ft ff z : Q')
    (hz : z ≈ (tt + tf) + (ft + ff)) :
    tt * z - (tt + tf) * (tt + ft) ≈ tt * ff - ft * tf := by
  refine Q'.eqv_trans _
    (tt * ((tt + tf) + (ft + ff)) -
      (tt + tf) * (tt + ft)) _ ?_ ?_
  · exact sub_eqv_both_local
      (mul_eqv_both_local (Q'.eqv_refl _) hz)
      (Q'.eqv_refl _)
  · refine Q'.eqv_trans _
      (((tt + tf) + (ft + ff)) * tt -
        (tt + tf) * (tt + ft)) _ ?_ ?_
    · exact sub_eqv_both_local
        (Q'.mul_comm_eqv tt ((tt + tf) + (ft + ff)))
        (Q'.eqv_refl _)
    refine Q'.eqv_trans _
      ((ft + ff) * tt - (tt + tf) * ft) _
      (crossDifference_split (tt + tf) (ft + ff) tt ft) ?_
    refine Q'.eqv_trans _
      ((ft + ff) * tt - ft * (tt + tf)) _ ?_ ?_
    · exact sub_eqv_both_local (Q'.eqv_refl _)
        (Q'.mul_comm_eqv (tt + tf) ft)
    refine Q'.eqv_trans _ (ff * tt - ft * tf) _
      (crossDifference_split ft ff tt tf) ?_
    exact sub_eqv_both_local
      (Q'.mul_comm_eqv ff tt) (Q'.eqv_refl _)

/-! ## 1. The unnormalized pushed target law -/

/-- Raw mass delivered by a finite physical block kernel to one coarse
target, before division by the fine physical partition. -/
def pushedPhysicalTargetRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (target : EdgeLabelling) : Q' :=
  listQSum
    (fun source =>
      S.fine.physicalTerm source * K.kernel source target)
    S.fine.physicalLabellings

private theorem weightedCylinderSum_eqv_filter
    (weight : EdgeLabelling → Q') (states : List EdgeLabelling)
    (event : EdgeLabelling → Bool) :
    listQSum
        (fun state =>
          weight state * weightedCylinderObservable event 1 state)
        states ≈
      listQSum weight (states.filter event) := by
  unfold weightedCylinderObservable
  refine Q'.eqv_trans _
    (listQSum
      (fun state => if event state then weight state else 0)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    cases hevent : event state
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.mul_zero_eqv (weight state)
    · simp only [if_true]
      exact Q'.mul_one_eqv (weight state)
  · exact Q'.eqv_symm (listQSum_filter weight event states)

/-- The raw pushed target law has the fine physical partition as its total
mass. -/
theorem pushedPhysicalTargetRawMass_total
    {S : SlabScalePair} (K : S.FiniteSlabKernel) :
    listQSum (pushedPhysicalTargetRawMass K)
        S.coarse.physicalLabellings ≈
      S.fine.physicalPartition := by
  unfold pushedPhysicalTargetRawMass
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            S.fine.physicalTerm source * K.kernel source target)
          S.coarse.physicalLabellings)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_swap
      (fun source target =>
        S.fine.physicalTerm source * K.kernel source target)
      S.fine.physicalLabellings S.coarse.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum S.fine.physicalTerm S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    exact Q'.eqv_trans _
      (S.fine.physicalTerm source *
        listQSum (K.kernel source) S.coarse.physicalLabellings) _
      (listQSum_mul_left
        (S.fine.physicalTerm source) (K.kernel source)
        S.coarse.physicalLabellings)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (S.fine.physicalTerm source) _ _
          (K.row_normalized source hsource))
        (Q'.mul_one_eqv (S.fine.physicalTerm source)))
  · unfold SlabPhysicalData.physicalPartition
      SlabPhysicalData.physicalTerm SlabPhysicalData.physicalLabellings
      SlabPhysicalData.faceEdges
    exact Q'.eqv_refl _

/-- Every pushed raw event numerator is exactly the filtered mass of the raw
pushed target law. -/
theorem pushedPhysicalEventNumerator_eqv_targetRawEventMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) :
    pushedPhysicalEventNumerator K event ≈
      finiteWeightedEventMass
        S.coarse.physicalLabellings
        (pushedPhysicalTargetRawMass K) event := by
  unfold pushedPhysicalEventNumerator finiteWeightedEventMass
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            S.fine.physicalTerm source * K.kernel source target)
          (S.coarse.physicalLabellings.filter event))
      S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    refine Q'.eqv_trans _
      (S.fine.physicalTerm source *
        listQSum (K.kernel source)
          (S.coarse.physicalLabellings.filter event)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (S.fine.physicalTerm source) _ _
        (weightedCylinderSum_eqv_filter
          (K.kernel source) S.coarse.physicalLabellings event)
    · exact Q'.eqv_symm
        (listQSum_mul_left
          (S.fine.physicalTerm source) (K.kernel source)
          (S.coarse.physicalLabellings.filter event))
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun source target =>
          S.fine.physicalTerm source * K.kernel source target)
        S.fine.physicalLabellings
        (S.coarse.physicalLabellings.filter event))

/-! ## 2. A cancellation-free four-cell factorization -/

private theorem rawCovarianceNumerator_eqv_fourCell_mul_partition
    {A : Type} (states : List A) (weight : A → Q')
    (partition : Q')
    (partition_eqv : listQSum weight states ≈ partition)
    (first second : A → Bool) :
    rawCovarianceNumerator
        (finiteWeightedTT states weight first second)
        (finiteWeightedEventMass states weight first)
        (finiteWeightedEventMass states weight second)
        partition ≈
      finiteWeightedFourCellCrossNumerator
          states weight first second * partition := by
  let tt := finiteWeightedTT states weight first second
  let tf := finiteWeightedTF states weight first second
  let ft := finiteWeightedFT states weight first second
  let ff := finiteWeightedFF states weight first second
  have hfirst := finiteWeightedFirstEventMass_eqv_TT_add_TF
    states weight first second
  have hsecond := finiteWeightedSecondEventMass_eqv_TT_add_FT
    states weight first second
  have hcarrier := finiteWeightedPartition_eqv_fourCells
    states weight first second
  have hz : partition ≈ (tt + tf) + (ft + ff) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm partition_eqv) hcarrier
  refine Q'.eqv_trans _
    (rawCovarianceNumerator tt (tt + tf) (tt + ft) partition) _ ?_ ?_
  · exact rawCovarianceNumerator_eqv_of_eqv_local
      (Q'.eqv_refl _) hfirst hsecond
  refine Q'.eqv_trans _
    ((tt * partition - (tt + tf) * (tt + ft)) * partition) _ ?_ ?_
  · unfold rawCovarianceNumerator
    refine Q'.eqv_trans _
      ((tt * partition) * partition -
        ((tt + tf) * (tt + ft)) * partition) _ ?_ ?_
    · exact sub_eqv_both_local
        (Q'.eqv_symm (Q'.mul_assoc_eqv tt partition partition))
        (Q'.eqv_refl _)
    · exact Q'.eqv_symm
        (Q'.sub_mul_eqv
          (tt * partition) ((tt + tf) * (tt + ft)) partition)
  have hcross :
      tt * partition - (tt + tf) * (tt + ft) ≈
        tt * ff - ft * tf :=
    fourCellCross_eqv_jointCross_local tt tf ft ff partition hz
  refine Q'.eqv_trans _ ((tt * ff - ft * tf) * partition) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ partition hcross
  · dsimp only [tt, tf, ft, ff]
    unfold finiteWeightedFourCellCrossNumerator
    exact Q'.eqv_refl _

/-- Four-cell determinant of the raw pushed law on coarse target states. -/
def pushedFaceRawFourCellCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  finiteWeightedFourCellCrossNumerator
    S.coarse.physicalLabellings
    (pushedPhysicalTargetRawMass K)
    (slabPhysicalFacePositiveB root)
    (slabPhysicalFacePositiveB target)

/-- The generic pushed cubic numerator is one redundant partition factor
times its raw four-cell determinant. -/
theorem pushedFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    pushedFaceRawCovarianceNumerator K root target ≈
      pushedFaceRawFourCellCross K root target *
        S.fine.physicalPartition := by
  let states := S.coarse.physicalLabellings
  let weight := pushedPhysicalTargetRawMass K
  let first := slabPhysicalFacePositiveB root
  let second := slabPhysicalFacePositiveB target
  have hjoint :
      pushedPhysicalEventNumerator K
          (slabPhysicalFacePairPositiveB root target) ≈
        finiteWeightedTT states weight first second := by
    simpa only [states, weight, first, second,
        finiteWeightedTT, slabPhysicalFacePairPositiveB] using
      (pushedPhysicalEventNumerator_eqv_targetRawEventMass K
        (slabPhysicalFacePairPositiveB root target))
  have hroot :
      pushedPhysicalEventNumerator K
          (slabPhysicalFacePositiveB root) ≈
        finiteWeightedEventMass states weight first :=
    pushedPhysicalEventNumerator_eqv_targetRawEventMass K first
  have htarget :
      pushedPhysicalEventNumerator K
          (slabPhysicalFacePositiveB target) ≈
        finiteWeightedEventMass states weight second :=
    pushedPhysicalEventNumerator_eqv_targetRawEventMass K second
  unfold pushedFaceRawCovarianceNumerator
  refine Q'.eqv_trans _
    (rawCovarianceNumerator
      (finiteWeightedTT states weight first second)
      (finiteWeightedEventMass states weight first)
      (finiteWeightedEventMass states weight second)
      S.fine.physicalPartition) _ ?_ ?_
  · exact rawCovarianceNumerator_eqv_of_eqv_local
      hjoint hroot htarget
  · exact rawCovarianceNumerator_eqv_fourCell_mul_partition
      states weight S.fine.physicalPartition
      (pushedPhysicalTargetRawMass_total K) first second

/-! ## 3. Specialize all four cells to positive-row raw ratios -/

/-- The actual raw-ratio four-cell determinant.  Each displayed event
numerator is definitionally the positive-row recursion from the actual raw
kernel module. -/
def actualPushedFaceRawFourCellCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  let first := slabPhysicalFacePositiveB root
  let second := slabPhysicalFacePositiveB target
  actualPushedPhysicalEventNumerator S hfineCutoff hcoarseCoupling
        (fun state => first state && second state) *
      actualPushedPhysicalEventNumerator S hfineCutoff hcoarseCoupling
        (fun state => !(first state) && !(second state)) -
    actualPushedPhysicalEventNumerator S hfineCutoff hcoarseCoupling
          (fun state => !(first state) && second state) *
      actualPushedPhysicalEventNumerator S hfineCutoff hcoarseCoupling
        (fun state => first state && !(second state))

theorem pushedFaceRawFourCellCross_physicalKernel_eqv_actualRaw
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    pushedFaceRawFourCellCross
        (physicalKernel S hfineCutoff hcoarseCoupling) root target ≈
      actualPushedFaceRawFourCellCross S hfineCutoff
        hcoarseCoupling root target := by
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let states := S.coarse.physicalLabellings
  let weight := pushedPhysicalTargetRawMass K
  let first := slabPhysicalFacePositiveB root
  let second := slabPhysicalFacePositiveB target
  have hevent : ∀ event : EdgeLabelling → Bool,
      finiteWeightedEventMass states weight event ≈
        actualPushedPhysicalEventNumerator S hfineCutoff
          hcoarseCoupling event := by
    intro event
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (pushedPhysicalEventNumerator_eqv_targetRawEventMass K event))
      (pushedPhysicalEventNumerator_physicalKernel_eqv_actualRaw
        S hfineCutoff hcoarseCoupling event)
  unfold pushedFaceRawFourCellCross
    finiteWeightedFourCellCrossNumerator finiteWeightedTT
    finiteWeightedTF finiteWeightedFT finiteWeightedFF
    actualPushedFaceRawFourCellCross
  exact sub_eqv_both_local
    (mul_eqv_both_local
      (hevent (fun state => first state && second state))
      (hevent (fun state => !(first state) && !(second state))))
    (mul_eqv_both_local
      (hevent (fun state => !(first state) && second state))
      (hevent (fun state => first state && !(second state))))

/-- The production-kernel cubic numerator is exactly its positive-row
raw-ratio four-cell determinant times the fine partition. -/
theorem actualPushedFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPushedFaceRawCovarianceNumerator S hfineCutoff
        hcoarseCoupling root target ≈
      actualPushedFaceRawFourCellCross S hfineCutoff
          hcoarseCoupling root target * S.fine.physicalPartition := by
  refine Q'.eqv_trans _
    (pushedFaceRawCovarianceNumerator
      (physicalKernel S hfineCutoff hcoarseCoupling) root target) _ ?_ ?_
  · exact Q'.eqv_symm
      (pushedFaceRawCovarianceNumerator_physicalKernel_eqv_actualRaw
        S hfineCutoff hcoarseCoupling root target)
  refine Q'.eqv_trans _
    (pushedFaceRawFourCellCross
        (physicalKernel S hfineCutoff hcoarseCoupling) root target *
      S.fine.physicalPartition) _ ?_ ?_
  · exact pushedFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
      (physicalKernel S hfineCutoff hcoarseCoupling) root target
  · exact Q'.mul_eqv_congr_right _ _ S.fine.physicalPartition
      (pushedFaceRawFourCellCross_physicalKernel_eqv_actualRaw
        S hfineCutoff hcoarseCoupling root target)

/-! ## 4. The complete connected four-cell raw cross -/

def physicalFaceRawFourCellCross
    (D : SlabPhysicalData) (root target : Nat) : Q' :=
  finiteWeightedFourCellCrossNumerator
    D.physicalLabellings D.physicalTerm
    (slabPhysicalFacePositiveB root)
    (slabPhysicalFacePositiveB target)

private theorem physicalEventNumerator_eqv_weightedEventMass
    (D : SlabPhysicalData) (event : EdgeLabelling → Bool) :
    physicalEventNumerator D event ≈
      finiteWeightedEventMass
        D.physicalLabellings D.physicalTerm event := by
  unfold physicalEventNumerator finiteWeightedEventMass
  exact weightedCylinderSum_eqv_filter
    D.physicalTerm D.physicalLabellings event

theorem coarseFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
    (D : SlabPhysicalData) (root target : Nat) :
    coarseFaceRawCovarianceNumerator D root target ≈
      physicalFaceRawFourCellCross D root target *
        D.physicalPartition := by
  let states := D.physicalLabellings
  let weight := D.physicalTerm
  let first := slabPhysicalFacePositiveB root
  let second := slabPhysicalFacePositiveB target
  have hjoint :
      physicalEventNumerator D
          (slabPhysicalFacePairPositiveB root target) ≈
        finiteWeightedTT states weight first second := by
    simpa only [states, weight, first, second,
        finiteWeightedTT, slabPhysicalFacePairPositiveB] using
      (physicalEventNumerator_eqv_weightedEventMass D
        (slabPhysicalFacePairPositiveB root target))
  have hroot :
      physicalEventNumerator D
          (slabPhysicalFacePositiveB root) ≈
        finiteWeightedEventMass states weight first :=
    physicalEventNumerator_eqv_weightedEventMass D first
  have htarget :
      physicalEventNumerator D
          (slabPhysicalFacePositiveB target) ≈
        finiteWeightedEventMass states weight second :=
    physicalEventNumerator_eqv_weightedEventMass D second
  have hpartition :
      listQSum weight states ≈ D.physicalPartition := by
    unfold states weight SlabPhysicalData.physicalPartition
      SlabPhysicalData.physicalTerm SlabPhysicalData.physicalLabellings
      SlabPhysicalData.faceEdges
    exact Q'.eqv_refl _
  unfold coarseFaceRawCovarianceNumerator
  refine Q'.eqv_trans _
    (rawCovarianceNumerator
      (finiteWeightedTT states weight first second)
      (finiteWeightedEventMass states weight first)
      (finiteWeightedEventMass states weight second)
      D.physicalPartition) _ ?_ ?_
  · exact rawCovarianceNumerator_eqv_of_eqv_local
      hjoint hroot htarget
  · exact rawCovarianceNumerator_eqv_fourCell_mul_partition
      states weight D.physicalPartition hpartition first second

/-- Connected coarse-versus-pushed covariance cross with both covariance
numerators exposed as four-cell determinants. -/
def physicalConnectedCovarianceFourCellRawCrossDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  (physicalFaceRawFourCellCross
      S.coarse M.coarseRoot M.coarseTarget *
      S.coarse.physicalPartition) *
      rawCovarianceDenominator S.fine.physicalPartition -
    (actualPushedFaceRawFourCellCross S hfineCutoff
      hcoarseCoupling M.coarseRoot M.coarseTarget *
      S.fine.physicalPartition) *
      rawCovarianceDenominator S.coarse.physicalPartition

theorem physicalConnectedCovarianceRawCrossDefect_eqv_fourCellRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovarianceRawCrossDefect S hfineCutoff
        hcoarseCoupling M ≈
      physicalConnectedCovarianceFourCellRawCrossDefect
        S hfineCutoff hcoarseCoupling M := by
  unfold physicalConnectedCovarianceRawCrossDefect
    physicalConnectedCovarianceFourCellRawCrossDefect
  exact sub_eqv_both_local
    (Q'.mul_eqv_congr_right _ _
      (rawCovarianceDenominator S.fine.physicalPartition)
      (coarseFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
        S.coarse M.coarseRoot M.coarseTarget))
    (Q'.mul_eqv_congr_right _ _
      (rawCovarianceDenominator S.coarse.physicalPartition)
      (actualPushedFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget))

/-- A relative estimate on the actual two-replica four-cell cross is enough
for the exact connected pushed-law remainder bound. -/
theorem centeredCylinderRemainder_physicalKernel_abs_le_of_fourCellRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (budget : Q')
    (hcross :
      Q'.abs
          (physicalConnectedCovarianceFourCellRawCrossDefect
            S hfineCutoff hcoarseCoupling M) ≤
        budget * connectedCovarianceRawCrossDenominator S) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      budget := by
  apply centeredCylinderRemainder_physicalKernel_abs_le_of_actualRawCross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (physicalConnectedCovarianceRawCrossDefect_eqv_fourCellRawCross
          S hfineCutoff hcoarseCoupling M)))
    hcross

/-! ## 5. The literal coarse-output pair carrier -/

def pushedFaceRawFourCellSourcePairs
    {S : SlabScalePair} (root target : Nat) :
    List (EdgeLabelling × EdgeLabelling) :=
  cartesian
    (S.coarse.physicalLabellings.filter fun state =>
      slabPhysicalFacePositiveB root state &&
        slabPhysicalFacePositiveB target state)
    (S.coarse.physicalLabellings.filter fun state =>
      !(slabPhysicalFacePositiveB root state) &&
        !(slabPhysicalFacePositiveB target state))

def pushedFaceRawFourCellTargetPairs
    {S : SlabScalePair} (root target : Nat) :
    List (EdgeLabelling × EdgeLabelling) :=
  cartesian
    (S.coarse.physicalLabellings.filter fun state =>
      !(slabPhysicalFacePositiveB root state) &&
        slabPhysicalFacePositiveB target state)
    (S.coarse.physicalLabellings.filter fun state =>
      slabPhysicalFacePositiveB root state &&
        !(slabPhysicalFacePositiveB target state))

def pushedPhysicalTargetPairRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  pushedPhysicalTargetRawMass K pair.1 *
    pushedPhysicalTargetRawMass K pair.2

/-- The pushed four-cell determinant is literally the source-pair raw mass
minus the opposite target-pair raw mass on the coarse output carrier. -/
theorem pushedFaceRawFourCellCross_eqv_pair_mass_difference
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    pushedFaceRawFourCellCross K root target ≈
      listQSum (pushedPhysicalTargetPairRawMass K)
          (pushedFaceRawFourCellSourcePairs
            (S := S) root target) -
        listQSum (pushedPhysicalTargetPairRawMass K)
          (pushedFaceRawFourCellTargetPairs
            (S := S) root target) := by
  unfold pushedFaceRawFourCellCross
    finiteWeightedFourCellCrossNumerator finiteWeightedTT
    finiteWeightedTF finiteWeightedFT finiteWeightedFF
    finiteWeightedEventMass
    pushedFaceRawFourCellSourcePairs pushedFaceRawFourCellTargetPairs
    pushedPhysicalTargetPairRawMass
  exact sub_eqv_both_local
    (Q'.eqv_symm
      (listQSum_cartesian_product
        (pushedPhysicalTargetRawMass K)
        (pushedPhysicalTargetRawMass K)
        (S.coarse.physicalLabellings.filter fun state =>
          slabPhysicalFacePositiveB root state &&
            slabPhysicalFacePositiveB target state)
        (S.coarse.physicalLabellings.filter fun state =>
          !(slabPhysicalFacePositiveB root state) &&
            !(slabPhysicalFacePositiveB target state))))
    (Q'.eqv_symm
      (listQSum_cartesian_product
        (pushedPhysicalTargetRawMass K)
        (pushedPhysicalTargetRawMass K)
        (S.coarse.physicalLabellings.filter fun state =>
          !(slabPhysicalFacePositiveB root state) &&
            slabPhysicalFacePositiveB target state)
        (S.coarse.physicalLabellings.filter fun state =>
          slabPhysicalFacePositiveB root state &&
            !(slabPhysicalFacePositiveB target state))))

#print axioms pushedPhysicalTargetRawMass
#print axioms pushedPhysicalTargetRawMass_total
#print axioms pushedPhysicalEventNumerator_eqv_targetRawEventMass
#print axioms pushedFaceRawFourCellCross
#print axioms pushedFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
#print axioms actualPushedFaceRawFourCellCross
#print axioms pushedFaceRawFourCellCross_physicalKernel_eqv_actualRaw
#print axioms actualPushedFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
#print axioms physicalFaceRawFourCellCross
#print axioms coarseFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
#print axioms physicalConnectedCovarianceFourCellRawCrossDefect
#print axioms physicalConnectedCovarianceRawCrossDefect_eqv_fourCellRawCross
#print axioms centeredCylinderRemainder_physicalKernel_abs_le_of_fourCellRawCross
#print axioms pushedFaceRawFourCellCross_eqv_pair_mass_difference

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
