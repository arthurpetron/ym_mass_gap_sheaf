/-
# Signed cancellation of the eight outward geometry cells

Before taking cellwise absolute values, changing the coarse subsupport query
triple to the fine query triple only moves each compatible family from one
three-bit cell to another.  The family weight itself is unchanged.  This
module records that signed transport exactly: summing all eight pattern
numerators gives the same compatible support-gas partition for either query,
and the sum of the eight signed geometry drifts is zero.

This is genuine cross-cell slack.  It is deliberately stated before any
absolute value, so a later cycle or path pairing may retain it instead of
paying the full XOR numerator independently in every cell.
-/

import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.Z4OutwardFineCoarseDisagreementInjectionInterface

namespace YMGap.Continuum.Z4OutwardFineCoarseSignedGeometryCancellation

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasErrorSplit
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasEventDifference
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable

local infix:50 " ≈ " => Q'.eqv

/-! ## The complete duplicate-free three-bit target -/

def outwardAllThreeBlockPatterns : List ThreeBlockPattern :=
  [(false, false, false),
   (false, false, true),
   (false, true, false),
   (false, true, true),
   (true, false, false),
   (true, false, true),
   (true, true, false),
   (true, true, true)]

theorem outwardAllThreeBlockPatterns_nodup :
    outwardAllThreeBlockPatterns.Nodup := by
  decide

theorem pattern_mem_outwardAllThreeBlockPatterns
    (pattern : ThreeBlockPattern) :
    pattern ∈ outwardAllThreeBlockPatterns := by
  rcases pattern with ⟨left, shared, right⟩
  cases left <;> cases shared <;> cases right <;> decide

theorem outwardPatternEvent_eq_fiberTest
    (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) (family : List (List Nat)) :
    outwardComponentSubsupportFamilyPatternEvent queries pattern family =
      decide (pattern =
        outwardComponentSubsupportFamilyPattern queries family) := by
  unfold outwardComponentSubsupportFamilyPatternEvent
  simp only [eq_comm]

theorem outwardCompatibleSupportPatternNumerator_eq_fiberWeight
    (coupling : Q') (queries : ComponentSubsupportQueryTriple)
    (pattern : ThreeBlockPattern) :
    outwardCompatibleSupportPatternNumerator coupling queries pattern =
      fiberWeight
        (canonicalCompatibleAmbientFamilies 6)
        (couplingParametricKSupportFamilyActivity coupling 1 6)
        (outwardComponentSubsupportFamilyPattern queries)
        pattern := by
  unfold outwardCompatibleSupportPatternNumerator
    couplingParametricKCompatibleSupportEventNumerator fiberWeight
  rw [show
    outwardComponentSubsupportFamilyPatternEvent queries pattern =
      (fun family => decide (pattern =
        outwardComponentSubsupportFamilyPattern queries family)) from by
      funext family
      exact outwardPatternEvent_eq_fiberTest queries pattern family]

/-! ## Exact mass conservation for either query triple -/

theorem outwardAllPatternNumerators_eqv_partition
    (coupling : Q') (queries : ComponentSubsupportQueryTriple) :
    listQSum
        (outwardCompatibleSupportPatternNumerator coupling queries)
        outwardAllThreeBlockPatterns ≈
      outwardCompatibleSupportPartition coupling := by
  have hreindex :
      listQSum
          (outwardCompatibleSupportPatternNumerator coupling queries)
          outwardAllThreeBlockPatterns ≈
        listQSum
          (fiberWeight
            (canonicalCompatibleAmbientFamilies 6)
            (couplingParametricKSupportFamilyActivity coupling 1 6)
            (outwardComponentSubsupportFamilyPattern queries))
          outwardAllThreeBlockPatterns := by
    apply listQSum_congr
    intro pattern
    exact Q'.eqv_of_eq
      (outwardCompatibleSupportPatternNumerator_eq_fiberWeight
        coupling queries pattern)
  refine Q'.eqv_trans _ _ _ hreindex ?_
  unfold outwardCompatibleSupportPartition
    couplingParametricKCompatibleSupportGasPartition
  exact fiberWeight_total
    (canonicalCompatibleAmbientFamilies 6)
    (couplingParametricKSupportFamilyActivity coupling 1 6)
    (outwardComponentSubsupportFamilyPattern queries)
    outwardAllThreeBlockPatterns
    outwardAllThreeBlockPatterns_nodup
    (fun family _ => pattern_mem_outwardAllThreeBlockPatterns
      (outwardComponentSubsupportFamilyPattern queries family))

theorem outwardCoarseQueryAllPatternNumerators_eqv_partition
    (coupling : Q') :
    listQSum
        (outwardCompatibleSupportPatternNumerator
          coupling outwardCoarseQueries)
        outwardAllThreeBlockPatterns ≈
      outwardCompatibleSupportPartition coupling :=
  outwardAllPatternNumerators_eqv_partition coupling outwardCoarseQueries

theorem outwardFineQueryAllPatternNumerators_eqv_partition
    (coupling : Q') :
    listQSum
        (outwardCompatibleSupportPatternNumerator
          coupling outwardFineQueries)
        outwardAllThreeBlockPatterns ≈
      outwardCompatibleSupportPartition coupling :=
  outwardAllPatternNumerators_eqv_partition coupling outwardFineQueries

/-! ## The signed eight-cell drift cancels -/

def outwardSignedGeometryPatternNumerator
    (fineCoupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardFineCouplingCoarseQueryNumerator fineCoupling pattern +
    (-outwardFineCompatibleSupportPatternNumerator
      fineCoupling pattern)

private theorem listQSum_neg_local {A : Type} (value : A → Q') :
    ∀ states : List A,
      listQSum (fun state => -(value state)) states ≈
        -(listQSum value states)
  | [] => by
      have h := Q'.neg_add_self_eqv (0 : Q')
      rw [Q'.add_zero'] at h
      exact Q'.eqv_symm h
  | head :: tail => by
      change -(value head) +
          listQSum (fun state => -(value state)) tail ≈
        -(value head + listQSum value tail)
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_neg_local value tail)) ?_
      exact Q'.eqv_symm
        (Q'.neg_add_eqv (value head) (listQSum value tail))

/-- Exact sign-reversing cancellation across the complete eight-cell target.
Each compatible family has the same activity on the positive coarse-labelled
occurrence and the negative fine-labelled occurrence. -/
theorem outwardSignedGeometryAllPatternSum_eqv_zero
    (fineCoupling : Q') :
    listQSum (outwardSignedGeometryPatternNumerator fineCoupling)
        outwardAllThreeBlockPatterns ≈ 0 := by
  let coarse : ThreeBlockPattern → Q' :=
    outwardCompatibleSupportPatternNumerator
      fineCoupling outwardCoarseQueries
  let fine : ThreeBlockPattern → Q' :=
    outwardCompatibleSupportPatternNumerator
      fineCoupling outwardFineQueries
  have hsplit :
      listQSum (outwardSignedGeometryPatternNumerator fineCoupling)
          outwardAllThreeBlockPatterns ≈
        listQSum coarse outwardAllThreeBlockPatterns +
          listQSum (fun pattern => -(fine pattern))
            outwardAllThreeBlockPatterns := by
    unfold outwardSignedGeometryPatternNumerator
      outwardFineCouplingCoarseQueryNumerator
      outwardFineCompatibleSupportPatternNumerator
    exact listQSum_add coarse (fun pattern => -(fine pattern))
      outwardAllThreeBlockPatterns
  have hneg :
      listQSum (fun pattern => -(fine pattern))
          outwardAllThreeBlockPatterns ≈
        -(listQSum fine outwardAllThreeBlockPatterns) :=
    listQSum_neg_local fine outwardAllThreeBlockPatterns
  have hcoarse :
      listQSum coarse outwardAllThreeBlockPatterns ≈
        outwardCompatibleSupportPartition fineCoupling := by
    exact outwardCoarseQueryAllPatternNumerators_eqv_partition fineCoupling
  have hfine :
      listQSum fine outwardAllThreeBlockPatterns ≈
        outwardCompatibleSupportPartition fineCoupling := by
    exact outwardFineQueryAllPatternNumerators_eqv_partition fineCoupling
  refine Q'.eqv_trans _
    (listQSum coarse outwardAllThreeBlockPatterns +
      listQSum (fun pattern => -(fine pattern))
        outwardAllThreeBlockPatterns) _ hsplit ?_
  refine Q'.eqv_trans _
    (listQSum coarse outwardAllThreeBlockPatterns +
      -(listQSum fine outwardAllThreeBlockPatterns)) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) hneg) ?_
  refine Q'.eqv_trans _
    (outwardCompatibleSupportPartition fineCoupling +
      (-outwardCompatibleSupportPartition fineCoupling)) _
    (Q'.add_eqv_congr' hcoarse
      (Q'.neg_eqv_congr _ _ hfine)) ?_
  exact Q'.add_neg_self_eqv
    (outwardCompatibleSupportPartition fineCoupling)

/-- The same zero-sum identity after multiplying every cell by the common
coarse partition occurring in the physical geometry cross-difference. -/
theorem outwardGeometryCrossDifferenceAllPatternSum_eqv_zero
    (fineCoupling : Q') :
    listQSum
        (outwardFineCoarseSupportGeometryCrossDifference fineCoupling)
        outwardAllThreeBlockPatterns ≈ 0 := by
  have hfactor :
      listQSum
          (outwardFineCoarseSupportGeometryCrossDifference fineCoupling)
          outwardAllThreeBlockPatterns ≈
        outwardCoarseCompatibleSupportPartition fineCoupling *
          listQSum (outwardSignedGeometryPatternNumerator fineCoupling)
            outwardAllThreeBlockPatterns := by
    refine Q'.eqv_trans _
      (listQSum
        (fun pattern =>
          outwardSignedGeometryPatternNumerator fineCoupling pattern *
            outwardCoarseCompatibleSupportPartition fineCoupling)
        outwardAllThreeBlockPatterns) _ ?_ ?_
    · apply listQSum_congr
      intro pattern
      exact outwardFineCoarseSupportGeometryCrossDifference_eqv
        fineCoupling pattern
    · refine Q'.eqv_trans _
        (listQSum
          (fun pattern =>
            outwardCoarseCompatibleSupportPartition fineCoupling *
              outwardSignedGeometryPatternNumerator fineCoupling pattern)
          outwardAllThreeBlockPatterns) _ ?_ ?_
      · apply listQSum_congr
        intro pattern
        exact Q'.mul_comm_eqv _ _
      · exact listQSum_mul_left
          (outwardCoarseCompatibleSupportPartition fineCoupling)
          (outwardSignedGeometryPatternNumerator fineCoupling)
          outwardAllThreeBlockPatterns
  refine Q'.eqv_trans _
    (outwardCoarseCompatibleSupportPartition fineCoupling *
      listQSum (outwardSignedGeometryPatternNumerator fineCoupling)
        outwardAllThreeBlockPatterns) _ hfactor ?_
  exact Q'.eqv_trans _
    (outwardCoarseCompatibleSupportPartition fineCoupling * 0) _
    (Q'.mul_eqv_congr_left _ _ _
      (outwardSignedGeometryAllPatternSum_eqv_zero fineCoupling))
    (Q'.mul_zero_eqv _)

/-! ## Zero-sum alone does not control the maximum cell defect -/

private def fenceHalf : Q' := Q'.mkPos 1 2 (by decide)

def zeroSumFenceFineMass (_pattern : ThreeBlockPattern) : Q' := 1

def zeroSumFenceCoarseMass (pattern : ThreeBlockPattern) : Q' :=
  if pattern = (false, false, false) then 1 + fenceHalf
  else if pattern = (true, false, false) then fenceHalf
  else 1

theorem zeroSumFenceFineMass_pos (pattern : ThreeBlockPattern) :
    (0 : Q') < zeroSumFenceFineMass pattern := by
  unfold zeroSumFenceFineMass
  decide

theorem zeroSumFenceCoarseMass_pos (pattern : ThreeBlockPattern) :
    (0 : Q') < zeroSumFenceCoarseMass pattern := by
  rcases pattern with ⟨left, shared, right⟩
  cases left <;> cases shared <;> cases right <;>
    simp [zeroSumFenceCoarseMass, fenceHalf] <;> decide

/-- Both strictly positive eight-cell masses have exactly the same total.
The extra half-unit in `000` is the missing half-unit in `100`. -/
theorem zeroSumFence_totals_eqv :
    listQSum zeroSumFenceCoarseMass outwardAllThreeBlockPatterns ≈
      listQSum zeroSumFenceFineMass outwardAllThreeBlockPatterns := by
  unfold outwardAllThreeBlockPatterns zeroSumFenceCoarseMass
    zeroSumFenceFineMass fenceHalf listQSum
  decide

theorem zeroSumFence_signed_sum_eqv_zero :
    listQSum
        (fun pattern => zeroSumFenceCoarseMass pattern +
          (-zeroSumFenceFineMass pattern))
        outwardAllThreeBlockPatterns ≈ 0 := by
  unfold outwardAllThreeBlockPatterns zeroSumFenceCoarseMass
    zeroSumFenceFineMass fenceHalf listQSum
  decide

/-- Even strict positivity plus exact conservation of total mass does not let
cross-cell slack pay a singleton-cell relative defect below one half.  Thus
the production maximum-over-cells consumer still needs a within-cell signed
pairing (or a genuinely different norm), not merely the global zero sum. -/
theorem zeroSumFence_pattern100_cost_forces_half_le
    {bound : Q'}
    (hcell : Q'.abs
        (zeroSumFenceCoarseMass (true, false, false) +
          (-zeroSumFenceFineMass (true, false, false))) ≤
      bound * zeroSumFenceFineMass (true, false, false)) :
    fenceHalf ≤ bound := by
  have hleft : Q'.abs
      (zeroSumFenceCoarseMass (true, false, false) +
        (-zeroSumFenceFineMass (true, false, false))) ≈ fenceHalf := by
    unfold zeroSumFenceCoarseMass zeroSumFenceFineMass fenceHalf
    decide
  have hright : bound *
      zeroSumFenceFineMass (true, false, false) ≈ bound := by
    unfold zeroSumFenceFineMass
    exact Q'.mul_one_eqv bound
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hleft) (Q'.le_trans' _ _ _ hcell
      (Q'.le_of_eqv hright))

#print axioms outwardAllPatternNumerators_eqv_partition
#print axioms outwardCoarseQueryAllPatternNumerators_eqv_partition
#print axioms outwardFineQueryAllPatternNumerators_eqv_partition
#print axioms outwardSignedGeometryAllPatternSum_eqv_zero
#print axioms outwardGeometryCrossDifferenceAllPatternSum_eqv_zero
#print axioms zeroSumFenceFineMass_pos
#print axioms zeroSumFenceCoarseMass_pos
#print axioms zeroSumFence_totals_eqv
#print axioms zeroSumFence_signed_sum_eqv_zero
#print axioms zeroSumFence_pattern100_cost_forces_half_le

end YMGap.Continuum.Z4OutwardFineCoarseSignedGeometryCancellation
