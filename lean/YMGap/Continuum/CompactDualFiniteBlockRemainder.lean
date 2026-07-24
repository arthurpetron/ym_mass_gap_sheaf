/-
# Exact finite remainder algebra for a corrected-slab block

This module advances CD-2 to its genuine physical frontier.  A scale pair
uses the boundary-complete reflected slab at both scales, the affine dyadic
extent forced by reflection, the lossless four-character cutoff, and an
explicit coupling map.  A finite kernel is required to be nonnegative,
row-normalized, source-dependent, and reflection-intertwining.

For any such kernel the pushforward remainder is defined, not supplied:

    R(y) = sum_x mu_fine(x) K(x,y) - mu_coarse(y).

Finite Fubini and normalization prove `sum_y R(y) = 0`.  Thus zero total mass
is no longer an independent CD-2 obligation.  The still-open physical step is
to construct this kernel from the globally link-glued corrected-slab
character/fusion weight.  This file deliberately supplies no inhabitant.

## Axiom gate

Finite exact-rational algebra and previously audited slab theorems only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.CompactDualSlabPhysicalData
import YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.CompactDualFiniteBlockRemainder

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel

local infix:50 " ≈ " => Q'.eqv

/-- The exact geometry and representation schedule of one dyadic slab step.

Four bounded fine characters can fuse up to twice-spin `4 * cutoff`, so the
coarse cutoff records that lossless local target rather than silently
truncating it. -/
structure SlabScalePair : Type where
  fine : SlabPhysicalData
  coarse : SlabPhysicalData
  couplingFlow : Q' → Q'
  fine_extent :
    fine.extent = dyadicSlabFineExtent coarse.extent
  coarse_cutoff :
    coarse.cutoff = 4 * fine.cutoff
  coarse_coupling :
    coarse.coupling ≈ couplingFlow fine.coupling

namespace SlabScalePair

/-- A finite algebraic kernel on the actual corrected-slab Cartesian spaces.

This is intentionally named `FiniteSlabKernel`, not
`SpinFoamRPBlockRemainder`: the latter name is reserved for a constructor
whose entries have been identified with the complete globally link-glued
physical block weight. -/
structure FiniteSlabKernel (S : SlabScalePair) : Type where
  kernel : EdgeLabelling → EdgeLabelling → Q'
  nonnegative :
    ∀ fineState coarseState,
      fineState ∈ S.fine.physicalLabellings →
      coarseState ∈ S.coarse.physicalLabellings →
      (0 : Q') ≤ kernel fineState coarseState
  row_normalized :
    ∀ fineState,
      fineState ∈ S.fine.physicalLabellings →
      listQSum (kernel fineState) S.coarse.physicalLabellings ≈ 1
  reflection_intertwines :
    ∀ fineState coarseState,
      fineState ∈ S.fine.physicalLabellings →
      coarseState ∈ S.coarse.physicalLabellings →
      kernel
          (S.fine.reflectLabelling fineState)
          (S.coarse.reflectLabelling coarseState) ≈
        kernel fineState coarseState
  source_dependent :
    ∃ first second target,
      first ∈ S.fine.physicalLabellings ∧
      second ∈ S.fine.physicalLabellings ∧
      target ∈ S.coarse.physicalLabellings ∧
      ¬ kernel first target ≈ kernel second target

namespace FiniteSlabKernel

/-- Push the normalized fine physical law through the finite kernel. -/
def blockedMass
    {S : SlabScalePair} (K : FiniteSlabKernel S)
    (target : EdgeLabelling) : Q' :=
  listQSum
    (fun source => S.fine.normalizedMass source * K.kernel source target)
    S.fine.physicalLabellings

/-- The retained signed discrepancy from the normalized coarse physical law. -/
def remainder
    {S : SlabScalePair} (K : FiniteSlabKernel S)
    (target : EdgeLabelling) : Q' :=
  K.blockedMass target + -(S.coarse.normalizedMass target)

/-- The exact finite `L¹` size of the retained signed remainder. -/
def remainderL1
    {S : SlabScalePair} (K : FiniteSlabKernel S) : Q' :=
  listQSum (fun target => Q'.abs (K.remainder target))
    S.coarse.physicalLabellings

/-- The requested pushforward decomposition is true by the definition of the
retained remainder; no error term is hidden or discarded. -/
theorem pushforward_decomposition
    {S : SlabScalePair} (K : FiniteSlabKernel S)
    (target : EdgeLabelling) :
    K.blockedMass target ≈
      S.coarse.normalizedMass target + K.remainder target := by
  exact Q'.add_sub_cancel_eqv
    (K.blockedMass target) (S.coarse.normalizedMass target)

/-- The complete pushed fine mass is exactly one. -/
theorem blockedMass_total
    {S : SlabScalePair} (K : FiniteSlabKernel S) :
    listQSum K.blockedMass S.coarse.physicalLabellings ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            S.fine.normalizedMass source * K.kernel source target)
          S.coarse.physicalLabellings)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_swap
      (fun source target =>
        S.fine.normalizedMass source * K.kernel source target)
      S.fine.physicalLabellings S.coarse.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum
      (fun source => S.fine.normalizedMass source * 1)
      S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    exact Q'.eqv_trans _ _ _
      (listQSum_mul_left
        (S.fine.normalizedMass source) (K.kernel source)
        S.coarse.physicalLabellings)
      (Q'.mul_eqv_congr_left
        (S.fine.normalizedMass source) _ _
        (K.row_normalized source hsource))
  · exact Q'.eqv_trans _ _ _
      (listQSum_congr_on
        (fun source => S.fine.normalizedMass source * 1)
        S.fine.normalizedMass S.fine.physicalLabellings
        (fun source _ => Q'.mul_one_eqv _))
      S.fine.normalizedMass_total

/-- Every pushed target mass is nonnegative. -/
theorem blockedMass_nonnegative
    {S : SlabScalePair} (K : FiniteSlabKernel S)
    {target : EdgeLabelling}
    (htarget : target ∈ S.coarse.physicalLabellings) :
    (0 : Q') ≤ K.blockedMass target := by
  unfold blockedMass
  apply listQSum_nonnegative_on
  intro source hsource
  exact Q'.mul_nonneg _ _
    (S.fine.normalizedMass_nonnegative source)
    (K.nonnegative source target hsource htarget)

private theorem listQSum_neg {A : Type} (value : A → Q') :
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
          (listQSum_neg value tail)) ?_
      exact Q'.eqv_symm
        (Q'.neg_add_eqv (value head) (listQSum value tail))

/-- Row normalization makes zero total remainder automatic.  The only
remaining content of the remainder gate is its physical identification and
uniform norm, not a separate mass-cancellation hypothesis. -/
theorem remainder_total_eqv_zero
    {S : SlabScalePair} (K : FiniteSlabKernel S) :
    listQSum K.remainder S.coarse.physicalLabellings ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum K.blockedMass S.coarse.physicalLabellings +
      listQSum
        (fun target => -(S.coarse.normalizedMass target))
        S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_add K.blockedMass
      (fun target => -(S.coarse.normalizedMass target))
      S.coarse.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum K.blockedMass S.coarse.physicalLabellings +
      -(listQSum S.coarse.normalizedMass
        S.coarse.physicalLabellings)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (listQSum_neg S.coarse.normalizedMass
        S.coarse.physicalLabellings)
  refine Q'.eqv_trans _ ((1 : Q') + -(1 : Q')) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      K.blockedMass_total
      (Q'.neg_eqv_congr _ _ S.coarse.normalizedMass_total)
  · exact Q'.add_neg_self_eqv 1

private theorem listQSum_mono {A : Type} (lower upper : A → Q') :
    ∀ states : List A,
      (∀ state, state ∈ states → lower state ≤ upper state) →
      listQSum lower states ≤ listQSum upper states
  | [], _ => Q'.le_refl' 0
  | head :: tail, h => by
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _
          (h head List.mem_cons_self))
        (Q'.add_le_add_left _ _ _
          (listQSum_mono lower upper tail
            (fun state hstate =>
              h state (List.mem_cons_of_mem head hstate))))

private theorem remainder_abs_le_mass_sum
    {S : SlabScalePair} (K : FiniteSlabKernel S)
    {target : EdgeLabelling}
    (htarget : target ∈ S.coarse.physicalLabellings) :
    Q'.abs (K.remainder target) ≤
      K.blockedMass target + S.coarse.normalizedMass target := by
  have hblocked := K.blockedMass_nonnegative htarget
  have hcoarse := S.coarse.normalizedMass_nonnegative target
  have htriangle := Q'.abs_add_le'
    (K.blockedMass target) (-(S.coarse.normalizedMass target))
  have hblockedAbs :
      Q'.abs (K.blockedMass target) ≈ K.blockedMass target := by
    unfold Q'.abs
    rw [if_pos hblocked]
    exact Q'.eqv_refl _
  have hcoarseAbs :
      Q'.abs (-(S.coarse.normalizedMass target)) ≈
        S.coarse.normalizedMass target := by
    refine Q'.eqv_trans _ (Q'.abs (S.coarse.normalizedMass target)) _
      (Q'.abs_neg' _) ?_
    unfold Q'.abs
    rw [if_pos hcoarse]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_of_eqv
      (Q'.add_eqv_congr' hblockedAbs hcoarseAbs))

/-- Universal probability-simplex bound for the retained remainder.

The constant `2` is independent of cutoff and volume, but it is deliberately
too large to close CD-3: the analytic target is a vanishing quadratic defect
bound in the RG coordinate. -/
theorem remainderL1_le_two
    {S : SlabScalePair} (K : FiniteSlabKernel S) :
    K.remainderL1 ≤ (2 : Q') := by
  refine Q'.le_trans' K.remainderL1
    (listQSum
      (fun target =>
        K.blockedMass target + S.coarse.normalizedMass target)
      S.coarse.physicalLabellings) (2 : Q') ?_ ?_
  · unfold remainderL1
    apply listQSum_mono
    intro target htarget
    exact K.remainder_abs_le_mass_sum htarget
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _
        (listQSum K.blockedMass S.coarse.physicalLabellings +
          listQSum S.coarse.normalizedMass
            S.coarse.physicalLabellings)
        (2 : Q')
        (listQSum_add K.blockedMass S.coarse.normalizedMass
          S.coarse.physicalLabellings)
        (Q'.eqv_trans _ ((1 : Q') + 1) _
          (Q'.add_eqv_congr'
            K.blockedMass_total S.coarse.normalizedMass_total)
          (Q'.eqv_refl 2)))

end FiniteSlabKernel

end SlabScalePair

end YMGap.Continuum.CompactDualFiniteBlockRemainder

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel.pushforward_decomposition
#print axioms YMGap.Continuum.CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel.blockedMass_total
#print axioms YMGap.Continuum.CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel.blockedMass_nonnegative
#print axioms YMGap.Continuum.CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel.remainder_total_eqv_zero
#print axioms YMGap.Continuum.CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel.remainderL1_le_two
