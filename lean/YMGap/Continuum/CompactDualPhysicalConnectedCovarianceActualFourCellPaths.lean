/-
# Source-to-target path expansion of the actual four-cell covariance

The pushed four-cell determinant is a difference of raw masses on pairs of
coarse outputs.  Each coarse-output mass is itself a sum over fine physical
sources.  This module performs the missing finite Fubini step: it expands the
two output masses into a literal two-replica path carrier

  ((coarse target 1, coarse target 2),
   (fine source 1, fine source 2)).

The path weight is the product of the two fine physical source terms and the
two actual kernel entries.  Thus the exact receiver-column frontier now has
both endpoints in its type.  A receiver map or contraction estimate on this
carrier remains open; in particular, this expansion does not identify these
paths with the earlier same-datum paired recoupling carrier.

Constructive contract: finite Cartesian lists and exact rational Fubini only;
no choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPaths

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B → Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum
        (fun a => listQSum (fun b => value (a, b)) right)
        left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr
  intro a
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-! ## 1. Literal two-replica paths -/

abbrev PhysicalLabellingPair := EdgeLabelling × EdgeLabelling

/-- A path stores its pair of coarse outputs first and its pair of fine
sources second. -/
abbrev PushedPhysicalTwoReplicaPath :=
  PhysicalLabellingPair × PhysicalLabellingPair

def pushedPhysicalSourcePairs (S : SlabScalePair) :
    List PhysicalLabellingPair :=
  cartesian S.fine.physicalLabellings S.fine.physicalLabellings

def pushedFaceRawFourCellSourcePaths
    (S : SlabScalePair) (root target : Nat) :
    List PushedPhysicalTwoReplicaPath :=
  cartesian
    (pushedFaceRawFourCellSourcePairs (S := S) root target)
    (pushedPhysicalSourcePairs S)

def pushedFaceRawFourCellTargetPaths
    (S : SlabScalePair) (root target : Nat) :
    List PushedPhysicalTwoReplicaPath :=
  cartesian
    (pushedFaceRawFourCellTargetPairs (S := S) root target)
    (pushedPhysicalSourcePairs S)

/-- Product weight of two fine-source to coarse-target kernel paths. -/
def pushedPhysicalTwoReplicaPathRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (path : PushedPhysicalTwoReplicaPath) : Q' :=
  (S.fine.physicalTerm path.2.1 *
      K.kernel path.2.1 path.1.1) *
    (S.fine.physicalTerm path.2.2 *
      K.kernel path.2.2 path.1.2)

/-! ## 2. Expand every output pair into its source paths -/

/-- For one fixed pair of coarse targets, summing the literal two-replica
paths over both fine sources gives exactly the product pushed target mass. -/
theorem pushedPhysicalTwoReplicaSourcePathMass_eqv_targetPairRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (targetPair : PhysicalLabellingPair) :
    listQSum
        (fun sourcePair =>
          pushedPhysicalTwoReplicaPathRawMass K
            (targetPair, sourcePair))
        (pushedPhysicalSourcePairs S) ≈
      pushedPhysicalTargetPairRawMass K targetPair := by
  unfold pushedPhysicalSourcePairs pushedPhysicalTwoReplicaPathRawMass
    pushedPhysicalTargetPairRawMass pushedPhysicalTargetRawMass
  exact listQSum_cartesian_product
    (fun source =>
      S.fine.physicalTerm source * K.kernel source targetPair.1)
    (fun source =>
      S.fine.physicalTerm source * K.kernel source targetPair.2)
    S.fine.physicalLabellings S.fine.physicalLabellings

/-- The `TT x FF` coarse-output pair mass is exactly the mass of all literal
two-replica paths ending in that cell. -/
theorem pushedFaceRawFourCellSourcePaths_mass_eqv_pair_mass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    listQSum (pushedPhysicalTwoReplicaPathRawMass K)
        (pushedFaceRawFourCellSourcePaths S root target) ≈
      listQSum (pushedPhysicalTargetPairRawMass K)
        (pushedFaceRawFourCellSourcePairs
          (S := S) root target) := by
  unfold pushedFaceRawFourCellSourcePaths
  refine Q'.eqv_trans _
    (listQSum
      (fun targetPair =>
        listQSum
          (fun sourcePair =>
            pushedPhysicalTwoReplicaPathRawMass K
              (targetPair, sourcePair))
          (pushedPhysicalSourcePairs S))
      (pushedFaceRawFourCellSourcePairs
        (S := S) root target)) _ ?_ ?_
  · exact listQSum_cartesian_eq_nested_local
      (pushedPhysicalTwoReplicaPathRawMass K)
      (pushedFaceRawFourCellSourcePairs
        (S := S) root target)
      (pushedPhysicalSourcePairs S)
  · apply listQSum_congr
    intro targetPair
    exact pushedPhysicalTwoReplicaSourcePathMass_eqv_targetPairRawMass
      K targetPair

/-- The `FT x TF` opposite coarse-output pair mass is exactly the mass of all
literal two-replica paths ending in that cell. -/
theorem pushedFaceRawFourCellTargetPaths_mass_eqv_pair_mass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    listQSum (pushedPhysicalTwoReplicaPathRawMass K)
        (pushedFaceRawFourCellTargetPaths S root target) ≈
      listQSum (pushedPhysicalTargetPairRawMass K)
        (pushedFaceRawFourCellTargetPairs
          (S := S) root target) := by
  unfold pushedFaceRawFourCellTargetPaths
  refine Q'.eqv_trans _
    (listQSum
      (fun targetPair =>
        listQSum
          (fun sourcePair =>
            pushedPhysicalTwoReplicaPathRawMass K
              (targetPair, sourcePair))
          (pushedPhysicalSourcePairs S))
      (pushedFaceRawFourCellTargetPairs
        (S := S) root target)) _ ?_ ?_
  · exact listQSum_cartesian_eq_nested_local
      (pushedPhysicalTwoReplicaPathRawMass K)
      (pushedFaceRawFourCellTargetPairs
        (S := S) root target)
      (pushedPhysicalSourcePairs S)
  · apply listQSum_congr
    intro targetPair
    exact pushedPhysicalTwoReplicaSourcePathMass_eqv_targetPairRawMass
      K targetPair

/-- Exact path form of the generic pushed four-cell determinant. -/
def pushedFaceRawFourCellPathCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  listQSum (pushedPhysicalTwoReplicaPathRawMass K)
      (pushedFaceRawFourCellSourcePaths S root target) -
    listQSum (pushedPhysicalTwoReplicaPathRawMass K)
      (pushedFaceRawFourCellTargetPaths S root target)

theorem pushedFaceRawFourCellCross_eqv_pathCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    pushedFaceRawFourCellCross K root target ≈
      pushedFaceRawFourCellPathCross K root target := by
  refine Q'.eqv_trans _
    (listQSum (pushedPhysicalTargetPairRawMass K)
          (pushedFaceRawFourCellSourcePairs
            (S := S) root target) -
      listQSum (pushedPhysicalTargetPairRawMass K)
        (pushedFaceRawFourCellTargetPairs
          (S := S) root target)) _ ?_ ?_
  · exact pushedFaceRawFourCellCross_eqv_pair_mass_difference
      K root target
  · unfold pushedFaceRawFourCellPathCross
    exact sub_eqv_both_local
      (Q'.eqv_symm
        (pushedFaceRawFourCellSourcePaths_mass_eqv_pair_mass
          K root target))
      (Q'.eqv_symm
        (pushedFaceRawFourCellTargetPaths_mass_eqv_pair_mass
          K root target))

/-! ## 3. Specialize the path carrier to the production kernel -/

def actualPushedFaceRawFourCellPathCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  pushedFaceRawFourCellPathCross
    (physicalKernel S hfineCutoff hcoarseCoupling) root target

/-- The positive-row raw-ratio determinant is exactly the difference of
literal two-replica source-to-target path masses. -/
theorem actualPushedFaceRawFourCellCross_eqv_pathCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPushedFaceRawFourCellCross S hfineCutoff
        hcoarseCoupling root target ≈
      actualPushedFaceRawFourCellPathCross S hfineCutoff
        hcoarseCoupling root target := by
  refine Q'.eqv_trans _
    (pushedFaceRawFourCellCross
      (physicalKernel S hfineCutoff hcoarseCoupling) root target) _ ?_ ?_
  · exact Q'.eqv_symm
      (pushedFaceRawFourCellCross_physicalKernel_eqv_actualRaw
        S hfineCutoff hcoarseCoupling root target)
  · exact pushedFaceRawFourCellCross_eqv_pathCross
      (physicalKernel S hfineCutoff hcoarseCoupling) root target

theorem actualPushedFaceRawCovarianceNumerator_eqv_pathCross_mul_partition
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPushedFaceRawCovarianceNumerator S hfineCutoff
        hcoarseCoupling root target ≈
      actualPushedFaceRawFourCellPathCross S hfineCutoff
          hcoarseCoupling root target * S.fine.physicalPartition := by
  refine Q'.eqv_trans _
    (actualPushedFaceRawFourCellCross S hfineCutoff
        hcoarseCoupling root target * S.fine.physicalPartition) _ ?_ ?_
  · exact
      actualPushedFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
        S hfineCutoff hcoarseCoupling root target
  · exact Q'.mul_eqv_congr_right _ _ S.fine.physicalPartition
      (actualPushedFaceRawFourCellCross_eqv_pathCross
        S hfineCutoff hcoarseCoupling root target)

/-! ## 4. Complete connected path raw cross -/

/-- Connected defect with the pushed four-cell determinant replaced by its
literal two-replica source-to-target path sum. -/
def physicalConnectedCovariancePathRawCrossDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  (physicalFaceRawFourCellCross
      S.coarse M.coarseRoot M.coarseTarget *
      S.coarse.physicalPartition) *
      rawCovarianceDenominator S.fine.physicalPartition -
    (actualPushedFaceRawFourCellPathCross S hfineCutoff
      hcoarseCoupling M.coarseRoot M.coarseTarget *
      S.fine.physicalPartition) *
      rawCovarianceDenominator S.coarse.physicalPartition

theorem physicalConnectedCovarianceFourCellRawCrossDefect_eqv_pathRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovarianceFourCellRawCrossDefect
        S hfineCutoff hcoarseCoupling M ≈
      physicalConnectedCovariancePathRawCrossDefect
        S hfineCutoff hcoarseCoupling M := by
  unfold physicalConnectedCovarianceFourCellRawCrossDefect
    physicalConnectedCovariancePathRawCrossDefect
  exact sub_eqv_both_local (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_right _ _
      (rawCovarianceDenominator S.coarse.physicalPartition)
      (Q'.mul_eqv_congr_right _ _ S.fine.physicalPartition
        (actualPushedFaceRawFourCellCross_eqv_pathCross
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget)))

theorem physicalConnectedCovarianceRawCrossDefect_eqv_pathRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovarianceRawCrossDefect S hfineCutoff
        hcoarseCoupling M ≈
      physicalConnectedCovariancePathRawCrossDefect
        S hfineCutoff hcoarseCoupling M :=
  Q'.eqv_trans _ _ _
    (physicalConnectedCovarianceRawCrossDefect_eqv_fourCellRawCross
      S hfineCutoff hcoarseCoupling M)
    (physicalConnectedCovarianceFourCellRawCrossDefect_eqv_pathRawCross
      S hfineCutoff hcoarseCoupling M)

/-- A relative estimate on the literal paired source-to-target path cross is
enough for the exact connected pushed-law remainder bound. -/
theorem centeredCylinderRemainder_physicalKernel_abs_le_of_pathRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (budget : Q')
    (hcross :
      Q'.abs
          (physicalConnectedCovariancePathRawCrossDefect
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
        (physicalConnectedCovarianceRawCrossDefect_eqv_pathRawCross
          S hfineCutoff hcoarseCoupling M)))
    hcross

#print axioms pushedPhysicalSourcePairs
#print axioms pushedFaceRawFourCellSourcePaths
#print axioms pushedFaceRawFourCellTargetPaths
#print axioms pushedPhysicalTwoReplicaPathRawMass
#print axioms pushedPhysicalTwoReplicaSourcePathMass_eqv_targetPairRawMass
#print axioms pushedFaceRawFourCellSourcePaths_mass_eqv_pair_mass
#print axioms pushedFaceRawFourCellTargetPaths_mass_eqv_pair_mass
#print axioms pushedFaceRawFourCellPathCross
#print axioms pushedFaceRawFourCellCross_eqv_pathCross
#print axioms actualPushedFaceRawFourCellPathCross
#print axioms actualPushedFaceRawFourCellCross_eqv_pathCross
#print axioms actualPushedFaceRawCovarianceNumerator_eqv_pathCross_mul_partition
#print axioms physicalConnectedCovariancePathRawCrossDefect
#print axioms physicalConnectedCovarianceFourCellRawCrossDefect_eqv_pathRawCross
#print axioms physicalConnectedCovarianceRawCrossDefect_eqv_pathRawCross
#print axioms centeredCylinderRemainder_physicalKernel_abs_le_of_pathRawCross

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPaths
