/-
# Positive-source path expansion of the actual four-cell covariance

The literal paired path carrier still ranges over all fine physical sources.
This module performs the next constructive restriction.  It recursively
attaches the two facts needed by the production kernel to every surviving
source:

* membership in the finite fine physical carrier;
* strict positivity of its physical Gibbs term.

Every omitted source has exactly zero path mass.  Every retained kernel entry
is rewritten as the whole-slab conditional recoupling row, hence as its raw
weight divided by its positive row partition.  The two-replica four-cell path
cross and the complete connected raw cross are unchanged.

This gives the next receiver construction proof-carrying positive sources and
literal coarse targets.  It does not itself construct a successful receiver
column or prove an `O(a)` estimate, continuum measure, OS/GNS reconstruction,
or physical mass gap.

Constructive contract: dependent finite recursion and exact rational
identities only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPaths

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

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

/-! ## 1. The proof-carrying positive fine source carrier -/

/-- A fine physical source carrying both finite-carrier membership and the
strict positivity needed to construct its coherent recoupling row. -/
abbrev PositivePhysicalSource (S : SlabScalePair) :=
  {source : EdgeLabelling //
    source ∈ S.fine.physicalLabellings ∧
      (0 : Q') < S.fine.physicalTerm source}

/-- Constructively retain precisely the positive members of a physical source
list.  The membership transformer avoids any choice of evidence. -/
def positivePhysicalSourcesAux
    (S : SlabScalePair) :
    (sources : List EdgeLabelling) →
      (∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings) →
      List (PositivePhysicalSource S)
  | [], _ => []
  | source :: tail, hphysical =>
      if hpositive : (0 : Q') < S.fine.physicalTerm source then
        ⟨source, hphysical source List.mem_cons_self, hpositive⟩ ::
          positivePhysicalSourcesAux S tail
            (fun item hitem =>
              hphysical item (List.mem_cons_of_mem source hitem))
      else
        positivePhysicalSourcesAux S tail
          (fun item hitem =>
            hphysical item (List.mem_cons_of_mem source hitem))

def positivePhysicalSources (S : SlabScalePair) :
    List (PositivePhysicalSource S) :=
  positivePhysicalSourcesAux S S.fine.physicalLabellings
    (fun _ hsource => hsource)

/-- One retained fine-source to coarse-target path, with the actual kernel
entry exposed as the positive whole-slab conditional recoupling row. -/
def positivePhysicalSourceKernelPathRawMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling)
    (source : PositivePhysicalSource S) : Q' :=
  S.fine.physicalTerm source.1 *
    wholeSlabRecouplingConditionalKernel
      (positiveCoherentSource S hfineCutoff hcoarseCoupling
        source.1 source.2.1 source.2.2)
      target

/-- The surviving path weight literally contains the selected recoupling raw
weight divided by its complete positive row partition. -/
theorem positivePhysicalSourceKernelPathRawMass_eqv_rawRatio
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling)
    (source : PositivePhysicalSource S) :
    positivePhysicalSourceKernelPathRawMass S hfineCutoff
        hcoarseCoupling target source ≈
      S.fine.physicalTerm source.1 *
        Q'.divPos
          (wholeSlabRecouplingRawWeight S source.1 target)
          (wholeSlabRecouplingPartition
            (positiveCoherentSource S hfineCutoff hcoarseCoupling
              source.1 source.2.1 source.2.2))
          (wholeSlabRecouplingPartition_pos
            (positiveCoherentSource S hfineCutoff hcoarseCoupling
              source.1 source.2.1 source.2.2)) := by
  unfold positivePhysicalSourceKernelPathRawMass
    wholeSlabRecouplingConditionalKernel
  exact Q'.eqv_refl _

/-! ## 2. Delete zero source paths and expose every retained row -/

private theorem physicalSourcePathSum_eqv_positiveAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings),
      listQSum
          (fun source =>
            S.fine.physicalTerm source *
              (physicalKernel S hfineCutoff hcoarseCoupling).kernel
                source target)
          sources ≈
        listQSum
          (positivePhysicalSourceKernelPathRawMass S hfineCutoff
            hcoarseCoupling target)
          (positivePhysicalSourcesAux S sources hphysical)
  | [], _ => Q'.eqv_refl 0
  | source :: tail, hphysical => by
      let hsource := hphysical source List.mem_cons_self
      let htail : ∀ item, item ∈ tail →
          item ∈ S.fine.physicalLabellings :=
        fun item hitem =>
          hphysical item (List.mem_cons_of_mem source hitem)
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source
      · simp only [listQSum, positivePhysicalSourcesAux,
          dif_pos hpositive]
        exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left
            (S.fine.physicalTerm source) _ _
            (cutoffOneWholeSlabKernel_eq_positive
              S hfineCutoff hcoarseCoupling hsource hpositive target))
          (physicalSourcePathSum_eqv_positiveAux
            S hfineCutoff hcoarseCoupling target tail htail)
      · simp only [listQSum, positivePhysicalSourcesAux,
          dif_neg hpositive]
        let rowWeight :=
          (physicalKernel S hfineCutoff hcoarseCoupling).kernel
            source target
        refine Q'.eqv_trans _
          (0 + listQSum
            (positivePhysicalSourceKernelPathRawMass S hfineCutoff
              hcoarseCoupling target)
            (positivePhysicalSourcesAux S tail htail)) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.eqv_trans _ (0 * rowWeight) _
              (Q'.mul_eqv_congr_right _ _ rowWeight
                (physicalTerm_eqv_zero_of_not_positive
                  S.fine source hpositive))
              (Q'.zero_mul_eqv rowWeight))
            (physicalSourcePathSum_eqv_positiveAux
              S hfineCutoff hcoarseCoupling target tail htail)
        · exact Q'.eqv_of_eq (Q'.zero_add' _)

theorem physicalSourcePathSum_eqv_positive
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling) :
    listQSum
        (fun source =>
          S.fine.physicalTerm source *
            (physicalKernel S hfineCutoff hcoarseCoupling).kernel
              source target)
        S.fine.physicalLabellings ≈
      listQSum
        (positivePhysicalSourceKernelPathRawMass S hfineCutoff
          hcoarseCoupling target)
        (positivePhysicalSources S) := by
  unfold positivePhysicalSources
  exact physicalSourcePathSum_eqv_positiveAux
    S hfineCutoff hcoarseCoupling target
    S.fine.physicalLabellings (fun _ hsource => hsource)

/-! ## 3. Positive paired source-to-target paths -/

abbrev PositivePhysicalSourcePair (S : SlabScalePair) :=
  PositivePhysicalSource S × PositivePhysicalSource S

abbrev PositivePushedPhysicalTwoReplicaPath (S : SlabScalePair) :=
  PhysicalLabellingPair × PositivePhysicalSourcePair S

def positivePhysicalSourcePairs (S : SlabScalePair) :
    List (PositivePhysicalSourcePair S) :=
  cartesian (positivePhysicalSources S) (positivePhysicalSources S)

def positivePushedFaceRawFourCellSourcePaths
    (S : SlabScalePair) (root target : Nat) :
    List (PositivePushedPhysicalTwoReplicaPath S) :=
  cartesian
    (pushedFaceRawFourCellSourcePairs (S := S) root target)
    (positivePhysicalSourcePairs S)

def positivePushedFaceRawFourCellTargetPaths
    (S : SlabScalePair) (root target : Nat) :
    List (PositivePushedPhysicalTwoReplicaPath S) :=
  cartesian
    (pushedFaceRawFourCellTargetPairs (S := S) root target)
    (positivePhysicalSourcePairs S)

/-- Product of two retained positive conditional-row path weights. -/
def positivePushedPhysicalTwoReplicaPathRawMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (path : PositivePushedPhysicalTwoReplicaPath S) : Q' :=
  positivePhysicalSourceKernelPathRawMass S hfineCutoff
      hcoarseCoupling path.1.1 path.2.1 *
    positivePhysicalSourceKernelPathRawMass S hfineCutoff
      hcoarseCoupling path.1.2 path.2.2

/-- For fixed coarse targets, deleting zero fine sources and specializing all
survivors to their conditional raw rows preserves the paired path mass. -/
theorem pushedPhysicalTwoReplicaSourcePathMass_eqv_positivePathMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (targetPair : PhysicalLabellingPair) :
    listQSum
        (fun sourcePair =>
          pushedPhysicalTwoReplicaPathRawMass
            (physicalKernel S hfineCutoff hcoarseCoupling)
            (targetPair, sourcePair))
        (pushedPhysicalSourcePairs S) ≈
      listQSum
        (fun sourcePair =>
          positivePushedPhysicalTwoReplicaPathRawMass
            S hfineCutoff hcoarseCoupling
            (targetPair, sourcePair))
        (positivePhysicalSourcePairs S) := by
  let leftFull := fun source : EdgeLabelling =>
    S.fine.physicalTerm source *
      (physicalKernel S hfineCutoff hcoarseCoupling).kernel
        source targetPair.1
  let rightFull := fun source : EdgeLabelling =>
    S.fine.physicalTerm source *
      (physicalKernel S hfineCutoff hcoarseCoupling).kernel
        source targetPair.2
  let leftPositive :=
    positivePhysicalSourceKernelPathRawMass S hfineCutoff
      hcoarseCoupling targetPair.1
  let rightPositive :=
    positivePhysicalSourceKernelPathRawMass S hfineCutoff
      hcoarseCoupling targetPair.2
  refine Q'.eqv_trans _
    (listQSum leftFull S.fine.physicalLabellings *
      listQSum rightFull S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_cartesian_product leftFull rightFull
      S.fine.physicalLabellings S.fine.physicalLabellings
  · refine Q'.eqv_trans _
      (listQSum leftPositive (positivePhysicalSources S) *
        listQSum rightPositive (positivePhysicalSources S)) _ ?_ ?_
    · exact mul_eqv_both_local
        (physicalSourcePathSum_eqv_positive
          S hfineCutoff hcoarseCoupling targetPair.1)
        (physicalSourcePathSum_eqv_positive
          S hfineCutoff hcoarseCoupling targetPair.2)
    · exact Q'.eqv_symm
        (listQSum_cartesian_product leftPositive rightPositive
          (positivePhysicalSources S) (positivePhysicalSources S))

theorem pushedFaceRawFourCellSourcePaths_mass_eqv_positivePaths
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (pushedPhysicalTwoReplicaPathRawMass
          (physicalKernel S hfineCutoff hcoarseCoupling))
        (pushedFaceRawFourCellSourcePaths S root target) ≈
      listQSum
        (positivePushedPhysicalTwoReplicaPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positivePushedFaceRawFourCellSourcePaths S root target) := by
  unfold pushedFaceRawFourCellSourcePaths
    positivePushedFaceRawFourCellSourcePaths
  refine Q'.eqv_trans _
    (listQSum
      (fun targetPair =>
        listQSum
          (fun sourcePair =>
            pushedPhysicalTwoReplicaPathRawMass
              (physicalKernel S hfineCutoff hcoarseCoupling)
              (targetPair, sourcePair))
          (pushedPhysicalSourcePairs S))
      (pushedFaceRawFourCellSourcePairs (S := S) root target)) _ ?_ ?_
  · exact listQSum_cartesian_eq_nested_local _ _ _
  · refine Q'.eqv_trans _
      (listQSum
        (fun targetPair =>
          listQSum
            (fun sourcePair =>
              positivePushedPhysicalTwoReplicaPathRawMass
                S hfineCutoff hcoarseCoupling
                (targetPair, sourcePair))
            (positivePhysicalSourcePairs S))
        (pushedFaceRawFourCellSourcePairs (S := S) root target)) _ ?_ ?_
    · apply listQSum_congr
      intro targetPair
      exact pushedPhysicalTwoReplicaSourcePathMass_eqv_positivePathMass
        S hfineCutoff hcoarseCoupling targetPair
    · exact Q'.eqv_symm
        (listQSum_cartesian_eq_nested_local _ _ _)

theorem pushedFaceRawFourCellTargetPaths_mass_eqv_positivePaths
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (pushedPhysicalTwoReplicaPathRawMass
          (physicalKernel S hfineCutoff hcoarseCoupling))
        (pushedFaceRawFourCellTargetPaths S root target) ≈
      listQSum
        (positivePushedPhysicalTwoReplicaPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positivePushedFaceRawFourCellTargetPaths S root target) := by
  unfold pushedFaceRawFourCellTargetPaths
    positivePushedFaceRawFourCellTargetPaths
  refine Q'.eqv_trans _
    (listQSum
      (fun targetPair =>
        listQSum
          (fun sourcePair =>
            pushedPhysicalTwoReplicaPathRawMass
              (physicalKernel S hfineCutoff hcoarseCoupling)
              (targetPair, sourcePair))
          (pushedPhysicalSourcePairs S))
      (pushedFaceRawFourCellTargetPairs (S := S) root target)) _ ?_ ?_
  · exact listQSum_cartesian_eq_nested_local _ _ _
  · refine Q'.eqv_trans _
      (listQSum
        (fun targetPair =>
          listQSum
            (fun sourcePair =>
              positivePushedPhysicalTwoReplicaPathRawMass
                S hfineCutoff hcoarseCoupling
                (targetPair, sourcePair))
            (positivePhysicalSourcePairs S))
        (pushedFaceRawFourCellTargetPairs (S := S) root target)) _ ?_ ?_
    · apply listQSum_congr
      intro targetPair
      exact pushedPhysicalTwoReplicaSourcePathMass_eqv_positivePathMass
        S hfineCutoff hcoarseCoupling targetPair
    · exact Q'.eqv_symm
        (listQSum_cartesian_eq_nested_local _ _ _)

/-! ## 4. The exact positive-path covariance cross -/

def actualPositivePushedFaceRawFourCellPathCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
      (positivePushedPhysicalTwoReplicaPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positivePushedFaceRawFourCellSourcePaths S root target) -
    listQSum
      (positivePushedPhysicalTwoReplicaPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positivePushedFaceRawFourCellTargetPaths S root target)

theorem actualPushedFaceRawFourCellPathCross_eqv_positivePaths
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPushedFaceRawFourCellPathCross S hfineCutoff
        hcoarseCoupling root target ≈
      actualPositivePushedFaceRawFourCellPathCross S hfineCutoff
        hcoarseCoupling root target := by
  unfold actualPushedFaceRawFourCellPathCross
    pushedFaceRawFourCellPathCross
    actualPositivePushedFaceRawFourCellPathCross
  exact sub_eqv_both_local
    (pushedFaceRawFourCellSourcePaths_mass_eqv_positivePaths
      S hfineCutoff hcoarseCoupling root target)
    (pushedFaceRawFourCellTargetPaths_mass_eqv_positivePaths
      S hfineCutoff hcoarseCoupling root target)

/-- The complete connected raw cross with its pushed half represented on the
proof-carrying positive paired-path carrier. -/
def physicalConnectedCovariancePositivePathRawCrossDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  (physicalFaceRawFourCellCross
      S.coarse M.coarseRoot M.coarseTarget *
      S.coarse.physicalPartition) *
      rawCovarianceDenominator S.fine.physicalPartition -
    (actualPositivePushedFaceRawFourCellPathCross S hfineCutoff
      hcoarseCoupling M.coarseRoot M.coarseTarget *
      S.fine.physicalPartition) *
      rawCovarianceDenominator S.coarse.physicalPartition

theorem physicalConnectedCovariancePathRawCrossDefect_eqv_positivePaths
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovariancePathRawCrossDefect
        S hfineCutoff hcoarseCoupling M ≈
      physicalConnectedCovariancePositivePathRawCrossDefect
        S hfineCutoff hcoarseCoupling M := by
  unfold physicalConnectedCovariancePathRawCrossDefect
    physicalConnectedCovariancePositivePathRawCrossDefect
  exact sub_eqv_both_local (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_right _ _
      (rawCovarianceDenominator S.coarse.physicalPartition)
      (Q'.mul_eqv_congr_right _ _ S.fine.physicalPartition
        (actualPushedFaceRawFourCellPathCross_eqv_positivePaths
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget)))

theorem physicalConnectedCovarianceRawCrossDefect_eqv_positivePathRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovarianceRawCrossDefect S hfineCutoff
        hcoarseCoupling M ≈
      physicalConnectedCovariancePositivePathRawCrossDefect
        S hfineCutoff hcoarseCoupling M :=
  Q'.eqv_trans _ _ _
    (physicalConnectedCovarianceRawCrossDefect_eqv_pathRawCross
      S hfineCutoff hcoarseCoupling M)
    (physicalConnectedCovariancePathRawCrossDefect_eqv_positivePaths
      S hfineCutoff hcoarseCoupling M)

/-- A relative bound on the proof-carrying positive paired paths is enough for
the exact connected pushed-law remainder estimate. -/
theorem centeredCylinderRemainder_physicalKernel_abs_le_of_positivePathRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (budget : Q')
    (hcross :
      Q'.abs
          (physicalConnectedCovariancePositivePathRawCrossDefect
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
        (physicalConnectedCovarianceRawCrossDefect_eqv_positivePathRawCross
          S hfineCutoff hcoarseCoupling M)))
    hcross

#print axioms PositivePhysicalSource
#print axioms positivePhysicalSourcesAux
#print axioms positivePhysicalSources
#print axioms positivePhysicalSourceKernelPathRawMass
#print axioms positivePhysicalSourceKernelPathRawMass_eqv_rawRatio
#print axioms physicalSourcePathSum_eqv_positive
#print axioms PositivePhysicalSourcePair
#print axioms PositivePushedPhysicalTwoReplicaPath
#print axioms positivePhysicalSourcePairs
#print axioms positivePushedFaceRawFourCellSourcePaths
#print axioms positivePushedFaceRawFourCellTargetPaths
#print axioms positivePushedPhysicalTwoReplicaPathRawMass
#print axioms pushedPhysicalTwoReplicaSourcePathMass_eqv_positivePathMass
#print axioms pushedFaceRawFourCellSourcePaths_mass_eqv_positivePaths
#print axioms pushedFaceRawFourCellTargetPaths_mass_eqv_positivePaths
#print axioms actualPositivePushedFaceRawFourCellPathCross
#print axioms actualPushedFaceRawFourCellPathCross_eqv_positivePaths
#print axioms physicalConnectedCovariancePositivePathRawCrossDefect
#print axioms physicalConnectedCovariancePathRawCrossDefect_eqv_positivePaths
#print axioms physicalConnectedCovarianceRawCrossDefect_eqv_positivePathRawCross
#print axioms centeredCylinderRemainder_physicalKernel_abs_le_of_positivePathRawCross

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
