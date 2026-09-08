/-
# Accepted-fiber expansion of the positive actual four-cell paths

The positive path carrier records the two fine physical sources and their
coarse kernel targets, but the existing successful receiver-column machinery
acts on accepted fine-intertwiner assignments over those physical sources.
This module performs the exact missing disintegration.  Each positive source
is paired with every accepted assignment in its literal finite fiber, and the
fiber weight is placed before the same whole-slab conditional kernel entry.

Summing the accepted fiber recovers the positive physical path mass exactly,
first for one source, then for the paired four-cell path cross, and finally for
the complete connected raw-cross defect.  Every expanded source also projects
constructively to the attached expanded-source type used by the same-datum
receiver theory, with definitionally equal fine-source weight.

This does not orient an expanded path at a chosen observable face, identify a
coarse kernel target with a same-datum receiver target, or prove a receiver
weight comparison.  It proves no `O(a)` estimate, continuum measure, OS/GNS
reconstruction, or physical mass gap.

Constructive contract: dependent finite attachment and exact rational Fubini
only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
import YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
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

/-! ## 1. Positive sources with accepted fine-intertwiner assignments -/

/-- A positive physical source together with a proof-carrying accepted
fine-intertwiner assignment above it. -/
abbrev PositiveExpandedPhysicalSource (S : SlabScalePair) :=
  Sigma fun source : PositivePhysicalSource S =>
    {assignment : SlabFusionWitnessAssignment //
      assignment ∈ slabFineFusionWitnesses S.fine source.1}

/-- The complete accepted assignment fiber above one positive source. -/
def positiveExpandedPhysicalSourceBlock
    (S : SlabScalePair) (source : PositivePhysicalSource S) :
    List (PositiveExpandedPhysicalSource S) :=
  (slabFineFusionWitnesses S.fine source.1).attach.map fun assignment =>
    ⟨source, assignment⟩

/-- The positive physical source enumeration with every accepted assignment
made explicit. -/
def positiveExpandedPhysicalSources (S : SlabScalePair) :
    List (PositiveExpandedPhysicalSource S) :=
  (positivePhysicalSources S).flatMap
    (positiveExpandedPhysicalSourceBlock S)

/-- Forget positivity and expose the exact attached expanded-source entry
used by the same-datum receiver-column theory. -/
def positiveExpandedPhysicalSourceEntry
    {S : SlabScalePair} (source : PositiveExpandedPhysicalSource S) :
    SlabExpandedFineSourceEntry S.fine :=
  ⟨(source.1.1, source.2.1),
    mem_slabExpandedFineSources_iff.mpr
      ⟨source.1.2.1, source.2.2⟩⟩

/-- The fine-source factor of an expanded path is the literal retained
intertwiner fiber weight. -/
def positiveExpandedPhysicalSourceWeight
    (S : SlabScalePair) (source : PositiveExpandedPhysicalSource S) : Q' :=
  retainedFineIntertwinerPhysicalFiberWeight
    S.fine source.1.1 source.2.1

/-- Projection to the established receiver source universe preserves the
fine-source weight definitionally. -/
theorem positiveExpandedPhysicalSourceEntry_weight_eq
    {S : SlabScalePair} (source : PositiveExpandedPhysicalSource S) :
    slabExpandedFineEntryWeight S.fine
        (positiveExpandedPhysicalSourceEntry source) =
      positiveExpandedPhysicalSourceWeight S source :=
  rfl

/-- The attached accepted fiber above a fixed positive source sums to its
genuine corrected-slab physical term. -/
theorem positiveExpandedPhysicalSourceBlock_weight_total
    (S : SlabScalePair) (source : PositivePhysicalSource S) :
    listQSum
        (positiveExpandedPhysicalSourceWeight S)
        (positiveExpandedPhysicalSourceBlock S source) ≈
      S.fine.physicalTerm source.1 := by
  unfold positiveExpandedPhysicalSourceBlock
    positiveExpandedPhysicalSourceWeight
  rw [listQSum_map]
  change
    listQSum
        (fun assignment :
          {item // item ∈ slabFineFusionWitnesses S.fine source.1} =>
          retainedFineIntertwinerPhysicalFiberWeight
            S.fine source.1 assignment.1)
        (slabFineFusionWitnesses S.fine source.1).attach ≈
      S.fine.physicalTerm source.1
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq
      (listQSum_attach
        (retainedFineIntertwinerPhysicalFiberWeight S.fine source.1)
        (slabFineFusionWitnesses S.fine source.1)))
    (retainedFineIntertwinerPhysicalFiberWeight_total S.fine source.1)

/-! ## 2. Exact one-replica path disintegration -/

/-- One accepted-fiber contribution followed by the same positive
fine-source to coarse-target conditional row. -/
def positiveExpandedSourceKernelPathRawMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling)
    (source : PositiveExpandedPhysicalSource S) : Q' :=
  positiveExpandedPhysicalSourceWeight S source *
    wholeSlabRecouplingConditionalKernel
      (positiveCoherentSource S hfineCutoff hcoarseCoupling
        source.1.1 source.1.2.1 source.1.2.2)
      target

/-- Summing the accepted assignments above one fixed positive source exactly
recovers that source's physical conditional-kernel path mass. -/
theorem positiveExpandedSourceKernelPathBlock_mass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling)
    (source : PositivePhysicalSource S) :
    listQSum
        (positiveExpandedSourceKernelPathRawMass
          S hfineCutoff hcoarseCoupling target)
        (positiveExpandedPhysicalSourceBlock S source) ≈
      positivePhysicalSourceKernelPathRawMass
        S hfineCutoff hcoarseCoupling target source := by
  let row :=
    wholeSlabRecouplingConditionalKernel
      (positiveCoherentSource S hfineCutoff hcoarseCoupling
        source.1 source.2.1 source.2.2)
      target
  unfold positiveExpandedPhysicalSourceBlock
    positiveExpandedSourceKernelPathRawMass
    positiveExpandedPhysicalSourceWeight
  rw [listQSum_map]
  change
    listQSum
        (fun assignment :
          {item // item ∈ slabFineFusionWitnesses S.fine source.1} =>
          retainedFineIntertwinerPhysicalFiberWeight
              S.fine source.1 assignment.1 * row)
        (slabFineFusionWitnesses S.fine source.1).attach ≈
      S.fine.physicalTerm source.1 * row
  refine Q'.eqv_trans _
    (listQSum
      (fun assignment =>
        retainedFineIntertwinerPhysicalFiberWeight
          S.fine source.1 assignment * row)
      (slabFineFusionWitnesses S.fine source.1)) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (listQSum_attach
        (fun assignment =>
          retainedFineIntertwinerPhysicalFiberWeight
            S.fine source.1 assignment * row)
        (slabFineFusionWitnesses S.fine source.1))
  · exact Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (retainedFineIntertwinerPhysicalFiberWeight S.fine source.1)
        row (slabFineFusionWitnesses S.fine source.1))
      (Q'.mul_eqv_congr_right _ _ row
        (retainedFineIntertwinerPhysicalFiberWeight_total
          S.fine source.1))

/-- Expanding all accepted fibers preserves the complete one-replica
positive-source to fixed-target path mass. -/
theorem positivePhysicalSourcePathMass_eqv_positiveExpandedPathMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling) :
    listQSum
        (positivePhysicalSourceKernelPathRawMass
          S hfineCutoff hcoarseCoupling target)
        (positivePhysicalSources S) ≈
      listQSum
        (positiveExpandedSourceKernelPathRawMass
          S hfineCutoff hcoarseCoupling target)
        (positiveExpandedPhysicalSources S) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (positiveExpandedSourceKernelPathRawMass
            S hfineCutoff hcoarseCoupling target)
          (positiveExpandedPhysicalSourceBlock S source))
      (positivePhysicalSources S)) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact Q'.eqv_symm
      (positiveExpandedSourceKernelPathBlock_mass
        S hfineCutoff hcoarseCoupling target source)
  · unfold positiveExpandedPhysicalSources
    exact Q'.eqv_symm
      (listQSum_flatMap
        (positiveExpandedSourceKernelPathRawMass
          S hfineCutoff hcoarseCoupling target)
        (positiveExpandedPhysicalSourceBlock S)
        (positivePhysicalSources S))

/-! ## 3. Accepted-fiber paired four-cell paths -/

abbrev PositiveExpandedPhysicalSourcePair (S : SlabScalePair) :=
  PositiveExpandedPhysicalSource S × PositiveExpandedPhysicalSource S

abbrev PositiveExpandedPushedPhysicalTwoReplicaPath (S : SlabScalePair) :=
  PhysicalLabellingPair × PositiveExpandedPhysicalSourcePair S

def positiveExpandedPhysicalSourcePairs (S : SlabScalePair) :
    List (PositiveExpandedPhysicalSourcePair S) :=
  cartesian
    (positiveExpandedPhysicalSources S)
    (positiveExpandedPhysicalSources S)

def positiveExpandedPushedFaceRawFourCellSourcePaths
    (S : SlabScalePair) (root target : Nat) :
    List (PositiveExpandedPushedPhysicalTwoReplicaPath S) :=
  cartesian
    (pushedFaceRawFourCellSourcePairs (S := S) root target)
    (positiveExpandedPhysicalSourcePairs S)

def positiveExpandedPushedFaceRawFourCellTargetPaths
    (S : SlabScalePair) (root target : Nat) :
    List (PositiveExpandedPushedPhysicalTwoReplicaPath S) :=
  cartesian
    (pushedFaceRawFourCellTargetPairs (S := S) root target)
    (positiveExpandedPhysicalSourcePairs S)

/-- Product of two accepted-fiber conditional-row path contributions. -/
def positiveExpandedPushedPhysicalTwoReplicaPathRawMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (path : PositiveExpandedPushedPhysicalTwoReplicaPath S) : Q' :=
  positiveExpandedSourceKernelPathRawMass S hfineCutoff
      hcoarseCoupling path.1.1 path.2.1 *
    positiveExpandedSourceKernelPathRawMass S hfineCutoff
      hcoarseCoupling path.1.2 path.2.2

/-- For fixed coarse targets, expanding both accepted fibers preserves the
positive paired path mass exactly. -/
theorem positivePushedPhysicalTwoReplicaPathMass_eqv_expandedPathMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (targetPair : PhysicalLabellingPair) :
    listQSum
        (fun sourcePair =>
          positivePushedPhysicalTwoReplicaPathRawMass
            S hfineCutoff hcoarseCoupling
            (targetPair, sourcePair))
        (positivePhysicalSourcePairs S) ≈
      listQSum
        (fun sourcePair =>
          positiveExpandedPushedPhysicalTwoReplicaPathRawMass
            S hfineCutoff hcoarseCoupling
            (targetPair, sourcePair))
        (positiveExpandedPhysicalSourcePairs S) := by
  let leftPositive :=
    positivePhysicalSourceKernelPathRawMass S hfineCutoff
      hcoarseCoupling targetPair.1
  let rightPositive :=
    positivePhysicalSourceKernelPathRawMass S hfineCutoff
      hcoarseCoupling targetPair.2
  let leftExpanded :=
    positiveExpandedSourceKernelPathRawMass S hfineCutoff
      hcoarseCoupling targetPair.1
  let rightExpanded :=
    positiveExpandedSourceKernelPathRawMass S hfineCutoff
      hcoarseCoupling targetPair.2
  refine Q'.eqv_trans _
    (listQSum leftPositive (positivePhysicalSources S) *
      listQSum rightPositive (positivePhysicalSources S)) _ ?_ ?_
  · exact listQSum_cartesian_product leftPositive rightPositive
      (positivePhysicalSources S) (positivePhysicalSources S)
  · refine Q'.eqv_trans _
      (listQSum leftExpanded (positiveExpandedPhysicalSources S) *
        listQSum rightExpanded (positiveExpandedPhysicalSources S)) _ ?_ ?_
    · exact mul_eqv_both_local
        (positivePhysicalSourcePathMass_eqv_positiveExpandedPathMass
          S hfineCutoff hcoarseCoupling targetPair.1)
        (positivePhysicalSourcePathMass_eqv_positiveExpandedPathMass
          S hfineCutoff hcoarseCoupling targetPair.2)
    · exact Q'.eqv_symm
        (listQSum_cartesian_product leftExpanded rightExpanded
          (positiveExpandedPhysicalSources S)
          (positiveExpandedPhysicalSources S))

theorem positivePushedFaceRawFourCellSourcePaths_mass_eqv_expandedPaths
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (positivePushedPhysicalTwoReplicaPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positivePushedFaceRawFourCellSourcePaths S root target) ≈
      listQSum
        (positiveExpandedPushedPhysicalTwoReplicaPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedPushedFaceRawFourCellSourcePaths
          S root target) := by
  unfold positivePushedFaceRawFourCellSourcePaths
    positiveExpandedPushedFaceRawFourCellSourcePaths
  refine Q'.eqv_trans _
    (listQSum
      (fun targetPair =>
        listQSum
          (fun sourcePair =>
            positivePushedPhysicalTwoReplicaPathRawMass
              S hfineCutoff hcoarseCoupling
              (targetPair, sourcePair))
          (positivePhysicalSourcePairs S))
      (pushedFaceRawFourCellSourcePairs (S := S) root target)) _ ?_ ?_
  · exact listQSum_cartesian_eq_nested_local _ _ _
  · refine Q'.eqv_trans _
      (listQSum
        (fun targetPair =>
          listQSum
            (fun sourcePair =>
              positiveExpandedPushedPhysicalTwoReplicaPathRawMass
                S hfineCutoff hcoarseCoupling
                (targetPair, sourcePair))
            (positiveExpandedPhysicalSourcePairs S))
        (pushedFaceRawFourCellSourcePairs (S := S) root target)) _ ?_ ?_
    · apply listQSum_congr
      intro targetPair
      exact positivePushedPhysicalTwoReplicaPathMass_eqv_expandedPathMass
        S hfineCutoff hcoarseCoupling targetPair
    · exact Q'.eqv_symm
        (listQSum_cartesian_eq_nested_local _ _ _)

theorem positivePushedFaceRawFourCellTargetPaths_mass_eqv_expandedPaths
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (positivePushedPhysicalTwoReplicaPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positivePushedFaceRawFourCellTargetPaths S root target) ≈
      listQSum
        (positiveExpandedPushedPhysicalTwoReplicaPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedPushedFaceRawFourCellTargetPaths
          S root target) := by
  unfold positivePushedFaceRawFourCellTargetPaths
    positiveExpandedPushedFaceRawFourCellTargetPaths
  refine Q'.eqv_trans _
    (listQSum
      (fun targetPair =>
        listQSum
          (fun sourcePair =>
            positivePushedPhysicalTwoReplicaPathRawMass
              S hfineCutoff hcoarseCoupling
              (targetPair, sourcePair))
          (positivePhysicalSourcePairs S))
      (pushedFaceRawFourCellTargetPairs (S := S) root target)) _ ?_ ?_
  · exact listQSum_cartesian_eq_nested_local _ _ _
  · refine Q'.eqv_trans _
      (listQSum
        (fun targetPair =>
          listQSum
            (fun sourcePair =>
              positiveExpandedPushedPhysicalTwoReplicaPathRawMass
                S hfineCutoff hcoarseCoupling
                (targetPair, sourcePair))
            (positiveExpandedPhysicalSourcePairs S))
        (pushedFaceRawFourCellTargetPairs (S := S) root target)) _ ?_ ?_
    · apply listQSum_congr
      intro targetPair
      exact positivePushedPhysicalTwoReplicaPathMass_eqv_expandedPathMass
        S hfineCutoff hcoarseCoupling targetPair
    · exact Q'.eqv_symm
        (listQSum_cartesian_eq_nested_local _ _ _)

/-! ## 4. The exact accepted-fiber covariance cross -/

def actualPositiveExpandedPushedFaceRawFourCellPathCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
      (positiveExpandedPushedPhysicalTwoReplicaPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positiveExpandedPushedFaceRawFourCellSourcePaths S root target) -
    listQSum
      (positiveExpandedPushedPhysicalTwoReplicaPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positiveExpandedPushedFaceRawFourCellTargetPaths S root target)

theorem actualPositivePushedFaceRawFourCellPathCross_eqv_expandedPaths
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositivePushedFaceRawFourCellPathCross S hfineCutoff
        hcoarseCoupling root target ≈
      actualPositiveExpandedPushedFaceRawFourCellPathCross S hfineCutoff
        hcoarseCoupling root target := by
  unfold actualPositivePushedFaceRawFourCellPathCross
    actualPositiveExpandedPushedFaceRawFourCellPathCross
  exact sub_eqv_both_local
    (positivePushedFaceRawFourCellSourcePaths_mass_eqv_expandedPaths
      S hfineCutoff hcoarseCoupling root target)
    (positivePushedFaceRawFourCellTargetPaths_mass_eqv_expandedPaths
      S hfineCutoff hcoarseCoupling root target)

/-- The complete connected raw cross with the pushed half represented on
accepted, proof-carrying fine-intertwiner fibers. -/
def physicalConnectedCovariancePositiveExpandedPathRawCrossDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  (physicalFaceRawFourCellCross
      S.coarse M.coarseRoot M.coarseTarget *
      S.coarse.physicalPartition) *
      rawCovarianceDenominator S.fine.physicalPartition -
    (actualPositiveExpandedPushedFaceRawFourCellPathCross S hfineCutoff
      hcoarseCoupling M.coarseRoot M.coarseTarget *
      S.fine.physicalPartition) *
      rawCovarianceDenominator S.coarse.physicalPartition

theorem physicalConnectedCovariancePositivePathRawCrossDefect_eqv_expandedPaths
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovariancePositivePathRawCrossDefect
        S hfineCutoff hcoarseCoupling M ≈
      physicalConnectedCovariancePositiveExpandedPathRawCrossDefect
        S hfineCutoff hcoarseCoupling M := by
  unfold physicalConnectedCovariancePositivePathRawCrossDefect
    physicalConnectedCovariancePositiveExpandedPathRawCrossDefect
  exact sub_eqv_both_local (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_right _ _
      (rawCovarianceDenominator S.coarse.physicalPartition)
      (Q'.mul_eqv_congr_right _ _ S.fine.physicalPartition
        (actualPositivePushedFaceRawFourCellPathCross_eqv_expandedPaths
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget)))

theorem physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedPathRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovarianceRawCrossDefect S hfineCutoff
        hcoarseCoupling M ≈
      physicalConnectedCovariancePositiveExpandedPathRawCrossDefect
        S hfineCutoff hcoarseCoupling M :=
  Q'.eqv_trans _ _ _
    (physicalConnectedCovarianceRawCrossDefect_eqv_positivePathRawCross
      S hfineCutoff hcoarseCoupling M)
    (physicalConnectedCovariancePositivePathRawCrossDefect_eqv_expandedPaths
      S hfineCutoff hcoarseCoupling M)

/-- A relative bound on the accepted-fiber paired paths is enough for the
exact connected pushed-law remainder estimate. -/
theorem centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedPathRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (budget : Q')
    (hcross :
      Q'.abs
          (physicalConnectedCovariancePositiveExpandedPathRawCrossDefect
            S hfineCutoff hcoarseCoupling M) ≤
        budget * connectedCovarianceRawCrossDenominator S) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      budget := by
  apply centeredCylinderRemainder_physicalKernel_abs_le_of_positivePathRawCross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (physicalConnectedCovariancePositivePathRawCrossDefect_eqv_expandedPaths
          S hfineCutoff hcoarseCoupling M)))
    hcross

#print axioms PositiveExpandedPhysicalSource
#print axioms positiveExpandedPhysicalSourceBlock
#print axioms positiveExpandedPhysicalSources
#print axioms positiveExpandedPhysicalSourceEntry
#print axioms positiveExpandedPhysicalSourceWeight
#print axioms positiveExpandedPhysicalSourceEntry_weight_eq
#print axioms positiveExpandedPhysicalSourceBlock_weight_total
#print axioms positiveExpandedSourceKernelPathRawMass
#print axioms positiveExpandedSourceKernelPathBlock_mass
#print axioms positivePhysicalSourcePathMass_eqv_positiveExpandedPathMass
#print axioms PositiveExpandedPhysicalSourcePair
#print axioms PositiveExpandedPushedPhysicalTwoReplicaPath
#print axioms positiveExpandedPhysicalSourcePairs
#print axioms positiveExpandedPushedFaceRawFourCellSourcePaths
#print axioms positiveExpandedPushedFaceRawFourCellTargetPaths
#print axioms positiveExpandedPushedPhysicalTwoReplicaPathRawMass
#print axioms positivePushedPhysicalTwoReplicaPathMass_eqv_expandedPathMass
#print axioms positivePushedFaceRawFourCellSourcePaths_mass_eqv_expandedPaths
#print axioms positivePushedFaceRawFourCellTargetPaths_mass_eqv_expandedPaths
#print axioms actualPositiveExpandedPushedFaceRawFourCellPathCross
#print axioms actualPositivePushedFaceRawFourCellPathCross_eqv_expandedPaths
#print axioms physicalConnectedCovariancePositiveExpandedPathRawCrossDefect
#print axioms physicalConnectedCovariancePositivePathRawCrossDefect_eqv_expandedPaths
#print axioms physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedPathRawCross
#print axioms centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedPathRawCross

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths
