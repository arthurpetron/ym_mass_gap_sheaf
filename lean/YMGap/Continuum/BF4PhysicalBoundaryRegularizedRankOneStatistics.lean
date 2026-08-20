/-
# Finite statistical control of the canonical BF4 boundary projection

The canonical regularized boundary profile is literally the generic
regularized empirical column profile of

* the retained positive BF4 half-states;
* the finite BF4 boundary carrier; and
* the physical half-amplitude matrix.

This file records that identification and specializes the deterministic
finite-statistics theorem.  A uniform bound on pairwise cross-row residuals
then controls the physical rank-one defect, with only the explicit source
cardinality and pseudocount bias as losses.  Exact source blocks can instead
be compressed to one representative and a multiplicity after their residual
invariance and coverage are checked in Lean.

This remains a finite-regulator reduction.  It does not assert the needed
pairwise estimate uniformly in the cutoff or identify a continuum theory.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneCrossTail
import YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
import YMGap.Continuum.FiniteRegularizedRankOneStatistics

namespace YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteRegularizedRankOneStatistics
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal identification with the generic finite matrix -/

theorem finiteRowMass_eq_centralHalfAmplitudeBoundaryRowMass
    (w : Q') (K half : Nat) (source : EdgeLabelling) :
    finiteRowMass
        (centralBoundaryChannels K half)
        (centralHalfAmplitude w K half)
        source =
      centralHalfAmplitudeBoundaryRowMass w K half source :=
  rfl

theorem finiteColumnMass_eq_centralBoundaryColumnMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) :
    finiteColumnMass
        (centralPositiveHalfStates w hw K half)
        (centralHalfAmplitude w K half)
        boundary =
      centralBoundaryColumnMass w hw K half boundary :=
  rfl

theorem finiteRegularizedNumerator_eq_central
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (boundary : EdgeLabelling) :
    finiteRegularizedNumerator
        (centralPositiveHalfStates w hw K half)
        (centralHalfAmplitude w K half)
        pseudocount boundary =
      centralRegularizedBoundaryNumerator
        w hw K half pseudocount boundary :=
  rfl

theorem finiteRegularizedDenominator_eq_central
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q') :
    finiteRegularizedDenominator
        (centralPositiveHalfStates w hw K half)
        (centralBoundaryChannels K half)
        (centralHalfAmplitude w K half)
        pseudocount =
      centralRegularizedBoundaryDenominator
        w hw K half pseudocount :=
  rfl

theorem finiteRegularizedProfile_eq_central
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (boundary : EdgeLabelling) :
    finiteRegularizedProfile
        (centralPositiveHalfStates w hw K half)
        (centralBoundaryChannels K half)
        (centralHalfAmplitude w K half)
        pseudocount
        (centralRegularizedBoundaryDenominator_pos
          hw K half pseudocount_pos)
        boundary =
      centralRegularizedBoundaryProfile
        w hw K half pseudocount pseudocount_pos boundary :=
  rfl

theorem finiteRegularizedRankOneDefect_eq_central
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (source boundary : EdgeLabelling) :
    finiteRegularizedRankOneDefect
        (centralPositiveHalfStates w hw K half)
        (centralBoundaryChannels K half)
        (centralHalfAmplitude w K half)
        pseudocount
        (centralRegularizedBoundaryDenominator_pos
          hw K half pseudocount_pos)
        source boundary =
      centralHalfAmplitudeRegularizedRankOneDefect
        w hw K half pseudocount pseudocount_pos source boundary :=
  rfl

/-! ## 2. BF4 pairwise statistic and explicit defect budget -/

/-- Pairwise proportionality residual between two physical boundary-message
rows, after clearing their row masses. -/
def centralBoundaryPairwiseRowCrossTerm
    (w : Q') (K half : Nat)
    (source other boundary : EdgeLabelling) : Q' :=
  finitePairwiseRowCrossTerm
    (centralBoundaryChannels K half)
    (centralHalfAmplitude w K half)
    source other boundary

/-- Uniform pairwise cross-row residual statement for one finite BF4
boundary-message matrix. -/
def CentralBoundaryPairwiseRowResidualBound
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pairwiseBound : Q') : Prop :=
  ∀ source,
    source ∈ centralPositiveHalfStates w hw K half →
      ∀ boundary,
        boundary ∈ centralBoundaryChannels K half →
          ∀ other,
            other ∈ centralPositiveHalfStates w hw K half →
              Q'.abs
                  (centralBoundaryPairwiseRowCrossTerm
                    w K half source other boundary) ≤
                pairwiseBound

/-! ## 3. Exact finite residual-and-bias budget -/

/-- The exact deterministic budget before replacing individual pairwise
residuals or the pseudocount bias by coarser upper bounds. -/
def centralBoundaryExactStatisticalRankOneBudget
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (source boundary : EdgeLabelling) : Q' :=
  Q'.divPos
    (finitePairwiseRowResidualBudget
        (centralPositiveHalfStates w hw K half)
        (centralBoundaryChannels K half)
        (centralHalfAmplitude w K half)
        source boundary +
      finitePseudocountBiasBudget
        (centralBoundaryChannels K half)
        (centralHalfAmplitude w K half)
        pseudocount source boundary)
    (centralRegularizedBoundaryDenominator
      w hw K half pseudocount)
    (centralRegularizedBoundaryDenominator_pos
      hw K half pseudocount_pos)

/-- Executable maximum of the exact residual-and-bias budget over the literal
retained source-by-boundary rectangle. -/
def centralBoundaryExactStatisticalRankOneMaxBudget
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount) : Q' :=
  listQMaxZero
    (fun source =>
      listQMaxZero
        (centralBoundaryExactStatisticalRankOneBudget
          w hw K half pseudocount pseudocount_pos source)
        (centralBoundaryChannels K half))
    (centralPositiveHalfStates w hw K half)

theorem centralBoundaryExactStatisticalRankOneBudget_le_max
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {pseudocount : Q'}
    {pseudocount_pos : (0 : Q') < pseudocount}
    {source boundary : EdgeLabelling}
    (source_mem : source ∈ centralPositiveHalfStates w hw K half)
    (boundary_mem : boundary ∈ centralBoundaryChannels K half) :
    centralBoundaryExactStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos source boundary ≤
      centralBoundaryExactStatisticalRankOneMaxBudget
        w hw K half pseudocount pseudocount_pos := by
  exact Q'.le_trans' _ _ _
    (le_listQMaxZero_of_mem
      (centralBoundaryExactStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos source)
      (centralBoundaryChannels K half)
      boundary_mem)
    (le_listQMaxZero_of_mem
      (fun source' =>
        listQMaxZero
          (centralBoundaryExactStatisticalRankOneBudget
            w hw K half pseudocount pseudocount_pos source')
          (centralBoundaryChannels K half))
      (centralPositiveHalfStates w hw K half)
      source_mem)

/-- Every physical entry defect is bounded by its exact finite sum of
absolute pairwise residuals and exact pseudocount bias. -/
theorem centralHalfAmplitudeRegularizedRankOneDefect_le_exactStatisticalBudget
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (source boundary : EdgeLabelling) :
    centralHalfAmplitudeRegularizedRankOneDefect
        w hw K half pseudocount pseudocount_pos source boundary ≤
      centralBoundaryExactStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos source boundary := by
  exact finiteRegularizedRankOneDefect_le_divPos_budget
    (centralPositiveHalfStates w hw K half)
    (centralBoundaryChannels K half)
    (centralHalfAmplitude w K half)
    pseudocount
    (centralRegularizedBoundaryDenominator_pos
      hw K half pseudocount_pos)
    source boundary

/-- Packaged exact finite form: no separately supplied pairwise bound is
needed to dominate the retained source-by-boundary rectangle. -/
theorem centralHalfAmplitudeRegularizedRankOneDefect_le_exactStatisticalMax
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {pseudocount : Q'}
    {pseudocount_pos : (0 : Q') < pseudocount}
    (source boundary : EdgeLabelling)
    (source_mem : source ∈ centralPositiveHalfStates w hw K half)
    (boundary_mem : boundary ∈ centralBoundaryChannels K half) :
    centralHalfAmplitudeRegularizedRankOneDefect
        w hw K half pseudocount pseudocount_pos source boundary ≤
      centralBoundaryExactStatisticalRankOneMaxBudget
        w hw K half pseudocount pseudocount_pos := by
  exact Q'.le_trans' _ _ _
    (centralHalfAmplitudeRegularizedRankOneDefect_le_exactStatisticalBudget
      hw K half pseudocount_pos source boundary)
    (centralBoundaryExactStatisticalRankOneBudget_le_max
      source_mem boundary_mem)

/-! ## 4. Bounded-memory source-shard certificates -/

/-- A BF4 coordinate budget assembled from independently checked source
shards.  The per-shard majorant may depend on the displayed source and
boundary coordinate. -/
def centralBoundaryChunkedStatisticalRankOneBudget
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (sourceChunks : List (List EdgeLabelling))
    (chunkMajorant :
      List EdgeLabelling → EdgeLabelling → EdgeLabelling → Q')
    (source boundary : EdgeLabelling) : Q' :=
  Q'.divPos
    (finiteChunkedPairwiseRowResidualMajorant
        sourceChunks
        (fun chunk => chunkMajorant chunk source boundary) +
      finitePseudocountBiasBudget
        (centralBoundaryChannels K half)
        (centralHalfAmplitude w K half)
        pseudocount source boundary)
    (centralRegularizedBoundaryDenominator
      w hw K half pseudocount)
    (centralRegularizedBoundaryDenominator_pos
      hw K half pseudocount_pos)

/-- Executable outer maximum of the sum of certified shard majorants and the
exact pseudocount bias. -/
def centralBoundaryChunkedStatisticalRankOneMaxBudget
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (sourceChunks : List (List EdgeLabelling))
    (chunkMajorant :
      List EdgeLabelling → EdgeLabelling → EdgeLabelling → Q') : Q' :=
  listQMaxZero
    (fun source =>
      listQMaxZero
        (centralBoundaryChunkedStatisticalRankOneBudget
          w hw K half pseudocount pseudocount_pos
          sourceChunks chunkMajorant source)
        (centralBoundaryChannels K half))
    (centralPositiveHalfStates w hw K half)

theorem centralBoundaryChunkedStatisticalRankOneBudget_le_max
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {pseudocount : Q'}
    {pseudocount_pos : (0 : Q') < pseudocount}
    {sourceChunks : List (List EdgeLabelling)}
    {chunkMajorant :
      List EdgeLabelling → EdgeLabelling → EdgeLabelling → Q'}
    {source boundary : EdgeLabelling}
    (source_mem : source ∈ centralPositiveHalfStates w hw K half)
    (boundary_mem : boundary ∈ centralBoundaryChannels K half) :
    centralBoundaryChunkedStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos
        sourceChunks chunkMajorant source boundary ≤
      centralBoundaryChunkedStatisticalRankOneMaxBudget
        w hw K half pseudocount pseudocount_pos
        sourceChunks chunkMajorant := by
  exact Q'.le_trans' _ _ _
    (le_listQMaxZero_of_mem
      (centralBoundaryChunkedStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos
        sourceChunks chunkMajorant source)
      (centralBoundaryChannels K half)
      boundary_mem)
    (le_listQMaxZero_of_mem
      (fun source' =>
        listQMaxZero
          (centralBoundaryChunkedStatisticalRankOneBudget
            w hw K half pseudocount pseudocount_pos
            sourceChunks chunkMajorant source')
          (centralBoundaryChannels K half))
      (centralPositiveHalfStates w hw K half)
      source_mem)

/-- BF4 map-reduce adapter.  The checked flattening equality guarantees that
the shards cover exactly the literal retained source list; each shard bound
is then sufficient for the global finite defect maximum. -/
theorem centralHalfAmplitudeRegularizedRankOneDefect_le_chunkedStatisticalMax
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {pseudocount : Q'}
    {pseudocount_pos : (0 : Q') < pseudocount}
    (sourceChunks : List (List EdgeLabelling))
    (sourceChunks_flatten :
      sourceChunks.flatten = centralPositiveHalfStates w hw K half)
    (chunkMajorant :
      List EdgeLabelling → EdgeLabelling → EdgeLabelling → Q')
    (chunk_bound :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K half →
          ∀ boundary,
            boundary ∈ centralBoundaryChannels K half →
              ∀ chunk,
                chunk ∈ sourceChunks →
                  finitePairwiseRowResidualBudget
                      chunk
                      (centralBoundaryChannels K half)
                      (centralHalfAmplitude w K half)
                      source boundary ≤
                    chunkMajorant chunk source boundary)
    (source boundary : EdgeLabelling)
    (source_mem : source ∈ centralPositiveHalfStates w hw K half)
    (boundary_mem : boundary ∈ centralBoundaryChannels K half) :
    centralHalfAmplitudeRegularizedRankOneDefect
        w hw K half pseudocount pseudocount_pos source boundary ≤
      centralBoundaryChunkedStatisticalRankOneMaxBudget
        w hw K half pseudocount pseudocount_pos
        sourceChunks chunkMajorant := by
  refine Q'.le_trans' _ _ _ ?_
    (centralBoundaryChunkedStatisticalRankOneBudget_le_max
      source_mem boundary_mem)
  exact finiteRegularizedRankOneDefect_le_chunkedMajorant_of_flatten_eq
    (centralPositiveHalfStates w hw K half)
    sourceChunks sourceChunks_flatten
    (centralBoundaryChannels K half)
    (centralHalfAmplitude w K half)
    pseudocount
    (centralRegularizedBoundaryDenominator_pos
      hw K half pseudocount_pos)
    (fun chunk => chunkMajorant chunk source boundary)
    source boundary
    (fun chunk chunk_mem =>
      chunk_bound source source_mem boundary boundary_mem chunk chunk_mem)

/-! ## 5. Exact source-block sufficient-statistics certificates -/

/-- A BF4 coordinate budget in which every certified source block is
represented by one residual and its exact list multiplicity. -/
def centralBoundaryBlockCompressedStatisticalRankOneBudget
    {Class : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (classes : List Class) (block : Class → List EdgeLabelling)
    (representative : Class → EdgeLabelling)
    (source boundary : EdgeLabelling) : Q' :=
  Q'.divPos
    (finiteBlockCompressedPairwiseRowResidualBudget
        classes block representative
        (centralBoundaryChannels K half)
        (centralHalfAmplitude w K half)
        source boundary +
      finitePseudocountBiasBudget
        (centralBoundaryChannels K half)
        (centralHalfAmplitude w K half)
        pseudocount source boundary)
    (centralRegularizedBoundaryDenominator
      w hw K half pseudocount)
    (centralRegularizedBoundaryDenominator_pos
      hw K half pseudocount_pos)

/-- Executable retained-coordinate maximum of the exact block-compressed
budget. -/
def centralBoundaryBlockCompressedStatisticalRankOneMaxBudget
    {Class : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (classes : List Class) (block : Class → List EdgeLabelling)
    (representative : Class → EdgeLabelling) : Q' :=
  listQMaxZero
    (fun source =>
      listQMaxZero
        (centralBoundaryBlockCompressedStatisticalRankOneBudget
          w hw K half pseudocount pseudocount_pos
          classes block representative source)
        (centralBoundaryChannels K half))
    (centralPositiveHalfStates w hw K half)

theorem centralBoundaryBlockCompressedStatisticalRankOneBudget_le_max
    {Class : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {pseudocount : Q'}
    {pseudocount_pos : (0 : Q') < pseudocount}
    {classes : List Class} {block : Class → List EdgeLabelling}
    {representative : Class → EdgeLabelling}
    {source boundary : EdgeLabelling}
    (source_mem : source ∈ centralPositiveHalfStates w hw K half)
    (boundary_mem : boundary ∈ centralBoundaryChannels K half) :
    centralBoundaryBlockCompressedStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos
        classes block representative source boundary ≤
      centralBoundaryBlockCompressedStatisticalRankOneMaxBudget
        w hw K half pseudocount pseudocount_pos
        classes block representative := by
  exact Q'.le_trans' _ _ _
    (le_listQMaxZero_of_mem
      (centralBoundaryBlockCompressedStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos
        classes block representative source)
      (centralBoundaryChannels K half)
      boundary_mem)
    (le_listQMaxZero_of_mem
      (fun source' =>
        listQMaxZero
          (centralBoundaryBlockCompressedStatisticalRankOneBudget
            w hw K half pseudocount pseudocount_pos
            classes block representative source')
          (centralBoundaryChannels K half))
      (centralPositiveHalfStates w hw K half)
      source_mem)

/-- BF4 sufficient-statistics adapter.  A proposed finite classification is
accepted only with exact list coverage and pointwise residual invariance for
every retained source, boundary, class, and member. -/
theorem centralHalfAmplitudeRegularizedRankOneDefect_le_blockCompressedStatisticalMax
    {Class : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {pseudocount : Q'}
    {pseudocount_pos : (0 : Q') < pseudocount}
    (classes : List Class) (block : Class → List EdgeLabelling)
    (blocks_flatten :
      classes.flatMap block = centralPositiveHalfStates w hw K half)
    (representative : Class → EdgeLabelling)
    (block_invariant :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K half →
          ∀ boundary,
            boundary ∈ centralBoundaryChannels K half →
              ∀ cls,
                cls ∈ classes →
                  ∀ other,
                    other ∈ block cls →
                      Q'.abs
                          (centralBoundaryPairwiseRowCrossTerm
                            w K half source other boundary) ≈
                        Q'.abs
                          (centralBoundaryPairwiseRowCrossTerm
                            w K half source (representative cls) boundary))
    (source boundary : EdgeLabelling)
    (source_mem : source ∈ centralPositiveHalfStates w hw K half)
    (boundary_mem : boundary ∈ centralBoundaryChannels K half) :
    centralHalfAmplitudeRegularizedRankOneDefect
        w hw K half pseudocount pseudocount_pos source boundary ≤
      centralBoundaryBlockCompressedStatisticalRankOneMaxBudget
        w hw K half pseudocount pseudocount_pos
        classes block representative := by
  refine Q'.le_trans' _ _ _ ?_
    (centralBoundaryBlockCompressedStatisticalRankOneBudget_le_max
      source_mem boundary_mem)
  exact finiteRegularizedRankOneDefect_le_blockCompressed_of_flatMap_eq
    (centralPositiveHalfStates w hw K half)
    classes block blocks_flatten representative
    (centralBoundaryChannels K half)
    (centralHalfAmplitude w K half)
    pseudocount
    (centralRegularizedBoundaryDenominator_pos
      hw K half pseudocount_pos)
    source boundary
    (fun cls cls_mem other other_mem =>
      block_invariant source source_mem boundary boundary_mem
        cls cls_mem other other_mem)

/-! ## 6. Uniform pairwise estimate with exact pseudocount bias -/

/-- Hybrid analytic budget: use one uniform pairwise-row residual bound, but
retain the exact absolute pseudocount bias at the displayed coordinate. -/
def centralBoundaryHybridStatisticalRankOneBudget
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (pairwiseBound : Q')
    (source boundary : EdgeLabelling) : Q' :=
  Q'.divPos
    (Q'.ofNat (centralPositiveHalfStates w hw K half).length *
        pairwiseBound +
      finitePseudocountBiasBudget
        (centralBoundaryChannels K half)
        (centralHalfAmplitude w K half)
        pseudocount source boundary)
    (centralRegularizedBoundaryDenominator
      w hw K half pseudocount)
    (centralRegularizedBoundaryDenominator_pos
      hw K half pseudocount_pos)

def centralBoundaryHybridStatisticalRankOneMaxBudget
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (pairwiseBound : Q') : Q' :=
  listQMaxZero
    (fun source =>
      listQMaxZero
        (centralBoundaryHybridStatisticalRankOneBudget
          w hw K half pseudocount pseudocount_pos pairwiseBound source)
        (centralBoundaryChannels K half))
    (centralPositiveHalfStates w hw K half)

theorem centralBoundaryHybridStatisticalRankOneBudget_le_max
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {pseudocount : Q'}
    {pseudocount_pos : (0 : Q') < pseudocount}
    {pairwiseBound : Q'}
    {source boundary : EdgeLabelling}
    (source_mem : source ∈ centralPositiveHalfStates w hw K half)
    (boundary_mem : boundary ∈ centralBoundaryChannels K half) :
    centralBoundaryHybridStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos pairwiseBound
        source boundary ≤
      centralBoundaryHybridStatisticalRankOneMaxBudget
        w hw K half pseudocount pseudocount_pos pairwiseBound := by
  exact Q'.le_trans' _ _ _
    (le_listQMaxZero_of_mem
      (centralBoundaryHybridStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos pairwiseBound source)
      (centralBoundaryChannels K half)
      boundary_mem)
    (le_listQMaxZero_of_mem
      (fun source' =>
        listQMaxZero
          (centralBoundaryHybridStatisticalRankOneBudget
            w hw K half pseudocount pseudocount_pos pairwiseBound source')
          (centralBoundaryChannels K half))
      (centralPositiveHalfStates w hw K half)
      source_mem)

/-- The hybrid BF4 budget follows from the uniform pairwise-row estimate
without any nonnegativity relaxation of the pseudocount bias. -/
theorem centralHalfAmplitudeRegularizedRankOneDefect_le_hybridStatisticalMax
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {pseudocount : Q'}
    {pseudocount_pos : (0 : Q') < pseudocount}
    {pairwiseBound : Q'}
    (pairwiseBound_nonnegative : (0 : Q') ≤ pairwiseBound)
    (pairwise :
      CentralBoundaryPairwiseRowResidualBound
        w hw K half pairwiseBound)
    (source boundary : EdgeLabelling)
    (source_mem : source ∈ centralPositiveHalfStates w hw K half)
    (boundary_mem : boundary ∈ centralBoundaryChannels K half) :
    centralHalfAmplitudeRegularizedRankOneDefect
        w hw K half pseudocount pseudocount_pos source boundary ≤
      centralBoundaryHybridStatisticalRankOneMaxBudget
        w hw K half pseudocount pseudocount_pos pairwiseBound := by
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_of_pairwise_exactBias
      (centralPositiveHalfStates w hw K half)
      (centralBoundaryChannels K half)
      (centralHalfAmplitude w K half)
      pseudocount
      (centralRegularizedBoundaryDenominator_pos
        hw K half pseudocount_pos)
      pairwiseBound pairwiseBound_nonnegative
      source boundary
      (fun other other_mem =>
        pairwise source source_mem boundary boundary_mem other other_mem))
    (centralBoundaryHybridStatisticalRankOneBudget_le_max
      source_mem boundary_mem)

/-- The deterministic rank-one error budget produced by a uniform pairwise
row residual bound. -/
def centralBoundaryStatisticalRankOneBudget
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (pairwiseBound : Q')
    (source boundary : EdgeLabelling) : Q' :=
  Q'.divPos
    (Q'.ofNat (centralPositiveHalfStates w hw K half).length *
        pairwiseBound +
      pseudocount *
        (Q'.ofNat (centralBoundaryChannels K half).length *
            centralHalfAmplitude w K half source boundary +
          centralHalfAmplitudeBoundaryRowMass w K half source))
    (centralRegularizedBoundaryDenominator
      w hw K half pseudocount)
    (centralRegularizedBoundaryDenominator_pos
      hw K half pseudocount_pos)

/-- Exact finite maximum of the statistical rank-one budget over every
retained positive source and boundary coordinate.  It is executable because
both carriers are literal lists and `Q'` has decidable order. -/
def centralBoundaryStatisticalRankOneMaxBudget
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (pseudocount : Q')
    (pseudocount_pos : (0 : Q') < pseudocount)
    (pairwiseBound : Q') : Q' :=
  listQMaxZero
    (fun source =>
      listQMaxZero
        (centralBoundaryStatisticalRankOneBudget
          w hw K half pseudocount pseudocount_pos pairwiseBound source)
        (centralBoundaryChannels K half))
    (centralPositiveHalfStates w hw K half)

theorem centralBoundaryStatisticalRankOneBudget_le_max
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {pseudocount : Q'}
    {pseudocount_pos : (0 : Q') < pseudocount}
    {pairwiseBound : Q'}
    {source boundary : EdgeLabelling}
    (source_mem : source ∈ centralPositiveHalfStates w hw K half)
    (boundary_mem : boundary ∈ centralBoundaryChannels K half) :
    centralBoundaryStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos pairwiseBound
        source boundary ≤
      centralBoundaryStatisticalRankOneMaxBudget
        w hw K half pseudocount pseudocount_pos pairwiseBound := by
  exact Q'.le_trans' _ _ _
    (le_listQMaxZero_of_mem
      (centralBoundaryStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos pairwiseBound source)
      (centralBoundaryChannels K half)
      boundary_mem)
    (le_listQMaxZero_of_mem
      (fun source' =>
        listQMaxZero
          (centralBoundaryStatisticalRankOneBudget
            w hw K half pseudocount pseudocount_pos pairwiseBound source')
          (centralBoundaryChannels K half))
      (centralPositiveHalfStates w hw K half)
      source_mem)

/-- A finite BF4 boundary-message matrix is close to its canonical
regularized rank-one projection whenever all cross-multiplied row pairs are
uniformly close.  The theorem is deterministic: no sampling interpretation
or asymptotic inference is used. -/
theorem centralHalfAmplitudeRegularizedRankOneDefect_le_of_pairwise
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) {pseudocount : Q'}
    (pseudocount_pos : (0 : Q') < pseudocount)
    (pairwiseBound : Q')
    (pairwiseBound_nonnegative : (0 : Q') ≤ pairwiseBound)
    (source boundary : EdgeLabelling)
    (boundary_mem : boundary ∈ centralBoundaryChannels K half)
    (pairwise :
      ∀ other,
        other ∈ centralPositiveHalfStates w hw K half →
          Q'.abs
              (centralBoundaryPairwiseRowCrossTerm
                w K half source other boundary) ≤
            pairwiseBound) :
    centralHalfAmplitudeRegularizedRankOneDefect
        w hw K half pseudocount pseudocount_pos source boundary ≤
      centralBoundaryStatisticalRankOneBudget
        w hw K half pseudocount pseudocount_pos pairwiseBound
        source boundary := by
  exact finiteRegularizedRankOneDefect_le_of_pairwise
    (centralPositiveHalfStates w hw K half)
    (centralBoundaryChannels K half)
    (centralHalfAmplitude w K half)
    (Q'.le_of_lt pseudocount_pos)
    (centralRegularizedBoundaryDenominator_pos
      hw K half pseudocount_pos)
    (fun source' boundary' _boundary_mem =>
      centralHalfAmplitude_nonnegative
        hw K half source' boundary')
    pairwiseBound pairwiseBound_nonnegative
    source boundary boundary_mem
    (by
      intro other other_mem
      exact pairwise other other_mem)

/-- Packaged one-scale form: the uniform pairwise residual proposition
controls every retained entry by the exact nested finite maximum. -/
theorem centralHalfAmplitudeRegularizedRankOneDefect_le_max_of_pairwiseBound
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {pseudocount : Q'}
    {pseudocount_pos : (0 : Q') < pseudocount}
    {pairwiseBound : Q'}
    (pairwiseBound_nonnegative : (0 : Q') ≤ pairwiseBound)
    (pairwise :
      CentralBoundaryPairwiseRowResidualBound
        w hw K half pairwiseBound)
    (source boundary : EdgeLabelling)
    (source_mem : source ∈ centralPositiveHalfStates w hw K half)
    (boundary_mem : boundary ∈ centralBoundaryChannels K half) :
    centralHalfAmplitudeRegularizedRankOneDefect
        w hw K half pseudocount pseudocount_pos source boundary ≤
      centralBoundaryStatisticalRankOneMaxBudget
        w hw K half pseudocount pseudocount_pos pairwiseBound := by
  exact Q'.le_trans' _ _ _
    (centralHalfAmplitudeRegularizedRankOneDefect_le_of_pairwise
      hw K half pseudocount_pos pairwiseBound
      pairwiseBound_nonnegative source boundary boundary_mem
      (fun other other_mem =>
        pairwise source source_mem boundary boundary_mem other other_mem))
    (centralBoundaryStatisticalRankOneBudget_le_max
      source_mem boundary_mem)

end YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.finiteRegularizedDenominator_eq_central
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.finiteRegularizedRankOneDefect_eq_central
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralBoundaryExactStatisticalRankOneBudget_le_max
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralHalfAmplitudeRegularizedRankOneDefect_le_exactStatisticalBudget
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralHalfAmplitudeRegularizedRankOneDefect_le_exactStatisticalMax
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralBoundaryChunkedStatisticalRankOneBudget_le_max
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralHalfAmplitudeRegularizedRankOneDefect_le_chunkedStatisticalMax
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralBoundaryBlockCompressedStatisticalRankOneBudget_le_max
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralHalfAmplitudeRegularizedRankOneDefect_le_blockCompressedStatisticalMax
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralBoundaryHybridStatisticalRankOneBudget_le_max
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralHalfAmplitudeRegularizedRankOneDefect_le_hybridStatisticalMax
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralBoundaryStatisticalRankOneBudget_le_max
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralHalfAmplitudeRegularizedRankOneDefect_le_of_pairwise
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics.centralHalfAmplitudeRegularizedRankOneDefect_le_max_of_pairwiseBound
