/-
# Cross-tail closure from finite BF4 row statistics

At each matched scale, the exact finite maximum of the deterministic
pairwise-row budget is an executable rational.  This file uses that maximum
as the error sequence in the existing positive-floor cross-tail theorem.

The resulting contract no longer assumes the physical rank-one defect
directly.  Its physical input is the more local statement that every pair of
retained boundary-message rows has a bounded cross-multiplied residual.
Finite enumeration may certify the prefix; the all-cutoff tail remains an
explicit division-free analytic obligation.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics

namespace YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail
open YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneCrossTail
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingCrossTail
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteRegularizedRankOneStatistics
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Pairwise cross-row residual hypothesis at one matched physical scale.
Naming the proposition keeps the scale-indexed records compact enough for
predictable constructive elaboration. -/
def MatchedBoundaryPairwiseResidualBoundAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pairwiseBound : Nat → Q')
    (scale : Nat) : Prop :=
  CentralBoundaryPairwiseRowResidualBound
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (pairwiseBound scale)

/-! ## 1. Exact scale-indexed finite-statistical contract -/

/-- Exact residual-and-bias maximum at one matched physical scale. -/
def matchedBoundaryExactStatisticalRankOneMaxBudget
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (scale : Nat) : Q' :=
  centralBoundaryExactStatisticalRankOneMaxBudget
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (pseudocount scale)
    (pseudocount_pos scale)

/-- A named exact-statistical error sequence is accountable when every entry
is rationally equivalent to the executable residual-and-bias maximum. -/
def MatchedBoundaryExactStatisticalMajorantIdentity
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (errorMajorant : Nat → Q') : Prop :=
  ∀ scale,
    matchedBoundaryExactStatisticalRankOneMaxBudget
        family coupling halfExtent pseudocount pseudocount_pos scale ≈
      errorMajorant scale

/-- Cross-tail contract for the exact finite residual-and-bias statistic.
There is no separately asserted defect majorant or pairwise-row estimate: the
named error sequence must equal the literal finite maximum. -/
structure MatchedPhysicalBoundaryRegularizedRankOneExactStatisticsCrossTailRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat)
    (pseudocount : Nat → Q') : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) (diagonalOrder scale) 0
  pseudocount_pos :
    ∀ scale, (0 : Q') < pseudocount scale
  errorMajorant : Nat → Q'
  exactMaxBudget_eqv_errorMajorant :
    MatchedBoundaryExactStatisticalMajorantIdentity
      family coupling halfExtent pseudocount pseudocount_pos
      errorMajorant
  errorTail :
    PositiveFloorErrorCrossTail
      errorMajorant
      (matchedRegularizedBoundaryRankOneFloor
        (family := family)
        coupling halfExtent pseudocount pseudocount_pos)
      physicalRelativeErrorTolerance

namespace MatchedPhysicalBoundaryRegularizedRankOneExactStatisticsCrossTailRows

/-- The exact statistic directly supplies the physical defect field of the
canonical regularized rank-one cross-tail contract. -/
def toRegularizedRankOneCrossTailRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneExactStatisticsCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows
      family law spacing coupling halfExtent diagonalOrder
      pseudocount where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  pseudocount_pos := data.pseudocount_pos
  errorMajorant := data.errorMajorant
  rank_one_defect_le := by
    intro scale source source_mem boundary boundary_mem
    exact Q'.le_trans' _ _ _
      (centralHalfAmplitudeRegularizedRankOneDefect_le_exactStatisticalMax
        source boundary source_mem boundary_mem)
      (Q'.le_of_eqv
        (data.exactMaxBudget_eqv_errorMajorant scale))
  errorTail := data.errorTail

/-- Hence the exact finite statistic reaches the generic computed-floor
physical-error interface without a separately assumed pairwise estimate. -/
def toComputedFloorErrorRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneExactStatisticsCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
      (fun _ => EdgeLabelling)
      family law spacing coupling halfExtent diagonalOrder :=
  data.toRegularizedRankOneCrossTailRows.toComputedFloorErrorRows

end MatchedPhysicalBoundaryRegularizedRankOneExactStatisticsCrossTailRows

/-! ## 2. Bounded-memory chunked-statistics contract -/

def matchedBoundaryChunkedStatisticalRankOneMaxBudget
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (sourceChunks : Nat → List (List EdgeLabelling))
    (chunkMajorant :
      Nat → List EdgeLabelling → EdgeLabelling → EdgeLabelling → Q')
    (scale : Nat) : Q' :=
  centralBoundaryChunkedStatisticalRankOneMaxBudget
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (pseudocount scale)
    (pseudocount_pos scale)
    (sourceChunks scale)
    (chunkMajorant scale)

def MatchedBoundaryChunkedStatisticalMajorantIdentity
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (sourceChunks : Nat → List (List EdgeLabelling))
    (chunkMajorant :
      Nat → List EdgeLabelling → EdgeLabelling → EdgeLabelling → Q')
    (errorMajorant : Nat → Q') : Prop :=
  ∀ scale,
    matchedBoundaryChunkedStatisticalRankOneMaxBudget
        family coupling halfExtent pseudocount pseudocount_pos
        sourceChunks chunkMajorant scale ≈
      errorMajorant scale

/-- Scale-indexed map-reduce contract.  Source shards must flatten exactly to
the literal retained BF4 list, and every proposed shard majorant is proved
coordinatewise before the existing cross-tail argument is used. -/
structure MatchedPhysicalBoundaryRegularizedRankOneChunkedStatisticsCrossTailRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat)
    (pseudocount : Nat → Q') : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) (diagonalOrder scale) 0
  pseudocount_pos :
    ∀ scale, (0 : Q') < pseudocount scale
  sourceChunks : Nat → List (List EdgeLabelling)
  sourceChunks_flatten :
    ∀ scale,
      (sourceChunks scale).flatten =
        centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
  chunkMajorant :
    Nat → List EdgeLabelling → EdgeLabelling → EdgeLabelling → Q'
  chunk_bound :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ boundary,
          boundary ∈
              centralBoundaryChannels
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            ∀ chunk,
              chunk ∈ sourceChunks scale →
                finitePairwiseRowResidualBudget
                    chunk
                    (centralBoundaryChannels
                      (matchedAllSpinCutoff family coupling scale)
                      (halfExtent scale))
                    (centralHalfAmplitude
                      (matchedAllSpinWeight family coupling scale)
                      (matchedAllSpinCutoff family coupling scale)
                      (halfExtent scale))
                    source boundary ≤
                  chunkMajorant scale chunk source boundary
  errorMajorant : Nat → Q'
  chunkedMaxBudget_eqv_errorMajorant :
    MatchedBoundaryChunkedStatisticalMajorantIdentity
      family coupling halfExtent pseudocount pseudocount_pos
      sourceChunks chunkMajorant errorMajorant
  errorTail :
    PositiveFloorErrorCrossTail
      errorMajorant
      (matchedRegularizedBoundaryRankOneFloor
        (family := family)
        coupling halfExtent pseudocount pseudocount_pos)
      physicalRelativeErrorTolerance

namespace MatchedPhysicalBoundaryRegularizedRankOneChunkedStatisticsCrossTailRows

def toRegularizedRankOneCrossTailRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneChunkedStatisticsCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows
      family law spacing coupling halfExtent diagonalOrder
      pseudocount where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  pseudocount_pos := data.pseudocount_pos
  errorMajorant := data.errorMajorant
  rank_one_defect_le := by
    intro scale source source_mem boundary boundary_mem
    exact Q'.le_trans' _ _ _
      (centralHalfAmplitudeRegularizedRankOneDefect_le_chunkedStatisticalMax
        (data.sourceChunks scale)
        (data.sourceChunks_flatten scale)
        (data.chunkMajorant scale)
        (data.chunk_bound scale)
        source boundary source_mem boundary_mem)
      (Q'.le_of_eqv
        (data.chunkedMaxBudget_eqv_errorMajorant scale))
  errorTail := data.errorTail

def toComputedFloorErrorRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneChunkedStatisticsCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
      (fun _ => EdgeLabelling)
      family law spacing coupling halfExtent diagonalOrder :=
  data.toRegularizedRankOneCrossTailRows.toComputedFloorErrorRows

end MatchedPhysicalBoundaryRegularizedRankOneChunkedStatisticsCrossTailRows

/-! ## 3. Exact block-compressed statistics contract -/

/-- Block-compressed finite maximum at one matched physical scale.  Natural
class identifiers keep generated scale-indexed certificates first-order. -/
def matchedBoundaryBlockCompressedStatisticalRankOneMaxBudget
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (sourceClasses : Nat → List Nat)
    (sourceBlock : Nat → Nat → List EdgeLabelling)
    (representative : Nat → Nat → EdgeLabelling)
    (scale : Nat) : Q' :=
  centralBoundaryBlockCompressedStatisticalRankOneMaxBudget
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (pseudocount scale)
    (pseudocount_pos scale)
    (sourceClasses scale)
    (sourceBlock scale)
    (representative scale)

def MatchedBoundaryBlockCompressedStatisticalMajorantIdentity
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (sourceClasses : Nat → List Nat)
    (sourceBlock : Nat → Nat → List EdgeLabelling)
    (representative : Nat → Nat → EdgeLabelling)
    (errorMajorant : Nat → Q') : Prop :=
  ∀ scale,
    matchedBoundaryBlockCompressedStatisticalRankOneMaxBudget
        family coupling halfExtent pseudocount pseudocount_pos
        sourceClasses sourceBlock representative scale ≈
      errorMajorant scale

/-- Scale-indexed exact sufficient-statistics contract.  A generated orbit
or histogram partition is accepted only if its flattened blocks reproduce
the retained source list and every member has the representative residual at
every retained coordinate. -/
structure MatchedPhysicalBoundaryRegularizedRankOneBlockCompressedStatisticsCrossTailRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat)
    (pseudocount : Nat → Q') : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) (diagonalOrder scale) 0
  pseudocount_pos :
    ∀ scale, (0 : Q') < pseudocount scale
  sourceClasses : Nat → List Nat
  sourceBlock : Nat → Nat → List EdgeLabelling
  sourceBlocks_flatten :
    ∀ scale,
      (sourceClasses scale).flatMap (sourceBlock scale) =
        centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
  representative : Nat → Nat → EdgeLabelling
  block_invariant :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ boundary,
          boundary ∈
              centralBoundaryChannels
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            ∀ cls,
              cls ∈ sourceClasses scale →
                ∀ other,
                  other ∈ sourceBlock scale cls →
                    Q'.abs
                        (centralBoundaryPairwiseRowCrossTerm
                          (matchedAllSpinWeight family coupling scale)
                          (matchedAllSpinCutoff family coupling scale)
                          (halfExtent scale) source other boundary) ≈
                      Q'.abs
                        (centralBoundaryPairwiseRowCrossTerm
                          (matchedAllSpinWeight family coupling scale)
                          (matchedAllSpinCutoff family coupling scale)
                          (halfExtent scale) source
                          (representative scale cls) boundary)
  errorMajorant : Nat → Q'
  blockCompressedMaxBudget_eqv_errorMajorant :
    MatchedBoundaryBlockCompressedStatisticalMajorantIdentity
      family coupling halfExtent pseudocount pseudocount_pos
      sourceClasses sourceBlock representative errorMajorant
  errorTail :
    PositiveFloorErrorCrossTail
      errorMajorant
      (matchedRegularizedBoundaryRankOneFloor
        (family := family)
        coupling halfExtent pseudocount pseudocount_pos)
      physicalRelativeErrorTolerance

namespace MatchedPhysicalBoundaryRegularizedRankOneBlockCompressedStatisticsCrossTailRows

def toRegularizedRankOneCrossTailRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneBlockCompressedStatisticsCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows
      family law spacing coupling halfExtent diagonalOrder
      pseudocount where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  pseudocount_pos := data.pseudocount_pos
  errorMajorant := data.errorMajorant
  rank_one_defect_le := by
    intro scale source source_mem boundary boundary_mem
    exact Q'.le_trans' _ _ _
      (centralHalfAmplitudeRegularizedRankOneDefect_le_blockCompressedStatisticalMax
        (data.sourceClasses scale)
        (data.sourceBlock scale)
        (data.sourceBlocks_flatten scale)
        (data.representative scale)
        (data.block_invariant scale)
        source boundary source_mem boundary_mem)
      (Q'.le_of_eqv
        (data.blockCompressedMaxBudget_eqv_errorMajorant scale))
  errorTail := data.errorTail

def toComputedFloorErrorRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneBlockCompressedStatisticsCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
      (fun _ => EdgeLabelling)
      family law spacing coupling halfExtent diagonalOrder :=
  data.toRegularizedRankOneCrossTailRows.toComputedFloorErrorRows

end MatchedPhysicalBoundaryRegularizedRankOneBlockCompressedStatisticsCrossTailRows

/-! ## 4. Hybrid pairwise-plus-exact-bias contract -/

def matchedBoundaryHybridStatisticalRankOneMaxBudget
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (pairwiseBound : Nat → Q')
    (scale : Nat) : Q' :=
  centralBoundaryHybridStatisticalRankOneMaxBudget
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (pseudocount scale)
    (pseudocount_pos scale)
    (pairwiseBound scale)

def MatchedBoundaryHybridStatisticalMajorantIdentity
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (pairwiseBound errorMajorant : Nat → Q') : Prop :=
  ∀ scale,
    matchedBoundaryHybridStatisticalRankOneMaxBudget
        family coupling halfExtent pseudocount pseudocount_pos
        pairwiseBound scale ≈
      errorMajorant scale

/-- Scale-indexed hybrid contract.  The physical analytic input is a uniform
pairwise-row estimate; the pseudocount bias remains the literal absolute
finite statistic rather than its two-term nonnegative relaxation. -/
structure MatchedPhysicalBoundaryRegularizedRankOneHybridStatisticsCrossTailRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat)
    (pseudocount : Nat → Q') : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) (diagonalOrder scale) 0
  pseudocount_pos :
    ∀ scale, (0 : Q') < pseudocount scale
  pairwiseBound : Nat → Q'
  pairwiseBound_nonnegative :
    ∀ scale, (0 : Q') ≤ pairwiseBound scale
  pairwise_cross_residual_le :
    ∀ scale,
      MatchedBoundaryPairwiseResidualBoundAt
        family coupling halfExtent pairwiseBound scale
  errorMajorant : Nat → Q'
  hybridMaxBudget_eqv_errorMajorant :
    MatchedBoundaryHybridStatisticalMajorantIdentity
      family coupling halfExtent pseudocount pseudocount_pos
      pairwiseBound errorMajorant
  errorTail :
    PositiveFloorErrorCrossTail
      errorMajorant
      (matchedRegularizedBoundaryRankOneFloor
        (family := family)
        coupling halfExtent pseudocount pseudocount_pos)
      physicalRelativeErrorTolerance

namespace MatchedPhysicalBoundaryRegularizedRankOneHybridStatisticsCrossTailRows

def toRegularizedRankOneCrossTailRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneHybridStatisticsCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows
      family law spacing coupling halfExtent diagonalOrder
      pseudocount where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  pseudocount_pos := data.pseudocount_pos
  errorMajorant := data.errorMajorant
  rank_one_defect_le := by
    intro scale source source_mem boundary boundary_mem
    exact Q'.le_trans' _ _ _
      (centralHalfAmplitudeRegularizedRankOneDefect_le_hybridStatisticalMax
        (data.pairwiseBound_nonnegative scale)
        (data.pairwise_cross_residual_le scale)
        source boundary source_mem boundary_mem)
      (Q'.le_of_eqv
        (data.hybridMaxBudget_eqv_errorMajorant scale))
  errorTail := data.errorTail

def toComputedFloorErrorRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneHybridStatisticsCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
      (fun _ => EdgeLabelling)
      family law spacing coupling halfExtent diagonalOrder :=
  data.toRegularizedRankOneCrossTailRows.toComputedFloorErrorRows

end MatchedPhysicalBoundaryRegularizedRankOneHybridStatisticsCrossTailRows

/-! ## 5. Coarse pairwise-majorized scale-indexed contract -/

/-- Exact finite statistical majorant at one matched scale. -/
def matchedBoundaryStatisticalRankOneMaxBudget
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (pairwiseBound : Nat → Q')
    (scale : Nat) : Q' :=
  centralBoundaryStatisticalRankOneMaxBudget
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (pseudocount scale)
    (pseudocount_pos scale)
    (pairwiseBound scale)

/-- A named error sequence is definitionally accountable when every entry is
rationally equivalent to the exact finite statistical maximum. -/
def MatchedBoundaryStatisticalMajorantIdentity
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat)
    (pseudocount : Nat → Q')
    (pseudocount_pos : ∀ scale, (0 : Q') < pseudocount scale)
    (pairwiseBound errorMajorant : Nat → Q') : Prop :=
  ∀ scale,
    matchedBoundaryStatisticalRankOneMaxBudget
        family coupling halfExtent pseudocount pseudocount_pos
        pairwiseBound scale ≈
      errorMajorant scale

/-- A matched-scale physical boundary contract stated in terms of pairwise
row statistics.  The error majorant is not arbitrary: it is the exact nested
finite maximum of the cardinality-plus-pseudocount budget. -/
structure MatchedPhysicalBoundaryRegularizedRankOneStatisticsCrossTailRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat)
    (pseudocount : Nat → Q') : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) (diagonalOrder scale) 0
  pseudocount_pos :
    ∀ scale, (0 : Q') < pseudocount scale
  pairwiseBound : Nat → Q'
  pairwiseBound_nonnegative :
    ∀ scale, (0 : Q') ≤ pairwiseBound scale
  pairwise_cross_residual_le :
    ∀ scale,
      MatchedBoundaryPairwiseResidualBoundAt
        family coupling halfExtent pairwiseBound scale
  errorMajorant : Nat → Q'
  maxBudget_eqv_errorMajorant :
    MatchedBoundaryStatisticalMajorantIdentity
      family coupling halfExtent pseudocount pseudocount_pos
      pairwiseBound errorMajorant
  errorTail :
    PositiveFloorErrorCrossTail
      errorMajorant
      (matchedRegularizedBoundaryRankOneFloor
        (family := family)
        coupling halfExtent pseudocount pseudocount_pos)
      physicalRelativeErrorTolerance

namespace MatchedPhysicalBoundaryRegularizedRankOneStatisticsCrossTailRows

/-! ## 5. Adapter to the canonical physical cross-tail -/

/-- The finite-statistical contract supplies the literal physical defect
field of the canonical regularized rank-one cross-tail contract. -/
def toRegularizedRankOneCrossTailRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneStatisticsCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows
      family law spacing coupling halfExtent diagonalOrder
      pseudocount where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  pseudocount_pos := data.pseudocount_pos
  errorMajorant := data.errorMajorant
  rank_one_defect_le := by
    intro scale source source_mem boundary boundary_mem
    exact Q'.le_trans' _ _ _
      (centralHalfAmplitudeRegularizedRankOneDefect_le_max_of_pairwiseBound
        (data.pairwiseBound_nonnegative scale)
        (data.pairwise_cross_residual_le scale)
        source boundary source_mem boundary_mem)
      (Q'.le_of_eqv
        (data.maxBudget_eqv_errorMajorant scale))
  errorTail := data.errorTail

/-- Hence finite pairwise row statistics reach the generic computed-floor
physical-error interface. -/
def toComputedFloorErrorRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    {pseudocount : Nat → Q'}
    (data :
      MatchedPhysicalBoundaryRegularizedRankOneStatisticsCrossTailRows
        family law spacing coupling halfExtent diagonalOrder
        pseudocount) :
    MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
      (fun _ => EdgeLabelling)
      family law spacing coupling halfExtent diagonalOrder :=
  data.toRegularizedRankOneCrossTailRows.toComputedFloorErrorRows

end MatchedPhysicalBoundaryRegularizedRankOneStatisticsCrossTailRows

end YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail.MatchedPhysicalBoundaryRegularizedRankOneExactStatisticsCrossTailRows.toRegularizedRankOneCrossTailRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail.MatchedPhysicalBoundaryRegularizedRankOneExactStatisticsCrossTailRows.toComputedFloorErrorRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail.MatchedPhysicalBoundaryRegularizedRankOneChunkedStatisticsCrossTailRows.toRegularizedRankOneCrossTailRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail.MatchedPhysicalBoundaryRegularizedRankOneChunkedStatisticsCrossTailRows.toComputedFloorErrorRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail.MatchedPhysicalBoundaryRegularizedRankOneBlockCompressedStatisticsCrossTailRows.toRegularizedRankOneCrossTailRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail.MatchedPhysicalBoundaryRegularizedRankOneBlockCompressedStatisticsCrossTailRows.toComputedFloorErrorRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail.MatchedPhysicalBoundaryRegularizedRankOneHybridStatisticsCrossTailRows.toRegularizedRankOneCrossTailRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail.MatchedPhysicalBoundaryRegularizedRankOneHybridStatisticsCrossTailRows.toComputedFloorErrorRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail.MatchedPhysicalBoundaryRegularizedRankOneStatisticsCrossTailRows.toRegularizedRankOneCrossTailRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail.MatchedPhysicalBoundaryRegularizedRankOneStatisticsCrossTailRows.toComputedFloorErrorRows
