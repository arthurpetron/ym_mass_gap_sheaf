/- Generated computed-floor prefix data.  The generator is untrusted; Lean checks this file. -/
import YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail
import YMGap.Continuum.FiniteRegularizedRankOneStatistics

namespace YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample

open YMGap.Constructive
open YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation

local infix:50 " ≈ " => Q'.eqv

-- Generator-side threshold: 2
-- Generator-side maximum error/floor ratio: 4097/100642817
def regularizedRankOnePrefixDemoBudget
    (error floor : Nat -> Q')
    (regularizedRankOnePrefixDemoErrorStage0_exact : error 0 ≈ (0 : Q'))
    (regularizedRankOnePrefixDemoFloorStage0_exact : floor 0 ≈ Q'.mkPos 4096 1 (by decide))
    (regularizedRankOnePrefixDemoErrorStage1_exact : error 1 ≈ Q'.mkPos 1 8195 (by decide))
    (regularizedRankOnePrefixDemoFloorStage1_exact : floor 1 ≈ Q'.mkPos 33566721 8195 (by decide))
    (regularizedRankOnePrefixDemoErrorStage2_exact : error 2 ≈ Q'.mkPos 4097 24576 (by decide))
    (regularizedRankOnePrefixDemoFloorStage2_exact : floor 2 ≈ Q'.mkPos 100642817 24576 (by decide))
    (floor_pos : forall stage, (0 : Q') < floor stage)
    (tail_cross : forall stage : Nat,
      2 <= stage ->
        error (stage + 1) * floor stage <=
          error stage * floor (stage + 1))
    : PositiveFloorErrorCrossTail
        error floor physicalRelativeErrorTolerance where
  threshold := 2
  floor_pos := floor_pos
  prefix_bound := by
    intro stage hstage
    have hcases : stage = 0 ∨ stage = 1 := by omega
    rcases hcases with rfl | rfl
    ·
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv regularizedRankOnePrefixDemoErrorStage0_exact)
        (Q'.le_trans' _ _ _
          (by decide)
          (Q'.ge_of_eqv
            (Q'.mul_eqv_congr_left
              physicalRelativeErrorTolerance _ _
              regularizedRankOnePrefixDemoFloorStage0_exact)))
    ·
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv regularizedRankOnePrefixDemoErrorStage1_exact)
        (Q'.le_trans' _ _ _
          (by decide)
          (Q'.ge_of_eqv
            (Q'.mul_eqv_congr_left
              physicalRelativeErrorTolerance _ _
              regularizedRankOnePrefixDemoFloorStage1_exact)))
  threshold_bound := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv regularizedRankOnePrefixDemoErrorStage2_exact)
      (Q'.le_trans' _ _ _
        (by decide)
        (Q'.ge_of_eqv
          (Q'.mul_eqv_congr_left
            physicalRelativeErrorTolerance _ _
            regularizedRankOnePrefixDemoFloorStage2_exact)))
  tail_cross := tail_cross

theorem regularizedRankOnePrefixDemoAllStages_le
    (error floor : Nat -> Q')
    (regularizedRankOnePrefixDemoErrorStage0_exact : error 0 ≈ (0 : Q'))
    (regularizedRankOnePrefixDemoFloorStage0_exact : floor 0 ≈ Q'.mkPos 4096 1 (by decide))
    (regularizedRankOnePrefixDemoErrorStage1_exact : error 1 ≈ Q'.mkPos 1 8195 (by decide))
    (regularizedRankOnePrefixDemoFloorStage1_exact : floor 1 ≈ Q'.mkPos 33566721 8195 (by decide))
    (regularizedRankOnePrefixDemoErrorStage2_exact : error 2 ≈ Q'.mkPos 4097 24576 (by decide))
    (regularizedRankOnePrefixDemoFloorStage2_exact : floor 2 ≈ Q'.mkPos 100642817 24576 (by decide))
    (floor_pos : forall stage, (0 : Q') < floor stage)
    (tail_cross : forall stage : Nat,
      2 <= stage ->
        error (stage + 1) * floor stage <=
          error stage * floor (stage + 1))
    : forall stage : Nat,
      error stage <= physicalRelativeErrorTolerance * floor stage := by
  intro stage
  exact (regularizedRankOnePrefixDemoBudget error floor regularizedRankOnePrefixDemoErrorStage0_exact regularizedRankOnePrefixDemoFloorStage0_exact regularizedRankOnePrefixDemoErrorStage1_exact regularizedRankOnePrefixDemoFloorStage1_exact regularizedRankOnePrefixDemoErrorStage2_exact regularizedRankOnePrefixDemoFloorStage2_exact floor_pos tail_cross)
    |>.error_le_tolerance_mul_floor stage

end YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample

#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoBudget
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoAllStages_le

namespace YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.FiniteRegularizedRankOneStatistics
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/- Literal finite amplitude matrices.  Each theorem below is checked
by Lean; the external exact-arithmetic run is not part of the proof. -/

def regularizedRankOnePrefixDemoScale0Sources : List (Fin 2) := [0, 1]
def regularizedRankOnePrefixDemoScale0Targets : List (Fin 2) := [0, 1]
def regularizedRankOnePrefixDemoScale0SourceShard0 : List (Fin 2) := [0]
def regularizedRankOnePrefixDemoScale0SourceShard1 : List (Fin 2) := [1]
def regularizedRankOnePrefixDemoScale0SourceChunks : List (List (Fin 2)) :=
  [regularizedRankOnePrefixDemoScale0SourceShard0, regularizedRankOnePrefixDemoScale0SourceShard1]
theorem regularizedRankOnePrefixDemoScale0SourceChunks_flatten : regularizedRankOnePrefixDemoScale0SourceChunks.flatten = regularizedRankOnePrefixDemoScale0Sources := by
  decide
def regularizedRankOnePrefixDemoScale0Pseudocount : Q' := Q'.mkPos 1 1 (by decide)

def regularizedRankOnePrefixDemoScale0Amplitude (source : Fin 2) (target : Fin 2) : Q' :=
  match source.val, target.val with
  | 0, 0 => Q'.mkPos 4096 1 (by decide)
  | 0, 1 => Q'.mkPos 4096 1 (by decide)
  | 1, 0 => Q'.mkPos 8192 1 (by decide)
  | 1, 1 => Q'.mkPos 8192 1 (by decide)
  | _, _ => 0

def regularizedRankOnePrefixDemoScale0ColumnMass (target : Fin 2) : Q' :=
  listQSum (fun source => regularizedRankOnePrefixDemoScale0Amplitude source target) regularizedRankOnePrefixDemoScale0Sources

def regularizedRankOnePrefixDemoScale0Numerator (target : Fin 2) : Q' :=
  regularizedRankOnePrefixDemoScale0Pseudocount + regularizedRankOnePrefixDemoScale0ColumnMass target

def regularizedRankOnePrefixDemoScale0Denominator : Q' :=
  listQSum regularizedRankOnePrefixDemoScale0Numerator regularizedRankOnePrefixDemoScale0Targets

theorem regularizedRankOnePrefixDemoScale0Denominator_pos : (0 : Q') < regularizedRankOnePrefixDemoScale0Denominator := by
  decide

theorem regularizedRankOnePrefixDemoScale0FiniteDenominator_pos :
    (0 : Q') < finiteRegularizedDenominator
      regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount := by
  decide

def regularizedRankOnePrefixDemoScale0Profile (target : Fin 2) : Q' :=
  Q'.divPos (regularizedRankOnePrefixDemoScale0Numerator target) regularizedRankOnePrefixDemoScale0Denominator regularizedRankOnePrefixDemoScale0Denominator_pos

def regularizedRankOnePrefixDemoScale0RowMass (source : Fin 2) : Q' :=
  listQSum (regularizedRankOnePrefixDemoScale0Amplitude source) regularizedRankOnePrefixDemoScale0Targets

def regularizedRankOnePrefixDemoScale0Projection
    (source : Fin 2) (target : Fin 2) : Q' :=
  regularizedRankOnePrefixDemoScale0RowMass source * regularizedRankOnePrefixDemoScale0Profile target

def regularizedRankOnePrefixDemoScale0Error : Q' := (0 : Q')
def regularizedRankOnePrefixDemoScale0PairwiseBound : Q' := (0 : Q')

def regularizedRankOnePrefixDemoScale0ExactStatisticalBudget
    (source : Fin 2) (target : Fin 2) : Q' :=
  Q'.divPos
    (finitePairwiseRowResidualBudget
        regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude source target +
      finitePseudocountBiasBudget
        regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount source target)
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets
      regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount)
    regularizedRankOnePrefixDemoScale0FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale0ExactStatisticalError : Q' := (0 : Q')

def regularizedRankOnePrefixDemoScale0ChunkMajorant
    (chunk : List (Fin 2))
    (_source : Fin 2) (_target : Fin 2) : Q' :=
  if chunk = regularizedRankOnePrefixDemoScale0SourceShard0 then (0 : Q')
  else if chunk = regularizedRankOnePrefixDemoScale0SourceShard1 then (0 : Q')
  else 0

def regularizedRankOnePrefixDemoScale0ChunkedStatisticalBudget
    (source : Fin 2) (target : Fin 2) : Q' :=
  Q'.divPos
    (finiteChunkedPairwiseRowResidualMajorant
        regularizedRankOnePrefixDemoScale0SourceChunks
        (fun chunk => regularizedRankOnePrefixDemoScale0ChunkMajorant chunk source target) +
      finitePseudocountBiasBudget
        regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount source target)
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets
      regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount)
    regularizedRankOnePrefixDemoScale0FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale0ChunkedStatisticalError : Q' := (0 : Q')

def regularizedRankOnePrefixDemoScale0HybridStatisticalBudget
    (source : Fin 2) (target : Fin 2) : Q' :=
  Q'.divPos
    (Q'.ofNat regularizedRankOnePrefixDemoScale0Sources.length * regularizedRankOnePrefixDemoScale0PairwiseBound +
      finitePseudocountBiasBudget
        regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount source target)
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets
      regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount)
    regularizedRankOnePrefixDemoScale0FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale0HybridStatisticalError : Q' := (0 : Q')

def regularizedRankOnePrefixDemoScale0StatisticalBudget
    (source : Fin 2) (target : Fin 2) : Q' :=
  Q'.divPos
    (Q'.ofNat regularizedRankOnePrefixDemoScale0Sources.length * regularizedRankOnePrefixDemoScale0PairwiseBound +
      regularizedRankOnePrefixDemoScale0Pseudocount *
        (Q'.ofNat regularizedRankOnePrefixDemoScale0Targets.length * regularizedRankOnePrefixDemoScale0Amplitude source target +
          finiteRowMass regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude source))
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets
      regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount)
    regularizedRankOnePrefixDemoScale0FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale0StatisticalError : Q' := Q'.mkPos 16384 12289 (by decide)
def regularizedRankOnePrefixDemoScale0Floor : Q' := Q'.mkPos 4096 1 (by decide)

theorem regularizedRankOnePrefixDemoScale0Pairwise_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        ∀ other, other ∈ regularizedRankOnePrefixDemoScale0Sources →
          Q'.abs (finitePairwiseRowCrossTerm
            regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude source other target) ≤
              regularizedRankOnePrefixDemoScale0PairwiseBound := by
  decide

theorem regularizedRankOnePrefixDemoScale0StatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        regularizedRankOnePrefixDemoScale0StatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale0StatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale0ExactStatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        regularizedRankOnePrefixDemoScale0ExactStatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale0ExactStatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale0ChunkBound :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        ∀ chunk, chunk ∈ regularizedRankOnePrefixDemoScale0SourceChunks →
          finitePairwiseRowResidualBudget
              chunk regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude source target ≤
            regularizedRankOnePrefixDemoScale0ChunkMajorant chunk source target := by
  decide

theorem regularizedRankOnePrefixDemoScale0ChunkedStatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        regularizedRankOnePrefixDemoScale0ChunkedStatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale0ChunkedStatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale0HybridStatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        regularizedRankOnePrefixDemoScale0HybridStatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale0HybridStatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale0GenericDefect_le_hybridStatisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount
            regularizedRankOnePrefixDemoScale0FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale0HybridStatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_of_pairwise_exactBias
      regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount
      regularizedRankOnePrefixDemoScale0FiniteDenominator_pos
      regularizedRankOnePrefixDemoScale0PairwiseBound (by decide)
      source target
      (by
        intro other other_mem
        exact regularizedRankOnePrefixDemoScale0Pairwise_le source source_mem target
          target_mem other other_mem))
    (regularizedRankOnePrefixDemoScale0HybridStatisticalBudget_le
      source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale0GenericDefect_le_chunkedStatisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount
            regularizedRankOnePrefixDemoScale0FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale0ChunkedStatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_chunkedMajorant_of_flatten_eq
      regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0SourceChunks regularizedRankOnePrefixDemoScale0SourceChunks_flatten
      regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount
      regularizedRankOnePrefixDemoScale0FiniteDenominator_pos
      (fun chunk => regularizedRankOnePrefixDemoScale0ChunkMajorant chunk source target)
      source target
      (by
        intro chunk chunk_mem
        exact regularizedRankOnePrefixDemoScale0ChunkBound source source_mem target
          target_mem chunk chunk_mem))
    (regularizedRankOnePrefixDemoScale0ChunkedStatisticalBudget_le
      source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale0GenericDefect_le_exactStatisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount
            regularizedRankOnePrefixDemoScale0FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale0ExactStatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_divPos_budget
      regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount
      regularizedRankOnePrefixDemoScale0FiniteDenominator_pos source target)
    (regularizedRankOnePrefixDemoScale0ExactStatisticalBudget_le
      source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale0GenericDefect_le_statisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude regularizedRankOnePrefixDemoScale0Pseudocount
            regularizedRankOnePrefixDemoScale0FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale0StatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_of_pairwise
      regularizedRankOnePrefixDemoScale0Sources regularizedRankOnePrefixDemoScale0Targets regularizedRankOnePrefixDemoScale0Amplitude
      (by decide)
      regularizedRankOnePrefixDemoScale0FiniteDenominator_pos
      (by intro source' target' target'_mem; decide +revert)
      regularizedRankOnePrefixDemoScale0PairwiseBound (by decide)
      source target target_mem
      (by
        intro other other_mem
        exact regularizedRankOnePrefixDemoScale0Pairwise_le source source_mem target
          target_mem other other_mem))
    (regularizedRankOnePrefixDemoScale0StatisticalBudget_le source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale0Defect_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        Q'.abs (regularizedRankOnePrefixDemoScale0Amplitude source target +
          -regularizedRankOnePrefixDemoScale0Projection source target) ≤ regularizedRankOnePrefixDemoScale0Error := by
  decide

theorem regularizedRankOnePrefixDemoScale0Floor_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale0Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale0Targets →
        regularizedRankOnePrefixDemoScale0Floor ≤ regularizedRankOnePrefixDemoScale0Projection source target := by
  decide

def regularizedRankOnePrefixDemoScale1Sources : List (Fin 1) := [0]
def regularizedRankOnePrefixDemoScale1Targets : List (Fin 2) := [0, 1]
def regularizedRankOnePrefixDemoScale1SourceShard0 : List (Fin 1) := [0]
def regularizedRankOnePrefixDemoScale1SourceChunks : List (List (Fin 1)) :=
  [regularizedRankOnePrefixDemoScale1SourceShard0]
theorem regularizedRankOnePrefixDemoScale1SourceChunks_flatten : regularizedRankOnePrefixDemoScale1SourceChunks.flatten = regularizedRankOnePrefixDemoScale1Sources := by
  decide
def regularizedRankOnePrefixDemoScale1Pseudocount : Q' := Q'.mkPos 1 1 (by decide)

def regularizedRankOnePrefixDemoScale1Amplitude (source : Fin 1) (target : Fin 2) : Q' :=
  match source.val, target.val with
  | 0, 0 => Q'.mkPos 4097 1 (by decide)
  | 0, 1 => Q'.mkPos 4096 1 (by decide)
  | _, _ => 0

def regularizedRankOnePrefixDemoScale1ColumnMass (target : Fin 2) : Q' :=
  listQSum (fun source => regularizedRankOnePrefixDemoScale1Amplitude source target) regularizedRankOnePrefixDemoScale1Sources

def regularizedRankOnePrefixDemoScale1Numerator (target : Fin 2) : Q' :=
  regularizedRankOnePrefixDemoScale1Pseudocount + regularizedRankOnePrefixDemoScale1ColumnMass target

def regularizedRankOnePrefixDemoScale1Denominator : Q' :=
  listQSum regularizedRankOnePrefixDemoScale1Numerator regularizedRankOnePrefixDemoScale1Targets

theorem regularizedRankOnePrefixDemoScale1Denominator_pos : (0 : Q') < regularizedRankOnePrefixDemoScale1Denominator := by
  decide

theorem regularizedRankOnePrefixDemoScale1FiniteDenominator_pos :
    (0 : Q') < finiteRegularizedDenominator
      regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount := by
  decide

def regularizedRankOnePrefixDemoScale1Profile (target : Fin 2) : Q' :=
  Q'.divPos (regularizedRankOnePrefixDemoScale1Numerator target) regularizedRankOnePrefixDemoScale1Denominator regularizedRankOnePrefixDemoScale1Denominator_pos

def regularizedRankOnePrefixDemoScale1RowMass (source : Fin 1) : Q' :=
  listQSum (regularizedRankOnePrefixDemoScale1Amplitude source) regularizedRankOnePrefixDemoScale1Targets

def regularizedRankOnePrefixDemoScale1Projection
    (source : Fin 1) (target : Fin 2) : Q' :=
  regularizedRankOnePrefixDemoScale1RowMass source * regularizedRankOnePrefixDemoScale1Profile target

def regularizedRankOnePrefixDemoScale1Error : Q' := Q'.mkPos 1 8195 (by decide)
def regularizedRankOnePrefixDemoScale1PairwiseBound : Q' := (0 : Q')

def regularizedRankOnePrefixDemoScale1ExactStatisticalBudget
    (source : Fin 1) (target : Fin 2) : Q' :=
  Q'.divPos
    (finitePairwiseRowResidualBudget
        regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude source target +
      finitePseudocountBiasBudget
        regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount source target)
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets
      regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount)
    regularizedRankOnePrefixDemoScale1FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale1ExactStatisticalError : Q' := Q'.mkPos 1 8195 (by decide)

def regularizedRankOnePrefixDemoScale1ChunkMajorant
    (chunk : List (Fin 1))
    (_source : Fin 1) (_target : Fin 2) : Q' :=
  if chunk = regularizedRankOnePrefixDemoScale1SourceShard0 then (0 : Q')
  else 0

def regularizedRankOnePrefixDemoScale1ChunkedStatisticalBudget
    (source : Fin 1) (target : Fin 2) : Q' :=
  Q'.divPos
    (finiteChunkedPairwiseRowResidualMajorant
        regularizedRankOnePrefixDemoScale1SourceChunks
        (fun chunk => regularizedRankOnePrefixDemoScale1ChunkMajorant chunk source target) +
      finitePseudocountBiasBudget
        regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount source target)
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets
      regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount)
    regularizedRankOnePrefixDemoScale1FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale1ChunkedStatisticalError : Q' := Q'.mkPos 1 8195 (by decide)

def regularizedRankOnePrefixDemoScale1HybridStatisticalBudget
    (source : Fin 1) (target : Fin 2) : Q' :=
  Q'.divPos
    (Q'.ofNat regularizedRankOnePrefixDemoScale1Sources.length * regularizedRankOnePrefixDemoScale1PairwiseBound +
      finitePseudocountBiasBudget
        regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount source target)
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets
      regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount)
    regularizedRankOnePrefixDemoScale1FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale1HybridStatisticalError : Q' := Q'.mkPos 1 8195 (by decide)

def regularizedRankOnePrefixDemoScale1StatisticalBudget
    (source : Fin 1) (target : Fin 2) : Q' :=
  Q'.divPos
    (Q'.ofNat regularizedRankOnePrefixDemoScale1Sources.length * regularizedRankOnePrefixDemoScale1PairwiseBound +
      regularizedRankOnePrefixDemoScale1Pseudocount *
        (Q'.ofNat regularizedRankOnePrefixDemoScale1Targets.length * regularizedRankOnePrefixDemoScale1Amplitude source target +
          finiteRowMass regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude source))
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets
      regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount)
    regularizedRankOnePrefixDemoScale1FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale1StatisticalError : Q' := Q'.mkPos 16387 8195 (by decide)
def regularizedRankOnePrefixDemoScale1Floor : Q' := Q'.mkPos 33566721 8195 (by decide)

theorem regularizedRankOnePrefixDemoScale1Pairwise_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        ∀ other, other ∈ regularizedRankOnePrefixDemoScale1Sources →
          Q'.abs (finitePairwiseRowCrossTerm
            regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude source other target) ≤
              regularizedRankOnePrefixDemoScale1PairwiseBound := by
  decide

theorem regularizedRankOnePrefixDemoScale1StatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        regularizedRankOnePrefixDemoScale1StatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale1StatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale1ExactStatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        regularizedRankOnePrefixDemoScale1ExactStatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale1ExactStatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale1ChunkBound :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        ∀ chunk, chunk ∈ regularizedRankOnePrefixDemoScale1SourceChunks →
          finitePairwiseRowResidualBudget
              chunk regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude source target ≤
            regularizedRankOnePrefixDemoScale1ChunkMajorant chunk source target := by
  decide

theorem regularizedRankOnePrefixDemoScale1ChunkedStatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        regularizedRankOnePrefixDemoScale1ChunkedStatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale1ChunkedStatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale1HybridStatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        regularizedRankOnePrefixDemoScale1HybridStatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale1HybridStatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale1GenericDefect_le_hybridStatisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount
            regularizedRankOnePrefixDemoScale1FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale1HybridStatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_of_pairwise_exactBias
      regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount
      regularizedRankOnePrefixDemoScale1FiniteDenominator_pos
      regularizedRankOnePrefixDemoScale1PairwiseBound (by decide)
      source target
      (by
        intro other other_mem
        exact regularizedRankOnePrefixDemoScale1Pairwise_le source source_mem target
          target_mem other other_mem))
    (regularizedRankOnePrefixDemoScale1HybridStatisticalBudget_le
      source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale1GenericDefect_le_chunkedStatisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount
            regularizedRankOnePrefixDemoScale1FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale1ChunkedStatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_chunkedMajorant_of_flatten_eq
      regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1SourceChunks regularizedRankOnePrefixDemoScale1SourceChunks_flatten
      regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount
      regularizedRankOnePrefixDemoScale1FiniteDenominator_pos
      (fun chunk => regularizedRankOnePrefixDemoScale1ChunkMajorant chunk source target)
      source target
      (by
        intro chunk chunk_mem
        exact regularizedRankOnePrefixDemoScale1ChunkBound source source_mem target
          target_mem chunk chunk_mem))
    (regularizedRankOnePrefixDemoScale1ChunkedStatisticalBudget_le
      source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale1GenericDefect_le_exactStatisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount
            regularizedRankOnePrefixDemoScale1FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale1ExactStatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_divPos_budget
      regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount
      regularizedRankOnePrefixDemoScale1FiniteDenominator_pos source target)
    (regularizedRankOnePrefixDemoScale1ExactStatisticalBudget_le
      source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale1GenericDefect_le_statisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude regularizedRankOnePrefixDemoScale1Pseudocount
            regularizedRankOnePrefixDemoScale1FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale1StatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_of_pairwise
      regularizedRankOnePrefixDemoScale1Sources regularizedRankOnePrefixDemoScale1Targets regularizedRankOnePrefixDemoScale1Amplitude
      (by decide)
      regularizedRankOnePrefixDemoScale1FiniteDenominator_pos
      (by intro source' target' target'_mem; decide +revert)
      regularizedRankOnePrefixDemoScale1PairwiseBound (by decide)
      source target target_mem
      (by
        intro other other_mem
        exact regularizedRankOnePrefixDemoScale1Pairwise_le source source_mem target
          target_mem other other_mem))
    (regularizedRankOnePrefixDemoScale1StatisticalBudget_le source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale1Defect_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        Q'.abs (regularizedRankOnePrefixDemoScale1Amplitude source target +
          -regularizedRankOnePrefixDemoScale1Projection source target) ≤ regularizedRankOnePrefixDemoScale1Error := by
  decide

theorem regularizedRankOnePrefixDemoScale1Floor_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale1Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale1Targets →
        regularizedRankOnePrefixDemoScale1Floor ≤ regularizedRankOnePrefixDemoScale1Projection source target := by
  decide

def regularizedRankOnePrefixDemoScale2Sources : List (Fin 2) := [0, 1]
def regularizedRankOnePrefixDemoScale2Targets : List (Fin 2) := [0, 1]
def regularizedRankOnePrefixDemoScale2SourceShard0 : List (Fin 2) := [0]
def regularizedRankOnePrefixDemoScale2SourceShard1 : List (Fin 2) := [1]
def regularizedRankOnePrefixDemoScale2SourceChunks : List (List (Fin 2)) :=
  [regularizedRankOnePrefixDemoScale2SourceShard0, regularizedRankOnePrefixDemoScale2SourceShard1]
theorem regularizedRankOnePrefixDemoScale2SourceChunks_flatten : regularizedRankOnePrefixDemoScale2SourceChunks.flatten = regularizedRankOnePrefixDemoScale2Sources := by
  decide
def regularizedRankOnePrefixDemoScale2Pseudocount : Q' := Q'.mkPos 1 1 (by decide)

def regularizedRankOnePrefixDemoScale2Amplitude (source : Fin 2) (target : Fin 2) : Q' :=
  match source.val, target.val with
  | 0, 0 => Q'.mkPos 8192 1 (by decide)
  | 0, 1 => Q'.mkPos 8191 1 (by decide)
  | 1, 0 => Q'.mkPos 4096 1 (by decide)
  | 1, 1 => Q'.mkPos 4095 1 (by decide)
  | _, _ => 0

def regularizedRankOnePrefixDemoScale2ColumnMass (target : Fin 2) : Q' :=
  listQSum (fun source => regularizedRankOnePrefixDemoScale2Amplitude source target) regularizedRankOnePrefixDemoScale2Sources

def regularizedRankOnePrefixDemoScale2Numerator (target : Fin 2) : Q' :=
  regularizedRankOnePrefixDemoScale2Pseudocount + regularizedRankOnePrefixDemoScale2ColumnMass target

def regularizedRankOnePrefixDemoScale2Denominator : Q' :=
  listQSum regularizedRankOnePrefixDemoScale2Numerator regularizedRankOnePrefixDemoScale2Targets

theorem regularizedRankOnePrefixDemoScale2Denominator_pos : (0 : Q') < regularizedRankOnePrefixDemoScale2Denominator := by
  decide

theorem regularizedRankOnePrefixDemoScale2FiniteDenominator_pos :
    (0 : Q') < finiteRegularizedDenominator
      regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount := by
  decide

def regularizedRankOnePrefixDemoScale2Profile (target : Fin 2) : Q' :=
  Q'.divPos (regularizedRankOnePrefixDemoScale2Numerator target) regularizedRankOnePrefixDemoScale2Denominator regularizedRankOnePrefixDemoScale2Denominator_pos

def regularizedRankOnePrefixDemoScale2RowMass (source : Fin 2) : Q' :=
  listQSum (regularizedRankOnePrefixDemoScale2Amplitude source) regularizedRankOnePrefixDemoScale2Targets

def regularizedRankOnePrefixDemoScale2Projection
    (source : Fin 2) (target : Fin 2) : Q' :=
  regularizedRankOnePrefixDemoScale2RowMass source * regularizedRankOnePrefixDemoScale2Profile target

def regularizedRankOnePrefixDemoScale2Error : Q' := Q'.mkPos 4097 24576 (by decide)
def regularizedRankOnePrefixDemoScale2PairwiseBound : Q' := Q'.mkPos 4096 1 (by decide)

def regularizedRankOnePrefixDemoScale2ExactStatisticalBudget
    (source : Fin 2) (target : Fin 2) : Q' :=
  Q'.divPos
    (finitePairwiseRowResidualBudget
        regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude source target +
      finitePseudocountBiasBudget
        regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount source target)
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets
      regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount)
    regularizedRankOnePrefixDemoScale2FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale2ExactStatisticalError : Q' := Q'.mkPos 4097 24576 (by decide)

def regularizedRankOnePrefixDemoScale2ChunkMajorant
    (chunk : List (Fin 2))
    (_source : Fin 2) (_target : Fin 2) : Q' :=
  if chunk = regularizedRankOnePrefixDemoScale2SourceShard0 then Q'.mkPos 4096 1 (by decide)
  else if chunk = regularizedRankOnePrefixDemoScale2SourceShard1 then Q'.mkPos 4096 1 (by decide)
  else 0

def regularizedRankOnePrefixDemoScale2ChunkedStatisticalBudget
    (source : Fin 2) (target : Fin 2) : Q' :=
  Q'.divPos
    (finiteChunkedPairwiseRowResidualMajorant
        regularizedRankOnePrefixDemoScale2SourceChunks
        (fun chunk => regularizedRankOnePrefixDemoScale2ChunkMajorant chunk source target) +
      finitePseudocountBiasBudget
        regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount source target)
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets
      regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount)
    regularizedRankOnePrefixDemoScale2FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale2ChunkedStatisticalError : Q' := Q'.mkPos 2731 8192 (by decide)

def regularizedRankOnePrefixDemoScale2HybridStatisticalBudget
    (source : Fin 2) (target : Fin 2) : Q' :=
  Q'.divPos
    (Q'.ofNat regularizedRankOnePrefixDemoScale2Sources.length * regularizedRankOnePrefixDemoScale2PairwiseBound +
      finitePseudocountBiasBudget
        regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount source target)
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets
      regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount)
    regularizedRankOnePrefixDemoScale2FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale2HybridStatisticalError : Q' := Q'.mkPos 2731 8192 (by decide)

def regularizedRankOnePrefixDemoScale2StatisticalBudget
    (source : Fin 2) (target : Fin 2) : Q' :=
  Q'.divPos
    (Q'.ofNat regularizedRankOnePrefixDemoScale2Sources.length * regularizedRankOnePrefixDemoScale2PairwiseBound +
      regularizedRankOnePrefixDemoScale2Pseudocount *
        (Q'.ofNat regularizedRankOnePrefixDemoScale2Targets.length * regularizedRankOnePrefixDemoScale2Amplitude source target +
          finiteRowMass regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude source))
    (finiteRegularizedDenominator regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets
      regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount)
    regularizedRankOnePrefixDemoScale2FiniteDenominator_pos

def regularizedRankOnePrefixDemoScale2StatisticalError : Q' := Q'.mkPos 13653 8192 (by decide)
def regularizedRankOnePrefixDemoScale2Floor : Q' := Q'.mkPos 100642817 24576 (by decide)

theorem regularizedRankOnePrefixDemoScale2Pairwise_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        ∀ other, other ∈ regularizedRankOnePrefixDemoScale2Sources →
          Q'.abs (finitePairwiseRowCrossTerm
            regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude source other target) ≤
              regularizedRankOnePrefixDemoScale2PairwiseBound := by
  decide

theorem regularizedRankOnePrefixDemoScale2StatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        regularizedRankOnePrefixDemoScale2StatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale2StatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale2ExactStatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        regularizedRankOnePrefixDemoScale2ExactStatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale2ExactStatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale2ChunkBound :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        ∀ chunk, chunk ∈ regularizedRankOnePrefixDemoScale2SourceChunks →
          finitePairwiseRowResidualBudget
              chunk regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude source target ≤
            regularizedRankOnePrefixDemoScale2ChunkMajorant chunk source target := by
  decide

theorem regularizedRankOnePrefixDemoScale2ChunkedStatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        regularizedRankOnePrefixDemoScale2ChunkedStatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale2ChunkedStatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale2HybridStatisticalBudget_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        regularizedRankOnePrefixDemoScale2HybridStatisticalBudget source target ≤
          regularizedRankOnePrefixDemoScale2HybridStatisticalError := by
  decide

theorem regularizedRankOnePrefixDemoScale2GenericDefect_le_hybridStatisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount
            regularizedRankOnePrefixDemoScale2FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale2HybridStatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_of_pairwise_exactBias
      regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount
      regularizedRankOnePrefixDemoScale2FiniteDenominator_pos
      regularizedRankOnePrefixDemoScale2PairwiseBound (by decide)
      source target
      (by
        intro other other_mem
        exact regularizedRankOnePrefixDemoScale2Pairwise_le source source_mem target
          target_mem other other_mem))
    (regularizedRankOnePrefixDemoScale2HybridStatisticalBudget_le
      source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale2GenericDefect_le_chunkedStatisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount
            regularizedRankOnePrefixDemoScale2FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale2ChunkedStatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_chunkedMajorant_of_flatten_eq
      regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2SourceChunks regularizedRankOnePrefixDemoScale2SourceChunks_flatten
      regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount
      regularizedRankOnePrefixDemoScale2FiniteDenominator_pos
      (fun chunk => regularizedRankOnePrefixDemoScale2ChunkMajorant chunk source target)
      source target
      (by
        intro chunk chunk_mem
        exact regularizedRankOnePrefixDemoScale2ChunkBound source source_mem target
          target_mem chunk chunk_mem))
    (regularizedRankOnePrefixDemoScale2ChunkedStatisticalBudget_le
      source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale2GenericDefect_le_exactStatisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount
            regularizedRankOnePrefixDemoScale2FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale2ExactStatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_divPos_budget
      regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount
      regularizedRankOnePrefixDemoScale2FiniteDenominator_pos source target)
    (regularizedRankOnePrefixDemoScale2ExactStatisticalBudget_le
      source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale2GenericDefect_le_statisticalError :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        finiteRegularizedRankOneDefect
            regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude regularizedRankOnePrefixDemoScale2Pseudocount
            regularizedRankOnePrefixDemoScale2FiniteDenominator_pos source target ≤
          regularizedRankOnePrefixDemoScale2StatisticalError := by
  intro source source_mem target target_mem
  exact Q'.le_trans' _ _ _
    (finiteRegularizedRankOneDefect_le_of_pairwise
      regularizedRankOnePrefixDemoScale2Sources regularizedRankOnePrefixDemoScale2Targets regularizedRankOnePrefixDemoScale2Amplitude
      (by decide)
      regularizedRankOnePrefixDemoScale2FiniteDenominator_pos
      (by intro source' target' target'_mem; decide +revert)
      regularizedRankOnePrefixDemoScale2PairwiseBound (by decide)
      source target target_mem
      (by
        intro other other_mem
        exact regularizedRankOnePrefixDemoScale2Pairwise_le source source_mem target
          target_mem other other_mem))
    (regularizedRankOnePrefixDemoScale2StatisticalBudget_le source source_mem target target_mem)

theorem regularizedRankOnePrefixDemoScale2Defect_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        Q'.abs (regularizedRankOnePrefixDemoScale2Amplitude source target +
          -regularizedRankOnePrefixDemoScale2Projection source target) ≤ regularizedRankOnePrefixDemoScale2Error := by
  decide

theorem regularizedRankOnePrefixDemoScale2Floor_le :
    ∀ source, source ∈ regularizedRankOnePrefixDemoScale2Sources →
      ∀ target, target ∈ regularizedRankOnePrefixDemoScale2Targets →
        regularizedRankOnePrefixDemoScale2Floor ≤ regularizedRankOnePrefixDemoScale2Projection source target := by
  decide

end YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample

#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale0Pairwise_le
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale0GenericDefect_le_exactStatisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale0GenericDefect_le_chunkedStatisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale0GenericDefect_le_hybridStatisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale0GenericDefect_le_statisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale0Defect_le
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale0Floor_le
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale1Pairwise_le
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale1GenericDefect_le_exactStatisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale1GenericDefect_le_chunkedStatisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale1GenericDefect_le_hybridStatisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale1GenericDefect_le_statisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale1Defect_le
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale1Floor_le
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale2Pairwise_le
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale2GenericDefect_le_exactStatisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale2GenericDefect_le_chunkedStatisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale2GenericDefect_le_hybridStatisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale2GenericDefect_le_statisticalError
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale2Defect_le
#print axioms YMGap.Continuum.BF4BoundaryMessageRegularizedRankOnePrefixExample.regularizedRankOnePrefixDemoScale2Floor_le
