/-
# Canonical unordered pairs for the cutoff-two spatial S3 action

This module defines a deterministic least-code representative of an unordered
pair under the six checked spatial actions.  Physical-kernel transport and
stored-raw-table certificates are deliberately kept in separate modules so
that this finite combinatorial datum remains cheap to elaborate.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3KernelAction

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3KernelAction

structure CutoffTwoSectorPair : Type where
  row : Fin 65
  column : Fin 65
  deriving DecidableEq, Repr

def cutoffTwoSectorPairCode (pair : CutoffTwoSectorPair) : Nat :=
  pair.row.val * 65 + pair.column.val

def cutoffTwoSectorPairNormalize
    (pair : CutoffTwoSectorPair) : CutoffTwoSectorPair :=
  if pair.row.val ≤ pair.column.val then pair
  else ⟨pair.column, pair.row⟩

theorem cutoffTwoSectorPairNormalize_upper (pair : CutoffTwoSectorPair) :
    (cutoffTwoSectorPairNormalize pair).row.val ≤
      (cutoffTwoSectorPairNormalize pair).column.val := by
  unfold cutoffTwoSectorPairNormalize
  by_cases horder : pair.row.val ≤ pair.column.val
  · simp [horder]
  · simp [horder]
    omega

def cutoffTwoSectorPairAction
    (action : CutoffTwoSpatialS3)
    (pair : CutoffTwoSectorPair) : CutoffTwoSectorPair :=
  ⟨cutoffTwoSpatialS3Action action pair.row,
    cutoffTwoSpatialS3Action action pair.column⟩

def cutoffTwoSectorPairActionNormalized
    (action : CutoffTwoSpatialS3)
    (pair : CutoffTwoSectorPair) : CutoffTwoSectorPair :=
  cutoffTwoSectorPairNormalize (cutoffTwoSectorPairAction action pair)

theorem cutoffTwoSectorPairActionNormalized_upper
    (action : CutoffTwoSpatialS3)
    (pair : CutoffTwoSectorPair) :
    (cutoffTwoSectorPairActionNormalized action pair).row.val ≤
      (cutoffTwoSectorPairActionNormalized action pair).column.val :=
  cutoffTwoSectorPairNormalize_upper _

def cutoffTwoSpatialS3BetterAction
    (pair : CutoffTwoSectorPair)
    (current candidate : CutoffTwoSpatialS3) : CutoffTwoSpatialS3 :=
  if cutoffTwoSectorPairCode
        (cutoffTwoSectorPairActionNormalized candidate pair) <
      cutoffTwoSectorPairCode
        (cutoffTwoSectorPairActionNormalized current pair) then
    candidate
  else current

/-- The first least-code normal word, using the declared six-word order. -/
def cutoffTwoSectorPairCanonicalAction
    (pair : CutoffTwoSectorPair) : CutoffTwoSpatialS3 :=
  cutoffTwoSpatialS3Elements.foldl
    (cutoffTwoSpatialS3BetterAction pair) .identity

def cutoffTwoSectorPairCanonical
    (pair : CutoffTwoSectorPair) : CutoffTwoSectorPair :=
  cutoffTwoSectorPairActionNormalized
    (cutoffTwoSectorPairCanonicalAction pair) pair

theorem cutoffTwoSectorPairCanonical_upper (pair : CutoffTwoSectorPair) :
    (cutoffTwoSectorPairCanonical pair).row.val ≤
      (cutoffTwoSectorPairCanonical pair).column.val := by
  rw [cutoffTwoSectorPairCanonical]
  exact cutoffTwoSectorPairActionNormalized_upper _ _

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData
