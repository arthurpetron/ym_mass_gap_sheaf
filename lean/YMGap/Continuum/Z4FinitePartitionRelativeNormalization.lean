/-
# Relative normalization from a constructive partition floor

The repaired finite-box graph partition has a derived unit vacuum floor.  This
module turns that floor into the denominator estimate needed by a normalized
cutoff or volume limit: an additive bound on two positive partition functions
immediately becomes a relative bound on their quotient.

No cutoff- or volume-comparison estimate is assumed to be proved here.  The
load-bearing content is the exact denominator transport, specialized afterward
to the production fusion-complete graph partition.  The missing analytic input
remains an additive comparison for the actual interacting graph sums.
-/

import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Continuum.Z4FiniteGraphVacuumFloor

namespace YMGap.Continuum.Z4FinitePartitionRelativeNormalization

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.Z4FiniteGraphVacuumFloor

/-- A unit floor absorbs an additive error into the denominator.  Consequently
the quotient of two partition values differs relatively from one by no more
than their additive error. -/
theorem additive_partition_error_to_relative
    {Z Z' error : Q'} (hfloor : (1 : Q') ≤ Z)
    (herror : (0 : Q') ≤ error)
    (hdiff : absQ (Z' + -Z) ≤ error) :
    absQ (Q'.divPos Z' Z
        (ClusteringImpliesGap.lt_of_lt_of_le (by decide : (0 : Q') < 1) hfloor) +
      -(1 : Q')) ≤ error := by
  have hZ : (0 : Q') < Z :=
    ClusteringImpliesGap.lt_of_lt_of_le (by decide : (0 : Q') < 1) hfloor
  have hscale : error ≤ error * Z := by
    have hmul : error * (1 : Q') ≤ error * Z :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor herror
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_one_eqv error)) hmul
  exact absQ_divPos_sub_one_le hZ
    (Q'.le_trans' _ _ _ hdiff hscale)

/-- Concrete specialization to the repaired production graph.  Thus any
additive comparison between two external cutoffs at a fixed box immediately
controls their relative partition quotient with the same error. -/
theorem fusionCompleteVertexPartition_relative_cutoff
    {K K' n : Nat} {error : Q'}
    (herror : (0 : Q') ≤ error)
    (hdiff : absQ
        (fusionCompleteVertexPartition K' n +
          -fusionCompleteVertexPartition K n) ≤ error) :
    absQ
        (Q'.divPos
            (fusionCompleteVertexPartition K' n)
            (fusionCompleteVertexPartition K n)
            (fusionCompleteVertexPartition_pos K n) +
          -(1 : Q')) ≤ error := by
  exact additive_partition_error_to_relative
    (fusionCompleteVertexPartition_one_le K n) herror hdiff

/-- The same denominator transport is uniform in the box labels: an explicit
stage modulus for additive production-partition differences is already a
relative modulus, with no volume-dependent loss. -/
theorem fusionCompleteVertexPartition_relative_modulus
    (cutoff : Nat → Nat) (error : Nat → Q')
    (herror : ∀ stage, (0 : Q') ≤ error stage)
    (hadditive : ∀ stage extension n,
      absQ
        (fusionCompleteVertexPartition (cutoff (stage + extension)) n +
          -fusionCompleteVertexPartition (cutoff stage) n) ≤ error stage) :
    ∀ stage extension n,
      absQ
        (Q'.divPos
            (fusionCompleteVertexPartition (cutoff (stage + extension)) n)
            (fusionCompleteVertexPartition (cutoff stage) n)
            (fusionCompleteVertexPartition_pos (cutoff stage) n) +
          -(1 : Q')) ≤ error stage := by
  intro stage extension n
  exact fusionCompleteVertexPartition_relative_cutoff
    (herror stage) (hadditive stage extension n)

#print axioms additive_partition_error_to_relative
#print axioms fusionCompleteVertexPartition_relative_cutoff
#print axioms fusionCompleteVertexPartition_relative_modulus

end YMGap.Continuum.Z4FinitePartitionRelativeNormalization
