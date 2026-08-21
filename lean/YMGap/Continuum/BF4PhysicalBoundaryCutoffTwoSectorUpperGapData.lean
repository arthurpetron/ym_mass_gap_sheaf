/-
# Canonical cutoff-two sector upper-gap bridge data

The historical exact `64 x 64` LDL table was generated as the positive-head
mean-zero restriction of `(49/50) D - K` on the verified 65-state cutoff-two
sector.  This module states that rate and the corresponding sparse canonical
entry formula.  Separate row shards compare every historical table entry to
this formula by kernel reduction.

The penalty `d d^T` is retained in the canonical full matrix.  It vanishes
only after the explicit head-centered pullback, so the comparison does not
silently replace the canonical restriction by an unpenalized surrogate.

No full physical-carrier identification, cofinal cutoff family, completion
modulus, continuum theory, or Clay conclusion is constructed here.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.FiniteRationalHeadCenteredPullback

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalHeadCenteredPullback
open YMGap.Continuum.FiniteRationalMatrixPullback
open YMGap.Continuum.FiniteRationalPenalizedMatrix
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- The exact strict rate used by the historical cutoff-two LDL table. -/
def cutoffTwoSectorRate49Over50 : Q' :=
  Q'.mkPos 49 50 (by decide)

theorem cutoffTwoSectorRate49Over50_nonnegative :
    (0 : Q') ≤ cutoffTwoSectorRate49Over50 := by
  decide

theorem cutoffTwoSectorRate49Over50_lt_one :
    cutoffTwoSectorRate49Over50 < (1 : Q') := by
  decide

/-- The canonical head coordinate is legal because the exact vacuum-row
weight is strictly positive. -/
theorem cutoffTwoSectorRawRowSum_zero_pos_at49Over50 :
    (0 : Q') < cutoffTwoSectorRawRowSum 0 := by
  decide

/-- Local sparse-entry lemma.  Keeping it here avoids invalidating the broad
reverse-dependency tree of the generic pullback module. -/
private theorem finiteHeadCenteredMatrix_entry_local
    (n : Nat) (weight : Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (matrix : Nat → Nat → Q')
    (left right : Nat) (hleft : left < n) (hright : right < n) :
    finiteMatrixPullback (n + 1) matrix
        (finiteHeadCenteredTransform weight hhead) left right ≈
      let a := Q'.divPos (-(weight (left + 1))) (weight 0) hhead
      let b := Q'.divPos (-(weight (right + 1))) (weight 0) hhead
      (matrix 0 0 * b + matrix 0 (right + 1)) * a +
        (matrix (left + 1) 0 * b +
          matrix (left + 1) (right + 1)) := by
  let transform := finiteHeadCenteredTransform weight hhead
  let a := Q'.divPos (-(weight (left + 1))) (weight 0) hhead
  let b := Q'.divPos (-(weight (right + 1))) (weight 0) hhead
  have hinner : ∀ i,
      listQSum
          (fun j =>
            matrix i j * (transform i left * transform j right))
          (List.range (n + 1)) ≈
        (matrix i 0 * transform i left) * b +
          matrix i (right + 1) * transform i left := by
    intro i
    refine Q'.eqv_trans _
      (listQSum
        (fun j =>
          (matrix i j * transform i left) * transform j right)
        (List.range (n + 1))) _ ?_ ?_
    · apply listQSum_congr_on
      intro j _hj
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    · simpa only [transform, b] using
        (finiteHeadCenteredColumnSum n weight hhead
          (fun j => matrix i j * transform i left) right hright)
  refine Q'.eqv_trans _
    (listQSum
      (fun i =>
        (matrix i 0 * transform i left) * b +
          matrix i (right + 1) * transform i left)
      (List.range (n + 1))) _ ?_ ?_
  · unfold finiteMatrixPullback
    apply listQSum_congr_on
    intro i _hi
    exact hinner i
  · refine Q'.eqv_trans _
      (listQSum
        (fun i =>
          (matrix i 0 * b + matrix i (right + 1)) *
            transform i left)
        (List.range (n + 1))) _ ?_ ?_
    · apply listQSum_congr_on
      intro i _hi
      have hswap :
          (matrix i 0 * transform i left) * b ≈
            (matrix i 0 * b) * transform i left := by
        refine Q'.eqv_trans _
          (matrix i 0 * (transform i left * b)) _
          (Q'.mul_assoc_eqv _ _ _) ?_
        refine Q'.eqv_trans _
          (matrix i 0 * (b * transform i left)) _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_comm_eqv _ _)) ?_
        exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      exact Q'.eqv_trans _
        ((matrix i 0 * b) * transform i left +
          matrix i (right + 1) * transform i left) _
        (Q'.add_eqv_congr' hswap (Q'.eqv_refl _))
        (Q'.eqv_symm
          (Q'.add_mul_eqv
            (matrix i 0 * b) (matrix i (right + 1))
            (transform i left)))
    · simpa only [transform, a, b] using
        (finiteHeadCenteredColumnSum n weight hhead
          (fun i => matrix i 0 * b + matrix i (right + 1))
          left hleft)

/-- Sparse four-entry formula for the canonical upper pullback at rate
`49/50`.  The two division witnesses are part of the constructive data. -/
def cutoffTwoSectorCanonicalUpperSparseEntryAt49Over50
    (left right : Nat) : Q' :=
  let matrix := finiteUpperPenalizedMatrix cutoffTwoSectorRate49Over50
    cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
  let a := Q'.divPos (-(cutoffTwoSectorRawRowSum (left + 1)))
    (cutoffTwoSectorRawRowSum 0)
    cutoffTwoSectorRawRowSum_zero_pos_at49Over50
  let b := Q'.divPos (-(cutoffTwoSectorRawRowSum (right + 1)))
    (cutoffTwoSectorRawRowSum 0)
    cutoffTwoSectorRawRowSum_zero_pos_at49Over50
  (matrix 0 0 * b + matrix 0 (right + 1)) * a +
    (matrix (left + 1) 0 * b + matrix (left + 1) (right + 1))

/-- The sparse formula is exactly the corresponding entry of the canonical
positive-head upper matrix. -/
theorem cutoffTwoSectorCanonicalUpper_eqv_sparseAt49Over50
    (left right : Nat) (hleft : left < 64) (hright : right < 64) :
    finiteHeadCenteredUpperMatrix
        64 cutoffTwoSectorRate49Over50
        cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
        cutoffTwoSectorRawRowSum_zero_pos_at49Over50 left right ≈
      cutoffTwoSectorCanonicalUpperSparseEntryAt49Over50 left right := by
  simpa only [finiteHeadCenteredUpperMatrix,
    cutoffTwoSectorCanonicalUpperSparseEntryAt49Over50] using
    (finiteHeadCenteredMatrix_entry_local
      64 cutoffTwoSectorRawRowSum
      cutoffTwoSectorRawRowSum_zero_pos_at49Over50
      (finiteUpperPenalizedMatrix cutoffTwoSectorRate49Over50
        cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel)
      left right hleft hright)

/-- Executable comparison of one historical row with all 64 sparse canonical
entries.  Each concrete row theorem is compiled in its own process shard. -/
def cutoffTwoSectorCanonicalUpperBridgeRowCheck (row : Nat) : Bool :=
  (List.range 64).all fun column =>
    decide (cutoffTwoSectorMeanZeroMatrix row column ≈
      cutoffTwoSectorCanonicalUpperSparseEntryAt49Over50 row column)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap.cutoffTwoSectorCanonicalUpper_eqv_sparseAt49Over50
