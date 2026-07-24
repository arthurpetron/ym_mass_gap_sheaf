/-
# Core-B root-cumulative consumer alignment

The determinant telescope consumes only cumulatives starting at row zero.  A
proof of positivity at one preferred diagonal length is therefore not yet a
closure theorem.  This file records the sharper interface:

  C(0,r,n+1) ≈ R(0,r+n) + C(1,r,n).

Consequently a row-zero residual sign together with all-length row-one
cumulative positivity is sufficient for every offset determinant.  The file
contains only the reduction and consumer; it does not assert either analytic
sign premise.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, or noncomputable declaration.
-/

import YMGap.Continuum.CoreBDiagonalCumulative
import YMGap.Continuum.CoreBResidualPotential

namespace YMGap.Continuum.CoreBRootCumulative

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.CoreBStructuralRecurrence
open YMGap.Continuum.CoreBResidualPotential

local infix:50 " ≈ " => Q'.eqv

/-- **Root/row-one split.**  Separate the first term of an arbitrary root
diagonal, leaving a cumulative of one shorter length starting in row one. -/
theorem cumulativeResidual_zero_succ_split (w h : Q') (r : Nat) : ∀ n,
    cumulativeResidual w h 0 r (n + 1) ≈
      boundaryResidualAt w h 0 (r + n) + cumulativeResidual w h 1 r n
  | 0 => by
      simp only [cumulativeResidual, Nat.add_zero]
      exact Q'.eqv_trans _ _ _
        (q_zero_add_eqv (boundaryResidualAt w h 0 r))
        (Q'.eqv_symm (q_add_zero_eqv (boundaryResidualAt w h 0 r)))
  | n + 1 => by
      simp only [cumulativeResidual]
      have ih := cumulativeResidual_zero_succ_split w h (r + 1) n
      rw [show r + (n + 1) = r + 1 + n by omega]
      rw [show 0 + (n + 1) = n + 1 by omega]
      rw [show 1 + n = n + 1 by omega]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _
          (boundaryResidualAt w h (n + 1) r) ih) ?_
      exact Q'.add_assoc_eqv
        (boundaryResidualAt w h 0 (r + 1 + n))
        (cumulativeResidual w h 1 (r + 1) n)
        (boundaryResidualAt w h (n + 1) r)

/-- The exact aggregate interface actually needed by the determinant
telescope: nonnegativity only for cumulatives whose starting row is zero. -/
structure RootCumulativeResidualNonnegative (w h : Q') : Type where
  nonneg : ∀ r n, (0 : Q') ≤ cumulativeResidual w h 0 r n

/-- Row-zero residual signs plus all-length row-one diagonal positivity imply
the complete root cumulative certificate. -/
def rootCumulativeResidualNonnegativeOfRowOne {w h : Q'}
    (Hzero : ∀ r, (0 : Q') ≤ boundaryResidualAt w h 0 r)
    (Hone : ∀ r n, (0 : Q') ≤ cumulativeResidual w h 1 r n) :
    RootCumulativeResidualNonnegative w h where
  nonneg := by
    intro r n
    cases n with
    | zero => exact Q'.le_refl' 0
    | succ n =>
        have hsum : (0 : Q') ≤
            boundaryResidualAt w h 0 (r + n) + cumulativeResidual w h 1 r n :=
          Q'.zero_le_add _ _ (Hzero (r + n)) (Hone r n)
        exact Q'.le_trans' _ _ _ hsum
          (Q'.ge_of_eqv (cumulativeResidual_zero_succ_split w h r n))

/-- **Consumer-aligned propagation.**  Root cumulatives, rather than
cumulatives from every starting row, are sufficient for all Core-B offset
determinants. -/
theorem offsetDelta_nonneg_of_root_cumulative {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (H : RootCumulativeResidualNonnegative w h) (s r : Nat) :
    (0 : Q') ≤ offsetDelta w h s r := by
  have hbase := offsetDelta_zero_nonneg hh0 hhw (r + s)
  have hcum := H.nonneg r s
  have hsum : (0 : Q') ≤
      offsetDelta w h 0 (r + s) + cumulativeResidual w h 0 r s :=
    Q'.zero_le_add _ _ hbase hcum
  have htel := offsetDelta_diagonal_telescope w h 0 r s
  simpa only [Nat.zero_add] using
    Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv htel)

/-- Direct row-one form of the consumer-aligned closure criterion. -/
theorem offsetDelta_nonneg_of_rowOne_cumulative {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (Hzero : ∀ r, (0 : Q') ≤ boundaryResidualAt w h 0 r)
    (Hone : ∀ r n, (0 : Q') ≤ cumulativeResidual w h 1 r n)
    (s r : Nat) : (0 : Q') ≤ offsetDelta w h s r :=
  offsetDelta_nonneg_of_root_cumulative hh0 hhw
    (rootCumulativeResidualNonnegativeOfRowOne Hzero Hone) s r

#print axioms cumulativeResidual_zero_succ_split
#print axioms rootCumulativeResidualNonnegativeOfRowOne
#print axioms offsetDelta_nonneg_of_root_cumulative
#print axioms offsetDelta_nonneg_of_rowOne_cumulative

end YMGap.Continuum.CoreBRootCumulative
