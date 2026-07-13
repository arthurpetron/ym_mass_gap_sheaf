/-
`FusedOffDiagonalCompression` continues the enriched-operator audit.

A positive diagonal/convex compression of the two distinct endpoint modes
cannot preserve the coarse fused eigenvalue unless it assigns zero weight to
the new shell.  This is proved by positive cancellation and machine-instantiated
at consecutive quadratic cutoffs.

The minimal genuine coupling is then constructed explicitly.  A rational
3-4-5 rotation conjugates the two-mode diagonal spectrum, producing a symmetric
2x2 operator with nonzero off-diagonal entry while retaining the old and new
fused eigenvalues on explicit rational eigenvectors.  Thus any viable RG
compression must use a coupled shell (and subsequently control its Schur
complement); positive diagonal averaging cannot supply the cross-scale law.
-/

import YMGap.Continuum.CorrectedCarrierOperatorBridge

namespace YMGap.Continuum.FusedOffDiagonalCompression

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.CorrectedCarrierOperatorBridge
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.QuadraticCutoffSchedule

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
               Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

/-! ## 1. Positive diagonal compression is forced to ignore the shell -/

/-- Convex diagonal compression of an old and a new eigenmode. -/
def diagonalCompress (u lamOld lamNew : Q') : Q' :=
  ((1 : Q') - u) * lamOld + u * lamNew

/-- The residual equality left after cancelling the unchanged head contribution
from a diagonal compression.  A positive shell weight must transport the new
shell eigenvalue to the old one. -/
structure PositiveDiagonalCompression (lamOld lamNew : Q') : Type where
  shellWeight : Q'
  shellWeight_pos : (0 : Q') < shellWeight
  shellPreserves : shellWeight * lamNew ≈ shellWeight * lamOld

/-- Positive cancellation shows that such a diagonal compression forces the
two eigenvalues to coincide. -/
theorem positive_diagonal_compression_forces_eigen_eq
    {lamOld lamNew : Q'} (C : PositiveDiagonalCompression lamOld lamNew) :
    lamOld ≈ lamNew :=
  Q'.eqv_symm (Q'.mul_left_cancel_of_pos C.shellWeight_pos C.shellPreserves)

/-- The consecutive endpoint fused eigenvalues are exactly distinct. -/
theorem endpoint_consecutive_fused_eigenvalues_ne :
    ¬ (lamPW (1 : Q') (Ncut 0) 1 ≈ lamPW (1 : Q') (Ncut 1) 1) := by
  decide

/-- A positive diagonal shell weight cannot preserve the coarse endpoint mode
at consecutive quadratic cutoffs. -/
theorem no_positive_endpoint_diagonal_compression
    (C : PositiveDiagonalCompression
      (lamPW (1 : Q') (Ncut 0) 1)
      (lamPW (1 : Q') (Ncut 1) 1)) : False := by
  exact endpoint_consecutive_fused_eigenvalues_ne
    (positive_diagonal_compression_forces_eigen_eq C)

/-! ## 2. Minimal rational off-diagonal coupling -/

private def q35 : Q' := Q'.mkPos 3 5 (by decide)
private def q45 : Q' := Q'.mkPos 4 5 (by decide)

private theorem rotation_norm : q35 * q35 + q45 * q45 ≈ (1 : Q') := by
  decide

/-- Old-mode unit eigenvector of the rational rotation. -/
def oldVec : QSeq := fun i => if i = 0 then q35 else if i = 1 then q45 else 0

/-- New shell-mode unit eigenvector, orthogonal to `oldVec`. -/
def shellVec : QSeq := fun i => if i = 0 then -q45 else if i = 1 then q35 else 0

/-- Rotated first diagonal entry. -/
def rot00 (lamOld lamNew : Q') : Q' :=
  (q35 * q35) * lamOld + (q45 * q45) * lamNew

/-- Rotated second diagonal entry. -/
def rot11 (lamOld lamNew : Q') : Q' :=
  (q45 * q45) * lamOld + (q35 * q35) * lamNew

/-- The minimal off-diagonal shell coupling. -/
def rot01 (lamOld lamNew : Q') : Q' :=
  (q35 * q45) * lamOld + -((q35 * q45) * lamNew)

/-- The exact 3-4-5 rotation preserves the two-by-two determinant. -/
theorem rotated_det (lamOld lamNew : Q') :
    rot00 lamOld lamNew * rot11 lamOld lamNew +
        -(rot01 lamOld lamNew * rot01 lamOld lamNew) ≈
      lamOld * lamNew := by
  let x2 := q35 * q35
  let y2 := q45 * q45
  let xy := q35 * q45
  let Taa := (x2 * y2) * (lamOld * lamOld)
  let Tbb := (x2 * y2) * (lamNew * lamNew)
  let Txx := (x2 * x2) * (lamOld * lamNew)
  let Tyy := (y2 * y2) * (lamOld * lamNew)
  let Txy := (xy * xy) * (lamOld * lamNew)
  let core := ((Txx + Tyy) + Txy) + Txy
  have hexpand :
      rot00 lamOld lamNew * rot11 lamOld lamNew +
          -(rot01 lamOld lamNew * rot01 lamOld lamNew) ≈
        ((Taa + (-Taa)) + (Tbb + (-Tbb))) + core := by
    unfold rot00 rot11 rot01 core
    unfold Taa Tbb Txx Tyy Txy x2 y2 xy
    ring_qeqv
  have hcancel :
      ((Taa + (-Taa)) + (Tbb + (-Tbb))) + core ≈ core := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ core
        (Q'.add_eqv_congr'
          (Q'.add_neg_self_eqv Taa) (Q'.add_neg_self_eqv Tbb))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ core (QPoly.q_zero_add_eqv (0 : Q'))) ?_
    exact QPoly.q_zero_add_eqv core
  have hfactor :
      core ≈
        ((q35 * q35 + q45 * q45) * (q35 * q35 + q45 * q45)) *
          (lamOld * lamNew) := by
    unfold core
    unfold Txx Tyy Txy x2 y2 xy
    ring_qeqv
  refine Q'.eqv_trans _ _ _ hexpand ?_
  refine Q'.eqv_trans _ _ _ hcancel ?_
  refine Q'.eqv_trans _ _ _ hfactor ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (lamOld * lamNew)
      (Q'.mul_eqv_congr_right _ _ _ rotation_norm)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (lamOld * lamNew)
      (Q'.one_mul_eqv (q35 * q35 + q45 * q45))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (lamOld * lamNew) rotation_norm) ?_
  exact Q'.one_mul_eqv _

/-- The rotated head entry is at most the old eigenvalue whenever the new
eigenvalue is nonnegative and no larger than the old one. -/
theorem rot00_le_left {lamOld lamNew : Q'}
    (hnewOld : lamNew <= lamOld) :
    rot00 lamOld lamNew <= lamOld := by
  have hq0 : (0 : Q') <= q45 * q45 :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (by decide)) (Q'.le_of_lt (by decide))
  have hscaled : (q45 * q45) * lamNew <= (q45 * q45) * lamOld :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hnewOld hq0
  have hadd :
      (q35 * q35) * lamOld + (q45 * q45) * lamNew <=
        (q35 * q35) * lamOld + (q45 * q45) * lamOld :=
    Q'.add_le_add_left _ _ _ hscaled
  have hcollapse :
      (q35 * q35) * lamOld + (q45 * q45) * lamOld ≈ lamOld := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv (q35 * q35) (q45 * q45) lamOld)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ lamOld rotation_norm) ?_
    exact Q'.one_mul_eqv _
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hcollapse)

/-- Symmetric entry function for the rationally rotated two-mode operator. -/
def rotatedEntry (lamOld lamNew : Q') (i j : Nat) : Q' :=
  if i = j then
    if i = 0 then rot00 lamOld lamNew else rot11 lamOld lamNew
  else if Nat.min i j = 0 ∧ Nat.max i j = 1 then
    rot01 lamOld lamNew
  else 0

theorem rotatedEntry_symm (lamOld lamNew : Q') (i j : Nat) :
    rotatedEntry lamOld lamNew i j = rotatedEntry lamOld lamNew j i := by
  unfold rotatedEntry
  by_cases h : i = j
  · subst j
    rfl
  · have h' : ¬ j = i := fun e => h e.symm
    rw [if_neg h, if_neg h']
    by_cases hp : Nat.min i j = 0 ∧ Nat.max i j = 1
    · have hp' : Nat.min j i = 0 ∧ Nat.max j i = 1 := by
        exact ⟨(Nat.min_comm j i).trans hp.1,
          (Nat.max_comm j i).trans hp.2⟩
      rw [if_pos hp, if_pos hp']
    · have hp' : ¬ (Nat.min j i = 0 ∧ Nat.max j i = 1) := by
        intro hs
        apply hp
        exact ⟨(Nat.min_comm i j).trans hs.1,
          (Nat.max_comm i j).trans hs.2⟩
      rw [if_neg hp, if_neg hp']

/-- The genuinely coupled symmetric two-mode transfer operator. -/
def rotatedFusedOp (lamOld lamNew : Q') : FiniteOp where
  k := 2
  entry := rotatedEntry lamOld lamNew
  symm := rotatedEntry_symm lamOld lamNew

/-- Coordinate zero of the old endpoint rotated eigenvector equation. -/
theorem endpoint_rotated_old_eigen_zero :
    ((rotatedFusedOp
      (lamPW (1 : Q') (Ncut 0) 1)
      (lamPW (1 : Q') (Ncut 1) 1)).apply oldVec 0) ≈
        lamPW (1 : Q') (Ncut 0) 1 * oldVec 0 := by
  decide

/-- Coordinate one of the old endpoint rotated eigenvector equation. -/
theorem endpoint_rotated_old_eigen_one :
    ((rotatedFusedOp
      (lamPW (1 : Q') (Ncut 0) 1)
      (lamPW (1 : Q') (Ncut 1) 1)).apply oldVec 1) ≈
        lamPW (1 : Q') (Ncut 0) 1 * oldVec 1 := by
  decide

/-- Coordinate zero of the new endpoint shell eigenvector equation. -/
theorem endpoint_rotated_shell_eigen_zero :
    ((rotatedFusedOp
      (lamPW (1 : Q') (Ncut 0) 1)
      (lamPW (1 : Q') (Ncut 1) 1)).apply shellVec 0) ≈
        lamPW (1 : Q') (Ncut 1) 1 * shellVec 0 := by
  decide

/-- Coordinate one of the new endpoint shell eigenvector equation. -/
theorem endpoint_rotated_shell_eigen_one :
    ((rotatedFusedOp
      (lamPW (1 : Q') (Ncut 0) 1)
      (lamPW (1 : Q') (Ncut 1) 1)).apply shellVec 1) ≈
        lamPW (1 : Q') (Ncut 1) 1 * shellVec 1 := by
  decide

/-- The endpoint off-diagonal entry is nonzero, so the coupled construction is
not a disguised diagonal direct sum. -/
theorem endpoint_rotated_coupling_nonzero :
    ¬ (rot01
      (lamPW (1 : Q') (Ncut 0) 1)
      (lamPW (1 : Q') (Ncut 1) 1) ≈ (0 : Q')) := by
  decide

/-- The coupled endpoint operator carries the old coarse fused mode on the
explicit mixed vector `(3/5,4/5)`. -/
theorem endpoint_coupled_old_mode_zero :
    ((rotatedFusedOp
      (lamPW (1 : Q') (Ncut 0) 1)
      (lamPW (1 : Q') (Ncut 1) 1)).apply oldVec 0) ≈
        lamPW (1 : Q') (Ncut 0) 1 * oldVec 0 :=
  endpoint_rotated_old_eigen_zero

/-- The same operator carries the new fused shell mode on the orthogonal mixed
vector `(-4/5,3/5)`. -/
theorem endpoint_coupled_shell_mode_zero :
    ((rotatedFusedOp
      (lamPW (1 : Q') (Ncut 0) 1)
      (lamPW (1 : Q') (Ncut 1) 1)).apply shellVec 0) ≈
        lamPW (1 : Q') (Ncut 1) 1 * shellVec 0 :=
  endpoint_rotated_shell_eigen_zero

end YMGap.Continuum.FusedOffDiagonalCompression

#print axioms YMGap.Continuum.FusedOffDiagonalCompression.rotated_det

#print axioms YMGap.Continuum.FusedOffDiagonalCompression.positive_diagonal_compression_forces_eigen_eq
#print axioms YMGap.Continuum.FusedOffDiagonalCompression.no_positive_endpoint_diagonal_compression
#print axioms YMGap.Continuum.FusedOffDiagonalCompression.rot00_le_left
#print axioms YMGap.Continuum.FusedOffDiagonalCompression.rotatedEntry_symm
#print axioms YMGap.Continuum.FusedOffDiagonalCompression.endpoint_rotated_old_eigen_zero
#print axioms YMGap.Continuum.FusedOffDiagonalCompression.endpoint_rotated_old_eigen_one
#print axioms YMGap.Continuum.FusedOffDiagonalCompression.endpoint_rotated_shell_eigen_zero
#print axioms YMGap.Continuum.FusedOffDiagonalCompression.endpoint_rotated_shell_eigen_one
#print axioms YMGap.Continuum.FusedOffDiagonalCompression.endpoint_rotated_coupling_nonzero
#print axioms YMGap.Continuum.FusedOffDiagonalCompression.endpoint_coupled_old_mode_zero
#print axioms YMGap.Continuum.FusedOffDiagonalCompression.endpoint_coupled_shell_mode_zero
