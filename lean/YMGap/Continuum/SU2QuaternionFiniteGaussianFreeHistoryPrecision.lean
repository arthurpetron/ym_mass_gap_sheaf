/-
# Coordinate precision for the finite free Gaussian history

This leaf encodes a coordinate-space precision used by the finite
FREE-reference calculation before any spatial mode diagonalization.  A supplied
finite curl-incidence matrix produces the ambient spatial precision `d^* d`.
For a gauge theory this ambient matrix can have gradient zero modes; this file
does not assert invertibility.  The time precision has the two free endpoints
from the paper calculation: endpoint degree one, interior degree two, adjacent
coefficient minus one, and zero time degree for a one-slice history.  Their
Kronecker sum is flattened into the ordinary `Nat` matrix interface consumed by
the rational inverse and LDL checkers only after an explicit invertible
coordinate restriction or positive completion has been supplied.

An executable two-sided inverse check identifies a proposed rational
covariance with this precision.  Combining that check with the existing
positive LDL and Heron-factor checks gives a rational covariance factor with
an explicit entrywise geometric error.  No Fourier/trigonometric mode rows or
irrational square roots are selected.

Consumer: an explicitly gauge-reduced finite coordinate-space FREE Gaussian
reference behind the retained three-color trace-source covariance.  The
concrete open-cube edge/face incidence table, the transverse coordinate map,
and an all-scale inverse/LDL certificate producer remain separate.  This file
proves no Gaussian density or pushforward law,
compact-Haar/ORIGINAL comparison, uniform response estimate, continuum theory,
or physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor

local infix:50 " ≈ " => Q'.eqv

/-- Spatial coordinate precision `d^* d` from a finite rational curl-incidence
matrix whose rows are faces and columns are edge coordinates. -/
def finiteCurlPrecision (faceCount : Nat) (curl : Nat → Nat → Q')
    (left right : Nat) : Q' :=
  listQSum
    (fun face => curl face left * curl face right)
    (List.range faceCount)

theorem finiteCurlPrecision_symm (faceCount : Nat)
    (curl : Nat → Nat → Q') (left right : Nat) :
    finiteCurlPrecision faceCount curl left right ≈
      finiteCurlPrecision faceCount curl right left := by
  unfold finiteCurlPrecision
  exact listQSum_congr
    (fun face => Q'.mul_comm_eqv (curl face left) (curl face right))
    (List.range faceCount)

/-- Number of scalar coordinate slices in a history with bonds `0,...,T-1`. -/
def historySliceCount (timeBonds : Nat) : Nat := timeBonds + 1

/-- Temporal diagonal degree for the literal free-endpoint action. -/
def freeTemporalDegree (timeBonds time : Nat) : Q' :=
  if timeBonds = 0 then 0
  else if time = 0 ∨ time = timeBonds then 1 else 2

/-- Scalar temporal precision entry.  It is the free-endpoint tridiagonal
matrix, including the one-slice `timeBonds = 0` case. -/
def freeTemporalPrecision (timeBonds left right : Nat) : Q' :=
  if left = right then freeTemporalDegree timeBonds left
  else if left + 1 = right ∨ right + 1 = left then -1 else 0

theorem freeTemporalPrecision_symm (timeBonds left right : Nat) :
    freeTemporalPrecision timeBonds left right =
      freeTemporalPrecision timeBonds right left := by
  unfold freeTemporalPrecision
  by_cases heq : left = right
  · subst right
    simp
  · have hreverse : right ≠ left := fun h => heq h.symm
    rw [if_neg heq, if_neg hreverse]
    by_cases hadjacent : left + 1 = right ∨ right + 1 = left
    · have hreverseAdjacent : right + 1 = left ∨ left + 1 = right :=
        hadjacent.elim Or.inr Or.inl
      rw [if_pos hadjacent, if_pos hreverseAdjacent]
    · have hreverseAdjacent : ¬(right + 1 = left ∨ left + 1 = right) := by
        intro h
        exact hadjacent (h.elim Or.inr Or.inl)
      rw [if_neg hadjacent, if_neg hreverseAdjacent]

/-- Flatten `(time, spatial)` with spatial coordinate as the mixed-radix
digit. -/
def historyIndex (spatialSize time spatial : Nat) : Nat :=
  spatialSize * time + spatial

def historyTime (spatialSize index : Nat) : Nat := index / spatialSize

def historySpatial (spatialSize index : Nat) : Nat := index % spatialSize

def historyCoordinateCount (timeBonds spatialSize : Nat) : Nat :=
  historySliceCount timeBonds * spatialSize

theorem historyTime_index {spatialSize time spatial : Nat}
    (hsize : 0 < spatialSize) (hspatial : spatial < spatialSize) :
    historyTime spatialSize (historyIndex spatialSize time spatial) = time := by
  unfold historyTime historyIndex
  rw [Nat.mul_add_div hsize, Nat.div_eq_of_lt hspatial, Nat.add_zero]

theorem historySpatial_index {spatialSize time spatial : Nat}
    (hspatial : spatial < spatialSize) :
    historySpatial spatialSize (historyIndex spatialSize time spatial) = spatial := by
  unfold historySpatial historyIndex
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hspatial]

/-- Kronecker-sum precision `I_time ⊗ spatial + temporal ⊗ I_space`
on flattened finite-history coordinates. -/
def freeHistoryPrecision (timeBonds spatialSize : Nat)
    (spatialPrecision : Nat → Nat → Q') (left right : Nat) : Q' :=
  (if historyTime spatialSize left = historyTime spatialSize right then
      spatialPrecision (historySpatial spatialSize left)
        (historySpatial spatialSize right)
    else 0) +
  (if historySpatial spatialSize left = historySpatial spatialSize right then
      freeTemporalPrecision timeBonds
        (historyTime spatialSize left) (historyTime spatialSize right)
    else 0)

/-- Entry formula on valid flattened coordinates. -/
theorem freeHistoryPrecision_index
    (timeBonds spatialSize : Nat) (spatialPrecision : Nat → Nat → Q')
    (leftTime rightTime leftSpatial rightSpatial : Nat)
    (hsize : 0 < spatialSize)
    (hleft : leftSpatial < spatialSize)
    (hright : rightSpatial < spatialSize) :
    freeHistoryPrecision timeBonds spatialSize spatialPrecision
        (historyIndex spatialSize leftTime leftSpatial)
        (historyIndex spatialSize rightTime rightSpatial) =
      (if leftTime = rightTime then
          spatialPrecision leftSpatial rightSpatial else 0) +
      (if leftSpatial = rightSpatial then
          freeTemporalPrecision timeBonds leftTime rightTime else 0) := by
  unfold freeHistoryPrecision
  rw [historyTime_index hsize hleft, historyTime_index hsize hright,
    historySpatial_index hleft, historySpatial_index hright]

theorem freeHistoryPrecision_sameTime
    (timeBonds spatialSize : Nat) (spatialPrecision : Nat → Nat → Q')
    (time leftSpatial rightSpatial : Nat)
    (hsize : 0 < spatialSize)
    (hleft : leftSpatial < spatialSize)
    (hright : rightSpatial < spatialSize) :
    freeHistoryPrecision timeBonds spatialSize spatialPrecision
        (historyIndex spatialSize time leftSpatial)
        (historyIndex spatialSize time rightSpatial) =
      spatialPrecision leftSpatial rightSpatial +
        (if leftSpatial = rightSpatial then
          freeTemporalDegree timeBonds time else 0) := by
  rw [freeHistoryPrecision_index timeBonds spatialSize spatialPrecision
    time time leftSpatial rightSpatial hsize hleft hright]
  simp [freeTemporalPrecision]

theorem freeHistoryPrecision_adjacentTime
    (timeBonds spatialSize : Nat) (spatialPrecision : Nat → Nat → Q')
    (time leftSpatial rightSpatial : Nat)
    (hsize : 0 < spatialSize)
    (hleft : leftSpatial < spatialSize)
    (hright : rightSpatial < spatialSize) :
    freeHistoryPrecision timeBonds spatialSize spatialPrecision
        (historyIndex spatialSize time leftSpatial)
        (historyIndex spatialSize (time + 1) rightSpatial) ≈
      if leftSpatial = rightSpatial then -1 else 0 := by
  rw [freeHistoryPrecision_index timeBonds spatialSize spatialPrecision
    time (time + 1) leftSpatial rightSpatial hsize hleft hright]
  have htime : time ≠ time + 1 := by omega
  have hadjacent : time + 1 = time + 1 ∨ time + 1 + 1 = time := Or.inl rfl
  by_cases hspace : leftSpatial = rightSpatial
  · rw [if_neg htime, if_pos hspace, if_pos hspace]
    unfold freeTemporalPrecision
    rw [if_neg htime, if_pos hadjacent]
    exact QPoly.q_zero_add_eqv _
  · rw [if_neg htime, if_neg hspace, if_neg hspace]
    exact QPoly.q_zero_add_eqv _

theorem freeHistoryPrecision_separatedTime
    (timeBonds spatialSize : Nat) (spatialPrecision : Nat → Nat → Q')
    (leftTime rightTime leftSpatial rightSpatial : Nat)
    (hsize : 0 < spatialSize)
    (hleft : leftSpatial < spatialSize)
    (hright : rightSpatial < spatialSize)
    (hne : leftTime ≠ rightTime)
    (hforward : leftTime + 1 ≠ rightTime)
    (hbackward : rightTime + 1 ≠ leftTime) :
    freeHistoryPrecision timeBonds spatialSize spatialPrecision
        (historyIndex spatialSize leftTime leftSpatial)
        (historyIndex spatialSize rightTime rightSpatial) ≈ 0 := by
  rw [freeHistoryPrecision_index timeBonds spatialSize spatialPrecision
    leftTime rightTime leftSpatial rightSpatial hsize hleft hright]
  rw [if_neg hne]
  by_cases hspace : leftSpatial = rightSpatial
  · rw [if_pos hspace]
    unfold freeTemporalPrecision
    rw [if_neg hne, if_neg (not_or_intro hforward hbackward)]
    exact QPoly.q_zero_add_eqv _
  · rw [if_neg hspace]
    exact QPoly.q_zero_add_eqv _

theorem freeHistoryPrecision_symm
    (timeBonds spatialSize : Nat) (spatialPrecision : Nat → Nat → Q')
    (hspatial : ∀ left right,
      spatialPrecision left right ≈ spatialPrecision right left)
    (left right : Nat) :
    freeHistoryPrecision timeBonds spatialSize spatialPrecision left right ≈
      freeHistoryPrecision timeBonds spatialSize spatialPrecision right left := by
  unfold freeHistoryPrecision
  by_cases htime : historyTime spatialSize left = historyTime spatialSize right
  · have htimeReverse : historyTime spatialSize right = historyTime spatialSize left :=
      htime.symm
    rw [if_pos htime, if_pos htimeReverse]
    by_cases hspace : historySpatial spatialSize left = historySpatial spatialSize right
    · have hspaceReverse : historySpatial spatialSize right =
          historySpatial spatialSize left := hspace.symm
      rw [if_pos hspace, if_pos hspaceReverse]
      exact Q'.add_eqv_congr'
        (hspatial _ _)
        (Q'.eqv_of_eq (freeTemporalPrecision_symm _ _ _))
    · have hspaceReverse : historySpatial spatialSize right ≠
          historySpatial spatialSize left := fun h => hspace h.symm
      rw [if_neg hspace, if_neg hspaceReverse]
      exact Q'.add_eqv_congr' (hspatial _ _) (Q'.eqv_refl _)
  · have htimeReverse : historyTime spatialSize right ≠ historyTime spatialSize left :=
      fun h => htime h.symm
    rw [if_neg htime, if_neg htimeReverse]
    by_cases hspace : historySpatial spatialSize left = historySpatial spatialSize right
    · have hspaceReverse : historySpatial spatialSize right =
          historySpatial spatialSize left := hspace.symm
      rw [if_pos hspace, if_pos hspaceReverse]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_of_eq (freeTemporalPrecision_symm _ _ _))
    · have hspaceReverse : historySpatial spatialSize right ≠
          historySpatial spatialSize left := fun h => hspace h.symm
      rw [if_neg hspace, if_neg hspaceReverse]
      exact Q'.eqv_refl _

/-- Actual coordinate precision from a supplied finite spatial curl incidence. -/
def freeHistoryCurlPrecision (timeBonds edgeCount faceCount : Nat)
    (curl : Nat → Nat → Q') : Nat → Nat → Q' :=
  freeHistoryPrecision timeBonds edgeCount (finiteCurlPrecision faceCount curl)

theorem freeHistoryCurlPrecision_symm
    (timeBonds edgeCount faceCount : Nat) (curl : Nat → Nat → Q')
    (left right : Nat) :
    freeHistoryCurlPrecision timeBonds edgeCount faceCount curl left right ≈
      freeHistoryCurlPrecision timeBonds edgeCount faceCount curl right left := by
  exact freeHistoryPrecision_symm timeBonds edgeCount
    (finiteCurlPrecision faceCount curl)
    (finiteCurlPrecision_symm faceCount curl) left right

/-- Literal finite matrix product used by the executable inverse certificate. -/
def finiteMatrixProduct (n : Nat) (left right : Nat → Nat → Q')
    (row column : Nat) : Q' :=
  listQSum
    (fun k => left row k * right k column)
    (List.range n)

def finiteIdentityMatrix (row column : Nat) : Q' :=
  if row = column then 1 else 0

/-- Executable two-sided exact inverse check on every in-range entry. -/
def finiteMatrixInverseCheck (n : Nat) (matrix inverse : Nat → Nat → Q') : Bool :=
  (List.range n).all fun row =>
    (List.range n).all fun column =>
      decide
        (finiteMatrixProduct n matrix inverse row column ≈
          finiteIdentityMatrix row column) &&
      decide
        (finiteMatrixProduct n inverse matrix row column ≈
          finiteIdentityMatrix row column)

theorem finiteMatrixInverseCheck_entries
    {n : Nat} {matrix inverse : Nat → Nat → Q'}
    (hcheck : finiteMatrixInverseCheck n matrix inverse = true)
    {row column : Nat} (hrow : row < n) (hcolumn : column < n) :
    finiteMatrixProduct n matrix inverse row column ≈
        finiteIdentityMatrix row column ∧
      finiteMatrixProduct n inverse matrix row column ≈
        finiteIdentityMatrix row column := by
  have hrowCheck :=
    List.all_eq_true.mp hcheck row (List.mem_range.mpr hrow)
  have hentry :=
    List.all_eq_true.mp hrowCheck column (List.mem_range.mpr hcolumn)
  exact ⟨of_decide_eq_true ((Bool.and_eq_true _ _).mp hentry).1,
    of_decide_eq_true ((Bool.and_eq_true _ _).mp hentry).2⟩

/-- The inverse check specialized to the supplied finite free-history curl
precision.  A singular ambient gauge carrier simply cannot pass this check. -/
def freeHistoryCovarianceInverseCheck
    (timeBonds edgeCount faceCount : Nat) (curl : Nat → Nat → Q')
    (covariance : Nat → Nat → Q') : Bool :=
  finiteMatrixInverseCheck
    (historyCoordinateCount timeBonds edgeCount)
    (freeHistoryCurlPrecision timeBonds edgeCount faceCount curl)
    covariance

/-- A checked rational inverse of the actual history precision, together with
a checked positive LDL factorization of that inverse, produces the explicit
Heron factor error bound consumed by the finite Gaussian covariance theorem. -/
theorem freeHistoryCovariance_heronFactor
    {timeBonds edgeCount faceCount stage left right : Nat}
    {curl covariance lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hinverse : freeHistoryCovarianceInverseCheck
      timeBonds edgeCount faceCount curl covariance = true)
    (hldl : finiteLDLCheck
      (historyCoordinateCount timeBonds edgeCount)
      covariance lower diagonal = true)
    (hpositive : finiteLDLPositiveDiagonalCheck
      (historyCoordinateCount timeBonds edgeCount) diagonal = true)
    (hleft : left < historyCoordinateCount timeBonds edgeCount)
    (hright : right < historyCoordinateCount timeBonds edgeCount) :
    (finiteMatrixProduct
        (historyCoordinateCount timeBonds edgeCount)
        (freeHistoryCurlPrecision timeBonds edgeCount faceCount curl)
        covariance left right ≈ finiteIdentityMatrix left right) ∧
      Q'.abs
          (factorCovariance
              (historyCoordinateCount timeBonds edgeCount)
              (heronLDLTransform lower diagonal stage) left right +
            -covariance left right) ≤
        ldlFactorResidualEnvelope
          (historyCoordinateCount timeBonds edgeCount)
          lower diagonal stage left right := by
  constructor
  · exact (finiteMatrixInverseCheck_entries hinverse hleft hright).1
  · exact factorCovariance_heronLDLTransform_error
      hldl hpositive hleft hright

end YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision.finiteCurlPrecision_symm
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision.freeHistoryPrecision_index
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision.freeHistoryPrecision_sameTime
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision.freeHistoryPrecision_adjacentTime
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision.freeHistoryPrecision_separatedTime
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision.freeHistoryCurlPrecision_symm
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision.finiteMatrixInverseCheck_entries
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision.freeHistoryCovariance_heronFactor
