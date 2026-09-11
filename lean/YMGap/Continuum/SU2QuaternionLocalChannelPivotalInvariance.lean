/-
# Storage-polarization obstruction for cutoff-one SU(2) channels

The semantic target/source reshaping in the positive local Haar kernels is
load-bearing.  A tempting shortcut would instead regard every local kernel as
a positive matrix from its stored row indices to its stored column indices,
hoping that the plaquette trace then becomes an ordinary cyclic wiring.

That shortcut already fails at valence two.  For one forward and one reverse
occurrence, the storage-polarized kernel is one half of the four-dimensional
swap matrix.  Its antisymmetric quadratic value is exactly `-1`, so it is not
positive semidefinite.  No orthogonal channel basis change can turn it into a
same-vector positive-channel resolution.

The primitive epsilon/Kronecker identity is retained as the true local
pivotal atom.  This leaf deliberately makes no all-leg channel-invariance or
global cup/cap-straightening claim.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SymbolicFiniteBoolTensor
import YMGap.Continuum.SU2QuaternionBivalentOperatorKernel
import YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector

namespace YMGap.Continuum.SU2QuaternionLocalChannelPivotalInvariance

open YMGap.Constructive
open YMGap.Continuum.SymbolicFiniteBoolTensor
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector
open YMGap.Continuum.SU2QuaternionBivalentOperatorKernel
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The true one-strand pivotal atom -/

/-- Simultaneous epsilon complementation fixes one Kronecker strand. -/
theorem epsilonPair_boolKronecker
    (left right : Bool) :
    epsilonCoordinateSign left *
        (epsilonCoordinateSign right * boolKronecker (!left) (!right)) ≈
      boolKronecker left right := by
  cases left <;> cases right <;> decide

/-! ## 2. Storage-row positivity obstruction -/

/-- The forward/reverse bivalent kernel polarized by stored rows and stored
columns rather than semantic operator target/source coordinates. -/
def forwardReverseStorageKernelScalar
    (storedRows storedColumns : BivalentOperatorIndex) : Q' :=
  (orientedBivalentHaarKernel
    ⟨.forward, storedRows.output, storedColumns.output⟩
    ⟨.reverse, storedRows.input, storedColumns.input⟩).1

/-- In storage coordinates the kernel is one half of the swap matrix. -/
theorem forwardReverseStorageKernelScalar_eq_swap
    (storedRows storedColumns : BivalentOperatorIndex) :
    forwardReverseStorageKernelScalar storedRows storedColumns ≈
      if storedRows.output = storedColumns.input ∧
          storedRows.input = storedColumns.output then
        Q'.invSucc 1
      else 0 := by
  rcases storedRows with ⟨firstRow, secondRow⟩
  rcases storedColumns with ⟨firstColumn, secondColumn⟩
  cases firstRow <;> cases secondRow <;>
    cases firstColumn <;> cases secondColumn <;> decide

/-- Antisymmetric storage-coordinate vector supported on `01` and `10`. -/
def storageSwapNegativeWitness (index : BivalentOperatorIndex) : Q' :=
  if index.output = false ∧ index.input = true then 1
  else if index.output = true ∧ index.input = false then -1
  else 0

/-- Quadratic form of the storage-polarized kernel on the antisymmetric
witness. -/
def forwardReverseStorageQuadraticWitness : Q' :=
  rationalFourBoolSum (fun firstRow secondRow firstColumn secondColumn =>
    storageSwapNegativeWitness ⟨firstRow, secondRow⟩ *
      (forwardReverseStorageKernelScalar
          ⟨firstRow, secondRow⟩ ⟨firstColumn, secondColumn⟩ *
        storageSwapNegativeWitness ⟨firstColumn, secondColumn⟩))

/-- The storage-row/storage-column kernel is not positive semidefinite: its
antisymmetric quadratic value is exactly `-1`. -/
theorem forwardReverseStorageQuadraticWitness_exact :
    forwardReverseStorageQuadraticWitness ≈ -1 := by
  unfold forwardReverseStorageQuadraticWitness rationalFourBoolSum
    rationalBoolSum storageSwapNegativeWitness
    forwardReverseStorageKernelScalar orientedBivalentHaarKernel
    orientedFundamentalSchurDelta
  decide

#print axioms epsilonPair_boolKronecker
#print axioms forwardReverseStorageKernelScalar_eq_swap
#print axioms forwardReverseStorageQuadraticWitness_exact

end YMGap.Continuum.SU2QuaternionLocalChannelPivotalInvariance
