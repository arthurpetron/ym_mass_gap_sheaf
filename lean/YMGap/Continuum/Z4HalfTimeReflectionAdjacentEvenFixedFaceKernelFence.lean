/-
# Fixed-face channel fence for the adjacent even kernel

The interface-vacuum fixed-link multiplicity is a positive channel Gram.
It is tempting to treat each nonzero spatial face fixed by the integer
reflection plane as another nonnegative boundary channel.  That is false:
conditioning on a fixed spin inserts its SU(2) fusion matrix between the two
halves, and a fusion matrix need not be positive semidefinite.

The fundamental fixed spin already gives the `2 x 2` exchange matrix on the
states `[0]` and `[1]`.  The coefficient vector `(1,-1)` has quadratic value
`-2`.  Thus the full adjacent-even kernel must resum the fixed-face character
weight before positivity; channelwise positivity cannot be asserted.
-/

import YMGap.Continuum.Z4FusionChannelConvolution
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceKernelFence

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion

local infix:50 " ≈ " => Q'.eqv

/-- Local fixed-link multiplicity after inserting a prescribed word of
spatial-face spins on the reflection plane. -/
def adjacentEvenFixedFaceLinkKernel
    (cutoff : Nat) (fixed left right : List Nat) : Q' :=
  Q'.ofNat
    (fusionPathMultiplicity cutoff
      (left ++ fixed ++ right.reverse))

def fundamentalFixedFaceStates : List (List Nat) := [[0], [1]]

def fundamentalFixedFaceCoefficient (state : List Nat) : Q' :=
  if state = [0] then 1 else -1

def fundamentalFixedFaceQuadratic : Q' :=
  listQSum (fun left => listQSum (fun right =>
    (fundamentalFixedFaceCoefficient left *
      fundamentalFixedFaceCoefficient right) *
      adjacentEvenFixedFaceLinkKernel 2 [1] left right)
    fundamentalFixedFaceStates) fundamentalFixedFaceStates

theorem fundamentalFixedFaceKernel_00 :
    adjacentEvenFixedFaceLinkKernel 2 [1] [0] [0] = 0 := by
  decide

theorem fundamentalFixedFaceKernel_01 :
    adjacentEvenFixedFaceLinkKernel 2 [1] [0] [1] = 1 := by
  decide

theorem fundamentalFixedFaceKernel_10 :
    adjacentEvenFixedFaceLinkKernel 2 [1] [1] [0] = 1 := by
  decide

theorem fundamentalFixedFaceKernel_11 :
    adjacentEvenFixedFaceLinkKernel 2 [1] [1] [1] = 0 := by
  decide

/-- Exact negative quadratic witness for a fixed fundamental interface face. -/
theorem fundamentalFixedFaceQuadratic_eq_neg_two :
    fundamentalFixedFaceQuadratic = -2 := by
  decide

theorem fundamentalFixedFaceKernel_not_positiveSemidefinite :
    ¬ ((0 : Q') ≤ fundamentalFixedFaceQuadratic) := by
  rw [fundamentalFixedFaceQuadratic_eq_neg_two]
  decide

#print axioms fundamentalFixedFaceKernel_00
#print axioms fundamentalFixedFaceKernel_01
#print axioms fundamentalFixedFaceKernel_10
#print axioms fundamentalFixedFaceKernel_11
#print axioms fundamentalFixedFaceQuadratic_eq_neg_two
#print axioms fundamentalFixedFaceKernel_not_positiveSemidefinite

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceKernelFence
