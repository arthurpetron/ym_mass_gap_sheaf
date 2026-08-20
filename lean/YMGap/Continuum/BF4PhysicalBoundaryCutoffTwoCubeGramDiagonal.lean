/-
# Exact cutoff-two physical cube Gram diagonal

The genuine reflected physical kernel on the lower-cube state is reduced to
the certified 24-coordinate interface factor graph and evaluated exactly.
The external exact-arithmetic scout proposed the final rational; Lean checks
the production-to-factor bridge, the sparse contraction, and the final
rational identity.

This is a finite cutoff-two, half-extent-zero matrix entry.  It is not a
cutoff-uniform or continuum mass-gap theorem.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonalStage

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonal

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonalStage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoCubeExpectedPhysicalGramDiagonal : Q' :=
  cutoffTwoCubeGramScalar * cutoffTwoCubeExpectedInterfaceSum

theorem centralPhysicalReflectedKernel_cutoffTwo_cube_diagonal_eqv :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        centralLowerCubeState centralLowerCubeState ≈
      cutoffTwoCubeExpectedPhysicalGramDiagonal := by
  unfold cutoffTwoCubeExpectedPhysicalGramDiagonal
  exact stage5

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonal
