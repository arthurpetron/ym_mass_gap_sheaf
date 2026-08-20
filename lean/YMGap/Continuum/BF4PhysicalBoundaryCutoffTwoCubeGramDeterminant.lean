/-
# Strict cutoff-two vacuum/cube physical Gram minor

This module assembles the exact vacuum diagonal, both symmetric vacuum/cube
entries, and the exact cube diagonal.  Their genuine physical two-by-two
Gram determinant is strictly positive.  Thus this finite physical sector is
not rank one.

This remains a finite cutoff-two, half-extent-zero result.  A positive
two-state Gram minor is not by itself an invariant spectral block, a
cutoff-uniform gap, or a continuum Yang--Mills mass gap.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramCross
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDeterminant

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramCross
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonal
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem q_one_mul_product_sub (c interface : Q') :
    (1 * (c * interface)) + -c ≈
      c * (interface + -(1 : Q')) := by
  have hneg : c * (-(1 : Q')) ≈ -c := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_neg_eqv c 1)
      (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv c))
  refine Q'.eqv_trans _ (c * interface + -c) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv (c * interface)) (Q'.eqv_refl _)
  refine Q'.eqv_trans _ (c * interface + c * (-(1 : Q'))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_symm hneg)
  exact Q'.eqv_symm (Q'.mul_add_eqv c interface (-(1 : Q')))

theorem centralPhysicalReflectedKernel_cutoffTwo_vacuum_diagonal_eqv_one :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling zeroEdgeLabelling ≈ 1 := by
  have hvacuum : zeroEdgeLabelling ∈ cutoffTwoVacuumColumnCarrier := by
    unfold cutoffTwoVacuumColumnCarrier
    exact zeroEdgeLabelling_mem_centralPositiveHalfStates
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
  refine Q'.eqv_trans _
    (centralBoundaryWeight cutoffTwoHalfCoupling 2 0 zeroEdgeLabelling *
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling zeroEdgeLabelling) _
    (centralPhysicalReflectedKernel_cutoffTwo_vacuum_row_eqv
      zeroEdgeLabelling hvacuum) ?_
  refine Q'.eqv_trans _ ((1 : Q') * 1) _
    (q_mul_congr centralBoundaryWeight_cutoffTwo_vacuum_eqv_one
      (centralHalfAmplitude_vacuum_eqv_one
        cutoffTwoHalfCoupling 2 0)) ?_
  exact Q'.one_mul_eqv 1

theorem centralPhysicalReflectedKernel_cutoffTwo_cube_vacuum_eqv :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        centralLowerCubeState zeroEdgeLabelling ≈
      cutoffTwoCubeLowerFaceScalar := by
  have hcube : centralLowerCubeState ∈ centralHalfStates 2 0 :=
    centralLowerCubeState_mem_centralHalfStates (by decide)
  have hvacuum : zeroEdgeLabelling ∈ centralHalfStates 2 0 :=
    zeroEdgeLabelling_mem_centralHalfStates 2 0
  exact Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_symm cutoffTwoHalfCoupling
      hcube hvacuum)
    centralPhysicalReflectedKernel_cutoffTwo_vacuum_cube_eqv

def cutoffTwoVacuumCubePhysicalGramDeterminant : Q' :=
  centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      zeroEdgeLabelling zeroEdgeLabelling *
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      centralLowerCubeState centralLowerCubeState +
  -(centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      zeroEdgeLabelling centralLowerCubeState *
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      centralLowerCubeState zeroEdgeLabelling)

def cutoffTwoVacuumCubeExpectedGramDeterminant : Q' :=
  cutoffTwoCubeGramScalar *
    (cutoffTwoCubeExpectedInterfaceSum + -(1 : Q'))

theorem cutoffTwoVacuumCubePhysicalGramDeterminant_eqv :
    cutoffTwoVacuumCubePhysicalGramDeterminant ≈
      cutoffTwoVacuumCubeExpectedGramDeterminant := by
  unfold cutoffTwoVacuumCubePhysicalGramDeterminant
  refine Q'.eqv_trans _
    ((1 : Q') * cutoffTwoCubeExpectedPhysicalGramDiagonal +
      -(cutoffTwoCubeLowerFaceScalar *
        cutoffTwoCubeLowerFaceScalar)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (q_mul_congr
        centralPhysicalReflectedKernel_cutoffTwo_vacuum_diagonal_eqv_one
        centralPhysicalReflectedKernel_cutoffTwo_cube_diagonal_eqv)
      (Q'.neg_eqv_congr _ _
        (q_mul_congr
          centralPhysicalReflectedKernel_cutoffTwo_vacuum_cube_eqv
          centralPhysicalReflectedKernel_cutoffTwo_cube_vacuum_eqv))
  unfold cutoffTwoCubeExpectedPhysicalGramDiagonal
    cutoffTwoCubeGramScalar cutoffTwoVacuumCubeExpectedGramDeterminant
  exact q_one_mul_product_sub
    (cutoffTwoCubeLowerFaceScalar * cutoffTwoCubeLowerFaceScalar)
    cutoffTwoCubeExpectedInterfaceSum

theorem cutoffTwoVacuumCubeExpectedGramDeterminant_pos :
    (0 : Q') < cutoffTwoVacuumCubeExpectedGramDeterminant := by
  unfold cutoffTwoVacuumCubeExpectedGramDeterminant
  apply Q'.mul_pos
  · unfold cutoffTwoCubeGramScalar cutoffTwoCubeLowerFaceScalar
    decide
  · unfold cutoffTwoCubeExpectedInterfaceSum
    decide

theorem cutoffTwoVacuumCubePhysicalGramDeterminant_pos :
    (0 : Q') < cutoffTwoVacuumCubePhysicalGramDeterminant := by
  exact Q'.pos_of_lt_of_le
    cutoffTwoVacuumCubeExpectedGramDeterminant_pos
    (Q'.ge_of_eqv cutoffTwoVacuumCubePhysicalGramDeterminant_eqv)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDeterminant

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDeterminant.centralPhysicalReflectedKernel_cutoffTwo_vacuum_diagonal_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDeterminant.centralPhysicalReflectedKernel_cutoffTwo_cube_vacuum_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDeterminant.cutoffTwoVacuumCubePhysicalGramDeterminant_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDeterminant.cutoffTwoVacuumCubePhysicalGramDeterminant_pos
