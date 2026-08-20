/-
# Exact cutoff-two vacuum-column posterior denominator

This module exposes the exact positive denominator for the retained cutoff-two
vacuum column and identifies explicit division by it with the project's
canonical target-given-boundary posterior.  Keeping this bridge separate
prevents later finite-statistics proofs from reopening the sparse contraction.

This is a finite `K = 2`, half-extent-zero result at coupling `1/2`; it is not
a cutoff-uniform, spectral-gap, or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosteriorDenominatorBridge

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The genuine retained source-to-vacuum amplitudes divided by their exact
column total. -/
def cutoffTwoVacuumColumnPosterior (source : EdgeLabelling) : Q' :=
  Q'.divPos
    (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
      zeroEdgeLabelling)
    cutoffTwoVacuumColumnDenominator
    cutoffTwoVacuumColumnDenominator_pos

private theorem qeqv_of_le_of_ge_local {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local {a a' b b' : Q'}
    (hb : (0 : Q') < b) (hb' : (0 : Q') < b')
    (ha : a ≈ a') (hden : b ≈ b') :
    Q'.divPos a b hb ≈ Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le a' b' hb'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hden))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hb) ha))
  · apply Q'.le_divPos_of_mul_le a b hb
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hb') b b' hden)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm ha)))

/-- The explicit normalization is the project's canonical physical
target-given-boundary posterior. -/
theorem centralTargetGivenVacuum_cutoffTwo_eqv_explicit
    (source : EdgeLabelling) :
    centralTargetGivenBoundary
        cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 zeroEdgeLabelling
        centralPositiveBoundaryTotalHalfAmplitude_cutoffTwo_vacuum_pos
        source ≈
      cutoffTwoVacuumColumnPosterior source := by
  unfold centralTargetGivenBoundary finiteStateGivenChannel
    cutoffTwoVacuumColumnPosterior
  exact divPos_eqv_congr_local
    centralPositiveBoundaryTotalHalfAmplitude_cutoffTwo_vacuum_pos
    cutoffTwoVacuumColumnDenominator_pos
    (Q'.eqv_refl _)
    centralPositiveBoundaryTotalHalfAmplitude_cutoffTwo_vacuum_eqv

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior.centralPositiveBoundaryTotalHalfAmplitude_cutoffTwo_vacuum_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior.centralTargetGivenVacuum_cutoffTwo_eqv_explicit
