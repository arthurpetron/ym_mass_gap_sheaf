/-
# Vacuum correlations of the SAME bounded Wilson observables

The operator expression <U, M_L T_n M_K U> uses the already constructed
vacuum, physical time and bounded time-zero multipliers. Reflection balance
identifies it with the original state pairing. Subtracting the product of
the SAME vacuum expectations gives the existing connected scalar, so its
previously proved decay estimate applies without a new mixing assumption.

Fixed-spacing, small-nome SU(2) only. Neither one-step positivity, canonical
full observable coverage, a continuum Hamiltonian nor physical mass
calibration is supplied by this identification.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroOperator
import YMGap.Continuum.BF4WilsonSpatialUnionVacuumRelaxation
import YMGap.Continuum.BF4WilsonTimeZeroVacuum

namespace YMGap.Continuum.BF4WilsonTimeZeroCorrelations

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnion (pairing time)
open YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm (centeredMoment)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm (completedTime_correlator)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier (completedMultiply)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroOperator (completedInner_multiplier_balance)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap (completedCenteredScalar)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection (center)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumRelaxation (connected_sq_decay connected_embedStage)
open YMGap.Continuum.BF4WilsonTimeZeroVacuum (loopStage loopState completedMultiply_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "M" => completedMultiply hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "C" => center hw0 hw1 hsmall hd hs

def vacuumCorrelation {leftBase rightBase : Nat} (n : Nat)
    (L : SourceLoop leftBase) (leftSpin : Nat) (K : SourceLoop rightBase) (rightSpin : Nat) : RC :=
  B U (M L leftSpin (T n (M K rightSpin U)))

def vacuumConnected {leftBase rightBase : Nat} (n : Nat)
    (L : SourceLoop leftBase) (leftSpin : Nat) (K : SourceLoop rightBase) (rightSpin : Nat) : RC :=
  RCsub (vacuumCorrelation hw0 hw1 hsmall hd hs n L leftSpin K rightSpin)
    (RCmul (B U (M L leftSpin U)) (B U (M K rightSpin U)))

theorem vacuumCorrelation_state {leftBase rightBase : Nat} (n : Nat)
    (L : SourceLoop leftBase) (leftSpin : Nat) (K : SourceLoop rightBase) (rightSpin : Nat) :
    vacuumCorrelation hw0 hw1 hsmall hd hs n L leftSpin K rightSpin =
      B (M L leftSpin U) (T n (M K rightSpin U)) :=
  (completedInner_multiplier_balance hw0 hw1 hsmall hd hs L leftSpin U
    (T n (M K rightSpin U))).symm

/-- Both expectation factors and the time pairing use the same observable-created states. -/
theorem vacuumConnected_state {leftBase rightBase : Nat} (n : Nat)
    (L : SourceLoop leftBase) (leftSpin : Nat) (K : SourceLoop rightBase) (rightSpin : Nat) :
    vacuumConnected hw0 hw1 hsmall hd hs n L leftSpin K rightSpin =
      completedCenteredScalar hw0 hw1 hsmall hd hs n (M L leftSpin U) (M K rightSpin U) := by
  unfold vacuumConnected completedCenteredScalar
  rw [vacuumCorrelation_state,
    completedInner_multiplier_balance hw0 hw1 hsmall hd hs L leftSpin U U]

/-- Operator vacuum matrix elements equal the original dense Wilson time pairing. -/
theorem vacuumCorrelation_original {leftBase rightBase : Nat}
    (hleft : 0 < leftBase) (hright : 0 < rightBase) (n : Nat)
    (L : SourceLoop leftBase) (leftSpin : Nat) (K : SourceLoop rightBase) (rightSpin : Nat) :
    vacuumCorrelation hw0 hw1 hsmall hd hs n L leftSpin K rightSpin =
      Quotient.mk crealSetoid (pairing hw0 hw1 hsmall hd hs (loopStage hleft L leftSpin)
        (time n (loopStage hright K rightSpin))) := by
  rw [vacuumCorrelation_state, completedMultiply_unit hw0 hw1 hsmall hd hs hleft L leftSpin,
    completedMultiply_unit hw0 hw1 hsmall hd hs hright K rightSpin]
  exact completedTime_correlator hw0 hw1 hsmall hd hs n
    (loopStage hleft L leftSpin) (loopStage hright K rightSpin)

/-- No surrogate correlator: the SAME original connected scalar and its existing moduli. -/
theorem vacuumConnected_original {leftBase rightBase : Nat}
    (hleft : 0 < leftBase) (hright : 0 < rightBase) (n : Nat)
    (L : SourceLoop leftBase) (leftSpin : Nat) (K : SourceLoop rightBase) (rightSpin : Nat) :
    vacuumConnected hw0 hw1 hsmall hd hs n L leftSpin K rightSpin =
      Quotient.mk crealSetoid (centeredMoment hw0 hw1 hsmall hd hs n
        (loopStage hleft L leftSpin) (loopStage hright K rightSpin)) := by
  rw [vacuumConnected_state, completedMultiply_unit hw0 hw1 hsmall hd hs hleft L leftSpin,
    completedMultiply_unit hw0 hw1 hsmall hd hs hright K rightSpin]
  exact connected_embedStage hw0 hw1 hsmall hd hs n
    (loopStage hleft L leftSpin) (loopStage hright K rightSpin)

/-- Existing geometric decay now applies to actual observable vacuum matrix elements. -/
theorem vacuumConnected_sq_decay {leftBase rightBase : Nat} (n : Nat)
    (L : SourceLoop leftBase) (leftSpin : Nat) (K : SourceLoop rightBase) (rightSpin : Nat) :
    RCle
      (RCmul (vacuumConnected hw0 hw1 hsmall hd hs n L leftSpin K rightSpin)
        (vacuumConnected hw0 hw1 hsmall hd hs n L leftSpin K rightSpin))
      (RCmul (B (C (M L leftSpin U)) (C (M L leftSpin U)))
        (RCscale ((twoStepRate w hd)^n)
          (B (C (M K rightSpin U)) (C (M K rightSpin U))))) := by
  rw [vacuumConnected_state]
  exact connected_sq_decay hw0 hw1 hsmall hd hs n (M L leftSpin U) (M K rightSpin U)

#print axioms vacuumCorrelation
#print axioms vacuumConnected
#print axioms vacuumCorrelation_state
#print axioms vacuumConnected_state
#print axioms vacuumCorrelation_original
#print axioms vacuumConnected_original
#print axioms vacuumConnected_sq_decay

end YMGap.Continuum.BF4WilsonTimeZeroCorrelations
