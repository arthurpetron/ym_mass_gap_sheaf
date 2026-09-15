/-
# Existing positive-real-time evolution recovers EVERY original lattice time

The first dyadic generator is now the actual geometric T1. Induction
identifies depth-one mesh time n/2 with original completedTime n, including
odd n. The existing positive-dyadic pin transports this equality to the
previous positive-real-time action, independently of its time presentation.
The same semigroup then commutes with every original integer translation.

Time normalization is explicit: these are the PREVIOUS dimensionless
semigroup units, where time one means TWO lattice steps. No spacing or
Hamiltonian calibration is silently introduced. SU(2) nome 1/1024 and
spacing are fixed; full-space time-zero continuity, injectivity/range,
physical Hamiltonian, continuum/QFT, other groups and Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification
import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup

namespace YMGap.Continuum.BF4ExactSlabThermodynamicGeometricTimePins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint embed)
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup (action action_embed)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction (positiveAction)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup (realTimeAction_commutes)
open YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification

/-- Half-integer SEMIGROUP time, not a physical-spacing rescaling. -/
theorem geometric_mesh_value (n : Nat) : Q'.eqv (value ⟨1,n⟩) (HalfPow.half * Q'.ofNat n) := by
  change (n : Int)*2=(1*(n : Int))*2
  rw [Int.one_mul]

/-- Supplied original step count constructs the time and all its existing numerical moduli. -/
def geometricTime (n : Nat) (hn : 0<n) : PositiveTime := dyadicTime ⟨1,n⟩ hn

theorem geometricTime_real (n : Nat) (hn : 0<n) :
    Equiv (geometricTime n hn).real (ofQ' (HalfPow.half * Q'.ofNat n)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => geometric_mesh_value n)

theorem dyadic_geometric (n : Nat) (x : Completion) : action (embed ⟨1,n⟩) x=completedTime n x := by
  change time 1 n x=completedTime n x
  induction n with
  | zero => exact (completedTime_zero x).symm
  | succ n ih =>
      rw [time,generator_one_geometric,ih,completedTime_comp]

theorem positiveAction_geometric (n : Nat) (hn : 0<n) (x : Completion) :
    positiveAction (geometricTime n hn) x=completedTime n x :=
  (positiveAction_dyadic ⟨1,n⟩ hn x).trans (dyadic_geometric n x)

/-- Any existing represented positive time with value n/2 gives the literal old operator. -/
theorem positiveAction_at_geometric (D : PositiveTime) (n : Nat) (hn : 0<n)
    (h : Equiv D.real (ofQ' (HalfPow.half * Q'.ofNat n))) (x : Completion) :
    positiveAction D x=completedTime n x :=
  (positiveAction_time_congr D (geometricTime n hn) (h.trans (geometricTime_real n hn).symm) x).trans
    (positiveAction_geometric n hn x)

theorem realTimeAction_geometric (n : Nat) (hn : 0<n) (x : Completion) :
    realTimeAction (timeValue (geometricTime n hn)) x=completedTime n x := positiveAction_geometric n hn x

/-- The previous positive-real-time semigroup and ALL original integer translations commute. -/
theorem realTimeAction_geometric_commutes (t : PositiveTimeValue) (n : Nat) (x : Completion) :
    realTimeAction t (completedTime n x)=completedTime n (realTimeAction t x) := by
  cases n with
  | zero => rw [completedTime_zero,completedTime_zero]
  | succ n =>
      rw [← realTimeAction_geometric (n+1) (Nat.succ_pos n),
        ← realTimeAction_geometric (n+1) (Nat.succ_pos n)]
      exact realTimeAction_commutes t _ x

end YMGap.Continuum.BF4ExactSlabThermodynamicGeometricTimePins

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricTimePins.geometric_mesh_value
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricTimePins.geometricTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricTimePins.geometricTime_real
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricTimePins.dyadic_geometric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricTimePins.positiveAction_geometric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricTimePins.positiveAction_at_geometric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricTimePins.realTimeAction_geometric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricTimePins.realTimeAction_geometric_commutes
