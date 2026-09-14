/-
# The ORIGINAL excited probe survives every discrete time

The proved positive one-step response and the equality of all positive-time
kernels rule out finite-time annihilation of the existing excitation. Every
orbit point remains a nonzero unit-complement vector and is not fixed by any
positive later time. Every even-time autocorrelation is nonzero.

These are same-object discrete-time statements, not a uniform positive lower
bound as time tends to infinity. The orbit still relaxes toward zero by the
proved gap. No assertion of injectivity on the entire completion, full
observable realization, continuous-time generator or continuum YM is made.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTimeKernel
import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse

namespace YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit

set_option autoImplicit false

open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeKernel
open YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeExcitation (state state_ne_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveResponse

def orbit (n : Nat) : UnitComplement := complementTime n state

theorem orbit_zero : (orbit 0).val=state.val := completedTime_zero state.val

theorem orbit_advance (s t : Nat) : completedTime t (orbit s).val=(orbit (s+t)).val :=
  completedTime_comp s t state.val

theorem orbit_orthogonal (n : Nat) : completedInner (orbit n).val completedUnit=RCzero :=
  (orbit n).property

theorem orbit_nonzero (n : Nat) : (orbit n).val ≠ completedZero := by
  cases n with
  | zero => rw [orbit_zero]; exact state_ne_zero
  | succ n =>
    intro h
    exact original_translatedState_ne_zero ((time_succ_zero_iff_one n state.val).mp h)

theorem orbit_not_fixed (n lag : Nat) (hlag : 0<lag) :
    completedTime lag (orbit n).val ≠ (orbit n).val := by
  intro h
  have hz := fixed_center_zero lag hlag (orbit n).val h
  rw [(center_fixed_iff (orbit n).val).mpr (orbit n).property] at hz
  exact orbit_nonzero n hz

theorem even_autocorrelation_nonzero (n : Nat) :
    completedInner state.val (completedTime (n+n) state.val) ≠ RCzero := by
  intro h
  have hn := (BF4ExactSlabThermodynamicCompletedPosdef.completedInner_posdef
    (completedTime n state.val)).mp ((completedTime_moments n n state.val state.val).trans h)
  exact orbit_nonzero n hn

theorem orbit_even_autocorrelation_nonzero (n lag : Nat) :
    completedInner (orbit n).val (completedTime (lag+lag) (orbit n).val) ≠ RCzero := by
  intro h
  have hn := (BF4ExactSlabThermodynamicCompletedPosdef.completedInner_posdef
    (completedTime lag (orbit n).val)).mp ((completedTime_moments lag lag _ _).trans h)
  rw [orbit_advance] at hn
  exact orbit_nonzero (n+lag) hn

end YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit.orbit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit.orbit_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit.orbit_advance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit.orbit_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit.orbit_nonzero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit.orbit_not_fixed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit.even_autocorrelation_nonzero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicProbeOrbit.orbit_even_autocorrelation_nonzero
