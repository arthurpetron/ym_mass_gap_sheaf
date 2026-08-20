/-
M2p -- a computable exact ceiling for every finite prefix of the full-range
physical logarithmic rate.

The prefix input in `FullLogRateCeilingGlue` is finite, but asking callers to
provide it still hides a proof obligation.  Here every index receives an
explicit rational upper bound:

    (k log 2 - log m) / a
      <= (k U₂ + (9/4) |y(m)|) / a,

where `U₂ = (9/4)|y(2)|`, `m` is the computed binary mantissa, and `a > 0` is
the physical spacing.  All quantities on the right are computable `Q'` data.
Taking a recursively computed located maximum over `j < start` therefore
constructs the entire prefix certificate with no analytic hypothesis.
-/

import YMGap.Continuum.FullLogRateCeilingGlue
import YMGap.Continuum.EffMassConvergence

namespace YMGap.Continuum.FinitePrefixFullLogRateCeiling

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogComparison

/-! ## 1. Explicit approximation ceilings for the two logarithmic pieces -/

/-- A rational ceiling for every approximation of the constructive `log 2`. -/
def log2ApproxCeiling : Q' :=
  EffMassConvergence.c94 * Q'.abs (yOf (2 : Q') (by decide))

theorem log2_approx_le_ceiling (n : Nat) :
    log2.approx n <= log2ApproxCeiling := by
  exact Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    (EffMassConvergence.logRat_approx_abs_le
      (2 : Q') (by decide) yOf_two_window n)

/-- The corresponding computable upper bound for `k * log 2`. -/
def kLog2ApproxCeiling : Nat -> Q'
  | 0 => 0
  | k + 1 => log2ApproxCeiling + kLog2ApproxCeiling k

theorem kLog2_approx_le_ceiling (k n : Nat) :
    (kLog2 k).approx n <= kLog2ApproxCeiling k := by
  induction k with
  | zero => exact Q'.le_refl' 0
  | succ k ih =>
      change log2.approx n + (kLog2 k).approx n <=
        log2ApproxCeiling + kLog2ApproxCeiling k
      exact Q'.add_le_add (log2_approx_le_ceiling n) ih

/-- The explicit rational ceiling for the negative mantissa logarithm. -/
def mantissaLogApproxCeiling (P : PhysicalSeparator) (j : Nat) : Q' :=
  EffMassConvergence.c94 *
    Q'.abs (yOf (reducedMantissa P j) (reducedMantissaPlusOne_pos P j))

theorem neg_mantissa_log_approx_le_ceiling
    (P : PhysicalSeparator) (j n : Nat) :
    -((logRat (reducedMantissa P j) (reducedMantissaPlusOne_pos P j)
      (reducedMantissa_window P j)).approx n) <=
      mantissaLogApproxCeiling P j := by
  let x := (logRat (reducedMantissa P j) (reducedMantissaPlusOne_pos P j)
    (reducedMantissa_window P j)).approx n
  have hself : -x <= Q'.abs (-x) := Q'.le_abs_self (-x)
  have hneg : Q'.abs (-x) <= Q'.abs x :=
    Q'.le_of_eqv (Q'.abs_neg' x)
  have hlog : Q'.abs x <=
      EffMassConvergence.c94 *
        Q'.abs (yOf (reducedMantissa P j)
          (reducedMantissaPlusOne_pos P j)) :=
    EffMassConvergence.logRat_approx_abs_le
      (reducedMantissa P j) (reducedMantissaPlusOne_pos P j)
      (reducedMantissa_window P j) n
  exact Q'.le_trans' _ _ _ hself (Q'.le_trans' _ _ _ hneg hlog)

/-! ## 2. Pointwise full-mass and physical-rate ceilings -/

/-- A rational ceiling for every approximation of the full range-reduced mass
at index `j`. -/
def fullLogApproxCeiling (P : PhysicalSeparator) (j : Nat) : Q' :=
  kLog2ApproxCeiling (separatorBinExp P j).k +
    mantissaLogApproxCeiling P j

theorem fullLogMass_approx_le_ceiling
    (P : PhysicalSeparator) (j n : Nat) :
    (fullLogMass P j).approx n <= fullLogApproxCeiling P j := by
  change
    (kLog2 (separatorBinExp P j).k).approx n +
        -((logRat (reducedMantissa P j) (reducedMantissaPlusOne_pos P j)
          (reducedMantissa_window P j)).approx n) <=
      kLog2ApproxCeiling (separatorBinExp P j).k +
        mantissaLogApproxCeiling P j
  exact Q'.add_le_add
    (kLog2_approx_le_ceiling (separatorBinExp P j).k n)
    (neg_mantissa_log_approx_le_ceiling P j n)

/-- An explicit rational ceiling for the dimensionful full logarithmic rate at
one index. -/
def pointRateCeiling (P : PhysicalSeparator) (A : PhysicalSpacing)
    (j : Nat) : Q' :=
  fullLogApproxCeiling P j * reciprocalSpacing A j

theorem fullMassRate_approx_le_pointRateCeiling
    (P : PhysicalSeparator) (A : PhysicalSpacing) (j n : Nat) :
    (fullMassRate P A j).approx n <= pointRateCeiling P A j := by
  change
    (fullLogMass P j).approx n * reciprocalSpacing A j <=
      fullLogApproxCeiling P j * reciprocalSpacing A j
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (fullLogMass_approx_le_ceiling P j n)
    (Q'.le_of_lt (reciprocalSpacing_pos A j))

/-! ## 3. A computable maximum over a finite prefix -/

/-- Located maximum of `f 0, ..., f (start - 1)`, with neutral base `0`. -/
def prefixMax (f : Nat -> Q') : Nat -> Q'
  | 0 => 0
  | start + 1 => Q'.max' (prefixMax f start) (f start)

theorem le_prefixMax (f : Nat -> Q') (j start : Nat)
    (hj : j < start) : f j <= prefixMax f start := by
  induction start with
  | zero => omega
  | succ start ih =>
      by_cases hlt : j < start
      · exact Q'.le_trans' _ _ _ (ih hlt)
          (Q'.le_max'_left (prefixMax f start) (f start))
      · have heq : j = start := by omega
        rw [heq]
        exact Q'.le_max'_right (prefixMax f start) (f start)

/-- The full finite-prefix certificate is computed from the separator and
spacing alone. -/
def computedPrefixCeiling {P : PhysicalSeparator}
    (F : FullRangeExactPhysicalLogRateFamily P) (start : Nat) :
    PrefixFullRangeLogRateCeiling F start where
  ceiling := prefixMax (pointRateCeiling P F.physicalSpacing) start
  prefix_bound := fun j hj => by
    refine CReal.leEv_le_ofQ'_of_approx_le (fun n => ?_)
    exact Q'.le_trans' _ _ _
      (fullMassRate_approx_le_pointRateCeiling P F.physicalSpacing j n)
      (le_prefixMax (pointRateCeiling P F.physicalSpacing) j start hj)

@[simp] theorem computedPrefixCeiling_ceiling {P : PhysicalSeparator}
    (F : FullRangeExactPhysicalLogRateFamily P) (start : Nat) :
    (computedPrefixCeiling F start).ceiling =
      prefixMax (pointRateCeiling P F.physicalSpacing) start := rfl

end YMGap.Continuum.FinitePrefixFullLogRateCeiling

#print axioms YMGap.Continuum.FinitePrefixFullLogRateCeiling.log2_approx_le_ceiling
#print axioms YMGap.Continuum.FinitePrefixFullLogRateCeiling.kLog2_approx_le_ceiling
#print axioms YMGap.Continuum.FinitePrefixFullLogRateCeiling.fullLogMass_approx_le_ceiling
#print axioms YMGap.Continuum.FinitePrefixFullLogRateCeiling.fullMassRate_approx_le_pointRateCeiling
#print axioms YMGap.Continuum.FinitePrefixFullLogRateCeiling.le_prefixMax
#print axioms YMGap.Continuum.FinitePrefixFullLogRateCeiling.computedPrefixCeiling
