/-
# Convergence of the scheduled squared-rate Euler exponents

The finite Euler corridor for the normalized moving-cube rate has exponents

    U_j(t) = (1-q_j^2) floor(t/a_j),
    L_j(t) = ((1-q_j^2)/q_j^2) floor(t/a_j).

This module proves that both converge to the same constructive-real exponent
from the existing causal inputs:

* summable rational variation of the exact physical gap
  `g_j = (1-q_j)/a_j`, selecting a constructive-real limit `M`;
* the completed family's two-sided physical rate band, which forces
  `q_j -> 1`; and
* the canonical floor-sampling theorem
  `a_j floor(t/a_j) -> t`.

The common limit is the literal constructive-real product `M * 2 * t`.  The
odds correction is discharged by proving `1/q_j^2 -> 1` with an explicit
eventual positive floor.  No convergence of the exponential values or of the
scheduled powers is claimed here; those are the next squeeze step.  No
variation input, adaptive producer, raw moment, normalization control,
projective measure, OS reconstruction, continuum Yang--Mills theory, or Clay
conclusion is inhabited.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Constructive.TrigAddCReal
import YMGap.Continuum.ArtanhMonotone
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor
import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.SummableRationalStepVariation
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorPhysicalRateBand
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.RationalEulerPowerSandwich
open YMGap.Continuum.SummableRationalStepVariation

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Rational factorization identities -/

/-- Difference of squares in the rational setoid. -/
theorem one_sub_square_eqv (q : Q') :
    ((1 : Q') + -(q * q)) ≈
      (((1 : Q') + -q) * ((1 : Q') + q)) := by
  have hdistribute :
      (((1 : Q') + -q) * ((1 : Q') + q)) ≈
        ((1 : Q') * ((1 : Q') + q) +
          (-q) * ((1 : Q') + q)) :=
    Q'.add_mul_eqv 1 (-q) (1 + q)
  have hone :
      ((1 : Q') * ((1 : Q') + q) +
          (-q) * ((1 : Q') + q)) ≈
        (((1 : Q') + q) + ((-q) * 1 + (-q) * q)) :=
    Q'.eqv_trans _
      (((1 : Q') + q) + (-q) * ((1 : Q') + q)) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv (1 + q)))
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_add_eqv (-q) 1 q))
  have hsimplify :
      (((1 : Q') + q) + ((-q) * 1 + (-q) * q)) ≈
        (((1 : Q') + q) + (-q + -(q * q))) := by
    apply Q'.add_eqv_congr_left
    exact Q'.eqv_trans _
      ((-q) + (-q) * q) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv (-q)))
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_mul_eqv q q))
  have hcancel :
      (((1 : Q') + q) + (-q + -(q * q))) ≈
        ((1 : Q') + -(q * q)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv 1 q (-q + -(q * q))) ?_
    refine Q'.eqv_trans _
      ((1 : Q') + ((q + -q) + -(q * q))) _
      (Q'.add_eqv_congr_left 1 _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv q (-q) (-(q * q))))) ?_
    refine Q'.eqv_trans _
      ((1 : Q') + (0 + -(q * q))) _
      (Q'.add_eqv_congr_left 1 _ _
        (Q'.add_eqv_congr_right (q + -q) 0 (-(q * q))
          (Q'.add_neg_self_eqv q))) ?_
    exact Q'.add_eqv_congr_left 1 _ _
      (Q'.eqv_of_eq (Q'.zero_add' (-(q * q))))
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _ hdistribute
      (Q'.eqv_trans _ _ _ hone
        (Q'.eqv_trans _ _ _ hsimplify hcancel)))

/-- The exact physical gap cancels its positive spacing back to the lattice
margin. -/
theorem physicalGap_mul_spacing_eqv_latticeMargin
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    family.physicalGap scale * family.transferSpacing.spacing scale ≈
      family.latticeMargin scale := by
  unfold DynamicVacuumSectorCompletedFamily.physicalGap
  exact Q'.divPos_mul_eqv _ _ _

/-- The upper Euler exponent factors into physical gap, `1+q_j`, and sampled
physical distance. -/
theorem scheduledSquaredRateUpperExponent_factor_eqv
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) :
    scheduledSquaredRateUpperExponent family scale time ≈
      ((family.physicalGap scale *
          ((1 : Q') + (family.completedGap scale).rate)) *
        (family.transferSpacing.spacing scale *
          Q'.ofNat
            (centralPhysicalDynamicRCLatticeSteps family scale time))) := by
  let q := (family.completedGap scale).rate
  let a := family.transferSpacing.spacing scale
  let g := family.physicalGap scale
  let n := Q'.ofNat
    (centralPhysicalDynamicRCLatticeSteps family scale time)
  have hgap : g * a ≈ (1 : Q') + -q := by
    exact physicalGap_mul_spacing_eqv_latticeMargin family scale
  have hfactor : ((1 : Q') + -(q * q)) ≈
      (((1 : Q') + -q) * ((1 : Q') + q)) :=
    one_sub_square_eqv q
  unfold scheduledSquaredRateUpperExponent completedSquaredRate
  change (((1 : Q') + -(q * q)) * n) ≈ (g * (1 + q)) * (a * n)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ n hfactor) ?_
  refine Q'.eqv_trans _
    (((g * a) * (1 + q)) * n) _
    (Q'.mul_eqv_congr_right _ _ n
      (Q'.mul_eqv_congr_right _ _ (1 + q) (Q'.eqv_symm hgap))) ?_
  refine Q'.eqv_trans _
    ((g * (a * (1 + q))) * n) _
    (Q'.mul_eqv_congr_right _ _ n (Q'.mul_assoc_eqv g a (1 + q))) ?_
  refine Q'.eqv_trans _
    ((g * ((1 + q) * a)) * n) _
    (Q'.mul_eqv_congr_right _ _ n
      (Q'.mul_eqv_congr_left g _ _ (Q'.mul_comm_eqv a (1 + q)))) ?_
  refine Q'.eqv_trans _
    (((g * (1 + q)) * a) * n) _
    (Q'.mul_eqv_congr_right _ _ n
      (Q'.eqv_symm (Q'.mul_assoc_eqv g (1 + q) a))) ?_
  exact Q'.mul_assoc_eqv (g * (1 + q)) a n

/-! ## 2. Rate and reciprocal convergence -/

/-- The physical rate band forces the actual completed rate to converge to
one. -/
theorem completedRate_converges_one
    (family : DynamicVacuumSectorCompletedFamily 0)
    (band : DynamicVacuumSectorPhysicalRateBand family) :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ' (family.completedGap scale).rate)
      CReal.cone := by
  intro epsilon hepsilon
  refine ⟨band.marginModulus epsilon, fun scale hscale => ?_⟩
  refine ⟨0, fun approximation _ => ?_⟩
  change
    (family.completedGap scale).rate <= (1 : Q') + epsilon /\
    (1 : Q') <= (family.completedGap scale).rate + epsilon
  have hrateOne : (family.completedGap scale).rate <= (1 : Q') :=
    Q'.le_of_lt (family.completedGap scale).rate_lt_one
  exact
    ⟨Q'.le_trans' _ _ _ hrateOne
        (Q'.add_le_self_of_nonneg 1 epsilon (Q'.le_of_lt hepsilon)),
      Q'.le_trans' _ _ _
        (Q'.le_add_of_sub_le
          (one_sub_epsilon_le_rate band epsilon hepsilon scale hscale))
        (Q'.le_of_eqv
          (Q'.add_comm_eqv epsilon (family.completedGap scale).rate))⟩

/-- Consequently `1+q_j` converges to the constructive-real value `2`. -/
theorem one_add_completedRate_converges_two
    (family : DynamicVacuumSectorCompletedFamily 0)
    (band : DynamicVacuumSectorPhysicalRateBand family) :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ'
        ((1 : Q') + (family.completedGap scale).rate))
      (CReal.add CReal.cone CReal.cone) := by
  simpa only [CReal.ofQ'_add] using
    CReal.convergesTo_add (CReal.convergesTo_const CReal.cone)
      (completedRate_converges_one family band)

/-- The squared completed rate also converges to one. -/
theorem completedSquaredRate_converges_one
    (family : DynamicVacuumSectorCompletedFamily 0)
    (band : DynamicVacuumSectorPhysicalRateBand family) :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ' (completedSquaredRate family scale))
      CReal.cone := by
  have hmul :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (completedRate_converges_one family band)
      (completedRate_converges_one family band)
  have hterms : forall scale,
      CReal.Equiv
        (CReal.mul
          (CReal.ofQ' (family.completedGap scale).rate)
          (CReal.ofQ' (family.completedGap scale).rate))
        (CReal.ofQ' (completedSquaredRate family scale)) := by
    intro scale
    exact CReal.Equiv.symm
      (CRealAlg.ofQ'_mul _ _)
  have hconverted :=
    YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq hterms hmul
  exact CReal.convergesTo_limit_congr hconverted
    (CRealAlg.cmul_cone CReal.cone)

/-- The positive reciprocal of the squared rate. -/
def completedSquaredRateReciprocal
    (family : DynamicVacuumSectorCompletedFamily 0)
    (rate_pos : forall scale,
      (0 : Q') < (family.completedGap scale).rate)
    (scale : Nat) : Q' :=
  Q'.recipPos (completedSquaredRate family scale)
    (completedSquaredRate_pos family rate_pos scale)

/-- Since `q_j^2 -> 1` and the rate is eventually bounded below by `1/2`,
the exact rational reciprocal `1/q_j^2` converges constructively to one. -/
theorem completedSquaredRateReciprocal_converges_one
    (family : DynamicVacuumSectorCompletedFamily 0)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (rate_pos : forall scale,
      (0 : Q') < (family.completedGap scale).rate) :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ'
        (completedSquaredRateReciprocal family rate_pos scale))
      CReal.cone := by
  intro epsilon hepsilon
  let baseFloor : Q' := (1 : Q') + -HalfPow.half
  let squareFloor : Q' := baseFloor * baseFloor
  let delta : Q' := squareFloor * epsilon
  have hbaseFloorPos : (0 : Q') < baseFloor := by
    unfold baseFloor
    decide
  have hsquareFloorPos : (0 : Q') < squareFloor :=
    Q'.mul_pos hbaseFloorPos hbaseFloorPos
  have hdeltaPos : (0 : Q') < delta :=
    Q'.mul_pos hsquareFloorPos hepsilon
  obtain ⟨Nclose, hclose⟩ :=
    completedSquaredRate_converges_one family band delta hdeltaPos
  let Nfloor := band.marginModulus HalfPow.half
  refine ⟨max Nclose Nfloor, fun scale hscale => ?_⟩
  have hscaleClose : Nclose <= scale :=
    Nat.le_trans (Nat.le_max_left _ _) hscale
  have hscaleFloor : Nfloor <= scale :=
    Nat.le_trans (Nat.le_max_right _ _) hscale
  obtain ⟨Pclose, hPclose⟩ := hclose scale hscaleClose
  obtain ⟨hrUpper, hrLower⟩ := hPclose Pclose (Nat.le_refl _)
  let q := (family.completedGap scale).rate
  let r := completedSquaredRate family scale
  have hqFloor : baseFloor <= q := by
    exact one_sub_epsilon_le_rate band HalfPow.half
      (by decide) scale hscaleFloor
  have hrFloor : squareFloor <= r := by
    change squareFloor <= q * q
    unfold squareFloor
    exact Q'.mul_le_mul_of_nonneg hqFloor hqFloor
      (family.completedGap scale).rate_nonnegative
      (Q'.le_of_lt hbaseFloorPos)
  have hrPos : (0 : Q') < r :=
    completedSquaredRate_pos family rate_pos scale
  have hrOne : r <= (1 : Q') :=
    completedSquaredRate_le_one family scale
  change r <= (1 : Q') + delta at hrUpper
  change (1 : Q') <= r + delta at hrLower
  refine ⟨0, fun approximation _ => ?_⟩
  change
    completedSquaredRateReciprocal family rate_pos scale <=
        (1 : Q') + epsilon /\
      (1 : Q') <=
        completedSquaredRateReciprocal family rate_pos scale + epsilon
  have hdeltaLe : delta <= epsilon * r := by
    have hscaled : squareFloor * epsilon <= r * epsilon :=
      Q'.mul_le_mul_of_nonneg_right squareFloor r epsilon hrFloor
        (Q'.le_of_lt hepsilon)
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_comm_eqv r epsilon))
  have hOneLeScaled : (1 : Q') <= ((1 : Q') + epsilon) * r := by
    refine Q'.le_trans' _ _ _ hrLower ?_
    have hadd : r + delta <= r + epsilon * r :=
      Q'.add_le_add_left r delta (epsilon * r) hdeltaLe
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.eqv_trans _ _ _
            (Q'.add_mul_eqv 1 epsilon r)
            (Q'.add_eqv_congr_right (1 * r) r (epsilon * r)
              (Q'.one_mul_eqv r)))))
  have hdivUpper :
      Q'.divPos 1 r hrPos <= (1 : Q') + epsilon :=
    Q'.divPos_le_of_le_mul 1 r hrPos hOneLeScaled
  have hrecipDiv :
      completedSquaredRateReciprocal family rate_pos scale ≈
        Q'.divPos 1 r hrPos := by
    unfold completedSquaredRateReciprocal Q'.divPos
    exact Q'.eqv_symm
      (Q'.one_mul_eqv (Q'.recipPos r hrPos))
  have hupper :
      completedSquaredRateReciprocal family rate_pos scale <=
        (1 : Q') + epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hrecipDiv) hdivUpper
  have hrecipOne :
      (1 : Q') <= completedSquaredRateReciprocal family rate_pos scale := by
    have hanti := ArtanhMonotone.recipPos_antitone
      r 1 hrPos (by decide) hrOne
    have honeRecip : (1 : Q') <= Q'.recipPos 1 (by decide) :=
      Q'.ge_of_eqv (by decide)
    exact Q'.le_trans' _ _ _ honeRecip hanti
  exact
    ⟨hupper,
      Q'.le_trans' _ _ _ hrecipOne
        (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩

/-! ## 3. Upper and lower exponent limits -/

/-- The common physical exponent selected by the gap-variation limit. -/
def scheduledSquaredRatePhysicalExponentLimit
    {family : DynamicVacuumSectorCompletedFamily 0}
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (time : Nat) : CReal :=
  CReal.mul
    (CReal.mul gapVariation.limit (CReal.add CReal.cone CReal.cone))
    (CReal.ofQ' (Q'.ofNat time))

/-- The upper Euler exponent converges to `M * 2 * t`. -/
theorem scheduledSquaredRateUpperExponent_converges
    (family : DynamicVacuumSectorCompletedFamily 0)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (time : Nat) :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ'
        (scheduledSquaredRateUpperExponent family scale time))
      (scheduledSquaredRatePhysicalExponentLimit gapVariation time) := by
  have hfirst :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      gapVariation.converges
      (one_add_completedRate_converges_two family band)
  have htriple :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      hfirst (centralPhysicalDynamicRCSampledDistance_converges family time)
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq _ htriple
  intro scale
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_symm
      (scheduledSquaredRateUpperExponent_factor_eqv family scale time))

/-- The lower Euler exponent is the upper exponent multiplied by the exact
reciprocal squared rate. -/
theorem scheduledSquaredRateLowerExponent_factor_eqv
    (family : DynamicVacuumSectorCompletedFamily 0)
    (rate_pos : forall scale,
      (0 : Q') < (family.completedGap scale).rate)
    (scale time : Nat) :
    scheduledSquaredRateLowerExponent family rate_pos scale time ≈
      scheduledSquaredRateUpperExponent family scale time *
        completedSquaredRateReciprocal family rate_pos scale := by
  let r := completedSquaredRate family scale
  let d : Q' := (1 : Q') + -r
  let n := Q'.ofNat
    (centralPhysicalDynamicRCLatticeSteps family scale time)
  have hrPos : (0 : Q') < r :=
    completedSquaredRate_pos family rate_pos scale
  have hd1 : d < (1 : Q') := one_sub_lt_one_of_pos hrPos
  have hmargin : eulerMargin d ≈ r :=
    eulerMargin_one_sub_eqv r
  have hrecip :
      Q'.recipPos (eulerMargin d) (eulerMargin_pos hd1) ≈
        Q'.recipPos r hrPos :=
    Q'.recipPos_eqv_congr _ _ _ _ hmargin
  unfold scheduledSquaredRateLowerExponent scheduledSquaredRateUpperExponent
    eulerOdds completedSquaredRateReciprocal
  change
    ((d * Q'.recipPos (eulerMargin d) (eulerMargin_pos hd1)) * n) ≈
      (d * n) * Q'.recipPos r hrPos
  refine Q'.eqv_trans _
    ((d * Q'.recipPos r hrPos) * n) _
    (Q'.mul_eqv_congr_right _ _ n
      (Q'.mul_eqv_congr_left d _ _ hrecip)) ?_
  refine Q'.eqv_trans _
    (d * (Q'.recipPos r hrPos * n)) _
    (Q'.mul_assoc_eqv d (Q'.recipPos r hrPos) n) ?_
  refine Q'.eqv_trans _
    (d * (n * Q'.recipPos r hrPos)) _
    (Q'.mul_eqv_congr_left d _ _
      (Q'.mul_comm_eqv (Q'.recipPos r hrPos) n)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv d n (Q'.recipPos r hrPos))

/-- The odds-corrected lower Euler exponent converges to the same `M * 2 * t`
as the upper exponent. -/
theorem scheduledSquaredRateLowerExponent_converges
    (family : DynamicVacuumSectorCompletedFamily 0)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (rate_pos : forall scale,
      (0 : Q') < (family.completedGap scale).rate)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (time : Nat) :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ'
        (scheduledSquaredRateLowerExponent family rate_pos scale time))
      (scheduledSquaredRatePhysicalExponentLimit gapVariation time) := by
  have hmul :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (scheduledSquaredRateUpperExponent_converges
        family band gapVariation time)
      (completedSquaredRateReciprocal_converges_one family band rate_pos)
  have hlimit := CReal.convergesTo_limit_congr hmul
    (CRealAlg.cmul_cone
      (scheduledSquaredRatePhysicalExponentLimit gapVariation time))
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq _ hlimit
  intro scale
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_symm
      (scheduledSquaredRateLowerExponent_factor_eqv
        family rate_pos scale time))

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler.one_sub_square_eqv
#print axioms YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler.completedRate_converges_one
#print axioms YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler.completedSquaredRateReciprocal_converges_one
#print axioms YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler.scheduledSquaredRateUpperExponent_converges
#print axioms YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler.scheduledSquaredRateLowerExponent_converges
