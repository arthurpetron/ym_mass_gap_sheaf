/-
# Physical-exponential identification of the scheduled squared-rate limit

The finite Euler corridor brackets the literal scheduled rate power between
two rational constructive exponentials.  The preceding exponent compiler
proves that their rational exponents converge to the same physical value
`2 * M * t`.  This module closes the remaining squeeze without postulating a
global exponential on arbitrary `CReal`s.

The physical exponential at this route is the already-constructed complete
limit of the literal scheduled powers.  It is identified constructively by
proving that both rational exponential endpoint streams converge to that same
limit.  Thus the value used in the normalized moving-cube decay theorem and
the value selected by the physical exponent are definitionally connected.

No physical-gap variation, scheduled-power variation, raw moment,
normalization control, adaptive producer, projective measure, OS
reconstruction, continuum Yang--Mills theory, or Clay conclusion is inhabited
here.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler
open YMGap.Continuum.RationalEulerPowerSandwich
open YMGap.Continuum.SummableRationalStepVariation

/-! ## 1. A reusable constructive exponential squeeze -/

/-- If two nonnegative rational exponent streams converge to the same
constructive real and `upper_j <= lower_j`, then their decreasing exponential
images become arbitrarily close in `leRat`.  The fixed unit-scale comparison
supplies the range required by `expNeg_contraction`; the requested tolerance
is handled independently. -/
theorem expNegEndpoints_leRat_close
    {upper lower : Nat -> Q'} {exponentLimit : CReal}
    (upper_nonnegative : forall scale, (0 : Q') <= upper scale)
    (lower_nonnegative : forall scale, (0 : Q') <= lower scale)
    (upper_le_lower : forall scale, upper scale <= lower scale)
    (upper_converges : CReal.ConvergesTo
      (fun scale => CReal.ofQ' (upper scale)) exponentLimit)
    (lower_converges : CReal.ConvergesTo
      (fun scale => CReal.ofQ' (lower scale)) exponentLimit) :
    forall epsilon : Q', (0 : Q') < epsilon ->
      exists start : Nat, forall scale : Nat, start <= scale ->
        CReal.leRat
          (CReal.sub
            (ExpNeg.expNeg (upper scale) (upper_nonnegative scale))
            (ExpNeg.expNeg (lower scale) (lower_nonnegative scale)))
          epsilon := by
  intro epsilon hepsilon
  let q : Q' := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  have hhalf : (0 : Q') < HalfPow.half := by decide
  obtain ⟨Nupper, hNupper⟩ := upper_converges q hq
  obtain ⟨Nlower, hNlower⟩ := lower_converges q hq
  obtain ⟨NupperUnit, hNupperUnit⟩ :=
    upper_converges HalfPow.half hhalf
  obtain ⟨NlowerUnit, hNlowerUnit⟩ :=
    lower_converges HalfPow.half hhalf
  let start := max (max Nupper Nlower) (max NupperUnit NlowerUnit)
  refine ⟨start, fun scale hscale => ?_⟩
  have hsUpper : Nupper <= scale :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_left _ _) hscale)
  have hsLower : Nlower <= scale :=
    Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_left _ _) hscale)
  have hsUpperUnit : NupperUnit <= scale :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) hscale)
  have hsLowerUnit : NlowerUnit <= scale :=
    Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _) hscale)
  obtain ⟨Kupper, hKupper⟩ := hNupper scale hsUpper
  obtain ⟨Klower, hKlower⟩ := hNlower scale hsLower
  let K := max Kupper Klower
  obtain ⟨_, hLimitUpper⟩ :=
    hKupper K (Nat.le_max_left _ _)
  obtain ⟨hLowerLimit, _⟩ :=
    hKlower K (Nat.le_max_right _ _)
  have hlowerUpperEpsilon : lower scale <= upper scale + epsilon := by
    have hchain : lower scale <= (upper scale + q) + q :=
      Q'.le_trans' _ _ _ hLowerLimit
        (Q'.add_le_add_right _ _ q hLimitUpper)
    refine Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (upper scale) q q) ?_
    exact Q'.add_eqv_congr_left (upper scale) (q + q) epsilon
      (ExpNeg.two_halves epsilon)
  have hdiffEpsilon : lower scale - upper scale <= epsilon :=
    Q'.sub_le_of_le_add hlowerUpperEpsilon
  obtain ⟨KupperUnit, hKupperUnit⟩ :=
    hNupperUnit scale hsUpperUnit
  obtain ⟨KlowerUnit, hKlowerUnit⟩ :=
    hNlowerUnit scale hsLowerUnit
  let Kunit := max KupperUnit KlowerUnit
  obtain ⟨_, hLimitUpperUnit⟩ :=
    hKupperUnit Kunit (Nat.le_max_left _ _)
  obtain ⟨hLowerLimitUnit, _⟩ :=
    hKlowerUnit Kunit (Nat.le_max_right _ _)
  have hlowerUpperUnit : lower scale <= upper scale + (1 : Q') := by
    have hchain : lower scale <=
        (upper scale + HalfPow.half) + HalfPow.half :=
      Q'.le_trans' _ _ _ hLowerLimitUnit
        (Q'.add_le_add_right _ _ HalfPow.half hLimitUpperUnit)
    refine Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (upper scale) HalfPow.half HalfPow.half) ?_
    exact Q'.add_eqv_congr_left (upper scale)
      (HalfPow.half + HalfPow.half) 1 ExpNeg.half_add_half_eqv
  have hdiffUnit : lower scale - upper scale <= (1 : Q') :=
    Q'.sub_le_of_le_add hlowerUpperUnit
  exact CReal.leRat_mono
    (CReal.expNeg_contraction (upper_nonnegative scale)
      (upper_le_lower scale) hdiffUnit)
    hdiffEpsilon

/-- A convergent middle sequence and an asymptotically vanishing width between
two `leEv` bounds force both bounds to converge to the middle limit.  This is
the eventual-order analogue of the ordinary squeeze theorem and is stated in
the exact currency produced by `expNeg_contraction`. -/
theorem endpoints_converge_of_leRat_sandwich
    {lower middle upper : Nat -> CReal} {limit : CReal}
    (middle_converges : CReal.ConvergesTo middle limit)
    (lower_le_middle : forall scale,
      CReal.leEv (lower scale) (middle scale))
    (middle_le_upper : forall scale,
      CReal.leEv (middle scale) (upper scale))
    (width_closes : forall epsilon : Q', (0 : Q') < epsilon ->
      exists start : Nat, forall scale : Nat, start <= scale ->
        CReal.leRat (CReal.sub (upper scale) (lower scale)) epsilon) :
    CReal.ConvergesTo upper limit /\
      CReal.ConvergesTo lower limit := by
  constructor
  · intro epsilon hepsilon
    let q : Q' := HalfPow.half * (HalfPow.half * epsilon)
    have hq : (0 : Q') < q :=
      ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)
    obtain ⟨Nmiddle, hNmiddle⟩ := middle_converges q hq
    obtain ⟨Nwidth, hNwidth⟩ := width_closes q hq
    refine ⟨max Nmiddle Nwidth, fun scale hscale => ?_⟩
    have hsMiddle : Nmiddle <= scale :=
      Nat.le_trans (Nat.le_max_left _ _) hscale
    have hsWidth : Nwidth <= scale :=
      Nat.le_trans (Nat.le_max_right _ _) hscale
    obtain ⟨Kmiddle, hKmiddle⟩ := hNmiddle scale hsMiddle
    obtain ⟨Klower, hKlower⟩ := lower_le_middle scale q hq
    obtain ⟨Kupper, hKupper⟩ := middle_le_upper scale q hq
    obtain ⟨Kwidth, hKwidth⟩ := (hNwidth scale hsWidth) q hq
    let K := max (max Kmiddle Klower) (max Kupper Kwidth)
    refine ⟨K, fun k hk => ?_⟩
    have hkMiddle : Kmiddle <= k :=
      Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hk)
    have hkLower : Klower <= k :=
      Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hk)
    have hkUpper : Kupper <= k :=
      Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_right _ _) hk)
    have hkWidth : Kwidth <= k :=
      Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _) hk)
    obtain ⟨hMiddleLimit, hLimitMiddle⟩ := hKmiddle k hkMiddle
    have hLowerMiddle := hKlower k hkLower
    have hMiddleUpper := hKupper k hkUpper
    have hWidth := hKwidth k hkWidth
    have hUpperLower : (upper scale).approx k <=
        (lower scale).approx k + (q + q) :=
      CReal.leAddOfSubLe hWidth
    have hUpperLimit : (upper scale).approx k <=
        (((((limit.approx k + q) + q) + q) + q)) := by
      have h0 : (upper scale).approx k <=
          ((lower scale).approx k + q) + q :=
        Q'.le_trans' _ _ _ hUpperLower
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (Q'.add_assoc_eqv ((lower scale).approx k) q q)))
      have h1 : ((lower scale).approx k + q) + q <=
          (((middle scale).approx k + q) + q) + q :=
        Q'.add_le_add_right _ _ q
          (Q'.add_le_add_right _ _ q hLowerMiddle)
      have h2 : (((middle scale).approx k + q) + q) + q <=
          ((((limit.approx k + q) + q) + q) + q) :=
        Q'.add_le_add_right _ _ q
          (Q'.add_le_add_right _ _ q
            (Q'.add_le_add_right _ _ q hMiddleLimit))
      exact Q'.le_trans' _ _ _ h0
        (Q'.le_trans' _ _ _ h1 h2)
    have hUpperLimitFinal : (upper scale).approx k <=
        limit.approx k + epsilon :=
      Q'.le_trans' _ _ _ hUpperLimit
        (CReal.collapse4 (limit.approx k) q epsilon
          (CReal.fourQ_le epsilon hepsilon))
    have hLimitUpper2 : limit.approx k <=
        ((upper scale).approx k + q) + q :=
      Q'.le_trans' _ _ _ hLimitMiddle
        (Q'.add_le_add_right _ _ q hMiddleUpper)
    have hq0 : (0 : Q') <= q := Q'.le_of_lt hq
    have hpad1 : ((upper scale).approx k + q) + q <=
        (((upper scale).approx k + q) + q) + q :=
      Q'.add_le_self_of_nonneg _ q hq0
    have hpad2 : (((upper scale).approx k + q) + q) + q <=
        ((((upper scale).approx k + q) + q) + q) + q :=
      Q'.add_le_self_of_nonneg _ q hq0
    have hLimitUpperFinal : limit.approx k <=
        (upper scale).approx k + epsilon :=
      Q'.le_trans' _ _ _ hLimitUpper2
        (Q'.le_trans' _ _ _ hpad1
          (Q'.le_trans' _ _ _ hpad2
            (CReal.collapse4 ((upper scale).approx k) q epsilon
              (CReal.fourQ_le epsilon hepsilon))))
    exact ⟨hUpperLimitFinal, hLimitUpperFinal⟩
  · intro epsilon hepsilon
    let q : Q' := HalfPow.half * (HalfPow.half * epsilon)
    have hq : (0 : Q') < q :=
      ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)
    obtain ⟨Nmiddle, hNmiddle⟩ := middle_converges q hq
    obtain ⟨Nwidth, hNwidth⟩ := width_closes q hq
    refine ⟨max Nmiddle Nwidth, fun scale hscale => ?_⟩
    have hsMiddle : Nmiddle <= scale :=
      Nat.le_trans (Nat.le_max_left _ _) hscale
    have hsWidth : Nwidth <= scale :=
      Nat.le_trans (Nat.le_max_right _ _) hscale
    obtain ⟨Kmiddle, hKmiddle⟩ := hNmiddle scale hsMiddle
    obtain ⟨Klower, hKlower⟩ := lower_le_middle scale q hq
    obtain ⟨Kupper, hKupper⟩ := middle_le_upper scale q hq
    obtain ⟨Kwidth, hKwidth⟩ := (hNwidth scale hsWidth) q hq
    let K := max (max Kmiddle Klower) (max Kupper Kwidth)
    refine ⟨K, fun k hk => ?_⟩
    have hkMiddle : Kmiddle <= k :=
      Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hk)
    have hkLower : Klower <= k :=
      Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hk)
    have hkUpper : Kupper <= k :=
      Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_right _ _) hk)
    have hkWidth : Kwidth <= k :=
      Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _) hk)
    obtain ⟨hMiddleLimit, hLimitMiddle⟩ := hKmiddle k hkMiddle
    have hLowerMiddle := hKlower k hkLower
    have hMiddleUpper := hKupper k hkUpper
    have hWidth := hKwidth k hkWidth
    have hUpperLower : (upper scale).approx k <=
        (lower scale).approx k + (q + q) :=
      CReal.leAddOfSubLe hWidth
    have hLowerLimit2 : (lower scale).approx k <=
        ((limit.approx k + q) + q) :=
      Q'.le_trans' _ _ _ hLowerMiddle
        (Q'.add_le_add_right _ _ q hMiddleLimit)
    have hq0 : (0 : Q') <= q := Q'.le_of_lt hq
    have hpad1 : ((limit.approx k + q) + q) <=
        (((limit.approx k + q) + q) + q) :=
      Q'.add_le_self_of_nonneg _ q hq0
    have hpad2 : (((limit.approx k + q) + q) + q) <=
        ((((limit.approx k + q) + q) + q) + q) :=
      Q'.add_le_self_of_nonneg _ q hq0
    have hLowerLimitFinal : (lower scale).approx k <=
        limit.approx k + epsilon :=
      Q'.le_trans' _ _ _ hLowerLimit2
        (Q'.le_trans' _ _ _ hpad1
          (Q'.le_trans' _ _ _ hpad2
            (CReal.collapse4 (limit.approx k) q epsilon
              (CReal.fourQ_le epsilon hepsilon))))
    have hLimitLower : limit.approx k <=
        (((((lower scale).approx k + q) + q) + q) + q) := by
      have h0 : limit.approx k <=
          ((upper scale).approx k + q) + q :=
        Q'.le_trans' _ _ _ hLimitMiddle
          (Q'.add_le_add_right _ _ q hMiddleUpper)
      have h1 : ((upper scale).approx k + q) + q <=
          ((((lower scale).approx k + q) + q) + q) + q := by
        have hbase : (upper scale).approx k <=
            ((lower scale).approx k + q) + q :=
          Q'.le_trans' _ _ _ hUpperLower
            (Q'.le_of_eqv
              (Q'.eqv_symm
                (Q'.add_assoc_eqv ((lower scale).approx k) q q)))
        exact Q'.add_le_add_right _ _ q
          (Q'.add_le_add_right _ _ q hbase)
      exact Q'.le_trans' _ _ _ h0 h1
    have hLimitLowerFinal : limit.approx k <=
        (lower scale).approx k + epsilon :=
      Q'.le_trans' _ _ _ hLimitLower
        (CReal.collapse4 ((lower scale).approx k) q epsilon
          (CReal.fourQ_le epsilon hepsilon))
    exact ⟨hLowerLimitFinal, hLimitLowerFinal⟩

/-! ## 2. Specialization to the dynamic scheduled squared rate -/

/-- The upper rational Euler exponent is no larger than the odds-corrected
lower exponent. -/
theorem scheduledSquaredRateUpperExponent_le_lower
    (family : DynamicVacuumSectorCompletedFamily 0)
    (rate_pos : forall scale,
      (0 : Q') < (family.completedGap scale).rate)
    (scale time : Nat) :
    scheduledSquaredRateUpperExponent family scale time <=
      scheduledSquaredRateLowerExponent family rate_pos scale time := by
  let r := completedSquaredRate family scale
  have hrPos : (0 : Q') < r :=
    completedSquaredRate_pos family rate_pos scale
  have hrOne : r <= (1 : Q') :=
    completedSquaredRate_le_one family scale
  have hrecipOne : (1 : Q') <=
      completedSquaredRateReciprocal family rate_pos scale := by
    have hanti := ArtanhMonotone.recipPos_antitone
      r 1 hrPos (by decide) hrOne
    have honeRecip : (1 : Q') <= Q'.recipPos 1 (by decide) :=
      Q'.ge_of_eqv (by decide)
    exact Q'.le_trans' _ _ _ honeRecip hanti
  let upper := scheduledSquaredRateUpperExponent family scale time
  have hupper0 : (0 : Q') <= upper :=
    scheduledSquaredRateUpperExponent_nonnegative family scale time
  have hmul : upper * (1 : Q') <=
      upper * completedSquaredRateReciprocal family rate_pos scale :=
    Q'.mul_le_mul_of_nonneg_left _ _ upper hrecipOne hupper0
  have hupperProduct : upper <=
      upper * completedSquaredRateReciprocal family rate_pos scale :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_one_eqv upper)) hmul
  exact Q'.le_trans' _ _ _ hupperProduct
    (Q'.ge_of_eqv
      (scheduledSquaredRateLowerExponent_factor_eqv
        family rate_pos scale time))

/-- The actual upper Euler exponential stream. -/
def scheduledSquaredRateUpperExponential
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) : CReal :=
  ExpNeg.expNeg (scheduledSquaredRateUpperExponent family scale time)
    (scheduledSquaredRateUpperExponent_nonnegative family scale time)

/-- The actual lower Euler exponential stream. -/
def scheduledSquaredRateLowerExponential
    (family : DynamicVacuumSectorCompletedFamily 0)
    (rate_pos : forall scale,
      (0 : Q') < (family.completedGap scale).rate)
    (scale time : Nat) : CReal :=
  ExpNeg.expNeg
    (scheduledSquaredRateLowerExponent family rate_pos scale time)
    (scheduledSquaredRateLowerExponent_nonnegative
      family rate_pos scale time)

/-- Both rational exponential endpoints converge to the same complete limit
as the literal scheduled powers.  Their exponents converge to the physical
value `2 * M * t` by the preceding compiler, so this theorem is the
constructive physical-exponential identification for this route. -/
theorem scheduledSquaredRateEulerExponentials_converge
    (family : DynamicVacuumSectorCompletedFamily 0)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (rate_pos : forall scale,
      (0 : Q') < (family.completedGap scale).rate)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (time : Nat)
    (ratePowerVariation : SummableRationalStepVariation
      (fun scale => normalizedMovingCubeSampledRatePower family scale time)) :
    CReal.ConvergesTo
        (fun scale => scheduledSquaredRateUpperExponential
          family scale time)
        ratePowerVariation.limit /\
      CReal.ConvergesTo
        (fun scale => scheduledSquaredRateLowerExponential
          family rate_pos scale time)
        ratePowerVariation.limit := by
  apply endpoints_converge_of_leRat_sandwich
    ratePowerVariation.converges
    (fun scale =>
      (normalizedMovingCubeSampledRatePower_euler_sandwich
        family rate_pos scale time).1)
    (fun scale =>
      (normalizedMovingCubeSampledRatePower_euler_sandwich
        family rate_pos scale time).2)
  exact expNegEndpoints_leRat_close
    (fun scale =>
      scheduledSquaredRateUpperExponent_nonnegative family scale time)
    (fun scale =>
      scheduledSquaredRateLowerExponent_nonnegative
        family rate_pos scale time)
    (fun scale =>
      scheduledSquaredRateUpperExponent_le_lower
        family rate_pos scale time)
    (scheduledSquaredRateUpperExponent_converges
      family band gapVariation time)
    (scheduledSquaredRateLowerExponent_converges
      family band rate_pos gapVariation time)

/-! ## 3. Rejoin with the exact normalized observable decay -/

/-- The rate-power limit already consumed by the normalized moving-cube decay
theorem, now named as the route-specific physical exponential. -/
def normalizedMovingCubePhysicalExponentialLimit
    (family : DynamicVacuumSectorCompletedFamily 0)
    (ratePower : NormalizedMovingCubeSampledRatePowerRationalVariation family) :
    NormalizedMovingCubeSampledRatePowerLimit family :=
  normalizedMovingCubeSampledRatePowerLimitOfVariation family
    (normalizedMovingCubeSampledRatePowerVariationOfRational family ratePower)

/-- At every physical time the upper and lower rational exponential streams
converge to the exact rate factor appearing in the same-observable continuum
decay theorem. -/
theorem normalizedMovingCubePhysicalExponentialLimit_identification
    (family : DynamicVacuumSectorCompletedFamily 0)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (rate_pos : forall scale,
      (0 : Q') < (family.completedGap scale).rate)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (ratePower : NormalizedMovingCubeSampledRatePowerRationalVariation family)
    (time : Nat) :
    CReal.ConvergesTo
        (fun scale => scheduledSquaredRateUpperExponential
          family scale time)
        ((normalizedMovingCubePhysicalExponentialLimit
          family ratePower).limitRepresentative time) /\
      CReal.ConvergesTo
        (fun scale => scheduledSquaredRateLowerExponential
          family rate_pos scale time)
        ((normalizedMovingCubePhysicalExponentialLimit
          family ratePower).limitRepresentative time) := by
  exact scheduledSquaredRateEulerExponentials_converge
    family band rate_pos gapVariation time (ratePower time)

/-- The normalized same-observable continuum squared-decay bound and the two
physical exponential identifications are returned together.  This prevents a
later consumer from pairing the decay theorem with an unrelated exponential
limit. -/
theorem normalizedMovingCubePhysicalExponential_sq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (normDebt : MovingCubeNormalizationNormDebtRationalVariation family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (rate_pos : forall scale,
      (0 : Q') < (family.completedGap scale).rate)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (ratePower : NormalizedMovingCubeSampledRatePowerRationalVariation family)
    (time : Nat) :
    CReal.RCle
        (CReal.RCmul
          (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
            (normalizedMovingCubeLimitOfRationalDebtVariation
              family raw normDebt) time)
          (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
            (normalizedMovingCubeLimitOfRationalDebtVariation
              family raw normDebt) time))
        (CReal.RCmul
          (CReal.RCmul
            (Quotient.mk CReal.crealSetoid
              ((normalizedMovingCubePhysicalExponentialLimit
                family ratePower).limitRepresentative time))
            (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
              (normalizedMovingCubeLimitOfRationalDebtVariation
                family raw normDebt) 0))
          (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
            (normalizedMovingCubeLimitOfRationalDebtVariation
              family raw normDebt) 0)) /\
      (CReal.ConvergesTo
          (fun scale => scheduledSquaredRateUpperExponential
            family scale time)
          ((normalizedMovingCubePhysicalExponentialLimit
            family ratePower).limitRepresentative time) /\
        CReal.ConvergesTo
          (fun scale => scheduledSquaredRateLowerExponential
            family rate_pos scale time)
          ((normalizedMovingCubePhysicalExponentialLimit
            family ratePower).limitRepresentative time)) := by
  exact
    ⟨normalizedMovingCubeLimitOfRationalVariations_sq_decay
        family raw normDebt ratePower time,
      normalizedMovingCubePhysicalExponentialLimit_identification
        family band rate_pos gapVariation ratePower time⟩

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler.expNegEndpoints_leRat_close
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler.endpoints_converge_of_leRat_sandwich
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler.scheduledSquaredRateUpperExponent_le_lower
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler.scheduledSquaredRateEulerExponentials_converge
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler.normalizedMovingCubePhysicalExponentialLimit_identification
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler.normalizedMovingCubePhysicalExponential_sq_decay
