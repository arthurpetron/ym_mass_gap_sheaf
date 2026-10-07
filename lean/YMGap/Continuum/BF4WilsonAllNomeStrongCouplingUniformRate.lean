/-
# Strong-coupling, width-independent contraction on the literal all-nome carrier

Route (b) of `audits/SCOPE-UNION-ALLNOME-CARRIER-BRIDGE-2026-10-06.md`.

The fixed-width all-nome form is the original joint cutoff/time limit of
`originalWindowScalar` at the literal source width.  At each finite cutoff and
boundary depth that scalar is literally one selected-chain `finiteValue` on the
extent `width+(t+(2H+t))`.  The existing GENERAL selected-chain cluster bound
`finite_covariance_distance_bound` (any extent, any nodup physical id list, any
two link-local probes with connected carriers) is applied there directly, with
the two probes placed at spatial offset `0` (no spatial collar, no
recentering) and separated by the physical lag.  The resulting finite bound
has the fixed rate `timeRate = 1/4` of `BF4WilsonDescentUniformConnectedDecay`
and an amplitude depending on nome, width and the expressions, but not on
cutoff, boundary depth or lag.  It passes through the witnessed original joint
limits; the dyadic moment argument removes the amplitude, giving the two-step
rate `twoStepRate = timeRate*timeRate = 1/16` on the existing completed
vacuum complement.

STRONG-COUPLING ONLY.  All three small-nome guards
(`heatRatio w ≤ 1/2`, `heatRemainderBound w < 1`,
`entropyRate 625 (adjustedCoreRate w hd) < 1`) are explicit hypotheses.  The
rate `timeRate` is the same constant for EVERY literal width; the width only
enters the (removed) amplitude.  This is not an asymptotic-freedom statement
and does not feed the AF capstone: a constant rate fails the B04 upper half on
unbounded `side_j` (`BF4WilsonStrongCouplingUniformRate.constant_rate_not_all_scale_upper`),
and every `NomeSchedule` has `w_j → 1`, leaving the guarded window.  No
continuum, Hamiltonian or physical-spacing identification is made.
-/

import YMGap.Continuum.BF4WilsonStrongCouplingUniformRate
import YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction
import YMGap.Continuum.BF4WilsonAllNomeSeparatedCovariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBoxLocality

namespace YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabDescentDistanceDecay
  (oldGuardBudget comparisonCoreRate comparison_guard)
open YMGap.Continuum.BF4ExactSlabDescentSelectedCovariance
open YMGap.Continuum.BF4ExactSlabDescentCoreCount (countPrefactor)
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount (totalProbeSize)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within unit chart_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl
  (reverse reverse_within reverse_cap mirror_chart_reverse placedPolynomial_shift
   probeBoxSize probeBoxSize_pos)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay
  (sizeLoss probeLinkCount)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBoxLocality (placed_recenter_local)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (includeExpression_placed)
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl (placed_interval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_nodup chainIds_physical)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (RatPolyCoeffEqv)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (LinkLocal)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance (finiteValue_coeff_congr)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry (shiftFace shiftLink)
open YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
open YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay (shifted_root_distance)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal (originFace)
open YMGap.Continuum.Z4FiniteBoxExhaustion (boxLinks)
open YMGap.Continuum.SepLatticeZ4Linf (linfDist natDist)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonAllNomeTimeForm
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap (dyadic_geometric_first_le)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
  (representativeCenteredMoment representativeCenteredMoment_converges
   representativeCenteredMoment_pin completedCenteredScalar completedCenteredScalar_of_orthogonal)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.BF4WilsonStrongCouplingUniformRate (existingPilotNome)

local infix:50 " ≈ " => Q'.eqv

/-! ## Finite geometry at the literal width, spatial offset zero -/

/-- The literal original-window extent at cutoff index `t` and horizon `H`. -/
def litExtent (width H t : Nat) : Nat := width+(t+(2*H+t))

def litIds (width H t : Nat) : List Nat :=
  chainIds (litExtent width H t) width 0 (t+(2*H+t))

/-- Upper probe: the radius-reversed left expression placed after the lag. -/
def litUpper {width : Nat} (R n t : Nat) (x : IntrinsicExpression width) : RatPoly :=
  placedPolynomial (litExtent width (R+n) t) (t+(R+n)) (reverse x)

/-- Lower probe: the right expression in its fixed `R` chart. -/
def litLower {width : Nat} (R n t : Nat) (y : IntrinsicExpression width) : RatPoly :=
  placedPolynomial (litExtent width (R+n) t) t (chart R y)

theorem litInsertion_separated {width : Nat} (R n t : Nat) (x y : IntrinsicExpression width)
    (hx : x.radius ≤ R) :
    placedPolynomial (litExtent width (R+n) t) t
      (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (advance n y))) =
      polyMul (litUpper R n t x) (litLower R n t y) := by
  rw [mirror_chart_reverse (R+n) x (Nat.le_trans hx (Nat.le_add_right R n)),
    chart_advance_add_center]
  change polyMul (placedPolynomial _ t (shift (R+n) (reverse x)))
      (placedPolynomial _ t (chart R y)) = _
  rw [placedPolynomial_shift]
  rfl

theorem litInsertion_left_unit {width : Nat} (R n t : Nat) (x : IntrinsicExpression width)
    (hx : x.radius ≤ R) :
    RatPolyCoeffEqv
      (placedPolynomial (litExtent width (R+n) t) t
        (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (unit width))))
      (litUpper R n t x) := by
  rw [mirror_chart_reverse (R+n) x (Nat.le_trans hx (Nat.le_add_right R n)), chart_unit]
  change RatPolyCoeffEqv (polyMul (placedPolynomial _ t (shift (R+n) (reverse x))) polyOne) _
  rw [placedPolynomial_shift]
  exact RatPolyCoeffEqv.mul_one _

theorem litInsertion_right_unit {width : Nat} (R n t : Nat) (y : IntrinsicExpression width) :
    RatPolyCoeffEqv
      (placedPolynomial (litExtent width (R+n) t) t
        (.mul (mirror (R+n) (chart (R+n) (unit width))) (chart (R+n) (advance n y))))
      (litLower R n t y) := by
  rw [chart_unit, chart_advance_add_center]
  change RatPolyCoeffEqv (polyMul polyOne (placedPolynomial _ t (chart R y))) _
  exact RatPolyCoeffEqv.one_mul _

def litUpper_interval {width : Nat} (R n t : Nat) (x : IntrinsicExpression width)
    (hx : x.radius ≤ R) :
    Interval (boundaryCompleteSlabLinks (litExtent width (R+n) t)).length
      (litUpper R n t x) (intrinsicCap x) := by
  have hw : width ≤ litExtent width (R+n) t := by unfold litExtent; omega
  have ht : t+(R+n)+R ≤ litExtent width (R+n) t := by unfold litExtent; omega
  have P := placed_interval hw ht (reverse x) (within_mono hx _ (reverse_within x))
  simpa only [litUpper, reverse_cap] using P

def litLower_interval {width : Nat} (R n t : Nat) (y : IntrinsicExpression width)
    (hy : y.radius ≤ R) :
    Interval (boundaryCompleteSlabLinks (litExtent width (R+n) t)).length
      (litLower R n t y) (intrinsicCap y) := by
  have hw : width ≤ litExtent width (R+n) t := by unfold litExtent; omega
  have ht : t+R ≤ litExtent width (R+n) t := by unfold litExtent; omega
  have P := placed_interval hw ht (chart R y) (chart_within R y hy)
  simpa only [litLower, chart_cap] using P

/-- Spatial offset `0`: the box sits on the literal slab, no collar. -/
theorem litUpper_local {width : Nat} (R n t : Nat) (x : IntrinsicExpression width)
    (hx : x.radius ≤ R) :
    LinkLocal (litExtent width (R+n) t)
      ((boxLinks (probeBoxSize width R)).map (shiftLink 0 (t+(R+n))))
      (litUpper R n t x) := by
  have h := placed_recenter_local (extent := litExtent width (R+n) t) (start := t+(R+n))
    (space := 0) (targetWidth := width) (by omega : width+0 ≤ width) R (reverse x)
    (within_mono hx _ (reverse_within x))
  have hp := includeExpression_placed (Nat.le_refl width) (litExtent width (R+n) t)
    (t+(R+n)) (reverse x)
  unfold litUpper
  rw [← hp]
  exact h

theorem litLower_local {width : Nat} (R n t : Nat) (y : IntrinsicExpression width)
    (hy : y.radius ≤ R) :
    LinkLocal (litExtent width (R+n) t)
      ((boxLinks (probeBoxSize width R)).map (shiftLink 0 t))
      (litLower R n t y) := by
  have h := placed_recenter_local (extent := litExtent width (R+n) t) (start := t)
    (space := 0) (targetWidth := width) (by omega : width+0 ≤ width) R (chart R y)
    (chart_within R y hy)
  have hp := includeExpression_placed (Nat.le_refl width) (litExtent width (R+n) t)
    t (chart R y)
  unfold litLower
  rw [← hp]
  exact h

private theorem root_distance (space start gap : Nat) :
    linfDist (shiftFace space (start+gap) originFace) (shiftFace space start originFace) = gap := by
  have h := shifted_root_distance space gap 0 start
  simpa only [Nat.add_comm, Nat.zero_add, natDist, Nat.sub_zero, Nat.zero_sub, Nat.add_zero] using h

private theorem budget_pin (w : Q') (hd : heatRemainderBound w < 1)
    {width : Nat} (R n t : Nat) (x y : IntrinsicExpression width) :
    oldGuardBudget
      (shiftedBoxProbe (probeBoxSize width R) 0 (t+(R+n)) (probeBoxSize_pos width R))
      (shiftedBoxProbe (probeBoxSize width R) 0 t (probeBoxSize_pos width R))
      w hd (intrinsicCap x) (intrinsicCap y) ≈
        decayAmplitude w hd width R x y * timeRate^(R+n+1-sizeLoss width R) := by
  have h := oldGuardBudget_factor
    (shiftedBoxProbe (probeBoxSize width R) 0 (t+(R+n)) (probeBoxSize_pos width R))
    (shiftedBoxProbe (probeBoxSize width R) 0 t (probeBoxSize_pos width R))
    w hd (intrinsicCap x) (intrinsicCap y)
  unfold countPrefactor totalProbeSize at h
  rw [shiftedBoxProbe_size, shiftedBoxProbe_size, shiftedBoxProbe_root, shiftedBoxProbe_root,
    root_distance, List.length_append, shiftedBoxLinks_length, shiftedBoxLinks_length] at h
  exact h

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- Finite connected original-window scalar at the literal width, at every
cutoff and boundary depth: fixed rate `timeRate`, amplitude free of cutoff,
depth and lag. -/
theorem originalWindowScalar_connected_sc_bound
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {width : Nat} (stage t n : Nat)
    (x y : IntrinsicExpression width) (R : Nat) (hx : x.radius ≤ R) (hy : y.radius ≤ R) :
    Q'.abs
      (originalWindowScalar hw0 hw1 (2*(R+n))
          (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (advance n y))) stage t t +
        -(originalWindowScalar hw0 hw1 (2*(R+n))
            (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (unit width))) stage t t *
          originalWindowScalar hw0 hw1 (2*(R+n))
            (.mul (mirror (R+n) (chart (R+n) (unit width)))
              (chart (R+n) (advance n y))) stage t t)) ≤
      decayAmplitude w hd width R x y * timeRate^(R+n+1-sizeLoss width R) := by
  have hpin :
      originalWindowScalar hw0 hw1 (2*(R+n))
          (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (advance n y))) stage t t +
        -(originalWindowScalar hw0 hw1 (2*(R+n))
            (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (unit width))) stage t t *
          originalWindowScalar hw0 hw1 (2*(R+n))
            (.mul (mirror (R+n) (chart (R+n) (unit width)))
              (chart (R+n) (advance n y))) stage t t) ≈
      finiteCovariance w hw0 hw1 (litExtent width (R+n) t) (litIds width (R+n) t)
        (fun _ hi => chainIds_physical hi)
        (litUpper R n t x) (litLower R n t y) stage := by
    unfold finiteCovariance
    apply Q'.add_eqv_congr'
    · change finiteValue w hw0 hw1 (litExtent width (R+n) t) (litIds width (R+n) t)
          (fun _ hi => chainIds_physical hi)
          (placedPolynomial (litExtent width (R+n) t) t
            (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (advance n y)))) stage ≈ _
      rw [litInsertion_separated R n t x y hx]
      exact Q'.eqv_refl _
    · apply Q'.neg_eqv_congr
      apply qmul
      · exact finiteValue_coeff_congr w hw0 hw1 _ _ _ _ _
          (litInsertion_left_unit R n t x hx) stage
      · exact finiteValue_coeff_congr w hw0 hw1 _ _ _ _ _
          (litInsertion_right_unit R n t y) stage
  have h := finite_covariance_distance_bound hw0 hw1 hsmall hd hs
    (litExtent width (R+n) t) (litIds width (R+n) t) (chainIds_nodup _ _ _ _)
    (fun _ hi => chainIds_physical hi)
    (litUpper R n t x) (litLower R n t y) (intrinsicCap x) (intrinsicCap y)
    (litUpper_interval R n t x hx) (litLower_interval R n t y hy)
    ((boxLinks (probeBoxSize width R)).map (shiftLink 0 (t+(R+n))))
    ((boxLinks (probeBoxSize width R)).map (shiftLink 0 t))
    (shiftedBoxProbe (probeBoxSize width R) 0 (t+(R+n)) (probeBoxSize_pos width R))
    (shiftedBoxProbe (probeBoxSize width R) 0 t (probeBoxSize_pos width R))
    (litUpper_local R n t x hx) (litLower_local R n t y hy) stage
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (budget_pin w hd R n t x y)))


/-! ## Passage through the witnessed original joint limits -/

/-- The literal-width all-nome intrinsic centered pairing obeys the same
fixed-rate bound; the amplitude is not uniform in width, the rate is. -/
theorem intrinsic_centered_sc_bound
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {width : Nat} (n : Nat) (x y : IntrinsicExpression width)
    (R : Nat) (hx : x.radius ≤ R) (hy : y.radius ≤ R) :
    leEv
      (sub (intrinsicForm hw0 hw1 x (advance n y))
        (mul (intrinsicForm hw0 hw1 x (unit width))
          (intrinsicForm hw0 hw1 (unit width) y)))
      (ofQ' (decayAmplitude w hd width R x y * timeRate^(R+n+1-sizeLoss width R))) := by
  let H := R+n
  let eXY := WindowExpression.mul (mirror H (chart H x)) (chart H (advance n y))
  let eXU := WindowExpression.mul (mirror H (chart H x)) (chart H (unit width))
  let eUY := WindowExpression.mul (mirror H (chart H (unit width))) (chart H (advance n y))
  have hXY := originalJoint_diagonal_converges hw0 hw1 (2*H) eXY
    ⟨mirror_within H (chart H x), within_mono (by omega : H ≤ 2*H) _
      (chart_within H (advance n y) (by change y.radius+n ≤ H; unfold H; omega))⟩
  have hXU := originalJoint_diagonal_converges hw0 hw1 (2*H) eXU
    ⟨mirror_within H (chart H x), True.intro⟩
  have hUY := originalJoint_diagonal_converges hw0 hw1 (2*H) eUY
    ⟨mirror_within H (chart H (unit width)), within_mono (by omega : H ≤ 2*H) _
      (chart_within H (advance n y) (by change y.radius+n ≤ H; unfold H; omega))⟩
  have hprod :=
    Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hXU hUY
  have hconn := TrigAddCReal.convergesTo_add hXY (TrigAddCReal.convergesTo_neg hprod)
  have hbound := leEv_of_convergesTo_le hconn
    (convergesTo_const (ofQ' (decayAmplitude w hd width R x y *
      timeRate^(R+n+1-sizeLoss width R))))
    (fun k => by
      have h := originalWindowScalar_connected_sc_bound hw0 hw1 hsmall hd hs k k n x y R hx hy
      apply leEv_le_ofQ'_of_approx_le
      intro _
      exact Q'.le_trans' _ _ _ (Q'.le_abs_self _) h)
  have hchartXY := intrinsicForm_chart hw0 hw1 x (advance n y) H
    (by unfold H; omega) (by change y.radius+n ≤ H; unfold H; omega)
  have hchartXU := intrinsicForm_chart hw0 hw1 x (unit width) H
    (by unfold H; omega) (Nat.zero_le _)
  have hchartUY := intrinsicForm_chart hw0 hw1 (unit width) (advance n y) H
    (Nat.zero_le _) (by change y.radius+n ≤ H; unfold H; omega)
  have hmarg := intrinsicForm_unit_invariant_right hw0 hw1 n y
  have hmul :=
    (CReal.mul_congr_left hchartXU).trans
      (TrigSignedAdd.mul_congr_right (hmarg.symm.trans hchartUY))
  exact leEv_trans (leEv_of_equiv
    (Equiv_add hchartXY (neg_congr hmul))) hbound

/-! ## Dyadic moment removal of the width-dependent amplitude -/

/-- Strictly positive auxiliary prefactor; it disappears in `scEvenMoment_first_le`. -/
def scPrefactor (w : Q') (hd : heatRemainderBound w < 1)
    {width : Nat} (x : IntrinsicExpression width) : Q' :=
  RationalShiftedGeometric.amplitude timeRate (decayAmplitude w hd width x.radius x x)
    timeRate_positive (sizeLoss width x.radius)

theorem scPrefactor_pos (w : Q') (hd : heatRemainderBound w < 1)
    {width : Nat} (x : IntrinsicExpression width) : (0 : Q') < scPrefactor w hd x :=
  RationalShiftedGeometric.amplitude_pos _ _ timeRate_positive
    (decayAmplitude_nonnegative w hd width x.radius x x) _

theorem scEvenMoment_le_geometric
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {width : Nat} (x : IntrinsicExpression width) (k : Nat) :
    leEv (evenMoment hw0 hw1 x k) (ofQ' (scPrefactor w hd x * twoStepRate^k)) := by
  have h := RationalShiftedGeometric.shifted_bound timeRate_positive timeRate_lt_one
    (decayAmplitude_nonnegative w hd width x.radius x x) (sizeLoss width x.radius) x.radius (2*k)
  rw [Nat.add_comm (2*k) x.radius] at h
  exact leEv_trans
    (intrinsic_centered_sc_bound hw0 hw1 hsmall hd hs (2*k) x x x.radius
      (Nat.le_refl _) (Nat.le_refl _))
    (leEv_ofQ'_of_approx_ge (fun _ => Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (RationalShiftedGeometric.even_power timeRate k)))))

theorem scEvenMoment_first_le
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {width : Nat} (x : IntrinsicExpression width) :
    leEv (evenMoment hw0 hw1 x 1) (mul (ofQ' twoStepRate) (evenMoment hw0 hw1 x 0)) :=
  dyadic_geometric_first_le (evenMoment hw0 hw1 x)
    twoStepRate (scPrefactor w hd x)
    twoStepRate_positive (scPrefactor_pos w hd x)
    (evenMoment_nonnegative hw0 hw1 x)
    (evenMoment_le_zero hw0 hw1 x)
    (evenMoment_dyadic hw0 hw1 x)
    (scEvenMoment_le_geometric hw0 hw1 hsmall hd hs x)

/-- Prefactor-free dense two-step estimate, rate `1/16` at every literal width. -/
theorem sc_centered_twoStep_bound
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {width : Nat} (x : IntrinsicExpression width) :
    leEv (centeredTimeMoment hw0 hw1 2 x x)
      (mul (ofQ' twoStepRate) (centeredTimeMoment hw0 hw1 0 x x)) := by
  simpa only [evenMoment, Nat.mul_one, Nat.mul_zero] using
    scEvenMoment_first_le hw0 hw1 hsmall hd hs x

/-! ## The existing completed all-nome carrier -/

section Completed

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (width : Nat)

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 width

include hsmall hs in
theorem sc_representative_twoStep_form_gap (X : (D).Cauchy) :
    leEv (representativeCenteredMoment hw0 hw1 width 2 X X)
      (mul (ofQ' twoStepRate) (representativeCenteredMoment hw0 hw1 width 0 X X)) :=
  leEv_of_convergesTo_le
    (representativeCenteredMoment_converges hw0 hw1 width 2 X X)
    (convergesTo_const_mul (ofQ' twoStepRate)
      (representativeCenteredMoment_converges hw0 hw1 width 0 X X))
    (fun k => sc_centered_twoStep_bound hw0 hw1 hsmall hd hs (X.seq k))

include hsmall hs in
theorem sc_completed_twoStep_form_gap (x : V) (hx : B x U = RCzero) :
    RCle (B x (T 2 x)) (RCmul (Quotient.mk crealSetoid (ofQ' twoStepRate)) (B x x)) := by
  have h : RCle (completedCenteredScalar hw0 hw1 width 2 x x)
      (RCmul (Quotient.mk crealSetoid (ofQ' twoStepRate))
        (completedCenteredScalar hw0 hw1 width 0 x x)) := by
    refine Quotient.inductionOn x ?_
    intro X
    rw [representativeCenteredMoment_pin hw0 hw1 width 2 X X,
      representativeCenteredMoment_pin hw0 hw1 width 0 X X]
    exact sc_representative_twoStep_form_gap hw0 hw1 hsmall hd hs width X
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 width 2 x hx,
    completedCenteredScalar_of_orthogonal hw0 hw1 width 0 x hx,
    completedTime_zero] at h
  exact h

include hsmall hs in
/-- One-step norm contraction at the width-INDEPENDENT rate `twoStepRate = 1/16`
on every vector orthogonal to the unit state of the literal-width carrier. -/
theorem sc_oneStep_norm_gap (x : V) (hx : B x U = RCzero) :
    RCle (B (T 1 x) (T 1 x)) (RCscale twoStepRate (B x x)) := by
  have h := sc_completed_twoStep_form_gap hw0 hw1 hsmall hd hs width x hx
  have hd2 : B x (T 2 x) = B (T 1 x) (T 1 x) := by
    simpa only [Nat.two_mul] using
      (completedInner_time_sum (width := width) hw0 hw1 1 1 x x).symm
  rw [hd2] at h
  exact h

include hsmall hd hs in
/-- **Route (b), strong coupling.**  The literal fixed-width all-nome carrier
contracts its vacuum complement at the rate `timeRate = 1/4` (squared:
`1/16`), the SAME constant for every width, under the three small-nome guards.
Not an AF statement. -/
theorem allNome_strongCoupling_vacuumSq :
    WilsonVacuumSqContraction hw0 hw1 width timeRate := fun y =>
  sc_oneStep_norm_gap hw0 hw1 hsmall hd hs width y.val
    ((completedInner_symm hw0 hw1 y.val _).trans y.property)

include hsmall hd hs in
/-- Width-uniform form: one rate for all literal widths at once. -/
theorem allNome_strongCoupling_vacuumSq_all_widths :
    ∀ width : Nat, WilsonVacuumSqContraction hw0 hw1 width timeRate :=
  fun width => allNome_strongCoupling_vacuumSq hw0 hw1 hsmall hd hs width

end Completed

/-! ## Non-vacuity at the existing pilot nome `w = 1/1024` -/

/-- Unconditional: at `w = 1/1024` every literal width carries the same
strong-coupling contraction rate `1/4`, with `0 < 1/4 < 1`. -/
theorem existingNome_allNome_strongCoupling :
    let w := existingPilotNome
    ∃ (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')),
      (0 : Q') < timeRate ∧ timeRate < (1 : Q') ∧
      ∀ width : Nat, WilsonVacuumSqContraction hw0 hw1 width timeRate := by
  intro w
  exact ⟨nome_pos, nome_lt_one, timeRate_positive, timeRate_lt_one,
    allNome_strongCoupling_vacuumSq_all_widths nome_pos nome_lt_one
      existingNome_guards.1 existingNome_guards.2 existingNome_entropyRate.2⟩

end YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate

#print axioms YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.litInsertion_separated
#print axioms YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.litUpper_local
#print axioms YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.originalWindowScalar_connected_sc_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.intrinsic_centered_sc_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.scEvenMoment_first_le
#print axioms YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.sc_centered_twoStep_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.sc_oneStep_norm_gap
#print axioms YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.allNome_strongCoupling_vacuumSq
#print axioms YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.allNome_strongCoupling_vacuumSq_all_widths
#print axioms YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.existingNome_allNome_strongCoupling
