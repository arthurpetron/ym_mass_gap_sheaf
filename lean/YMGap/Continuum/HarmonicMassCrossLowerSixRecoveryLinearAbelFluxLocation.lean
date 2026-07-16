/-
# Rational location of the complementary-increment peak

The preceding unimodality module proves that one local descent persists.  This
module supplies a fully rational descent certificate.  Writing `M = k+2`,
the ratio of consecutive harmonic weights is governed by

    harmW k / harmW (k+1) = 1 - 1/M^2.

Reciprocal Bernoulli therefore locates the descending side as soon as the
power exponent is at least `M`.  For the quadratic complementary exponent
this gives the explicit, measurement-free threshold

    k + 2 <= 2*j*(j-1) + 2.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxUnimodality
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxLocation

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryClearing
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxUnimodality
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem flux_location_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "flux_location_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               flux_location_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.natCast_mul,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem harmU_step_mul_one_add_eqv (k : Nat) :
    harmU (k + 1) * ((1 : Q') + harmU k) ≈ harmU k := by
  change Q'.invSucc (k + 2) *
      ((1 : Q') + Q'.invSucc (k + 1)) ≈ Q'.invSucc (k + 1)
  have h := YMGap.Constructive.ExpNeg.invSucc_cancel (k + 1)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_comm_eqv (1 : Q') (Q'.invSucc (k + 1)))) h

private def peakCofactorL : RingNormaliser.PolyExpr :=
  .mul (.add (.const 1) (.var 0))
    (.add (.const 1) (.neg (.var 1)))

private def peakCofactorR : RingNormaliser.PolyExpr :=
  .add (.add (.const 1) (.var 0))
    (.neg (.mul (.var 1) (.add (.const 1) (.var 0))))

private theorem peakCofactor_normal :
    RingNormaliser.normalize peakCofactorL =
      RingNormaliser.normalize peakCofactorR := by decide

private theorem peak_cofactor_regroup (u v : Q') :
    ((1 : Q') + u) * ((1 : Q') + -v) ≈
      ((1 : Q') + u) + -(v * ((1 : Q') + u)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    peakCofactorL peakCofactorR peakCofactor_normal
    (fun | 0 => u | _ => v)
  simpa [peakCofactorL, peakCofactorR, RingNormaliser.eval] using h

private def peakWeightFactorL : RingNormaliser.PolyExpr :=
  .mul (.add (.const 1) (.neg (.var 1)))
    (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))

private def peakWeightFactorR : RingNormaliser.PolyExpr :=
  .mul (.add (.const 1) (.neg (.var 0)))
    (.mul (.add (.const 1) (.var 0))
      (.add (.const 1) (.neg (.var 1))))

private theorem peakWeightFactor_normal :
    RingNormaliser.normalize peakWeightFactorL =
      RingNormaliser.normalize peakWeightFactorR := by decide

private theorem peak_weight_factor_regroup (u v : Q') :
    ((1 : Q') + -v) * ((1 : Q') + -(u * u)) ≈
      ((1 : Q') + -u) *
        (((1 : Q') + u) * ((1 : Q') + -v)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    peakWeightFactorL peakWeightFactorR peakWeightFactor_normal
    (fun | 0 => u | _ => v)
  simpa [peakWeightFactorL, peakWeightFactorR,
    RingNormaliser.eval] using h

private theorem oldWeight_eqv_newWeight_mul_inverseSquareBase (k : Nat) :
    harmW k ≈
      harmW (k + 1) * oneSub (harmU k * harmU k) := by
  let u := harmU k
  let v := harmU (k + 1)
  have huv : v * ((1 : Q') + u) ≈ u := by
    dsimp only [u, v]
    exact harmU_step_mul_one_add_eqv k
  have hcofactor : ((1 : Q') + u) * ((1 : Q') + -v) ≈ (1 : Q') := by
    refine Q'.eqv_trans _
      ((1 : Q') + u + -(v * ((1 : Q') + u))) _ ?_ ?_
    · exact peak_cofactor_regroup u v
    refine Q'.eqv_trans _ ((1 : Q') + u + -u) _ ?_ ?_
    · exact Q'.add_eqv_congr_left ((1 : Q') + u) _ _
        (Q'.neg_eqv_congr _ _ huv)
    refine Q'.eqv_trans _ ((1 : Q') + (u + -u)) _
      (Q'.add_assoc_eqv (1 : Q') u (-u)) ?_
    refine Q'.eqv_trans _ ((1 : Q') + (0 : Q')) _
      (Q'.add_eqv_congr_left (1 : Q') _ _ (Q'.add_neg_self_eqv u)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (1 : Q'))
  have hregroup := peak_weight_factor_regroup u v
  have hfinish :
      ((1 : Q') + -u) *
          (((1 : Q') + u) * ((1 : Q') + -v)) ≈
        ((1 : Q') + -u) := by
    refine Q'.eqv_trans _ (((1 : Q') + -u) * (1 : Q')) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hcofactor
    exact Q'.mul_one_eqv _
  dsimp only [u, v] at hregroup hfinish ⊢
  unfold harmW oneSub
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hregroup hfinish)

private theorem oneSub_oneSub_eqv_local (x : Q') :
    (1 : Q') + -oneSub x ≈ x := by
  unfold oneSub
  have hneg : (-((1 : Q') + -x)) ≈ (-(1 : Q')) + x :=
    Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (1 : Q') (-x))
      (Q'.add_eqv_congr_left (-(1 : Q')) _ _ (Q'.neg_neg_eqv x))
  refine Q'.eqv_trans _ ((1 : Q') + (-(1 : Q') + x)) _
    (Q'.add_eqv_congr_left (1 : Q') _ _ hneg) ?_
  refine Q'.eqv_trans _ (((1 : Q') + -(1 : Q')) + x) _
    (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-(1 : Q')) x)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + x) _
    (Q'.add_eqv_congr_right _ _ x (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' x)

/-- The reciprocal-Bernoulli denominator at one harmonic block is exactly
`1 + harmU k`. -/
theorem lowerSixRecoveryPeakBernDen_eqv_one_add_margin (k : Nat) :
    bernDen (harmU k * harmU k) (k + 2) ≈
      (1 : Q') + harmU k := by
  let u := harmU k
  have hMu : Q'.ofNat (k + 2) * u ≈ (1 : Q') := by
    dsimp only [u]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (Q'.ofNat (k + 2)) (harmU k))
      (recovery_harmU_mul_den k)
  have hscaled : Q'.ofNat (k + 2) * (u * u) ≈ u := by
    refine Q'.eqv_trans _ ((Q'.ofNat (k + 2) * u) * u) _ ?_ ?_
    · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    refine Q'.eqv_trans _ ((1 : Q') * u) _
      (Q'.mul_eqv_congr_right _ _ u hMu) ?_
    exact Q'.one_mul_eqv u
  unfold bernDen
  dsimp only [u] at hscaled ⊢
  exact Q'.add_eqv_congr_left (1 : Q') _ _ hscaled

private theorem oldMargin_eqv_newMargin_mul_peakBernDen (k : Nat) :
    (1 : Q') + -harmW k ≈
      ((1 : Q') + -harmW (k + 1)) *
        bernDen (harmU k * harmU k) (k + 2) := by
  let u := harmU k
  let v := harmU (k + 1)
  let B := bernDen (u * u) (k + 2)
  have hB : B ≈ (1 : Q') + u := by
    dsimp only [B, u]
    exact lowerSixRecoveryPeakBernDen_eqv_one_add_margin k
  have hvB : v * B ≈ u := by
    refine Q'.eqv_trans _ (v * ((1 : Q') + u)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left v _ _ hB
    dsimp only [u, v]
    exact harmU_step_mul_one_add_eqv k
  have hold : (1 : Q') + -harmW k ≈ u := by
    unfold harmW
    dsimp only [u]
    exact oneSub_oneSub_eqv_local (harmU k)
  have hnew : (1 : Q') + -harmW (k + 1) ≈ v := by
    unfold harmW
    dsimp only [v]
    exact oneSub_oneSub_eqv_local (harmU (k + 1))
  have hright :
      ((1 : Q') + -harmW (k + 1)) * B ≈ u := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ B hnew) hvB
  dsimp only [B, u, v] at hold hright ⊢
  exact Q'.eqv_trans _ _ _ hold (Q'.eqv_symm hright)

private theorem bernDen_mono_exponent
    {u : Q'} (hu0 : (0 : Q') ≤ u) {a b : Nat} (hab : a ≤ b) :
    bernDen u a ≤ bernDen u b := by
  have hnat : Q'.ofNat a ≤ Q'.ofNat b := Q'.ofNat_le_ofNat hab
  have hmul : Q'.ofNat a * u ≤ Q'.ofNat b * u :=
    Q'.mul_le_mul_of_nonneg_right _ _ u hnat hu0
  unfold bernDen
  exact Q'.add_le_add_left (1 : Q') _ _ hmul

/-- Reciprocal Bernoulli pays the exact harmonic peak factor at every power
at least `k+2`. -/
theorem lowerSixRecoveryInverseSquarePeakFactor_le_one
    {k m : Nat} (hkm : k + 2 ≤ m) :
    qpow (oneSub (harmU k * harmU k)) m *
        bernDen (harmU k * harmU k) (k + 2) ≤ (1 : Q') := by
  let u := harmU k
  let d := u * u
  let t := oneSub d
  have hu0 : (0 : Q') ≤ u := by
    dsimp only [u]
    exact harmU_nonneg k
  have hu1 : u ≤ (1 : Q') := by
    dsimp only [u]
    exact harmU_le_one k
  have hd0 : (0 : Q') ≤ d := by
    dsimp only [d]
    exact Q'.mul_nonneg _ _ hu0 hu0
  have hdraw : d ≤ (1 : Q') * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg hu1 hu1 (by decide) hu0
  have hd1 : d ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hdraw (Q'.le_of_eqv (Q'.one_mul_eqv (1 : Q')))
  have ht0 : (0 : Q') ≤ t := by
    dsimp only [t]
    exact Q'.sub_nonneg_of_le hd1
  have hden : bernDen d (k + 2) ≤ bernDen d m :=
    bernDen_mono_exponent hd0 hkm
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (qpow t m) hden
    (qpow_nonneg t ht0 m)
  have hbern := oneSub_pow_mul_bernDen_le hd0 hd1 m
  dsimp only [u, d, t] at hscaled hbern ⊢
  exact Q'.le_trans' _ _ _ hscaled hbern

private theorem lowerSixRecoveryPowerStepFlux_eqv_peakFactor
    (k m : Nat) :
    lowerSixRecoveryPowerStepFlux (harmW k) m ≈
      lowerSixRecoveryPowerStepFlux (harmW (k + 1)) m *
        (qpow (oneSub (harmU k * harmU k)) m *
          bernDen (harmU k * harmU k) (k + 2)) := by
  let t := oneSub (harmU k * harmU k)
  have hbase := oldWeight_eqv_newWeight_mul_inverseSquareBase k
  have hpowBase :=
    YMGap.Continuum.BondMovingRelResidual.qpow_eqv_congr_base hbase m
  have hpowMul :=
    YMGap.Continuum.RefinedRetune.qpow_mul_base (harmW (k + 1)) t m
  have hpow : qpow (harmW k) m ≈
      qpow (harmW (k + 1)) m * qpow t m :=
    Q'.eqv_trans _ _ _ hpowBase hpowMul
  have hmargin := oldMargin_eqv_newMargin_mul_peakBernDen k
  unfold lowerSixRecoveryPowerStepFlux
  dsimp only [t] at hpow ⊢
  refine Q'.eqv_trans _
    ((qpow (harmW (k + 1)) m *
        qpow (oneSub (harmU k * harmU k)) m) *
      (((1 : Q') + -harmW (k + 1)) *
        bernDen (harmU k * harmU k) (k + 2))) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((qpow (harmW (k + 1)) m *
          qpow (oneSub (harmU k * harmU k)) m) *
        ((1 : Q') + -harmW k)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hpow
    exact Q'.mul_eqv_congr_left _ _ _ hmargin
  flux_location_ring

/-- The old harmonic power flux is below the new one from exponent `k+2`
onward.  This is the rational peak-location certificate. -/
theorem lowerSixRecoveryPowerStepFlux_mono_of_scale_le_exponent
    {k m : Nat} (hkm : k + 2 ≤ m) :
    lowerSixRecoveryPowerStepFlux (harmW k) m ≤
      lowerSixRecoveryPowerStepFlux (harmW (k + 1)) m := by
  let F := lowerSixRecoveryPowerStepFlux (harmW (k + 1)) m
  let P := qpow (oneSub (harmU k * harmU k)) m *
    bernDen (harmU k * harmU k) (k + 2)
  have hF0 : (0 : Q') ≤ F := by
    dsimp only [F]
    exact lowerSixRecoveryPowerStepFlux_nonnegative
      (harmW_nonneg (k + 1)) (harmW_le_one (k + 1)) m
  have hP : P ≤ (1 : Q') := by
    dsimp only [P]
    exact lowerSixRecoveryInverseSquarePeakFactor_le_one hkm
  have hmul := Q'.mul_le_mul_of_nonneg_left P (1 : Q') F hP hF0
  have heq := lowerSixRecoveryPowerStepFlux_eqv_peakFactor k m
  dsimp only [F, P] at hmul ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.mul_one_eqv _)))

private theorem powerScaleIncrement_descent_of_flux_mono_local
    {x y : Q'} {m : Nat}
    (hflux : lowerSixRecoveryPowerStepFlux x m ≤
      lowerSixRecoveryPowerStepFlux y m) :
    lowerSixRecoveryPowerScaleIncrement x y (m + 1) ≤
      lowerSixRecoveryPowerScaleIncrement x y m := by
  have hnonneg := Q'.sub_nonneg_of_le hflux
  have h := lowerSixRecoveryPowerScaleIncrement_step_sub_eqv_fluxDrop x y m
  have hn := Q'.neg_eqv_congr _ _ h
  have hreverse :
      lowerSixRecoveryPowerScaleIncrement x y m +
          -lowerSixRecoveryPowerScaleIncrement x y (m + 1) ≈
        lowerSixRecoveryPowerStepFlux y m +
          -lowerSixRecoveryPowerStepFlux x m := by
    refine Q'.eqv_trans _
      (-(lowerSixRecoveryPowerScaleIncrement x y (m + 1) +
        -lowerSixRecoveryPowerScaleIncrement x y m)) _ ?_ ?_
    · flux_location_ring
    refine Q'.eqv_trans _
      (-(lowerSixRecoveryPowerStepFlux x m +
        -lowerSixRecoveryPowerStepFlux y m)) _ hn ?_
    flux_location_ring
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hnonneg (Q'.ge_of_eqv hreverse))

private theorem lowerSixRecoveryPowerScaleIncrement_step_descent
    {k m : Nat} (hkm : k + 2 ≤ m) :
    lowerSixRecoveryPowerScaleIncrement (harmW k) (harmW (k + 1)) (m + 1) ≤
      lowerSixRecoveryPowerScaleIncrement (harmW k) (harmW (k + 1)) m := by
  exact powerScaleIncrement_descent_of_flux_mono_local
    (lowerSixRecoveryPowerStepFlux_mono_of_scale_le_exponent hkm)

private theorem lowerSixRecoveryPowerScaleIncrement_antitone_above_scale
    {k a b : Nat} (hka : k + 2 ≤ a) (hab : a ≤ b) :
    lowerSixRecoveryPowerScaleIncrement (harmW k) (harmW (k + 1)) b ≤
      lowerSixRecoveryPowerScaleIncrement (harmW k) (harmW (k + 1)) a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      have hstep := lowerSixRecoveryPowerScaleIncrement_step_descent
        (k := k) (m := a + d) (by omega)
      rw [show a + (d + 1) = (a + d) + 1 by omega]
      exact Q'.le_trans' _ _ _ hstep (ih (by omega))

/-- Explicit descending-side certificate for the production complementary
increment.  The threshold is entirely rational and derived in substrate. -/
theorem lowerSixRecoveryComplementScaleIncrement_descent_of_exponent_ge_scale
    {k j : Nat}
    (hkj : k + 2 ≤ lowerSixRecoveryComplementExponent j) :
    lowerSixRecoveryComplementScaleIncrement k (j + 1) ≤
      lowerSixRecoveryComplementScaleIncrement k j := by
  let e := lowerSixRecoveryComplementExponent j
  have hshape : lowerSixRecoveryComplementExponent (j + 1) = e + 4 * j := by
    dsimp only [e, lowerSixRecoveryComplementExponent]
    exact lowerSixRecoveryComplementExponent_succ j
  have hp := lowerSixRecoveryPowerScaleIncrement_antitone_above_scale
    hkj (show e ≤ e + 4 * j by omega)
  rw [← hshape] at hp
  have hj := lowerSixRecoveryComplementScaleIncrement_eqv_powerIncrement k j
  have hj1 := lowerSixRecoveryComplementScaleIncrement_eqv_powerIncrement
    k (j + 1)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hj1)
    (Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv hj))

/-- Once the quadratic exponent reaches `k+2`, the entire later variation
tail has the favorable Abel sign. -/
theorem lowerSixRecoveryComplementScaleIncrement_tail_antitone_of_exponent_ge_scale
    {k j : Nat} (hj : 1 ≤ j)
    (hkj : k + 2 ≤ lowerSixRecoveryComplementExponent j) :
    ∀ d,
      lowerSixRecoveryComplementScaleIncrement k (j + d + 1) ≤
        lowerSixRecoveryComplementScaleIncrement k (j + d) := by
  exact lowerSixRecoveryComplementScaleIncrement_tail_antitone hj
    (lowerSixRecoveryComplementScaleIncrement_descent_of_exponent_ge_scale hkj)

#print axioms lowerSixRecoveryPeakBernDen_eqv_one_add_margin
#print axioms lowerSixRecoveryInverseSquarePeakFactor_le_one
#print axioms lowerSixRecoveryPowerStepFlux_mono_of_scale_le_exponent
#print axioms lowerSixRecoveryComplementScaleIncrement_descent_of_exponent_ge_scale
#print axioms lowerSixRecoveryComplementScaleIncrement_tail_antitone_of_exponent_ge_scale

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxLocation
