/-
Post-bootstrap quantitative bounds for the linear-preload recovery carrier.

The exact linear-Abel split reduces the favorable scale reserve to monotonicity
of a one-variable weighted recovery polynomial.  This file isolates the two
uniform estimates on the physical fixed-center window used by that monotonicity
argument: an old-scale odd-power floor and a tiny adjacent-scale preload-growth
ceiling.  Both constants are derived from the exact square-root cell geometry.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
import YMGap.Continuum.MovingCutoff
import YMGap.Continuum.CoreBResidualBaseUniform

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPostBootstrap

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.CoreBResidualBaseUniform

local infix:50 " ≈ " => Q'.eqv

private theorem post_bootstrap_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "post_bootstrap_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               post_bootstrap_neg_num_cast, Q'.ofNat_num_cast,
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

local macro "post_bootstrap_fraction_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               post_bootstrap_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.natCast_add, Int.natCast_mul,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Uniform old-power floor retained in the post-bootstrap physical window. -/
def lowerSixRecoveryPowerFloor : Q' := Q'.mkPos 31 40 (by decide)

/-- Uniform ceiling for the very small adjacent-scale preload growth. -/
def lowerSixRecoveryDriftPowerCeil : Q' := Q'.mkPos 65 64 (by decide)

/-- Reciprocal floor paired with the post-bootstrap drift ceiling. -/
def lowerSixRecoveryHarmWFloor : Q' := Q'.mkPos 64 65 (by decide)

private def nineFortieths : Q' := Q'.mkPos 9 40 (by decide)
private def oneSixtyFifth : Q' := Q'.mkPos 1 65 (by decide)
private def nineFifths : Q' := Q'.mkPos 9 5 (by decide)
private def sixtyTwoFifths : Q' := Q'.mkPos 62 5 (by decide)
private def threeFifths : Q' := Q'.mkPos 3 5 (by decide)
private def thirtyOneFifths : Q' := Q'.mkPos 31 5 (by decide)

private abbrev PostBootstrapPE := RingNormaliser.PolyExpr

private def pSixtyFiveSub : PostBootstrapPE :=
  .add (.mul (.const 65) (.var 0)) (.neg (.var 0))

private def pSixtyFourMul : PostBootstrapPE :=
  .mul (.const 64) (.var 0)

private theorem pSixtyFiveSub_normal :
    RingNormaliser.normalize pSixtyFiveSub =
      RingNormaliser.normalize pSixtyFourMul := by
  decide

private theorem sixtyFive_sub_algebra (P : Q') :
    Q'.ofNat 65 * P + -P ≈ Q'.ofNat 64 * P := by
  simpa [pSixtyFiveSub, pSixtyFourMul, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSixtyFiveSub pSixtyFourMul pSixtyFiveSub_normal (fun _ => P))

private def pAddCancel : PostBootstrapPE :=
  .add (.add (.const 65) (.var 0)) (.neg (.var 0))

private def pAddCancelR : PostBootstrapPE := .const 65

private theorem pAddCancel_normal :
    RingNormaliser.normalize pAddCancel =
      RingNormaliser.normalize pAddCancelR := by
  decide

private theorem add_cancel_algebra (P : Q') :
    (Q'.ofNat 65 + P) + -P ≈ Q'.ofNat 65 := by
  simpa [pAddCancel, pAddCancelR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pAddCancel pAddCancelR pAddCancel_normal (fun _ => P))

/-- The first cell after the finite bootstrap has center at least thirty-six,
and every later fixed-center cell does as well. -/
theorem lowerSixWithinCenterCell_center_ge_thirtySix
    {k c : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c) :
    36 ≤ c := by
  rcases Nat.lt_or_ge c 36 with hc | hc
  · have hcp : c + 1 ≤ 36 := by omega
    have hsquare := Nat.mul_le_mul hcp hcp
    have hright := hcell.2.2.2
    omega
  · exact hc

/-- The physical recovery modes obey a sharpened odd-exponent budget.  The
constant `9/40` is chosen to leave a strict margin after the preload drift. -/
theorem lowerSixWithinCenterCell_oddExponent_budget
    {k c j : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hj : j < 2 * c) :
    40 * (2 * (j + 1) + 1) ≤ 9 * (k + 2) := by
  let D := k + 2
  have hc36 : 36 ≤ c :=
    lowerSixWithinCenterCell_center_ge_thirtySix hk hcell
  have h89 : 89 ≤ 4 * c := by omega
  have hfirst : 320 * c + 89 ≤ 324 * c := by omega
  have h36c : 36 * c ≤ c * c :=
    Nat.mul_le_mul_right c hc36
  have hscaled : 324 * c ≤ 9 * (c * c) := by
    have h := Nat.mul_le_mul_left 9 h36c
    omega
  have hquad : 320 * c + 89 ≤ 9 * (c * c) :=
    Nat.le_trans hfirst hscaled
  have hcellSq := hcell.2.2.1
  have hcellScaled := Nat.mul_le_mul_left 9 hcellSq
  have hcD : 160 * c + 40 ≤ 9 * D := by
    dsimp only [D]
    omega
  have hjc : j + 1 ≤ 2 * c := by omega
  dsimp only [D] at hcD ⊢
  omega

private theorem recovery_mode_fraction_le_nineFortieths
    {k c j : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hj : j < 2 * c) :
    Q'.ofNat (2 * (j + 1) + 1) * harmU k ≤ nineFortieths := by
  have hnat := lowerSixWithinCenterCell_oddExponent_budget hk hcell hj
  unfold harmU unit nineFortieths
  show
    (Q'.ofNat (2 * (j + 1) + 1) *
      Q'.mkPos 1 (k + 2) (by omega)).num *
        ((Q'.mkPos 9 40 (by decide)).den : Int) ≤
      (Q'.mkPos 9 40 (by decide)).num *
        (Q'.ofNat (2 * (j + 1) + 1) *
          Q'.mkPos 1 (k + 2) (by omega)).den
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
    Int.mul_one, Int.one_mul]
  have hnat' : (2 * (j + 1) + 1) * 40 ≤ 9 * (k + 2) := by
    simpa [Nat.mul_comm] using hnat
  exact_mod_cast hnat'

private theorem one_sub_harmW_eqv_harmU (k : Nat) :
    (1 : Q') - harmW k ≈ harmU k := by
  unfold harmW ReciprocalBernoulliUpper.oneSub
  let rho : Nat → Q' := fun _ => harmU k
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
    (.var 0) (by decide) rho

/-- On every post-bootstrap physical recovery mode, the old odd heat-kernel
power is at least `31/40`. -/
theorem lowerSixRecoveryOldOddPower_ge_floor
    {k c j : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hj : j < 2 * c) :
    lowerSixRecoveryPowerFloor ≤
      qpow (harmW k) (2 * (j + 1) + 1) := by
  let b := 2 * (j + 1) + 1
  have hfrac := recovery_mode_fraction_le_nineFortieths hk hcell hj
  have hneg := Q'.neg_le_neg hfrac
  have hadd := Q'.add_le_add_left (1 : Q') _ _ hneg
  have hconstant :
      (1 : Q') + -nineFortieths ≈ lowerSixRecoveryPowerFloor := by
    unfold nineFortieths lowerSixRecoveryPowerFloor
    decide
  have hfloor : lowerSixRecoveryPowerFloor ≤
      (1 : Q') + -(Q'.ofNat b * harmU k) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hconstant) hadd
  have hcomp := one_sub_harmW_eqv_harmU k
  have hleft :
      (1 : Q') - Q'.ofNat b * ((1 : Q') - harmW k) ≈
        (1 : Q') + -(Q'.ofNat b * harmU k) := by
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat b) _ _ hcomp))
  have hbern := MovingCutoff.qpow_ge_bernoulli
    (harmW_nonneg k) (harmW_le_one k) b
  dsimp only [b] at hfrac hfloor hleft hbern ⊢
  exact Q'.le_trans' _ _ _ hfloor
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hbern)

/-- The linear preload exponent is much smaller than one harmonic drift
denominator throughout the post-bootstrap physical cell. -/
theorem lowerSixWithinCenterCell_preload_driftDen_budget
    {k c j : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hj : j < 2 * c) :
    65 * (6 * j) ≤ driftDen k := by
  let D := k + 2
  have hc36 : 36 ≤ c :=
    lowerSixWithinCenterCell_center_ge_thirtySix hk hcell
  have h36c : 36 * c ≤ c * c :=
    Nat.mul_le_mul_right c hc36
  have hcellSq := hcell.2.2.1
  have h12c : 12 * c ≤ D := by
    dsimp only [D]
    omega
  have h6j : 6 * j ≤ D := by
    dsimp only [D] at h12c ⊢
    omega
  have hD66 : 66 ≤ D := by dsimp only [D]; omega
  have hcoef : 65 < D := by omega
  have hstrict : 65 * D < D * D :=
    Nat.mul_lt_mul_of_pos_right hcoef (by omega)
  have hden : 65 * D ≤ D * D - 1 := by omega
  have hscaled := Nat.mul_le_mul_left 65 h6j
  unfold driftDen
  dsimp only [D] at hscaled hden ⊢
  exact Nat.le_trans hscaled hden

private theorem preload_fraction_le_oneSixtyFifth
    {k c j : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hj : j < 2 * c) :
    Q'.ofNat (6 * j) * unit (driftDen k) (driftDen_pos k) ≤
      oneSixtyFifth := by
  have hnat := lowerSixWithinCenterCell_preload_driftDen_budget hk hcell hj
  unfold oneSixtyFifth unit
  show
    (Q'.ofNat (6 * j) *
      Q'.mkPos 1 (driftDen k) (driftDen_pos k)).num *
        ((Q'.mkPos 1 65 (by decide)).den : Int) ≤
      (Q'.mkPos 1 65 (by decide)).num *
        (Q'.ofNat (6 * j) *
          Q'.mkPos 1 (driftDen k) (driftDen_pos k)).den
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
    Int.mul_one, Int.one_mul]
  have hnat' : 6 * j * 65 ≤ driftDen k := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hnat
  exact_mod_cast hnat'

private theorem qpow_one_add_le_sixtyFive_sixtyFour
    {u : Q'} (hu : (0 : Q') ≤ u) (m : Nat)
    (hsmall : Q'.ofNat m * u ≤ oneSixtyFifth) :
    qpow ((1 : Q') + u) m ≤ lowerSixRecoveryDriftPowerCeil := by
  let P := qpow ((1 : Q') + u) m
  let x := Q'.ofNat m * u
  have hP0 : (0 : Q') ≤ P := by
    dsimp only [P]
    exact qpow_nonneg _ (Q'.zero_le_add _ _ (by decide) hu) _
  have hgrowth := qpow_one_add_growth hu
    (Q'.eqv_refl ((1 : Q') + u)) m
  change P ≤ (1 : Q') + x * P at hgrowth
  have h65x : Q'.ofNat 65 * x ≤ (1 : Q') := by
    have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 65)
      hsmall (HeatKernelRGStep.zero_le_ofNat _)
    have hconst : Q'.ofNat 65 * oneSixtyFifth ≈ (1 : Q') := by
      unfold oneSixtyFifth
      decide
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hconst)
  have h65xP := Q'.mul_le_mul_of_nonneg_right _ _ P h65x hP0
  have h65xP' : (Q'.ofNat 65 * x) * P ≤ P :=
    Q'.le_trans' _ _ _ h65xP
      (Q'.le_of_eqv (Q'.one_mul_eqv P))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 65)
    hgrowth (HeatKernelRGStep.zero_le_ofNat _)
  have hupper : Q'.ofNat 65 * ((1 : Q') + x * P) ≤
      Q'.ofNat 65 + P := by
    have hadd := Q'.add_le_add_left (Q'.ofNat 65) _ _ h65xP'
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by post_bootstrap_ring)) hadd
  have h65 : Q'.ofNat 65 * P ≤ Q'.ofNat 65 + P :=
    Q'.le_trans' _ _ _ hscaled hupper
  have hsub := Q'.add_le_add_right _ _ (-P) h65
  have h64 : Q'.ofNat 64 * P ≤ Q'.ofNat 65 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm
      (sixtyFive_sub_algebra P)))
      (Q'.le_trans' _ _ _ hsub (Q'.le_of_eqv (add_cancel_algebra P)))
  have hceil : Q'.ofNat 64 * lowerSixRecoveryDriftPowerCeil ≈
      Q'.ofNat 65 := by
    unfold lowerSixRecoveryDriftPowerCeil
    decide
  have hmul : Q'.ofNat 64 * P ≤
      Q'.ofNat 64 * lowerSixRecoveryDriftPowerCeil :=
    Q'.le_trans' _ _ _ h64 (Q'.ge_of_eqv hceil)
  exact Q'.le_of_mul_le_mul_left hmul
    (by decide : (0 : Q') < Q'.ofNat 64)

/-- Every physical linear preload grows by at most `65/64` across one
post-bootstrap harmonic scale. -/
theorem lowerSixRecoveryDriftRatio_preload_le_ceil
    {k c j : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hj : j < 2 * c) :
    qpow (driftRatio k) (6 * j) ≤
      lowerSixRecoveryDriftPowerCeil := by
  let u := unit (driftDen k) (driftDen_pos k)
  have hsmall := preload_fraction_le_oneSixtyFifth hk hcell hj
  have hpow := qpow_one_add_le_sixtyFive_sixtyFour
    (unit_nonneg _ _) (6 * j) hsmall
  have hbase := BondMovingRelResidual.qpow_eqv_congr_base
    (driftRatio_eqv_one_add_unitDen k) (6 * j)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hbase) hpow

private theorem postBootstrap_one_le_qpow {q : Q'}
    (hq : (1 : Q') ≤ q) : ∀ d, (1 : Q') ≤ qpow q d
  | 0 => Q'.le_refl' 1
  | d + 1 => by
      have hq0 : (0 : Q') ≤ q := Q'.le_trans' _ _ _ (by decide) hq
      have hd0 : (0 : Q') ≤ qpow q d := qpow_nonneg q hq0 d
      have hm := Q'.mul_le_mul_of_nonneg_left _ _ (qpow q d) hq hd0
      exact Q'.le_trans' _ _ _ (postBootstrap_one_le_qpow hq d)
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) hm)

private theorem qpow_exp_mono_of_one_le {q : Q'}
    (hq : (1 : Q') ≤ q) {a b : Nat} (hab : a ≤ b) :
    qpow q a ≤ qpow q b := by
  obtain ⟨d, hbd⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  subst b
  have hq0 : (0 : Q') ≤ q := Q'.le_trans' _ _ _ (by decide) hq
  have ha0 : (0 : Q') ≤ qpow q a := qpow_nonneg q hq0 a
  have hone : (1 : Q') ≤ qpow q d := postBootstrap_one_le_qpow hq d
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (qpow q a) hone ha0
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) hm)
    (Q'.le_of_eqv (Q'.eqv_symm (HeatKernelRGStep.qpow_add q a d)))

/-- The next-scale preload just below exponent `6j` is controlled by the same
`65/64` ceiling.  This is the exact power comparison needed by the secant
estimate, including the `j=0` truncated-exponent corner. -/
theorem lowerSixRecoveryNextPreloadPred_le_ceil
    {k c j : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hj : j < 2 * c) :
    qpow (harmW (k + 1)) (6 * j - 1) ≤
      lowerSixRecoveryDriftPowerCeil *
        qpow (harmW k) (6 * j - 1) := by
  let e := 6 * j - 1
  have hratio := lowerSixRecoveryDriftRatio_preload_le_ceil hk hcell hj
  have hmono : qpow (driftRatio k) e ≤ qpow (driftRatio k) (6 * j) :=
    qpow_exp_mono_of_one_le
      (HarmonicDriftAntisymmetry.one_le_driftRatio k)
      (by dsimp only [e]; omega)
  have hrceil : qpow (driftRatio k) e ≤
      lowerSixRecoveryDriftPowerCeil :=
    Q'.le_trans' _ _ _ hmono hratio
  have hold0 : (0 : Q') ≤ qpow (harmW k) e :=
    qpow_nonneg _ (harmW_nonneg k) _
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (qpow (harmW k) e) hrceil hold0
  have hstep := BondMovingRelResidual.qpow_eqv_congr_base
    (harmW_step_eqv k) e
  have hfactor := RefinedRetune.qpow_mul_base
    (harmW k) (driftRatio k) e
  have hnext : qpow (harmW (k + 1)) e ≈
      qpow (harmW k) e * qpow (driftRatio k) e :=
    Q'.eqv_trans _ _ _ hstep hfactor
  have hcomm : qpow (harmW k) e * lowerSixRecoveryDriftPowerCeil ≈
      lowerSixRecoveryDriftPowerCeil * qpow (harmW k) e :=
    Q'.mul_comm_eqv _ _
  dsimp only [e] at hnext hmul hcomm ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hnext)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hcomm))

/-! ## Homogeneous power secants -/

/-- Upper endpoint bound for the homogeneous divided-power chain. -/
private theorem homChain_le_length_mul_high
    {x y : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ m, homChain y x 0 m ≤ Q'.ofNat m * qpow y (m - 1)
  | 0 => by
      unfold homChain
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | 1 => by
      simp only [homChain, qpow]
      exact Q'.le_of_eqv (by post_bootstrap_ring)
  | m + 2 => by
      have hy0 : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx0 hxy
      have ih := homChain_le_length_mul_high hx0 hxy (m + 1)
      have ih' : homChain y x 0 (m + 1) ≤
          Q'.ofNat (m + 1) * qpow y m := by
        simpa only [Nat.add_sub_cancel] using ih
      have hxmul := Q'.mul_le_mul_of_nonneg_left _ _ x ih' hx0
      have hp0 : (0 : Q') ≤ Q'.ofNat (m + 1) * qpow y m :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
          (qpow_nonneg _ hy0 _)
      have hxyMul := Q'.mul_le_mul_of_nonneg_right _ _
        (Q'.ofNat (m + 1) * qpow y m) hxy hp0
      have htail : x * homChain y x 0 (m + 1) ≤
          Q'.ofNat (m + 1) * qpow y (m + 1) := by
        have htailEq :
            y * (Q'.ofNat (m + 1) * qpow y m) ≈
              Q'.ofNat (m + 1) * qpow y (m + 1) := by
          change y * (Q'.ofNat (m + 1) * qpow y m) ≈
            Q'.ofNat (m + 1) * (qpow y m * y)
          post_bootstrap_ring
        exact Q'.le_trans' _ _ _ hxmul
          (Q'.le_trans' _ _ _ hxyMul (Q'.le_of_eqv htailEq))
      have hadd := Q'.add_le_add_left (qpow y (m + 1)) _ _ htail
      unfold homChain
      rw [show m + 2 - 1 = m + 1 by omega]
      have hcast : Q'.ofNat (m + 2) ≈ Q'.ofNat (m + 1) + (1 : Q') := by
        exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (m + 1) 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide))
      have hsum : qpow y (m + 1) +
          Q'.ofNat (m + 1) * qpow y (m + 1) ≈
          Q'.ofNat (m + 2) * qpow y (m + 1) := by
        refine Q'.eqv_trans _
          ((Q'.ofNat (m + 1) + (1 : Q')) * qpow y (m + 1)) _ ?_ ?_
        · post_bootstrap_ring
        · exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hcast)
      have hhead : qpow y (0 + (m + 1)) * qpow x 0 ≈
          qpow y (m + 1) := by
        simp only [Nat.zero_add, RGTransport.qpow_zero]
        exact Q'.mul_one_eqv _
      have hnormalize :
          qpow y (0 + (m + 1)) * qpow x 0 +
              x * homChain y x 0 (m + 1) ≈
            qpow y (m + 1) + x * homChain y x 0 (m + 1) :=
        Q'.add_eqv_congr_right _ _ _ hhead
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hnormalize)
        (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hsum))

/-- Lower endpoint bound for the homogeneous divided-power chain. -/
private theorem length_mul_low_le_homChain
    {x y : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ m, Q'.ofNat m * qpow x (m - 1) ≤ homChain y x 0 m
  | 0 => by
      unfold homChain
      exact Q'.le_of_eqv (Q'.zero_mul_eqv _)
  | 1 => by
      simp only [homChain, qpow]
      exact Q'.le_of_eqv (by post_bootstrap_ring)
  | m + 2 => by
      have ih := length_mul_low_le_homChain hx0 hxy (m + 1)
      have ih' : Q'.ofNat (m + 1) * qpow x m ≤
          homChain y x 0 (m + 1) := by
        simpa only [Nat.add_sub_cancel] using ih
      have hxih := Q'.mul_le_mul_of_nonneg_left _ _ x ih' hx0
      have hbase := FusedAmplitudeDerivation.qpow_mono_base hx0 hxy (m + 1)
      have hsum := Q'.add_le_add hbase hxih
      unfold homChain
      rw [show m + 2 - 1 = m + 1 by omega]
      have hcast : Q'.ofNat (m + 2) ≈ Q'.ofNat (m + 1) + (1 : Q') := by
        exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (m + 1) 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide))
      have hleft : Q'.ofNat (m + 2) * qpow x (m + 1) ≈
          qpow x (m + 1) +
            x * (Q'.ofNat (m + 1) * qpow x m) := by
        refine Q'.eqv_trans _
          ((Q'.ofNat (m + 1) + (1 : Q')) * qpow x (m + 1)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _ hcast
        · change (Q'.ofNat (m + 1) + (1 : Q')) *
              (qpow x m * x) ≈
            qpow x m * x + x * (Q'.ofNat (m + 1) * qpow x m)
          post_bootstrap_ring
      have hhead : qpow y (0 + (m + 1)) * qpow x 0 ≈
          qpow y (m + 1) := by
        simp only [Nat.zero_add, RGTransport.qpow_zero]
        exact Q'.mul_one_eqv _
      have hnormalize :
          qpow y (0 + (m + 1)) * qpow x 0 +
              x * homChain y x 0 (m + 1) ≈
            qpow y (m + 1) + x * homChain y x 0 (m + 1) :=
        Q'.add_eqv_congr_right _ _ _ hhead
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hnormalize))

/-! ## The cubic recovery profile -/

/-- The lower-six recovery cubic after the exact substitution `u = 1-w`:
`(1+w)^3 - 6(1-w)^2 = w^3 - 3w^2 + 15w - 5`. -/
def lowerSixRecoveryCubicProfile (w : Q') : Q' :=
  (w * w * w + -(Q'.ofNat 3 * (w * w))) +
    (Q'.ofNat 15 * w + -(Q'.ofNat 5))

/-- Exact secant polynomial of the recovery cubic. -/
def lowerSixRecoveryCubicSecant (x y : Q') : Q' :=
  ((y * y + y * x) + x * x) +
    (Q'.ofNat 15 + -(Q'.ofNat 3 * (y + x)))

private def pRecoveryProfile (w : PostBootstrapPE) : PostBootstrapPE :=
  .add
    (.add (.mul (.mul w w) w)
      (.neg (.mul (.const 3) (.mul w w))))
    (.add (.mul (.const 15) w) (.neg (.const 5)))

private def pRecoverySecant (x y : PostBootstrapPE) : PostBootstrapPE :=
  .add
    (.add (.add (.mul y y) (.mul y x)) (.mul x x))
    (.add (.const 15) (.neg (.mul (.const 3) (.add y x))))

private def pRecoverySecantL : PostBootstrapPE :=
  .add (pRecoveryProfile (.var 1))
    (.neg (pRecoveryProfile (.var 0)))

private def pRecoverySecantR : PostBootstrapPE :=
  .mul (.add (.var 1) (.neg (.var 0)))
    (pRecoverySecant (.var 0) (.var 1))

private theorem pRecoverySecant_normal :
    RingNormaliser.normalize pRecoverySecantL =
      RingNormaliser.normalize pRecoverySecantR := by
  decide

private theorem lowerSixRecoveryCubicProfile_secant (x y : Q') :
    lowerSixRecoveryCubicProfile y +
        -lowerSixRecoveryCubicProfile x ≈
      (y + -x) * lowerSixRecoveryCubicSecant x y := by
  simpa [lowerSixRecoveryCubicProfile, lowerSixRecoveryCubicSecant,
    pRecoverySecantL, pRecoverySecantR, pRecoveryProfile,
    pRecoverySecant, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pRecoverySecantL pRecoverySecantR pRecoverySecant_normal
      (fun | 0 => x | _ => y))

private theorem lowerSixRecoveryCubicSecant_nonnegative
    {x y : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y)
    (hy1 : y ≤ (1 : Q')) :
    (0 : Q') ≤ lowerSixRecoveryCubicSecant x y := by
  have hy0 : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx0 hxy
  have hsum0 : (0 : Q') ≤ (y * y + y * x) + x * x :=
    Q'.zero_le_add _ _
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hy0 hy0)
        (Q'.mul_nonneg _ _ hy0 hx0))
      (Q'.mul_nonneg _ _ hx0 hx0)
  have hx1 : x ≤ (1 : Q') := Q'.le_trans' _ _ _ hxy hy1
  have hyx2 : y + x ≤ Q'.ofNat 2 := by
    have h := Q'.add_le_add hy1 hx1
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide))
  have hthree := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3)
    hyx2 (HeatKernelRGStep.zero_le_ofNat _)
  have hsix : Q'.ofNat 3 * (y + x) ≤ Q'.ofNat 6 :=
    Q'.le_trans' _ _ _ hthree (Q'.le_of_eqv (by decide))
  have hto15 : Q'.ofNat 3 * (y + x) ≤ Q'.ofNat 15 :=
    Q'.le_trans' _ _ _ hsix (by decide)
  have hpart : (0 : Q') ≤
      Q'.ofNat 15 + -(Q'.ofNat 3 * (y + x)) :=
    Q'.sub_nonneg_of_le hto15
  unfold lowerSixRecoveryCubicSecant
  exact Q'.zero_le_add _ _ hsum0 hpart

private theorem lowerSixRecoveryCubicSecant_le_eighteen
    {x y : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y)
    (hy1 : y ≤ (1 : Q')) :
    lowerSixRecoveryCubicSecant x y ≤ Q'.ofNat 18 := by
  have hy0 : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx0 hxy
  have hx1 : x ≤ (1 : Q') := Q'.le_trans' _ _ _ hxy hy1
  have hyy : y * y ≤ (1 : Q') * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg hy1 hy1 (by decide) hy0
  have hyx : y * x ≤ (1 : Q') * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg hy1 hx1 (by decide) hx0
  have hxx : x * x ≤ (1 : Q') * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg hx1 hx1 (by decide) hx0
  have hsquares := Q'.add_le_add (Q'.add_le_add hyy hyx) hxx
  have hsquares3 : (y * y + y * x) + x * x ≤ Q'.ofNat 3 :=
    Q'.le_trans' _ _ _ hsquares (Q'.le_of_eqv (by post_bootstrap_ring))
  have hyx0 : (0 : Q') ≤ y + x := Q'.zero_le_add _ _ hy0 hx0
  have hthree0 : (0 : Q') ≤ Q'.ofNat 3 * (y + x) :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) hyx0
  have hneg : -(Q'.ofNat 3 * (y + x)) ≤ (0 : Q') := by
    have h := Q'.neg_le_neg hthree0
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide))
  have hpart := Q'.add_le_add_left (Q'.ofNat 15) _ _ hneg
  have hpart15 : Q'.ofNat 15 + -(Q'.ofNat 3 * (y + x)) ≤
      Q'.ofNat 15 :=
    Q'.le_trans' _ _ _ hpart (Q'.le_of_eqv (QPoly.q_add_zero_eqv _))
  have hadd := Q'.add_le_add hsquares3 hpart15
  unfold lowerSixRecoveryCubicSecant
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (by decide))

private theorem lowerSixRecoveryCubicProfile_mono
    {x y : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y)
    (hy1 : y ≤ (1 : Q')) :
    lowerSixRecoveryCubicProfile x ≤ lowerSixRecoveryCubicProfile y := by
  have hdiff0 : (0 : Q') ≤
      lowerSixRecoveryCubicProfile y +
        -lowerSixRecoveryCubicProfile x := by
    have hsub0 : (0 : Q') ≤ y + -x := Q'.sub_nonneg_of_le hxy
    have hsec0 := lowerSixRecoveryCubicSecant_nonnegative
      (x := x) (y := y) hx0 hxy hy1
    have hprod := Q'.mul_nonneg _ _ hsub0 hsec0
    exact Q'.le_trans' _ _ _ hprod
      (Q'.le_of_eqv
        (Q'.eqv_symm (lowerSixRecoveryCubicProfile_secant x y)))
  exact Q'.le_of_sub_nonneg hdiff0

private theorem lowerSixRecoveryCubicProfile_le_eight
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    lowerSixRecoveryCubicProfile w ≤ Q'.ofNat 8 := by
  have hmono := lowerSixRecoveryCubicProfile_mono hw0 hw1
    (by decide : (1 : Q') ≤ (1 : Q'))
  have hone : lowerSixRecoveryCubicProfile (1 : Q') ≈ Q'.ofNat 8 := by
    unfold lowerSixRecoveryCubicProfile
    decide
  exact Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv hone)

private theorem lowerSixRecoveryCubicProfile_diff_le
    {x y : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y)
    (hy1 : y ≤ (1 : Q')) :
    lowerSixRecoveryCubicProfile y +
        -lowerSixRecoveryCubicProfile x ≤
      Q'.ofNat 18 * (y + -x) := by
  have hsub0 : (0 : Q') ≤ y + -x := Q'.sub_nonneg_of_le hxy
  have hsec := lowerSixRecoveryCubicSecant_le_eighteen hx0 hxy hy1
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (y + -x) hsec hsub0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (lowerSixRecoveryCubicProfile_secant x y))
    (Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

/-! ## Exact power and raw-slope secants -/

private theorem qpow_diff_eqv_homChain (x y : Q') (m : Nat) :
    qpow y m + -qpow x m ≈
      (y + -x) * homChain y x 0 m := by
  have hfactor := homChain_factor y x 0 m
  have hraw :
      qpow y (0 + m) * qpow x 0 +
          -(qpow y 0 * qpow x (0 + m)) ≈
        qpow y m + -qpow x m := by
    simp only [Nat.zero_add, RGTransport.qpow_zero]
    exact Q'.add_eqv_congr'
      (Q'.mul_one_eqv _) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hraw) (Q'.eqv_symm hfactor)

private theorem qpow_diff_le_upper_secant
    {x y : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y) (m : Nat) :
    qpow y m + -qpow x m ≤
      (y + -x) * (Q'.ofNat m * qpow y (m - 1)) := by
  have hsub0 : (0 : Q') ≤ y + -x := Q'.sub_nonneg_of_le hxy
  have hchain := homChain_le_length_mul_high hx0 hxy m
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (y + -x) hchain hsub0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (qpow_diff_eqv_homChain x y m)) hmul

private theorem lower_secant_floor_le_qpow_diff
    {x y floor : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y)
    (hx1 : x ≤ (1 : Q')) {m : Nat}
    (hfloor : floor ≤ qpow x m) :
    (y + -x) * (Q'.ofNat m * floor) ≤
      qpow y m + -qpow x m := by
  have hpred : qpow x m ≤ qpow x (m - 1) :=
    HeatKernelRGStep.qpow_antitone hx0 hx1 (m - 1) m (Nat.sub_le m 1)
  have hfloorPred : floor ≤ qpow x (m - 1) :=
    Q'.le_trans' _ _ _ hfloor hpred
  have hm0 : (0 : Q') ≤ Q'.ofNat m := HeatKernelRGStep.zero_le_ofNat _
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat m)
    hfloorPred hm0
  have hsub0 : (0 : Q') ≤ y + -x := Q'.sub_nonneg_of_le hxy
  have hscaled' := Q'.mul_le_mul_of_nonneg_left _ _ (y + -x)
    hscaled hsub0
  have hchain := length_mul_low_le_homChain hx0 hxy m
  have hchain' := Q'.mul_le_mul_of_nonneg_left _ _ (y + -x)
    hchain hsub0
  exact Q'.le_trans' _ _ _ hscaled'
    (Q'.le_trans' _ _ _ hchain'
      (Q'.le_of_eqv (Q'.eqv_symm (qpow_diff_eqv_homChain x y m))))

/-- Recovery slope written solely as a polynomial and one odd power of `w`. -/
def lowerSixRecoveryCubicSlope (w : Q') (n : Nat) : Q' :=
  Q'.ofNat n * lowerSixRecoveryCubicProfile w +
    -(Q'.ofNat 8 *
      (Q'.ofNat (n + 1) * qpow w (2 * n + 1)))

private def pModeSlopeExpanded : PostBootstrapPE :=
  let w := RingNormaliser.PolyExpr.var 0
  let n := RingNormaliser.PolyExpr.var 1
  let n1 := RingNormaliser.PolyExpr.var 2
  let t := RingNormaliser.PolyExpr.var 3
  let onePlusW : PostBootstrapPE := .add (.const 1) w
  let oneSubW : PostBootstrapPE := .add (.const 1) (.neg w)
  .add
    (.add
      (.mul n (.mul (.mul onePlusW onePlusW) onePlusW))
      (.neg (.mul (.const 8) (.mul n1 t))))
    (.neg (.mul (.mul (.const 6) (.mul oneSubW oneSubW)) n))

private def pModeSlopeCubic : PostBootstrapPE :=
  let w := RingNormaliser.PolyExpr.var 0
  let n := RingNormaliser.PolyExpr.var 1
  let n1 := RingNormaliser.PolyExpr.var 2
  let t := RingNormaliser.PolyExpr.var 3
  let profile : PostBootstrapPE :=
    .add
      (.add
        (.mul (.mul w w) w)
        (.neg (.mul (.const 3) (.mul w w))))
      (.add (.mul (.const 15) w) (.neg (.const 5)))
  .add (.mul n profile) (.neg (.mul (.const 8) (.mul n1 t)))

private theorem pModeSlope_normal :
    RingNormaliser.normalize pModeSlopeExpanded =
      RingNormaliser.normalize pModeSlopeCubic := by
  decide

private theorem mode_slope_cubic_algebra (w n n1 t : Q') :
    (n * (((1 : Q') + w) * ((1 : Q') + w) * ((1 : Q') + w)) +
        -(Q'.ofNat 8 * (n1 * t))) +
      -((Q'.ofNat 6 *
        (((1 : Q') + -w) * ((1 : Q') + -w))) * n) ≈
      n * ((w * w * w + -(Q'.ofNat 3 * (w * w))) +
        (Q'.ofNat 15 * w + -(Q'.ofNat 5))) +
        -(Q'.ofNat 8 * (n1 * t)) := by
  simpa [pModeSlopeExpanded, pModeSlopeCubic, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pModeSlopeExpanded pModeSlopeCubic pModeSlope_normal
      (fun | 0 => w | 1 => n | 2 => n1 | _ => t))

theorem lowerSixRecoveryModeSlope_eqv_cubicSlope (k n : Nat) :
    lowerSixRecoveryModeSlope k n ≈
      lowerSixRecoveryCubicSlope (harmW k) n := by
  have hu := Q'.eqv_symm (one_sub_harmW_eqv_harmU k)
  have hu2 : harmU k * harmU k ≈
      ((1 : Q') + -harmW k) * ((1 : Q') + -harmW k) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hu)
      (Q'.mul_eqv_congr_left _ _ _ hu)
  unfold lowerSixRecoveryModeSlope thetaResidualCellSlope
    lowerSixRecoveryCubicSlope lowerSixRecoveryCubicProfile
  refine Q'.eqv_trans _
    (Q'.ofNat n * qpow ((1 : Q') + harmW k) 3 +
        -(Q'.ofNat 8 *
          (Q'.ofNat (n + 1) * qpow (harmW k) (2 * n + 1))) +
      -(Q'.ofNat 6 *
        (((1 : Q') + -harmW k) * ((1 : Q') + -harmW k)) *
          Q'.ofNat n)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ (Q'.ofNat n)
          (Q'.mul_eqv_congr_left (Q'.ofNat 6) _ _ hu2)))
  · have hcube : qpow ((1 : Q') + harmW k) 3 ≈
        (((1 : Q') + harmW k) * ((1 : Q') + harmW k)) *
          ((1 : Q') + harmW k) := by
      change ((((1 : Q') * ((1 : Q') + harmW k)) *
        ((1 : Q') + harmW k)) * ((1 : Q') + harmW k)) ≈ _
      exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.one_mul_eqv ((1 : Q') + harmW k)))
    refine Q'.eqv_trans _
      (Q'.ofNat n *
          ((((1 : Q') + harmW k) * ((1 : Q') + harmW k)) *
            ((1 : Q') + harmW k)) +
        -(Q'.ofNat 8 *
          (Q'.ofNat (n + 1) * qpow (harmW k) (2 * n + 1))) +
        -((Q'.ofNat 6 *
          (((1 : Q') + -harmW k) * ((1 : Q') + -harmW k))) *
            Q'.ofNat n)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ hcube))
    · exact mode_slope_cubic_algebra (harmW k) (Q'.ofNat n)
        (Q'.ofNat (n + 1)) (qpow (harmW k) (2 * n + 1))

/-- Coefficient of the raw (un-preloaded) slope reserve. -/
def lowerSixRecoveryRawSlopeReserveCoeff (n : Nat) : Q' :=
  Q'.ofNat 8 * Q'.ofNat (n + 1) * Q'.ofNat (2 * n + 1) *
      lowerSixRecoveryPowerFloor +
    -(Q'.ofNat 18 * Q'.ofNat n)

/-- The old-minus-new raw cubic slope has a uniform secant reserve. -/
theorem lowerSixRecoveryCubicSlope_rawDrop_ge_reserve
    {x y : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y)
    (hy1 : y ≤ (1 : Q')) {n : Nat}
    (hfloor : lowerSixRecoveryPowerFloor ≤ qpow x (2 * n + 1)) :
    (y + -x) * lowerSixRecoveryRawSlopeReserveCoeff n ≤
      lowerSixRecoveryCubicSlope x n +
        -lowerSixRecoveryCubicSlope y n := by
  let b := 2 * n + 1
  let d := y + -x
  let Pdiff := lowerSixRecoveryCubicProfile y +
    -lowerSixRecoveryCubicProfile x
  let Wdiff := qpow y b + -qpow x b
  have hx1 : x ≤ (1 : Q') := Q'.le_trans' _ _ _ hxy hy1
  have hW := lower_secant_floor_le_qpow_diff hx0 hxy hx1 hfloor
  have hP := lowerSixRecoveryCubicProfile_diff_le hx0 hxy hy1
  have hWscale := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat 8 * Q'.ofNat (n + 1)) hW
    (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (HeatKernelRGStep.zero_le_ofNat _))
  have hPscale := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat n) hP (HeatKernelRGStep.zero_le_ofNat _)
  have hPneg := Q'.neg_le_neg hPscale
  have hadd := Q'.add_le_add hWscale hPneg
  unfold lowerSixRecoveryRawSlopeReserveCoeff
    lowerSixRecoveryCubicSlope
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by post_bootstrap_ring))
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (by post_bootstrap_ring)))

/-- Uniform ceiling for a positive next-scale cubic slope once the old odd
power floor is available. -/
def lowerSixRecoveryPositiveSlopeCeil (n : Nat) : Q' :=
  Q'.ofNat n * Q'.ofNat 8 +
    -(Q'.ofNat 8 *
      (Q'.ofNat (n + 1) * lowerSixRecoveryPowerFloor))

private theorem lowerSixRecoveryCubicSlope_le_positiveSlopeCeil
    {x y : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y)
    (hy1 : y ≤ (1 : Q')) {n : Nat}
    (hfloor : lowerSixRecoveryPowerFloor ≤ qpow x (2 * n + 1)) :
    lowerSixRecoveryCubicSlope y n ≤
      lowerSixRecoveryPositiveSlopeCeil n := by
  have hy0 : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx0 hxy
  have hprofile := lowerSixRecoveryCubicProfile_le_eight hy0 hy1
  have hn0 : (0 : Q') ≤ Q'.ofNat n :=
    HeatKernelRGStep.zero_le_ofNat _
  have hprofileScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat n) hprofile hn0
  have hpowMono := FusedAmplitudeDerivation.qpow_mono_base
    hx0 hxy (2 * n + 1)
  have hfloorY := Q'.le_trans' _ _ _ hfloor hpowMono
  have hn10 : (0 : Q') ≤ Q'.ofNat (n + 1) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hpowScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (n + 1)) hfloorY hn10
  have hpowScaled8 := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat 8) hpowScaled (HeatKernelRGStep.zero_le_ofNat _)
  have hneg := Q'.neg_le_neg hpowScaled8
  unfold lowerSixRecoveryCubicSlope lowerSixRecoveryPositiveSlopeCeil
  exact Q'.add_le_add hprofileScaled hneg

private def pPositiveSlopeRemainderL : PostBootstrapPE :=
  let A := RingNormaliser.PolyExpr.var 0
  let B := RingNormaliser.PolyExpr.var 1
  let N := RingNormaliser.PolyExpr.var 2
  .add (.mul B N)
    (.neg (.add (.mul N (.add A B))
      (.neg (.mul A (.add N (.const 1))))))

private def pPositiveSlopeRemainderR : PostBootstrapPE :=
  .var 0

private theorem pPositiveSlopeRemainder_normal :
    RingNormaliser.normalize pPositiveSlopeRemainderL =
      RingNormaliser.normalize pPositiveSlopeRemainderR := by
  decide

private theorem positive_slope_remainder_algebra (A B N : Q') :
    B * N + -(N * (A + B) + -(A * (N + (1 : Q')))) ≈ A := by
  simpa [pPositiveSlopeRemainderL, pPositiveSlopeRemainderR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pPositiveSlopeRemainderL pPositiveSlopeRemainderR
      pPositiveSlopeRemainder_normal
      (fun | 0 => A | 1 => B | _ => N))

private theorem lowerSixRecoveryPositiveSlopeCeil_le_nineFifths
    (n : Nat) :
    lowerSixRecoveryPositiveSlopeCeil n ≤
      nineFifths * Q'.ofNat n := by
  apply Q'.le_of_sub_nonneg
  let A := thirtyOneFifths
  let B := nineFifths
  let N := Q'.ofNat n
  have h8 : Q'.ofNat 8 ≈ A + B := by
    dsimp only [A, B]
    unfold thirtyOneFifths nineFifths
    decide
  have h8floor : Q'.ofNat 8 * lowerSixRecoveryPowerFloor ≈ A := by
    dsimp only [A]
    unfold lowerSixRecoveryPowerFloor thirtyOneFifths
    decide
  have hn1 : Q'.ofNat (n + 1) ≈ N + (1 : Q') := by
    dsimp only [N]
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hfirst : N * Q'.ofNat 8 ≈ N * (A + B) :=
    Q'.mul_eqv_congr_left N _ _ h8
  have hsecond0 : Q'.ofNat 8 *
      (Q'.ofNat (n + 1) * lowerSixRecoveryPowerFloor) ≈
      (Q'.ofNat 8 * lowerSixRecoveryPowerFloor) *
        Q'.ofNat (n + 1) := by
    post_bootstrap_ring
  have hsecond : Q'.ofNat 8 *
      (Q'.ofNat (n + 1) * lowerSixRecoveryPowerFloor) ≈
      A * (N + (1 : Q')) :=
    Q'.eqv_trans _ _ _ hsecond0
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ h8floor)
        (Q'.mul_eqv_congr_left A _ _ hn1))
  have hceil : lowerSixRecoveryPositiveSlopeCeil n ≈
      N * (A + B) + -(A * (N + (1 : Q'))) := by
    unfold lowerSixRecoveryPositiveSlopeCeil
    dsimp only [N]
    exact Q'.add_eqv_congr' hfirst
      (Q'.neg_eqv_congr _ _ hsecond)
  have hrem : B * N +
      -lowerSixRecoveryPositiveSlopeCeil n ≈ A :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (B * N) _ _
        (Q'.neg_eqv_congr _ _ hceil))
      (positive_slope_remainder_algebra A B N)
  dsimp only [A, B, N] at hrem ⊢
  exact Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ thirtyOneFifths)
    (Q'.ge_of_eqv hrem)

private def pRawReserveRemainderL : PostBootstrapPE :=
  let A := RingNormaliser.PolyExpr.var 0
  let N := RingNormaliser.PolyExpr.var 1
  let n1 := .add N (.const 1)
  let twoN1 := .add (.add N N) (.const 1)
  .add
    (.add (.mul (.mul A n1) twoN1)
      (.neg (.mul (.const 18) N)))
    (.neg (.mul (.mul (.add A A) N) N))

private def pRawReserveRemainderR : PostBootstrapPE :=
  let A := RingNormaliser.PolyExpr.var 0
  let N := RingNormaliser.PolyExpr.var 1
  .add (.mul (.add (.add (.add A A) A) (.neg (.const 18))) N) A

private theorem pRawReserveRemainder_normal :
    RingNormaliser.normalize pRawReserveRemainderL =
      RingNormaliser.normalize pRawReserveRemainderR := by
  decide

private theorem raw_reserve_remainder_algebra (A N : Q') :
    (A * (N + (1 : Q')) * ((N + N) + (1 : Q')) +
        -(Q'.ofNat 18 * N)) +
      -((A + A) * N * N) ≈
      (((A + A) + A) + -(Q'.ofNat 18)) * N + A := by
  simpa [pRawReserveRemainderL, pRawReserveRemainderR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pRawReserveRemainderL pRawReserveRemainderR
      pRawReserveRemainder_normal
      (fun | 0 => A | _ => N))

/-- The raw slope reserve contains a clean quadratic floor. -/
theorem lowerSixRecoveryRawSlopeReserveCoeff_ge_quadratic (n : Nat) :
    sixtyTwoFifths * Q'.ofNat n * Q'.ofNat n ≤
      lowerSixRecoveryRawSlopeReserveCoeff n := by
  apply Q'.le_of_sub_nonneg
  let A := thirtyOneFifths
  let N := Q'.ofNat n
  have h8floor : Q'.ofNat 8 * lowerSixRecoveryPowerFloor ≈ A := by
    dsimp only [A]
    unfold lowerSixRecoveryPowerFloor thirtyOneFifths
    decide
  have h62 : sixtyTwoFifths ≈ A + A := by
    dsimp only [A]
    unfold sixtyTwoFifths thirtyOneFifths
    decide
  have hn1 : Q'.ofNat (n + 1) ≈ N + (1 : Q') := by
    dsimp only [N]
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hn2nat : 2 * n + 1 = (n + n) + 1 := by omega
  have hn2 : Q'.ofNat (2 * n + 1) ≈ (N + N) + (1 : Q') := by
    rw [hn2nat]
    dsimp only [N]
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (n + n) 1)
      (Q'.add_eqv_congr'
        (Q'.ofNat_add_eqv n n) (by decide))
  have hfirst0 : Q'.ofNat 8 * Q'.ofNat (n + 1) *
      Q'.ofNat (2 * n + 1) * lowerSixRecoveryPowerFloor ≈
      (Q'.ofNat 8 * lowerSixRecoveryPowerFloor) *
        Q'.ofNat (n + 1) * Q'.ofNat (2 * n + 1) := by
    post_bootstrap_ring
  have hfirst : Q'.ofNat 8 * Q'.ofNat (n + 1) *
      Q'.ofNat (2 * n + 1) * lowerSixRecoveryPowerFloor ≈
      A * (N + (1 : Q')) * ((N + N) + (1 : Q')) :=
    Q'.eqv_trans _ _ _ hfirst0
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _ h8floor))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left A _ _ hn1))
          (Q'.mul_eqv_congr_left (A * (N + (1 : Q'))) _ _ hn2)))
  have hquad : sixtyTwoFifths * N * N ≈ (A + A) * N * N :=
    Q'.mul_eqv_congr_right _ _ N
      (Q'.mul_eqv_congr_right _ _ N h62)
  have hcanonical : lowerSixRecoveryRawSlopeReserveCoeff n +
        -(sixtyTwoFifths * N * N) ≈
      (A * (N + (1 : Q')) * ((N + N) + (1 : Q')) +
          -(Q'.ofNat 18 * N)) + -((A + A) * N * N) := by
    unfold lowerSixRecoveryRawSlopeReserveCoeff
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_right _ _ _ hfirst)
      (Q'.neg_eqv_congr _ _ hquad)
  have hrem := Q'.eqv_trans _ _ _ hcanonical
    (raw_reserve_remainder_algebra A N)
  have hcoef : (0 : Q') ≤
      ((A + A) + A) + -(Q'.ofNat 18) := by
    dsimp only [A]
    unfold thirtyOneFifths
    decide
  have hright : (0 : Q') ≤
      (((A + A) + A) + -(Q'.ofNat 18)) * N + A :=
    Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ hcoef
        (HeatKernelRGStep.zero_le_ofNat _))
      (by decide)
  dsimp only [A, N] at hright hrem ⊢
  exact Q'.le_trans' _ _ _ hright (Q'.ge_of_eqv hrem)

/-! ## Post-bootstrap spacing identities -/

private def pStepSubL : PostBootstrapPE :=
  let x := RingNormaliser.PolyExpr.var 0
  let u := RingNormaliser.PolyExpr.var 1
  .add (.mul x (.add (.const 1) u)) (.neg x)

private def pStepSubR : PostBootstrapPE :=
  .mul (.var 0) (.var 1)

private theorem pStepSub_normal :
    RingNormaliser.normalize pStepSubL =
      RingNormaliser.normalize pStepSubR := by
  decide

private theorem step_sub_algebra (x u : Q') :
    x * ((1 : Q') + u) + -x ≈ x * u := by
  simpa [pStepSubL, pStepSubR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pStepSubL pStepSubR pStepSub_normal
      (fun | 0 => x | _ => u))

/-- The old harmonic weight is uniformly bounded away from zero after the
finite bootstrap. -/
theorem lowerSixRecoveryHarmW_ge_floor {k : Nat} (hk : 648 ≤ k) :
    lowerSixRecoveryHarmWFloor ≤ harmW k := by
  have hu : harmU k ≤ oneSixtyFifth := by
    unfold harmU oneSixtyFifth
    exact unit_antitone (by decide) (by omega) (by omega)
  have hneg := Q'.neg_le_neg hu
  have hadd := Q'.add_le_add_left (1 : Q') _ _ hneg
  have hfloor : lowerSixRecoveryHarmWFloor ≈
      (1 : Q') + -oneSixtyFifth := by
    unfold lowerSixRecoveryHarmWFloor oneSixtyFifth
    decide
  unfold harmW ReciprocalBernoulliUpper.oneSub
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfloor) hadd

private theorem lowerSixRecovery_one_le_ceil_mul_harmW
    {k : Nat} (hk : 648 ≤ k) :
    (1 : Q') ≤ lowerSixRecoveryDriftPowerCeil * harmW k := by
  have hfloor := lowerSixRecoveryHarmW_ge_floor hk
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    lowerSixRecoveryDriftPowerCeil hfloor (by decide)
  have hunit : lowerSixRecoveryDriftPowerCeil *
      lowerSixRecoveryHarmWFloor ≈ (1 : Q') := by
    unfold lowerSixRecoveryDriftPowerCeil lowerSixRecoveryHarmWFloor
    decide
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hunit) hmul

/-- Exact adjacent-scale spacing in unit-denominator coordinates. -/
theorem lowerSixRecoveryHarmW_step_sub_eqv (k : Nat) :
    harmW (k + 1) + -harmW k ≈
      harmW k * unit (driftDen k) (driftDen_pos k) := by
  let u := unit (driftDen k) (driftDen_pos k)
  have hs := harmW_step_eqv k
  have hr := driftRatio_eqv_one_add_unitDen k
  refine Q'.eqv_trans _
    (harmW k * driftRatio k + -harmW k) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _ hs
  refine Q'.eqv_trans _
    (harmW k * ((1 : Q') + u) + -harmW k) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left (harmW k) _ _ hr)
  · dsimp only [u]
    exact step_sub_algebra _ _

/-- The reciprocal drift unit is at most the adjacent weight increment times
the reciprocal harmonic floor. -/
theorem lowerSixRecoveryUnit_le_ceil_mul_step
    {k : Nat} (hk : 648 ≤ k) :
    unit (driftDen k) (driftDen_pos k) ≤
      lowerSixRecoveryDriftPowerCeil *
        (harmW (k + 1) + -harmW k) := by
  let u := unit (driftDen k) (driftDen_pos k)
  let C := lowerSixRecoveryDriftPowerCeil
  let x := harmW k
  let d := harmW (k + 1) + -harmW k
  have hu0 : (0 : Q') ≤ u := unit_nonneg _ _
  have hone : (1 : Q') ≤ C * x := by
    dsimp only [C, x]
    exact lowerSixRecovery_one_le_ceil_mul_harmW hk
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ u hone hu0
  have hleft : u ≈ u * (1 : Q') := Q'.eqv_symm (Q'.mul_one_eqv u)
  have hright : u * (C * x) ≈ C * (x * u) := by
    post_bootstrap_ring
  have hstep : d ≈ x * u := by
    dsimp only [d, x, u]
    exact lowerSixRecoveryHarmW_step_sub_eqv k
  have hCstep : C * d ≈ C * (x * u) :=
    Q'.mul_eqv_congr_left C _ _ hstep
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hmul
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright)
        (Q'.ge_of_eqv hCstep)))

/-! ## Linear-preload payment -/

private theorem lowerSixRecoveryDebtConstant_le_reserve :
    Q'.ofNat 6 * lowerSixRecoveryDriftPowerCeil *
        lowerSixRecoveryDriftPowerCeil * nineFifths ≤
      sixtyTwoFifths := by
  unfold lowerSixRecoveryDriftPowerCeil nineFifths sixtyTwoFifths
  decide

private theorem lowerSixRecoveryPreloadDebtCoeff_le_quadratic (j : Nat) :
    Q'.ofNat (6 * j) * lowerSixRecoveryDriftPowerCeil *
        lowerSixRecoveryDriftPowerCeil *
        (nineFifths * Q'.ofNat (j + 1)) ≤
      sixtyTwoFifths * Q'.ofNat (j + 1) * Q'.ofNat (j + 1) := by
  let C := lowerSixRecoveryDriftPowerCeil
  let B := nineFifths
  let R := sixtyTwoFifths
  let N := Q'.ofNat (j + 1)
  have hexpNat : 6 * j ≤ 6 * (j + 1) := by omega
  have hexp0 : Q'.ofNat (6 * j) ≤ Q'.ofNat (6 * (j + 1)) :=
    CReal.ofNat_le_ofNat hexpNat
  have h6N : Q'.ofNat (6 * (j + 1)) ≈ Q'.ofNat 6 * N := by
    dsimp only [N]
    exact HeatKernelRGStep.ofNat_mul_eqv 6 (j + 1)
  have hexp : Q'.ofNat (6 * j) ≤ Q'.ofNat 6 * N :=
    Q'.le_trans' _ _ _ hexp0 (Q'.le_of_eqv h6N)
  have hC0 : (0 : Q') ≤ C := by dsimp only [C]; decide
  have hBN0 : (0 : Q') ≤ B * N :=
    Q'.mul_nonneg _ _ (by dsimp only [B]; decide)
      (HeatKernelRGStep.zero_le_ofNat _)
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ C hexp hC0
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _ C h1 hC0
  have h3 := Q'.mul_le_mul_of_nonneg_right _ _ (B * N) h2 hBN0
  have hregroup :
      (Q'.ofNat 6 * N) * C * C * (B * N) ≈
        (Q'.ofNat 6 * C * C * B) * (N * N) := by
    post_bootstrap_ring
  have hNN0 : (0 : Q') ≤ N * N :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (HeatKernelRGStep.zero_le_ofNat _)
  have hconst : Q'.ofNat 6 * C * C * B ≤ R := by
    dsimp only [C, B, R]
    exact lowerSixRecoveryDebtConstant_le_reserve
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ (N * N)
    hconst hNN0
  have hright : R * (N * N) ≈ R * N * N :=
    Q'.eqv_symm (Q'.mul_assoc_eqv R N N)
  dsimp only [C, B, R, N] at h3 hregroup hscaled hright ⊢
  exact Q'.le_trans' _ _ _ h3
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright)))

private theorem lowerSixRecoveryPositivePreloadDebt_le_quadratic
    {k c j : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hj : j < 2 * c)
    (hs0 : (0 : Q') ≤ lowerSixRecoveryCubicSlope (harmW (k + 1)) (j + 1))
    (hsCeil : lowerSixRecoveryCubicSlope (harmW (k + 1)) (j + 1) ≤
      lowerSixRecoveryPositiveSlopeCeil (j + 1)) :
    (qpow (driftRatio k) (6 * j) + -(1 : Q')) *
        lowerSixRecoveryCubicSlope (harmW (k + 1)) (j + 1) ≤
      (harmW (k + 1) + -harmW k) *
        (sixtyTwoFifths * Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) := by
  let A := Q'.ofNat (6 * j)
  let u := unit (driftDen k) (driftDen_pos k)
  let rp := qpow (driftRatio k) (6 * j)
  let C := lowerSixRecoveryDriftPowerCeil
  let d := harmW (k + 1) + -harmW k
  let S := lowerSixRecoveryCubicSlope (harmW (k + 1)) (j + 1)
  let U := nineFifths * Q'.ofNat (j + 1)
  let K := sixtyTwoFifths * Q'.ofNat (j + 1) * Q'.ofNat (j + 1)
  have hA0 : (0 : Q') ≤ A := HeatKernelRGStep.zero_le_ofNat _
  have hu0 : (0 : Q') ≤ u := unit_nonneg _ _
  have hrp0 : (0 : Q') ≤ rp := by
    dsimp only [rp]
    exact qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _
  have hC0 : (0 : Q') ≤ C := by dsimp only [C]; decide
  have hd0 : (0 : Q') ≤ d := by
    dsimp only [d]
    exact Q'.sub_nonneg_of_le
      (HarmonicDriftAntisymmetry.harmW_mono_step k)
  have hU0 : (0 : Q') ≤ U := by
    dsimp only [U]
    exact Q'.mul_nonneg _ _ (by decide)
      (HeatKernelRGStep.zero_le_ofNat _)
  have hinc : rp + -(1 : Q') ≤ A * u * rp := by
    dsimp only [rp, A, u]
    exact qpow_one_add_increment_le (unit_nonneg _ _)
      (driftRatio_eqv_one_add_unitDen k) (6 * j)
  have huStep : u ≤ C * d := by
    dsimp only [u, C, d]
    exact lowerSixRecoveryUnit_le_ceil_mul_step hk
  have hrpCeil : rp ≤ C := by
    dsimp only [rp, C]
    exact lowerSixRecoveryDriftRatio_preload_le_ceil hk hcell hj
  have hAu := Q'.mul_le_mul_of_nonneg_left _ _ A huStep hA0
  have hAuUpper0 : (0 : Q') ≤ A * (C * d) :=
    Q'.mul_nonneg _ _ hA0
      (Q'.mul_nonneg _ _ hC0 hd0)
  have hgrowth0 := Q'.mul_le_mul_of_nonneg hAu hrpCeil
    hAuUpper0 hrp0
  have hgrowthEq : (A * (C * d)) * C ≈ d * (A * C * C) := by
    post_bootstrap_ring
  have hgrowth : A * u * rp ≤ d * (A * C * C) :=
    Q'.le_trans' _ _ _ hgrowth0 (Q'.le_of_eqv hgrowthEq)
  have hgrowthUpper0 : (0 : Q') ≤ d * (A * C * C) :=
    Q'.mul_nonneg _ _ hd0
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ hA0 hC0) hC0)
  have hSU : S ≤ U :=
    Q'.le_trans' _ _ _ hsCeil
      (lowerSixRecoveryPositiveSlopeCeil_le_nineFifths (j + 1))
  have hincS := Q'.mul_le_mul_of_nonneg_right _ _ S hinc hs0
  have hdebtGrowth := Q'.mul_le_mul_of_nonneg hgrowth hSU
    hgrowthUpper0 hs0
  have hdebtEq : (d * (A * C * C)) * U ≈
      d * (A * C * C * U) := by
    post_bootstrap_ring
  have hcoeff : A * C * C * U ≤ K := by
    dsimp only [A, C, U, K]
    exact lowerSixRecoveryPreloadDebtCoeff_le_quadratic j
  have hcoeffScaled := Q'.mul_le_mul_of_nonneg_left _ _ d hcoeff hd0
  dsimp only [S, rp, d, K] at hincS ⊢
  exact Q'.le_trans' _ _ _ hincS
    (Q'.le_trans' _ _ _ hdebtGrowth
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hdebtEq) hcoeffScaled))

private def pPreloadPaymentL : PostBootstrapPE :=
  let X := RingNormaliser.PolyExpr.var 0
  let Y := RingNormaliser.PolyExpr.var 1
  let R := RingNormaliser.PolyExpr.var 2
  .add (.add X (.neg Y))
    (.neg (.mul (.add R (.neg (.const 1))) Y))

private def pPreloadPaymentR : PostBootstrapPE :=
  let X := RingNormaliser.PolyExpr.var 0
  let Y := RingNormaliser.PolyExpr.var 1
  let R := RingNormaliser.PolyExpr.var 2
  .add X (.neg (.mul R Y))

private theorem pPreloadPayment_normal :
    RingNormaliser.normalize pPreloadPaymentL =
      RingNormaliser.normalize pPreloadPaymentR := by
  decide

private theorem preload_payment_algebra (X Y R : Q') :
    (X + -Y) + -((R + -(1 : Q')) * Y) ≈
      X + -(R * Y) := by
  simpa [pPreloadPaymentL, pPreloadPaymentR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pPreloadPaymentL pPreloadPaymentR pPreloadPayment_normal
      (fun | 0 => X | 1 => Y | _ => R))

/-- Every physical post-bootstrap recovery mode has a nonnegative exact
linear-preload slope-drop carrier.  The proof splits on the sign of the
next-scale raw slope: a nonpositive slope is helped by preload growth, while a
nonnegative slope is paid by the quadratic secant reserve. -/
theorem lowerSixRecoveryLinearSlopeDropCarrier_nonnegative_postBootstrap
    {k c j : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hj : j < 2 * c) :
    (0 : Q') ≤ lowerSixRecoveryLinearSlopeDropCarrier k j := by
  let n := j + 1
  let x := harmW k
  let y := harmW (k + 1)
  let d := y + -x
  let rp := qpow (driftRatio k) (6 * j)
  let X := lowerSixRecoveryCubicSlope x n
  let Y := lowerSixRecoveryCubicSlope y n
  let K := sixtyTwoFifths * Q'.ofNat n * Q'.ofNat n
  have hx0 : (0 : Q') ≤ x := by dsimp only [x]; exact harmW_nonneg k
  have hxy : x ≤ y := by
    dsimp only [x, y]
    exact HarmonicDriftAntisymmetry.harmW_mono_step k
  have hy1 : y ≤ (1 : Q') := by dsimp only [y]; exact harmW_le_one _
  have hd0 : (0 : Q') ≤ d := Q'.sub_nonneg_of_le hxy
  have hfloor : lowerSixRecoveryPowerFloor ≤ qpow x (2 * n + 1) := by
    dsimp only [x, n]
    exact lowerSixRecoveryOldOddPower_ge_floor hk hcell hj
  have hraw : d * lowerSixRecoveryRawSlopeReserveCoeff n ≤
      X + -Y := by
    dsimp only [d, X, Y]
    exact lowerSixRecoveryCubicSlope_rawDrop_ge_reserve
      hx0 hxy hy1 hfloor
  have hcoeff := lowerSixRecoveryRawSlopeReserveCoeff_ge_quadratic n
  have hquadReserve := Q'.mul_le_mul_of_nonneg_left _ _ d hcoeff hd0
  have hquadRaw : d * K ≤ X + -Y := by
    dsimp only [K]
    exact Q'.le_trans' _ _ _ hquadReserve hraw
  have hK0 : (0 : Q') ≤ K := by
    dsimp only [K]
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide)
        (HeatKernelRGStep.zero_le_ofNat _))
      (HeatKernelRGStep.zero_le_ofNat _)
  have hraw0 : (0 : Q') ≤ X + -Y :=
    Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ hd0 hK0) hquadRaw
  have hcubic : (0 : Q') ≤ X + -(rp * Y) := by
    by_cases hYnonpos : Y ≤ (0 : Q')
    · let u := unit (driftDen k) (driftDen_pos k)
      have honeAdd : (1 : Q') ≤ (1 : Q') + u :=
        Q'.add_le_self_of_nonneg _ _ (unit_nonneg _ _)
      have hr : driftRatio k ≈ (1 : Q') + u := by
        dsimp only [u]
        exact driftRatio_eqv_one_add_unitDen k
      have honeRatio : (1 : Q') ≤ driftRatio k :=
        Q'.le_trans' _ _ _ honeAdd (Q'.ge_of_eqv hr)
      have honePow : (1 : Q') ≤ rp := by
        dsimp only [rp]
        exact postBootstrap_one_le_qpow honeRatio _
      have hmul : rp * Y ≤ (1 : Q') * Y :=
        IntervalArithmetic.mul_le_mul_of_nonpos_right
          (1 : Q') rp Y honePow hYnonpos
      have hneg := Q'.neg_le_neg hmul
      have hadd := Q'.add_le_add_left X _ _ hneg
      have honeEq : X + -((1 : Q') * Y) ≈ X + -Y :=
        Q'.add_eqv_congr_left X _ _
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv Y))
      exact Q'.le_trans' _ _ _ hraw0
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv honeEq) hadd)
    · have hYnonneg : (0 : Q') ≤ Y := Q'.le_of_not_le hYnonpos
      have hYceil : Y ≤ lowerSixRecoveryPositiveSlopeCeil n := by
        dsimp only [Y, y, x, n] at hYnonneg ⊢
        exact lowerSixRecoveryCubicSlope_le_positiveSlopeCeil
          hx0 hxy hy1 hfloor
      have hdebt : (rp + -(1 : Q')) * Y ≤ d * K := by
        dsimp only [rp, Y, d, K, n, y, x] at hYnonneg hYceil ⊢
        exact lowerSixRecoveryPositivePreloadDebt_le_quadratic
          hk hcell hj hYnonneg hYceil
      have hpay : (rp + -(1 : Q')) * Y ≤ X + -Y :=
        Q'.le_trans' _ _ _ hdebt hquadRaw
      have hsub : (0 : Q') ≤
          (X + -Y) + -((rp + -(1 : Q')) * Y) :=
        Q'.sub_nonneg_of_le hpay
      exact Q'.le_trans' _ _ _ hsub
        (Q'.le_of_eqv (preload_payment_algebra X Y rp))
  have hX := lowerSixRecoveryModeSlope_eqv_cubicSlope k n
  have hY := lowerSixRecoveryModeSlope_eqv_cubicSlope (k + 1) n
  have hcarrier : lowerSixRecoveryLinearSlopeDropCarrier k j ≈
      X + -(rp * Y) := by
    unfold lowerSixRecoveryLinearSlopeDropCarrier
    dsimp only [n, X, Y, x, y, rp]
    exact Q'.add_eqv_congr' hX
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hY))
  exact Q'.le_trans' _ _ _ hcubic (Q'.ge_of_eqv hcarrier)

/-- The exact preloaded recovery carrier drop is pointwise nonnegative on the
physical post-bootstrap block. -/
theorem lowerSixRecoveryLinearCarrierDrop_nonnegative_postBootstrap
    {k c j : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hj : j < 2 * c) :
    (0 : Q') ≤ lowerSixRecoveryLinearCarrierDrop k j :=
  lowerSixRecoveryLinearCarrierDrop_nonnegative_of_slopeCarrier
    (lowerSixRecoveryLinearSlopeDropCarrier_nonnegative_postBootstrap
      hk hcell hj)

/-- Consequently the complete favorable component of the exact linear-Abel
split is a genuine nonnegative reserve. -/
theorem lowerSixRecoveryLinearScaleReserve_nonnegative_postBootstrap
    {k c : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c) :
    (0 : Q') ≤ lowerSixRecoveryLinearScaleReserve k c :=
  lowerSixRecoveryLinearScaleReserve_nonnegative_of_carrierDrops
    (fun j hj =>
      lowerSixRecoveryLinearCarrierDrop_nonnegative_postBootstrap
        (j := j) hk hcell hj)

#print axioms lowerSixWithinCenterCell_center_ge_thirtySix
#print axioms lowerSixWithinCenterCell_oddExponent_budget
#print axioms lowerSixRecoveryOldOddPower_ge_floor
#print axioms lowerSixWithinCenterCell_preload_driftDen_budget
#print axioms lowerSixRecoveryDriftRatio_preload_le_ceil
#print axioms lowerSixRecoveryNextPreloadPred_le_ceil
#print axioms lowerSixRecoveryModeSlope_eqv_cubicSlope
#print axioms lowerSixRecoveryCubicSlope_rawDrop_ge_reserve
#print axioms lowerSixRecoveryRawSlopeReserveCoeff_ge_quadratic
#print axioms lowerSixRecoveryHarmW_ge_floor
#print axioms lowerSixRecoveryHarmW_step_sub_eqv
#print axioms lowerSixRecoveryUnit_le_ceil_mul_step
#print axioms lowerSixRecoveryPositivePreloadDebt_le_quadratic
#print axioms lowerSixRecoveryLinearSlopeDropCarrier_nonnegative_postBootstrap
#print axioms lowerSixRecoveryLinearCarrierDrop_nonnegative_postBootstrap
#print axioms lowerSixRecoveryLinearScaleReserve_nonnegative_postBootstrap

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPostBootstrap
