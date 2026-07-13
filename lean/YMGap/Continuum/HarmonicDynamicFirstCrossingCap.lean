/-
# Dynamic first-crossing control for the quadratic carrier

The fixed node-one reduction is false, and no fixed seed remains valid at all
scales.  This module instead uses the actual first-crossing hypotheses.  Its
first result bounds the terminal-gap overshoot at a nonzero crossing by the
single crossing coefficient.  The second part supplies an exact fence around
the next tempting fixed-seed claim.
-/

import YMGap.Continuum.HarmonicQuadraticBoundaryAll
import YMGap.Continuum.RDThetaCentered
import YMGap.Continuum.HarmonicSignedChordAbsorption

namespace YMGap.Continuum.HarmonicDynamicFirstCrossingCap

set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicQuadraticBoundaryAll
open YMGap.Continuum.HarmonicSignedChordAbsorption
open YMGap.Continuum.HarmonicThetaPascalClosure
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RDThetaCentered
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-- Terminal carrier gap at a chosen right endpoint. -/
def terminalGap (k L p : Nat) : Q' :=
  trapezoidNodeCumulative k L + -(trapezoidNodeCumulative k p)

private theorem gap_succ_algebra (x y q : Q') :
    x + (-(y + q)) ≈ (x + (-y)) + (-q) := by
  ring_qeqv

/-- Advancing the seed subtracts exactly the next node coefficient. -/
theorem terminalGap_succ_eqv (k L p : Nat) :
    terminalGap k L (p + 1) ≈
      terminalGap k L p + -(trapezoidNodeCoeff k (p + 1)) := by
  unfold terminalGap
  refine Q'.eqv_trans _
    (trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k p + trapezoidNodeCoeff k (p + 1))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (trapezoidNodeCumulative_succ_eq k p))
  · exact gap_succ_algebra _ _ _

/-- At a nonzero first terminal crossing the crossing coefficient is still
nonpositive.  This is the local sign information hidden by a fixed-seed
reduction. -/
theorem first_crossing_coeff_nonpos
    {k L s : Nat} (hs : 0 < s)
    (hfirst : ∀ p, p < s → terminalGap k L p ≤ (0 : Q'))
    (hboundary : (0 : Q') ≤ terminalGap k L s) :
    trapezoidNodeCoeff k s ≤ (0 : Q') := by
  let p := s - 1
  have hp : p < s := by unfold p; omega
  have hps : p + 1 = s := by unfold p; omega
  have hprev : terminalGap k L p ≤ (0 : Q') := hfirst p hp
  have hstep := terminalGap_succ_eqv k L p
  rw [hps] at hstep
  have hsub : (0 : Q') ≤
      terminalGap k L p + -(trapezoidNodeCoeff k s) :=
    Q'.le_trans' _ _ _ hboundary (Q'.le_of_eqv hstep)
  have hqprev : trapezoidNodeCoeff k s ≤ terminalGap k L p :=
    Q'.le_of_sub_nonneg hsub
  exact Q'.le_trans' _ _ _ hqprev hprev

/-- The amount by which a nonzero first crossing clears zero is no larger
than the magnitude of its (nonpositive) crossing coefficient. -/
theorem first_crossing_overshoot_le
    {k L s : Nat} (hs : 0 < s)
    (hfirst : ∀ p, p < s → terminalGap k L p ≤ (0 : Q'))
    (_hboundary : (0 : Q') ≤ terminalGap k L s) :
    terminalGap k L s ≤ -(trapezoidNodeCoeff k s) := by
  let p := s - 1
  have hp : p < s := by unfold p; omega
  have hps : p + 1 = s := by unfold p; omega
  have hprev : terminalGap k L p ≤ (0 : Q') := hfirst p hp
  have hstep := terminalGap_succ_eqv k L p
  rw [hps] at hstep
  have hadd := Q'.add_le_add_right _ _ (-(trapezoidNodeCoeff k s)) hprev
  have hzero : (0 : Q') + -(trapezoidNodeCoeff k s) ≈
      -(trapezoidNodeCoeff k s) := q_zero_add_eqv _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hstep)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hzero))

private theorem thetaTerm2_succ_eq_integerThetaTerm (w : Q') (j : Nat) :
    thetaTerm (w * w) 2 (j + 1) ≈ integerThetaTerm w (j + 1) := by
  unfold thetaTerm integerThetaTerm
  rw [Nat.pow_two]
  exact Q'.eqv_refl _

private theorem thetaCentered2_eq_integerPrefix (w : Q') : ∀ n : Nat,
    thetaCenteredSum (w * w) 2 n ≈
      RationalTail.finSum (fun j => integerThetaTerm w (j + 1)) n
  | 0 => by
      unfold thetaCenteredSum thetaTerm
      change (0 : Q') + Q'.ofNat 0 * qpow (w * w) 0 ≈ (0 : Q')
      refine Q'.eqv_trans _ (Q'.ofNat 0 * qpow (w * w) 0) _
        (q_zero_add_eqv _) ?_
      exact Q'.zero_mul_eqv _
  | n + 1 => by
      unfold thetaCenteredSum
      rw [show n + 1 + 1 = (n + 1) + 1 by omega]
      change RationalTail.finSum (thetaTerm (w * w) 2) (n + 1) +
          thetaTerm (w * w) 2 (n + 1) ≈
        RationalTail.finSum (fun j => integerThetaTerm w (j + 1)) n +
          integerThetaTerm w (n + 1)
      exact Q'.add_eqv_congr'
        (thetaCentered2_eq_integerPrefix w n)
        (thetaTerm2_succ_eq_integerThetaTerm w n)

private theorem thetaCentered2_le_integerTheta (w : Q')
    (hw0 : (0 : Q') ≤ w) (n : Nat) :
    thetaCenteredSum (w * w) 2 n ≤ integerThetaSum w n := by
  have hpre : RationalTail.finSum
      (fun j => integerThetaTerm w (j + 1)) n ≤
      RationalTail.finSum (fun j => integerThetaTerm w (j + 1)) (n + 1) :=
    RDThetaCentered.finSum_le_of_le (p := n) (n := n + 1) (by
      intro i
      unfold integerThetaTerm
      exact Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _)
        (qpow_nonneg _ (Q'.mul_nonneg _ _ hw0 hw0) _)) (by omega)
  unfold integerThetaSum
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (thetaCentered2_eq_integerPrefix w n)) hpre

private theorem square_harmW_le_one (k : Nat) :
    harmW k * harmW k ≤ (1 : Q') := by
  have hm := Q'.mul_le_mul_of_nonneg
    (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv 1))

/-- A comfortable exact scale at which the fixed node-two boundary is already
strictly false.  It is deliberately not claimed to be the first such scale. -/
def bigK : Nat := 999998

private theorem big_scale_floor_closed :
    Q'.ofNat 2 *
        (Q'.ofNat (450 * 450) *
          ((1 : Q') - harmW bigK * harmW bigK)) ≤
      (1 : Q') := by
  unfold bigK harmW harmU oneSub unit
  decide

private theorem d0_below_big_cutoff : 450 + 1 ≤ Ncut bigK + 1 := by
  unfold bigK Ncut
  decide

private theorem six_times_cube_constant :
    Q'.ofNat 6 * Q'.ofNat 15187500 ≈ Q'.ofNat (450 * 450 * 450) := by
  decide

private theorem D_lower_of_centered_cube (k d M : Nat)
    (hcut : d + 1 ≤ Ncut k + 1)
    (hfloor : ∀ i, i ≤ d →
      Q'.ofNat 2 *
        (Q'.ofNat (i * i) * ((1 : Q') - harmW k * harmW k)) ≤
          (1 : Q'))
    (hscale : Q'.ofNat 6 * Q'.ofNat M ≈ Q'.ofNat (d * d * d)) :
    Q'.ofNat M ≤ harmonicD k := by
  let w := harmW k
  let σ := w * w
  have hσ0 : (0 : Q') ≤ σ := by
    exact Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)
  have hσ1 : σ ≤ (1 : Q') := square_harmW_le_one k
  have hfloor' : ∀ i, i ≤ d →
      Q'.ofNat 2 * (Q'.ofNat (i * i) * ((1 : Q') - σ)) ≤ (1 : Q') := by
    intro i hi
    dsimp only [σ, w]
    exact hfloor i hi
  have hcube := thetaCentered2_ge_cube hσ0 hσ1 d hfloor'
  have htheta : thetaCenteredSum σ 2 d ≤ integerThetaSum w d := by
    dsimp only [σ]
    exact thetaCentered2_le_integerTheta w (harmW_nonneg k) d
  have h6theta := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 6) htheta (by decide)
  have hcoordEq := coordNormSq_theta_eqv w d
  have hwcoord : integerThetaSum w d ≤ coordNormSq w d := by
    have hcoord0 := coordNormSq_nonneg (harmW_nonneg k) d
    have hq1 : qpow w 2 ≤ (1 : Q') :=
      HeatKernelGap.qpow_le_one (harmW_nonneg k) (harmW_le_one k) 2
    have hm := Q'.mul_le_mul_of_nonneg_right _ _ (coordNormSq w d) hq1 hcoord0
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcoordEq)
      (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv _)))
  have h6coord := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 6) hwcoord (by decide)
  have hprefix : coordNormSq w d ≤ harmonicD k := by
    unfold harmonicD
    apply AFRateCalibration.fsum_le_of_le
    · intro i
      exact Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg k) i)
        (coeffW_nonneg (harmW_nonneg k) i)
    · exact hcut
  have h6D := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 6) hprefix (by decide)
  have hscaled : Q'.ofNat (d * d * d) ≤
      Q'.ofNat 6 * harmonicD k :=
    Q'.le_trans' _ _ _ hcube
      (Q'.le_trans' _ _ _ h6theta (Q'.le_trans' _ _ _ h6coord h6D))
  have hmul : Q'.ofNat 6 * Q'.ofNat M ≤
      Q'.ofNat 6 * harmonicD k :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hscale) hscaled
  exact Q'.le_of_mul_le_mul_left hmul (by decide)

private theorem D_bigScale_lower :
    Q'.ofNat 15187500 ≤ harmonicD bigK := by
  apply D_lower_of_centered_cube bigK 450 15187500
  · exact d0_below_big_cutoff
  · intro i hi
    have hii : i * i ≤ 450 * 450 := Nat.mul_le_mul hi hi
    have hnat : Q'.ofNat (i * i) ≤ Q'.ofNat (450 * 450) :=
      MovingCutoff.ofNat_le_ofNat' hii
    have hdelta0 : (0 : Q') ≤
        (1 : Q') - harmW bigK * harmW bigK :=
      Q'.sub_nonneg_of_le (square_harmW_le_one bigK)
    have hm := Q'.mul_le_mul_of_nonneg_right _ _
      ((1 : Q') - harmW bigK * harmW bigK) hnat hdelta0
    have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hm (by decide)
    exact Q'.le_trans' _ _ _ h2 big_scale_floor_closed
  · exact six_times_cube_constant

private def pairRateBig : Q' :=
  (retuneCube (harmW bigK) + twoInvSq bigK) +
    (retuneCube (harmW bigK) + twoInvSq bigK)

private def seedTwoDiagBig : Q' :=
  (oldDiag bigK 0 + oldDiag bigK 1) + oldDiag bigK 2

private def seedTwoEdgeBig : Q' :=
  ((oldAdj bigK 0 + oldAdj bigK 0) +
    (oldAdj bigK 1 + oldAdj bigK 1)) + oldAdj bigK 2

private def bracketBigTwo : Q' :=
  pairRateBig *
      (seedTwoDiagBig + invSqTerm 2 (by decide) bigK) +
    (-seedTwoEdgeBig) +
    -((twoInvSq bigK + twoInvSq bigK) * Q'.ofNat 15187500)

private theorem bracketBigTwo_neg : bracketBigTwo < (0 : Q') := by
  unfold bracketBigTwo pairRateBig seedTwoDiagBig seedTwoEdgeBig bigK
    retuneCube retuneBase twoInvSq invSqTerm oldAdj oldDiag harmW harmU
    oneSub unit coeffW dimQ c4 qpow
  decide

private def pairActualBig : Q' :=
  (harmonicA bigK + twoInvSq bigK * harmonicD bigK) +
    (harmonicA bigK + twoInvSq bigK * harmonicD bigK)

private theorem pair_collect (r lam D : Q') :
    (r * D + lam * D) + (r * D + lam * D) ≈
      ((r + lam) + (r + lam)) * D := by
  ring_qeqv

private theorem pair_upper {A D lam r : Q'} (hA : A ≤ r * D) :
    (A + lam * D) + (A + lam * D) ≤
      ((r + lam) + (r + lam)) * D := by
  have hs := Q'.add_le_add hA (Q'.le_refl' (lam * D))
  have ht := Q'.add_le_add hs hs
  exact Q'.le_trans' _ _ _ ht (Q'.le_of_eqv (pair_collect r lam D))

private theorem four_factor (B x y z t : Q') :
    ((B * x + B * y) + B * z) + B * t ≈
      B * (((x + y) + z) + t) := by
  ring_qeqv

private theorem slack_collect
    (D C S E lam d : Q') :
    ((C * D) * S + -(D * E)) + -((lam + lam) * (D * d)) ≈
      D * ((C * S + (-E)) + -((lam + lam) * d)) := by
  ring_qeqv

private theorem retuneCube_nonneg (w : Q') (hw0 : (0 : Q') ≤ w) :
    (0 : Q') ≤ retuneCube w := by
  unfold retuneCube retuneBase
  exact qpow_nonneg _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (by decide) hw0)) 3

private theorem twoInvSq_nonneg (k : Nat) :
    (0 : Q') ≤ twoInvSq k := by
  unfold twoInvSq
  exact Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) k)

private theorem pairRateBig_nonneg : (0 : Q') ≤ pairRateBig := by
  unfold pairRateBig
  have hr := retuneCube_nonneg (harmW bigK) (harmW_nonneg bigK)
  have hl := twoInvSq_nonneg bigK
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ hr hl) (Q'.zero_le_add _ _ hr hl)

private theorem seedTwoDiagBig_nonneg : (0 : Q') ≤ seedTwoDiagBig := by
  unfold seedTwoDiagBig oldDiag
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg bigK) 0)
        (coeffW_nonneg (harmW_nonneg bigK) 0))
      (Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg bigK) 1)
        (coeffW_nonneg (harmW_nonneg bigK) 1)))
    (Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg bigK) 2)
      (coeffW_nonneg (harmW_nonneg bigK) 2))

private theorem terminalDiagBig_upper :
    oldDiag bigK (Ncut bigK) ≤ invSqTerm 2 (by decide) bigK := by
  simpa only [oldDiag] using coeffW_Ncut_sq_le_invSq bigK

private theorem pairActualBig_upper :
    pairActualBig ≤ pairRateBig * harmonicD bigK := by
  have hA : harmonicA bigK ≤
      retuneCube (harmW bigK) * harmonicD bigK := by
    simpa only [harmonicA, harmonicD] using
      (harmonic_physical_cutoff_retune (k := bigK) (by unfold bigK; decide))
  unfold pairActualBig pairRateBig
  exact pair_upper hA

private theorem headSeedTwoBig_upper :
    ((pairActualBig * oldDiag bigK 0 + pairActualBig * oldDiag bigK 1) +
        pairActualBig * oldDiag bigK 2) +
        pairActualBig * oldDiag bigK (Ncut bigK) ≤
      (pairRateBig * harmonicD bigK) *
        (seedTwoDiagBig + invSqTerm 2 (by decide) bigK) := by
  have hsum0 : (0 : Q') ≤
      seedTwoDiagBig + oldDiag bigK (Ncut bigK) := by
    have ht0 : (0 : Q') ≤ oldDiag bigK (Ncut bigK) := by
      unfold oldDiag
      exact Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg bigK) (Ncut bigK))
        (coeffW_nonneg (harmW_nonneg bigK) (Ncut bigK))
    exact Q'.zero_le_add _ _ seedTwoDiagBig_nonneg ht0
  have hsum : seedTwoDiagBig + oldDiag bigK (Ncut bigK) ≤
      seedTwoDiagBig + invSqTerm 2 (by decide) bigK :=
    Q'.add_le_add_left seedTwoDiagBig _ _ terminalDiagBig_upper
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _
    (seedTwoDiagBig + oldDiag bigK (Ncut bigK))
    pairActualBig_upper hsum0
  have hCD0 : (0 : Q') ≤ pairRateBig * harmonicD bigK :=
    Q'.mul_nonneg _ _ pairRateBig_nonneg (Q'.le_of_lt (harmonicD_pos bigK))
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _
    (pairRateBig * harmonicD bigK) hsum hCD0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (four_factor pairActualBig
      (oldDiag bigK 0) (oldDiag bigK 1) (oldDiag bigK 2)
      (oldDiag bigK (Ncut bigK))))
    (Q'.le_trans' _ _ _ h1 h2)

private theorem edgeSeedTwoBig_drop :
    -(harmonicD bigK *
        (seedTwoEdgeBig + oldAdj bigK (Ncut bigK - 1))) ≤
      -(harmonicD bigK * seedTwoEdgeBig) := by
  have heL : (0 : Q') ≤ oldAdj bigK (Ncut bigK - 1) := by
    unfold oldAdj
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg bigK) _)
      (coeffW_nonneg (harmW_nonneg bigK) _)
  have he := Q'.add_le_self_of_nonneg seedTwoEdgeBig _ heL
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD bigK) he
    (Q'.le_of_lt (harmonicD_pos bigK))
  exact Q'.neg_le_neg hm

private theorem budgetBig_upper :
    -((twoInvSq bigK + twoInvSq bigK) *
        (harmonicD bigK * harmonicD bigK)) ≤
      -((twoInvSq bigK + twoInvSq bigK) *
        (harmonicD bigK * Q'.ofNat 15187500)) := by
  have hDD := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD bigK)
    D_bigScale_lower (Q'.le_of_lt (harmonicD_pos bigK))
  have hl : (0 : Q') ≤ twoInvSq bigK + twoInvSq bigK :=
    Q'.zero_le_add _ _ (twoInvSq_nonneg bigK) (twoInvSq_nonneg bigK)
  exact Q'.neg_le_neg
    (Q'.mul_le_mul_of_nonneg_left _ _
      (twoInvSq bigK + twoInvSq bigK) hDD hl)

private theorem carrier_node_two_slackBig_le :
    let N := Ncut bigK
    let L := N - 1
    let D := harmonicD bigK
    let A := harmonicA bigK
    let lam := twoInvSq bigK
    let B := (A + lam * D) + (A + lam * D)
    (((B * oldDiag bigK 0 + B * oldDiag bigK 1) +
        B * oldDiag bigK 2) + B * oldDiag bigK N) +
      -(D * ((((oldAdj bigK 0 + oldAdj bigK 0) +
        (oldAdj bigK 1 + oldAdj bigK 1)) + oldAdj bigK 2) +
          oldAdj bigK L)) +
      -((lam + lam) * (D * D)) ≤ D * bracketBigTwo := by
  dsimp only
  have hhead :
      ((((harmonicA bigK + twoInvSq bigK * harmonicD bigK) +
          (harmonicA bigK + twoInvSq bigK * harmonicD bigK)) * oldDiag bigK 0 +
        ((harmonicA bigK + twoInvSq bigK * harmonicD bigK) +
          (harmonicA bigK + twoInvSq bigK * harmonicD bigK)) * oldDiag bigK 1) +
        ((harmonicA bigK + twoInvSq bigK * harmonicD bigK) +
          (harmonicA bigK + twoInvSq bigK * harmonicD bigK)) * oldDiag bigK 2) +
        ((harmonicA bigK + twoInvSq bigK * harmonicD bigK) +
          (harmonicA bigK + twoInvSq bigK * harmonicD bigK)) *
            oldDiag bigK (Ncut bigK) ≤
      (pairRateBig * harmonicD bigK) *
        (seedTwoDiagBig + invSqTerm 2 (by decide) bigK) := by
    simpa only [pairActualBig] using headSeedTwoBig_upper
  have hedge :
      -(harmonicD bigK *
          (((((oldAdj bigK 0 + oldAdj bigK 0) +
            (oldAdj bigK 1 + oldAdj bigK 1)) + oldAdj bigK 2)) +
            oldAdj bigK (Ncut bigK - 1))) ≤
        -(harmonicD bigK * seedTwoEdgeBig) := by
    simpa only [seedTwoEdgeBig] using edgeSeedTwoBig_drop
  have hall := Q'.add_le_add (Q'.add_le_add hhead hedge) budgetBig_upper
  unfold bracketBigTwo
  exact Q'.le_trans' _ _ _ hall (Q'.le_of_eqv
    (slack_collect (harmonicD bigK) pairRateBig
      (seedTwoDiagBig + invSqTerm 2 (by decide) bigK)
      seedTwoEdgeBig (twoInvSq bigK) (Q'.ofNat 15187500)))

/-- The fixed seed `s = 2` already fails at an exact, finite harmonic scale.
This is a machine-checked fence against replacing the dynamic first crossing
by either of the first two fixed seeds. -/
theorem node_two_boundary_fails_bigK :
    ¬ ((0 : Q') ≤ terminalGap bigK (Ncut bigK - 1) 2) := by
  intro hgap
  have hid := carrier_node_two_gap_eq_slack bigK
  have hup : terminalGap bigK (Ncut bigK - 1) 2 ≤
      harmonicD bigK * bracketBigTwo := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
      unfold terminalGap
      exact hid)) carrier_node_two_slackBig_le
  have hneg : harmonicD bigK * bracketBigTwo < (0 : Q') := by
    have hm := Q'.mul_lt_mul_of_pos_left (harmonicD_pos bigK) bracketBigTwo_neg
    exact HeatKernelRGStep.lt_of_lt_of_le hm
      (Q'.le_of_eqv (Q'.mul_zero_eqv (harmonicD bigK)))
  exact ClusteringImpliesGap.lt_irrefl' (0 : Q') (Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _ hgap hup) hneg)

/-- The actual first crossing at the fence scale occurs strictly after node
two, and its sign and overshoot are controlled by its own coefficient.  This
is the dynamic replacement for the refuted fixed-seed premise. -/
theorem dynamic_first_crossing_beyond_two_bigK :
    ∃ s, s ≤ Ncut bigK - 1 ∧ 2 < s ∧
      (0 : Q') ≤ terminalGap bigK (Ncut bigK - 1) s ∧
      (∀ p, p < s → terminalGap bigK (Ncut bigK - 1) p ≤ (0 : Q')) ∧
      trapezoidNodeCoeff bigK s ≤ (0 : Q') ∧
      terminalGap bigK (Ncut bigK - 1) s ≤
        -(trapezoidNodeCoeff bigK s) := by
  let L := Ncut bigK - 1
  obtain ⟨s, hsL, hboundaryRaw, hfirstRaw⟩ :=
    exists_harmonic_terminal_carrier_crossing bigK L
  have hboundary : (0 : Q') ≤ terminalGap bigK L s := by
    simpa only [terminalGap] using hboundaryRaw
  have hfirst : ∀ p, p < s → terminalGap bigK L p ≤ (0 : Q') := by
    intro p hp
    simpa only [terminalGap] using hfirstRaw p hp
  have htwoL : 2 ≤ L := by
    dsimp only [L]
    unfold bigK Ncut
    decide
  have hnle : ¬ s ≤ 2 := by
    intro hs2
    have htwoRaw : (0 : Q') ≤
        trapezoidNodeCumulative bigK L +
          -(trapezoidNodeCumulative bigK 2) :=
      terminal_carrier_gap_nonneg_from_split bigK L s hsL hboundaryRaw hs2 htwoL
    have htwo : (0 : Q') ≤ terminalGap bigK L 2 := by
      simpa only [terminalGap] using htwoRaw
    apply node_two_boundary_fails_bigK
    simpa only [L] using htwo
  have hgt : 2 < s := by omega
  have hs0 : 0 < s := by omega
  have hcoeff := first_crossing_coeff_nonpos hs0 hfirst hboundary
  have hover := first_crossing_overshoot_le hs0 hfirst hboundary
  exact ⟨s, hsL, hgt, hboundary, hfirst, hcoeff, hover⟩

#print axioms terminalGap_succ_eqv
#print axioms first_crossing_coeff_nonpos
#print axioms first_crossing_overshoot_le
#print axioms D_bigScale_lower
#print axioms bracketBigTwo_neg
#print axioms node_two_boundary_fails_bigK
#print axioms dynamic_first_crossing_beyond_two_bigK

end YMGap.Continuum.HarmonicDynamicFirstCrossingCap
