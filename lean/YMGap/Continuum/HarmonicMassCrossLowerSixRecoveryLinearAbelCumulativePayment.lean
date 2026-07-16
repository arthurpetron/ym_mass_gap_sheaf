/-
# Cumulative payment coordinates after the linear preload

The post-bootstrap carrier drop is pointwise nonnegative, but the remaining
complementary-weight drift is not pointwise payable in the far suffix.  This
module puts that obstruction and the exact cumulative Abel normal form in the
kernel.  The analytic residual is thereby isolated as a two-sided estimate
for a one-crossing carrier against a unimodal scale increment, together with
the already explicit terminal mode.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPostBootstrap
import YMGap.Continuum.HarmonicWeightedAbelReserve

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPostBootstrap
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem cumulative_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "cumulative_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               cumulative_neg_num_cast, Q'.ofNat_num_cast,
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

/-! ## Exact adverse-drift normal form -/

/-- The positive scale increment of the complementary Gaussian weight. -/
def lowerSixRecoveryComplementScaleIncrement (k j : Nat) : Q' :=
  lowerSixRecoveryComplementWeight (k + 1) j +
    -lowerSixRecoveryComplementWeight k j

/-- The adverse complementary drift with its sign made explicit. -/
def lowerSixRecoveryLinearComplementDebt (k c : Nat) : Q' :=
  finSum (fun j =>
    lowerSixRecoveryLinearCarrier (k + 1) j *
      lowerSixRecoveryComplementScaleIncrement k j) (2 * c)

/-- Prefix of the next-scale one-crossing carrier. -/
def lowerSixRecoveryNextCarrierPrefix (k p : Nat) : Q' :=
  finSum (fun j => lowerSixRecoveryLinearCarrier (k + 1) j) (p + 1)

theorem lowerSixRecoveryComplementScaleIncrement_eqv_neg_drop (k j : Nat) :
    lowerSixRecoveryComplementScaleIncrement k j ≈
      -lowerSixRecoveryComplementWeightDrop k j := by
  unfold lowerSixRecoveryComplementScaleIncrement
    lowerSixRecoveryComplementWeightDrop
  cumulative_ring

theorem lowerSixRecoveryComplementScaleIncrement_nonnegative (k j : Nat) :
    (0 : Q') ≤ lowerSixRecoveryComplementScaleIncrement k j := by
  unfold lowerSixRecoveryComplementScaleIncrement
  exact Q'.sub_nonneg_of_le
    (lowerSixRecoveryComplementWeight_scale_mono k j)

private theorem complementDebt_sum_eqv_neg_driftSum (k c : Nat) :
    lowerSixRecoveryLinearComplementDebt k c ≈
      -finSum (fun j =>
        lowerSixRecoveryLinearCarrier (k + 1) j *
          lowerSixRecoveryComplementWeightDrop k j) (2 * c) := by
  have hterms := RationalTail.finSum_eqv_congr
    (fun j =>
      lowerSixRecoveryLinearCarrier (k + 1) j *
        lowerSixRecoveryComplementScaleIncrement k j)
    (fun j =>
      -(lowerSixRecoveryLinearCarrier (k + 1) j *
        lowerSixRecoveryComplementWeightDrop k j))
    (fun j => by
      refine Q'.eqv_trans _
        (lowerSixRecoveryLinearCarrier (k + 1) j *
          (-lowerSixRecoveryComplementWeightDrop k j)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (lowerSixRecoveryComplementScaleIncrement_eqv_neg_drop k j)
      · exact Q'.mul_neg_eqv _ _)
    (2 * c)
  have hneg := YMGap.Constructive.neg_finSum
    (fun j =>
      lowerSixRecoveryLinearCarrier (k + 1) j *
        lowerSixRecoveryComplementWeightDrop k j) (2 * c)
  unfold lowerSixRecoveryLinearComplementDebt
  exact Q'.eqv_trans _ _ _ hterms (Q'.eqv_symm hneg)

/-- Exact payment normal form: the negated linear drift debt is the positive
complement-scale increment paired with the next carrier, plus the negated
terminal drop. -/
theorem neg_lowerSixRecoveryLinearDriftDebt_eqv_complementDebt_sub_terminal
    (k c : Nat) :
    -lowerSixRecoveryLinearDriftDebt k c ≈
      lowerSixRecoveryLinearComplementDebt k c +
        -lowerSixRecoveryTerminalDrop k (2 * c) := by
  let S := finSum (fun j =>
    lowerSixRecoveryLinearCarrier (k + 1) j *
      lowerSixRecoveryComplementWeightDrop k j) (2 * c)
  let T := lowerSixRecoveryTerminalDrop k (2 * c)
  let A := lowerSixRecoveryLinearComplementDebt k c
  have hA : A ≈ -S := by
    dsimp only [A, S]
    exact complementDebt_sum_eqv_neg_driftSum k c
  unfold lowerSixRecoveryLinearDriftDebt
  dsimp only [S, T, A] at hA ⊢
  refine Q'.eqv_trans _ (-S + -T) _ ?_ ?_
  · exact Q'.neg_add_eqv S T
  · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hA)

/-- The original payment goal can be transported without loss to the adverse
increment normal form. -/
theorem lowerSixRecoveryLinearPayment_of_complementPayment
    {k c : Nat}
    (hpay : lowerSixRecoveryLinearComplementDebt k c +
        -lowerSixRecoveryTerminalDrop k (2 * c) ≤
      lowerSixRecoveryLinearScaleReserve k c) :
    -lowerSixRecoveryLinearDriftDebt k c ≤
      lowerSixRecoveryLinearScaleReserve k c := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (neg_lowerSixRecoveryLinearDriftDebt_eqv_complementDebt_sub_terminal
        k c)) hpay

/-! ## Generic finite Abel split -/

/-- Finite summation by parts in the `finSum` coordinate used by the recovery
development.  No order assumptions are hidden in the identity. -/
theorem finSum_mul_eqv_prefix_terminal_add_variation
    (a x : Nat → Q') (n : Nat) :
    finSum (fun j => a j * x j) (n + 1) ≈
      finSum a (n + 1) * x n +
        finSum (fun p =>
          finSum a (p + 1) * (x p + -x (p + 1))) n := by
  have h := HarmonicDriftAntisymmetry.finite_abel a x n
  unfold HarmonicDriftAntisymmetry.abelPrefix
    HarmonicDriftAntisymmetry.abelIncrementSum at h
  simp only [HarmonicDriftAntisymmetry.abelPrefix,
    MovingCutoff.fsum_eq_finSum] at h
  exact h

/-- Concrete Abel split of the adverse complementary debt.  Its variation
term is now controlled by carrier prefixes and successive changes of the
positive scale increment; this is the exact two-sided object required by the
unimodality argument. -/
theorem lowerSixRecoveryLinearComplementDebt_eqv_abel
    {k c : Nat} (hc : 1 ≤ c) :
    lowerSixRecoveryLinearComplementDebt k c ≈
      lowerSixRecoveryNextCarrierPrefix k (2 * c - 1) *
          lowerSixRecoveryComplementScaleIncrement k (2 * c - 1) +
        finSum (fun p =>
          lowerSixRecoveryNextCarrierPrefix k p *
            (lowerSixRecoveryComplementScaleIncrement k p +
              -lowerSixRecoveryComplementScaleIncrement k (p + 1)))
          (2 * c - 1) := by
  have hpos : 0 < 2 * c := by omega
  have hshape : 2 * c = (2 * c - 1) + 1 := by omega
  unfold lowerSixRecoveryLinearComplementDebt
    lowerSixRecoveryNextCarrierPrefix
  rw [hshape]
  exact finSum_mul_eqv_prefix_terminal_add_variation
    (fun j => lowerSixRecoveryLinearCarrier (k + 1) j)
    (fun j => lowerSixRecoveryComplementScaleIncrement k j)
    (2 * c - 1)

/-! ## Exact scale-increment transition -/

/-- Power flux whose old/new comparison gives the successive change of the
complementary scale increment. -/
def lowerSixRecoveryComplementPeakFlux (w : Q') (j : Nat) : Q' :=
  let e := 2 * j * (j - 1) + 2
  qpow w e * ((1 : Q') + -qpow w (4 * j))

/-- Successive complementary exponents differ by exactly `4j`. -/
theorem lowerSixRecoveryComplementExponent_succ (j : Nat) :
    2 * (j + 1) * ((j + 1) - 1) + 2 =
      (2 * j * (j - 1) + 2) + 4 * j := by
  cases j with
  | zero => decide
  | succ j =>
      simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add,
        Nat.mul_one]
      omega

/-- Exact flux identity locating the peak of the drift increment.  Before
the peak the new-weight flux is below the old-weight flux; after it, the
inequality reverses. -/
theorem lowerSixRecoveryComplementScaleIncrement_succ_sub_eqv_fluxDrop
    (k j : Nat) :
    lowerSixRecoveryComplementScaleIncrement k (j + 1) +
        -lowerSixRecoveryComplementScaleIncrement k j ≈
      lowerSixRecoveryComplementPeakFlux (harmW k) j +
        -lowerSixRecoveryComplementPeakFlux (harmW (k + 1)) j := by
  let e := 2 * j * (j - 1) + 2
  let q := 4 * j
  have heq : 2 * (j + 1) * ((j + 1) - 1) + 2 = e + q := by
    dsimp only [e, q]
    exact lowerSixRecoveryComplementExponent_succ j
  have hold := HeatKernelRGStep.qpow_add (harmW k) e q
  have hnew := HeatKernelRGStep.qpow_add (harmW (k + 1)) e q
  unfold lowerSixRecoveryComplementScaleIncrement
    lowerSixRecoveryComplementWeight
    lowerSixRecoveryComplementPeakFlux
  rw [heq]
  change
    (qpow (harmW (k + 1)) (e + q) +
        -qpow (harmW k) (e + q)) +
      -(qpow (harmW (k + 1)) e + -qpow (harmW k) e) ≈
    qpow (harmW k) e * ((1 : Q') + -qpow (harmW k) q) +
      -(qpow (harmW (k + 1)) e *
        ((1 : Q') + -qpow (harmW (k + 1)) q))
  refine Q'.eqv_trans _
    ((qpow (harmW (k + 1)) e * qpow (harmW (k + 1)) q +
        -(qpow (harmW k) e * qpow (harmW k) q)) +
      -(qpow (harmW (k + 1)) e + -qpow (harmW k) e)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr'
        hnew
        (Q'.neg_eqv_congr _ _ hold))
  · cumulative_ring

/-- If the flux grows across the harmonic step, the complementary increment
has entered its decreasing side. -/
theorem lowerSixRecoveryComplementScaleIncrement_succ_le_of_flux_mono
    {k j : Nat}
    (hflux : lowerSixRecoveryComplementPeakFlux (harmW k) j ≤
      lowerSixRecoveryComplementPeakFlux (harmW (k + 1)) j) :
    lowerSixRecoveryComplementScaleIncrement k (j + 1) ≤
      lowerSixRecoveryComplementScaleIncrement k j := by
  have hnonneg := Q'.sub_nonneg_of_le hflux
  have hreverse :
      lowerSixRecoveryComplementScaleIncrement k j +
          -lowerSixRecoveryComplementScaleIncrement k (j + 1) ≈
        lowerSixRecoveryComplementPeakFlux (harmW (k + 1)) j +
          -lowerSixRecoveryComplementPeakFlux (harmW k) j := by
    have h := lowerSixRecoveryComplementScaleIncrement_succ_sub_eqv_fluxDrop
      k j
    have hn := Q'.neg_eqv_congr _ _ h
    refine Q'.eqv_trans _
      (-(lowerSixRecoveryComplementScaleIncrement k (j + 1) +
        -lowerSixRecoveryComplementScaleIncrement k j)) _ ?_ ?_
    · cumulative_ring
    refine Q'.eqv_trans _
      (-(lowerSixRecoveryComplementPeakFlux (harmW k) j +
        -lowerSixRecoveryComplementPeakFlux (harmW (k + 1)) j)) _ hn ?_
    cumulative_ring
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hnonneg (Q'.ge_of_eqv hreverse))

/-- If the flux decreases across the harmonic step, the complementary
increment is still on its increasing side. -/
theorem lowerSixRecoveryComplementScaleIncrement_le_succ_of_flux_antitone
    {k j : Nat}
    (hflux : lowerSixRecoveryComplementPeakFlux (harmW (k + 1)) j ≤
      lowerSixRecoveryComplementPeakFlux (harmW k) j) :
    lowerSixRecoveryComplementScaleIncrement k j ≤
      lowerSixRecoveryComplementScaleIncrement k (j + 1) := by
  have hnonneg := Q'.sub_nonneg_of_le hflux
  have h := lowerSixRecoveryComplementScaleIncrement_succ_sub_eqv_fluxDrop
    k j
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hnonneg (Q'.ge_of_eqv h))

/-! ## Kernel fence around the false pointwise payment -/

/-- In the first physical post-bootstrap cell (`D=650,c=36`), mode `j=25`
is the first far-suffix mode where the favorable carrier reserve does not pay
the adverse complementary drift pointwise.  Cumulative compensation and the
terminal boundary are therefore logically indispensable. -/
theorem lowerSixRecoveryPointwiseComplementPayment_648_25_fails :
    not (
      -(lowerSixRecoveryLinearCarrier (648 + 1) 25 *
          lowerSixRecoveryComplementWeightDrop 648 25) ≤
        lowerSixRecoveryLinearCarrierDrop 648 25 *
          lowerSixRecoveryComplementWeight 648 25) := by
  unfold lowerSixRecoveryLinearCarrierDrop
    lowerSixRecoveryLinearCarrier
    lowerSixRecoveryComplementWeightDrop
    lowerSixRecoveryComplementWeight
    lowerSixRecoveryModeSlope
    thetaResidualCellSlope
    harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit qpow
  decide

#print axioms lowerSixRecoveryComplementScaleIncrement_eqv_neg_drop
#print axioms lowerSixRecoveryComplementScaleIncrement_nonnegative
#print axioms neg_lowerSixRecoveryLinearDriftDebt_eqv_complementDebt_sub_terminal
#print axioms lowerSixRecoveryLinearPayment_of_complementPayment
#print axioms finSum_mul_eqv_prefix_terminal_add_variation
#print axioms lowerSixRecoveryLinearComplementDebt_eqv_abel
#print axioms lowerSixRecoveryComplementExponent_succ
#print axioms lowerSixRecoveryComplementScaleIncrement_succ_sub_eqv_fluxDrop
#print axioms lowerSixRecoveryComplementScaleIncrement_succ_le_of_flux_mono
#print axioms lowerSixRecoveryComplementScaleIncrement_le_succ_of_flux_antitone
#print axioms lowerSixRecoveryPointwiseComplementPayment_648_25_fails

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment
