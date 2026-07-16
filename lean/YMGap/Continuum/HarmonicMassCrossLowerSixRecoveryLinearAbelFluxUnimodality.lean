/-
# Unimodality of the complementary scale increment

The cumulative linear-Abel payment pairs a one-crossing carrier with the
positive difference of two adjacent harmonic powers.  This file proves the
exact location structure needed for the two-sided Abel split: the elementary
power difference `y^m-x^m` has persistent descent, and therefore so does its
strictly increasing quadratic-exponent subsequence used by the complementary
weight.  No numerical peak location or transcendental estimate is used.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxUnimodality

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem flux_unimodal_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "flux_unimodal_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               flux_unimodal_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-! ## Generic persistent-descent algebra -/

private theorem exists_local_descent_aux (A : Nat → Q') (a : Nat) :
    ∀ d,
      A (a + (d + 1)) ≤ A a →
      ∃ m, a ≤ m ∧ m < a + (d + 1) ∧ A (m + 1) ≤ A m
  | 0, h => ⟨a, Nat.le_refl a, by omega, by simpa using h⟩
  | d + 1, h => by
      by_cases hfirst : A (a + 1) ≤ A a
      · exact ⟨a, Nat.le_refl a, by omega, hfirst⟩
      · have hforward : A a ≤ A (a + 1) := Q'.le_of_not_le hfirst
        have htail : A ((a + 1) + (d + 1)) ≤ A (a + 1) := by
          rw [show (a + 1) + (d + 1) = a + (d + 1 + 1) by omega]
          exact Q'.le_trans' _ _ _ h hforward
        obtain ⟨m, ham, hmb, hm⟩ :=
          exists_local_descent_aux A (a + 1) d htail
        exact ⟨m, by omega, by omega, hm⟩

private theorem exists_local_descent_between
    (A : Nat → Q') {a b : Nat} (hab : a < b)
    (hend : A b ≤ A a) :
    ∃ m, a ≤ m ∧ m < b ∧ A (m + 1) ≤ A m := by
  let d := b - a - 1
  have hshape : b = a + (d + 1) := by
    dsimp only [d]
    omega
  rw [hshape] at hend ⊢
  exact exists_local_descent_aux A a d hend

private theorem local_descent_propagates
    (A : Nat → Q')
    (hpersist : ∀ m, A (m + 1) ≤ A m → A (m + 2) ≤ A (m + 1))
    {m n : Nat} (hm : A (m + 1) ≤ A m) (hmn : m ≤ n) :
    A (n + 1) ≤ A n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction d with
  | zero => simpa using hm
  | succ d ih =>
      rw [show m + (d + 1) + 1 = (m + d) + 2 by omega,
        show m + (d + 1) = (m + d) + 1 by omega]
      exact hpersist (m + d) (ih (by omega))

private theorem value_antitone_after_local_descent
    (A : Nat → Q')
    (hpersist : ∀ m, A (m + 1) ≤ A m → A (m + 2) ≤ A (m + 1))
    {m a b : Nat} (hm : A (m + 1) ≤ A m)
    (hma : m ≤ a) (hab : a ≤ b) :
    A b ≤ A a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      have hlast : A (a + d + 1) ≤ A (a + d) :=
        local_descent_propagates A hpersist hm (by omega)
      exact Q'.le_trans' _ _ _ hlast (ih (by omega))

/-- A persistent local descent remains persistent after restriction to any
strictly increasing subsequence. -/
theorem descent_persists_on_strict_subsequence
    (A : Nat → Q') (f : Nat → Nat)
    (hpersist : ∀ m, A (m + 1) ≤ A m → A (m + 2) ≤ A (m + 1))
    {j : Nat} (hfj : f j < f (j + 1))
    (hfj1 : f (j + 1) < f (j + 2))
    (hdesc : A (f (j + 1)) ≤ A (f j)) :
    A (f (j + 2)) ≤ A (f (j + 1)) := by
  obtain ⟨m, _, hmright, hm⟩ :=
    exists_local_descent_between A hfj hdesc
  exact value_antitone_after_local_descent A hpersist hm
    (by omega) (by exact Nat.le_of_lt hfj1)

/-! ## Adjacent-power scale increments -/

/-- Difference of the same power at two ordered bases. -/
def lowerSixRecoveryPowerScaleIncrement (x y : Q') (m : Nat) : Q' :=
  qpow y m + -qpow x m

/-- Flux governing the change from power `m` to power `m+1`. -/
def lowerSixRecoveryPowerStepFlux (w : Q') (m : Nat) : Q' :=
  qpow w m * ((1 : Q') + -w)

theorem lowerSixRecoveryPowerScaleIncrement_step_sub_eqv_fluxDrop
    (x y : Q') (m : Nat) :
    lowerSixRecoveryPowerScaleIncrement x y (m + 1) +
        -lowerSixRecoveryPowerScaleIncrement x y m ≈
      lowerSixRecoveryPowerStepFlux x m +
        -lowerSixRecoveryPowerStepFlux y m := by
  unfold lowerSixRecoveryPowerScaleIncrement
    lowerSixRecoveryPowerStepFlux
  change
    ((qpow y m * y + -(qpow x m * x)) +
      -(qpow y m + -qpow x m)) ≈
    qpow x m * ((1 : Q') + -x) +
      -(qpow y m * ((1 : Q') + -y))
  flux_unimodal_ring

theorem lowerSixRecoveryPowerStepFlux_succ_factor (w : Q') (m : Nat) :
    lowerSixRecoveryPowerStepFlux w (m + 1) ≈
      w * lowerSixRecoveryPowerStepFlux w m := by
  unfold lowerSixRecoveryPowerStepFlux
  change (qpow w m * w) * ((1 : Q') + -w) ≈
    w * (qpow w m * ((1 : Q') + -w))
  flux_unimodal_ring

theorem lowerSixRecoveryPowerStepFlux_nonnegative
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (m : Nat) :
    (0 : Q') ≤ lowerSixRecoveryPowerStepFlux w m := by
  unfold lowerSixRecoveryPowerStepFlux
  exact Q'.mul_nonneg _ _ (qpow_nonneg w hw0 m)
    (Q'.sub_nonneg_of_le hw1)

private theorem powerScaleIncrement_descent_of_flux_mono
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
    · flux_unimodal_ring
    refine Q'.eqv_trans _
      (-(lowerSixRecoveryPowerStepFlux x m +
        -lowerSixRecoveryPowerStepFlux y m)) _ hn ?_
    flux_unimodal_ring
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hnonneg (Q'.ge_of_eqv hreverse))

private theorem powerStepFlux_mono_of_increment_descent
    {x y : Q'} {m : Nat}
    (hdesc : lowerSixRecoveryPowerScaleIncrement x y (m + 1) ≤
      lowerSixRecoveryPowerScaleIncrement x y m) :
    lowerSixRecoveryPowerStepFlux x m ≤
      lowerSixRecoveryPowerStepFlux y m := by
  have hnonneg := Q'.sub_nonneg_of_le hdesc
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
    · flux_unimodal_ring
    refine Q'.eqv_trans _
      (-(lowerSixRecoveryPowerStepFlux x m +
        -lowerSixRecoveryPowerStepFlux y m)) _ hn ?_
    flux_unimodal_ring
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hnonneg (Q'.le_of_eqv hreverse))

/-- For ordered bases in `[0,1]`, descent of the power-scale increment is
persistent.  This is the division-free log-concavity/unimodality mechanism. -/
theorem lowerSixRecoveryPowerScaleIncrement_descent_persists
    {x y : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y)
    (hy1 : y ≤ (1 : Q')) (m : Nat)
    (hdesc : lowerSixRecoveryPowerScaleIncrement x y (m + 1) ≤
      lowerSixRecoveryPowerScaleIncrement x y m) :
    lowerSixRecoveryPowerScaleIncrement x y (m + 2) ≤
      lowerSixRecoveryPowerScaleIncrement x y (m + 1) := by
  have hy0 : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx0 hxy
  have hx1 : x ≤ (1 : Q') := Q'.le_trans' _ _ _ hxy hy1
  have hflux := powerStepFlux_mono_of_increment_descent hdesc
  have hyflux0 := lowerSixRecoveryPowerStepFlux_nonnegative hy0 hy1 m
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ x hflux hx0
  have hbase := Q'.mul_le_mul_of_nonneg_right _ _
    (lowerSixRecoveryPowerStepFlux y m) hxy hyflux0
  have hnextRaw : x * lowerSixRecoveryPowerStepFlux x m ≤
      y * lowerSixRecoveryPowerStepFlux y m :=
    Q'.le_trans' _ _ _ hscaled hbase
  have hxnext := lowerSixRecoveryPowerStepFlux_succ_factor x m
  have hynext := lowerSixRecoveryPowerStepFlux_succ_factor y m
  have hnextFlux : lowerSixRecoveryPowerStepFlux x (m + 1) ≤
      lowerSixRecoveryPowerStepFlux y (m + 1) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hxnext)
      (Q'.le_trans' _ _ _ hnextRaw (Q'.ge_of_eqv hynext))
  exact powerScaleIncrement_descent_of_flux_mono hnextFlux

/-! ## Complementary quadratic-exponent subsequence -/

def lowerSixRecoveryComplementExponent (j : Nat) : Nat :=
  2 * j * (j - 1) + 2

theorem lowerSixRecoveryComplementExponent_strict_succ
    {j : Nat} (hj : 1 ≤ j) :
    lowerSixRecoveryComplementExponent j <
      lowerSixRecoveryComplementExponent (j + 1) := by
  unfold lowerSixRecoveryComplementExponent
  rw [lowerSixRecoveryComplementExponent_succ]
  omega

theorem lowerSixRecoveryComplementScaleIncrement_eqv_powerIncrement
    (k j : Nat) :
    lowerSixRecoveryComplementScaleIncrement k j ≈
      lowerSixRecoveryPowerScaleIncrement (harmW k) (harmW (k + 1))
        (lowerSixRecoveryComplementExponent j) := by
  unfold lowerSixRecoveryComplementScaleIncrement
    lowerSixRecoveryComplementWeight
    lowerSixRecoveryPowerScaleIncrement
    lowerSixRecoveryComplementExponent
  exact Q'.eqv_refl _

/-- Exact unimodality transition for the production complementary drift:
after mode one, once a successive increment decreases, every subsequent
quadratic-exponent increment also decreases. -/
theorem lowerSixRecoveryComplementScaleIncrement_descent_persists
    {k j : Nat} (hj : 1 ≤ j)
    (hdesc : lowerSixRecoveryComplementScaleIncrement k (j + 1) ≤
      lowerSixRecoveryComplementScaleIncrement k j) :
    lowerSixRecoveryComplementScaleIncrement k (j + 2) ≤
      lowerSixRecoveryComplementScaleIncrement k (j + 1) := by
  let x := harmW k
  let y := harmW (k + 1)
  let A := lowerSixRecoveryPowerScaleIncrement x y
  let f := lowerSixRecoveryComplementExponent
  have hx0 : (0 : Q') ≤ x := by dsimp only [x]; exact harmW_nonneg k
  have hxy : x ≤ y := by
    dsimp only [x, y]
    exact HarmonicDriftAntisymmetry.harmW_mono_step k
  have hy1 : y ≤ (1 : Q') := by dsimp only [y]; exact harmW_le_one _
  have hpersist : ∀ m, A (m + 1) ≤ A m → A (m + 2) ≤ A (m + 1) :=
    fun m hm => lowerSixRecoveryPowerScaleIncrement_descent_persists
      hx0 hxy hy1 m hm
  have hfj : f j < f (j + 1) := by
    dsimp only [f]
    exact lowerSixRecoveryComplementExponent_strict_succ hj
  have hfj1 : f (j + 1) < f (j + 2) := by
    dsimp only [f]
    simpa only [Nat.add_assoc] using
      (lowerSixRecoveryComplementExponent_strict_succ
        (j := j + 1) (by omega))
  have hj0 := lowerSixRecoveryComplementScaleIncrement_eqv_powerIncrement k j
  have hj1 := lowerSixRecoveryComplementScaleIncrement_eqv_powerIncrement
    k (j + 1)
  have hbase : A (f (j + 1)) ≤ A (f j) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hj1)
      (Q'.le_trans' _ _ _ hdesc (Q'.le_of_eqv hj0))
  have hnext := descent_persists_on_strict_subsequence A f hpersist
    hfj hfj1 hbase
  have hj2 := lowerSixRecoveryComplementScaleIncrement_eqv_powerIncrement
    k (j + 2)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hj2)
    (Q'.le_trans' _ _ _ hnext (Q'.ge_of_eqv hj1))

/-- Tail form of the same result: one certified descent point makes the whole
later complementary-increment suffix antitone. -/
theorem lowerSixRecoveryComplementScaleIncrement_tail_antitone
    {k p : Nat} (hp : 1 ≤ p)
    (hstart : lowerSixRecoveryComplementScaleIncrement k (p + 1) ≤
      lowerSixRecoveryComplementScaleIncrement k p) :
    ∀ d,
      lowerSixRecoveryComplementScaleIncrement k (p + d + 1) ≤
        lowerSixRecoveryComplementScaleIncrement k (p + d)
  | 0 => by simpa using hstart
  | d + 1 => by
      have ih := lowerSixRecoveryComplementScaleIncrement_tail_antitone
        hp hstart d
      have hnext := lowerSixRecoveryComplementScaleIncrement_descent_persists
        (k := k) (j := p + d) (by omega) (by
          simpa only [Nat.add_assoc] using ih)
      simpa only [Nat.add_assoc] using hnext

#print axioms descent_persists_on_strict_subsequence
#print axioms lowerSixRecoveryPowerScaleIncrement_step_sub_eqv_fluxDrop
#print axioms lowerSixRecoveryPowerStepFlux_succ_factor
#print axioms lowerSixRecoveryPowerStepFlux_nonnegative
#print axioms lowerSixRecoveryPowerScaleIncrement_descent_persists
#print axioms lowerSixRecoveryComplementExponent_strict_succ
#print axioms lowerSixRecoveryComplementScaleIncrement_eqv_powerIncrement
#print axioms lowerSixRecoveryComplementScaleIncrement_descent_persists
#print axioms lowerSixRecoveryComplementScaleIncrement_tail_antitone

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxUnimodality
