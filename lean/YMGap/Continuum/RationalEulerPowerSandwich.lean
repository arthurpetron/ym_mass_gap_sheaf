/-
# A constructive rational Euler-power sandwich

The dynamic moving-cube decay theorem contains the literal rational factor

    ((q_j * q_j) ^ floor(t / a_j)).

To identify such powers with a physical exponential, one first needs a
finite, cutoff-independent comparison that does not assume a classical
logarithm/exponential inverse.  For a rational decrement `0 <= d < 1`, put

    rho  = 1 - d,
    odds = d / (1 - d).

This module proves the exact constructive-real corridor

    exp(-odds * n) <= rho^n <= exp(-d * n)

for every natural `n`.  The lower bound uses the rational Pade majorant
`exp(-x) <= 1/(1+x)` and the exact identity
`1/(1+odds) = 1-d`.  The upper bound starts from the alternating-series
inequality `1-d <= exp(-d)` and raises it by constructive-real
multiplication.  The exponential addition law identifies the resulting
constructive-real power with `exp(-d*n)`.

This is only a finite scalar corridor.  It does not prove cross-cutoff
convergence, identify a dynamic Yang--Mills rate, construct a continuum
observable, perform OS reconstruction, or prove the Clay mass gap.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Constructive.ExpGeomBound
import YMGap.Constructive.CRealLogRatCongruence
import YMGap.Continuum.BlockSpinModel

namespace YMGap.Continuum.RationalEulerPowerSandwich

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The rational Euler margin and odds -/

/-- The positive Euler base `1-d`. -/
def eulerMargin (d : Q') : Q' := 1 + -d

/-- Strict positivity of the Euler base when `d < 1`. -/
theorem eulerMargin_pos {d : Q'} (hd1 : d < (1 : Q')) :
    (0 : Q') < eulerMargin d := by
  unfold eulerMargin
  have hlt : d.num * (1 : Int) < (1 : Int) * (d.den : Int) := hd1
  have hnum : d.num < (d.den : Int) := by
    rw [Int.mul_one, Int.one_mul] at hlt
    exact hlt
  apply CReal.pos_of_num_pos
  show (0 : Int) < (1 : Int) * (d.den : Int) + (-d.num) * (1 : Int)
  rw [Int.one_mul, Int.mul_one]
  have hsub : (0 : Int) < (d.den : Int) - d.num := Int.sub_pos.mpr hnum
  rwa [Int.sub_eq_add_neg] at hsub

/-- The multiplicative odds `d/(1-d)` associated with the Euler base. -/
def eulerOdds (d : Q') (hd1 : d < (1 : Q')) : Q' :=
  Q'.divPos d (eulerMargin d) (eulerMargin_pos hd1)

/-- Nonnegativity of the odds for a nonnegative decrement. -/
theorem eulerOdds_nonnegative {d : Q'} (hd0 : (0 : Q') <= d)
    (hd1 : d < (1 : Q')) :
    (0 : Q') <= eulerOdds d hd1 := by
  unfold eulerOdds Q'.divPos
  exact Q'.mul_nonneg d (Q'.recipPos (eulerMargin d) (eulerMargin_pos hd1))
    hd0 (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- The odds denominator cancels the Euler margin:
`(1 + d/(1-d)) * (1-d) = 1`. -/
theorem one_add_eulerOdds_mul_eulerMargin_eqv_one
    {d : Q'} (hd1 : d < (1 : Q')) :
    ((1 + eulerOdds d hd1) * eulerMargin d) ≈ (1 : Q') := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv 1 (eulerOdds d hd1) (eulerMargin d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv (eulerMargin d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (eulerMargin d)
      (eulerOdds d hd1 * eulerMargin d) d ?_) ?_
  · unfold eulerOdds
    exact Q'.divPos_mul_eqv d (eulerMargin d) (eulerMargin_pos hd1)
  · unfold eulerMargin
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-d) d) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 ((-d) + d) 0 (Q'.neg_add_self_eqv d)) ?_
    exact QPoly.q_add_zero_eqv 1

/-- The Pade base at the odds is exactly no larger than the Euler margin. -/
theorem oneOver1p_eulerOdds_le_margin
    {d : Q'} (hd0 : (0 : Q') <= d) (hd1 : d < (1 : Q')) :
    ExpUBInstance.oneOver1p (eulerOdds d hd1) <= eulerMargin d := by
  have hodds0 : (0 : Q') <= eulerOdds d hd1 :=
    eulerOdds_nonnegative hd0 hd1
  have hfactorPos : (0 : Q') < 1 + eulerOdds d hd1 :=
    YMGap.Continuum.one_add_pos hodds0
  have hleft :
      ((1 + eulerOdds d hd1) *
        ExpUBInstance.oneOver1p (eulerOdds d hd1)) ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (1 + eulerOdds d hd1)
        (ExpUBInstance.oneOver1p (eulerOdds d hd1)))
      (ExpUBInstance.oneOver1p_mul_oneAddX (eulerOdds d hd1) hodds0)
  have hright :
      ((1 + eulerOdds d hd1) * eulerMargin d) ≈ (1 : Q') :=
    one_add_eulerOdds_mul_eulerMargin_eqv_one hd1
  apply Q'.le_of_mul_le_mul_left
    (c := 1 + eulerOdds d hd1)
    (a := ExpUBInstance.oneOver1p (eulerOdds d hd1))
    (b := eulerMargin d)
  · exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright))
  · exact hfactorPos

/-! ## 2. The one-step exponential corridor -/

/-- The lower exponential base lies below the Euler margin. -/
theorem expNeg_eulerOdds_le_margin
    {d : Q'} (hd0 : (0 : Q') <= d) (hd1 : d < (1 : Q')) :
    CReal.leRat
      (ExpNeg.expNeg (eulerOdds d hd1) (eulerOdds_nonnegative hd0 hd1))
      (eulerMargin d) :=
  expNeg_le_rat (eulerOdds d hd1) (eulerMargin d)
    (eulerOdds_nonnegative hd0 hd1)
    (oneOver1p_eulerOdds_le_margin hd0 hd1)

/-- The Euler margin lies below the upper exponential base. -/
theorem eulerMargin_geRat_expNeg
    {d : Q'} (hd0 : (0 : Q') <= d) (hd1 : d < (1 : Q')) :
    ExpPos.geRat (ExpNeg.expNeg d hd0) (eulerMargin d) := by
  apply ExpPos.geRat_of_eventually
  refine ⟨2, fun n hn => ?_⟩
  unfold eulerMargin
  exact ExpNeg.oneSub_le_partialSum hd0 (Q'.le_of_lt hd1) n hn

/-! ## 3. Natural powers and the finite sandwich -/

/-- Raising the upper exponential base preserves the rational Euler lower
bound. -/
theorem expNeg_cpow_ge_eulerMargin_pow
  {d : Q'} (hd0 : (0 : Q') <= d) (hd1 : d < (1 : Q')) :
    forall n : Nat,
      ExpPos.geRat (CReal.cpow (ExpNeg.expNeg d hd0) n)
        ((eulerMargin d) ^ n)
  | 0 => by
      change ExpPos.geRat CReal.cone (1 : Q')
      exact ExpPos.geRat_of_eventually
        ⟨0, fun _ _ => Q'.le_refl' (1 : Q')⟩
  | n + 1 => by
      change ExpPos.geRat
        (CReal.mul (CReal.cpow (ExpNeg.expNeg d hd0) n)
          (ExpNeg.expNeg d hd0))
        (eulerMargin d * (eulerMargin d) ^ n)
      have hpow0 : (0 : Q') <= (eulerMargin d) ^ n :=
        Q'.pow_nonneg (eulerMargin d) (Q'.le_of_lt (eulerMargin_pos hd1)) n
      have hmul : ExpPos.geRat
          (CReal.mul (CReal.cpow (ExpNeg.expNeg d hd0) n)
            (ExpNeg.expNeg d hd0))
          (((eulerMargin d) ^ n) * eulerMargin d) :=
        YMGap.Continuum.geRat_mul hpow0
          (expNeg_cpow_ge_eulerMargin_pow hd0 hd1 n)
          (eulerMargin_geRat_expNeg hd0 hd1)
          (expNeg_geRat_zero d hd0)
      exact ExpPos.geRat_mono hmul
        (Q'.le_of_eqv
          (Q'.mul_comm_eqv (eulerMargin d) ((eulerMargin d) ^ n)))

/-- The constructive-real natural power of `exp(-d)` is equivalent to the
single exponential `exp(-d*n)`. -/
theorem expNeg_cpow_equiv_scaled
    (d : Q') (hd0 : (0 : Q') <= d) :
    forall n : Nat,
      CReal.Equiv (CReal.cpow (ExpNeg.expNeg d hd0) n)
        (ExpNeg.expNeg (d * Q'.ofNat n)
          (Q'.mul_nonneg d (Q'.ofNat n) hd0 (ofNat_nonneg n)))
  | 0 => by
      have harg : (d * Q'.ofNat 0) ≈ (0 : Q') :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left d (Q'.ofNat 0) 0 (by decide))
          (QPoly.q_mul_zero d)
      have hzero : CReal.Equiv
          (ExpNeg.expNeg (d * Q'.ofNat 0)
            (Q'.mul_nonneg d (Q'.ofNat 0) hd0 (ofNat_nonneg 0)))
          (ExpNeg.expNeg 0 (by decide)) :=
        expNeg_eqv_congr _ (by decide) harg
      exact CReal.Equiv.symm
        (CReal.Equiv.trans hzero (CReal.expNeg_zero_equiv_cone (by decide)))
  | n + 1 => by
      have hscaled0 : (0 : Q') <= d * Q'.ofNat n :=
        Q'.mul_nonneg d (Q'.ofNat n) hd0 (ofNat_nonneg n)
      have hsum0 : (0 : Q') <= d * Q'.ofNat n + d :=
        Q'.zero_le_add _ _ hscaled0 hd0
      have hnext0 : (0 : Q') <= d * Q'.ofNat (n + 1) :=
        Q'.mul_nonneg d (Q'.ofNat (n + 1)) hd0 (ofNat_nonneg (n + 1))
      refine CReal.Equiv.trans
        (CReal.mul_congr_left (expNeg_cpow_equiv_scaled d hd0 n)) ?_
      refine CReal.Equiv.trans
        (expNeg_add_equiv (d * Q'.ofNat n) d hscaled0 hd0) ?_
      exact expNeg_eqv_congr hsum0 hnext0
        (Q'.eqv_symm (mul_ofNat_succ_eqv d n))

/-- Convert a rational upper bound into eventual order against its rational
embedding. -/
private theorem leEv_of_leRat {x : CReal} {upper : Q'}
    (h : CReal.leRat x upper) : CReal.leEv x (CReal.ofQ' upper) := by
  intro epsilon hepsilon
  exact h epsilon hepsilon

/-- Convert a rational lower bound into eventual order from its rational
embedding. -/
private theorem leEv_of_geRat {x : CReal} {lower : Q'}
    (h : ExpPos.geRat x lower) : CReal.leEv (CReal.ofQ' lower) x := by
  intro epsilon hepsilon
  exact h epsilon hepsilon

/-- Lower half of the finite Euler corridor:
`exp(-(d/(1-d))*n) <= (1-d)^n`. -/
theorem rationalEulerPower_lower
    {d : Q'} (hd0 : (0 : Q') <= d) (hd1 : d < (1 : Q'))
    (n : Nat) :
    CReal.leEv
      (ExpNeg.expNeg (eulerOdds d hd1 * Q'.ofNat n)
        (Q'.mul_nonneg (eulerOdds d hd1) (Q'.ofNat n)
          (eulerOdds_nonnegative hd0 hd1) (ofNat_nonneg n)))
      (CReal.ofQ' ((eulerMargin d) ^ n)) :=
  leEv_of_leRat
    (expNeg_mul_le_pow (eulerOdds d hd1) (eulerMargin d)
      (eulerOdds_nonnegative hd0 hd1)
      (Q'.le_of_lt (eulerMargin_pos hd1))
      (expNeg_eulerOdds_le_margin hd0 hd1) n)

/-- Upper half of the finite Euler corridor:
`(1-d)^n <= exp(-d*n)`. -/
theorem rationalEulerPower_upper
    {d : Q'} (hd0 : (0 : Q') <= d) (hd1 : d < (1 : Q'))
    (n : Nat) :
    CReal.leEv
      (CReal.ofQ' ((eulerMargin d) ^ n))
      (ExpNeg.expNeg (d * Q'.ofNat n)
        (Q'.mul_nonneg d (Q'.ofNat n) hd0 (ofNat_nonneg n))) := by
  apply leEv_of_geRat
  exact SU3CharFactor.geRat_of_equiv
    (CReal.Equiv.symm (expNeg_cpow_equiv_scaled d hd0 n))
    (expNeg_cpow_ge_eulerMargin_pow hd0 hd1 n)

/-- The complete constructive finite Euler-power sandwich. -/
theorem rationalEulerPower_sandwich
    {d : Q'} (hd0 : (0 : Q') <= d) (hd1 : d < (1 : Q'))
    (n : Nat) :
    CReal.leEv
        (ExpNeg.expNeg (eulerOdds d hd1 * Q'.ofNat n)
          (Q'.mul_nonneg (eulerOdds d hd1) (Q'.ofNat n)
            (eulerOdds_nonnegative hd0 hd1) (ofNat_nonneg n)))
        (CReal.ofQ' ((eulerMargin d) ^ n))
      /\
    CReal.leEv
        (CReal.ofQ' ((eulerMargin d) ^ n))
        (ExpNeg.expNeg (d * Q'.ofNat n)
          (Q'.mul_nonneg d (Q'.ofNat n) hd0 (ofNat_nonneg n))) :=
  ⟨rationalEulerPower_lower hd0 hd1 n,
    rationalEulerPower_upper hd0 hd1 n⟩

/-! ## 4. The same corridor in transfer-rate currency -/

/-- A positive transfer rate has decrement strictly below one. -/
private theorem one_sub_lt_one_of_pos {q : Q'} (hq0 : (0 : Q') < q) :
    (1 : Q') + -q < (1 : Q') := by
  show ((1 : Q') + -q).num * ((1 : Q').den : Int) <
    (1 : Q').num * (((1 : Q') + -q).den : Int)
  have hnum : (0 : Int) < q.num := Q'.num_pos_of_pos hq0
  change
    (((1 : Int) * (q.den : Int) + (-q.num) * (1 : Int)) * (1 : Int)) <
      ((1 : Int) * (((1 : Nat) * q.den : Nat) : Int))
  push_cast
  omega

/-- Taking the Euler margin of the decrement `1-q` returns the original
transfer rate, up to the rational setoid equality. -/
theorem eulerMargin_one_sub_eqv (q : Q') :
    eulerMargin ((1 : Q') + -q) ≈ q := by
  unfold eulerMargin
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 (-(1 + -q)) (-(1 : Q') + -(-q))
      (Q'.neg_add_eqv 1 (-q))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 (-(1 : Q') + -(-q)) (-(1 : Q') + q)
      (Q'.add_eqv_congr_left (-(1 : Q')) (-(-q)) q
        (Q'.neg_neg_eqv q))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-(1 : Q')) q)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (1 + -(1 : Q')) 0 q
      (Q'.add_neg_self_eqv 1)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 q) (QPoly.q_add_zero_eqv q)

/-- For any positive subunit rational transfer rate `q`, its literal natural
power lies between exponentials of the exact linear decrement and its odds
correction.  Unlike the generic theorem, the middle term is syntactically the
same `q^n` consumed by transfer estimates. -/
theorem rationalRatePower_sandwich
    {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q <= (1 : Q'))
    (n : Nat) :
    CReal.leEv
        (ExpNeg.expNeg
          (eulerOdds ((1 : Q') + -q) (one_sub_lt_one_of_pos hq0) *
            Q'.ofNat n)
          (Q'.mul_nonneg
            (eulerOdds ((1 : Q') + -q) (one_sub_lt_one_of_pos hq0))
            (Q'.ofNat n)
            (eulerOdds_nonnegative (Q'.sub_nonneg_of_le hq1)
              (one_sub_lt_one_of_pos hq0))
            (ofNat_nonneg n)))
        (CReal.ofQ' (q ^ n))
      /\
    CReal.leEv
        (CReal.ofQ' (q ^ n))
        (ExpNeg.expNeg (((1 : Q') + -q) * Q'.ofNat n)
          (Q'.mul_nonneg ((1 : Q') + -q) (Q'.ofNat n)
            (Q'.sub_nonneg_of_le hq1) (ofNat_nonneg n))) := by
  let d : Q' := (1 : Q') + -q
  have hd0 : (0 : Q') <= d := Q'.sub_nonneg_of_le hq1
  have hd1 : d < (1 : Q') := one_sub_lt_one_of_pos hq0
  have hsandwich := rationalEulerPower_sandwich hd0 hd1 n
  have hmargin : eulerMargin d ≈ q := eulerMargin_one_sub_eqv q
  have hpower : (eulerMargin d) ^ n ≈ q ^ n :=
    Q'.pow_eqv_congr hmargin n
  have hmiddle : CReal.Equiv
      (CReal.ofQ' ((eulerMargin d) ^ n)) (CReal.ofQ' (q ^ n)) :=
    CReal.ofQ'_equiv_of_eqv hpower
  exact
    ⟨(CReal.leEv_congr (CReal.Equiv.refl _) hmiddle).mp hsandwich.1,
      (CReal.leEv_congr hmiddle (CReal.Equiv.refl _)).mp hsandwich.2⟩

end YMGap.Continuum.RationalEulerPowerSandwich

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.RationalEulerPowerSandwich.eulerMargin_pos
#print axioms YMGap.Continuum.RationalEulerPowerSandwich.oneOver1p_eulerOdds_le_margin
#print axioms YMGap.Continuum.RationalEulerPowerSandwich.expNeg_eulerOdds_le_margin
#print axioms YMGap.Continuum.RationalEulerPowerSandwich.eulerMargin_geRat_expNeg
#print axioms YMGap.Continuum.RationalEulerPowerSandwich.expNeg_cpow_equiv_scaled
#print axioms YMGap.Continuum.RationalEulerPowerSandwich.rationalEulerPower_sandwich
#print axioms YMGap.Continuum.RationalEulerPowerSandwich.eulerMargin_one_sub_eqv
#print axioms YMGap.Continuum.RationalEulerPowerSandwich.rationalRatePower_sandwich
