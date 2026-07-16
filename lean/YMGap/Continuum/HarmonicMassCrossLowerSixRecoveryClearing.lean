/-
Exact denominator clearing for the sparse lower-six recovery slack.

This file is deliberately algebraic.  It converts the harmonic coordinates

  u = 1 / D,       w = (D - 1) / D,       D = k + 2

into integer-polynomial coordinates before any positivity argument is made.
In particular, none of the inequalities downstream may depend on a sampled
decimal approximation to a theta sum.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryClearing

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem recovery_clear_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "recovery_clear_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               recovery_clear_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-! ## Harmonic denominator identities -/

/-- Exact reciprocal coordinate, in multiplication-first form. -/
theorem recovery_harmU_mul_den (k : Nat) :
    harmU k * Q'.ofNat (k + 2) ≈ (1 : Q') := by
  unfold harmU unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num,
    Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl,
    Int.mul_one, Int.one_mul]

/-- Exact harmonic weight coordinate `w D = D-1`. -/
theorem recovery_harmW_mul_den (k : Nat) :
    harmW k * Q'.ofNat (k + 2) ≈ Q'.ofNat (k + 1) := by
  have hD : Q'.ofNat (k + 2) ≈ Q'.ofNat (k + 1) + (1 : Q') := by
    simpa [Nat.add_assoc] using Q'.ofNat_add_eqv (k + 1) 1
  unfold harmW oneSub
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv 1 (-(harmU k)) (Q'.ofNat (k + 2))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.one_mul_eqv (Q'.ofNat (k + 2)))
      (Q'.neg_mul_eqv (harmU k) (Q'.ofNat (k + 2)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hD
      (Q'.neg_eqv_congr _ _ (recovery_harmU_mul_den k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (Q'.ofNat (k + 1)) 1 (-1)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.ofNat (k + 1)) _ _
      (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact QPoly.q_add_zero_eqv _

private theorem recovery_two_den_sub_one (k : Nat) :
    Q'.ofNat (k + 2) + Q'.ofNat (k + 1) ≈
      Q'.ofNat (2 * (k + 2)) + -(1 : Q') := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den,
    recovery_clear_neg_num_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.one_mul, Int.mul_one]
  push_cast
  omega

/-- Exact cleared base for the cubic profile: `D(1+w)=2D-1`. -/
theorem recovery_one_add_harmW_mul_den (k : Nat) :
    ((1 : Q') + harmW k) * Q'.ofNat (k + 2) ≈
      Q'.ofNat (2 * (k + 2)) + -(1 : Q') := by
  refine Q'.eqv_trans _
    ((1 : Q') * Q'.ofNat (k + 2) +
      harmW k * Q'.ofNat (k + 2)) _
    (Q'.add_mul_eqv 1 (harmW k) (Q'.ofNat (k + 2))) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (k + 2) + harmW k * Q'.ofNat (k + 2)) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.one_mul_eqv (Q'.ofNat (k + 2)))) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (k + 2) + Q'.ofNat (k + 1)) _
    (Q'.add_eqv_congr_left _ _ _ (recovery_harmW_mul_den k)) ?_
  exact recovery_two_den_sub_one k

/-! ## Power clearing -/

private theorem recovery_qpow_one : ∀ r,
    qpow (1 : Q') r ≈ (1 : Q')
  | 0 => Q'.eqv_refl _
  | r + 1 => by
      show qpow (1 : Q') r * 1 ≈ 1
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_right _ _ _ (recovery_qpow_one r))
        (Q'.one_mul_eqv 1)

private theorem recovery_qpow_cancel {D u : Q'}
    (hDu : D * u ≈ (1 : Q')) (a r : Nat) :
    qpow D (a + r) * qpow u r ≈ qpow D a := by
  have hsplit := qpow_add D a r
  have hprod : qpow D r * qpow u r ≈ (1 : Q') :=
    Q'.eqv_trans _ (qpow (D * u) r) _
      (Q'.eqv_symm (qpow_mul_base D u r))
      (Q'.eqv_trans _ (qpow (1 : Q') r) _
        (qpow_eqv_congr_base hDu r) (recovery_qpow_one r))
  exact Q'.eqv_trans _
    ((qpow D a * qpow D r) * qpow u r) _
    (Q'.mul_eqv_congr_right _ _ _ hsplit)
    (Q'.eqv_trans _ (qpow D a * (qpow D r * qpow u r)) _
      (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ (qpow D a * 1) _
        (Q'.mul_eqv_congr_left _ _ _ hprod)
        (Q'.mul_one_eqv _)))

/-- Clear an arbitrary harmonic-weight monomial against a sufficiently large
power of its denominator. -/
theorem recovery_clear_harmW_power (k M e : Nat) (he : e ≤ M) :
    qpow (Q'.ofNat (k + 2)) M * qpow (harmW k) e ≈
      qpow (Q'.ofNat (k + 1)) e *
        qpow (Q'.ofNat (k + 2)) (M - e) := by
  let D := Q'.ofNat (k + 2)
  let R := Q'.ofNat (k + 1)
  let w := harmW k
  have hsum : M - e + e = M := Nat.sub_add_cancel he
  have hbase : D * w ≈ R :=
    Q'.eqv_trans _ (w * D) _ (Q'.mul_comm_eqv _ _)
      (recovery_harmW_mul_den k)
  have hpow : qpow D e * qpow w e ≈ qpow R e :=
    Q'.eqv_trans _ (qpow (D * w) e) _
      (Q'.eqv_symm (qpow_mul_base D w e))
      (qpow_eqv_congr_base hbase e)
  have hsplit := qpow_add D (M - e) e
  rw [hsum] at hsplit
  refine Q'.eqv_trans _
    ((qpow D (M - e) * qpow D e) * qpow w e) _
    (Q'.mul_eqv_congr_right _ _ _ hsplit) ?_
  refine Q'.eqv_trans _
    (qpow D (M - e) * (qpow D e * qpow w e)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (qpow D (M - e) * qpow R e) _
    (Q'.mul_eqv_congr_left _ _ _ hpow) ?_
  exact Q'.mul_comm_eqv _ _

/-- Clear reciprocal powers: `D^(a+r) u^r = D^a`. -/
theorem recovery_clear_harmU_power (k a r : Nat) :
    qpow (Q'.ofNat (k + 2)) (a + r) * qpow (harmU k) r ≈
      qpow (Q'.ofNat (k + 2)) a := by
  apply recovery_qpow_cancel
  exact Q'.eqv_trans _ (harmU k * Q'.ofNat (k + 2)) _
    (Q'.mul_comm_eqv _ _) (recovery_harmU_mul_den k)

private theorem recovery_qpow_two (x : Q') : qpow x 2 ≈ x * x := by
  change ((1 : Q') * x) * x ≈ x * x
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

private theorem recovery_cubic_distrib_algebra (X A U : Q') :
    X * (A + -(Q'.ofNat 6 * U)) ≈
      X * A + -(Q'.ofNat 6 * (X * U)) := by
  recovery_clear_ring

/-- The cubic profile has precisely the polynomial numerator declared in the
sparse-coordinate module. -/
theorem recovery_cubic_profile_cleared (k : Nat) :
    qpow (Q'.ofNat (k + 2)) 3 *
        (qpow ((1 : Q') + harmW k) 3 +
          -(Q'.ofNat 6 * (harmU k * harmU k))) ≈
      lowerSixCenterCubicNumerator (k + 2) := by
  let D := Q'.ofNat (k + 2)
  let A := (1 : Q') + harmW k
  let U := harmU k
  let B := Q'.ofNat (2 * (k + 2)) + -(1 : Q')
  have hbase : D * A ≈ B :=
    Q'.eqv_trans _ (A * D) _ (Q'.mul_comm_eqv _ _)
      (recovery_one_add_harmW_mul_den k)
  have hcube : qpow D 3 * qpow A 3 ≈ qpow B 3 :=
    Q'.eqv_trans _ (qpow (D * A) 3) _
      (Q'.eqv_symm (qpow_mul_base D A 3))
      (qpow_eqv_congr_base hbase 3)
  have hu2 : U * U ≈ qpow U 2 := Q'.eqv_symm (recovery_qpow_two U)
  have hrecip : qpow D 3 * (U * U) ≈ D :=
    Q'.eqv_trans _ (qpow D 3 * qpow U 2) D
      (Q'.mul_eqv_congr_left _ _ _ hu2)
      (Q'.eqv_trans _ (qpow D 1) D
        (by simpa only [D, U] using recovery_clear_harmU_power k 1 2)
        (by
          change (1 : Q') * D ≈ D
          exact Q'.one_mul_eqv D))
  unfold lowerSixCenterCubicNumerator
  change
    qpow D 3 * (qpow A 3 + -(Q'.ofNat 6 * (U * U))) ≈
      qpow B 3 + -(Q'.ofNat (6 * (k + 2)))
  refine Q'.eqv_trans _
    (qpow D 3 * qpow A 3 +
      -(Q'.ofNat 6 * (qpow D 3 * (U * U)))) _
    (recovery_cubic_distrib_algebra (qpow D 3) (qpow A 3) (U * U)) ?_
  refine Q'.eqv_trans _
    (qpow B 3 + -(Q'.ofNat 6 * D)) _
    (Q'.add_eqv_congr' hcube
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 6) _ _ hrecip))) ?_
  exact Q'.add_eqv_congr_left (qpow B 3) _ _
    (Q'.neg_eqv_congr _ _
      (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 6 (k + 2))))

/-! ## Termwise theta clearing -/

private theorem recovery_qpow_sqbase_double (w : Q') (n : Nat) :
    qpow (w * w) n ≈ qpow w (2 * n) := by
  have hadd := qpow_add w n n
  have htwo : n + n = 2 * n := by omega
  rw [htwo] at hadd
  exact Q'.eqv_trans _ (qpow w n * qpow w n) _
    (qpow_mul_base w w n) (Q'.eqv_symm hadd)

/-- A single integer-theta term cleared at exponent `M`. -/
theorem recovery_integerThetaTerm_cleared
    (k M n : Nat) (he : 2 * (n * n) ≤ M) :
    qpow (Q'.ofNat (k + 2)) M * integerThetaTerm (harmW k) n ≈
      (Q'.ofNat (n * n) *
        qpow (Q'.ofNat (k + 1)) (2 * (n * n))) *
        qpow (Q'.ofNat (k + 2)) (M - 2 * (n * n)) := by
  let D := Q'.ofNat (k + 2)
  let R := Q'.ofNat (k + 1)
  let w := harmW k
  let p := n * n
  let e := 2 * p
  have htheta : qpow (w * w) p ≈ qpow w e := by
    dsimp only [e]
    exact recovery_qpow_sqbase_double w p
  have hclear : qpow D M * qpow w e ≈ qpow R e * qpow D (M - e) := by
    exact recovery_clear_harmW_power k M e he
  unfold integerThetaTerm
  dsimp only [D, R, w, p, e] at htheta hclear ⊢
  refine Q'.eqv_trans _
    (qpow D M *
      (Q'.ofNat (n * n) * qpow w (2 * (n * n)))) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ htheta)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (n * n) *
      (qpow D M * qpow w (2 * (n * n)))) _
    (by recovery_clear_ring) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (n * n) *
      (qpow R (2 * (n * n)) *
        qpow D (M - 2 * (n * n)))) _
    (Q'.mul_eqv_congr_left _ _ _ hclear) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- A single half-integer-theta term, including the extra leading harmonic
weight in the sparse slack, cleared at exponent `M`. -/
theorem recovery_weightedHalfThetaTerm_cleared
    (k M n : Nat) (he : 2 * (n * (n + 1)) + 1 ≤ M) :
    qpow (Q'.ofNat (k + 2)) M *
        (harmW k * halfThetaTerm (harmW k) n) ≈
      (Q'.ofNat (n * (n + 1)) *
        qpow (Q'.ofNat (k + 1)) (2 * (n * (n + 1)) + 1)) *
        qpow (Q'.ofNat (k + 2))
          (M - (2 * (n * (n + 1)) + 1)) := by
  let D := Q'.ofNat (k + 2)
  let R := Q'.ofNat (k + 1)
  let w := harmW k
  let p := n * (n + 1)
  let e := 2 * p
  have htheta : qpow (w * w) p ≈ qpow w e := by
    dsimp only [e]
    exact recovery_qpow_sqbase_double w p
  have hclear :
      qpow D M * qpow w (e + 1) ≈
        qpow R (e + 1) * qpow D (M - (e + 1)) := by
    exact recovery_clear_harmW_power k M (e + 1) he
  have hweighted :
      w * (Q'.ofNat (n * (n + 1)) * qpow w e) ≈
        Q'.ofNat (n * (n + 1)) * qpow w (e + 1) := by
    change
      w * (Q'.ofNat (n * (n + 1)) * qpow w e) ≈
        Q'.ofNat (n * (n + 1)) * (qpow w e * w)
    recovery_clear_ring
  unfold halfThetaTerm
  dsimp only [D, R, w, p, e] at htheta hclear hweighted ⊢
  refine Q'.eqv_trans _
    (qpow D M *
      (w * (Q'.ofNat (n * (n + 1)) *
        qpow w (2 * (n * (n + 1)))))) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ htheta))) ?_
  refine Q'.eqv_trans _
    (qpow D M *
      (Q'.ofNat (n * (n + 1)) *
        qpow w (2 * (n * (n + 1)) + 1))) _
    (Q'.mul_eqv_congr_left _ _ _ hweighted) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (n * (n + 1)) *
      (qpow D M * qpow w (2 * (n * (n + 1)) + 1))) _
    (by recovery_clear_ring) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (n * (n + 1)) *
      (qpow R (2 * (n * (n + 1)) + 1) *
        qpow D (M - (2 * (n * (n + 1)) + 1)))) _
    (Q'.mul_eqv_congr_left _ _ _ hclear) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

private theorem recovery_profile_term_algebra
    (D3 C DM T CN Z : Q')
    (hC : D3 * C ≈ CN) (hT : DM * T ≈ Z) :
    (D3 * DM) * (C * T) ≈ CN * Z := by
  refine Q'.eqv_trans _ ((D3 * C) * (DM * T)) _
    (by recovery_clear_ring) ?_
  refine Q'.eqv_trans _ (CN * (DM * T)) _
    (Q'.mul_eqv_congr_right _ _ _ hC) ?_
  exact Q'.mul_eqv_congr_left _ _ _ hT

/-- One integer-theta summand with the cubic profile cleared simultaneously. -/
theorem recovery_profileIntegerThetaTerm_cleared
    (k M n : Nat) (he : 2 * (n * n) ≤ M) :
    qpow (Q'.ofNat (k + 2)) (M + 3) *
        ((qpow ((1 : Q') + harmW k) 3 +
            -(Q'.ofNat 6 * (harmU k * harmU k))) *
          integerThetaTerm (harmW k) n) ≈
      ((lowerSixCenterCubicNumerator (k + 2) * Q'.ofNat (n * n)) *
        qpow (Q'.ofNat (k + 1)) (2 * (n * n))) *
        qpow (Q'.ofNat (k + 2)) (M - 2 * (n * n)) := by
  let D := Q'.ofNat (k + 2)
  let C := qpow ((1 : Q') + harmW k) 3 +
    -(Q'.ofNat 6 * (harmU k * harmU k))
  let T := integerThetaTerm (harmW k) n
  have hsplit := qpow_add D 3 M
  have hsum : 3 + M = M + 3 := by omega
  rw [hsum] at hsplit
  have hC : qpow D 3 * C ≈ lowerSixCenterCubicNumerator (k + 2) := by
    exact recovery_cubic_profile_cleared k
  have hT := recovery_integerThetaTerm_cleared k M n he
  refine Q'.eqv_trans _
    ((qpow D 3 * qpow D M) * (C * T)) _
    (Q'.mul_eqv_congr_right _ _ _ hsplit) ?_
  refine Q'.eqv_trans _
    (lowerSixCenterCubicNumerator (k + 2) *
      ((Q'.ofNat (n * n) *
        qpow (Q'.ofNat (k + 1)) (2 * (n * n))) *
        qpow D (M - 2 * (n * n)))) _
    (recovery_profile_term_algebra _ _ _ _ _ _ hC hT) ?_
  refine Q'.eqv_trans _
    ((lowerSixCenterCubicNumerator (k + 2) *
      (Q'.ofNat (n * n) *
        qpow (Q'.ofNat (k + 1)) (2 * (n * n)))) *
      qpow D (M - 2 * (n * n))) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem recovery_integer_exponent_le (c j : Nat) (hj : j < 2 * c) :
    2 * ((j + 1) * (j + 1)) ≤ lowerSixCenterMaxExponent c := by
  have hn : j + 1 ≤ 2 * c := by omega
  have hn' : j + 1 ≤ 2 * c + 1 := Nat.le_trans hn (by omega)
  have hs : (j + 1) * (j + 1) ≤
      (2 * c + 1) * (2 * c + 1) := Nat.mul_le_mul hn' hn'
  unfold lowerSixCenterMaxExponent
  exact Nat.mul_le_mul_left 2 hs

private theorem recovery_half_exponent_le (c j : Nat) (hj : j < 2 * c) :
    2 * ((j + 1) * (j + 2)) + 1 ≤
      lowerSixCenterClearingExponent c := by
  have hn : j + 1 ≤ 2 * c := by omega
  have hnL : j + 1 ≤ 2 * c + 1 := Nat.le_trans hn (by omega)
  have hnpL : j + 2 ≤ 2 * c + 1 := by omega
  have hs : (j + 1) * (j + 2) ≤
      (2 * c + 1) * (2 * c + 1) := Nat.mul_le_mul hnL hnpL
  unfold lowerSixCenterClearingExponent lowerSixCenterMaxExponent
  have := Nat.mul_le_mul_left 2 hs
  omega

/-- The entire cubic-times-integer block clears termwise, with the exponent
bound justified only from `j < 2c`. -/
theorem recovery_integerBlock_cleared (k c : Nat) :
    qpow (Q'.ofNat (k + 2)) (lowerSixCenterClearingExponent c) *
        ((qpow ((1 : Q') + harmW k) 3 +
            -(Q'.ofNat 6 * (harmU k * harmU k))) *
          lowerSixFixedIntegerMass k c) ≈
      finSum (fun j =>
        let n := j + 1
        let e := 2 * (n * n)
        ((lowerSixCenterCubicNumerator (k + 2) * Q'.ofNat (n * n)) *
          qpow (Q'.ofNat (k + 1)) e) *
          qpow (Q'.ofNat (k + 2))
            (lowerSixCenterMaxExponent c - e)) (2 * c) := by
  let D := Q'.ofNat (k + 2)
  let C := qpow ((1 : Q') + harmW k) 3 +
    -(Q'.ofNat 6 * (harmU k * harmU k))
  let f := fun j => integerThetaTerm (harmW k) (j + 1)
  let g := fun j =>
    let n := j + 1
    let e := 2 * (n * n)
    ((lowerSixCenterCubicNumerator (k + 2) * Q'.ofNat (n * n)) *
      qpow (Q'.ofNat (k + 1)) e) *
      qpow D (lowerSixCenterMaxExponent c - e)
  have hL : lowerSixCenterClearingExponent c =
      lowerSixCenterMaxExponent c + 3 := rfl
  unfold lowerSixFixedIntegerMass
  rw [hL]
  refine Q'.eqv_trans _
    ((qpow D (lowerSixCenterMaxExponent c + 3) * C) *
      finSum f (2 * c)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    (finSum (fun j =>
      (qpow D (lowerSixCenterMaxExponent c + 3) * C) * f j) (2 * c)) _
    (RationalTail.const_mul_finSum f
      (qpow D (lowerSixCenterMaxExponent c + 3) * C) (2 * c)) ?_
  refine RationalTail.finSum_eqv_congr_lt _ g (2 * c) (fun j hj => ?_)
  refine Q'.eqv_trans _
    (qpow D (lowerSixCenterMaxExponent c + 3) * (C * f j)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  exact recovery_profileIntegerThetaTerm_cleared k
    (lowerSixCenterMaxExponent c) (j + 1)
    (recovery_integer_exponent_le c j hj)

/-- The weighted half-integer block clears termwise at the common exponent. -/
theorem recovery_halfBlock_cleared (k c : Nat) :
    qpow (Q'.ofNat (k + 2)) (lowerSixCenterClearingExponent c) *
        (harmW k * lowerSixFixedHalfMass k c) ≈
      finSum (fun j =>
        let n := j + 1
        let e := 2 * (n * (n + 1))
        (Q'.ofNat (n * (n + 1)) *
          qpow (Q'.ofNat (k + 1)) (e + 1)) *
          qpow (Q'.ofNat (k + 2))
            (lowerSixCenterMaxExponent c + 2 - e)) (2 * c) := by
  let D := Q'.ofNat (k + 2)
  let w := harmW k
  let f := fun j => halfThetaTerm w (j + 1)
  let g := fun j =>
    let n := j + 1
    let e := 2 * (n * (n + 1))
    (Q'.ofNat (n * (n + 1)) *
      qpow (Q'.ofNat (k + 1)) (e + 1)) *
      qpow D (lowerSixCenterMaxExponent c + 2 - e)
  unfold lowerSixFixedHalfMass
  refine Q'.eqv_trans _
    ((qpow D (lowerSixCenterClearingExponent c) * w) *
      finSum f (2 * c)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    (finSum (fun j =>
      (qpow D (lowerSixCenterClearingExponent c) * w) * f j) (2 * c)) _
    (RationalTail.const_mul_finSum f
      (qpow D (lowerSixCenterClearingExponent c) * w) (2 * c)) ?_
  refine RationalTail.finSum_eqv_congr_lt _ g (2 * c) (fun j hj => ?_)
  refine Q'.eqv_trans _
    (qpow D (lowerSixCenterClearingExponent c) * (w * f j)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  have hterm := recovery_weightedHalfThetaTerm_cleared k
    (lowerSixCenterClearingExponent c) (j + 1)
    (recovery_half_exponent_le c j hj)
  have he : 2 * ((j + 1) * ((j + 1) + 1)) ≤
      lowerSixCenterMaxExponent c := by
    have hn : j + 1 ≤ 2 * c := by omega
    have hnL : j + 1 ≤ 2 * c + 1 := Nat.le_trans hn (by omega)
    have hnpL : (j + 1) + 1 ≤ 2 * c + 1 := by omega
    have hs := Nat.mul_le_mul hnL hnpL
    unfold lowerSixCenterMaxExponent
    exact Nat.mul_le_mul_left 2 hs
  have hsub :
      lowerSixCenterClearingExponent c -
          (2 * ((j + 1) * ((j + 1) + 1)) + 1) =
        lowerSixCenterMaxExponent c + 2 -
          2 * ((j + 1) * ((j + 1) + 1)) := by
    unfold lowerSixCenterClearingExponent
    omega
  rw [hsub] at hterm
  exact hterm

/-- The terminal integer mode reaches the maximal exponent exactly, leaving
only the three denominator powers reserved for the cubic profile. -/
theorem recovery_terminalTerm_cleared (k c : Nat) :
    qpow (Q'.ofNat (k + 2)) (lowerSixCenterClearingExponent c) *
        (Q'.ofNat 4 *
          integerThetaTerm (harmW k) (2 * c + 1)) ≈
      (Q'.ofNat (4 * ((2 * c + 1) * (2 * c + 1))) *
        qpow (Q'.ofNat (k + 1)) (lowerSixCenterMaxExponent c)) *
        qpow (Q'.ofNat (k + 2)) 3 := by
  let D := Q'.ofNat (k + 2)
  let R := Q'.ofNat (k + 1)
  let n := 2 * c + 1
  let M := lowerSixCenterMaxExponent c
  let L := lowerSixCenterClearingExponent c
  have heq : 2 * (n * n) = M := by
    dsimp only [n, M]
    rfl
  have he : 2 * (n * n) ≤ L := by
    rw [heq]
    dsimp only [L, M]
    unfold lowerSixCenterClearingExponent
    omega
  have hterm := recovery_integerThetaTerm_cleared k L n he
  rw [heq] at hterm
  have hsub : L - M = 3 := by
    dsimp only [L]
    unfold lowerSixCenterClearingExponent
    omega
  rw [hsub] at hterm
  change
    qpow D L * (Q'.ofNat 4 * integerThetaTerm (harmW k) n) ≈
      (Q'.ofNat (4 * (n * n)) * qpow R M) * qpow D 3
  refine Q'.eqv_trans _
    (Q'.ofNat 4 *
      (qpow D L * integerThetaTerm (harmW k) n)) _
    (by recovery_clear_ring) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 4 *
      ((Q'.ofNat (n * n) * qpow R M) * qpow D 3)) _
    (Q'.mul_eqv_congr_left _ _ _ hterm) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat 4 * Q'.ofNat (n * n)) *
      qpow R M * qpow D 3) _
    (by recovery_clear_ring) ?_
  exact Q'.mul_eqv_congr_right _ _ (qpow D 3)
    (Q'.mul_eqv_congr_right _ _ (qpow R M)
      (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 4 (n * n))))

private theorem recovery_sparse_scale_algebra
    (P A B E : Q') :
    P * (A + -(Q'.ofNat 8 * B) + Q'.ofNat 4 * E) ≈
      P * A + -(Q'.ofNat 8 * (P * B)) + P * (Q'.ofNat 4 * E) := by
  recovery_clear_ring

/-- Main raw-to-polynomial coordinate equivalence for the sparse fixed-center
slack.  The clearing exponent is large enough for every summand by the two
range proofs above, so every natural subtraction on the right is genuine. -/
theorem lowerSixFixedCenterSparseSlack_cleared (k c : Nat) :
    qpow (Q'.ofNat (k + 2)) (lowerSixCenterClearingExponent c) *
        lowerSixFixedCenterSparseSlack k c ≈
      lowerSixClearedCenterSlack (k + 2) c := by
  let P := qpow (Q'.ofNat (k + 2))
    (lowerSixCenterClearingExponent c)
  let C := qpow ((1 : Q') + harmW k) 3 +
    -(Q'.ofNat 6 * (harmU k * harmU k))
  let I := lowerSixFixedIntegerMass k c
  let B := harmW k * lowerSixFixedHalfMass k c
  let E := integerThetaTerm (harmW k) (2 * c + 1)
  let intPart := finSum (fun j =>
    let n := j + 1
    let e := 2 * (n * n)
    ((lowerSixCenterCubicNumerator (k + 2) * Q'.ofNat (n * n)) *
      qpow (Q'.ofNat (k + 1)) e) *
      qpow (Q'.ofNat (k + 2))
        (lowerSixCenterMaxExponent c - e)) (2 * c)
  let halfPart := finSum (fun j =>
    let n := j + 1
    let e := 2 * (n * (n + 1))
    (Q'.ofNat (n * (n + 1)) *
      qpow (Q'.ofNat (k + 1)) (e + 1)) *
      qpow (Q'.ofNat (k + 2))
        (lowerSixCenterMaxExponent c + 2 - e)) (2 * c)
  let terminal :=
    (Q'.ofNat (4 * ((2 * c + 1) * (2 * c + 1))) *
      qpow (Q'.ofNat (k + 1)) (lowerSixCenterMaxExponent c)) *
      qpow (Q'.ofNat (k + 2)) 3
  have hI : P * (C * I) ≈ intPart := by
    exact recovery_integerBlock_cleared k c
  have hB : P * B ≈ halfPart := by
    exact recovery_halfBlock_cleared k c
  have hE : P * (Q'.ofNat 4 * E) ≈ terminal := by
    exact recovery_terminalTerm_cleared k c
  unfold lowerSixFixedCenterSparseSlack lowerSixClearedCenterSlack
  have hpred : k + 2 - 1 = k + 1 := by omega
  rw [hpred]
  change P * (C * I + -(Q'.ofNat 8 * B) + Q'.ofNat 4 * E) ≈
    intPart + -(Q'.ofNat 8 * halfPart) + terminal
  refine Q'.eqv_trans _
    (P * (C * I) + -(Q'.ofNat 8 * (P * B)) +
      P * (Q'.ofNat 4 * E)) _
    (recovery_sparse_scale_algebra P (C * I) B E) ?_
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr' hI
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 8) _ _ hB)))
    hE

/-! ## Raw-drop coordinate equivalences and sign transport -/

private theorem recovery_drop_scale_algebra (A B X Y : Q') :
    (A * B) * (X + -Y) ≈ B * (A * X) + -(A * (B * Y)) := by
  recovery_clear_ring

/-- Exact common-denominator equivalence for a consecutive same-center drop.
It is algebraically valid for every `k,c`; the physical center-cell condition
is needed only by the later monotonicity theorem. -/
theorem lowerSixFixedCenterDrop_cleared (k c : Nat) :
    (qpow (Q'.ofNat (k + 2)) (lowerSixCenterClearingExponent c) *
      qpow (Q'.ofNat (k + 3)) (lowerSixCenterClearingExponent c)) *
        lowerSixFixedCenterDrop k c ≈
      lowerSixWithinCellClearedDrop (k + 2) c := by
  let A := qpow (Q'.ofNat (k + 2))
    (lowerSixCenterClearingExponent c)
  let B := qpow (Q'.ofNat (k + 3))
    (lowerSixCenterClearingExponent c)
  let X := lowerSixFixedCenterSparseSlack k c
  let Y := lowerSixFixedCenterSparseSlack (k + 1) c
  let PX := lowerSixClearedCenterSlack (k + 2) c
  let PY := lowerSixClearedCenterSlack (k + 3) c
  have hX : A * X ≈ PX := lowerSixFixedCenterSparseSlack_cleared k c
  have hY : B * Y ≈ PY := by
    have h := lowerSixFixedCenterSparseSlack_cleared (k + 1) c
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  unfold lowerSixFixedCenterDrop lowerSixWithinCellClearedDrop
  change (A * B) * (X + -Y) ≈ B * PX + -(A * PY)
  refine Q'.eqv_trans _ (B * (A * X) + -(A * (B * Y))) _
    (recovery_drop_scale_algebra A B X Y) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left B _ _ hX)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left A _ _ hY))

/-- A nonnegative cleared within-cell polynomial implies the original rational
drop is nonnegative; both denominator powers are cancelled using strict
positivity, never by classical field normalization. -/
theorem lowerSixFixedCenterDrop_nonnegative_of_cleared
    (k c : Nat)
    (h : (0 : Q') ≤ lowerSixWithinCellClearedDrop (k + 2) c) :
    (0 : Q') ≤ lowerSixFixedCenterDrop k c := by
  let A := qpow (Q'.ofNat (k + 2))
    (lowerSixCenterClearingExponent c)
  let B := qpow (Q'.ofNat (k + 3))
    (lowerSixCenterClearingExponent c)
  have hA : (0 : Q') < A := by
    apply qpow_pos
    exact Q'.ofNat_succ_pos (k + 1)
  have hB : (0 : Q') < B := by
    apply qpow_pos
    exact Q'.ofNat_succ_pos (k + 2)
  have hscale := lowerSixFixedCenterDrop_cleared k c
  have hmul : (0 : Q') ≤ (A * B) * lowerSixFixedCenterDrop k c :=
    Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.eqv_symm hscale))
  exact Q'.nonneg_of_mul_pos (Q'.mul_pos hA hB) hmul

/-- Every positive natural denominator has a strictly positive clearing
factor.  This is the sign-cancellation guard used by all raw-to-cleared
transports below. -/
theorem recovery_clearing_factor_pos (D L : Nat) (hD : 0 < D) :
    (0 : Q') < qpow (Q'.ofNat D) L := by
  apply qpow_pos
  rcases D with _ | D
  · omega
  · exact Q'.ofNat_succ_pos D

private theorem recovery_even_scale_den (m : Nat) (hm : 1 ≤ m) :
    lowerSixEvenCenterRightScale m + 2 =
      lowerSixEvenCenterRightDen m := by
  unfold lowerSixEvenCenterRightScale lowerSixEvenCenterRightDen
  have hmm : 1 ≤ m * m := Nat.mul_le_mul hm hm
  have hquad : 2 ≤ 2 * m * m := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hmm
  omega

private theorem recovery_odd_scale_den (m : Nat) (hm : 1 ≤ m) :
    lowerSixOddCenterRightScale m + 2 =
      lowerSixOddCenterRightDen m := by
  unfold lowerSixOddCenterRightScale lowerSixOddCenterRightDen
  omega

/-- Exact common-denominator identity for an even-center to odd-center right
endpoint transition. -/
theorem lowerSixEvenOddEndpointDrop_cleared (m : Nat) (hm : 1 ≤ m) :
    (qpow (Q'.ofNat (lowerSixEvenCenterRightDen m))
        (lowerSixCenterClearingExponent (2 * m)) *
      qpow (Q'.ofNat (lowerSixOddCenterRightDen m))
        (lowerSixCenterClearingExponent (2 * m + 1))) *
      lowerSixEvenOddEndpointDrop m ≈
        lowerSixEvenOddEndpointClearedDrop m := by
  let De := lowerSixEvenCenterRightDen m
  let Do := lowerSixOddCenterRightDen m
  let Le := lowerSixCenterClearingExponent (2 * m)
  let Lo := lowerSixCenterClearingExponent (2 * m + 1)
  let A := qpow (Q'.ofNat De) Le
  let B := qpow (Q'.ofNat Do) Lo
  let X := lowerSixFixedCenterSparseSlack
    (lowerSixEvenCenterRightScale m) (2 * m)
  let Y := lowerSixFixedCenterSparseSlack
    (lowerSixOddCenterRightScale m) (2 * m + 1)
  let PX := lowerSixClearedCenterSlack De (2 * m)
  let PY := lowerSixClearedCenterSlack Do (2 * m + 1)
  have hX : A * X ≈ PX := by
    have h := lowerSixFixedCenterSparseSlack_cleared
      (lowerSixEvenCenterRightScale m) (2 * m)
    rw [recovery_even_scale_den m hm] at h
    exact h
  have hY : B * Y ≈ PY := by
    have h := lowerSixFixedCenterSparseSlack_cleared
      (lowerSixOddCenterRightScale m) (2 * m + 1)
    rw [recovery_odd_scale_den m hm] at h
    exact h
  unfold lowerSixEvenOddEndpointDrop lowerSixEvenOddEndpointClearedDrop
  change (A * B) * (X + -Y) ≈ B * PX + -(A * PY)
  refine Q'.eqv_trans _ (B * (A * X) + -(A * (B * Y))) _
    (recovery_drop_scale_algebra A B X Y) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left B _ _ hX)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left A _ _ hY))

theorem lowerSixEvenOddEndpointDrop_nonnegative_of_cleared
    (m : Nat) (hm : 1 ≤ m)
    (h : (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop m) :
    (0 : Q') ≤ lowerSixEvenOddEndpointDrop m := by
  let De := lowerSixEvenCenterRightDen m
  let Do := lowerSixOddCenterRightDen m
  let A := qpow (Q'.ofNat De) (lowerSixCenterClearingExponent (2 * m))
  let B := qpow (Q'.ofNat Do) (lowerSixCenterClearingExponent (2 * m + 1))
  have hDe : 0 < De := by
    dsimp only [De]
    unfold lowerSixEvenCenterRightDen
    omega
  have hDo : 0 < Do := by
    dsimp only [Do]
    unfold lowerSixOddCenterRightDen
    omega
  have hA : (0 : Q') < A := recovery_clearing_factor_pos De _ hDe
  have hB : (0 : Q') < B := recovery_clearing_factor_pos Do _ hDo
  have hscale := lowerSixEvenOddEndpointDrop_cleared m hm
  have hmul : (0 : Q') ≤ (A * B) * lowerSixEvenOddEndpointDrop m :=
    Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_symm hscale))
  exact Q'.nonneg_of_mul_pos (Q'.mul_pos hA hB) hmul

/-- Exact common-denominator identity for an odd-center to the next even-center
right endpoint transition. -/
theorem lowerSixOddEvenEndpointDrop_cleared (m : Nat) (hm : 1 ≤ m) :
    (qpow (Q'.ofNat (lowerSixOddCenterRightDen m))
        (lowerSixCenterClearingExponent (2 * m + 1)) *
      qpow (Q'.ofNat (lowerSixEvenCenterRightDen (m + 1)))
        (lowerSixCenterClearingExponent (2 * (m + 1)))) *
      lowerSixOddEvenEndpointDrop m ≈
        lowerSixOddEvenEndpointClearedDrop m := by
  let Do := lowerSixOddCenterRightDen m
  let De := lowerSixEvenCenterRightDen (m + 1)
  let Lo := lowerSixCenterClearingExponent (2 * m + 1)
  let Le := lowerSixCenterClearingExponent (2 * (m + 1))
  let A := qpow (Q'.ofNat Do) Lo
  let B := qpow (Q'.ofNat De) Le
  let X := lowerSixFixedCenterSparseSlack
    (lowerSixOddCenterRightScale m) (2 * m + 1)
  let Y := lowerSixFixedCenterSparseSlack
    (lowerSixEvenCenterRightScale (m + 1)) (2 * (m + 1))
  let PX := lowerSixClearedCenterSlack Do (2 * m + 1)
  let PY := lowerSixClearedCenterSlack De (2 * (m + 1))
  have hX : A * X ≈ PX := by
    have h := lowerSixFixedCenterSparseSlack_cleared
      (lowerSixOddCenterRightScale m) (2 * m + 1)
    rw [recovery_odd_scale_den m hm] at h
    exact h
  have hY : B * Y ≈ PY := by
    have h := lowerSixFixedCenterSparseSlack_cleared
      (lowerSixEvenCenterRightScale (m + 1)) (2 * (m + 1))
    rw [recovery_even_scale_den (m + 1) (by omega)] at h
    exact h
  unfold lowerSixOddEvenEndpointDrop lowerSixOddEvenEndpointClearedDrop
  change (A * B) * (X + -Y) ≈ B * PX + -(A * PY)
  refine Q'.eqv_trans _ (B * (A * X) + -(A * (B * Y))) _
    (recovery_drop_scale_algebra A B X Y) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left B _ _ hX)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left A _ _ hY))

theorem lowerSixOddEvenEndpointDrop_nonnegative_of_cleared
    (m : Nat) (hm : 1 ≤ m)
    (h : (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop m) :
    (0 : Q') ≤ lowerSixOddEvenEndpointDrop m := by
  let Do := lowerSixOddCenterRightDen m
  let De := lowerSixEvenCenterRightDen (m + 1)
  let A := qpow (Q'.ofNat Do) (lowerSixCenterClearingExponent (2 * m + 1))
  let B := qpow (Q'.ofNat De)
    (lowerSixCenterClearingExponent (2 * (m + 1)))
  have hDo : 0 < Do := by
    dsimp only [Do]
    unfold lowerSixOddCenterRightDen
    omega
  have hDe : 0 < De := by
    dsimp only [De]
    unfold lowerSixEvenCenterRightDen
    omega
  have hA : (0 : Q') < A := recovery_clearing_factor_pos Do _ hDo
  have hB : (0 : Q') < B := recovery_clearing_factor_pos De _ hDe
  have hscale := lowerSixOddEvenEndpointDrop_cleared m hm
  have hmul : (0 : Q') ≤ (A * B) * lowerSixOddEvenEndpointDrop m :=
    Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_symm hscale))
  exact Q'.nonneg_of_mul_pos (Q'.mul_pos hA hB) hmul

#print axioms recovery_harmU_mul_den
#print axioms recovery_harmW_mul_den
#print axioms recovery_clear_harmW_power
#print axioms recovery_clear_harmU_power
#print axioms recovery_cubic_profile_cleared
#print axioms recovery_integerThetaTerm_cleared
#print axioms recovery_weightedHalfThetaTerm_cleared
#print axioms recovery_profileIntegerThetaTerm_cleared
#print axioms recovery_integerBlock_cleared
#print axioms recovery_halfBlock_cleared
#print axioms recovery_terminalTerm_cleared
#print axioms lowerSixFixedCenterSparseSlack_cleared
#print axioms lowerSixFixedCenterDrop_cleared
#print axioms lowerSixFixedCenterDrop_nonnegative_of_cleared
#print axioms recovery_clearing_factor_pos
#print axioms lowerSixEvenOddEndpointDrop_cleared
#print axioms lowerSixEvenOddEndpointDrop_nonnegative_of_cleared
#print axioms lowerSixOddEvenEndpointDrop_cleared
#print axioms lowerSixOddEvenEndpointDrop_nonnegative_of_cleared

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryClearing
