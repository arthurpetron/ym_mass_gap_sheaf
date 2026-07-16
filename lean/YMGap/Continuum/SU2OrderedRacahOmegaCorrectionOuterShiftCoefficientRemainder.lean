/-
# Coefficient remainder for the two ordered Racah outer shifts

The carrier transport is common to the first/second and first/third `N-2`
families, but the correction coefficients are not copied coefficientwise.
This file begins the exact remainder calculation with the upper coefficient:
both shifted directions have one common positive denominator and hence one
common upper coefficient, proved by constructive cancellation.
-/

import YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftTransport

namespace YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

private theorem ofNat_pos_of_pos (n : Nat) (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

private theorem scaled_difference (D X Y NX NY : Q')
    (hX : D * X ≈ NX) (hY : D * Y ≈ NY) :
    D * (X + -Y) ≈ NX + -NY := by
  refine Q'.eqv_trans _ (D * X + -(D * Y)) _ (by ring_qeqv) ?_
  exact Q'.add_eqv_congr' hX (Q'.neg_eqv_congr _ _ hY)

private theorem cross_scaled_difference (D E X Y NX NY : Q')
    (hX : D * X ≈ NX) (hY : E * Y ≈ NY) :
    (D * E) * (X + -Y) ≈ E * NX + -(D * NY) := by
  refine Q'.eqv_trans _ (E * (D * X) + -(D * (E * Y))) _
    (by ring_qeqv) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left E _ _ hX)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left D _ _ hY))

/-- The first/second and first/third shifts have exactly the same upper
correction coefficient.  The proof does not divide: it identifies the common
scaled numerator and cancels the explicitly positive common denominator. -/
theorem upperCorrectionCoefficient_firstSecond_eq_firstThird
    {a b c d : Nat} (q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hnext : qp.p = q.p + 1)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hqb : q.p < b) (hqc : q.p < c)
    (hpb : qp.p < b) (hpc : qp.p < c)
    (hr : 0 < q.r) (hrp : 0 < qp.r) :
    omegaCorrectionUpperCoefficient (a - 1) (b - 1) c d q.p ≈
      omegaCorrectionUpperCoefficient (a - 1) b (c - 1) d q.p := by
  let qs := reduceFirstSecondRightChannel q ha hb hqb hr
  let qps := reduceFirstSecondRightChannel qp ha hb hpb hrp
  let qt := reduceFirstThirdRightChannel q ha hc hqc hr
  let qpt := reduceFirstThirdRightChannel qp ha hc hpc hrp
  have hps : 0 < qs.p := by
    dsimp only [qs, reduceFirstSecondRightChannel]
    exact hp
  have hpt : 0 < qt.p := by
    dsimp only [qt, reduceFirstThirdRightChannel]
    exact hp
  have hnexts : qps.p = qs.p + 1 := by
    dsimp only [qps, qs, reduceFirstSecondRightChannel]
    exact hnext
  have hnextt : qpt.p = qt.p + 1 := by
    dsimp only [qpt, qt, reduceFirstThirdRightChannel]
    exact hnext
  have hs := omegaCorrectionUpperCoefficient_closed qs qps hps hnexts
  have ht := omegaCorrectionUpperCoefficient_closed qt qpt hpt hnextt
  have hfst : qs.intermediate = qt.intermediate := by
    rw [reduceFirstSecondRightChannel_intermediate,
      reduceFirstThirdRightChannel_intermediate]
  have hrst : qs.r = qt.r := by
    rfl
  rw [hfst, hrst] at hs
  have hscaled :
      Q'.ofNat (qt.intermediate * (qt.intermediate + 1)) *
          omegaCorrectionUpperCoefficient (a - 1) (b - 1) c d q.p ≈
        Q'.ofNat (qt.intermediate * (qt.intermediate + 1)) *
          omegaCorrectionUpperCoefficient (a - 1) b (c - 1) d q.p := by
    exact Q'.eqv_trans _ _ _ (by
      simpa only [qs, reduceFirstSecondRightChannel] using hs)
      (Q'.eqv_symm (by
        simpa only [qt, reduceFirstThirdRightChannel] using ht))
  have hqpmin := Nat.le_min.mp qp.p_le
  have hinter : 0 < qt.intermediate := by
    dsimp only [qt, reduceFirstThirdRightChannel,
      FixedRightCGChannel.intermediate]
    omega
  have hdenNat : 0 < qt.intermediate * (qt.intermediate + 1) :=
    Nat.mul_pos hinter (by omega)
  exact Q'.mul_left_cancel_of_pos (ofNat_pos_of_pos _ hdenNat) hscaled

/-- In contrast with the upper row, the lower shifted coefficients have a
nonzero directional remainder.  Clearing their one common positive
denominator gives the exact difference of the two natural numerators. -/
theorem lowerCorrectionCoefficient_shift_difference_scaled
    {a b c d : Nat} (qm q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmb : qm.p < b) (hmc : qm.p < c)
    (hqb : q.p < b) (hqc : q.p < c)
    (hrm : 0 < qm.r) (hr : 0 < q.r) :
    let qt := reduceFirstThirdRightChannel q ha hc hqc hr
    Q'.ofNat ((qt.intermediate + 2) * (qt.intermediate + 1)) *
        (omegaCorrectionLowerCoefficient (a - 1) (b - 1) c d q.p +
          -(omegaCorrectionLowerCoefficient (a - 1) b (c - 1) d q.p)) ≈
      Q'.ofNat
          (((b - 1) - q.p + 1) * (c - q.p + 1) *
            (qt.intermediate - qt.r + 1)) +
        -(Q'.ofNat
          ((b - q.p + 1) * ((c - 1) - q.p + 1) *
            (qt.intermediate - qt.r + 1))) := by
  dsimp only
  let qms := reduceFirstSecondRightChannel qm ha hb hmb hrm
  let qs := reduceFirstSecondRightChannel q ha hb hqb hr
  let qmt := reduceFirstThirdRightChannel qm ha hc hmc hrm
  let qt := reduceFirstThirdRightChannel q ha hc hqc hr
  have hps : 0 < qs.p := by
    dsimp only [qs, reduceFirstSecondRightChannel]
    exact hp
  have hpt : 0 < qt.p := by
    dsimp only [qt, reduceFirstThirdRightChannel]
    exact hp
  have hprevs : qs.p = qms.p + 1 := by
    dsimp only [qms, qs, reduceFirstSecondRightChannel]
    exact hprev
  have hprevt : qt.p = qmt.p + 1 := by
    dsimp only [qmt, qt, reduceFirstThirdRightChannel]
    exact hprev
  have hs := omegaCorrectionLowerCoefficient_closed qms qs hps hprevs
  have ht := omegaCorrectionLowerCoefficient_closed qmt qt hpt hprevt
  have hfst : qs.intermediate = qt.intermediate := by
    rw [reduceFirstSecondRightChannel_intermediate,
      reduceFirstThirdRightChannel_intermediate]
  have hrst : qs.r = qt.r := by rfl
  rw [hfst, hrst] at hs
  exact scaled_difference _ _ _ _ _
    (by simpa only [qs, reduceFirstSecondRightChannel] using hs)
    (by simpa only [qt, reduceFirstThirdRightChannel] using ht)

/-- The diagonal shifted coefficients have the same explicitly derived
denominator.  Clearing it leaves exactly the difference of their integer
numerators; no coefficientwise invariance is assumed. -/
theorem diagonalCorrectionCoefficient_shift_difference_scaled
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hqb : q.p < b) (hqc : q.p < c) (hr : 0 < q.r) :
    let qt := reduceFirstThirdRightChannel q ha hc hqc hr
    Q'.ofNat (omegaCorrectionDiagonalDenominator qt.intermediate) *
        (omegaCorrectionDiagonalCoefficient (a - 1) (b - 1) c d q.p +
          -(omegaCorrectionDiagonalCoefficient (a - 1) b (c - 1) d q.p)) ≈
      Q'.ofInt
          (omegaCorrectionDiagonalNumerator
            (a - 1) (b - 1) c d qt.intermediate) +
        -(Q'.ofInt
          (omegaCorrectionDiagonalNumerator
            (a - 1) b (c - 1) d qt.intermediate)) := by
  dsimp only
  let qs := reduceFirstSecondRightChannel q ha hb hqb hr
  let qt := reduceFirstThirdRightChannel q ha hc hqc hr
  have hps : 0 < qs.p := by
    dsimp only [qs, reduceFirstSecondRightChannel]
    exact hp
  have hpt : 0 < qt.p := by
    dsimp only [qt, reduceFirstThirdRightChannel]
    exact hp
  have hs := omegaCorrectionDiagonalCoefficient_closed qs hps
  have ht := omegaCorrectionDiagonalCoefficient_closed qt hpt
  have hfst : qs.intermediate = qt.intermediate := by
    rw [reduceFirstSecondRightChannel_intermediate,
      reduceFirstThirdRightChannel_intermediate]
  rw [hfst] at hs
  exact scaled_difference _ _ _ _ _
    (by simpa only [qs, reduceFirstSecondRightChannel] using hs)
    (by simpa only [qt, reduceFirstThirdRightChannel] using ht)

/-- The upper coefficient mismatch between the current family and the
first/second shifted family, with both independently derived denominators
cleared.  This is the exact nonzero mismatch fenced in the transport file. -/
theorem upperCorrectionCoefficient_current_firstSecond_shift_difference_scaled
    {a b c d : Nat} (q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hnext : qp.p = q.p + 1)
    (ha : 0 < a) (hb : 0 < b)
    (hqb : q.p < b) (hpb : qp.p < b)
    (hr : 0 < q.r) (hrp : 0 < qp.r) :
    let qs := reduceFirstSecondRightChannel q ha hb hqb hr
    (Q'.ofNat (q.intermediate * (q.intermediate + 1)) *
        Q'.ofNat (qs.intermediate * (qs.intermediate + 1))) *
      (omegaCorrectionUpperCoefficient a b c d q.p +
        -(omegaCorrectionUpperCoefficient (a - 1) (b - 1) c d q.p)) ≈
      Q'.ofNat (qs.intermediate * (qs.intermediate + 1)) *
          Q'.ofNat
            (q.r * (a - q.r + 1) *
              (a + q.intermediate - q.r + 1)) +
        -(Q'.ofNat (q.intermediate * (q.intermediate + 1)) *
          Q'.ofNat
            (qs.r * ((a - 1) - qs.r + 1) *
              ((a - 1) + qs.intermediate - qs.r + 1))) := by
  dsimp only
  let qs := reduceFirstSecondRightChannel q ha hb hqb hr
  let qps := reduceFirstSecondRightChannel qp ha hb hpb hrp
  have hps : 0 < qs.p := by
    dsimp only [qs, reduceFirstSecondRightChannel]
    exact hp
  have hnexts : qps.p = qs.p + 1 := by
    dsimp only [qps, qs, reduceFirstSecondRightChannel]
    exact hnext
  have hcurrent := omegaCorrectionUpperCoefficient_closed q qp hp hnext
  have hshift := omegaCorrectionUpperCoefficient_closed qs qps hps hnexts
  exact cross_scaled_difference _ _ _ _ _ _ hcurrent
    (by simpa only [qs, reduceFirstSecondRightChannel] using hshift)

/-- The lower coefficient mismatch between the current family and the
first/second shifted family, after clearing the two adjacent outer-label
denominators. -/
theorem lowerCorrectionCoefficient_current_firstSecond_shift_difference_scaled
    {a b c d : Nat} (qm q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (ha : 0 < a) (hb : 0 < b)
    (hmb : qm.p < b) (hqb : q.p < b)
    (hrm : 0 < qm.r) (hr : 0 < q.r) :
    let qs := reduceFirstSecondRightChannel q ha hb hqb hr
    (Q'.ofNat ((q.intermediate + 2) * (q.intermediate + 1)) *
        Q'.ofNat ((qs.intermediate + 2) * (qs.intermediate + 1))) *
      (omegaCorrectionLowerCoefficient a b c d q.p +
        -(omegaCorrectionLowerCoefficient (a - 1) (b - 1) c d q.p)) ≈
      Q'.ofNat ((qs.intermediate + 2) * (qs.intermediate + 1)) *
          Q'.ofNat
            ((b - q.p + 1) * (c - q.p + 1) *
              (q.intermediate - q.r + 1)) +
        -(Q'.ofNat ((q.intermediate + 2) * (q.intermediate + 1)) *
          Q'.ofNat
            (((b - 1) - q.p + 1) * (c - q.p + 1) *
              (qs.intermediate - qs.r + 1))) := by
  dsimp only
  let qms := reduceFirstSecondRightChannel qm ha hb hmb hrm
  let qs := reduceFirstSecondRightChannel q ha hb hqb hr
  have hps : 0 < qs.p := by
    dsimp only [qs, reduceFirstSecondRightChannel]
    exact hp
  have hprevs : qs.p = qms.p + 1 := by
    dsimp only [qms, qs, reduceFirstSecondRightChannel]
    exact hprev
  have hcurrent := omegaCorrectionLowerCoefficient_closed qm q hp hprev
  have hshift := omegaCorrectionLowerCoefficient_closed qms qs hps hprevs
  exact cross_scaled_difference _ _ _ _ _ _ hcurrent
    (by simpa only [qs, reduceFirstSecondRightChannel] using hshift)

/-- The diagonal coefficient mismatch between the current family and the
first/second shifted family, with the removable zero-label denominators kept
inside their proved total definitions. -/
theorem diagonalCorrectionCoefficient_current_firstSecond_shift_difference_scaled
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p)
    (ha : 0 < a) (hb : 0 < b)
    (hqb : q.p < b) (hr : 0 < q.r) :
    let qs := reduceFirstSecondRightChannel q ha hb hqb hr
    (Q'.ofNat (omegaCorrectionDiagonalDenominator q.intermediate) *
        Q'.ofNat (omegaCorrectionDiagonalDenominator qs.intermediate)) *
      (omegaCorrectionDiagonalCoefficient a b c d q.p +
        -(omegaCorrectionDiagonalCoefficient
          (a - 1) (b - 1) c d q.p)) ≈
      Q'.ofNat (omegaCorrectionDiagonalDenominator qs.intermediate) *
          Q'.ofInt
            (omegaCorrectionDiagonalNumerator a b c d q.intermediate) +
        -(Q'.ofNat (omegaCorrectionDiagonalDenominator q.intermediate) *
          Q'.ofInt
            (omegaCorrectionDiagonalNumerator
              (a - 1) (b - 1) c d qs.intermediate)) := by
  dsimp only
  let qs := reduceFirstSecondRightChannel q ha hb hqb hr
  have hps : 0 < qs.p := by
    dsimp only [qs, reduceFirstSecondRightChannel]
    exact hp
  have hcurrent := omegaCorrectionDiagonalCoefficient_closed q hp
  have hshift := omegaCorrectionDiagonalCoefficient_closed qs hps
  exact cross_scaled_difference _ _ _ _ _ _ hcurrent
    (by simpa only [qs, reduceFirstSecondRightChannel] using hshift)

/-- The corresponding exact upper mismatch for the first/third shifted
family.  Together with `upperCorrectionCoefficient_firstSecond_eq_firstThird`
this records both the common shifted value and its change from the parent. -/
theorem upperCorrectionCoefficient_current_firstThird_shift_difference_scaled
    {a b c d : Nat} (q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hnext : qp.p = q.p + 1)
    (ha : 0 < a) (hc : 0 < c)
    (hqc : q.p < c) (hpc : qp.p < c)
    (hr : 0 < q.r) (hrp : 0 < qp.r) :
    let qt := reduceFirstThirdRightChannel q ha hc hqc hr
    (Q'.ofNat (q.intermediate * (q.intermediate + 1)) *
        Q'.ofNat (qt.intermediate * (qt.intermediate + 1))) *
      (omegaCorrectionUpperCoefficient a b c d q.p +
        -(omegaCorrectionUpperCoefficient (a - 1) b (c - 1) d q.p)) ≈
      Q'.ofNat (qt.intermediate * (qt.intermediate + 1)) *
          Q'.ofNat
            (q.r * (a - q.r + 1) *
              (a + q.intermediate - q.r + 1)) +
        -(Q'.ofNat (q.intermediate * (q.intermediate + 1)) *
          Q'.ofNat
            (qt.r * ((a - 1) - qt.r + 1) *
              ((a - 1) + qt.intermediate - qt.r + 1))) := by
  dsimp only
  let qt := reduceFirstThirdRightChannel q ha hc hqc hr
  let qpt := reduceFirstThirdRightChannel qp ha hc hpc hrp
  have hpt : 0 < qt.p := by
    dsimp only [qt, reduceFirstThirdRightChannel]
    exact hp
  have hnextt : qpt.p = qt.p + 1 := by
    dsimp only [qpt, qt, reduceFirstThirdRightChannel]
    exact hnext
  have hcurrent := omegaCorrectionUpperCoefficient_closed q qp hp hnext
  have hshift := omegaCorrectionUpperCoefficient_closed qt qpt hpt hnextt
  exact cross_scaled_difference _ _ _ _ _ _ hcurrent
    (by simpa only [qt, reduceFirstThirdRightChannel] using hshift)

/-- The corresponding exact lower mismatch for the first/third shifted
family. -/
theorem lowerCorrectionCoefficient_current_firstThird_shift_difference_scaled
    {a b c d : Nat} (qm q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (ha : 0 < a) (hc : 0 < c)
    (hmc : qm.p < c) (hqc : q.p < c)
    (hrm : 0 < qm.r) (hr : 0 < q.r) :
    let qt := reduceFirstThirdRightChannel q ha hc hqc hr
    (Q'.ofNat ((q.intermediate + 2) * (q.intermediate + 1)) *
        Q'.ofNat ((qt.intermediate + 2) * (qt.intermediate + 1))) *
      (omegaCorrectionLowerCoefficient a b c d q.p +
        -(omegaCorrectionLowerCoefficient (a - 1) b (c - 1) d q.p)) ≈
      Q'.ofNat ((qt.intermediate + 2) * (qt.intermediate + 1)) *
          Q'.ofNat
            ((b - q.p + 1) * (c - q.p + 1) *
              (q.intermediate - q.r + 1)) +
        -(Q'.ofNat ((q.intermediate + 2) * (q.intermediate + 1)) *
          Q'.ofNat
            ((b - q.p + 1) * ((c - 1) - q.p + 1) *
              (qt.intermediate - qt.r + 1))) := by
  dsimp only
  let qmt := reduceFirstThirdRightChannel qm ha hc hmc hrm
  let qt := reduceFirstThirdRightChannel q ha hc hqc hr
  have hpt : 0 < qt.p := by
    dsimp only [qt, reduceFirstThirdRightChannel]
    exact hp
  have hprevt : qt.p = qmt.p + 1 := by
    dsimp only [qmt, qt, reduceFirstThirdRightChannel]
    exact hprev
  have hcurrent := omegaCorrectionLowerCoefficient_closed qm q hp hprev
  have hshift := omegaCorrectionLowerCoefficient_closed qmt qt hpt hprevt
  exact cross_scaled_difference _ _ _ _ _ _ hcurrent
    (by simpa only [qt, reduceFirstThirdRightChannel] using hshift)

/-- The corresponding exact diagonal mismatch for the first/third shifted
family. -/
theorem diagonalCorrectionCoefficient_current_firstThird_shift_difference_scaled
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p)
    (ha : 0 < a) (hc : 0 < c)
    (hqc : q.p < c) (hr : 0 < q.r) :
    let qt := reduceFirstThirdRightChannel q ha hc hqc hr
    (Q'.ofNat (omegaCorrectionDiagonalDenominator q.intermediate) *
        Q'.ofNat (omegaCorrectionDiagonalDenominator qt.intermediate)) *
      (omegaCorrectionDiagonalCoefficient a b c d q.p +
        -(omegaCorrectionDiagonalCoefficient
          (a - 1) b (c - 1) d q.p)) ≈
      Q'.ofNat (omegaCorrectionDiagonalDenominator qt.intermediate) *
          Q'.ofInt
            (omegaCorrectionDiagonalNumerator a b c d q.intermediate) +
        -(Q'.ofNat (omegaCorrectionDiagonalDenominator q.intermediate) *
          Q'.ofInt
            (omegaCorrectionDiagonalNumerator
              (a - 1) b (c - 1) d qt.intermediate)) := by
  dsimp only
  let qt := reduceFirstThirdRightChannel q ha hc hqc hr
  have hpt : 0 < qt.p := by
    dsimp only [qt, reduceFirstThirdRightChannel]
    exact hp
  have hcurrent := omegaCorrectionDiagonalCoefficient_closed q hp
  have hshift := omegaCorrectionDiagonalCoefficient_closed qt hpt
  exact cross_scaled_difference _ _ _ _ _ _ hcurrent
    (by simpa only [qt, reduceFirstThirdRightChannel] using hshift)

end YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder.upperCorrectionCoefficient_firstSecond_eq_firstThird
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder.lowerCorrectionCoefficient_shift_difference_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder.diagonalCorrectionCoefficient_shift_difference_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder.upperCorrectionCoefficient_current_firstSecond_shift_difference_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder.lowerCorrectionCoefficient_current_firstSecond_shift_difference_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder.diagonalCorrectionCoefficient_current_firstSecond_shift_difference_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder.upperCorrectionCoefficient_current_firstThird_shift_difference_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder.lowerCorrectionCoefficient_current_firstThird_shift_difference_scaled
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder.diagonalCorrectionCoefficient_current_firstThird_shift_difference_scaled
