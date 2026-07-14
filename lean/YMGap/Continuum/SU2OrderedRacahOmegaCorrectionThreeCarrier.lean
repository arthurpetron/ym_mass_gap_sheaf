/-
# The all-label three-carrier correction target

The one-Omega commutator correction is not a single adjacent carrier.  Its
correct coefficients are the differences between the original Jacobi row at
order `p` and the reduced-label Jacobi row at order `p-1`.  This file records
that exact target and begins its all-label discharge with the upper-component
coefficient identity.
-/

import YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification

namespace YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Q'.ofInt]; ac_rfl))

private theorem mkPos_difference_one_step (K T D : Nat) (hD : 0 < D) :
    Q'.ofNat D *
        (Q'.mkPos (K * (T + 1)) D hD +
          -(Q'.mkPos (K * T) D hD)) ≈
      Q'.ofNat K := by
  unfold Q'.eqv
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, neg_num]
  push_cast
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  let X : Int := (K : Int) * ((T : Int) * ((D : Int) * (D : Int)))
  let Y : Int := (K : Int) * ((D : Int) * (D : Int))
  calc
    _ = -X + (X + Y) := by dsimp only [X, Y]; ac_rfl
    _ = Y := Int.neg_add_cancel_left X Y
    _ = _ := by dsimp only [Y]; ac_rfl

private theorem mkPos_scale_cancel (K D : Nat) (hD : 0 < D) :
    Q'.ofNat D * Q'.mkPos K D hD ≈ Q'.ofNat K := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  ac_rfl

private theorem mkPos_difference_same_den (X Y : Int) (D : Nat)
    (hD : 0 < D) :
    Q'.ofNat D *
        (Q'.mkPos X D hD + -(Q'.mkPos Y D hD)) ≈
      Q'.ofInt (X + -Y) := by
  unfold Q'.eqv Q'.ofInt
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, neg_num]
  simp only [Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg]
  ac_rfl

private theorem scale_add_neg_zero (D X Y : Q') (h : D * X ≈ Y) :
    D * (X + -(0 : Q')) ≈ Y := by
  refine Q'.eqv_trans _ (D * X) _ ?_ h
  refine Q'.mul_eqv_congr_left D _ _ ?_
  refine Q'.eqv_trans _ (X + 0) _
    (Q'.add_eqv_congr_left X _ _ (by decide)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' X)

/-- Reduced-label contribution to the lower carrier.  At `p=1` the reduced
channel has order zero, so there is no lower neighbor. -/
def reducedLowerCoefficient (a b c d p : Nat) : Q' :=
  if 1 < p then jacobiForward a (b - 1) (c - 1) d (p - 2) else 0

/-- Difference coefficient of the original lower adjacent carrier. -/
def omegaCorrectionLowerCoefficient (a b c d p : Nat) : Q' :=
  jacobiForward a b c d (p - 1) +
    -(reducedLowerCoefficient a b c d p)

/-- Difference coefficient of the original diagonal carrier. -/
def omegaCorrectionDiagonalCoefficient (a b c d p : Nat) : Q' :=
  jacobiDiagonal a b c d p +
    -(jacobiDiagonal a (b - 1) (c - 1) d (p - 1))

/-- The common denominator of the two diagonal rows.  The removable
zero-label branch has denominator two; every positive intermediate label has
the ordinary projected-Casimir denominator. -/
def omegaCorrectionDiagonalDenominator (f : Nat) : Nat :=
  if f = 0 then 2 else diagonalDen f

/-- Integer numerator of the diagonal-row difference after putting both
terms over their common denominator. -/
def omegaCorrectionDiagonalNumerator (a b c d f : Nat) : Int :=
  if f = 0 then
    (-((a * b : Nat) : Int)) + -(-((a * (b - 1) : Nat) : Int))
  else
    diagonalNum a b c d f + -diagonalNum a (b - 1) (c - 1) d f

/-- Difference coefficient of the original upper adjacent carrier. -/
def omegaCorrectionUpperCoefficient (a b c d p : Nat) : Q' :=
  jacobiBackward a b c d (p + 1) +
    -(jacobiBackward a (b - 1) (c - 1) d p)

/-- Exact pointwise statement of the all-label three-carrier correction
identity.  `qm,q,qp` are consecutive proof-carrying physical right channels. -/
def OmegaCorrectionThreeCarrierAt {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (i j l s : Nat) : Prop :=
  triRightOmegaCorrection q i j l s ≈
    omegaCorrectionLowerCoefficient a b c d q.p *
        triRight a b c d qm.intermediate
          (mono i) (mono j) (mono l) s +
      omegaCorrectionDiagonalCoefficient a b c d q.p *
        triRight a b c d q.intermediate
          (mono i) (mono j) (mono l) s +
      omegaCorrectionUpperCoefficient a b c d q.p *
        triRight a b c d qp.intermediate
          (mono i) (mono j) (mono l) s

private theorem fixedRight_rightOrderOK {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    rightOrderOK a b c d q.p = true := by
  apply (rightOrderOK_spec a b c d q.p).2
  refine ⟨q.p_le, ?_⟩
  rw [show rightLabel b c q.p = q.intermediate by rfl]
  apply (fusionOK_iff_ladder a q.intermediate d).2
  have hr := Nat.le_min.mp q.r_le
  have hd : a + q.intermediate = d + 2 * q.r := by
    have h := q.degree_eq
    unfold FixedRightCGChannel.intermediate at h ⊢
    omega
  exact ⟨q.r, hr.1, hr.2, hd⟩

private theorem reduced_rightOrderOK {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p) :
    rightOrderOK a (b - 1) (c - 1) d (q.p - 1) = true :=
  fixedRight_rightOrderOK (reducePositiveInnerRightChannel q hp)

/-- For consecutive `q,qp`, the upper correction coefficient has the simple
closed numerator obtained by subtracting the two equal-denominator backward
coefficients.  This is stated division-free. -/
theorem omegaCorrectionUpperCoefficient_closed {a b c d : Nat}
    (q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hnext : qp.p = q.p + 1) :
    Q'.ofNat (q.intermediate * (q.intermediate + 1)) *
        omegaCorrectionUpperCoefficient a b c d q.p ≈
      Q'.ofNat
        (q.r * (a - q.r + 1) *
          (a + q.intermediate - q.r + 1)) := by
  have hqmin := Nat.le_min.mp q.p_le
  have hqpmin := Nat.le_min.mp qp.p_le
  have hqr := Nat.le_min.mp q.r_le
  have hqpr := Nat.le_min.mp qp.r_le
  have hf : qp.intermediate = q.intermediate - 2 := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hdeg := q.degree_eq
  have hdeg' := qp.degree_eq
  have hr : qp.r + 1 = q.r := by
    unfold FixedRightCGChannel.intermediate at hf hdeg hdeg'
    omega
  have hinter : 2 ≤ q.intermediate := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hguard0 : 0 < q.p + 1 ∧
      rightOrderOK a b c d (q.p + 1 - 1) = true := by
    rw [show q.p + 1 - 1 = q.p by omega]
    exact ⟨by omega, fixedRight_rightOrderOK q⟩
  have hguard1 : 0 < q.p ∧
      rightOrderOK a (b - 1) (c - 1) d (q.p - 1) = true :=
    ⟨hp, reduced_rightOrderOK q hp⟩
  have hlabel0 : rightLabel b c (q.p + 1) = q.intermediate - 2 := by
    rw [← hf, ← hnext]
    rfl
  have hlabel1 : rightLabel (b - 1) (c - 1) q.p =
      q.intermediate - 2 := by
    unfold rightLabel FixedRightCGChannel.intermediate
    omega
  have houter0 : outerOrder a b c d (q.p + 1) = qp.r := by
    unfold outerOrder
    rw [show rightLabel b c (q.p + 1) = qp.intermediate by
      rw [← hnext]; rfl]
    exact fixedRight_outer_couplingOrder qp
  have houter1 : outerOrder a (b - 1) (c - 1) d q.p = qp.r := by
    unfold outerOrder
    rw [hlabel1, ← hf]
    exact fixedRight_outer_couplingOrder qp
  unfold omegaCorrectionUpperCoefficient jacobiBackward
  rw [dif_pos hguard0, dif_pos hguard1]
  unfold backwardNum backwardDen
  simp only [hlabel0, hlabel1, houter0, houter1]
  simp only [show qp.r + 1 = q.r by omega,
    show a - qp.r = a - q.r + 1 by omega,
    show a + (q.intermediate - 2) - qp.r + 2 =
      a + q.intermediate - q.r + 1 by omega,
    show b + c - (q.p + 1) + 2 = b + c - q.p + 1 by omega,
    show (b - 1) + (c - 1) - q.p + 2 = b + c - q.p by omega,
    show q.intermediate - 2 + 2 = q.intermediate by omega,
    show q.intermediate - 2 + 3 = q.intermediate + 1 by omega]
  let K := q.r * (a - q.r + 1) *
    (a + q.intermediate - q.r + 1)
  let T := b + c - q.p
  let D := q.intermediate * (q.intermediate + 1)
  have hD : 0 < D := Nat.mul_pos (by omega) (by omega)
  simpa only [K, T, D] using mkPos_difference_one_step K T D hD

/-- The lower difference coefficient has the dual closed numerator.  The
proof includes the `p=1` face, where the reduced lower contribution is
definitionally guarded to zero. -/
theorem omegaCorrectionLowerCoefficient_closed {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1) :
    Q'.ofNat ((q.intermediate + 2) * (q.intermediate + 1)) *
        omegaCorrectionLowerCoefficient a b c d q.p ≈
      Q'.ofNat
        ((b - q.p + 1) * (c - q.p + 1) *
          (q.intermediate - q.r + 1)) := by
  have hqmin := Nat.le_min.mp q.p_le
  have hqmmin := Nat.le_min.mp qm.p_le
  have hqr := Nat.le_min.mp q.r_le
  have hqmr := Nat.le_min.mp qm.r_le
  have hrf : q.r ≤ q.intermediate := by
    simpa only [FixedRightCGChannel.intermediate] using hqr.2
  have hqmrf : qm.r ≤ qm.intermediate := by
    simpa only [FixedRightCGChannel.intermediate] using hqmr.2
  have hf : qm.intermediate = q.intermediate + 2 := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hdeg := q.degree_eq
  have hdegm := qm.degree_eq
  have hr : qm.r = q.r + 1 := by
    unfold FixedRightCGChannel.intermediate at hf hdeg hdegm
    omega
  have hguard0 :
      rightOrderOK a b c d (q.p - 1 + 1) = true := by
    rw [show q.p - 1 + 1 = q.p by omega]
    exact fixedRight_rightOrderOK q
  have hlabel0 : rightLabel b c (q.p - 1) = q.intermediate + 2 := by
    rw [← hf, show q.p - 1 = qm.p by omega]
    rfl
  have houter0 : outerOrder a b c d (q.p - 1) = qm.r := by
    unfold outerOrder
    rw [show rightLabel b c (q.p - 1) = qm.intermediate by omega]
    exact fixedRight_outer_couplingOrder qm
  by_cases hp1 : q.p = 1
  · have hnot : ¬ 1 < q.p := by omega
    unfold omegaCorrectionLowerCoefficient reducedLowerCoefficient
    rw [if_neg hnot]
    unfold jacobiForward
    rw [dif_pos hguard0]
    unfold forwardNum forwardDen
    simp only [hlabel0, houter0]
    have hF1 : q.intermediate + 2 - (q.r + 1) =
        q.intermediate - q.r + 1 := by omega
    have hDen : q.intermediate + 2 - 1 = q.intermediate + 1 := by
      omega
    simp only [hp1, Nat.one_sub, if_neg (by decide : ¬ (1 : Nat) = 0),
      Nat.zero_add, Nat.sub_zero, Nat.one_mul, hr, hF1, hDen]
    let K := (b - q.p + 1) * (c - q.p + 1) *
      (q.intermediate - q.r + 1)
    let D := (q.intermediate + 2) * (q.intermediate + 1)
    have hD : 0 < D := Nat.mul_pos (by omega) (by omega)
    have hb1 : b - 1 + 1 = b := by omega
    have hc1 : c - 1 + 1 = c := by omega
    have hcancel := mkPos_scale_cancel K D hD
    simpa only [K, D, hp1, Nat.one_sub, Nat.zero_add, Nat.one_mul,
      hb1, hc1] using
      scale_add_neg_zero (Q'.ofNat D) (Q'.mkPos K D hD)
        (Q'.ofNat K) hcancel
  · have hpgt : 1 < q.p := by omega
    have hguard1 :
        rightOrderOK a (b - 1) (c - 1) d (q.p - 2 + 1) = true := by
      rw [show q.p - 2 + 1 = q.p - 1 by omega]
      exact reduced_rightOrderOK q hp
    have hlabel1 : rightLabel (b - 1) (c - 1) (q.p - 2) =
        q.intermediate + 2 := by
      unfold rightLabel FixedRightCGChannel.intermediate
      omega
    have houter1 : outerOrder a (b - 1) (c - 1) d (q.p - 2) = qm.r := by
      unfold outerOrder
      rw [show rightLabel (b - 1) (c - 1) (q.p - 2) =
        qm.intermediate by omega]
      exact fixedRight_outer_couplingOrder qm
    unfold omegaCorrectionLowerCoefficient reducedLowerCoefficient
    rw [if_pos hpgt]
    unfold jacobiForward
    rw [dif_pos hguard0, dif_pos hguard1]
    unfold forwardNum forwardDen
    simp only [hlabel0, hlabel1, houter0, houter1]
    simp only [show q.p - 1 + 1 = q.p by omega,
      show q.p - 2 + 1 = q.p - 1 by omega,
      show b - (q.p - 1) = b - q.p + 1 by omega,
      show c - (q.p - 1) = c - q.p + 1 by omega,
      show b - 1 - (q.p - 2) = b - q.p + 1 by omega,
      show c - 1 - (q.p - 2) = c - q.p + 1 by omega,
      show q.intermediate + 2 - qm.r =
        q.intermediate - q.r + 1 by omega,
      show q.intermediate + 2 - 1 = q.intermediate + 1 by omega]
    let K := (b - q.p + 1) * (c - q.p + 1) *
      (q.intermediate - q.r + 1)
    let P := q.p
    let D := (q.intermediate + 2) * (q.intermediate + 1)
    have hD : 0 < D := Nat.mul_pos (by omega) (by omega)
    have hdiff := mkPos_difference_one_step K (P - 1) D hD
    have hcast : ((P - 1 : Nat) : Int) + 1 = (P : Int) := by
      dsimp only [P]
      omega
    rw [hcast] at hdiff
    have hF : q.intermediate + 2 - qm.r =
        q.intermediate - q.r + 1 := by omega
    have hnum0 :
        q.p * (b - q.p + 1) * (c - q.p + 1) *
            (q.intermediate - q.r + 1) = K * P := by
      dsimp only [K, P]
      ac_rfl
    have hnum1 :
        (q.p - 1) * (b - q.p + 1) * (c - q.p + 1) *
            (q.intermediate - q.r + 1) = K * (P - 1) := by
      dsimp only [K, P]
      ac_rfl
    rw [hnum0, hnum1]
    simpa only [D] using hdiff

/-- The diagonal correction is an exact same-denominator difference.  This
statement also covers the removable `f=0` branch, so no division or hidden
nonzero premise remains in the three-carrier row. -/
theorem omegaCorrectionDiagonalCoefficient_closed {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p) :
    Q'.ofNat (omegaCorrectionDiagonalDenominator q.intermediate) *
        omegaCorrectionDiagonalCoefficient a b c d q.p ≈
      Q'.ofInt
        (omegaCorrectionDiagonalNumerator a b c d q.intermediate) := by
  have hqmin := Nat.le_min.mp q.p_le
  have hlabel0 : rightLabel b c q.p = q.intermediate := rfl
  have hlabel1 : rightLabel (b - 1) (c - 1) (q.p - 1) =
      q.intermediate := by
    unfold rightLabel FixedRightCGChannel.intermediate
    omega
  unfold omegaCorrectionDiagonalCoefficient jacobiDiagonal
  simp only [hlabel0, hlabel1]
  by_cases hf : q.intermediate = 0
  · simp only [hf, if_pos, omegaCorrectionDiagonalDenominator,
      omegaCorrectionDiagonalNumerator]
    simpa using mkPos_difference_same_den
      (-((a * b : Nat) : Int)) (-((a * (b - 1) : Nat) : Int))
      2 (by decide)
  · have hD : 0 < diagonalDen q.intermediate := diagonalDen_pos hf
    simp only [hf, omegaCorrectionDiagonalDenominator,
      omegaCorrectionDiagonalNumerator]
    simpa using mkPos_difference_same_den
      (diagonalNum a b c d q.intermediate)
      (diagonalNum a (b - 1) (c - 1) d q.intermediate)
      (diagonalDen q.intermediate) hD

private theorem peeledRightCoefficient_zero_below {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l s : Nat) (hbelow : j + l < q.p - 1) :
    peeledRightCoefficient q s i j l ≈ 0 := by
  let qr := reducePositiveInnerRightChannel q hp
  have hqr : qr.p = q.p - 1 := rfl
  have hinter : qr.intermediate = q.intermediate :=
    reduced_intermediate_eq q hp
  have h := triRight_monomial_zero_below_inner_order qr i j l s (by
    rw [hqr]
    exact hbelow)
  simpa only [peeledRightCoefficient, hinter] using h

private theorem triRightOmegaCorrection_zero_below {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l s : Nat) (hbelow : j + l < q.p - 1) :
    triRightOmegaCorrection q i j l s ≈ 0 := by
  have h0 := peeledRightCoefficient_zero_below q hp (i - 1) j l s
    (by omega)
  have h1 := peeledRightCoefficient_zero_below q hp i j (l - 1) s
    (by omega)
  have h2 := peeledRightCoefficient_zero_below q hp i (j - 1) l s
    (by omega)
  have h3 := peeledRightCoefficient_zero_below q hp (i + 1) (j - 1)
    (l - 1) s (by omega)
  unfold triRightOmegaCorrection omegaExchangeCorrection
  refine Q'.eqv_trans _
    ((Q'.ofNat i * Q'.ofNat (b - j)) *
        (Q'.ofNat (c - l) * 0 + Q'.ofNat l * 0) +
      -((Q'.ofNat (a - i) * Q'.ofNat j) *
        (Q'.ofNat (c - l) * 0 + Q'.ofNat l * 0))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ h0)
          (Q'.mul_eqv_congr_left _ _ _ h1)))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left _ _ _ h2)
            (Q'.mul_eqv_congr_left _ _ _ h3))))
  · ring_qeqv

/-- The all-label correction identity is already exact on the entire region
below the lower adjacent channel's support.  This closes all truncated-index
faces in that region and isolates the remaining contiguous calculation to the
genuine three-carrier support. -/
theorem omegaCorrectionThreeCarrier_below_lower_support {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hbelow : j + l < qm.p) :
    OmegaCorrectionThreeCarrierAt qm q qp i j l s := by
  have hpred : q.p - 1 = qm.p := by omega
  have hcorr := triRightOmegaCorrection_zero_below q hp i j l s (by
    rw [hpred]
    exact hbelow)
  have hqm := triRight_monomial_zero_below_inner_order qm i j l s hbelow
  have hq := triRight_monomial_zero_below_inner_order q i j l s (by omega)
  have hqp := triRight_monomial_zero_below_inner_order qp i j l s (by omega)
  unfold OmegaCorrectionThreeCarrierAt
  refine Q'.eqv_trans _ 0 _ hcorr (Q'.eqv_symm ?_)
  refine Q'.eqv_trans _
    (omegaCorrectionLowerCoefficient a b c d q.p * 0 +
      omegaCorrectionDiagonalCoefficient a b c d q.p * 0 +
      omegaCorrectionUpperCoefficient a b c d q.p * 0) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hqm)
        (Q'.mul_eqv_congr_left _ _ _ hq))
      (Q'.mul_eqv_congr_left _ _ _ hqp)
  · refine Q'.eqv_trans _ (((0 : Q') + 0) + 0) _ ?_ (by decide)
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_zero_eqv _)
        (Q'.mul_zero_eqv _))
      (Q'.mul_zero_eqv _)

/-- Pure factorial/Hahn form of the surviving pointwise correction residual.
Unlike the raw nested maps, every support guard and output-shell guard is
literal in this predicate. -/
def OmegaCorrectionFactorialAt {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l s : Nat) : Prop :=
  omegaExchangeCorrection a b c
      (fun u v w => guardedRightFactorialCoefficient
        (reducePositiveInnerRightChannel q hp) u v w s) i j l ≈
    omegaCorrectionLowerCoefficient a b c d q.p *
        guardedRightFactorialCoefficient qm i j l s +
      omegaCorrectionDiagonalCoefficient a b c d q.p *
        guardedRightFactorialCoefficient q i j l s +
      omegaCorrectionUpperCoefficient a b c d q.p *
        guardedRightFactorialCoefficient qp i j l s

private theorem triRight_eq_guardedRightFactorial {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat) :
    triRight a b c d q.intermediate (mono i) (mono j) (mono l) s ≈
      guardedRightFactorialCoefficient q i j l s :=
  Q'.eqv_trans _ _ _ (triRight_monomial_eq_guardedHahn q i j l s)
    (guardedRightHahnCoefficient_eq_factorial q i j l s)

private theorem peeledRightCoefficient_eq_guardedFactorial
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (i j l s : Nat) :
    peeledRightCoefficient q s i j l ≈
      guardedRightFactorialCoefficient
        (reducePositiveInnerRightChannel q hp) i j l s := by
  let qr := reducePositiveInnerRightChannel q hp
  have hinter : qr.intermediate = q.intermediate :=
    reduced_intermediate_eq q hp
  have h := triRight_eq_guardedRightFactorial qr i j l s
  simpa only [peeledRightCoefficient, hinter] using h

private theorem triRightOmegaCorrection_eq_factorialCorrection
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (i j l s : Nat) :
    triRightOmegaCorrection q i j l s ≈
      omegaExchangeCorrection a b c
        (fun u v w => guardedRightFactorialCoefficient
          (reducePositiveInnerRightChannel q hp) u v w s) i j l := by
  have h0 := peeledRightCoefficient_eq_guardedFactorial
    q hp (i - 1) j l s
  have h1 := peeledRightCoefficient_eq_guardedFactorial
    q hp i j (l - 1) s
  have h2 := peeledRightCoefficient_eq_guardedFactorial
    q hp i (j - 1) l s
  have h3 := peeledRightCoefficient_eq_guardedFactorial
    q hp (i + 1) (j - 1) (l - 1) s
  unfold triRightOmegaCorrection omegaExchangeCorrection
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ h0)
        (Q'.mul_eqv_congr_left _ _ _ h1)))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ h2)
          (Q'.mul_eqv_congr_left _ _ _ h3))))

private theorem threeCarrierRHS_eq_factorialRHS {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (i j l s : Nat) :
    omegaCorrectionLowerCoefficient a b c d q.p *
          triRight a b c d qm.intermediate
            (mono i) (mono j) (mono l) s +
        omegaCorrectionDiagonalCoefficient a b c d q.p *
          triRight a b c d q.intermediate
            (mono i) (mono j) (mono l) s +
        omegaCorrectionUpperCoefficient a b c d q.p *
          triRight a b c d qp.intermediate
            (mono i) (mono j) (mono l) s ≈
      omegaCorrectionLowerCoefficient a b c d q.p *
          guardedRightFactorialCoefficient qm i j l s +
        omegaCorrectionDiagonalCoefficient a b c d q.p *
          guardedRightFactorialCoefficient q i j l s +
        omegaCorrectionUpperCoefficient a b c d q.p *
          guardedRightFactorialCoefficient qp i j l s := by
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _
        (triRight_eq_guardedRightFactorial qm i j l s))
      (Q'.mul_eqv_congr_left _ _ _
        (triRight_eq_guardedRightFactorial q i j l s)))
    (Q'.mul_eqv_congr_left _ _ _
      (triRight_eq_guardedRightFactorial qp i j l s))

/-- Exact equivalence between the raw nested-map correction and its fully
factorialized residual.  Thus the remaining supported case contains no hidden
functional extensionality or reconstruction statement: it is a finite
exact-rational Hahn identity at each coordinate. -/
theorem omegaCorrectionThreeCarrierAt_iff_factorial {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l s : Nat) :
    OmegaCorrectionThreeCarrierAt qm q qp i j l s ↔
      OmegaCorrectionFactorialAt qm q qp hp i j l s := by
  have hleft := triRightOmegaCorrection_eq_factorialCorrection
    q hp i j l s
  have hright := threeCarrierRHS_eq_factorialRHS qm q qp i j l s
  constructor
  · intro h
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
      (Q'.eqv_trans _ _ _ h hright)
  · intro h
    exact Q'.eqv_trans _ _ _ hleft
      (Q'.eqv_trans _ _ _ h (Q'.eqv_symm hright))

end YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier.omegaCorrectionUpperCoefficient_closed
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier.omegaCorrectionLowerCoefficient_closed
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier.omegaCorrectionDiagonalCoefficient_closed
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier.omegaCorrectionThreeCarrier_below_lower_support
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier.omegaCorrectionThreeCarrierAt_iff_factorial
