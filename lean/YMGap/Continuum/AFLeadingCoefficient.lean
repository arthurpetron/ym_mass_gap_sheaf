/-
Actual rational enclosures of the numerical coefficient 3*pi^2/(22*log 2).
The shifted Machin/artanh approximations, endpoints and precision modulus
are computed data. This is not a physical scale function or an AF/RG input.
-/

import YMGap.Constructive.Pi
import YMGap.Constructive.CRealLog
import YMGap.Continuum.ArtanhMonotone
import YMGap.Continuum.GNSHilbertSpace
import YMGap.Continuum.SummableRationalReciprocalStepVariation
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.SeriesComposition
import YMGap.Continuum.BoundedRationalCauchyProduct
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.AFLeadingCoefficient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SummableRationalSquareStepVariation (square_step_le)
open YMGap.Continuum.SummableRationalReciprocalStepVariation (reciprocal_step_le)

local infix:50 " ≈ " => Q'.eqv

/-- Shifted actual pi lower endpoint; the shift protects squaring. -/
def P (n : Nat) : Q' := Pi.piLower (n+1)
/-- Shifted actual pi upper endpoint. -/
def Q (n : Nat) : Q' := Pi.piUpper (n+1)
/-- Shifted actual log denominator lower endpoint. -/
def l (n : Nat) : Q' := CRealLog.log2Lower (n+1)
/-- Shifted actual log denominator upper endpoint. -/
def u (n : Nat) : Q' := CRealLog.log2Upper (n+1)

private theorem tail5_le_quarter (n : Nat) :
    Pi.piTail5 n ≤ Q'.mkPos 1 4 (by decide) :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Pi.ratioPow_antitone (by decide) (Nat.zero_le n)) (by decide))
    (Q'.le_of_eqv (Q'.one_mul_eqv _))

private theorem tail239_le (n : Nat) :
    Pi.piTail239 n ≤ Q'.mkPos 1 238 (by decide) :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Pi.ratioPow_antitone (by decide) (Nat.zero_le n)) (by decide))
    (Q'.le_of_eqv (Q'.one_mul_eqv _))

theorem two_le_P (n : Nat) : (2 : Q') ≤ P n := by
  have h := Q'.add_le_add (Pi.three_le_pi_approx (Nat.succ_le_succ (Nat.zero_le n)))
    (Q'.neg_le_neg (Q'.mul_le_mul_of_nonneg_left _ _ 4
      (tail239_le (n+1)) (by decide)))
  exact Q'.le_trans' _ _ _
    (by decide : (2 : Q') ≤ 3 + -(4 * Q'.mkPos 1 238 (by decide))) h

theorem Q_le_eight (n : Nat) : Q n ≤ (8 : Q') :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add (Pi.pi_approx_le_four (n+1))
      (Q'.mul_le_mul_of_nonneg_left _ _ 16 (tail5_le_quarter (n+1)) (by decide)))
    (by decide : (4 : Q') + 16 * Q'.mkPos 1 4 (by decide) ≤ 8)

theorem P_le_Q (n : Nat) : P n ≤ Q n :=
  Q'.le_trans' _ _ _ (Pi.pi_approx_enclosure (n+1) (n+1) (Nat.le_refl _)).1
    (Pi.pi_approx_enclosure (n+1) (n+1) (Nat.le_refl _)).2

theorem log_floor (n : Nat) : Q'.mkPos 2 3 (by decide) ≤ l n :=
  CRealLog.twoThirds_le_log2Lower (n+1) (Nat.succ_le_succ (Nat.zero_le n))

theorem l_le_u (n : Nat) : l n ≤ u n :=
  CRealLog.log2_approx_le_upper (n+1) (n+1) (Nat.le_refl _)

theorem l_positive (n : Nat) : (0 : Q') < l n :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < Q'.mkPos 2 3 (by decide)) (log_floor n)

theorem u_positive (n : Nat) : (0 : Q') < u n :=
  Q'.pos_of_lt_of_le (l_positive n) (l_le_u n)

theorem stream_denominator_positive (n : Nat) :
    (0 : Q') < (22 : Q') * CRealLog.log2.approx (n+1) :=
  Q'.mul_pos (by decide) (l_positive n)

/-- Literal shifted Machin/artanh quotient, not an assumed coefficient. -/
def stream (n : Nat) : Q' :=
  Q'.divPos (3 * (Pi.pi.approx (n+1) * Pi.pi.approx (n+1)))
    (22 * CRealLog.log2.approx (n+1)) (stream_denominator_positive n)

/-- Actual rational lower quotient endpoint. -/
def lower (n : Nat) : Q' :=
  Q'.divPos (3 * (P n * P n)) (22 * u n) (Q'.mul_pos (by decide) (u_positive n))

/-- Actual rational upper quotient endpoint. -/
def upper (n : Nat) : Q' :=
  Q'.divPos (3 * (Q n * Q n)) (22 * l n) (Q'.mul_pos (by decide) (l_positive n))

private theorem square_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    a*a ≤ b*b :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ a hab ha)
    (Q'.mul_le_mul_of_nonneg_right _ _ b hab (Q'.le_trans' _ _ _ ha hab))

private theorem quotient_mono {a b d e : Q'}
    (ha : (0 : Q') ≤ a) (hab : a ≤ b)
    (hd : (0 : Q') < d) (he : (0 : Q') < e) (hde : d ≤ e) :
    Q'.divPos a e he ≤ Q'.divPos b d hd :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ a
      (ArtanhMonotone.recipPos_antitone d e hd he hde) ha)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hab
      (Q'.le_of_lt (Q'.recipPos_pos d hd)))

/-- Both computed endpoints enclose every later actual quotient. -/
theorem stream_enclosure (n m : Nat) (hnm : n ≤ m) :
    lower n ≤ stream m ∧ stream m ≤ upper n := by
  have hnms := Nat.succ_le_succ hnm
  have hp := Pi.pi_approx_enclosure (n+1) (m+1) hnms
  have hl := CRealLog.log2Lower_le_approx (n+1) (m+1) hnms
  have hu := CRealLog.log2_approx_le_upper (n+1) (m+1) hnms
  have hp0 : (0 : Q') ≤ P n := Q'.le_trans' _ _ _ (by decide) (two_le_P n)
  have hm0 : (0 : Q') ≤ Pi.pi.approx (m+1) := Q'.le_trans' _ _ _ hp0 hp.1
  constructor
  · exact quotient_mono (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hp0 hp0))
      (Q'.mul_le_mul_of_nonneg_left _ _ 3 (square_mono hp0 hp.1) (by decide))
      (stream_denominator_positive m) (Q'.mul_pos (by decide) (u_positive n))
      (Q'.mul_le_mul_of_nonneg_left _ _ 22 hu (by decide))
  · exact quotient_mono (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hm0 hm0))
      (Q'.mul_le_mul_of_nonneg_left _ _ 3 (square_mono hm0 hp.2) (by decide))
      (Q'.mul_pos (by decide) (l_positive n)) (stream_denominator_positive m)
      (Q'.mul_le_mul_of_nonneg_left _ _ 22 hl (by decide))

private theorem pi_width (n : Nat) : Q n ≤ P n + 20 * HalfPow.half ^ n := by
  have h : Q n + -(P n) ≤ 20 * HalfPow.half ^ n :=
    Q'.le_trans' _ _ _ (Pi.pi_enclosure_width_le (n+1))
      (Q'.mul_le_mul_of_nonneg_left _ _ 20
        (ExpNeg.pow_half_antitone n 1) (by decide))
  exact Q'.le_add_of_sub_le h

private theorem log_width (n : Nat) :
    u n ≤ l n + Q'.mkPos 9 4 (by decide) * HalfPow.half ^ n :=
  Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
    (ExpNeg.pow_half_antitone n 1) (by decide))

private theorem square_payment (p h : Q') :
    (3 * (p*p + (8+8)*(20*h))) ≈ 3*(p*p) + 960*h := by
  exact poly_identity_of_normal_eq
    (.mul (.const 3) (.add (.mul (.var 0) (.var 0))
      (.mul (.add (.const 8) (.const 8)) (.mul (.const 20) (.var 1)))))
    (.add (.mul (.const 3) (.mul (.var 0) (.var 0))) (.mul (.const 960) (.var 1)))
    (by decide) (fun i => if i=0 then p else h)

private theorem scaled_log_payment (a h : Q') :
    (22 * (a + Q'.mkPos 9 4 (by decide)*h)) ≈
      22*a + Q'.mkPos 99 2 (by decide)*h :=
  Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ h
        (by decide : ((22 : Q') * Q'.mkPos 9 4 (by decide)) ≈ Q'.mkPos 99 2 (by decide)))))

private theorem collect_payment (z r d h : Q') :
    ((z + 192*(r*r*(d*h))) + (960*h)*r) ≈
      z + (192*(r*r*d) + 960*r)*h := by
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.mul (.const 192)
      (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 3)))))
      (.mul (.mul (.const 960) (.var 3)) (.var 1)))
    (.add (.var 0) (.mul (.add (.mul (.const 192)
      (.mul (.mul (.var 1) (.var 1)) (.var 2))) (.mul (.const 960) (.var 1))) (.var 3)))
    (by decide) (fun i => if i=0 then z else if i=1 then r else if i=2 then d else h)

/-- The quotient enclosure has a uniform explicit geometric width. -/
theorem upper_le_lower_add (n : Nat) : upper n ≤ lower n + 110 * HalfPow.half ^ n := by
  let h := HalfPow.half ^ n
  let f := Q'.mkPos 44 3 (by decide)
  let r := Q'.recipPos f (by decide)
  let d := Q'.mkPos 99 2 (by decide)
  let denl := (22 : Q')*l n
  let denu := (22 : Q')*u n
  have h0 : (0 : Q') ≤ h := Q'.pow_nonneg _ HalfPow.half_nonneg n
  have hp0 : (0 : Q') ≤ P n := Q'.le_trans' _ _ _ (by decide) (two_le_P n)
  have hq0 : (0 : Q') ≤ Q n := Q'.le_trans' _ _ _ hp0 (P_le_Q n)
  have hp8 : P n ≤ (8 : Q') := Q'.le_trans' _ _ _ (P_le_Q n) (Q_le_eight n)
  have hsquare := square_step_le (P n) (Q n) (20*h) 8 hp0 hq0
    (Q'.mul_nonneg _ _ (by decide) h0) hp8 (Q_le_eight n) (pi_width n)
  have hnum : 3*(Q n*Q n) ≤ 3*(P n*P n) + 960*h :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 3 hsquare (by decide))
      (Q'.le_of_eqv (square_payment (P n) h))
  have hfloorl : f ≤ denl := Q'.le_trans' _ _ _
    (by decide : Q'.mkPos 44 3 (by decide) ≤ (22 : Q')*Q'.mkPos 2 3 (by decide))
    (Q'.mul_le_mul_of_nonneg_left _ _ 22 (log_floor n) (by decide))
  have hflooru : f ≤ denu := Q'.le_trans' _ _ _ hfloorl
    (Q'.mul_le_mul_of_nonneg_left _ _ 22 (l_le_u n) (by decide))
  have hdenl : (0 : Q') < denl := Q'.mul_pos (by decide) (l_positive n)
  have hdenu : (0 : Q') < denu := Q'.mul_pos (by decide) (u_positive n)
  let rl := Q'.recipPos denl hdenl
  let ru := Q'.recipPos denu hdenu
  have hr0 : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos f (by decide))
  have hrl : rl ≤ r := ArtanhMonotone.recipPos_antitone f denl (by decide) hdenl hfloorl
  have hstep : denu ≤ denl + d*h := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 22 (log_width n) (by decide))
    (Q'.le_of_eqv (scaled_log_payment (l n) h))
  have hrec : rl ≤ ru + (r*r)*(d*h) :=
    reciprocal_step_le denl denu (d*h) f hdenl hdenu (by decide)
      (Q'.mul_nonneg _ _ (by decide) h0) hfloorl hflooru hstep
  let np := (3 : Q')*(P n*P n)
  have hnp0 : (0 : Q') ≤ np := Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hp0 hp0)
  have hnp : np ≤ (192 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 3 (square_mono hp0 hp8) (by decide))
    (by decide : (3 : Q')*(8*8) ≤ 192)
  have hnrec : np*rl ≤ lower n + 192*(r*r*(d*h)) := by
    have hv0 : (0 : Q') ≤ r*r*(d*h) := Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ hr0 hr0) (Q'.mul_nonneg _ _ (by decide) h0)
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ np hrec hnp0)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv np ru _))
        (Q'.add_le_add_left (np*ru) _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hnp hv0)))
  have ht : (960*h)*rl ≤ (960*h)*r :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hrl (Q'.mul_nonneg _ _ (by decide) h0)
  have htotal : upper n ≤ (lower n + 192*(r*r*(d*h))) + (960*h)*r :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ rl hnum (Q'.le_of_lt (Q'.recipPos_pos denl hdenl)))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_mul_eqv np (960*h) rl))
        (Q'.add_le_add hnrec ht))
  exact Q'.le_trans' _ _ _ htotal
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (collect_payment (lower n) r d h))
      (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ h
        (by decide : 192*(r*r*d)+960*r ≤ (110 : Q')) h0)))

theorem enclosure_width_le (n : Nat) :
    upper n + -(lower n) ≤ 110 * HalfPow.half ^ n :=
  Q'.sub_le_of_le_add (upper_le_lower_add n)

/-- Precision data computed before any legacy Prop-level Cauchy packaging. -/
def precisionModulus (epsilon : Q') : Nat := (Q'.mkPos 1 110 (by decide)*epsilon).den

theorem enclosure_width_le_of_modulus (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : precisionModulus epsilon ≤ n) : upper n + -(lower n) ≤ epsilon := by
  let delta := Q'.mkPos 1 110 (by decide)*epsilon
  have hd : (0 : Q') < delta := Q'.mul_pos (by decide) he
  obtain ⟨d, hdindex⟩ := Nat.exists_eq_add_of_le hn
  have hpow : HalfPow.half ^ n ≤ delta := by
    rw [hdindex]
    exact Q'.le_trans' _ _ _ (ExpNeg.pow_half_antitone _ d) (HalfPow.pow_half_le delta hd)
  have hc : ((110 : Q')*delta) ≈ epsilon :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ epsilon
        (by decide : ((110 : Q')*Q'.mkPos 1 110 (by decide)) ≈ 1)) (Q'.one_mul_eqv epsilon))
  exact Q'.le_trans' _ _ _ (enclosure_width_le n)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 110 hpow (by decide)) (Q'.le_of_eqv hc))

/-- Type-level Cauchy datum for the actual shifted quotient stream. -/
def streamQCauchy : CReal.QCauchy stream where
  M := precisionModulus
  bound := by
    intro epsilon he p q hp hq
    let n := precisionModulus epsilon
    have hwidth : upper n ≤ lower n + epsilon := Q'.le_add_of_sub_le
      (enclosure_width_le_of_modulus epsilon he n (Nat.le_refl _))
    have hpe := stream_enclosure n p hp
    have hqe := stream_enclosure n q hq
    exact ⟨Q'.le_trans' _ _ _ hpe.2 (Q'.le_trans' _ _ _ hwidth
        (Q'.add_le_add_right _ _ epsilon hqe.1)),
      Q'.le_trans' _ _ _ hqe.2 (Q'.le_trans' _ _ _ hwidth
        (Q'.add_le_add_right _ _ epsilon hpe.1))⟩

/-- One literal finite upper enclosure is already below two. -/
theorem upper_one_lt_two : upper 1 < (2 : Q') := by decide

/-- One literal finite lower enclosure is already above one. -/
theorem one_lt_lower_one : (1 : Q') < lower 1 := by decide

/-! ## The constructed coefficient and its exact series-value pin -/

/-- The value of the actual quotient stream, using its computed modulus. -/
def value : CReal := CReal.ofQ'CauchySeq stream streamQCauchy

/-- Explicit modulus data for the returned representative itself. -/
def valueQCauchy : CReal.QCauchy value.approx :=
  BoundedRationalCauchyProduct.representativeCauchy stream streamQCauchy

theorem value_approx (n : Nat) :
    value.approx n = stream (CReal.QMhat stream streamQCauchy n) := rfl

/-- Every computed lower endpoint bounds the SAME constructed value. -/
theorem value_geRat_lower (n : Nat) : ExpPos.geRat value (lower n) := by
  apply ExpPos.geRat_of_eventually
  refine ⟨n, fun m hnm => ?_⟩
  exact (stream_enclosure n _
    (Nat.le_trans hnm (CReal.self_le_QMhat stream streamQCauchy m))).1

/-- Every computed upper endpoint bounds the SAME constructed value. -/
theorem value_leRat_upper (n : Nat) : CReal.leRat value (upper n) := by
  apply CReal.leRat_of_eventually
  refine ⟨n, fun m hnm => ?_⟩
  exact (stream_enclosure n _
    (Nat.le_trans hnm (CReal.self_le_QMhat stream streamQCauchy m))).2

/-- Exact rational cancellation BEFORE passing to any limit. -/
theorem stream_product_pin (n : Nat) :
    ((22 * CRealLog.log2.approx (n+1)) * stream n) ≈
      ((3 * Pi.pi.approx (n+1)) * Pi.pi.approx (n+1)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv _ _ (stream_denominator_positive n)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- The cleared coefficient equation for the ACTUAL Machin/artanh values.
It follows from exact sample products and limit continuity; no supplied
real reciprocal, coefficient enclosure, physical scale or RG law is used. -/
theorem value_product_pin : CReal.Equiv
    (CReal.mul (CReal.mul (CReal.ofQ' 22) CRealLog.log2) value)
    (CReal.mul (CReal.mul (CReal.ofQ' 3) Pi.pi) Pi.pi) := by
  have hpi := SeriesComposition.convergesTo_shift (CReal.convergesTo_self Pi.pi)
  have hlog := SeriesComposition.convergesTo_shift (CReal.convergesTo_self CRealLog.log2)
  have hvalue := CReal.convergesTo_ofQ'CauchySeq stream streamQCauchy
  have hleft :=
    Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CReal.convergesTo_const_mul (CReal.ofQ' 22) hlog) hvalue
  have hright :=
    Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CReal.convergesTo_const_mul (CReal.ofQ' 3) hpi) hpi
  apply CReal.Equiv_of_limit_of_equal _ hleft hright
  intro n
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => stream_product_pin n)

end YMGap.Continuum.AFLeadingCoefficient

#print axioms YMGap.Continuum.AFLeadingCoefficient.P
#print axioms YMGap.Continuum.AFLeadingCoefficient.Q
#print axioms YMGap.Continuum.AFLeadingCoefficient.l
#print axioms YMGap.Continuum.AFLeadingCoefficient.u
#print axioms YMGap.Continuum.AFLeadingCoefficient.two_le_P
#print axioms YMGap.Continuum.AFLeadingCoefficient.Q_le_eight
#print axioms YMGap.Continuum.AFLeadingCoefficient.P_le_Q
#print axioms YMGap.Continuum.AFLeadingCoefficient.log_floor
#print axioms YMGap.Continuum.AFLeadingCoefficient.l_le_u
#print axioms YMGap.Continuum.AFLeadingCoefficient.l_positive
#print axioms YMGap.Continuum.AFLeadingCoefficient.u_positive
#print axioms YMGap.Continuum.AFLeadingCoefficient.stream_denominator_positive
#print axioms YMGap.Continuum.AFLeadingCoefficient.stream
#print axioms YMGap.Continuum.AFLeadingCoefficient.lower
#print axioms YMGap.Continuum.AFLeadingCoefficient.upper
#print axioms YMGap.Continuum.AFLeadingCoefficient.stream_enclosure
#print axioms YMGap.Continuum.AFLeadingCoefficient.upper_le_lower_add
#print axioms YMGap.Continuum.AFLeadingCoefficient.enclosure_width_le
#print axioms YMGap.Continuum.AFLeadingCoefficient.precisionModulus
#print axioms YMGap.Continuum.AFLeadingCoefficient.enclosure_width_le_of_modulus
#print axioms YMGap.Continuum.AFLeadingCoefficient.streamQCauchy
#print axioms YMGap.Continuum.AFLeadingCoefficient.upper_one_lt_two
#print axioms YMGap.Continuum.AFLeadingCoefficient.one_lt_lower_one
#print axioms YMGap.Continuum.AFLeadingCoefficient.value
#print axioms YMGap.Continuum.AFLeadingCoefficient.valueQCauchy
#print axioms YMGap.Continuum.AFLeadingCoefficient.value_approx
#print axioms YMGap.Continuum.AFLeadingCoefficient.value_geRat_lower
#print axioms YMGap.Continuum.AFLeadingCoefficient.value_leRat_upper
#print axioms YMGap.Continuum.AFLeadingCoefficient.stream_product_pin
#print axioms YMGap.Continuum.AFLeadingCoefficient.value_product_pin
