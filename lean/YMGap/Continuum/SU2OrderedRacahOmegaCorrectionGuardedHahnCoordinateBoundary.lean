/-
# Lower coordinate boundary for the guarded Hahn correction

This module treats the exact face `i = r`.  Here the outer predecessor is
evaluated at `x=r-1`, one step below the range of the ordinary row bridge.
The falling-factorial formula nevertheless gives a closed endpoint identity.
-/

import YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnUpperBoundary

namespace YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantHighestWeightRowFormula
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl]; ac_rfl))

local macro "ring_zero_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Int.natCast_zero,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl]; try ac_rfl))

private theorem mul_eqv_congr {a b c d : Q'}
    (ha : a ≈ c) (hb : b ≈ d) : a * b ≈ c * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem tvFallQ_label_shift (n r : Nat) (hr : r + 1 ≤ n) :
    Q'.ofNat n * tvFallQ (n - 1) r ≈
      Q'.ofNat (n - r) * tvFallQ n r := by
  refine Q'.eqv_trans _ (tvFallQ n (r + 1)) _
    (tvFallQ_leading_shift n r) ?_
  refine Q'.eqv_trans _ (tvFallQ n r * Q'.ofNat (n - r)) _
    (Q'.eqv_symm (tvFallQ_trailing_shift n r hr)) ?_
  exact Q'.mul_comm_eqv _ _

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

private theorem ofNat_pos_of_pos (n : Nat) (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

/-- Fence around the invalid bulk rewrite at `x=k-1`: truncated natural
subtraction makes the syntactic bulk factor equal to one, not zero. -/
theorem lower_coordinate_truncated_shift_eq_one
    (k : Nat) : k - 1 - k + 1 = 1 := by
  omega

/-- The second-index-one bridge at the exceptional coordinate `x=k-1`. -/
theorem second_one_scaled_to_zero_at_lower_coordinate
    (m n k : Nat) (hk : 0 < k) :
    (Q'.ofNat k * Q'.ofNat n) *
        transvectFactorialCoeff m n k (k - 1) 1 ≈
      (Q'.ofNat 0 * Q'.ofNat (n - k) +
          -(Q'.ofNat k * Q'.ofNat (m - (k - 1)))) *
        transvectFactorialCoeff m n k k 0 := by
  have hclosed := transvectFactorialCoeff_second_one_closed m n k (k - 1)
  have hz := tvFallQ_eqv_zero_of_lt (k - 1) k (by omega)
  have hmain : tvFallQ (k - 1) k * tvFallQ (n - 1) k ≈ 0 :=
    Q'.eqv_trans _ (0 * tvFallQ (n - 1) k) _
      (Q'.mul_eqv_congr_right _ _ _ hz) (Q'.zero_mul_eqv _)
  let T := Q'.ofNat k * tvFallQ (k - 1) (k - 1) *
    Q'.ofNat (m - (k - 1)) * tvFallQ (n - 1) (k - 1)
  have hrow : transvectFactorialCoeff m n k (k - 1) 1 ≈ -T := by
    refine Q'.eqv_trans _
      (tvFallQ (k - 1) k * tvFallQ (n - 1) k + -T) _
      (by simpa only [T] using hclosed) ?_
    refine Q'.eqv_trans _ ((0 : Q') + -T) _
      (Q'.add_eqv_congr_right _ _ _ hmain) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-T))
  have hzero := transvectFactorialCoeff_zero_second_closed m n k k
  have hk0 := tvFallQ_leading_shift k (k - 1)
  have hk' : Q'.ofNat k * tvFallQ (k - 1) (k - 1) ≈
      tvFallQ k k := by
    simpa only [show k - 1 + 1 = k by omega] using hk0
  have hn0 := tvFallQ_leading_shift n (k - 1)
  have hn' : Q'.ofNat n * tvFallQ (n - 1) (k - 1) ≈
      tvFallQ n k := by
    simpa only [show k - 1 + 1 = k by omega] using hn0
  let D := Q'.ofNat k * Q'.ofNat n
  let C := -(Q'.ofNat k * Q'.ofNat (m - (k - 1)))
  let U := tvFallQ k k
  let V := tvFallQ n k
  refine Q'.eqv_trans _ (D * (-T)) _
    (Q'.mul_eqv_congr_left D _ _ hrow) ?_
  refine Q'.eqv_trans _
    (C * ((Q'.ofNat k * tvFallQ (k - 1) (k - 1)) *
      (Q'.ofNat n * tvFallQ (n - 1) (k - 1)))) _
    (by simp only [D, C, T]; ring_qeqv) ?_
  refine Q'.eqv_trans _ (C * (U * V)) _
    (Q'.mul_eqv_congr_left C _ _ (mul_eqv_congr hk' hn')) ?_
  refine Q'.eqv_trans _
    (C * transvectFactorialCoeff m n k k 0) _
    (Q'.mul_eqv_congr_left C _ _ (Q'.eqv_symm (by
      simpa only [U, V] using hzero))) ?_
  simp only [C]
  ring_zero_qeqv

/-- The upper-adjacent row at `i=r`.  This is the coordinate-boundary
counterpart of `upper_second_one_scaled_to_base_zero`. -/
theorem upper_second_one_scaled_to_base_zero_lower_coordinate
    (a f r : Nat) (hrf : r ≤ f) :
    Q'.ofNat (f - r + 1) *
        transvectFactorialCoeff a (f + 2) (r + 1) r 1 ≈
      Q'.ofNat (f + 1) *
        (Q'.ofNat 0 * Q'.ofNat (f - r + 1) +
          -(Q'.ofNat (r + 1) * Q'.ofNat (a - r))) *
        transvectFactorialCoeff a f r r 0 := by
  have hclosed :=
    transvectFactorialCoeff_second_one_closed a (f + 2) (r + 1) r
  have hz := tvFallQ_eqv_zero_of_lt r (r + 1) (by omega)
  have hmain : tvFallQ r (r + 1) * tvFallQ (f + 1) (r + 1) ≈ 0 :=
    Q'.eqv_trans _ (0 * tvFallQ (f + 1) (r + 1)) _
      (Q'.mul_eqv_congr_right _ _ _ hz) (Q'.zero_mul_eqv _)
  let T := Q'.ofNat (r + 1) * tvFallQ r r *
    Q'.ofNat (a - r) * tvFallQ (f + 1) r
  have hrow :
      transvectFactorialCoeff a (f + 2) (r + 1) r 1 ≈ -T := by
    refine Q'.eqv_trans _
      (tvFallQ r (r + 1) * tvFallQ (f + 1) (r + 1) + -T) _
      (by simpa only [T,
        show f + 2 - 1 = f + 1 by omega,
        show r + 1 - 1 = r by omega] using hclosed) ?_
    refine Q'.eqv_trans _ ((0 : Q') + -T) _
      (Q'.add_eqv_congr_right _ _ _ hmain) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-T))
  have hzero := transvectFactorialCoeff_zero_second_closed a f r r
  have hlabel := tvFallQ_label_shift (f + 1) r (by omega)
  have hlabel' :
      Q'.ofNat (f + 1) * tvFallQ f r ≈
        Q'.ofNat (f - r + 1) * tvFallQ (f + 1) r := by
    simpa only [show f + 1 - r = f - r + 1 by omega] using hlabel
  let A := Q'.ofNat (f - r + 1)
  let G := Q'.ofNat (f + 1)
  let C := -(Q'.ofNat (r + 1) * Q'.ofNat (a - r))
  let U := tvFallQ r r
  let V1 := tvFallQ (f + 1) r
  let V := tvFallQ f r
  refine Q'.eqv_trans _ (A * (-T)) _
    (Q'.mul_eqv_congr_left A _ _ hrow) ?_
  refine Q'.eqv_trans _ ((C * U) * (A * V1)) _
    (by simp only [A, C, T, U, V1]; ring_qeqv) ?_
  refine Q'.eqv_trans _ ((C * U) * (G * V)) _
    (Q'.mul_eqv_congr_left (C * U) _ _ (Q'.eqv_symm (by
      simpa only [A, G, V1, V] using hlabel'))) ?_
  refine Q'.eqv_trans _ ((G * C) * (U * V)) _
    (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    ((G * C) * transvectFactorialCoeff a f r r 0) _
    (Q'.mul_eqv_congr_left (G * C) _ _ (Q'.eqv_symm (by
      simpa only [U, V] using hzero))) ?_
  simp only [G, C]
  ring_zero_qeqv

private theorem three_term_scale
    (P F G X Y Z : Q') :
    (P * (F * G)) * ((X + Y) + Z) ≈
      G * ((((P * F) * X + (P * F) * Y) + (P * F) * Z)) := by
  ring_qeqv

private theorem exchange_collect
    (G F A B I L AI J H O : Q') :
    G * (((A * B) * (H * O) +
        -(F * (I * L)) * (H * O)) +
      -(F * (AI * J)) * (H * O)) ≈
      G * ((A * B + -(F * (I * L + AI * J))) * (H * O)) := by
  ring_qeqv

private theorem neg_factor_reassoc (X H O : Q') :
    X * ((-H) * O) ≈ (-X) * (H * O) := by
  have hleft : X * ((-H) * O) ≈ -((X * H) * O) := by
    refine Q'.eqv_trans _ ((X * (-H)) * O) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv X (-H) O)) ?_
    refine Q'.eqv_trans _ (-(X * H) * O) _
      (Q'.mul_eqv_congr_right _ _ O (Q'.mul_neg_eqv X H)) ?_
    exact Q'.neg_mul_eqv (X * H) O
  have hright : (-X) * (H * O) ≈ -((X * H) * O) := by
    refine Q'.eqv_trans _ (((-X) * H) * O) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (-X) H O)) ?_
    refine Q'.eqv_trans _ (-(X * H) * O) _
      (Q'.mul_eqv_congr_right _ _ O (Q'.neg_mul_eqv X H)) ?_
    exact Q'.neg_mul_eqv (X * H) O
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

/-- The first-bulk exchange reduction on the exact lower coordinate face
`i=r`; its exceptional predecessor is supplied by the corrected endpoint
identity above. -/
theorem first_bulk_exchange_rows_scaled_lower_coordinate
    (a b c f p r i j l : Nat)
    (hj : 0 < j) (hl : 0 < l) (hsum : j + l = p)
    (hpb : p < b) (hpc : p < c)
    (hr : 0 < r) (hir : i = r) (hia : i ≤ a) :
    (Q'.ofNat p * (Q'.ofNat f * Q'.ofNat (f + 2))) *
        ((Q'.ofNat i * Q'.ofNat (b - j)) *
            (Q'.ofNat (c - l) *
              (transvectFactorialCoeff (b - 1) (c - 1) (p - 1) j l *
                transvectFactorialCoeff a f r (i - 1) 1)) +
          (Q'.ofNat i * Q'.ofNat (b - j)) *
            (Q'.ofNat l *
              (transvectFactorialCoeff (b - 1) (c - 1) (p - 1) j (l - 1) *
                transvectFactorialCoeff a f r i 0)) +
          -((Q'.ofNat (a - i) * Q'.ofNat j) *
            (Q'.ofNat (c - l) *
              (transvectFactorialCoeff (b - 1) (c - 1) (p - 1) (j - 1) l *
                transvectFactorialCoeff a f r i 0)))) ≈
      Q'.ofNat (f + 2) *
        (((Q'.ofNat j * Q'.ofNat (b - p) +
              -(Q'.ofNat l * Q'.ofNat (c - p))) *
            (Q'.ofNat (i - r) * Q'.ofNat (f - r) +
              -(Q'.ofNat r * Q'.ofNat (a - i + 1))) +
          -(Q'.ofNat f *
            (Q'.ofNat i * Q'.ofNat l +
              Q'.ofNat (a - i) * Q'.ofNat j))) *
        (transvectFactorialCoeff b c p j l *
          transvectFactorialCoeff a f r i 0)) := by
  let P := Q'.ofNat p
  let F := Q'.ofNat f
  let G := Q'.ofNat (f + 2)
  let I := Q'.ofNat i
  let J := Q'.ofNat j
  let L := Q'.ofNat l
  let Bj := Q'.ofNat (b - j)
  let Cl := Q'.ofNat (c - l)
  let Ai := Q'.ofNat (a - i)
  let A := J * Q'.ofNat (b - p) + -(L * Q'.ofNat (c - p))
  let B := Q'.ofNat (i - r) * Q'.ofNat (f - r) +
    -(Q'.ofNat r * Q'.ofNat (a - i + 1))
  let M := I * L + Ai * J
  let H0 := transvectFactorialCoeff (b - 1) (c - 1) (p - 1) j l
  let H1 := transvectFactorialCoeff (b - 1) (c - 1) (p - 1) j (l - 1)
  let H2 := transvectFactorialCoeff (b - 1) (c - 1) (p - 1) (j - 1) l
  let H := transvectFactorialCoeff b c p j l
  let O1 := transvectFactorialCoeff a f r (i - 1) 1
  let O := transvectFactorialCoeff a f r i 0
  have hinner0 := first_bulk_inner_above_reduced
    b c p j l hj hl hsum hpb hpc
  have hinner0' : P * ((Bj * Cl) * H0) ≈ A * H := by
    simpa only [P, Bj, Cl, H0, A, J, L, H] using hinner0
  have hinner1 := lowest_row_first_predecessor_scaled
    b c p j l hj hl hsum (by omega) (by omega)
  have hinner1' : (P * Bj) * H1 ≈ -H := by
    simpa only [P, Bj, H1, H] using hinner1
  have hinner2 := lowest_row_second_predecessor_scaled
    b c p j l hj hl hsum (by omega) (by omega)
  have hinner2' : (P * Cl) * H2 ≈ H := by
    simpa only [P, Cl, H2, H] using hinner2
  have houter0 := second_one_scaled_to_zero_at_lower_coordinate a f r hr
  have houter : (I * F) * O1 ≈ B * O := by
    simpa only [I, F, O1, B, O, hir, Nat.sub_self,
      show a - (r - 1) = a - r + 1 by omega] using houter0
  have hterm0 : (P * F) * ((I * Bj) * (Cl * (H0 * O1))) ≈
      (A * B) * (H * O) := by
    refine Q'.eqv_trans _
      (P * ((Bj * Cl) * H0) * ((I * F) * O1)) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ ((A * H) * (B * O)) _
      (mul_eqv_congr hinner0' houter) ?_
    ring_qeqv
  have hterm1 : (P * F) * ((I * Bj) * (L * (H1 * O))) ≈
      -(F * (I * L)) * (H * O) := by
    refine Q'.eqv_trans _
      (F * (I * L) * (((P * Bj) * H1) * O)) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ (F * (I * L) * ((-H) * O)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ O hinner1')) ?_
    exact neg_factor_reassoc (F * (I * L)) H O
  have hterm2 : (P * F) * (-((Ai * J) * (Cl * (H2 * O)))) ≈
      -(F * (Ai * J)) * (H * O) := by
    refine Q'.eqv_trans _
      (-(F * (Ai * J)) * (((P * Cl) * H2) * O)) _
      (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ O hinner2')
  refine Q'.eqv_trans _
    (G * (((P * F) * ((I * Bj) * (Cl * (H0 * O1))) +
      (P * F) * ((I * Bj) * (L * (H1 * O)))) +
      (P * F) * (-((Ai * J) * (Cl * (H2 * O)))))) _
    (three_term_scale P F G
      ((I * Bj) * (Cl * (H0 * O1)))
      ((I * Bj) * (L * (H1 * O)))
      (-((Ai * J) * (Cl * (H2 * O))))) ?_
  refine Q'.eqv_trans _
    (G * (((A * B) * (H * O) +
      -(F * (I * L)) * (H * O)) +
      -(F * (Ai * J)) * (H * O))) _
    (Q'.mul_eqv_congr_left G _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' hterm0 hterm1) hterm2)) ?_
  simpa only [P, F, G, I, J, L, Bj, Cl, Ai, A, B, M,
    H0, H1, H2, H, O1, O] using
      exchange_collect G F A B I L Ai J H O

/-- The lower adjacent carrier on the exact coordinate face `i=r`. -/
theorem first_bulk_lower_carrier_scaled_lower_coordinate
    {a b c d : Nat} (qm q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (i j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hir : i = q.r) :
    (Q'.ofNat q.p *
        (Q'.ofNat q.intermediate * Q'.ofNat (q.intermediate + 2))) *
        (omegaCorrectionLowerCoefficient a b c d q.p *
          (transvectFactorialCoeff b c qm.p j l *
            transvectFactorialCoeff a qm.intermediate qm.r i 1)) ≈
      Q'.ofNat q.intermediate *
        ((Q'.ofNat j * Q'.ofNat (b - q.p + 1) +
            -(Q'.ofNat l * Q'.ofNat (c - q.p + 1))) *
          (Q'.ofNat (i - q.r) *
              Q'.ofNat (q.intermediate - q.r + 1) +
            -(Q'.ofNat (q.r + 1) * Q'.ofNat (a - i)))) *
        (transvectFactorialCoeff b c q.p j l *
          transvectFactorialCoeff a q.intermediate q.r i 0) := by
  have hqr := Nat.le_min.mp q.r_le
  have hf : qm.intermediate = q.intermediate + 2 := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hrm : qm.r = q.r + 1 := by
    have hqm := Nat.le_min.mp qm.r_le
    have hq := Nat.le_min.mp q.r_le
    have hqp := Nat.le_min.mp q.p_le
    have hdegm := qm.degree_eq
    have hdeg := q.degree_eq
    unfold FixedRightCGChannel.intermediate at hqm hq hdegm hdeg
    omega
  let P := Q'.ofNat q.p
  let F := Q'.ofNat q.intermediate
  let G := Q'.ofNat (q.intermediate + 2)
  let G1 := Q'.ofNat (q.intermediate + 1)
  let U := Q'.ofNat (b - q.p + 1)
  let V := Q'.ofNat (c - q.p + 1)
  let R := Q'.ofNat (q.intermediate - q.r + 1)
  let A := Q'.ofNat j * U + -(Q'.ofNat l * V)
  let C := Q'.ofNat (i - q.r) * R +
    -(Q'.ofNat (q.r + 1) * Q'.ofNat (a - i))
  let L := omegaCorrectionLowerCoefficient a b c d q.p
  let Hm := transvectFactorialCoeff b c qm.p j l
  let Om := transvectFactorialCoeff a qm.intermediate qm.r i 1
  let H := transvectFactorialCoeff b c q.p j l
  let O := transvectFactorialCoeff a q.intermediate q.r i 0
  have hcoeff0 := omegaCorrectionLowerCoefficient_closed qm q hp hprev
  have hnum : Q'.ofNat
        ((b - q.p + 1) * (c - q.p + 1) *
          (q.intermediate - q.r + 1)) ≈ (U * V) * R := by
    refine Q'.eqv_trans _
      (Q'.ofNat ((b - q.p + 1) * (c - q.p + 1)) *
        Q'.ofNat (q.intermediate - q.r + 1)) _
      (Q'.eqv_symm (ofNat_mul_eqv
        ((b - q.p + 1) * (c - q.p + 1))
        (q.intermediate - q.r + 1))) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (ofNat_mul_eqv
        (b - q.p + 1) (c - q.p + 1)))
  have hcoeff : (G * G1) * L ≈ (U * V) * R :=
    Q'.eqv_trans _ _ _ (by simpa only [G, G1, L] using hcoeff0) hnum
  have hinner0 := one_above_lowest_scaled_to_lowest
    b c (q.p - 1) j l hj hl (by omega) (by omega) (by omega)
  have hinner : (P * (U * V)) * Hm ≈ A * H := by
    simpa only [P, U, V, A, Hm, H,
      show q.p - 1 + 1 = q.p by omega,
      show b - (q.p - 1) = b - q.p + 1 by omega,
      show c - (q.p - 1) = c - q.p + 1 by omega,
      show qm.p = q.p - 1 by omega] using hinner0
  have houter0 := upper_second_one_scaled_to_base_zero_lower_coordinate
    a q.intermediate q.r hqr.2
  have houter : R * Om ≈ (G1 * C) * O := by
    simpa only [R, Om, G1, C, O, hf, hrm, hir, Nat.sub_self] using houter0
  have hfactor :
      G1 * ((P * (F * G)) * (L * (Hm * Om))) ≈
        G1 * (F * (A * C) * (H * O)) := by
    refine Q'.eqv_trans _
      (F * (((G * G1) * L) * ((P * Hm) * Om))) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      (F * (((U * V) * R) * ((P * Hm) * Om))) _
      (Q'.mul_eqv_congr_left F _ _
        (Q'.mul_eqv_congr_right _ _ _ hcoeff)) ?_
    refine Q'.eqv_trans _
      (F * (((P * (U * V)) * Hm) * (R * Om))) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      (F * ((A * H) * ((G1 * C) * O))) _
      (Q'.mul_eqv_congr_left F _ _ (mul_eqv_congr hinner houter)) ?_
    ring_qeqv
  simpa only [P, F, G, G1, A, C, L, Hm, Om, H, O] using
    Q'.mul_left_cancel_of_pos
      (ofNat_pos_of_pos (q.intermediate + 1) (by omega)) hfactor

private theorem lower_outer_order {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1) : qm.r = q.r + 1 := by
  have hqm := Nat.le_min.mp qm.r_le
  have hq := Nat.le_min.mp q.r_le
  have hp := Nat.le_min.mp q.p_le
  have hdm := qm.degree_eq
  have hd := q.degree_eq
  unfold FixedRightCGChannel.intermediate at hqm hq hdm hd
  omega

private theorem scale_row_reassoc
    (P F G C W : Q') :
    (P * (F * G)) * (C * W) ≈ (P * ((F * G) * C)) * W := by
  ring_qeqv

/-- First-bulk shell closure on the exact coordinate face `i=r`. -/
theorem omegaCorrectionShellAt_first_bulk_lower_coordinate {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l : Nat)
    (hj : 0 < j) (hl : 0 < l) (hsum : j + l = q.p)
    (hpb : q.p < b) (hpc : q.p < c)
    (hr : 0 < q.r) (hir : i = q.r) (hia : i ≤ a) :
    OmegaCorrectionShellAt qm q qp hp i j l := by
  have hqr := Nat.le_min.mp q.r_le
  have hfpos : 0 < q.intermediate := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hf : qm.intermediate = q.intermediate + 2 := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hrm := lower_outer_order qm q hprev
  let qr := reducePositiveInnerRightChannel q hp
  have hqrp : qr.p = q.p - 1 := rfl
  have hqrr : qr.r = q.r := rfl
  have hqrf : qr.intermediate = q.intermediate :=
    reduced_intermediate_eq q hp
  let H0 := transvectFactorialCoeff
    (b - 1) (c - 1) (q.p - 1) j l
  let H1 := transvectFactorialCoeff
    (b - 1) (c - 1) (q.p - 1) j (l - 1)
  let H2 := transvectFactorialCoeff
    (b - 1) (c - 1) (q.p - 1) (j - 1) l
  let H := transvectFactorialCoeff b c q.p j l
  let Hm := transvectFactorialCoeff b c qm.p j l
  let O1 := transvectFactorialCoeff
    a q.intermediate q.r (i - 1) 1
  let O := transvectFactorialCoeff a q.intermediate q.r i 0
  let Om := transvectFactorialCoeff a qm.intermediate qm.r i 1
  have hx0 : rightShellFactorialCoefficient qr (i - 1) j l ≈
      H0 * O1 := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qr.p ≤ j + l)]
    unfold hahnEntry
    rw [show j + l - j = l by omega, hqrp,
      show j + l - (q.p - 1) = 1 by omega, hqrf, hqrr]
    exact Q'.eqv_refl _
  have hx1 : rightShellFactorialCoefficient qr i j (l - 1) ≈
      H1 * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qr.p ≤ j + (l - 1))]
    unfold hahnEntry
    rw [show j + (l - 1) - j = l - 1 by omega, hqrp,
      show j + (l - 1) - (q.p - 1) = 0 by omega, hqrf, hqrr]
    exact Q'.eqv_refl _
  have hx2 : rightShellFactorialCoefficient qr i (j - 1) l ≈
      H2 * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qr.p ≤ j - 1 + l)]
    unfold hahnEntry
    rw [show j - 1 + l - (j - 1) = l by omega, hqrp,
      show j - 1 + l - (q.p - 1) = 0 by omega, hqrf, hqrr]
    exact Q'.eqv_refl _
  have hx3 : rightShellFactorialCoefficient qr
      (i + 1) (j - 1) (l - 1) ≈ 0 := by
    unfold rightShellFactorialCoefficient
    rw [if_neg (by omega : ¬ qr.p ≤ j - 1 + (l - 1))]
    exact Q'.eqv_refl 0
  have hqm : rightShellFactorialCoefficient qm i j l ≈ Hm * Om := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qm.p ≤ j + l)]
    unfold hahnEntry
    rw [show j + l - j = l by omega,
      show j + l - qm.p = 1 by omega]
    exact Q'.eqv_refl _
  have hq : rightShellFactorialCoefficient q i j l ≈ H * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : q.p ≤ j + l)]
    unfold hahnEntry
    rw [show j + l - j = l by omega,
      show j + l - q.p = 0 by omega]
    exact Q'.eqv_refl _
  have hqp : rightShellFactorialCoefficient qp i j l ≈ 0 := by
    unfold rightShellFactorialCoefficient
    rw [if_neg (by omega : ¬ qp.p ≤ j + l)]
    exact Q'.eqv_refl 0
  let E :=
    (Q'.ofNat i * Q'.ofNat (b - j)) *
        (Q'.ofNat (c - l) * (H0 * O1)) +
      (Q'.ofNat i * Q'.ofNat (b - j)) *
        (Q'.ofNat l * (H1 * O)) +
      -((Q'.ofNat (a - i) * Q'.ofNat j) *
        (Q'.ofNat (c - l) * (H2 * O)))
  have hleft :
      omegaExchangeCorrection a b c
          (fun u v w => rightShellFactorialCoefficient qr u v w) i j l ≈
        E := by
    unfold omegaExchangeCorrection
    refine Q'.eqv_trans _
      ((Q'.ofNat i * Q'.ofNat (b - j)) *
          (Q'.ofNat (c - l) * (H0 * O1) +
            Q'.ofNat l * (H1 * O)) +
        -((Q'.ofNat (a - i) * Q'.ofNat j) *
          (Q'.ofNat (c - l) * (H2 * O) + Q'.ofNat l * 0))) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left _ _ _ hx0)
            (Q'.mul_eqv_congr_left _ _ _ hx1)))
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left _ _ _ hx2)
              (Q'.mul_eqv_congr_left _ _ _ hx3))))
    · simp only [E]
      ring_zero_qeqv
  let K := Q'.ofNat q.p *
    (Q'.ofNat q.intermediate * Q'.ofNat (q.intermediate + 2))
  let W := H * O
  let X0 :=
    ((Q'.ofNat j * Q'.ofNat (b - q.p) +
          -(Q'.ofNat l * Q'.ofNat (c - q.p))) *
        (Q'.ofNat (i - q.r) *
            Q'.ofNat (q.intermediate - q.r) +
          -(Q'.ofNat q.r * Q'.ofNat (a - i + 1))) +
      -(Q'.ofNat q.intermediate *
        (Q'.ofNat i * Q'.ofNat l +
          Q'.ofNat (a - i) * Q'.ofNat j)))
  let X := Q'.ofNat (q.intermediate + 2) * X0
  let Y := Q'.ofNat q.intermediate *
    ((Q'.ofNat j * Q'.ofNat (b - q.p + 1) +
          -(Q'.ofNat l * Q'.ofNat (c - q.p + 1))) *
      (Q'.ofNat (i - q.r) *
          Q'.ofNat (q.intermediate - q.r + 1) +
        -(Q'.ofNat (q.r + 1) * Q'.ofNat (a - i))))
  let S := firstBulkScalarQ a b c q.intermediate q.p q.r i j l
  have hleftScaled : K *
      omegaExchangeCorrection a b c
          (fun u v w => rightShellFactorialCoefficient qr u v w) i j l ≈
        X * W := by
    refine Q'.eqv_trans _ (K * E) _
      (Q'.mul_eqv_congr_left K _ _ hleft) ?_
    refine Q'.eqv_trans _
      (Q'.ofNat (q.intermediate + 2) * (X0 * W)) _ ?_ ?_
    · simpa only [K, E, X0, W, H0, H1, H2, H, O1, O] using
        first_bulk_exchange_rows_scaled_lower_coordinate
          a b c q.intermediate q.p q.r i j l
            hj hl hsum hpb hpc hr hir hia
    · simpa only [X] using Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat (q.intermediate + 2)) X0 W)
  let Lc := omegaCorrectionLowerCoefficient a b c d q.p
  let Dc := omegaCorrectionDiagonalCoefficient a b c d q.p
  have hright :
      omegaCorrectionLowerCoefficient a b c d q.p *
            rightShellFactorialCoefficient qm i j l +
          omegaCorrectionDiagonalCoefficient a b c d q.p *
            rightShellFactorialCoefficient q i j l +
          omegaCorrectionUpperCoefficient a b c d q.p *
            rightShellFactorialCoefficient qp i j l ≈
        Lc * (Hm * Om) + Dc * W := by
    refine Q'.eqv_trans _
      (Lc * (Hm * Om) + Dc * (H * O) +
        omegaCorrectionUpperCoefficient a b c d q.p * 0) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ hqm)
          (Q'.mul_eqv_congr_left _ _ _ hq))
        (Q'.mul_eqv_congr_left _ _ _ hqp)
    · simp only [Lc, Dc, W]
      ring_zero_qeqv
  have hlower : K * (Lc * (Hm * Om)) ≈ Y * W := by
    simpa only [K, Lc, Y, W, Hm, Om, H, O] using
      first_bulk_lower_carrier_scaled_lower_coordinate
        qm q hp hprev i j l hj hl hsum hpb hpc hir
  have hdiag0 := omegaCorrectionDiagonalCoefficient_first_bulk_scalar
    q hp i j l hpb hpc (by omega) hia hsum
  have hdiag : K * (Dc * W) ≈ S * W := by
    refine Q'.eqv_trans _
      ((Q'.ofNat q.p *
        ((Q'.ofNat q.intermediate * Q'.ofNat (q.intermediate + 2)) * Dc)) * W) _
      (by
        simpa only [K] using (scale_row_reassoc
          (Q'.ofNat q.p) (Q'.ofNat q.intermediate)
            (Q'.ofNat (q.intermediate + 2)) Dc W)) ?_
    exact Q'.mul_eqv_congr_right _ _ W (by
      simpa only [Dc, S] using hdiag0)
  have hrightScaled : K *
      (omegaCorrectionLowerCoefficient a b c d q.p *
            rightShellFactorialCoefficient qm i j l +
          omegaCorrectionDiagonalCoefficient a b c d q.p *
            rightShellFactorialCoefficient q i j l +
          omegaCorrectionUpperCoefficient a b c d q.p *
            rightShellFactorialCoefficient qp i j l) ≈
        (Y + S) * W := by
    refine Q'.eqv_trans _ (K * (Lc * (Hm * Om) + Dc * W)) _
      (Q'.mul_eqv_congr_left K _ _ hright) ?_
    refine Q'.eqv_trans _
      (K * (Lc * (Hm * Om)) + K * (Dc * W)) _
      (Q'.mul_add_eqv K _ _) ?_
    refine Q'.eqv_trans _ (Y * W + S * W) _
      (Q'.add_eqv_congr' hlower hdiag) ?_
    exact Q'.eqv_symm (Q'.add_mul_eqv Y S W)
  have hsplit : X ≈ Y + S := by
    simpa only [X, X0, Y, S] using
      firstBulkScalarQ_split
        a b c q.intermediate q.p q.r i j l
  have hscaled : K *
      omegaExchangeCorrection a b c
          (fun u v w => rightShellFactorialCoefficient qr u v w) i j l ≈
      K *
        (omegaCorrectionLowerCoefficient a b c d q.p *
              rightShellFactorialCoefficient qm i j l +
            omegaCorrectionDiagonalCoefficient a b c d q.p *
              rightShellFactorialCoefficient q i j l +
            omegaCorrectionUpperCoefficient a b c d q.p *
              rightShellFactorialCoefficient qp i j l) :=
    Q'.eqv_trans _ _ _ hleftScaled
      (Q'.eqv_trans _ ((Y + S) * W) _
        (Q'.mul_eqv_congr_right _ _ W hsplit)
        (Q'.eqv_symm hrightScaled))
  have hK : (0 : Q') < K := Q'.mul_pos
    (ofNat_pos_of_pos q.p hp)
    (Q'.mul_pos
      (ofNat_pos_of_pos q.intermediate hfpos)
      (ofNat_pos_of_pos (q.intermediate + 2) (by omega)))
  unfold OmegaCorrectionShellAt
  simpa only [qr] using Q'.mul_left_cancel_of_pos hK hscaled

/-- Guarded factorial correction on the exact coordinate face `i=r`. -/
theorem omegaCorrectionFactorialAt_first_bulk_lower_coordinate_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hr : 0 < q.r) (hir : i = q.r) (hia : i ≤ a) :
    OmegaCorrectionFactorialAt qm q qp hp i j l s := by
  apply (omegaCorrectionFactorialAt_on_shell_iff_shell
    qm q qp hp hprev hnext i j l s (by omega) hj hl hshell).2
  exact omegaCorrectionShellAt_first_bulk_lower_coordinate
    qm q qp hp hprev hnext i j l hj hl hsum hpb hpc hr hir hia

/-- Raw three-carrier correction on the exact coordinate face `i=r`. -/
theorem omegaCorrectionThreeCarrierAt_first_bulk_lower_coordinate_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hr : 0 < q.r) (hir : i = q.r) (hia : i ≤ a) :
    OmegaCorrectionThreeCarrierAt qm q qp i j l s :=
  (omegaCorrectionThreeCarrierAt_iff_factorial qm q qp hp i j l s).2
    (omegaCorrectionFactorialAt_first_bulk_lower_coordinate_on_shell
      qm q qp hp hprev hnext i j l s hj hl hshell hsum hpb hpc
        hr hir hia)

end YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary.second_one_scaled_to_zero_at_lower_coordinate
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary.lower_coordinate_truncated_shift_eq_one
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary.upper_second_one_scaled_to_base_zero_lower_coordinate
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary.first_bulk_exchange_rows_scaled_lower_coordinate
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary.first_bulk_lower_carrier_scaled_lower_coordinate
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary.omegaCorrectionShellAt_first_bulk_lower_coordinate
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary.omegaCorrectionFactorialAt_first_bulk_lower_coordinate_on_shell
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary.omegaCorrectionThreeCarrierAt_first_bulk_lower_coordinate_on_shell
