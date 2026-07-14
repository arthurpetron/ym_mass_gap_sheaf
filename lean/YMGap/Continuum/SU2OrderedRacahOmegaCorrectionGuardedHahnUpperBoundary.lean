/-
# Upper outer boundary for the guarded Hahn correction

This module closes the endpoint `r = f`.  The second-index-one row then sits
at `k=n`; its first falling-factorial branch vanishes and the remaining branch
matches the same scalar formula used in the bulk.
-/

import YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnBoundary

namespace YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnUpperBoundary

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
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnBoundary

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

/-- Endpoint `k=n` of the second-index-one row bridge. -/
theorem second_one_scaled_to_zero_next_upper
    (m n x : Nat) (hn : 0 < n) :
    (Q'.ofNat (x + 1) * Q'.ofNat n) *
        transvectFactorialCoeff m n n x 1 ≈
      (Q'.ofNat (x - n + 1) * Q'.ofNat (n - n) +
          -(Q'.ofNat n * Q'.ofNat (m - x))) *
        transvectFactorialCoeff m n n (x + 1) 0 := by
  have hclosed := transvectFactorialCoeff_second_one_closed m n n x
  have hz := tvFallQ_eqv_zero_of_lt (n - 1) n (by omega)
  have hmain : tvFallQ x n * tvFallQ (n - 1) n ≈ 0 :=
    Q'.eqv_trans _ (tvFallQ x n * 0) _
      (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)
  let T := Q'.ofNat n * tvFallQ x (n - 1) * Q'.ofNat (m - x) *
    tvFallQ (n - 1) (n - 1)
  have hrow : transvectFactorialCoeff m n n x 1 ≈ -T := by
    refine Q'.eqv_trans _
      (tvFallQ x n * tvFallQ (n - 1) n + -T) _
      (by simpa only [T] using hclosed) ?_
    refine Q'.eqv_trans _ ((0 : Q') + -T) _
      (Q'.add_eqv_congr_right _ _ _ hmain) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-T))
  have hzero := transvectFactorialCoeff_zero_second_closed m n n (x + 1)
  have hx0 := tvFallQ_leading_shift (x + 1) (n - 1)
  have hx : Q'.ofNat (x + 1) * tvFallQ x (n - 1) ≈
      tvFallQ (x + 1) n := by
    simpa only [show x + 1 - 1 = x by omega,
      show n - 1 + 1 = n by omega] using hx0
  have hn0 := tvFallQ_leading_shift n (n - 1)
  have hn' : Q'.ofNat n * tvFallQ (n - 1) (n - 1) ≈
      tvFallQ n n := by
    simpa only [show n - 1 + 1 = n by omega] using hn0
  let D := Q'.ofNat (x + 1) * Q'.ofNat n
  let C := -(Q'.ofNat n * Q'.ofNat (m - x))
  let U := tvFallQ (x + 1) n
  let V := tvFallQ n n
  refine Q'.eqv_trans _ (D * (-T)) _
    (Q'.mul_eqv_congr_left D _ _ hrow) ?_
  refine Q'.eqv_trans _
    (C * ((Q'.ofNat (x + 1) * tvFallQ x (n - 1)) *
      (Q'.ofNat n * tvFallQ (n - 1) (n - 1)))) _
    (by simp only [D, C, T]; ring_qeqv) ?_
  refine Q'.eqv_trans _ (C * (U * V)) _
    (Q'.mul_eqv_congr_left C _ _ (mul_eqv_congr hx hn')) ?_
  refine Q'.eqv_trans _ (C *
      transvectFactorialCoeff m n n (x + 1) 0) _
    (Q'.mul_eqv_congr_left C _ _ (Q'.eqv_symm (by
      simpa only [U, V] using hzero))) ?_
  simp only [C, Nat.sub_self]
  ring_zero_qeqv

/-- Second-index-one bridge closed at both contraction-order endpoints. -/
theorem second_one_scaled_to_zero_next_closed
    (m n k x : Nat) (hk : 0 < k) (hkx : k ≤ x) (hkn : k ≤ n) :
    (Q'.ofNat (x + 1) * Q'.ofNat n) *
        transvectFactorialCoeff m n k x 1 ≈
      (Q'.ofNat (x - k + 1) * Q'.ofNat (n - k) +
          -(Q'.ofNat k * Q'.ofNat (m - x))) *
        transvectFactorialCoeff m n k (x + 1) 0 := by
  rcases Nat.lt_or_eq_of_le hkn with hlt | rfl
  · exact second_one_scaled_to_zero_next_nonnegative m n k x hkx hlt
  · exact second_one_scaled_to_zero_next_upper m k x hk

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

/-- The first-bulk exchange reduction at the upper outer endpoint `r=f`. -/
theorem first_bulk_exchange_rows_scaled_upper_boundary
    (a b c f p r i j l : Nat)
    (hj : 0 < j) (hl : 0 < l) (hsum : j + l = p)
    (hpb : p < b) (hpc : p < c)
    (hr : 0 < r) (hrf : r = f) (hri : r < i) (hia : i ≤ a) :
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
  have houter0 := second_one_scaled_to_zero_next_closed
    a f r (i - 1) hr (by omega) (by omega)
  have houter : (I * F) * O1 ≈ B * O := by
    simpa only [I, F, O1, B, O,
      show i - 1 + 1 = i by omega,
      show i - 1 - r + 1 = i - r by omega,
      show a - (i - 1) = a - i + 1 by omega] using houter0
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

private theorem ofNat_pos_of_pos (n : Nat) (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

/-- First-bulk shell closure on the exact upper outer face `r=f`. -/
theorem omegaCorrectionShellAt_first_bulk_upper_boundary {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l : Nat)
    (hj : 0 < j) (hl : 0 < l) (hsum : j + l = q.p)
    (hpb : q.p < b) (hpc : q.p < c)
    (hr : 0 < q.r) (hrf : q.r = q.intermediate)
    (hri : q.r < i) (hia : i ≤ a) :
    OmegaCorrectionShellAt qm q qp hp i j l := by
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
        first_bulk_exchange_rows_scaled_upper_boundary
          a b c q.intermediate q.p q.r i j l
            hj hl hsum hpb hpc hr hrf hri hia
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
      first_bulk_lower_carrier_scaled
        qm q hp hprev i j l hj hl hsum hpb hpc hri
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
      (ofNat_pos_of_pos q.intermediate (by omega))
      (ofNat_pos_of_pos (q.intermediate + 2) (by omega)))
  unfold OmegaCorrectionShellAt
  simpa only [qr] using Q'.mul_left_cancel_of_pos hK hscaled

/-- Guarded factorial correction on the exact upper outer face `r=f`. -/
theorem omegaCorrectionFactorialAt_first_bulk_upper_boundary_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hr : 0 < q.r) (hrf : q.r = q.intermediate)
    (hri : q.r < i) (hia : i ≤ a) :
    OmegaCorrectionFactorialAt qm q qp hp i j l s := by
  apply (omegaCorrectionFactorialAt_on_shell_iff_shell
    qm q qp hp hprev hnext i j l s hi hj hl hshell).2
  exact omegaCorrectionShellAt_first_bulk_upper_boundary
    qm q qp hp hprev hnext i j l hj hl hsum hpb hpc hr hrf hri hia

/-- Raw three-carrier correction on the exact upper outer face `r=f`. -/
theorem omegaCorrectionThreeCarrierAt_first_bulk_upper_boundary_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hr : 0 < q.r) (hrf : q.r = q.intermediate)
    (hri : q.r < i) (hia : i ≤ a) :
    OmegaCorrectionThreeCarrierAt qm q qp i j l s :=
  (omegaCorrectionThreeCarrierAt_iff_factorial qm q qp hp i j l s).2
    (omegaCorrectionFactorialAt_first_bulk_upper_boundary_on_shell
      qm q qp hp hprev hnext i j l s hi hj hl hshell hsum hpb hpc
        hr hrf hri hia)

end YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnUpperBoundary

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnUpperBoundary.second_one_scaled_to_zero_next_upper
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnUpperBoundary.second_one_scaled_to_zero_next_closed
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnUpperBoundary.first_bulk_exchange_rows_scaled_upper_boundary
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnUpperBoundary.omegaCorrectionShellAt_first_bulk_upper_boundary
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnUpperBoundary.omegaCorrectionFactorialAt_first_bulk_upper_boundary_on_shell
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnUpperBoundary.omegaCorrectionThreeCarrierAt_first_bulk_upper_boundary_on_shell
