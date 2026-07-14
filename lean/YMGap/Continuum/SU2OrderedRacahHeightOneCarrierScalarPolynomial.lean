/-
# Common inner carrier for the three height-one adjacent channels

At correction height one the lower, diagonal, and upper channels expose
inner rows two above, one above, and exactly at lowest support.  This module
puts all three over the lower height-two factorial carrier and records the
remaining division-free scalars.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial

namespace YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation
open YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation
open YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; try ac_rfl))

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ (b * c) _
    (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

/-- Common inner carrier, indexed by the middle channel. -/
def heightOneCarrierInnerBase {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (j l : Nat) : Q' :=
  heightTwoCommonFactor b c (q.p - 1) j l

/-- Lower-channel height-two scalar. -/
def heightOneCarrierLowerInnerScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (j l : Nat) : Q' :=
  heightTwoFullPolynomial b c (q.p - 1) j l

/-- Diagonal height-one scalar over the lower carrier. -/
def heightOneCarrierDiagonalInnerScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (j l : Nat) : Q' :=
  -((Q'.ofNat q.p * Q'.ofNat (b - q.p + 1) *
      Q'.ofNat (c - q.p + 1)) *
    (Q'.ofNat l * Q'.ofNat (c - q.p) +
      -(Q'.ofNat j * Q'.ofNat (b - q.p))))

/-- Upper lowest-row scalar over the lower carrier. -/
def heightOneCarrierUpperInnerScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) : Q' :=
  (Q'.ofNat (q.p + 1) * Q'.ofNat q.p) *
    ((Q'.ofNat (b - q.p + 1) * Q'.ofNat (b - q.p)) *
      (Q'.ofNat (c - q.p + 1) * Q'.ofNat (c - q.p)))

/-- The lower adjacent row is already the chosen common-base row. -/
theorem height_one_carrier_lower_inner_at_common_base {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1)
    (j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 1 ≤ b) (hpc : q.p + 1 ≤ c) :
    transvectFactorialCoeff b c qm.p j l ≈
      heightOneCarrierInnerBase q j l *
        heightOneCarrierLowerInnerScalar q j l := by
  have hrow := transvectFactorialCoeff_two_above_lowest_closed
    b c qm.p j l hj hl (by omega) (by omega) (by omega)
  simpa only [heightOneCarrierInnerBase, heightOneCarrierLowerInnerScalar,
    show qm.p = q.p - 1 by omega] using hrow

/-- The middle one-above-lowest row over the lower height-two carrier. -/
theorem height_one_carrier_diagonal_inner_at_common_base {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 1 ≤ b) (hpc : q.p + 1 ≤ c) :
    transvectFactorialCoeff b c q.p j l ≈
      heightOneCarrierInnerBase q j l *
        heightOneCarrierDiagonalInnerScalar q j l := by
  let P := tvPhase (l - 2)
  let K := Q'.ofNat (tvFact (q.p - 1))
  let M := tvFallQ (b - j) (l - 2)
  let N := tvFallQ (c - l) (j - 2)
  let A := Q'.ofNat q.p
  let B := Q'.ofNat (b - q.p + 1)
  let C := Q'.ofNat (c - q.p + 1)
  let S := Q'.ofNat l * Q'.ofNat (c - q.p) +
    -(Q'.ofNat j * Q'.ofNat (b - q.p))
  have hrow := transvectFactorialCoeff_one_above_lowest_closed
    b c q.p j l (by omega) (by omega) hheight hpb hpc
  have hp0 := tvPhase_succ (l - 2)
  have hphase : tvPhase (l - 1) ≈ -P := by
    simpa only [P, show l - 2 + 1 = l - 1 by omega] using hp0
  have hfact : A * K ≈ Q'.ofNat (tvFact q.p) := by
    have hrec : tvFact q.p = q.p * tvFact (q.p - 1) := by
      have hpred : q.p - 1 + 1 = q.p := by omega
      calc
        tvFact q.p = tvFact (q.p - 1 + 1) :=
          congrArg tvFact hpred.symm
        _ = (q.p - 1 + 1) * tvFact (q.p - 1) := rfl
        _ = q.p * tvFact (q.p - 1) := by rw [hpred]
    rw [hrec]
    simpa only [A, K] using ofNat_mul_eqv q.p (tvFact (q.p - 1))
  have hm0 := tvFallQ_trailing_shift (b - j) (l - 2) (by omega)
  have hm : M * B ≈ tvFallQ (b - j) (l - 1) := by
    simpa only [M, B, show b - j - (l - 2) = b - q.p + 1 by omega,
      show l - 2 + 1 = l - 1 by omega] using hm0
  have hn0 := tvFallQ_trailing_shift (c - l) (j - 2) (by omega)
  have hn : N * C ≈ tvFallQ (c - l) (j - 1) := by
    simpa only [N, C, show c - l - (j - 2) = c - q.p + 1 by omega,
      show j - 2 + 1 = j - 1 by omega] using hn0
  refine Q'.eqv_trans _
    ((tvPhase (l - 1) * Q'.ofNat (tvFact q.p) *
        tvFallQ (b - j) (l - 1) * tvFallQ (c - l) (j - 1)) * S) _
    (by simpa only [S] using hrow) ?_
  refine Q'.eqv_trans _
    (((-P) * (A * K) * (M * B) * (N * C)) * S) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ S
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr hphase (Q'.eqv_symm hfact))
            (Q'.eqv_symm hm))
        (Q'.eqv_symm hn))
  · unfold heightOneCarrierInnerBase heightOneCarrierDiagonalInnerScalar
      heightTwoCommonFactor
    simp only [P, K, M, N, A, B, C, S]
    ring_qeqv

/-- The upper lowest row over the same lower height-two carrier. -/
theorem height_one_carrier_upper_inner_at_common_base {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 1 ≤ b) (hpc : q.p + 1 ≤ c) :
    transvectFactorialCoeff b c (q.p + 1) j l ≈
      heightOneCarrierInnerBase q j l *
        heightOneCarrierUpperInnerScalar q := by
  let P := tvPhase (l - 2)
  let K := Q'.ofNat (tvFact (q.p - 1))
  let A := Q'.ofNat q.p
  let A1 := Q'.ofNat (q.p + 1)
  let M := tvFallQ (b - j) (l - 2)
  let N := tvFallQ (c - l) (j - 2)
  let B1 := Q'.ofNat (b - q.p + 1)
  let B0 := Q'.ofNat (b - q.p)
  let C1 := Q'.ofNat (c - q.p + 1)
  let C0 := Q'.ofNat (c - q.p)
  have hrow := transvectFactorialCoeff_lowest_row_closed
    b c (q.p + 1) j l hheight
  have hp1 := tvPhase_succ (l - 2)
  have hp2 := tvPhase_succ (l - 1)
  have hphase1 : tvPhase (l - 1) ≈ -P := by
    simpa only [P, show l - 2 + 1 = l - 1 by omega] using hp1
  have hphase2 : tvPhase l ≈ -tvPhase (l - 1) := by
    simpa only [show l - 1 + 1 = l by omega] using hp2
  have hphase : tvPhase l ≈ P := by
    refine Q'.eqv_trans _ (-tvPhase (l - 1)) _ hphase2 ?_
    exact Q'.eqv_trans _ (-(-P)) _
      (Q'.neg_eqv_congr _ _ hphase1) (Q'.neg_neg_eqv P)
  have hf0 : A * K ≈ Q'.ofNat (tvFact q.p) := by
    have hrec : tvFact q.p = q.p * tvFact (q.p - 1) := by
      have hpred : q.p - 1 + 1 = q.p := by omega
      calc
        tvFact q.p = tvFact (q.p - 1 + 1) :=
          congrArg tvFact hpred.symm
        _ = (q.p - 1 + 1) * tvFact (q.p - 1) := rfl
        _ = q.p * tvFact (q.p - 1) := by rw [hpred]
    rw [hrec]
    simpa only [A, K] using ofNat_mul_eqv q.p (tvFact (q.p - 1))
  have hf1 : A1 * Q'.ofNat (tvFact q.p) ≈
      Q'.ofNat (tvFact (q.p + 1)) := by
    rw [show tvFact (q.p + 1) = (q.p + 1) * tvFact q.p by rfl]
    simpa only [A1] using ofNat_mul_eqv (q.p + 1) (tvFact q.p)
  have hfact : A1 * (A * K) ≈ Q'.ofNat (tvFact (q.p + 1)) :=
    Q'.eqv_trans _ (A1 * Q'.ofNat (tvFact q.p)) _
      (Q'.mul_eqv_congr_left A1 _ _ hf0) hf1
  have hm1 := tvFallQ_trailing_shift (b - j) (l - 2) (by omega)
  have hm1' : M * B1 ≈ tvFallQ (b - j) (l - 1) := by
    simpa only [M, B1,
      show b - j - (l - 2) = b - q.p + 1 by omega,
      show l - 2 + 1 = l - 1 by omega] using hm1
  have hm2 := tvFallQ_trailing_shift (b - j) (l - 1) (by omega)
  have hm2' : tvFallQ (b - j) (l - 1) * B0 ≈
      tvFallQ (b - j) l := by
    simpa only [B0, show b - j - (l - 1) = b - q.p by omega,
      show l - 1 + 1 = l by omega] using hm2
  have hm : (M * B1) * B0 ≈ tvFallQ (b - j) l :=
    Q'.eqv_trans _ (tvFallQ (b - j) (l - 1) * B0) _
      (Q'.mul_eqv_congr_right _ _ B0 hm1') hm2'
  have hn1 := tvFallQ_trailing_shift (c - l) (j - 2) (by omega)
  have hn1' : N * C1 ≈ tvFallQ (c - l) (j - 1) := by
    simpa only [N, C1,
      show c - l - (j - 2) = c - q.p + 1 by omega,
      show j - 2 + 1 = j - 1 by omega] using hn1
  have hn2 := tvFallQ_trailing_shift (c - l) (j - 1) (by omega)
  have hn2' : tvFallQ (c - l) (j - 1) * C0 ≈
      tvFallQ (c - l) j := by
    simpa only [C0, show c - l - (j - 1) = c - q.p by omega,
      show j - 1 + 1 = j by omega] using hn2
  have hn : (N * C1) * C0 ≈ tvFallQ (c - l) j :=
    Q'.eqv_trans _ (tvFallQ (c - l) (j - 1) * C0) _
      (Q'.mul_eqv_congr_right _ _ C0 hn1') hn2'
  refine Q'.eqv_trans _
    (tvPhase l * Q'.ofNat (tvFact (q.p + 1)) *
      tvFallQ (b - j) l * tvFallQ (c - l) j) _ hrow ?_
  refine Q'.eqv_trans _
    (P * (A1 * (A * K)) * ((M * B1) * B0) * ((N * C1) * C0)) _ ?_ ?_
  · exact mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr hphase (Q'.eqv_symm hfact))
          (Q'.eqv_symm hm))
      (Q'.eqv_symm hn)
  · unfold heightOneCarrierInnerBase heightOneCarrierUpperInnerScalar
      heightTwoCommonFactor
    simp only [P, K, A, A1, M, N, B1, B0, C1, C0]
    ring_qeqv

/-- Common outer carrier of the lower, diagonal, and upper channels after
using their forced label shifts `(n+2,r+1)`, `(n,r)`, `(n-2,r-1)`. -/
def heightOneCarrierOuterBase (n r i : Nat) : Q' :=
  tvFallQ i (r - 1) * tvFallQ (n - 2) (r - 3)

/-- Lower coordinate-two scalar over the common outer carrier. -/
def heightOneCarrierLowerOuterScalar (a n r i : Nat) : Q' :=
  (Q'.ofNat n * Q'.ofNat (n - 1)) *
    outerSecondTwoScalar a (n + 2) (r + 1) i

/-- Diagonal coordinate-one scalar over the common outer carrier. -/
def heightOneCarrierDiagonalOuterScalar (a n r i : Nat) : Q' :=
  (Q'.ofNat (n - 1) * Q'.ofNat (n - r + 1)) *
    (Q'.ofNat (i - r + 1) * Q'.ofNat (n - r) +
      -(Q'.ofNat r * Q'.ofNat (a - i)))

/-- Upper coordinate-zero scalar over the common outer carrier. -/
def heightOneCarrierUpperOuterScalar (n r : Nat) : Q' :=
  Q'.ofNat (n - r + 1) * Q'.ofNat (n - r)

/-- Lower outer row after the two forced leading label shifts. -/
theorem height_one_carrier_lower_outer_at_common_base
    (a n r i : Nat) (hr : 3 ≤ r) (hri : r + 1 ≤ i)
    (hrn : r + 1 ≤ n) :
    transvectFactorialCoeff a (n + 2) (r + 1) i 2 ≈
      heightOneCarrierOuterBase n r i *
        heightOneCarrierLowerOuterScalar a n r i := by
  let I := tvFallQ i (r - 1)
  let N := tvFallQ (n - 2) (r - 3)
  let A := Q'.ofNat (n - 1)
  let B := Q'.ofNat n
  let S := outerSecondTwoScalar a (n + 2) (r + 1) i
  have hn1 := tvFallQ_leading_shift (n - 1) (r - 3)
  have hn1' : A * N ≈ tvFallQ (n - 1) (r - 2) := by
    simpa only [A, N, show n - 1 - 1 = n - 2 by omega,
      show r - 3 + 1 = r - 2 by omega] using hn1
  have hn2 := tvFallQ_leading_shift n (r - 2)
  have hn2' : B * tvFallQ (n - 1) (r - 2) ≈
      tvFallQ n (r - 1) := by
    simpa only [B, show r - 2 + 1 = r - 1 by omega] using hn2
  have hn : B * (A * N) ≈ tvFallQ n (r - 1) :=
    Q'.eqv_trans _ (B * tvFallQ (n - 1) (r - 2)) _
      (Q'.mul_eqv_congr_left B _ _ hn1') hn2'
  have hrow := transvectFactorialCoeff_second_two_factored
    a (n + 2) (r + 1) i (by omega) hri (by omega)
  refine Q'.eqv_trans _ ((I * tvFallQ n (r - 1)) * S) _
    (by simpa only [I, S, show r + 1 - 2 = r - 1 by omega,
      show n + 2 - 2 = n by omega] using hrow) ?_
  refine Q'.eqv_trans _ ((I * (B * (A * N))) * S) _
    (Q'.mul_eqv_congr_right _ _ S
      (Q'.mul_eqv_congr_left I _ _ (Q'.eqv_symm hn))) ?_
  unfold heightOneCarrierOuterBase heightOneCarrierLowerOuterScalar
  simp only [I, N, A, B, S]
  ring_qeqv

/-- Diagonal outer row over the same carrier. -/
theorem height_one_carrier_diagonal_outer_at_common_base
    (a n r i : Nat) (hr : 3 ≤ r) (hri : r + 1 ≤ i)
    (hrn : r + 1 ≤ n) :
    transvectFactorialCoeff a n r i 1 ≈
      heightOneCarrierOuterBase n r i *
        heightOneCarrierDiagonalOuterScalar a n r i := by
  let I := tvFallQ i (r - 1)
  let N := tvFallQ (n - 2) (r - 3)
  let A := Q'.ofNat (n - r + 1)
  let B := Q'.ofNat (n - 1)
  let S := Q'.ofNat (i - r + 1) * Q'.ofNat (n - r) +
    -(Q'.ofNat r * Q'.ofNat (a - i))
  have ht0 := tvFallQ_trailing_shift (n - 2) (r - 3) (by omega)
  have ht : N * A ≈ tvFallQ (n - 2) (r - 2) := by
    simpa only [N, A, show n - 2 - (r - 3) = n - r + 1 by omega,
      show r - 3 + 1 = r - 2 by omega] using ht0
  have hl0 := tvFallQ_leading_shift (n - 1) (r - 2)
  have hl : B * tvFallQ (n - 2) (r - 2) ≈
      tvFallQ (n - 1) (r - 1) := by
    simpa only [B, show n - 1 - 1 = n - 2 by omega,
      show r - 2 + 1 = r - 1 by omega] using hl0
  have hn : B * (N * A) ≈ tvFallQ (n - 1) (r - 1) :=
    Q'.eqv_trans _ (B * tvFallQ (n - 2) (r - 2)) _
      (Q'.mul_eqv_congr_left B _ _ ht) hl
  have hrow := transvectFactorialCoeff_second_one_factored
    a n r i (by omega) (by omega) (by omega)
  refine Q'.eqv_trans _ ((I * tvFallQ (n - 1) (r - 1)) * S) _
    (by simpa only [I, S] using hrow) ?_
  refine Q'.eqv_trans _ ((I * (B * (N * A))) * S) _
    (Q'.mul_eqv_congr_right _ _ S
      (Q'.mul_eqv_congr_left I _ _ (Q'.eqv_symm hn))) ?_
  unfold heightOneCarrierOuterBase heightOneCarrierDiagonalOuterScalar
  simp only [I, N, A, B, S]
  ring_qeqv

/-- Upper outer row over the same carrier. -/
theorem height_one_carrier_upper_outer_at_common_base
    (a n r i : Nat) (hr : 3 ≤ r)
    (hrn : r + 1 ≤ n) :
    transvectFactorialCoeff a (n - 2) (r - 1) i 0 ≈
      heightOneCarrierOuterBase n r i *
        heightOneCarrierUpperOuterScalar n r := by
  let I := tvFallQ i (r - 1)
  let N := tvFallQ (n - 2) (r - 3)
  let A := Q'.ofNat (n - r + 1)
  let B := Q'.ofNat (n - r)
  have hn1 := tvFallQ_trailing_shift (n - 2) (r - 3) (by omega)
  have hn1' : N * A ≈ tvFallQ (n - 2) (r - 2) := by
    simpa only [N, A, show n - 2 - (r - 3) = n - r + 1 by omega,
      show r - 3 + 1 = r - 2 by omega] using hn1
  have hn2 := tvFallQ_trailing_shift (n - 2) (r - 2) (by omega)
  have hn2' : tvFallQ (n - 2) (r - 2) * B ≈
      tvFallQ (n - 2) (r - 1) := by
    simpa only [B, show n - 2 - (r - 2) = n - r by omega,
      show r - 2 + 1 = r - 1 by omega] using hn2
  have hn : (N * A) * B ≈ tvFallQ (n - 2) (r - 1) :=
    Q'.eqv_trans _ (tvFallQ (n - 2) (r - 2) * B) _
      (Q'.mul_eqv_congr_right _ _ B hn1') hn2'
  have hrow := transvectFactorialCoeff_zero_second_closed
    a (n - 2) (r - 1) i
  refine Q'.eqv_trans _ (I * tvFallQ (n - 2) (r - 1)) _
    (by simpa only [I] using hrow) ?_
  refine Q'.eqv_trans _ (I * ((N * A) * B)) _
    (Q'.mul_eqv_congr_left I _ _ (Q'.eqv_symm hn)) ?_
  unfold heightOneCarrierOuterBase heightOneCarrierUpperOuterScalar
  simp only [I, N, A, B]
  ring_qeqv

private theorem adjacent_intermediate {a b c d : Nat}
    (q0 q1 : FixedRightCGChannel a b c d) (hp : q1.p = q0.p + 1) :
    q1.intermediate = q0.intermediate - 2 := by
  have hp1 := Nat.le_min.mp q1.p_le
  unfold FixedRightCGChannel.intermediate
  omega

private theorem adjacent_outer_order {a b c d : Nat}
    (q0 q1 : FixedRightCGChannel a b c d) (hp : q1.p = q0.p + 1) :
    q0.r = q1.r + 1 := by
  have hf := adjacent_intermediate q0 q1 hp
  have hr0 := Nat.le_min.mp q0.r_le
  have hr1 := Nat.le_min.mp q1.r_le
  have hp1 := Nat.le_min.mp q1.p_le
  have hf2 : 2 ≤ q0.intermediate := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hd0 := q0.degree_eq
  have hd1 := q1.degree_eq
  have hd0' : a + q0.intermediate = d + 2 * q0.r := by
    unfold FixedRightCGChannel.intermediate at hd0 ⊢
    omega
  have hd1' : a + q1.intermediate = d + 2 * q1.r := by
    unfold FixedRightCGChannel.intermediate at hd1 ⊢
    omega
  omega

/-- Common inner-outer carrier of all three adjacent channels. -/
def heightOneCarrierBase {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  heightOneCarrierInnerBase q j l *
    heightOneCarrierOuterBase q.intermediate q.r i

/-- Lower-channel sample scalar. -/
def heightOneCarrierLowerScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  heightOneCarrierLowerInnerScalar q j l *
    heightOneCarrierLowerOuterScalar a q.intermediate q.r i

/-- Diagonal-channel sample scalar. -/
def heightOneCarrierDiagonalScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  heightOneCarrierDiagonalInnerScalar q j l *
    heightOneCarrierDiagonalOuterScalar a q.intermediate q.r i

/-- Upper-channel sample scalar. -/
def heightOneCarrierUpperScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) : Q' :=
  heightOneCarrierUpperInnerScalar q *
    heightOneCarrierUpperOuterScalar q.intermediate q.r

/-- Lower adjacent right-shell sample over the common carrier. -/
theorem height_one_carrier_lower_sample {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 1 ≤ b) (hpc : q.p + 1 ≤ c)
    (hr : 3 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 1 ≤ q.intermediate) :
    rightShellFactorialCoefficient qm i j l ≈
      heightOneCarrierBase q i j l *
        heightOneCarrierLowerScalar q i j l := by
  have hfm : qm.intermediate = q.intermediate + 2 := by
    have hf := adjacent_intermediate qm q hprev
    have hpq := Nat.le_min.mp q.p_le
    unfold FixedRightCGChannel.intermediate at hf ⊢
    omega
  have hrm : qm.r = q.r + 1 := adjacent_outer_order qm q hprev
  let H := transvectFactorialCoeff b c qm.p j l
  let O := transvectFactorialCoeff a qm.intermediate qm.r i 2
  have hraw : rightShellFactorialCoefficient qm i j l ≈ H * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qm.p ≤ j + l)]
    unfold hahnEntry
    simp only [show j + l - j = l by omega,
      show j + l - qm.p = 2 by omega, H, O]
    exact Q'.eqv_refl _
  have hinner := height_one_carrier_lower_inner_at_common_base
    qm q hprev j l hj hl hheight hpb hpc
  have houter0 := height_one_carrier_lower_outer_at_common_base
    a q.intermediate q.r i hr hri hrn
  have houter : O ≈ heightOneCarrierOuterBase q.intermediate q.r i *
      heightOneCarrierLowerOuterScalar a q.intermediate q.r i := by
    simpa only [O, hfm, hrm] using houter0
  refine Q'.eqv_trans _ (H * O) _ hraw ?_
  refine Q'.eqv_trans _
    ((heightOneCarrierInnerBase q j l *
        heightOneCarrierLowerInnerScalar q j l) *
      (heightOneCarrierOuterBase q.intermediate q.r i *
        heightOneCarrierLowerOuterScalar a q.intermediate q.r i)) _
    (mul_eqv_congr hinner houter) ?_
  unfold heightOneCarrierBase heightOneCarrierLowerScalar
  ring_qeqv

/-- Middle-channel right-shell sample over the common carrier. -/
theorem height_one_carrier_diagonal_sample {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 1 ≤ b) (hpc : q.p + 1 ≤ c)
    (hr : 3 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 1 ≤ q.intermediate) :
    rightShellFactorialCoefficient q i j l ≈
      heightOneCarrierBase q i j l *
        heightOneCarrierDiagonalScalar q i j l := by
  let H := transvectFactorialCoeff b c q.p j l
  let O := transvectFactorialCoeff a q.intermediate q.r i 1
  have hraw : rightShellFactorialCoefficient q i j l ≈ H * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : q.p ≤ j + l)]
    unfold hahnEntry
    simp only [show j + l - j = l by omega,
      show j + l - q.p = 1 by omega, H, O]
    exact Q'.eqv_refl _
  have hinner := height_one_carrier_diagonal_inner_at_common_base
    q hp j l hj hl hheight hpb hpc
  have houter := height_one_carrier_diagonal_outer_at_common_base
    a q.intermediate q.r i hr hri hrn
  refine Q'.eqv_trans _ (H * O) _ hraw ?_
  refine Q'.eqv_trans _
    ((heightOneCarrierInnerBase q j l *
        heightOneCarrierDiagonalInnerScalar q j l) *
      (heightOneCarrierOuterBase q.intermediate q.r i *
        heightOneCarrierDiagonalOuterScalar a q.intermediate q.r i)) _
    (mul_eqv_congr hinner houter) ?_
  unfold heightOneCarrierBase heightOneCarrierDiagonalScalar
  ring_qeqv

/-- Upper adjacent right-shell sample over the common carrier. -/
theorem height_one_carrier_upper_sample {a b c d : Nat}
    (q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hnext : qp.p = q.p + 1)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 1 ≤ b) (hpc : q.p + 1 ≤ c)
    (hr : 3 ≤ q.r)
    (hrn : q.r + 1 ≤ q.intermediate) :
    rightShellFactorialCoefficient qp i j l ≈
      heightOneCarrierBase q i j l * heightOneCarrierUpperScalar q := by
  have hfp : qp.intermediate = q.intermediate - 2 :=
    adjacent_intermediate q qp hnext
  have hrp : q.r = qp.r + 1 := adjacent_outer_order q qp hnext
  let H := transvectFactorialCoeff b c qp.p j l
  let O := transvectFactorialCoeff a qp.intermediate qp.r i 0
  have hraw : rightShellFactorialCoefficient qp i j l ≈ H * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by omega : qp.p ≤ j + l)]
    unfold hahnEntry
    simp only [show j + l - j = l by omega,
      show j + l - qp.p = 0 by omega, H, O]
    exact Q'.eqv_refl _
  have hinner0 := height_one_carrier_upper_inner_at_common_base
    q hp j l hj hl hheight hpb hpc
  have hinner : H ≈ heightOneCarrierInnerBase q j l *
      heightOneCarrierUpperInnerScalar q := by
    simpa only [H, hnext] using hinner0
  have houter0 := height_one_carrier_upper_outer_at_common_base
    a q.intermediate q.r i hr hrn
  have houter : O ≈ heightOneCarrierOuterBase q.intermediate q.r i *
      heightOneCarrierUpperOuterScalar q.intermediate q.r := by
    simpa only [O, hfp, show qp.r = q.r - 1 by omega] using houter0
  refine Q'.eqv_trans _ (H * O) _ hraw ?_
  refine Q'.eqv_trans _
    ((heightOneCarrierInnerBase q j l *
        heightOneCarrierUpperInnerScalar q) *
      (heightOneCarrierOuterBase q.intermediate q.r i *
        heightOneCarrierUpperOuterScalar q.intermediate q.r)) _
    (mul_eqv_congr hinner houter) ?_
  unfold heightOneCarrierBase heightOneCarrierUpperScalar
  ring_qeqv

/-- The complete carrier-side scalar, including the exact Jacobi
coefficients. -/
def heightOneCarrierSideScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  omegaCorrectionLowerCoefficient a b c d q.p *
      heightOneCarrierLowerScalar q i j l +
    omegaCorrectionDiagonalCoefficient a b c d q.p *
      heightOneCarrierDiagonalScalar q i j l +
    omegaCorrectionUpperCoefficient a b c d q.p *
      heightOneCarrierUpperScalar q

/-- **Complete three-carrier polynomial.** -/
theorem height_one_carrier_side_full_polynomial {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) (hnext : qp.p = q.p + 1)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 1 ≤ b) (hpc : q.p + 1 ≤ c)
    (hr : 3 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 1 ≤ q.intermediate) :
    omegaCorrectionLowerCoefficient a b c d q.p *
          rightShellFactorialCoefficient qm i j l +
        omegaCorrectionDiagonalCoefficient a b c d q.p *
          rightShellFactorialCoefficient q i j l +
        omegaCorrectionUpperCoefficient a b c d q.p *
          rightShellFactorialCoefficient qp i j l ≈
      heightOneCarrierBase q i j l *
        heightOneCarrierSideScalar q i j l := by
  let B := heightOneCarrierBase q i j l
  let L := heightOneCarrierLowerScalar q i j l
  let D := heightOneCarrierDiagonalScalar q i j l
  let U := heightOneCarrierUpperScalar q
  have hlower := height_one_carrier_lower_sample
    qm q hprev i j l hj hl hheight hpb hpc hr hri hrn
  have hdiag := height_one_carrier_diagonal_sample
    q hp i j l hj hl hheight hpb hpc hr hri hrn
  have hupp := height_one_carrier_upper_sample
    q qp hp hnext i j l hj hl hheight hpb hpc hr hrn
  refine Q'.eqv_trans _
    (omegaCorrectionLowerCoefficient a b c d q.p * (B * L) +
      omegaCorrectionDiagonalCoefficient a b c d q.p * (B * D) +
      omegaCorrectionUpperCoefficient a b c d q.p * (B * U)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hlower)
        (Q'.mul_eqv_congr_left _ _ _ hdiag))
      (Q'.mul_eqv_congr_left _ _ _ hupp)
  · unfold heightOneCarrierSideScalar
    simp only [B, L, D, U]
    ring_qeqv

end YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial.height_one_carrier_lower_inner_at_common_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial.height_one_carrier_diagonal_inner_at_common_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial.height_one_carrier_upper_inner_at_common_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial.height_one_carrier_lower_outer_at_common_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial.height_one_carrier_diagonal_outer_at_common_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial.height_one_carrier_upper_outer_at_common_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial.height_one_carrier_lower_sample
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial.height_one_carrier_diagonal_sample
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial.height_one_carrier_upper_sample
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial.height_one_carrier_side_full_polynomial
