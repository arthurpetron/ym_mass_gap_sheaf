/-
# Complete reduced exchange polynomial at correction height one

The four live reduced-channel samples occur at outer coordinates
`(i-1,2)`, `(i,1)`, `(i,1)`, and `(i+1,0)`.  We lower the first outer
falling-factorial carrier by two orders, align all four samples without
division, and collect the exchange correction into one explicit scalar.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneScalarPolynomial

namespace YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor
open YMGap.Continuum.SU2OrderedRacahHeightOneScalarPolynomial

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

/-- Common outer carrier for the three shifted first coordinates. -/
def reducedHeightOneOuterExchangeBase {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i : Nat) : Q' :=
  tvFallQ (i - 1) (q.r - 4) *
    tvFallQ (q.intermediate - 2) (q.r - 2)

/-- Coordinate-two outer scalar after aligning from `i-1` to the common
order-`r-4` first-coordinate carrier. -/
def reducedHeightOneOuterTwoScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i : Nat) : Q' :=
  (Q'.ofNat (i - q.r + 3) * Q'.ofNat (i - q.r + 2)) *
    outerSecondTwoScalar a q.intermediate q.r (i - 1)

/-- Coordinate-one outer scalar at `i` over the common carrier. -/
def reducedHeightOneOuterOneScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i : Nat) : Q' :=
  (Q'.ofNat i * Q'.ofNat (i - q.r + 3)) *
    outerSecondOneScalarAtTwoBase a q.intermediate q.r i

/-- Coordinate-zero outer scalar at `i+1` over the common carrier. -/
def reducedHeightOneOuterZeroScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i : Nat) : Q' :=
  (Q'.ofNat (i + 1) * Q'.ofNat i) *
    outerSecondZeroScalarAtTwoBase q.intermediate q.r (i + 1)

/-- The coordinate-two outer row at `i-1` over the exchange base. -/
theorem reduced_height_one_outer_two_at_exchange_base {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i : Nat)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 2 ≤ q.intermediate) :
    transvectFactorialCoeff a q.intermediate q.r (i - 1) 2 ≈
      reducedHeightOneOuterExchangeBase q i *
        reducedHeightOneOuterTwoScalar q i := by
  let I := tvFallQ (i - 1) (q.r - 4)
  let N := tvFallQ (q.intermediate - 2) (q.r - 2)
  let A := Q'.ofNat (i - q.r + 3)
  let B := Q'.ofNat (i - q.r + 2)
  let S := outerSecondTwoScalar a q.intermediate q.r (i - 1)
  have hi1 := tvFallQ_trailing_shift (i - 1) (q.r - 4) (by omega)
  have hi1' : I * A ≈ tvFallQ (i - 1) (q.r - 3) := by
    simpa only [I, A,
      show i - 1 - (q.r - 4) = i - q.r + 3 by omega,
      show q.r - 4 + 1 = q.r - 3 by omega] using hi1
  have hi2 := tvFallQ_trailing_shift (i - 1) (q.r - 3) (by omega)
  have hi2' : tvFallQ (i - 1) (q.r - 3) * B ≈
      tvFallQ (i - 1) (q.r - 2) := by
    simpa only [B,
      show i - 1 - (q.r - 3) = i - q.r + 2 by omega,
      show q.r - 3 + 1 = q.r - 2 by omega] using hi2
  have hi : (I * A) * B ≈ tvFallQ (i - 1) (q.r - 2) :=
    Q'.eqv_trans _ (tvFallQ (i - 1) (q.r - 3) * B) _
      (Q'.mul_eqv_congr_right _ _ _ hi1') hi2'
  have hrow := transvectFactorialCoeff_second_two_factored
    a q.intermediate q.r (i - 1) (by omega) (by omega) hrn
  refine Q'.eqv_trans _
    ((tvFallQ (i - 1) (q.r - 2) * N) * S) _
    (by simpa only [N, S] using hrow) ?_
  refine Q'.eqv_trans _ ((((I * A) * B) * N) * S) _
    (Q'.mul_eqv_congr_right _ _ S
      (Q'.mul_eqv_congr_right _ _ N (Q'.eqv_symm hi))) ?_
  unfold reducedHeightOneOuterExchangeBase reducedHeightOneOuterTwoScalar
  simp only [I, N, A, B, S]
  ring_qeqv

/-- Either coordinate-one outer row at `i` over the exchange base. -/
theorem reduced_height_one_outer_one_at_exchange_base {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i : Nat)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 2 ≤ q.intermediate) :
    transvectFactorialCoeff a q.intermediate q.r i 1 ≈
      reducedHeightOneOuterExchangeBase q i *
        reducedHeightOneOuterOneScalar q i := by
  let I := tvFallQ (i - 1) (q.r - 4)
  let N := tvFallQ (q.intermediate - 2) (q.r - 2)
  let A := Q'.ofNat (i - q.r + 3)
  let J := Q'.ofNat i
  let S := outerSecondOneScalarAtTwoBase a q.intermediate q.r i
  have ht0 := tvFallQ_trailing_shift (i - 1) (q.r - 4) (by omega)
  have ht : I * A ≈ tvFallQ (i - 1) (q.r - 3) := by
    simpa only [I, A,
      show i - 1 - (q.r - 4) = i - q.r + 3 by omega,
      show q.r - 4 + 1 = q.r - 3 by omega] using ht0
  have hl0 := tvFallQ_leading_shift i (q.r - 3)
  have hl : J * tvFallQ (i - 1) (q.r - 3) ≈
      tvFallQ i (q.r - 2) := by
    simpa only [J, show i - 1 = i - 1 by rfl,
      show q.r - 3 + 1 = q.r - 2 by omega] using hl0
  have hi : J * (I * A) ≈ tvFallQ i (q.r - 2) :=
    Q'.eqv_trans _ (J * tvFallQ (i - 1) (q.r - 3)) _
      (Q'.mul_eqv_congr_left J _ _ ht) hl
  have hrow := transvectFactorialCoeff_second_one_at_two_base
    a q.intermediate q.r i (by omega) (by omega) hrn
  refine Q'.eqv_trans _ ((tvFallQ i (q.r - 2) * N) * S) _
    (by simpa only [N, S] using hrow) ?_
  refine Q'.eqv_trans _ (((J * (I * A)) * N) * S) _
    (Q'.mul_eqv_congr_right _ _ S
      (Q'.mul_eqv_congr_right _ _ N (Q'.eqv_symm hi))) ?_
  unfold reducedHeightOneOuterExchangeBase reducedHeightOneOuterOneScalar
  simp only [I, N, A, J, S]
  ring_qeqv

/-- The coordinate-zero outer row at `i+1` over the exchange base. -/
theorem reduced_height_one_outer_zero_at_exchange_base {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i : Nat)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 2 ≤ q.intermediate) :
    transvectFactorialCoeff a q.intermediate q.r (i + 1) 0 ≈
      reducedHeightOneOuterExchangeBase q i *
        reducedHeightOneOuterZeroScalar q i := by
  let I := tvFallQ (i - 1) (q.r - 4)
  let N := tvFallQ (q.intermediate - 2) (q.r - 2)
  let J := Q'.ofNat i
  let K := Q'.ofNat (i + 1)
  let S := outerSecondZeroScalarAtTwoBase q.intermediate q.r (i + 1)
  have hl1 := tvFallQ_leading_shift i (q.r - 4)
  have hl1' : J * I ≈ tvFallQ i (q.r - 3) := by
    simpa only [I, J, show i - 1 = i - 1 by rfl,
      show q.r - 4 + 1 = q.r - 3 by omega] using hl1
  have hl2 := tvFallQ_leading_shift (i + 1) (q.r - 3)
  have hl2' : K * tvFallQ i (q.r - 3) ≈
      tvFallQ (i + 1) (q.r - 2) := by
    simpa only [K, show i + 1 - 1 = i by omega,
      show q.r - 3 + 1 = q.r - 2 by omega] using hl2
  have hi : K * (J * I) ≈ tvFallQ (i + 1) (q.r - 2) :=
    Q'.eqv_trans _ (K * tvFallQ i (q.r - 3)) _
      (Q'.mul_eqv_congr_left K _ _ hl1') hl2'
  have hrow := transvectFactorialCoeff_zero_second_at_two_base
    a q.intermediate q.r (i + 1) (by omega) (by omega) hrn
  refine Q'.eqv_trans _
    ((tvFallQ (i + 1) (q.r - 2) * N) * S) _
    (by simpa only [N, S] using hrow) ?_
  refine Q'.eqv_trans _ (((K * (J * I)) * N) * S) _
    (Q'.mul_eqv_congr_right _ _ S
      (Q'.mul_eqv_congr_right _ _ N (Q'.eqv_symm hi))) ?_
  unfold reducedHeightOneOuterExchangeBase reducedHeightOneOuterZeroScalar
  simp only [I, N, J, K, S]
  ring_qeqv

/-- Common inner-outer carrier of every reduced height-one exchange sample. -/
def reducedHeightOneExchangeBase {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  reducedHeightOneInnerBase q j l * reducedHeightOneOuterExchangeBase q i

/-- Scalar of the `(i-1,j,l)` sample. -/
def reducedHeightOneExchangeTwoScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  reducedHeightOneInnerTwoScalar q j l *
    reducedHeightOneOuterTwoScalar q i

/-- Scalar of the `(i,j,l-1)` sample. -/
def reducedHeightOneExchangeFirstOneScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  reducedHeightOneInnerFirstOneScalar q j l *
    reducedHeightOneOuterOneScalar q i

/-- Scalar of the `(i,j-1,l)` sample. -/
def reducedHeightOneExchangeSecondOneScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  reducedHeightOneInnerSecondOneScalar q j l *
    reducedHeightOneOuterOneScalar q i

/-- Scalar of the `(i+1,j-1,l-1)` sample. -/
def reducedHeightOneExchangeZeroScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  reducedHeightOneInnerZeroScalar b c j l *
    reducedHeightOneOuterZeroScalar q i

/-- Common hypotheses for the four sample factorizations are kept explicit:
the first-coordinate alignment needs `r≥4`, while inner height two needs
strict room in both source labels. -/
theorem reduced_height_one_exchange_two_sample {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 2 ≤ q.intermediate) :
    rightShellFactorialCoefficient (reducePositiveInnerRightChannel q hp)
        (i - 1) j l ≈
      reducedHeightOneExchangeBase q i j l *
        reducedHeightOneExchangeTwoScalar q i j l := by
  let qr := reducePositiveInnerRightChannel q hp
  let H := transvectFactorialCoeff (b - 1) (c - 1) (q.p - 1) j l
  let O := transvectFactorialCoeff a q.intermediate q.r (i - 1) 2
  have hraw : rightShellFactorialCoefficient qr (i - 1) j l ≈ H * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by change q.p - 1 ≤ j + l; omega)]
    unfold hahnEntry
    rw [reduced_inner_order_eq q hp, reduced_intermediate_eq q hp]
    simp only [show j + l - j = l by omega,
      show j + l - (q.p - 1) = 2 by omega, H, O]
    exact Q'.eqv_refl _
  have hinner := reduced_height_one_inner_two_at_common_base
    q hp j l hj hl hheight hpb hpc
  have houter := reduced_height_one_outer_two_at_exchange_base
    q i hr hri hrn
  refine Q'.eqv_trans _ (H * O) _ hraw ?_
  refine Q'.eqv_trans _
    ((reducedHeightOneInnerBase q j l *
        reducedHeightOneInnerTwoScalar q j l) *
      (reducedHeightOneOuterExchangeBase q i *
        reducedHeightOneOuterTwoScalar q i)) _
    (mul_eqv_congr hinner houter) ?_
  unfold reducedHeightOneExchangeBase reducedHeightOneExchangeTwoScalar
  ring_qeqv

/-- Common-base form of the first coordinate-one sample. -/
theorem reduced_height_one_exchange_first_one_sample {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 2 ≤ q.intermediate) :
    rightShellFactorialCoefficient (reducePositiveInnerRightChannel q hp)
        i j (l - 1) ≈
      reducedHeightOneExchangeBase q i j l *
        reducedHeightOneExchangeFirstOneScalar q i j l := by
  let qr := reducePositiveInnerRightChannel q hp
  let H := transvectFactorialCoeff
    (b - 1) (c - 1) (q.p - 1) j (l - 1)
  let O := transvectFactorialCoeff a q.intermediate q.r i 1
  have hraw : rightShellFactorialCoefficient qr i j (l - 1) ≈ H * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by change q.p - 1 ≤ j + (l - 1); omega)]
    unfold hahnEntry
    rw [reduced_inner_order_eq q hp, reduced_intermediate_eq q hp]
    simp only [show j + (l - 1) - j = l - 1 by omega,
      show j + (l - 1) - (q.p - 1) = 1 by omega, H, O]
    exact Q'.eqv_refl _
  have hinner := reduced_height_one_inner_first_one_at_common_base
    q hp j l hj hl hheight hpb hpc
  have houter := reduced_height_one_outer_one_at_exchange_base
    q i hr hri hrn
  refine Q'.eqv_trans _ (H * O) _ hraw ?_
  refine Q'.eqv_trans _
    ((reducedHeightOneInnerBase q j l *
        reducedHeightOneInnerFirstOneScalar q j l) *
      (reducedHeightOneOuterExchangeBase q i *
        reducedHeightOneOuterOneScalar q i)) _
    (mul_eqv_congr hinner houter) ?_
  unfold reducedHeightOneExchangeBase
    reducedHeightOneExchangeFirstOneScalar
  ring_qeqv

/-- Common-base form of the second coordinate-one sample. -/
theorem reduced_height_one_exchange_second_one_sample {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 2 ≤ q.intermediate) :
    rightShellFactorialCoefficient (reducePositiveInnerRightChannel q hp)
        i (j - 1) l ≈
      reducedHeightOneExchangeBase q i j l *
        reducedHeightOneExchangeSecondOneScalar q i j l := by
  let qr := reducePositiveInnerRightChannel q hp
  let H := transvectFactorialCoeff
    (b - 1) (c - 1) (q.p - 1) (j - 1) l
  let O := transvectFactorialCoeff a q.intermediate q.r i 1
  have hraw : rightShellFactorialCoefficient qr i (j - 1) l ≈ H * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by change q.p - 1 ≤ j - 1 + l; omega)]
    unfold hahnEntry
    rw [reduced_inner_order_eq q hp, reduced_intermediate_eq q hp]
    simp only [show j - 1 + l - (j - 1) = l by omega,
      show j - 1 + l - (q.p - 1) = 1 by omega, H, O]
    exact Q'.eqv_refl _
  have hinner := reduced_height_one_inner_second_one_at_common_base
    q hp j l hj hl hheight hpb hpc
  have houter := reduced_height_one_outer_one_at_exchange_base
    q i hr hri hrn
  refine Q'.eqv_trans _ (H * O) _ hraw ?_
  refine Q'.eqv_trans _
    ((reducedHeightOneInnerBase q j l *
        reducedHeightOneInnerSecondOneScalar q j l) *
      (reducedHeightOneOuterExchangeBase q i *
        reducedHeightOneOuterOneScalar q i)) _
    (mul_eqv_congr hinner houter) ?_
  unfold reducedHeightOneExchangeBase
    reducedHeightOneExchangeSecondOneScalar
  ring_qeqv

/-- Common-base form of the coordinate-zero sample. -/
theorem reduced_height_one_exchange_zero_sample {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 2 ≤ q.intermediate) :
    rightShellFactorialCoefficient (reducePositiveInnerRightChannel q hp)
        (i + 1) (j - 1) (l - 1) ≈
      reducedHeightOneExchangeBase q i j l *
        reducedHeightOneExchangeZeroScalar q i j l := by
  let qr := reducePositiveInnerRightChannel q hp
  let H := transvectFactorialCoeff
    (b - 1) (c - 1) (q.p - 1) (j - 1) (l - 1)
  let O := transvectFactorialCoeff a q.intermediate q.r (i + 1) 0
  have hraw : rightShellFactorialCoefficient qr
      (i + 1) (j - 1) (l - 1) ≈ H * O := by
    unfold rightShellFactorialCoefficient
    rw [if_pos (by change q.p - 1 ≤ j - 1 + (l - 1); omega)]
    unfold hahnEntry
    rw [reduced_inner_order_eq q hp, reduced_intermediate_eq q hp]
    simp only [show j - 1 + (l - 1) - (j - 1) = l - 1 by omega,
      show j - 1 + (l - 1) - (q.p - 1) = 0 by omega, H, O]
    exact Q'.eqv_refl _
  have hinner := reduced_height_one_inner_zero_at_common_base
    q hp j l hj hl hheight hpb hpc
  have houter := reduced_height_one_outer_zero_at_exchange_base
    q i hr hri hrn
  refine Q'.eqv_trans _ (H * O) _ hraw ?_
  refine Q'.eqv_trans _
    ((reducedHeightOneInnerBase q j l *
        reducedHeightOneInnerZeroScalar b c j l) *
      (reducedHeightOneOuterExchangeBase q i *
        reducedHeightOneOuterZeroScalar q i)) _
    (mul_eqv_congr hinner houter) ?_
  unfold reducedHeightOneExchangeBase reducedHeightOneExchangeZeroScalar
  ring_qeqv

/-- Explicit scalar left after collecting all four exchange samples. -/
def reducedHeightOneExchangeScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  (Q'.ofNat i * Q'.ofNat (b - j)) *
      (Q'.ofNat (c - l) * reducedHeightOneExchangeTwoScalar q i j l +
        Q'.ofNat l * reducedHeightOneExchangeFirstOneScalar q i j l) +
    -((Q'.ofNat (a - i) * Q'.ofNat j) *
      (Q'.ofNat (c - l) *
          reducedHeightOneExchangeSecondOneScalar q i j l +
        Q'.ofNat l * reducedHeightOneExchangeZeroScalar q i j l))

/-- **Complete reduced exchange polynomial.**  The full four-term correction
is one common factorial carrier times one explicit division-free scalar. -/
theorem reduced_height_one_exchange_full_polynomial {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 2 ≤ q.intermediate) :
    omegaExchangeCorrection a b c
        (fun u v w => rightShellFactorialCoefficient
          (reducePositiveInnerRightChannel q hp) u v w) i j l ≈
      reducedHeightOneExchangeBase q i j l *
        reducedHeightOneExchangeScalar q i j l := by
  let B := reducedHeightOneExchangeBase q i j l
  let X0 := reducedHeightOneExchangeTwoScalar q i j l
  let X1 := reducedHeightOneExchangeFirstOneScalar q i j l
  let X2 := reducedHeightOneExchangeSecondOneScalar q i j l
  let X3 := reducedHeightOneExchangeZeroScalar q i j l
  have hx0 := reduced_height_one_exchange_two_sample
    q hp i j l hj hl hheight hpb hpc hr hri hrn
  have hx1 := reduced_height_one_exchange_first_one_sample
    q hp i j l hj hl hheight hpb hpc hr hri hrn
  have hx2 := reduced_height_one_exchange_second_one_sample
    q hp i j l hj hl hheight hpb hpc hr hri hrn
  have hx3 := reduced_height_one_exchange_zero_sample
    q hp i j l hj hl hheight hpb hpc hr hri hrn
  unfold omegaExchangeCorrection
  refine Q'.eqv_trans _
    ((Q'.ofNat i * Q'.ofNat (b - j)) *
        (Q'.ofNat (c - l) * (B * X0) +
          Q'.ofNat l * (B * X1)) +
      -((Q'.ofNat (a - i) * Q'.ofNat j) *
        (Q'.ofNat (c - l) * (B * X2) +
          Q'.ofNat l * (B * X3)))) _ ?_ ?_
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
  · unfold reducedHeightOneExchangeScalar
    simp only [B, X0, X1, X2, X3]
    ring_qeqv

end YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial.reduced_height_one_outer_two_at_exchange_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial.reduced_height_one_outer_one_at_exchange_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial.reduced_height_one_outer_zero_at_exchange_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial.reduced_height_one_exchange_two_sample
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial.reduced_height_one_exchange_first_one_sample
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial.reduced_height_one_exchange_second_one_sample
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial.reduced_height_one_exchange_zero_sample
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial.reduced_height_one_exchange_full_polynomial
