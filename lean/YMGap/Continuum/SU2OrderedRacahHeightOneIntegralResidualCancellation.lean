/-
# Final integer certificate for strict-bulk height-one cancellation

The residual is now a polynomial over natural and integer casts.  The proof
below uses only the physical channel equations, the height-one equation, and
supported-coordinate subtraction identities before integer normalization.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualTransport
import YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualCertificate

namespace YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualCancellation

set_option maxHeartbeats 50000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation
open YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation
open YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor
open YMGap.Continuum.SU2OrderedRacahHeightOneScalarPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneScaledResidualPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneQuadraticNormalForm
open YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualTransport
open YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl
private theorem ofInt_num (z : Int) : (Q'.ofInt z).num = z := rfl
private theorem ofInt_den (z : Int) : ((Q'.ofInt z).den : Int) = 1 := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl

private theorem int_pred_sub_add_two (x y : Int) :
    x - 1 - y + 2 = x - y + 1 := by omega

private theorem int_pred_sub_add_one (x y : Int) :
    x - 1 - y + 1 = x - y := by omega

private theorem int_sub_pred (x y : Int) :
    x - (y - 1) = x - y + 1 := by omega

private theorem int_sub_succ (x y : Int) :
    x - (y + 1) = x - y - 1 := by omega

private theorem int_add_two_sub_pred (x y : Int) :
    x + 2 - y - 1 = x + 1 - y := by omega

private theorem int_succ_sub_one (x : Int) : x + 1 - 1 = x := by omega

private theorem int_succ_sub_pred (x y : Int) :
    x + 1 - y - 1 = x - y := by omega

private theorem int_add_one_one (x : Int) : x + 1 + 1 = x + 2 := by omega

private theorem int_add_two_one (x : Int) : x + 2 + 1 = x + 3 := by omega

/-- The fully integral residual vanishes on the supported strict bulk. -/
theorem height_one_integral_residual_zero {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat)
    (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hia : i + 1 ≤ a)
    (hrn : q.r + 2 ≤ q.intermediate) :
    heightOneIntegralResidualPolynomial q i j l ≈ 0 := by
  have hbc : b + c = 2 * q.p + q.intermediate := by
    have hpq := Nat.le_min.mp q.p_le
    unfold FixedRightCGChannel.intermediate
    omega
  have had : a + q.intermediate = d + 2 * q.r := by
    have hd := q.degree_eq
    have hqr := Nat.le_min.mp q.r_le
    unfold FixedRightCGChannel.intermediate at hd hqr ⊢
    omega
  have hC : (c : Int) = 2 * (q.p : Int) + (q.intermediate : Int) - (b : Int) := by
    have h := congrArg Int.ofNat hbc
    push_cast at h
    omega
  have hD : (d : Int) = (a : Int) + (q.intermediate : Int) - 2 * (q.r : Int) := by
    have h := congrArg Int.ofNat had
    push_cast at h
    omega
  have hL : (l : Int) = (q.p : Int) + 1 - (j : Int) := by
    have h := congrArg Int.ofNat hheight
    push_cast at h
    omega
  have hbm : (b - 1) - (q.p - 1) = b - q.p := by omega
  have hcm : (c - 1) - (q.p - 1) = c - q.p := by omega
  have him2 : i - 1 - q.r + 2 = i - q.r + 1 := by omega
  have him1 : i - 1 - q.r + 1 = i - q.r := by omega
  have ham : a - (i - 1) = a - i + 1 := by omega
  have hbp : ((b - q.p : Nat) : Int) = (b : Int) - (q.p : Int) := by omega
  have hcp : ((c - q.p : Nat) : Int) = (c : Int) - (q.p : Int) := by omega
  have hnr : ((q.intermediate - q.r : Nat) : Int) =
      (q.intermediate : Int) - (q.r : Int) := by omega
  have hbj : ((b - j : Nat) : Int) = (b : Int) - (j : Int) := by omega
  have hcl : ((c - l : Nat) : Int) = (c : Int) - (l : Int) := by omega
  have hl1 : ((l - 1 : Nat) : Int) = (l : Int) - 1 := by omega
  have hj1 : ((j - 1 : Nat) : Int) = (j : Int) - 1 := by omega
  have hbp1 : ((b - q.p - 1 : Nat) : Int) =
      (b : Int) - (q.p : Int) - 1 := by omega
  have hcp1 : ((c - q.p - 1 : Nat) : Int) =
      (c : Int) - (q.p : Int) - 1 := by omega
  have hir : ((i - q.r : Nat) : Int) = (i : Int) - (q.r : Int) := by omega
  have hnr1 : ((q.intermediate - q.r - 1 : Nat) : Int) =
      (q.intermediate : Int) - (q.r : Int) - 1 := by omega
  have hai : ((a - i : Nat) : Int) = (a : Int) - (i : Int) := by omega
  have hr1 : ((q.r - 1 : Nat) : Int) = (q.r : Int) - 1 := by omega
  have hn1 : ((q.intermediate - 1 : Nat) : Int) =
      (q.intermediate : Int) - 1 := by omega
  have hirp : ((i + 1 - q.r : Nat) : Int) =
      (i : Int) + 1 - (q.r : Int) := by omega
  have hbpPrev : ((b - (q.p - 1) : Nat) : Int) =
      (b : Int) - (q.p : Int) + 1 := by omega
  have hcpPrev : ((c - (q.p - 1) : Nat) : Int) =
      (c : Int) - (q.p : Int) + 1 := by omega
  have hbpPrev1 : ((b - (q.p - 1) - 1 : Nat) : Int) =
      (b : Int) - (q.p : Int) := by omega
  have hcpPrev1 : ((c - (q.p - 1) - 1 : Nat) : Int) =
      (c : Int) - (q.p : Int) := by omega
  have hirNext : ((i - (q.r + 1) : Nat) : Int) =
      (i : Int) - (q.r : Int) - 1 := by omega
  have hnrNext : ((q.intermediate + 1 - q.r : Nat) : Int) =
      (q.intermediate : Int) + 1 - (q.r : Int) := by omega
  have hnrNext1 : ((q.intermediate + 1 - q.r - 1 : Nat) : Int) =
      (q.intermediate : Int) - (q.r : Int) := by omega
  have hai1 : ((a - i - 1 : Nat) : Int) = (a : Int) - (i : Int) - 1 := by omega
  have hb1 : ((b - 1 : Nat) : Int) = (b : Int) - 1 := by omega
  have hc1 : ((c - 1 : Nat) : Int) = (c : Int) - 1 := by omega
  have har : ((a - q.r : Nat) : Int) = (a : Int) - (q.r : Int) := by omega
  have hanr : ((a + q.intermediate - q.r : Nat) : Int) =
      (a : Int) + (q.intermediate : Int) - (q.r : Int) := by omega
  unfold heightOneIntegralResidualPolynomial heightOneJacobiScale
    heightOneBulkExchangeScale heightOneIntegralExchangeScalar
    heightOneExchangeTwoIntegralScalar heightTwoFullPolynomialTwice
    reducedHeightOneOuterTwoIntegralScalar outerSecondTwoIntegralScalar
    heightOneExchangeFirstOneTwice heightOneExchangeSecondOneTwice
    heightOneExchangeZeroTwice reducedHeightOneExchangeFirstOneScalar
    reducedHeightOneExchangeSecondOneScalar reducedHeightOneExchangeZeroScalar
    reducedHeightOneInnerFirstOneScalar reducedHeightOneInnerSecondOneScalar
    reducedHeightOneInnerZeroScalar reducedHeightOneOuterOneScalar
    reducedHeightOneOuterZeroScalar outerSecondOneScalarAtTwoBase
    outerSecondZeroScalarAtTwoBase heightOneBulkCarrierScale
    heightOneIntegralScaledCarrierSideScalar heightOneScaledLowerCoefficient
    heightOneScaledDiagonalCoefficient heightOneScaledUpperCoefficient
    heightOneCarrierLowerIntegralScalar
    heightOneCarrierLowerOuterIntegralScalar
    heightOneCarrierDiagonalScalar heightOneCarrierUpperScalar
    heightOneCarrierDiagonalInnerScalar heightOneCarrierUpperInnerScalar
    heightOneCarrierDiagonalOuterScalar heightOneCarrierUpperOuterScalar
    omegaCorrectionDiagonalNumerator diagonalNum casimir4
  simp only [hbm, hcm, him2, him1, ham]
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, neg_num, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, ofInt_num, ofInt_den, zero_num_cast, zero_den_cast,
    heightTwoFullPolynomialTwice, outerSecondTwoIntegralScalar]
  push_cast
  rw [hbp, hcp, hnr, hbj, hcl, hl1, hj1, hbp1, hcp1, hir, hnr1,
    hai, hr1, hn1, hirp, hbpPrev, hcpPrev, hbpPrev1, hcpPrev1,
    hirNext, hnrNext, hnrNext1, hai1, hb1, hc1, har, hanr,
    hC, hD, hL]
  simp only [if_neg (by omega : q.intermediate ≠ 0)]
  have hcert := height_one_integral_residual_int_identity
    (a : Int) (b : Int) (q.intermediate : Int) (q.p : Int)
    (q.r : Int) (i : Int) (j : Int)
  unfold heightOneIntegralResidualInt heightOneJacobiScaleInt
    heightOneExchangeScaleInt heightOneCarrierScaleInt
    heightOneIntegralExchangeInt heightOneIntegralCarrierInt
    heightTwoInt outerTwoInt outerOneInt outerZeroInt
    diagonalInt casimirInt at hcert
  simp only [int_pred_sub_add_two, int_pred_sub_add_one, int_sub_pred,
    int_sub_succ, int_add_two_sub_pred, int_succ_sub_one, int_succ_sub_pred,
    int_add_one_one, int_add_two_one] at hcert ⊢
  simpa only [Int.mul_one, Int.one_mul, Int.zero_mul, Int.mul_zero,
    Int.sub_eq_add_neg, Int.mul_assoc] using hcert

end YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualCancellation

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualCancellation.height_one_integral_residual_zero
