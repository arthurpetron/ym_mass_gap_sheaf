/-
# Exact strict-bulk residual polynomial at correction height one

The reduced exchange side and the three-carrier side have each been
collected over their own common carrier.  In the strict inner and outer
bulk, these two carriers themselves share a smaller division-free base.
This module aligns them and exposes the complete remaining scalar residual.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial

namespace YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation
open YMGap.Continuum.SU2OrderedRacahHeightOneScalarPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial

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

/-- Smallest common inner carrier in the strict height-one bulk. -/
def heightOneBulkInnerBase {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (j l : Nat) : Q' :=
  tvPhase (l - 2) * Q'.ofNat (tvFact (q.p - 1)) *
    tvFallQ (b - 1 - j) (l - 3) * tvFallQ (c - 1 - l) (j - 3)

/-- Smallest common outer carrier. -/
def heightOneBulkOuterBase {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i : Nat) : Q' :=
  tvFallQ (i - 1) (q.r - 4) *
    tvFallQ (q.intermediate - 2) (q.r - 3)

/-- Common carrier of the complete correction residual. -/
def heightOneBulkResidualBase {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  heightOneBulkInnerBase q j l * heightOneBulkOuterBase q i

/-- Multiplier taking the residual base to the reduced exchange carrier. -/
def heightOneBulkExchangeScale {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) : Q' :=
  (Q'.ofNat (b - q.p + 1) * Q'.ofNat (c - q.p + 1)) *
    Q'.ofNat (q.intermediate - q.r + 1)

/-- Multiplier taking the residual base to the three-carrier base. -/
def heightOneBulkCarrierScale {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  (Q'.ofNat (b - j) * Q'.ofNat (c - l)) *
    (Q'.ofNat i * Q'.ofNat (i - q.r + 3) *
      Q'.ofNat (i - q.r + 2))

/-- The reduced exchange carrier over the final residual base. -/
theorem reduced_height_one_exchange_base_at_bulk_residual {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (i j l : Nat) (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r)
    (hrn : q.r + 2 ≤ q.intermediate) :
    reducedHeightOneExchangeBase q i j l ≈
      heightOneBulkResidualBase q i j l * heightOneBulkExchangeScale q := by
  let P := tvPhase (l - 2)
  let K := Q'.ofNat (tvFact (q.p - 1))
  let M := tvFallQ (b - 1 - j) (l - 3)
  let N := tvFallQ (c - 1 - l) (j - 3)
  let B := Q'.ofNat (b - q.p + 1)
  let C := Q'.ofNat (c - q.p + 1)
  let I := tvFallQ (i - 1) (q.r - 4)
  let F := tvFallQ (q.intermediate - 2) (q.r - 3)
  let G := Q'.ofNat (q.intermediate - q.r + 1)
  have hm0 := tvFallQ_trailing_shift (b - 1 - j) (l - 3) (by omega)
  have hm : M * B ≈ tvFallQ (b - 1 - j) (l - 2) := by
    simpa only [M, B,
      show b - 1 - j - (l - 3) = b - q.p + 1 by omega,
      show l - 3 + 1 = l - 2 by omega] using hm0
  have hn0 := tvFallQ_trailing_shift (c - 1 - l) (j - 3) (by omega)
  have hn : N * C ≈ tvFallQ (c - 1 - l) (j - 2) := by
    simpa only [N, C,
      show c - 1 - l - (j - 3) = c - q.p + 1 by omega,
      show j - 3 + 1 = j - 2 by omega] using hn0
  have hf0 := tvFallQ_trailing_shift
    (q.intermediate - 2) (q.r - 3) (by omega)
  have hf : F * G ≈ tvFallQ (q.intermediate - 2) (q.r - 2) := by
    simpa only [F, G,
      show q.intermediate - 2 - (q.r - 3) =
        q.intermediate - q.r + 1 by omega,
      show q.r - 3 + 1 = q.r - 2 by omega] using hf0
  have hinner :
      P * K * tvFallQ (b - 1 - j) (l - 2) *
          tvFallQ (c - 1 - l) (j - 2) ≈
        P * K * (M * B) * (N * C) :=
    mul_eqv_congr
      (Q'.mul_eqv_congr_left (P * K) _ _ (Q'.eqv_symm hm))
      (Q'.eqv_symm hn)
  have houter :
      I * tvFallQ (q.intermediate - 2) (q.r - 2) ≈
        I * (F * G) :=
    Q'.mul_eqv_congr_left I _ _ (Q'.eqv_symm hf)
  unfold reducedHeightOneExchangeBase reducedHeightOneInnerBase
    reducedHeightOneOuterExchangeBase heightTwoCommonFactor
  refine Q'.eqv_trans _
    ((P * K * (M * B) * (N * C)) * (I * (F * G))) _ ?_ ?_
  · exact mul_eqv_congr hinner houter
  · unfold heightOneBulkResidualBase heightOneBulkInnerBase
      heightOneBulkOuterBase heightOneBulkExchangeScale
    simp only [P, K, M, N, B, C, I, F, G]
    ring_qeqv

/-- The adjacent three-carrier base over the final residual base. -/
theorem height_one_carrier_base_at_bulk_residual {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (i j l : Nat) (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i) :
    heightOneCarrierBase q i j l ≈
      heightOneBulkResidualBase q i j l *
        heightOneBulkCarrierScale q i j l := by
  let P := tvPhase (l - 2)
  let K := Q'.ofNat (tvFact (q.p - 1))
  let M := tvFallQ (b - 1 - j) (l - 3)
  let N := tvFallQ (c - 1 - l) (j - 3)
  let B := Q'.ofNat (b - j)
  let C := Q'.ofNat (c - l)
  let I := tvFallQ (i - 1) (q.r - 4)
  let A := Q'.ofNat (i - q.r + 3)
  let A' := Q'.ofNat (i - q.r + 2)
  let J := Q'.ofNat i
  let F := tvFallQ (q.intermediate - 2) (q.r - 3)
  have hm0 := tvFallQ_leading_shift (b - j) (l - 3)
  have hm : B * M ≈ tvFallQ (b - j) (l - 2) := by
    simpa only [B, M, show b - j - 1 = b - 1 - j by omega,
      show l - 3 + 1 = l - 2 by omega] using hm0
  have hn0 := tvFallQ_leading_shift (c - l) (j - 3)
  have hn : C * N ≈ tvFallQ (c - l) (j - 2) := by
    simpa only [C, N, show c - l - 1 = c - 1 - l by omega,
      show j - 3 + 1 = j - 2 by omega] using hn0
  have hi1 := tvFallQ_trailing_shift (i - 1) (q.r - 4) (by omega)
  have hi1' : I * A ≈ tvFallQ (i - 1) (q.r - 3) := by
    simpa only [I, A, show i - 1 - (q.r - 4) = i - q.r + 3 by omega,
      show q.r - 4 + 1 = q.r - 3 by omega] using hi1
  have hi2 := tvFallQ_trailing_shift (i - 1) (q.r - 3) (by omega)
  have hi2' : tvFallQ (i - 1) (q.r - 3) * A' ≈
      tvFallQ (i - 1) (q.r - 2) := by
    simpa only [A', show i - 1 - (q.r - 3) = i - q.r + 2 by omega,
      show q.r - 3 + 1 = q.r - 2 by omega] using hi2
  have hit : (I * A) * A' ≈ tvFallQ (i - 1) (q.r - 2) :=
    Q'.eqv_trans _ (tvFallQ (i - 1) (q.r - 3) * A') _
      (Q'.mul_eqv_congr_right _ _ A' hi1') hi2'
  have hil := tvFallQ_leading_shift i (q.r - 2)
  have hil' : J * tvFallQ (i - 1) (q.r - 2) ≈
      tvFallQ i (q.r - 1) := by
    simpa only [J, show i - 1 = i - 1 by rfl,
      show q.r - 2 + 1 = q.r - 1 by omega] using hil
  have hi : J * ((I * A) * A') ≈ tvFallQ i (q.r - 1) :=
    Q'.eqv_trans _ (J * tvFallQ (i - 1) (q.r - 2)) _
      (Q'.mul_eqv_congr_left J _ _ hit) hil'
  have hinner :
      P * K * tvFallQ (b - j) (l - 2) * tvFallQ (c - l) (j - 2) ≈
        P * K * (B * M) * (C * N) :=
    mul_eqv_congr
      (Q'.mul_eqv_congr_left (P * K) _ _ (Q'.eqv_symm hm))
      (Q'.eqv_symm hn)
  have houter :
      tvFallQ i (q.r - 1) * F ≈ (J * ((I * A) * A')) * F :=
    Q'.mul_eqv_congr_right _ _ F (Q'.eqv_symm hi)
  unfold heightOneCarrierBase heightOneCarrierInnerBase
    heightOneCarrierOuterBase heightTwoCommonFactor
  refine Q'.eqv_trans _
    ((P * K * (B * M) * (C * N)) * ((J * ((I * A) * A')) * F)) _ ?_ ?_
  · exact mul_eqv_congr hinner houter
  · unfold heightOneBulkResidualBase heightOneBulkInnerBase
      heightOneBulkOuterBase heightOneBulkCarrierScale
    simp only [P, K, M, N, B, C, I, A, A', J, F]
    ring_qeqv

/-- Complete scalar residual after both sides use the final common base. -/
def heightOneBulkResidualScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  heightOneBulkExchangeScale q * reducedHeightOneExchangeScalar q i j l +
    -(heightOneBulkCarrierScale q i j l *
      heightOneCarrierSideScalar q i j l)

/-- **Exact strict-bulk residual factorization.**  No cancellation is assumed:
the full correction defect is exactly the common carrier times the displayed
finite scalar polynomial. -/
theorem height_one_full_correction_exact_residual {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) (hnext : qp.p = q.p + 1)
    (i j l : Nat) (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hrn : q.r + 2 ≤ q.intermediate) :
    omegaExchangeCorrection a b c
          (fun u v w => rightShellFactorialCoefficient
            (reducePositiveInnerRightChannel q hp) u v w) i j l +
        -((omegaCorrectionLowerCoefficient a b c d q.p *
              rightShellFactorialCoefficient qm i j l +
            omegaCorrectionDiagonalCoefficient a b c d q.p *
              rightShellFactorialCoefficient q i j l) +
          omegaCorrectionUpperCoefficient a b c d q.p *
            rightShellFactorialCoefficient qp i j l) ≈
      heightOneBulkResidualBase q i j l *
        heightOneBulkResidualScalar q i j l := by
  let EB := reducedHeightOneExchangeBase q i j l
  let ES := heightOneBulkExchangeScale q
  let X := reducedHeightOneExchangeScalar q i j l
  let CB := heightOneCarrierBase q i j l
  let CS := heightOneBulkCarrierScale q i j l
  let Y := heightOneCarrierSideScalar q i j l
  let G := heightOneBulkResidualBase q i j l
  have hx := reduced_height_one_exchange_full_polynomial
    q hp i j l (by omega) (by omega) hheight hpb hpc hr hri hrn
  have hy := height_one_carrier_side_full_polynomial
    qm q qp hp hprev hnext i j l (by omega) (by omega) hheight
      (by omega) (by omega) (by omega) hri (by omega)
  have heb := reduced_height_one_exchange_base_at_bulk_residual
    q i j l hj hl hheight hpb hpc hr hrn
  have hcb := height_one_carrier_base_at_bulk_residual
    q i j l hj hl hheight hpb hpc hr hri
  refine Q'.eqv_trans _ ((EB * X) + -(CB * Y)) _
    (Q'.add_eqv_congr' hx (Q'.neg_eqv_congr _ _ hy)) ?_
  refine Q'.eqv_trans _ (((G * ES) * X) + -((G * CS) * Y)) _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ X heb)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ Y hcb))) ?_
  unfold heightOneBulkResidualScalar
  simp only [ES, X, CS, Y, G]
  ring_qeqv

end YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial.reduced_height_one_exchange_base_at_bulk_residual
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial.height_one_carrier_base_at_bulk_residual
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial.height_one_full_correction_exact_residual
