/-
# Normalized strict-bulk height-one cancellation

The integral residual certificate is transported back through both positive
scales.  This closes the normalized bulk residual and then the on-shell
factorial and raw three-carrier correction identities.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualCancellation

namespace YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneScaledResidualPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualTransport
open YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualCancellation

local infix:50 " ≈ " => Q'.eqv

private theorem ofNat_pos_of_pos (n : Nat) (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

private theorem heightOneJacobiScale_pos {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hn : 0 < q.intermediate) :
    (0 : Q') < heightOneJacobiScale q := by
  unfold heightOneJacobiScale
  exact Q'.mul_pos
    (Q'.mul_pos (ofNat_pos_of_pos 8 (by omega))
      (ofNat_pos_of_pos q.intermediate hn))
    (Q'.mul_pos
      (ofNat_pos_of_pos (q.intermediate + 2) (by omega))
      (ofNat_pos_of_pos (q.intermediate + 1) (by omega)))

private theorem eqv_of_add_neg_eqv_zero (L R : Q')
    (h : L + -R ≈ 0) : L ≈ R := by
  have hR : (L + -R) + R ≈ 0 + R :=
    Q'.add_eqv_congr_right (L + -R) 0 R h
  have hleft : (L + -R) + R ≈ L := by
    refine Q'.eqv_trans _ (L + (-R + R)) _
      (Q'.add_assoc_eqv L (-R) R) ?_
    refine Q'.eqv_trans _ (L + 0) _
      (Q'.add_eqv_congr_left L (-R + R) 0
        (Q'.neg_add_self_eqv R)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' L)
  have hright : 0 + R ≈ R :=
    Q'.eqv_of_eq (Q'.zero_add' R)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hR hright)

/-- The integral certificate cancels the remaining factor two and hence the
pure scaled residual itself. -/
theorem height_one_scaled_residual_zero {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat)
    (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hia : i + 1 ≤ a)
    (hrn : q.r + 2 ≤ q.intermediate) :
    heightOneScaledResidualPolynomial q i j l ≈ 0 := by
  have htransport := height_one_scaled_residual_integral
    q i j l (by omega) (by omega) (by omega)
  have hintegral := height_one_integral_residual_zero
    q i j l hj hl hheight hpb hpc hr hri hia hrn
  have htwo : Q'.ofNat 2 * heightOneScaledResidualPolynomial q i j l ≈ 0 :=
    Q'.eqv_trans _ _ _ htransport hintegral
  exact Q'.mul_eqv_zero_of_pos
    (ofNat_pos_of_pos 2 (by omega)) htwo

/-- The normalized strict-bulk residual scalar vanishes after constructively
cancelling the positive Jacobi scale. -/
theorem height_one_bulk_residual_scalar_zero {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (i j l : Nat) (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hia : i + 1 ≤ a)
    (hrn : q.r + 2 ≤ q.intermediate) :
    heightOneBulkResidualScalar q i j l ≈ 0 := by
  have hpolynomial := height_one_scaled_residual_zero
    q i j l hj hl hheight hpb hpc hr hri hia hrn
  have hscaled := height_one_residual_scaled_to_polynomial
    qm q qp hp hprev hnext i j l (by omega)
  have hzero :
      heightOneJacobiScale q * heightOneBulkResidualScalar q i j l ≈ 0 :=
    Q'.eqv_trans _ _ _ hscaled hpolynomial
  exact Q'.mul_eqv_zero_of_pos
    (heightOneJacobiScale_pos q (by omega)) hzero

/-- The complete strict-bulk correction defect is zero. -/
theorem height_one_bulk_correction_defect_zero {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (i j l : Nat) (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hia : i + 1 ≤ a)
    (hrn : q.r + 2 ≤ q.intermediate) :
    omegaExchangeCorrection a b c
          (fun u v w => rightShellFactorialCoefficient
            (reducePositiveInnerRightChannel q hp) u v w) i j l +
        -((omegaCorrectionLowerCoefficient a b c d q.p *
              rightShellFactorialCoefficient qm i j l +
            omegaCorrectionDiagonalCoefficient a b c d q.p *
              rightShellFactorialCoefficient q i j l) +
          omegaCorrectionUpperCoefficient a b c d q.p *
            rightShellFactorialCoefficient qp i j l) ≈ 0 := by
  have hfactor := height_one_full_correction_exact_residual
    qm q qp hp hprev hnext i j l hj hl hheight hpb hpc hr hri hrn
  have hresidual := height_one_bulk_residual_scalar_zero
    qm q qp hp hprev hnext i j l hj hl hheight hpb hpc hr hri hia hrn
  refine Q'.eqv_trans _
    (heightOneBulkResidualBase q i j l *
      heightOneBulkResidualScalar q i j l) _ hfactor ?_
  refine Q'.eqv_trans _ (heightOneBulkResidualBase q i j l * 0) _
    (Q'.mul_eqv_congr_left _ _ _ hresidual) ?_
  exact Q'.mul_zero_eqv _

/-- The exact on-shell Hahn correction identity on the strict height-one
bulk. -/
theorem omegaCorrectionShellAt_height_one_strict_bulk
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (i j l : Nat) (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hia : i + 1 ≤ a)
    (hrn : q.r + 2 ≤ q.intermediate) :
    OmegaCorrectionShellAt qm q qp hp i j l := by
  unfold OmegaCorrectionShellAt
  apply eqv_of_add_neg_eqv_zero
  exact height_one_bulk_correction_defect_zero
    qm q qp hp hprev hnext i j l hj hl hheight hpb hpc hr hri hia hrn

/-- The normalized factorial correction on the common output shell. -/
theorem omegaCorrectionFactorialAt_height_one_strict_bulk_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (i j l s : Nat) (hshell : s + q.r + q.p = i + j + l)
    (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hia : i + 1 ≤ a)
    (hrn : q.r + 2 ≤ q.intermediate) :
    OmegaCorrectionFactorialAt qm q qp hp i j l s := by
  apply (omegaCorrectionFactorialAt_on_shell_iff_shell
    qm q qp hp hprev hnext i j l s (by omega) (by omega) (by omega)
      hshell).2
  exact omegaCorrectionShellAt_height_one_strict_bulk
    qm q qp hp hprev hnext i j l hj hl hheight hpb hpc hr hri hia hrn

/-- The raw ordered-Racah three-carrier correction on the strict height-one
bulk and common output shell. -/
theorem omegaCorrectionThreeCarrierAt_height_one_strict_bulk_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (i j l s : Nat) (hshell : s + q.r + q.p = i + j + l)
    (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hia : i + 1 ≤ a)
    (hrn : q.r + 2 ≤ q.intermediate) :
    OmegaCorrectionThreeCarrierAt qm q qp i j l s :=
  (omegaCorrectionThreeCarrierAt_iff_factorial
    qm q qp hp i j l s).2
    (omegaCorrectionFactorialAt_height_one_strict_bulk_on_shell
      qm q qp hp hprev hnext i j l s hshell hj hl hheight hpb hpc
        hr hri hia hrn)

end YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation.height_one_scaled_residual_zero
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation.height_one_bulk_residual_scalar_zero
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation.height_one_bulk_correction_defect_zero
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation.omegaCorrectionShellAt_height_one_strict_bulk
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation.omegaCorrectionFactorialAt_height_one_strict_bulk_on_shell
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation.omegaCorrectionThreeCarrierAt_height_one_strict_bulk_on_shell
