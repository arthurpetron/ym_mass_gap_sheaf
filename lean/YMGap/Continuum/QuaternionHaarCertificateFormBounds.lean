/-
# From supported-square Haar bounds to certified polynomial bounds

The certificate constructors are the only induction cases. In particular,
transport uses equality under every insertion, so the represented polynomial
itself need not have a support witness.
-/

import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.QuaternionHaarSquareCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer

local infix:50 " ≈ " => Q'.eqv

private theorem add_mono {a b c d : Q'} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c hab)
    (Q'.add_le_add_left b c d hcd)

private theorem scalar_swap (a c x : Q') : a * (c * x) ≈ c * (a * x) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a c x))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a c))
      (Q'.mul_assoc_eqv c a x))

private theorem weighted_add (blocks : Nat) (p q d : RatPoly) :
    quaternionHaar blocks (polyMul (polyAdd p q) d) ≈
      quaternionHaar blocks (polyMul p d) +
        quaternionHaar blocks (polyMul q d) := by
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

private theorem weighted_smul (blocks : Nat) (c : Q') (p d : RatPoly) :
    quaternionHaar blocks (polyMul (polySmul c p) d) ≈
      c * quaternionHaar blocks (polyMul p d) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p d))
    (quaternionHaar_polySmul blocks c (polyMul p d))

namespace Certificate

/-- A two-sided bound checked on every supported square extends to every
constructively certified polynomial, without support on the represented
polynomial or on the insertion `d`. -/
theorem form_interval {blocks : Nat} (d : RatPoly) (L U : Q')
    (hSquare : ∀ (r : RatPoly), SupportedQuaternionBlocks blocks r →
      L * quaternionHaar blocks (polyMul r r) ≤
        quaternionHaar blocks (polyMul (polyMul r r) d) ∧
      quaternionHaar blocks (polyMul (polyMul r r) d) ≤
        U * quaternionHaar blocks (polyMul r r)) :
    {p : RatPoly} → (P : Certificate blocks p) →
      L * quaternionHaar blocks p ≤
          quaternionHaar blocks (polyMul p d) ∧
      quaternionHaar blocks (polyMul p d) ≤
          U * quaternionHaar blocks p := by
  intro p P
  induction P with
  | square r hr => exact hSquare r hr
  | @add p q P Q ihP ihQ =>
      have hplain := quaternionHaar_append blocks p q
      have hweighted := weighted_add blocks p q d
      have hL : L * quaternionHaar blocks (polyAdd p q) ≈
          L * quaternionHaar blocks p + L * quaternionHaar blocks q :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hplain)
          (Q'.mul_add_eqv L _ _)
      have hU : U * quaternionHaar blocks (polyAdd p q) ≈
          U * quaternionHaar blocks p + U * quaternionHaar blocks q :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hplain)
          (Q'.mul_add_eqv U _ _)
      constructor
      · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
          (Q'.le_trans' _ _ _ (add_mono ihP.1 ihQ.1)
            (Q'.ge_of_eqv hweighted))
      · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hweighted)
          (Q'.le_trans' _ _ _ (add_mono ihP.2 ihQ.2)
            (Q'.ge_of_eqv hU))
  | @smul c hc p P ih =>
      have hplain := quaternionHaar_polySmul blocks c p
      have hweighted := weighted_smul blocks c p d
      have hL : L * quaternionHaar blocks (polySmul c p) ≈
          c * (L * quaternionHaar blocks p) :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hplain)
          (scalar_swap L c _)
      have hU : U * quaternionHaar blocks (polySmul c p) ≈
          c * (U * quaternionHaar blocks p) :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hplain)
          (scalar_swap U c _)
      constructor
      · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_left _ _ c ih.1 hc)
            (Q'.ge_of_eqv hweighted))
      · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hweighted)
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_left _ _ c ih.2 hc)
            (Q'.ge_of_eqv hU))
  | @transport p q h Q ih =>
      have hplain : quaternionHaar blocks p ≈ quaternionHaar blocks q :=
        haar_of_carrier h
      have hweighted : quaternionHaar blocks (polyMul p d) ≈
          quaternionHaar blocks (polyMul q d) :=
        haar_of_carrier (HaarCarrierEqv.mul_right d h)
      constructor
      · exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hplain))
          (Q'.le_trans' _ _ _ ih.1 (Q'.ge_of_eqv hweighted))
      · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hweighted)
          (Q'.le_trans' _ _ _ ih.2
            (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ hplain)))

end Certificate

end YMGap.Continuum.QuaternionHaarSquareCertificate

#print axioms YMGap.Continuum.QuaternionHaarSquareCertificate.Certificate.form_interval
