/-
# All-label actual right-channel endpoint Gram transpose

The closed factorial endpoint identity becomes a statement about the concrete
right-channel Hilbert--Schmidt weights once the exact nested Gram
factorization and the analytic/closed binary Gram identification are
substituted.  The intermediate-dimension factors cancel constructively,
leaving precisely the Gram transpose which sends the derived raw endpoint
coefficient to the Jacobi forward coefficient.
-/

import YMGap.Continuum.SU2ClosedBinaryGramIdentification
import YMGap.Continuum.SU2OrderedRacahEndpointClosedGramRatio
import YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection

namespace YMGap.Continuum.SU2OrderedRacahEndpointActualGramTranspose

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantNormalizedRows
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2OrderedRightNestedGramFactorization
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder
open YMGap.Continuum.SU2OrderedRacahEndpointGramTranspose
open YMGap.Continuum.SU2OrderedRacahEndpointClosedGramRatio
open YMGap.Continuum.SU2OrderedRacahEndpointReconstructedSection
open YMGap.Continuum.SU2ClosedBinaryGramIdentification
open YMGap.Continuum.SU2SignedRacahSquareNormalization

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem endpoint_left_reassoc (A B W J : Q') :
    (B * A) * (W * J) ≈ B * ((A * W) * J) := by
  refine Q'.eqv_trans _ (B * (A * (W * J))) _ ?_ ?_
  · refine Q'.eqv_trans _ ((B * A) * (W * J)) _ (Q'.eqv_refl _) ?_
    exact Q'.mul_assoc_eqv B A (W * J)
  · exact Q'.mul_eqv_congr_left B _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv A W J))

private theorem endpoint_right_reassoc (A B W R : Q') :
    A * ((B * W) * R) ≈ (B * A) * (W * R) := by
  refine Q'.eqv_trans _ (A * (B * (W * R))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left A _ _ (Q'.mul_assoc_eqv B W R)
  refine Q'.eqv_trans _ ((A * B) * (W * R)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv A B (W * R))) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv A B)

private theorem ofNat_pos_of_pos (N : Nat) (hN : 0 < N) :
    (0 : Q') < Q'.ofNat N := by
  cases N with
  | zero => omega
  | succ N => exact Q'.ofNat_succ_pos N

/-! ## Binary products for the two concrete endpoint channels -/

private theorem endpoint_zero_binary_product_closed
    (a b c q : Nat) (hqa : q ≤ a) (hqf : q ≤ b + c) :
    binaryTransvectantGram b c 0 *
        binaryTransvectantGram a (b + c) q ≈
      closedBinaryGram b c (b + c) *
        closedBinaryGram a (b + c) (endpointFinalLabel a b c q) := by
  apply mul_eqv_congr
  · simpa using binaryTransvectantGram_eq_closedBinaryGram b c 0
      (by omega) (by omega)
  · simpa only [endpointFinalLabel] using
      binaryTransvectantGram_eq_closedBinaryGram a (b + c) q hqa hqf

private theorem endpoint_one_binary_product_closed
    (a b c q : Nat)
    (hb : 0 < b) (hc : 0 < c) (hq0 : 0 < q)
    (hqa : q ≤ a) (hqf : q ≤ b + c - 1) :
    binaryTransvectantGram b c 1 *
        binaryTransvectantGram a (b + c - 2) (q - 1) ≈
      closedBinaryGram b c (b + c - 2) *
        closedBinaryGram a (b + c - 2)
          (endpointFinalLabel a b c q) := by
  apply mul_eqv_congr
  · simpa only [show b + c - 2 * 1 = b + c - 2 by omega] using
      binaryTransvectantGram_eq_closedBinaryGram b c 1
        (by omega) (by omega)
  · have hrA : q - 1 ≤ a := by omega
    have hrF : q - 1 ≤ b + c - 2 := by omega
    simpa only [endpointFinalLabel,
      show a + (b + c - 2) - 2 * (q - 1) =
        a + (b + c) - 2 * q by omega] using
      binaryTransvectantGram_eq_closedBinaryGram
        a (b + c - 2) (q - 1) hrA hrF

/-! ## Concrete endpoint detailed balance -/

/-- **All-label actual endpoint Gram transpose.**  The two weights are the
literal finite coefficient-box `triRightChannelWeight`s.  No closed Gram,
abstract weight, or measured normalization remains in the statement. -/
theorem endpoint_actual_right_channel_gram_ratio
    (a b c q : Nat)
    (hb : 0 < b) (hc : 0 < c) (hq0 : 0 < q)
    (hqa : q ≤ a) (hqf : q ≤ b + c - 1) :
    triRightChannelWeight a b c (endpointFinalLabel a b c q) (b + c) *
        jacobiForward a b c (endpointFinalLabel a b c q) 0 ≈
      triRightChannelWeight a b c (endpointFinalLabel a b c q)
          (b + c - 2) * rawEndpointForward a b c q := by
  let d := endpointFinalLabel a b c q
  let W0 := triRightChannelWeight a b c d (b + c)
  let W1 := triRightChannelWeight a b c d (b + c - 2)
  let J := jacobiForward a b c d 0
  let R := rawEndpointForward a b c q
  let A := Q'.ofNat (b + c + 1)
  let B := Q'.ofNat (b + c - 1)
  let G0 := closedBinaryGram b c (b + c) * closedBinaryGram a (b + c) d
  let G1 := closedBinaryGram b c (b + c - 2) *
    closedBinaryGram a (b + c - 2) d
  have hn0 := triRightChannelWeight_nested_binary_gram
    (endpointRightZero a b c q hqa (by omega))
  have hn1 := triRightChannelWeight_nested_binary_gram
    (endpointRightOne a b c q hb hc hq0 hqa hqf)
  have hc0 := endpoint_zero_binary_product_closed a b c q hqa (by omega)
  have hc1 := endpoint_one_binary_product_closed a b c q hb hc hq0 hqa hqf
  have h0 : A * W0 ≈ G0 := by
    refine Q'.eqv_trans _ _ _ ?_ hc0
    simpa only [A, W0, d, FixedRightCGChannel.intermediate,
      FixedRightCGChannel.p, FixedRightCGChannel.r] using hn0
  have h1 : B * W1 ≈ G1 := by
    refine Q'.eqv_trans _ _ _ ?_ hc1
    simpa only [A, B, W1, d, endpointRightOne,
      FixedRightCGChannel.intermediate,
      FixedRightCGChannel.p, FixedRightCGChannel.r,
      show b + c - 2 + 1 = b + c - 1 by omega] using hn1
  have hclosed : B * (G0 * J) ≈ A * (G1 * R) := by
    simpa only [A, B, G0, G1, J, R, d] using
      endpoint_closed_binary_gram_ratio a b c q hb hc hq0 hqa hqf
  have hscaled : (B * A) * (W0 * J) ≈ (B * A) * (W1 * R) := by
    refine Q'.eqv_trans _ (B * ((A * W0) * J)) _
      (endpoint_left_reassoc A B W0 J) ?_
    refine Q'.eqv_trans _ (B * (G0 * J)) _
      (Q'.mul_eqv_congr_left B _ _
        (Q'.mul_eqv_congr_right _ _ J h0)) ?_
    refine Q'.eqv_trans _ (A * (G1 * R)) _ hclosed ?_
    refine Q'.eqv_trans _ (A * ((B * W1) * R)) _
      (Q'.mul_eqv_congr_left A _ _
        (Q'.mul_eqv_congr_right _ _ R (Q'.eqv_symm h1))) ?_
    exact endpoint_right_reassoc A B W1 R
  have hA : (0 : Q') < A :=
    ofNat_pos_of_pos _ (by omega)
  have hB : (0 : Q') < B :=
    ofNat_pos_of_pos _ (by omega)
  have hBA : (0 : Q') < B * A := Q'.mul_pos hB hA
  exact Q'.mul_left_cancel_of_pos hBA hscaled

/-- The same identity packaged in the denominator-free interface consumed by
section coefficient uniqueness. -/
theorem endpoint_actual_section_forward_gram_transpose
    (a b c q : Nat)
    (hb : 0 < b) (hc : 0 < c) (hq0 : 0 < q)
    (hqa : q ≤ a) (hqf : q ≤ b + c - 1) :
    SectionForwardGramTranspose
      (triRightChannelWeight a b c (endpointFinalLabel a b c q) (b + c))
      (triRightChannelWeight a b c (endpointFinalLabel a b c q) (b + c - 2))
      (rawEndpointForward a b c q)
      (jacobiForward a b c (endpointFinalLabel a b c q) 0) := by
  exact endpoint_actual_right_channel_gram_ratio a b c q hb hc hq0 hqa hqf

end YMGap.Continuum.SU2OrderedRacahEndpointActualGramTranspose

#print axioms YMGap.Continuum.SU2OrderedRacahEndpointActualGramTranspose.endpoint_actual_right_channel_gram_ratio
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointActualGramTranspose.endpoint_actual_section_forward_gram_transpose
