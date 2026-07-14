/-
# All-order endpoint Casimir coefficient and transpose fence

The first-label Hahn contiguous identity closes the reduced carrier in the
endpoint Casimir factorization.  Consequently the raw order-zero right-channel
functional has neighbor numerator

`q * (a+b+c-q+1) * (a-q+1)`

over the common degree `b+c`.  This is the transpose coefficient of the dual
section Jacobi matrix.  Exact fundamental and mixed-label fences make the
normalization mismatch impossible to erase silently.
-/

import YMGap.Continuum.SU2HahnFirstLabelContiguous

namespace YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder

open YMGap.Constructive
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2HahnFirstLabelContiguous
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahEndpointCasimirAction
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- The residual endpoint carrier is exactly the outer row of the neighboring
inner-order-one channel, with scalar `a-q+1`. -/
theorem endpointReducedCarrier_eq_neighbor
    (a b c q i j l : Nat)
    (hq0 : 0 < q) (hqa : q ≤ a) (hqf : q ≤ b + c - 1)
    (hi : i ≤ a) (ht0 : 0 < j + l) (htf : j + l < b + c) :
    endpointReducedCarrier a b c q i j l ≈
      Q'.ofNat (a - q + 1) *
        transvectFactorialCoeff a (b + c - 2) (q - 1) i (j + l - 1) := by
  have h := hahn_first_label_contiguous (q - 1) a (b + c - 2)
    i (j + l - 1) (by omega) (by omega) hi (by omega)
  simpa only [endpointReducedCarrier,
    show (b + c - 2) + 1 = b + c - 1 by omega,
    show j + l - 1 + 1 = j + l by omega,
    show a - (q - 1) = a - q + 1 by omega] using h

private theorem neighbor_regroup (A H1 N : Q') :
    H1 * (A * N) ≈ A * (H1 * N) := by
  refine Q'.eqv_trans _ ((H1 * A) * N) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv H1 A N)) ?_
  refine Q'.eqv_trans _ ((A * H1) * N) _
    (Q'.mul_eqv_congr_right _ _ N (Q'.mul_comm_eqv H1 A)) ?_
  exact Q'.mul_assoc_eqv A H1 N

/-- **All-order raw endpoint action.**  This is the completed neighboring
coefficient on every strict physical source coordinate.  It is deliberately
written without division so that all constants remain exact naturals in the
constructive substrate. -/
theorem endpoint_pairExchange_all_order
    (a b c q i j l : Nat)
    (hq0 : 0 < q) (hqa : q ≤ a) (hqf : q ≤ b + c - 1)
    (hi0 : 0 < i) (hia : i < a)
    (hj0 : 0 < j) (hjb : j < b) (hl : l ≤ c) :
    Q'.ofNat (b + c) *
        pairExchange a b
          (fun x y => endpointZeroCarrier a b c q x y l) i j ≈
      Q'.ofNat (q * (a + (b + c) - q + 1)) *
        (Q'.ofNat (a - q + 1) * endpointOneCarrier a b c q i j l +
          -(Q'.ofNat b * endpointZeroCarrier a b c q i j l)) := by
  have hfactor := endpoint_pairExchange_factorization
    a b c q i j l hq0 hqa (by omega) hi0 hia hj0 hjb hl
  have hred := endpointReducedCarrier_eq_neighbor
    a b c q i j l hq0 hqa hqf (by omega) (by omega) (by omega)
  refine Q'.eqv_trans _ _ _ hfactor ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _
        (transvectFactorialCoeff b c 1 j l *
          (Q'.ofNat (a - q + 1) *
            transvectFactorialCoeff a (b + c - 2) (q - 1) i (j + l - 1))) _
        (Q'.mul_eqv_congr_left _ _ _ hred)
        (by
          simpa only [endpointOneCarrier] using neighbor_regroup
            (Q'.ofNat (a - q + 1))
            (transvectFactorialCoeff b c 1 j l)
            (transvectFactorialCoeff a (b + c - 2) (q - 1) i (j + l - 1))))
      (Q'.eqv_refl _))

/-- Raw-coordinate endpoint neighbor coefficient.  The zero-degree branch is
literal and is never used by the physical action theorem. -/
def rawEndpointForward (a b c q : Nat) : Q' :=
  if hf : 0 < b + c then
    Q'.mkPos (q * (a + (b + c) - q + 1) * (a - q + 1))
      (b + c) hf
  else 0

private def half : Q' := Q'.mkPos 1 2 (by decide)
private def threeHalves : Q' := Q'.mkPos 3 2 (by decide)
private def oneThird : Q' := Q'.mkPos 1 3 (by decide)
private def eightThirds : Q' := Q'.mkPos 8 3 (by decide)

/-- **Fundamental normalization fence.**  The raw functional coefficient is
`3/2`, whereas the dual reconstructed-section coefficient in the inverse-Schur
recurrence is `1/2`; they are provably not the same rational. -/
theorem fundamental_raw_dual_transpose_fence :
    rawEndpointForward 1 1 1 1 ≈ threeHalves ∧
    jacobiForward 1 1 1 1 0 ≈ half ∧
    ¬ (rawEndpointForward 1 1 1 1 ≈ jacobiForward 1 1 1 1 0) := by
  decide

/-- The asymmetric `(2,2,1,1)` block independently detects the same
transpose: raw `8/3` versus dual `1/3`. -/
theorem mixed221_raw_dual_transpose_fence :
    rawEndpointForward 2 2 1 2 ≈ eightThirds ∧
    jacobiForward 2 2 1 1 0 ≈ oneThird ∧
    ¬ (rawEndpointForward 2 2 1 2 ≈ jacobiForward 2 2 1 1 0) := by
  decide

end YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder

#print axioms YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder.endpointReducedCarrier_eq_neighbor
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder.endpoint_pairExchange_all_order
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder.fundamental_raw_dual_transpose_fence
#print axioms YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder.mixed221_raw_dual_transpose_fence
