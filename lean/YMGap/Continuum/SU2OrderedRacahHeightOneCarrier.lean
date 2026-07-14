/-
# The first off-lowest-shell factorial carrier

At correction height one, the reduced inner channel has total source degree
two above its lowest support.  Its defining factorial sum therefore has
three, rather than two, live summands.  This module isolates that exact new
term.  It is the first carrier identity required by any induction in
`h = (j+l)-p`.
-/

import YMGap.Continuum.SU2OrderedRacahRightJacobiOffShellFence

namespace YMGap.Continuum.SU2OrderedRacahHeightOneCarrier

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantHighestWeightRowFormula

local infix:50 " ≈ " => Q'.eqv

/-- One summand in the exact factorial transvectant row. -/
def heightFactorialSummand
    (m n k j l r : Nat) : Q' :=
  tvPhase r * tvBinomQ k r * tvFallQ j (k - r) *
    tvFallQ (m - j) r * tvFallQ l r * tvFallQ (n - l) (k - r)

private theorem finSum_eqv_two_local (f : Nat → Q') : ∀ N u v,
    u < v → v < N →
      (∀ r, r < N → r ≠ u → r ≠ v → f r ≈ 0) →
      finSum f N ≈ f u + f v
  | 0, _, _, _, hv, _ => by omega
  | N + 1, u, v, huv, hv, hzero => by
      by_cases hvtop : v = N
      · subst v
        change finSum f N + f N ≈ f u + f N
        exact Q'.add_eqv_congr_right _ _ _
          (finSum_eqv_single f N u (by omega)
            (fun r hr hru => hzero r (by omega) hru (by omega)))
      · change finSum f N + f N ≈ f u + f v
        refine Q'.eqv_trans _ ((f u + f v) + 0) _
          (Q'.add_eqv_congr'
            (finSum_eqv_two_local f N u v huv (by omega)
              (fun r hr hru hrv => hzero r (by omega) hru hrv))
            (hzero N (by omega) (by omega) (by omega))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' (f u + f v))

private theorem finSum_eqv_three_local (f : Nat → Q') : ∀ N u v w,
    u < v → v < w → w < N →
      (∀ r, r < N → r ≠ u → r ≠ v → r ≠ w → f r ≈ 0) →
      finSum f N ≈ (f u + f v) + f w
  | 0, _, _, _, _, _, hw, _ => by omega
  | N + 1, u, v, w, huv, hvw, hw, hzero => by
      by_cases hwtop : w = N
      · subst w
        change finSum f N + f N ≈ (f u + f v) + f N
        exact Q'.add_eqv_congr_right _ _ _
          (finSum_eqv_two_local f N u v huv (by omega)
            (fun r hr hru hrv => hzero r (by omega) hru hrv (by omega)))
      · change finSum f N + f N ≈ (f u + f v) + f w
        refine Q'.eqv_trans _ (((f u + f v) + f w) + 0) _
          (Q'.add_eqv_congr'
            (finSum_eqv_three_local f N u v w huv hvw (by omega)
              (fun r hr hru hrv hrw =>
                hzero r (by omega) hru hrv hrw))
            (hzero N (by omega) (by omega) (by omega) (by omega))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' ((f u + f v) + f w))

private theorem height_two_term_zero_below
    (m n k j l r : Nat) (hsum : j + l = k + 2)
    (hrl : r < l - 2) : heightFactorialSummand m n k j l r ≈ 0 := by
  have hz : tvFallQ j (k - r) ≈ 0 :=
    tvFallQ_eqv_zero_of_lt j (k - r) (by omega)
  let A := tvPhase r * tvBinomQ k r
  have h0 : A * tvFallQ j (k - r) ≈ 0 :=
    Q'.eqv_trans _ (A * 0) _
      (Q'.mul_eqv_congr_left A _ _ hz) (Q'.mul_zero_eqv A)
  have h1 : (A * tvFallQ j (k - r)) * tvFallQ (m - j) r ≈ 0 :=
    Q'.eqv_trans _ (0 * tvFallQ (m - j) r) _
      (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv _)
  have h2 :
      ((A * tvFallQ j (k - r)) * tvFallQ (m - j) r) *
          tvFallQ l r ≈ 0 :=
    Q'.eqv_trans _ (0 * tvFallQ l r) _
      (Q'.mul_eqv_congr_right _ _ _ h1) (Q'.zero_mul_eqv _)
  unfold heightFactorialSummand
  exact Q'.eqv_trans _ (0 * tvFallQ (n - l) (k - r)) _
    (Q'.mul_eqv_congr_right _ _ _ h2) (Q'.zero_mul_eqv _)

private theorem height_term_zero_above
    (m n k j l r : Nat) (hlr : l < r) :
    heightFactorialSummand m n k j l r ≈ 0 := by
  have hz : tvFallQ l r ≈ 0 := tvFallQ_eqv_zero_of_lt l r hlr
  let A := tvPhase r * tvBinomQ k r * tvFallQ j (k - r) *
    tvFallQ (m - j) r
  have h0 : A * tvFallQ l r ≈ 0 :=
    Q'.eqv_trans _ (A * 0) _
      (Q'.mul_eqv_congr_left A _ _ hz) (Q'.mul_zero_eqv A)
  unfold heightFactorialSummand
  exact Q'.eqv_trans _ (0 * tvFallQ (n - l) (k - r)) _
    (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv _)

/-- **Exact first height-step carrier.**  Two shells above lowest support,
the factorial transvectant row consists precisely of the consecutive
summands `l-2`, `l-1`, and `l`.  The first term is the genuinely new bulk
term absent from the already-closed lowest-shell proof. -/
theorem transvectFactorialCoeff_two_above_lowest_three_term
    (m n k j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hsum : j + l = k + 2) :
    transvectFactorialCoeff m n k j l ≈
      (heightFactorialSummand m n k j l (l - 2) +
        heightFactorialSummand m n k j l (l - 1)) +
        heightFactorialSummand m n k j l l := by
  unfold transvectFactorialCoeff
  apply finSum_eqv_three_local _ (k + 1) (l - 2) (l - 1) l
    (by omega) (by omega) (by omega)
  intro r hr hru hrv hrw
  by_cases hbelow : r < l - 2
  · exact height_two_term_zero_below m n k j l r hsum hbelow
  · exact height_term_zero_above m n k j l r (by omega)

/-- Specialization to correction height one.  Peeling an order-`p` channel
leaves order `p-1`, while `j+l=p+1`; hence the reduced inner carrier is
exactly two above its own lowest support and the new `l-2` term is live. -/
theorem reduced_inner_height_one_three_term
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1) :
    transvectFactorialCoeff (b - 1) (c - 1) (q.p - 1) j l ≈
      (heightFactorialSummand (b - 1) (c - 1) (q.p - 1) j l (l - 2) +
        heightFactorialSummand (b - 1) (c - 1) (q.p - 1) j l (l - 1)) +
        heightFactorialSummand (b - 1) (c - 1) (q.p - 1) j l l := by
  apply transvectFactorialCoeff_two_above_lowest_three_term
    (b - 1) (c - 1) (q.p - 1) j l hj hl
  omega

/-- The new lowest summand is not a formal zero: already at
`(m,n,k,j,l)=(4,4,2,2,2)` it is exactly four.  Therefore the height-zero
two-term cancellation cannot be reused at height one without an additional
bulk identity. -/
theorem height_one_new_summand_is_genuinely_nonzero :
    heightFactorialSummand 4 4 2 2 2 0 ≈ Q'.ofNat 4 ∧
    ¬ (heightFactorialSummand 4 4 2 2 2 0 ≈ 0) := by
  unfold heightFactorialSummand
  decide

end YMGap.Continuum.SU2OrderedRacahHeightOneCarrier

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrier.transvectFactorialCoeff_two_above_lowest_three_term
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrier.reduced_inner_height_one_three_term
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneCarrier.height_one_new_summand_is_genuinely_nonzero
