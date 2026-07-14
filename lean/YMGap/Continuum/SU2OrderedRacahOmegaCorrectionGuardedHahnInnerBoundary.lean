/-
# Inner-label boundary for the guarded Hahn correction

The strict first-bulk proof cancels the product `(b-p)(c-p)`.  At either
inner endpoint this multiplier is exactly zero, so that proof mechanism loses
all information.  These checked fences isolate the required replacement: a
direct saturated-label Hahn identity, not cancellation of the bulk formula.
-/

import YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary

namespace YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnInnerBoundary

open YMGap.Constructive
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantHighestWeightRowFormula
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn

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

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

private theorem tvFallQ_pred_endpoint (n : Nat) (hn : 0 < n) :
    tvFallQ n (n - 1) ≈
      Q'.ofNat n * tvFallQ (n - 1) (n - 1) := by
  have ht := tvFallQ_trailing_shift n (n - 1) (by omega)
  have ht' : tvFallQ n (n - 1) * Q'.ofNat 1 ≈ tvFallQ n n := by
    simpa only [show n - (n - 1) = 1 by omega,
      show n - 1 + 1 = n by omega] using ht
  have hlead := tvFallQ_leading_shift n (n - 1)
  refine Q'.eqv_trans _ (tvFallQ n (n - 1) * Q'.ofNat 1) _ ?_ ?_
  · refine Q'.eqv_trans _ (tvFallQ n (n - 1) * 1) _
      (Q'.eqv_symm (Q'.mul_one_eqv _)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (by decide)
  · exact Q'.eqv_trans _ _ _ ht' (Q'.eqv_symm (by
      simpa only [show n - 1 + 1 = n by omega] using hlead))

private theorem one_above_lowest_first_term_closed
    (m n k j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = k + 1) (hkn : k + 1 ≤ n) :
    tvPhase (l - 1) * tvBinomQ k (l - 1) *
        tvFallQ j (k - (l - 1)) * tvFallQ (m - j) (l - 1) *
        tvFallQ l (l - 1) * tvFallQ (n - l) (k - (l - 1)) ≈
      (tvPhase (l - 1) * Q'.ofNat (tvFact k) *
          tvFallQ (m - j) (l - 1) * tvFallQ (n - l) (j - 1)) *
        (Q'.ofNat l * Q'.ofNat (n - k)) := by
  have hcomp : k - (l - 1) = j := by omega
  have hcancel := tvBinomQ_mul_endpoint_factorials k (l - 1) (by omega)
  have hcancel' :
      tvBinomQ k (l - 1) * tvFallQ (l - 1) (l - 1) *
          tvFallQ j j ≈ Q'.ofNat (tvFact k) := by
    simpa only [hcomp] using hcancel
  have hlend := tvFallQ_pred_endpoint l hl
  have hnshift := tvFallQ_trailing_shift (n - l) (j - 1) (by omega)
  have hnshift' :
      tvFallQ (n - l) (j - 1) * Q'.ofNat (n - k) ≈
        tvFallQ (n - l) j := by
    simpa only [show n - l - (j - 1) = n - k by omega,
      show j - 1 + 1 = j by omega] using hnshift
  rw [hcomp]
  refine Q'.eqv_trans _
    (tvPhase (l - 1) * tvBinomQ k (l - 1) * tvFallQ j j *
      tvFallQ (m - j) (l - 1) *
      (Q'.ofNat l * tvFallQ (l - 1) (l - 1)) *
      (tvFallQ (n - l) (j - 1) * Q'.ofNat (n - k))) _ ?_ ?_
  · exact mul_eqv_congr
      (mul_eqv_congr (Q'.eqv_refl _) hlend)
      (Q'.eqv_symm hnshift')
  · refine Q'.eqv_trans _
      ((tvPhase (l - 1) *
          (tvBinomQ k (l - 1) * tvFallQ (l - 1) (l - 1) *
            tvFallQ j j) * tvFallQ (m - j) (l - 1) *
          tvFallQ (n - l) (j - 1)) *
        (Q'.ofNat l * Q'.ofNat (n - k))) _ (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hcancel')))

/-- Exact one-above-lowest row when the first label is saturated (`k=m`). -/
theorem one_above_lowest_left_saturated_closed
    (b c j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = b) (hbc : b < c) :
    transvectFactorialCoeff (b - 1) (c - 1) (b - 1) j l ≈
      (tvPhase (l - 1) * Q'.ofNat (tvFact (b - 1)) *
          tvFallQ ((b - 1) - j) (l - 1) *
          tvFallQ ((c - 1) - l) (j - 1)) *
        (Q'.ofNat l * Q'.ofNat (c - b)) := by
  have htwo := transvectFactorialCoeff_one_above_lowest_two_term
    (b - 1) (c - 1) (b - 1) j l hj hl (by omega)
  let T0 :=
    tvPhase (l - 1) * tvBinomQ (b - 1) (l - 1) *
      tvFallQ j ((b - 1) - (l - 1)) *
      tvFallQ ((b - 1) - j) (l - 1) * tvFallQ l (l - 1) *
      tvFallQ ((c - 1) - l) ((b - 1) - (l - 1))
  let T1 :=
    tvPhase l * tvBinomQ (b - 1) l * tvFallQ j ((b - 1) - l) *
      tvFallQ ((b - 1) - j) l * tvFallQ l l *
      tvFallQ ((c - 1) - l) ((b - 1) - l)
  have hfirst0 := one_above_lowest_first_term_closed
    (b - 1) (c - 1) (b - 1) j l hj hl (by omega) (by omega)
  have hfirst : T0 ≈
      (tvPhase (l - 1) * Q'.ofNat (tvFact (b - 1)) *
          tvFallQ ((b - 1) - j) (l - 1) *
          tvFallQ ((c - 1) - l) (j - 1)) *
        (Q'.ofNat l * Q'.ofNat (c - b)) := by
    simpa only [T0,
      show c - 1 - (b - 1) = c - b by omega] using hfirst0
  have hz : tvFallQ ((b - 1) - j) l ≈ 0 :=
    tvFallQ_eqv_zero_of_lt _ _ (by omega)
  let A := tvPhase l * tvBinomQ (b - 1) l *
    tvFallQ j ((b - 1) - l)
  have hz0 : A * tvFallQ ((b - 1) - j) l ≈ 0 :=
    Q'.eqv_trans _ (A * 0) _
      (Q'.mul_eqv_congr_left A _ _ hz) (Q'.mul_zero_eqv A)
  have hz1 : (A * tvFallQ ((b - 1) - j) l) * tvFallQ l l ≈ 0 :=
    Q'.eqv_trans _ (0 * tvFallQ l l) _
      (Q'.mul_eqv_congr_right _ _ _ hz0) (Q'.zero_mul_eqv _)
  have hsecond : T1 ≈ 0 := by
    simpa only [T1, A] using Q'.eqv_trans _
      (0 * tvFallQ ((c - 1) - l) ((b - 1) - l)) _
      (Q'.mul_eqv_congr_right _ _ _ hz1) (Q'.zero_mul_eqv _)
  refine Q'.eqv_trans _ (T0 + T1) _
    (by simpa only [T0, T1] using htwo) ?_
  refine Q'.eqv_trans _
    ((tvPhase (l - 1) * Q'.ofNat (tvFact (b - 1)) *
          tvFallQ ((b - 1) - j) (l - 1) *
          tvFallQ ((c - 1) - l) (j - 1)) *
        (Q'.ofNat l * Q'.ofNat (c - b)) + 0) _
    (Q'.add_eqv_congr' hfirst hsecond) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- Replacement for the inner-row reduction on the exact left endpoint
`p=b` (with the other label still unsaturated). -/
theorem first_bulk_inner_above_reduced_left_endpoint
    (b c j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = b) (hbc : b < c) :
    Q'.ofNat b *
        ((Q'.ofNat (b - j) * Q'.ofNat (c - l)) *
          transvectFactorialCoeff (b - 1) (c - 1) (b - 1) j l) ≈
      (Q'.ofNat j * Q'.ofNat (b - b) +
          -(Q'.ofNat l * Q'.ofNat (c - b))) *
        transvectFactorialCoeff b c b j l := by
  let R := tvPhase (l - 1) * Q'.ofNat (tvFact (b - 1)) *
    tvFallQ ((b - 1) - j) (l - 1) *
    tvFallQ ((c - 1) - l) (j - 1)
  let H0 := transvectFactorialCoeff (b - 1) (c - 1) (b - 1) j l
  let H := transvectFactorialCoeff b c b j l
  let D := Q'.ofNat b * (Q'.ofNat l * Q'.ofNat (c - l))
  let V := Q'.ofNat l * Q'.ofNat (c - b)
  have hsat := one_above_lowest_left_saturated_closed
    b c j l hj hl hsum hbc
  have hH0 : H0 ≈ R * V := by
    simpa only [H0, R, V] using hsat
  have hfull := transvectFactorialCoeff_lowest_row_closed b c b j l hsum
  have hphase0 := tvPhase_succ (l - 1)
  have hphase : tvPhase l ≈ -(tvPhase (l - 1)) := by
    simpa only [show l - 1 + 1 = l by omega] using hphase0
  have hfact : Q'.ofNat (tvFact b) ≈
      Q'.ofNat b * Q'.ofNat (tvFact (b - 1)) := by
    rw [show tvFact b = b * tvFact (b - 1) by
      cases b <;> simp_all [tvFact]]
    exact Q'.eqv_symm (ofNat_mul_eqv b (tvFact (b - 1)))
  have hl0 := tvFallQ_leading_shift l (l - 1)
  have hlshift : Q'.ofNat l * tvFallQ ((b - 1) - j) (l - 1) ≈
      tvFallQ (b - j) l := by
    simpa only [show (b - 1) - j = l - 1 by omega,
      show b - j = l by omega,
      show l - 1 + 1 = l by omega] using hl0
  have hc0 := tvFallQ_leading_shift (c - l) (j - 1)
  have hcshift : Q'.ofNat (c - l) *
      tvFallQ ((c - 1) - l) (j - 1) ≈ tvFallQ (c - l) j := by
    simpa only [show (c - 1) - l = c - l - 1 by omega,
      show j - 1 + 1 = j by omega] using hc0
  have hcomponents :
      tvPhase l * Q'.ofNat (tvFact b) * tvFallQ (b - j) l *
          tvFallQ (c - l) j ≈
        (-(tvPhase (l - 1))) *
          (Q'.ofNat b * Q'.ofNat (tvFact (b - 1))) *
          (Q'.ofNat l * tvFallQ ((b - 1) - j) (l - 1)) *
          (Q'.ofNat (c - l) * tvFallQ ((c - 1) - l) (j - 1)) :=
    mul_eqv_congr
      (mul_eqv_congr (mul_eqv_congr hphase hfact)
        (Q'.eqv_symm hlshift))
      (Q'.eqv_symm hcshift)
  have hH : H ≈ -(D * R) := by
    refine Q'.eqv_trans _
      (tvPhase l * Q'.ofNat (tvFact b) * tvFallQ (b - j) l *
        tvFallQ (c - l) j) _
      (by simpa only [H] using hfull) ?_
    refine Q'.eqv_trans _
      ((-(tvPhase (l - 1))) *
        (Q'.ofNat b * Q'.ofNat (tvFact (b - 1))) *
        (Q'.ofNat l * tvFallQ ((b - 1) - j) (l - 1)) *
        (Q'.ofNat (c - l) * tvFallQ ((c - 1) - l) (j - 1))) _
      hcomponents ?_
    simp only [D, R]
    ring_qeqv
  let Common := D * (R * V)
  have hleft :
      Q'.ofNat b *
          ((Q'.ofNat (b - j) * Q'.ofNat (c - l)) * H0) ≈
        Common := by
    refine Q'.eqv_trans _
      (Q'.ofNat b *
        ((Q'.ofNat l * Q'.ofNat (c - l)) * (R * V))) _ ?_ ?_
    · rw [show b - j = l by omega]
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hH0)
    · simp only [Common, D]
      ring_qeqv
  have hright :
      (Q'.ofNat j * Q'.ofNat (b - b) +
          -(Q'.ofNat l * Q'.ofNat (c - b))) * H ≈ Common := by
    refine Q'.eqv_trans _
      ((Q'.ofNat j * Q'.ofNat (b - b) +
          -(Q'.ofNat l * Q'.ofNat (c - b))) * (-(D * R))) _
      (Q'.mul_eqv_congr_left _ _ _ hH) ?_
    simp only [Common, V, Nat.sub_self]
    ring_zero_qeqv
  exact Q'.eqv_trans _ Common _ hleft (Q'.eqv_symm hright)

/-- At `p=b`, the multiplier cancelled by the strict inner-row proof is zero. -/
theorem left_inner_endpoint_cancellation_scale_zero
    (b c p : Nat) (hpb : p = b) :
    Q'.ofNat (b - p) * Q'.ofNat (c - p) ≈ 0 := by
  subst b
  simp only [Nat.sub_self]
  exact Q'.zero_mul_eqv _

/-- At `p=c`, the same strict multiplier is zero by its other factor. -/
theorem right_inner_endpoint_cancellation_scale_zero
    (b c p : Nat) (hpc : p = c) :
    Q'.ofNat (b - p) * Q'.ofNat (c - p) ≈ 0 := by
  subst c
  simp only [Nat.sub_self]
  exact Q'.mul_zero_eqv _

/-- The left endpoint is disjoint from the strict hypothesis used previously. -/
theorem left_inner_endpoint_not_strict
    (b p : Nat) (hpb : p = b) : ¬ p < b := by
  omega

/-- The right endpoint is disjoint from the strict hypothesis used previously. -/
theorem right_inner_endpoint_not_strict
    (c p : Nat) (hpc : p = c) : ¬ p < c := by
  omega

end YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnInnerBoundary

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnInnerBoundary.left_inner_endpoint_cancellation_scale_zero
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnInnerBoundary.right_inner_endpoint_cancellation_scale_zero
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnInnerBoundary.left_inner_endpoint_not_strict
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnInnerBoundary.right_inner_endpoint_not_strict
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnInnerBoundary.one_above_lowest_left_saturated_closed
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnInnerBoundary.first_bulk_inner_above_reduced_left_endpoint
