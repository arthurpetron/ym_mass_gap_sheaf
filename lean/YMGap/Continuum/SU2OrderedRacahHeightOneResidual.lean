/-
# Exact correction residual introduced at height one

The height-zero proof has no `l-2` factorial summand.  At height one that
summand occurs in both the reduced exchange sample and the lower adjacent
carrier.  This module separates those two new contributions from the legacy
two-term expression and factors the exact correction residual.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneCarrier

namespace YMGap.Continuum.SU2OrderedRacahHeightOneResidual

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahHeightOneCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

/-- The genuinely new `l-2` contribution in the reduced exchange sample. -/
def heightOneReducedNewTerm {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  heightFactorialSummand (b - 1) (c - 1) (q.p - 1) j l (l - 2) *
    transvectFactorialCoeff a q.intermediate q.r (i - 1) 2

/-- The old two summands in that reduced exchange sample. -/
def heightOneReducedLegacyTerm {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  (heightFactorialSummand (b - 1) (c - 1) (q.p - 1) j l (l - 1) +
      heightFactorialSummand (b - 1) (c - 1) (q.p - 1) j l l) *
    transvectFactorialCoeff a q.intermediate q.r (i - 1) 2

/-- The genuinely new `l-2` contribution in the lower adjacent carrier. -/
def heightOneLowerNewTerm {a b c d : Nat}
    (qm : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  heightFactorialSummand b c qm.p j l (l - 2) *
    transvectFactorialCoeff a qm.intermediate qm.r i 2

/-- The old two summands in the lower adjacent carrier. -/
def heightOneLowerLegacyTerm {a b c d : Nat}
    (qm : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  (heightFactorialSummand b c qm.p j l (l - 1) +
      heightFactorialSummand b c qm.p j l l) *
    transvectFactorialCoeff a qm.intermediate qm.r i 2

/-- Exact split of the reduced height-one exchange sample. -/
theorem reduced_height_one_sample_split {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1) :
    rightShellFactorialCoefficient (reducePositiveInnerRightChannel q hp)
        (i - 1) j l ≈
      heightOneReducedNewTerm q i j l +
        heightOneReducedLegacyTerm q i j l := by
  let qr := reducePositiveInnerRightChannel q hp
  have hinner := reduced_inner_height_one_three_term
    q hp j l hj hl hheight
  unfold rightShellFactorialCoefficient
  rw [if_pos (by
    change q.p - 1 ≤ j + l
    omega)]
  unfold hahnEntry
  rw [reduced_inner_order_eq q hp, reduced_intermediate_eq q hp]
  simp only [show j + l - j = l by omega,
    show j + l - (q.p - 1) = 2 by omega]
  refine Q'.eqv_trans _
    (((heightFactorialSummand (b - 1) (c - 1) (q.p - 1) j l (l - 2) +
        heightFactorialSummand (b - 1) (c - 1) (q.p - 1) j l (l - 1)) +
        heightFactorialSummand (b - 1) (c - 1) (q.p - 1) j l l) *
      transvectFactorialCoeff a q.intermediate q.r (i - 1) 2) _
    (Q'.mul_eqv_congr_right _ _ _ hinner) ?_
  unfold heightOneReducedNewTerm heightOneReducedLegacyTerm
  ring_qeqv

/-- Exact split of the lower adjacent height-one carrier. -/
theorem lower_height_one_sample_split {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1) (i j l : Nat)
    (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1) :
    rightShellFactorialCoefficient qm i j l ≈
      heightOneLowerNewTerm qm i j l +
        heightOneLowerLegacyTerm qm i j l := by
  have hsum : j + l = qm.p + 2 := by omega
  have hinner := transvectFactorialCoeff_two_above_lowest_three_term
    b c qm.p j l hj hl hsum
  unfold rightShellFactorialCoefficient
  rw [if_pos (by omega : qm.p ≤ j + l)]
  unfold hahnEntry
  simp only [show j + l - j = l by omega,
    show j + l - qm.p = 2 by omega]
  refine Q'.eqv_trans _
    (((heightFactorialSummand b c qm.p j l (l - 2) +
        heightFactorialSummand b c qm.p j l (l - 1)) +
        heightFactorialSummand b c qm.p j l l) *
      transvectFactorialCoeff a qm.intermediate qm.r i 2) _
    (Q'.mul_eqv_congr_right _ _ _ hinner) ?_
  unfold heightOneLowerNewTerm heightOneLowerLegacyTerm
  ring_qeqv

/-- Height-one correction LHS with the new reduced `l-2` term omitted. -/
def heightOneLegacyCorrectionLHS {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) : Q' :=
  let qr := reducePositiveInnerRightChannel q hp
  (Q'.ofNat i * Q'.ofNat (b - j)) *
      (Q'.ofNat (c - l) * heightOneReducedLegacyTerm q i j l +
        Q'.ofNat l * rightShellFactorialCoefficient qr i j (l - 1)) +
    -((Q'.ofNat (a - i) * Q'.ofNat j) *
      (Q'.ofNat (c - l) * rightShellFactorialCoefficient qr i (j - 1) l +
        Q'.ofNat l *
          rightShellFactorialCoefficient qr (i + 1) (j - 1) (l - 1)))

/-- Height-one correction RHS with the new lower-carrier `l-2` term omitted. -/
def heightOneLegacyCorrectionRHS {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  omegaCorrectionLowerCoefficient a b c d q.p *
      heightOneLowerLegacyTerm qm i j l +
    omegaCorrectionDiagonalCoefficient a b c d q.p *
      rightShellFactorialCoefficient q i j l +
    omegaCorrectionUpperCoefficient a b c d q.p *
      rightShellFactorialCoefficient qp i j l

/-- Contribution of the new reduced summand to the exchange side. -/
def heightOneNewExchangeContribution {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  ((Q'.ofNat i * Q'.ofNat (b - j)) * Q'.ofNat (c - l)) *
    heightOneReducedNewTerm q i j l

/-- Contribution of the new lower summand to the carrier side. -/
def heightOneNewLowerContribution {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  omegaCorrectionLowerCoefficient a b c d q.p *
    heightOneLowerNewTerm qm i j l

theorem height_one_correction_lhs_split {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1) :
    omegaExchangeCorrection a b c
        (fun u v w => rightShellFactorialCoefficient
          (reducePositiveInnerRightChannel q hp) u v w) i j l ≈
      heightOneLegacyCorrectionLHS q hp i j l +
        heightOneNewExchangeContribution q i j l := by
  have hx := reduced_height_one_sample_split q hp i j l hj hl hheight
  unfold omegaExchangeCorrection heightOneLegacyCorrectionLHS
    heightOneNewExchangeContribution
  refine Q'.eqv_trans _
    ((Q'.ofNat i * Q'.ofNat (b - j)) *
        (Q'.ofNat (c - l) *
            (heightOneReducedNewTerm q i j l +
              heightOneReducedLegacyTerm q i j l) +
          Q'.ofNat l * rightShellFactorialCoefficient
            (reducePositiveInnerRightChannel q hp) i j (l - 1)) +
      -((Q'.ofNat (a - i) * Q'.ofNat j) *
        (Q'.ofNat (c - l) * rightShellFactorialCoefficient
            (reducePositiveInnerRightChannel q hp) i (j - 1) l +
          Q'.ofNat l * rightShellFactorialCoefficient
            (reducePositiveInnerRightChannel q hp) (i + 1) (j - 1) (l - 1)))) _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ hx)
          (Q'.eqv_refl _)))
      (Q'.eqv_refl _)) ?_
  ring_qeqv

theorem height_one_correction_rhs_split {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1) (i j l : Nat)
    (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1) :
    omegaCorrectionLowerCoefficient a b c d q.p *
          rightShellFactorialCoefficient qm i j l +
        omegaCorrectionDiagonalCoefficient a b c d q.p *
          rightShellFactorialCoefficient q i j l +
        omegaCorrectionUpperCoefficient a b c d q.p *
          rightShellFactorialCoefficient qp i j l ≈
      heightOneLegacyCorrectionRHS qm q qp i j l +
        heightOneNewLowerContribution qm q i j l := by
  have hm := lower_height_one_sample_split qm q hprev i j l hj hl hheight
  unfold heightOneLegacyCorrectionRHS heightOneNewLowerContribution
  refine Q'.eqv_trans _
    (omegaCorrectionLowerCoefficient a b c d q.p *
          (heightOneLowerNewTerm qm i j l +
            heightOneLowerLegacyTerm qm i j l) +
        omegaCorrectionDiagonalCoefficient a b c d q.p *
          rightShellFactorialCoefficient q i j l +
        omegaCorrectionUpperCoefficient a b c d q.p *
          rightShellFactorialCoefficient qp i j l) _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hm)
        (Q'.eqv_refl _))
      (Q'.eqv_refl _)) ?_
  ring_qeqv

/-- Exact factorization of the first height-step residual.  Relative to the
legacy two-term expression, the only newly exposed defect is the reduced
exchange contribution minus the lower-carrier contribution. -/
theorem height_one_correction_residual_factorization {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) (i j l : Nat)
    (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1) :
    (omegaExchangeCorrection a b c
          (fun u v w => rightShellFactorialCoefficient
            (reducePositiveInnerRightChannel q hp) u v w) i j l +
        -((omegaCorrectionLowerCoefficient a b c d q.p *
              rightShellFactorialCoefficient qm i j l +
            omegaCorrectionDiagonalCoefficient a b c d q.p *
              rightShellFactorialCoefficient q i j l) +
          omegaCorrectionUpperCoefficient a b c d q.p *
            rightShellFactorialCoefficient qp i j l)) ≈
      (heightOneLegacyCorrectionLHS q hp i j l +
          -(heightOneLegacyCorrectionRHS qm q qp i j l)) +
        (heightOneNewExchangeContribution q i j l +
          -(heightOneNewLowerContribution qm q i j l)) := by
  have hL := height_one_correction_lhs_split q hp i j l hj hl hheight
  have hR := height_one_correction_rhs_split
    qm q qp hprev i j l hj hl hheight
  refine Q'.eqv_trans _
    ((heightOneLegacyCorrectionLHS q hp i j l +
          heightOneNewExchangeContribution q i j l) +
      -(heightOneLegacyCorrectionRHS qm q qp i j l +
          heightOneNewLowerContribution qm q i j l)) _
    (Q'.add_eqv_congr' hL (Q'.neg_eqv_congr _ _ hR)) ?_
  ring_qeqv

/-- Lower channel in a closed physical block exposing the first height-one
three-summand correction. -/
def heightOneFenceLower : FixedRightCGChannel 4 5 5 4 where
  p := 2
  p_le := by decide
  r := 3
  r_le := by decide
  degree_eq := by decide

/-- Middle channel in the height-one fence block. -/
def heightOneFenceMiddle : FixedRightCGChannel 4 5 5 4 where
  p := 3
  p_le := by decide
  r := 2
  r_le := by decide
  degree_eq := by decide

/-- Upper channel in the height-one fence block. -/
def heightOneFenceUpper : FixedRightCGChannel 4 5 5 4 where
  p := 4
  p_le := by decide
  r := 1
  r_le := by decide
  degree_eq := by decide

/-- The closed fence really is a consecutive physical three-channel block,
and `(i,j,l)=(3,2,2)` is at height one. -/
theorem height_one_fence_physical_data :
    0 < heightOneFenceMiddle.p ∧
    heightOneFenceMiddle.p = heightOneFenceLower.p + 1 ∧
    heightOneFenceUpper.p = heightOneFenceMiddle.p + 1 ∧
    2 ≤ (2 : Nat) ∧ 2 ≤ (2 : Nat) ∧
    2 + 2 = heightOneFenceMiddle.p + 1 := by
  decide

/-- The new reduced exchange summand has this exact value at the fence. -/
theorem height_one_fence_new_exchange_value :
    heightOneNewExchangeContribution heightOneFenceMiddle 3 2 2 ≈
      -(Q'.ofNat 2592) := by
  unfold heightOneNewExchangeContribution heightOneReducedNewTerm
    heightOneFenceMiddle
  decide

/-- The new lower-carrier summand has a different exact value. -/
theorem height_one_fence_new_lower_value :
    heightOneNewLowerContribution
        heightOneFenceLower heightOneFenceMiddle 3 2 2 ≈
      -(Q'.mkPos 15552 5 (by decide)) := by
  unfold heightOneNewLowerContribution heightOneLowerNewTerm
    heightOneFenceLower heightOneFenceMiddle
  decide

/-- **Height-one cancellation fence.**  The two newly exposed `l-2` terms
do not cancel each other: their exact residual is `2592/5`.  Consequently a
correct symbolic height-one proof must retain and cancel the legacy
two-summand residual; discarding it cannot prove the correction identity. -/
theorem height_one_new_terms_exact_residual :
    heightOneNewExchangeContribution heightOneFenceMiddle 3 2 2 +
        -(heightOneNewLowerContribution
          heightOneFenceLower heightOneFenceMiddle 3 2 2) ≈
      Q'.mkPos 2592 5 (by decide) := by
  unfold heightOneNewExchangeContribution heightOneReducedNewTerm
    heightOneNewLowerContribution heightOneLowerNewTerm
    heightOneFenceLower heightOneFenceMiddle
  decide

theorem height_one_new_terms_do_not_cancel :
    ¬ (heightOneNewExchangeContribution heightOneFenceMiddle 3 2 2 +
        -(heightOneNewLowerContribution
          heightOneFenceLower heightOneFenceMiddle 3 2 2) ≈ 0) := by
  unfold heightOneNewExchangeContribution heightOneReducedNewTerm
    heightOneNewLowerContribution heightOneLowerNewTerm
    heightOneFenceLower heightOneFenceMiddle
  decide

/-- The retained legacy residual supplies exactly the opposite fence value.
This pins down the compensating mechanism rather than merely observing that
the complete finite row happens to vanish. -/
theorem height_one_fence_legacy_exact_compensation :
    heightOneLegacyCorrectionLHS heightOneFenceMiddle (by decide) 3 2 2 +
        -(heightOneLegacyCorrectionRHS
          heightOneFenceLower heightOneFenceMiddle heightOneFenceUpper
          3 2 2) ≈
      -(Q'.mkPos 2592 5 (by decide)) := by
  unfold heightOneLegacyCorrectionLHS heightOneLegacyCorrectionRHS
    heightOneReducedLegacyTerm heightOneLowerLegacyTerm
    heightOneFenceLower heightOneFenceMiddle heightOneFenceUpper
  decide

/-- The exact compensation closes the full correction row at the fence. -/
theorem height_one_fence_full_correction :
    OmegaCorrectionShellAt heightOneFenceLower heightOneFenceMiddle
      heightOneFenceUpper (by decide) 3 2 2 := by
  unfold OmegaCorrectionShellAt omegaExchangeCorrection
    rightShellFactorialCoefficient heightOneFenceLower
    heightOneFenceMiddle heightOneFenceUpper
    reducePositiveInnerRightChannel
  decide

end YMGap.Continuum.SU2OrderedRacahHeightOneResidual

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneResidual.reduced_height_one_sample_split
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneResidual.lower_height_one_sample_split
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneResidual.height_one_correction_residual_factorization
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneResidual.height_one_new_terms_exact_residual
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneResidual.height_one_new_terms_do_not_cancel
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneResidual.height_one_fence_legacy_exact_compensation
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneResidual.height_one_fence_full_correction
