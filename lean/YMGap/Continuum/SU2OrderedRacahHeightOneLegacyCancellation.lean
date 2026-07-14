/-
# Height-one legacy compensation

The three-summand residual split shows that the complete height-one
correction closes exactly when the retained legacy two-summand residual
cancels the newly exposed `l-2` residual.  This module supplies the exact
constructive bridge and is the active home for the symbolic cancellation.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneResidual
import YMGap.Continuum.SU2TransvectantHighestWeightGramFormula

namespace YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantHighestWeightRowFormula
open YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahHeightOneCarrier
open YMGap.Continuum.SU2OrderedRacahHeightOneResidual

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ (b * c) _
    (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem neg_left_four_reassoc (A B C D E : Q') :
    ((((-A) * B) * C) * D) * E ≈ (-(((A * B) * C) * D)) * E := by
  have h1 : (-A) * B ≈ -(A * B) := Q'.neg_mul_eqv A B
  have h2 : ((-A) * B) * C ≈ -((A * B) * C) :=
    Q'.eqv_trans _ (-(A * B) * C) _
      (Q'.mul_eqv_congr_right _ _ C h1) (Q'.neg_mul_eqv (A * B) C)
  have h3 : (((-A) * B) * C) * D ≈ -(((A * B) * C) * D) :=
    Q'.eqv_trans _ (-((A * B) * C) * D) _
      (Q'.mul_eqv_congr_right _ _ D h2)
      (Q'.neg_mul_eqv ((A * B) * C) D)
  exact Q'.mul_eqv_congr_right _ _ E h3

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

/-- Common factorial carrier for the two-above-lowest row. -/
def heightTwoCommonFactor (m n k j l : Nat) : Q' :=
  tvPhase (l - 2) * Q'.ofNat (tvFact k) *
    tvFallQ (m - j) (l - 2) * tvFallQ (n - l) (j - 2)

/-- The signed mixed part of the quadratic height-two row. -/
def heightTwoMixedPolynomial (m n k j l : Nat) : Q' :=
  -(Q'.ofNat j * Q'.ofNat l * Q'.ofNat (m - k) *
      Q'.ofNat (n - k))

/-- The pure `j` part of the quadratic height-two row. -/
def heightTwoRightPolynomial (m k j : Nat) : Q' :=
  tvBinomQ j (j - 2) * Q'.ofNat (m - k) * Q'.ofNat (m - k - 1)

/-- The two-term legacy part of the height-two quadratic. -/
def heightTwoLegacyPolynomial (m n k j l : Nat) : Q' :=
  heightTwoMixedPolynomial m n k j l + heightTwoRightPolynomial m k j

/-- The middle (`l-1`) height-two summand is the mixed term of the exact
quadratic carrier. -/
theorem height_two_middle_summand_closed
    (m n k j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hsum : j + l = k + 2) (hkm : k + 2 ≤ m) (hkn : k + 2 ≤ n) :
    heightFactorialSummand m n k j l (l - 1) ≈
      heightTwoCommonFactor m n k j l *
        heightTwoMixedPolynomial m n k j l := by
  have hcomp : k - (l - 1) = j - 1 := by omega
  have hcancel := tvBinomQ_mul_endpoint_factorials k (l - 1) (by omega)
  have hcancel' :
      tvBinomQ k (l - 1) * tvFallQ (l - 1) (l - 1) *
          tvFallQ (j - 1) (j - 1) ≈ Q'.ofNat (tvFact k) := by
    simpa only [hcomp] using hcancel
  have hphase := tvPhase_succ (l - 2)
  have hphase' : tvPhase (l - 1) ≈ -(tvPhase (l - 2)) := by
    simpa only [show l - 2 + 1 = l - 1 by omega] using hphase
  have hjend := tvFallQ_pred_endpoint j (by omega)
  have hlend := tvFallQ_pred_endpoint l (by omega)
  have hmshift := tvFallQ_trailing_shift (m - j) (l - 2) (by omega)
  have hmshift' :
      tvFallQ (m - j) (l - 2) * Q'.ofNat (m - k) ≈
        tvFallQ (m - j) (l - 1) := by
    simpa only [show m - j - (l - 2) = m - k by omega,
      show l - 2 + 1 = l - 1 by omega] using hmshift
  have hnshift := tvFallQ_trailing_shift (n - l) (j - 2) (by omega)
  have hnshift' :
      tvFallQ (n - l) (j - 2) * Q'.ofNat (n - k) ≈
        tvFallQ (n - l) (j - 1) := by
    simpa only [show n - l - (j - 2) = n - k by omega,
      show j - 2 + 1 = j - 1 by omega] using hnshift
  unfold heightFactorialSummand
  rw [hcomp]
  refine Q'.eqv_trans _
    (-(tvPhase (l - 2)) * tvBinomQ k (l - 1) *
      (Q'.ofNat j * tvFallQ (j - 1) (j - 1)) *
      (tvFallQ (m - j) (l - 2) * Q'.ofNat (m - k)) *
      (Q'.ofNat l * tvFallQ (l - 1) (l - 1)) *
      (tvFallQ (n - l) (j - 2) * Q'.ofNat (n - k))) _ ?_ ?_
  · exact mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr
            (mul_eqv_congr hphase' (Q'.eqv_refl _)) hjend)
          (Q'.eqv_symm hmshift'))
        hlend)
      (Q'.eqv_symm hnshift')
  · unfold heightTwoCommonFactor heightTwoMixedPolynomial
    refine Q'.eqv_trans _
      ((-(tvPhase (l - 2)) *
          (tvBinomQ k (l - 1) * tvFallQ (l - 1) (l - 1) *
            tvFallQ (j - 1) (j - 1)) *
          tvFallQ (m - j) (l - 2) * tvFallQ (n - l) (j - 2)) *
        (Q'.ofNat j * Q'.ofNat l * Q'.ofNat (m - k) *
          Q'.ofNat (n - k))) _ (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      ((-(tvPhase (l - 2)) * Q'.ofNat (tvFact k) *
          tvFallQ (m - j) (l - 2) * tvFallQ (n - l) (j - 2)) *
        (Q'.ofNat j * Q'.ofNat l * Q'.ofNat (m - k) *
          Q'.ofNat (n - k))) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left _ _ _ hcancel')))) (by
        let X := tvPhase (l - 2) * Q'.ofNat (tvFact k) *
          tvFallQ (m - j) (l - 2) * tvFallQ (n - l) (j - 2)
        let S := Q'.ofNat j * Q'.ofNat l * Q'.ofNat (m - k) *
          Q'.ofNat (n - k)
        refine Q'.eqv_trans _ ((-X) * S) _ (by
          simpa only [X, S] using neg_left_four_reassoc
            (tvPhase (l - 2)) (Q'.ofNat (tvFact k))
              (tvFallQ (m - j) (l - 2))
              (tvFallQ (n - l) (j - 2)) S) ?_
        exact Q'.eqv_trans _ (-(X * S)) _
          (Q'.neg_mul_eqv X S) (Q'.eqv_symm (Q'.mul_neg_eqv X S)))

/-- The final (`l`) height-two summand is the pure `j` term of the exact
quadratic carrier. -/
theorem height_two_final_summand_closed
    (m n k j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hsum : j + l = k + 2) (hkm : k + 2 ≤ m) :
    heightFactorialSummand m n k j l l ≈
      heightTwoCommonFactor m n k j l *
        heightTwoRightPolynomial m k j := by
  have hcomp : k - l = j - 2 := by omega
  have hcancel := tvBinomQ_mul_endpoint_factorials k l (by omega)
  have hcancel' :
      tvBinomQ k l * tvFallQ l l * tvFallQ (j - 2) (j - 2) ≈
        Q'.ofNat (tvFact k) := by
    simpa only [hcomp] using hcancel
  have hphase1 := tvPhase_succ (l - 2)
  have hphase1' : tvPhase (l - 1) ≈ -(tvPhase (l - 2)) := by
    simpa only [show l - 2 + 1 = l - 1 by omega] using hphase1
  have hphase2 := tvPhase_succ (l - 1)
  have hphase2' : tvPhase l ≈ -(tvPhase (l - 1)) := by
    simpa only [show l - 1 + 1 = l by omega] using hphase2
  have hphase : tvPhase l ≈ tvPhase (l - 2) :=
    Q'.eqv_trans _ (-(tvPhase (l - 1))) _ hphase2'
      (Q'.eqv_trans _ (-(-(tvPhase (l - 2)))) _
        (Q'.neg_eqv_congr _ _ hphase1')
        (Q'.neg_neg_eqv (tvPhase (l - 2))))
  have hchoose0 := tvBinomQ_mul_fact_eq_fall j (j - 2) (by omega)
  have hjfact := tvFallQ_self_factorial (j - 2)
  have hchoose :
      tvFallQ j (j - 2) ≈
        tvBinomQ j (j - 2) * tvFallQ (j - 2) (j - 2) := by
    refine Q'.eqv_symm (Q'.eqv_trans _
      (tvBinomQ j (j - 2) * Q'.ofNat (tvFact (j - 2))) _ ?_ hchoose0)
    exact Q'.mul_eqv_congr_left _ _ _ hjfact
  have hmshift1 := tvFallQ_trailing_shift (m - j) (l - 2) (by omega)
  have hmshift1' :
      tvFallQ (m - j) (l - 2) * Q'.ofNat (m - k) ≈
        tvFallQ (m - j) (l - 1) := by
    simpa only [show m - j - (l - 2) = m - k by omega,
      show l - 2 + 1 = l - 1 by omega] using hmshift1
  have hmshift2 := tvFallQ_trailing_shift (m - j) (l - 1) (by omega)
  have hmshift2' :
      tvFallQ (m - j) (l - 1) * Q'.ofNat (m - k - 1) ≈
        tvFallQ (m - j) l := by
    simpa only [show m - j - (l - 1) = m - k - 1 by omega,
      show l - 1 + 1 = l by omega] using hmshift2
  have hmshift :
      (tvFallQ (m - j) (l - 2) * Q'.ofNat (m - k)) *
          Q'.ofNat (m - k - 1) ≈ tvFallQ (m - j) l :=
    Q'.eqv_trans _
      (tvFallQ (m - j) (l - 1) * Q'.ofNat (m - k - 1)) _
      (Q'.mul_eqv_congr_right _ _ _ hmshift1') hmshift2'
  unfold heightFactorialSummand
  rw [hcomp]
  refine Q'.eqv_trans _
    (tvPhase (l - 2) * tvBinomQ k l *
      (tvBinomQ j (j - 2) * tvFallQ (j - 2) (j - 2)) *
      ((tvFallQ (m - j) (l - 2) * Q'.ofNat (m - k)) *
        Q'.ofNat (m - k - 1)) *
      tvFallQ l l * tvFallQ (n - l) (j - 2)) _ ?_ ?_
  · exact mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr
            (mul_eqv_congr hphase (Q'.eqv_refl _)) hchoose)
          (Q'.eqv_symm hmshift))
        (Q'.eqv_refl _))
      (Q'.eqv_refl _)
  · unfold heightTwoCommonFactor heightTwoRightPolynomial
    refine Q'.eqv_trans _
      ((tvPhase (l - 2) *
          (tvBinomQ k l * tvFallQ l l *
            tvFallQ (j - 2) (j - 2)) *
          tvFallQ (m - j) (l - 2) * tvFallQ (n - l) (j - 2)) *
        (tvBinomQ j (j - 2) * Q'.ofNat (m - k) *
          Q'.ofNat (m - k - 1))) _ (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hcancel')))

/-- The retained two summands are exactly the common carrier times the
mixed-plus-right quadratic polynomial. -/
theorem height_two_legacy_pair_closed
    (m n k j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hsum : j + l = k + 2) (hkm : k + 2 ≤ m) (hkn : k + 2 ≤ n) :
    heightFactorialSummand m n k j l (l - 1) +
        heightFactorialSummand m n k j l l ≈
      heightTwoCommonFactor m n k j l *
        heightTwoLegacyPolynomial m n k j l := by
  have hm := height_two_middle_summand_closed
    m n k j l hj hl hsum hkm hkn
  have hr := height_two_final_summand_closed
    m n k j l hj hl hsum hkm
  refine Q'.eqv_trans _
    (heightTwoCommonFactor m n k j l *
        heightTwoMixedPolynomial m n k j l +
      heightTwoCommonFactor m n k j l *
        heightTwoRightPolynomial m k j) _
    (Q'.add_eqv_congr' hm hr) ?_
  unfold heightTwoLegacyPolynomial
  exact Q'.eqv_symm (Q'.mul_add_eqv
    (heightTwoCommonFactor m n k j l)
    (heightTwoMixedPolynomial m n k j l)
    (heightTwoRightPolynomial m k j))

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
    rw [Q'.add_zero']
    exact Q'.eqv_refl L
  have hright : 0 + R ≈ R := by
    rw [Q'.zero_add']
    exact Q'.eqv_refl R
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hR hright)

/-- Exact all-label closure criterion exposed by the height-one split.  The
legacy two-summand residual is not dispensable: once it is proved to be the
negative of the new `l-2` residual, the complete shell correction follows. -/
theorem height_one_correction_of_legacy_compensation {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) (i j l : Nat)
    (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hcomp :
      heightOneLegacyCorrectionLHS q hp i j l +
          -(heightOneLegacyCorrectionRHS qm q qp i j l) ≈
        -(heightOneNewExchangeContribution q i j l +
          -(heightOneNewLowerContribution qm q i j l))) :
    OmegaCorrectionShellAt qm q qp hp i j l := by
  let L := omegaExchangeCorrection a b c
    (fun u v w => rightShellFactorialCoefficient
      (reducePositiveInnerRightChannel q hp) u v w) i j l
  let R :=
    (omegaCorrectionLowerCoefficient a b c d q.p *
          rightShellFactorialCoefficient qm i j l +
      omegaCorrectionDiagonalCoefficient a b c d q.p *
          rightShellFactorialCoefficient q i j l) +
      omegaCorrectionUpperCoefficient a b c d q.p *
        rightShellFactorialCoefficient qp i j l
  let A := heightOneLegacyCorrectionLHS q hp i j l +
    -(heightOneLegacyCorrectionRHS qm q qp i j l)
  let B := heightOneNewExchangeContribution q i j l +
    -(heightOneNewLowerContribution qm q i j l)
  have hfactor : L + -R ≈ A + B := by
    simpa only [L, R, A, B] using
      height_one_correction_residual_factorization
        qm q qp hp hprev i j l hj hl hheight
  have hAB : A + B ≈ 0 := by
    refine Q'.eqv_trans _ ((-B) + B) _
      (Q'.add_eqv_congr_right A (-B) B (by
        simpa only [A, B] using hcomp)) ?_
    exact Q'.neg_add_self_eqv B
  have hres : L + -R ≈ 0 :=
    Q'.eqv_trans _ _ _ hfactor hAB
  unfold OmegaCorrectionShellAt
  simpa only [L, R] using eqv_of_add_neg_eqv_zero L R hres

/-- The exact fence compensation is consumed by the general bridge, rather
than by a second direct evaluation of the complete row. -/
theorem height_one_fence_from_legacy_compensation :
    OmegaCorrectionShellAt heightOneFenceLower heightOneFenceMiddle
      heightOneFenceUpper (by decide) 3 2 2 := by
  apply height_one_correction_of_legacy_compensation
    heightOneFenceLower heightOneFenceMiddle heightOneFenceUpper
    (by decide) (by decide) 3 2 2 (by decide) (by decide) (by decide)
  refine Q'.eqv_trans _ (-(Q'.mkPos 2592 5 (by decide))) _
    height_one_fence_legacy_exact_compensation ?_
  exact Q'.eqv_symm (Q'.neg_eqv_congr _ _
    height_one_new_terms_exact_residual)

end YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation.height_two_middle_summand_closed
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation.height_two_final_summand_closed
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation.height_two_legacy_pair_closed
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation.height_one_correction_of_legacy_compensation
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation.height_one_fence_from_legacy_compensation
