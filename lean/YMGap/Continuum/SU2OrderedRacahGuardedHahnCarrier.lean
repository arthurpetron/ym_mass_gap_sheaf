/-
# Exact guarded Hahn carrier for the ordered Racah bridge

The corrected raw ordered normalization is expressed through the actual
left/right channel Gram weights.  This file expands the corresponding cross
Gram entry into one finite rational sum.  The two inner Hahn factors carry
literal support guards; below their contraction orders the nested
transvectant coefficients are proved to vanish.
-/

import YMGap.Continuum.SU2OrderedRacahMultiplicityFence
import YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization
import YMGap.Continuum.SU2TransvectantAdmissibleSynthesis

namespace YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier

set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantGeneralCoefficient
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization
open YMGap.Continuum.SU2TransvectantAdmissibleSynthesis
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedFundamentalFRows
open YMGap.Continuum.SU2OrderedFixedOutputFKernel
open YMGap.Continuum.SU2OrderedRacahMultiplicityFence

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d := by
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a b c hab)
    (Q'.mul_eqv_congr_left b c d hcd)

/-! ## Exact lower-support fences -/

/-- A left-nested monomial coefficient vanishes when the first contraction
order exceeds the total input monomial index. -/
theorem triLeft_monomial_zero_below_inner_order {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (i j l s : Nat)
    (hbelow : i + j < q.k) :
    triLeft a b c d q.intermediate (mono i) (mono j) (mono l) s ≈ 0 := by
  have hinner : BFormEqv
      (transvect a b q.k (tprod (mono i) (mono j))) zeroF := by
    intro t
    exact transvect_monomial_zero_offshell a b q.k i j t (by omega)
  have htensor : BForm2Eqv
      (tprod (transvect a b q.k (tprod (mono i) (mono j))) (mono l))
      zeroForm2 := by
    intro x y
    unfold tprod zeroForm2
    exact Q'.eqv_trans _ (0 * mono l y) _
      (Q'.mul_eqv_congr_right _ _ _ (hinner x))
      (Q'.zero_mul_eqv _)
  have houter := transvect_congr q.intermediate c q.r htensor s
  have hzero := transvect_zeroForm2 q.intermediate c q.r s
  unfold triLeft
  rw [fixedLeft_inner_couplingOrder q, fixedLeft_outer_couplingOrder q]
  exact Q'.eqv_trans _ _ _ houter hzero

/-- A right-nested monomial coefficient vanishes when the last-pair
contraction order exceeds the total last-pair monomial index. -/
theorem triRight_monomial_zero_below_inner_order {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat)
    (hbelow : j + l < q.p) :
    triRight a b c d q.intermediate (mono i) (mono j) (mono l) s ≈ 0 := by
  have hinner : BFormEqv
      (transvect b c q.p (tprod (mono j) (mono l))) zeroF := by
    intro t
    exact transvect_monomial_zero_offshell b c q.p j l t (by omega)
  have htensor : BForm2Eqv
      (tprod (mono i) (transvect b c q.p (tprod (mono j) (mono l))))
      zeroForm2 := by
    intro x y
    unfold tprod zeroForm2
    exact Q'.eqv_trans _ (mono i x * 0) _
      (Q'.mul_eqv_congr_left _ _ _ (hinner y))
      (Q'.mul_zero_eqv _)
  have houter := transvect_congr a q.intermediate q.r htensor s
  have hzero := transvect_zeroForm2 a q.intermediate q.r s
  unfold triRight
  rw [fixedRight_inner_couplingOrder q, fixedRight_outer_couplingOrder q]
  exact Q'.eqv_trans _ _ _ houter hzero

/-! ## Guarded Hahn coefficients -/

/-- The literal finite Hahn/outer-transvectant coefficient for a physical
left channel, with its exact lower support guard. -/
def guardedLeftHahnCoefficient {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (i j l s : Nat) : Q' :=
  if q.k ≤ i + j then
    hahnEntry a b (i + j) q.k i *
      transvect q.intermediate c q.r
        (tprod (mono (i + j - q.k)) (mono l)) s
  else 0

/-- The literal finite Hahn/outer-transvectant coefficient for a physical
right channel, with its exact lower support guard. -/
def guardedRightHahnCoefficient {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat) : Q' :=
  if q.p ≤ j + l then
    hahnEntry b c (j + l) q.p j *
      transvect a q.intermediate q.r
        (tprod (mono i) (mono (j + l - q.p))) s
  else 0

theorem triLeft_monomial_eq_guardedHahn {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (i j l s : Nat) :
    triLeft a b c d q.intermediate (mono i) (mono j) (mono l) s ≈
      guardedLeftHahnCoefficient q i j l s := by
  by_cases h : q.k ≤ i + j
  · rw [guardedLeftHahnCoefficient, if_pos h]
    have h' : couplingOrder a b q.intermediate ≤ i + j := by
      rw [fixedLeft_inner_couplingOrder q]
      exact h
    simpa only [fixedLeft_inner_couplingOrder q,
      fixedLeft_outer_couplingOrder q] using
      triLeft_monomial_factorization a b c d q.intermediate i j l s h'
  · rw [guardedLeftHahnCoefficient, if_neg h]
    exact triLeft_monomial_zero_below_inner_order q i j l s (by omega)

theorem triRight_monomial_eq_guardedHahn {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat) :
    triRight a b c d q.intermediate (mono i) (mono j) (mono l) s ≈
      guardedRightHahnCoefficient q i j l s := by
  by_cases h : q.p ≤ j + l
  · rw [guardedRightHahnCoefficient, if_pos h]
    have h' : couplingOrder b c q.intermediate ≤ j + l := by
      rw [fixedRight_inner_couplingOrder q]
      exact h
    simpa only [fixedRight_inner_couplingOrder q,
      fixedRight_outer_couplingOrder q] using
      triRight_monomial_factorization a b c d q.intermediate i j l s h'
  · rw [guardedRightHahnCoefficient, if_neg h]
    exact triRight_monomial_zero_below_inner_order q i j l s (by omega)

/-! ## Fully factorialized outer coefficients -/

/-- The left coefficient with both its inner-order guard and its exact outer
output-shell guard visible. -/
def guardedLeftFactorialCoefficient {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (i j l s : Nat) : Q' :=
  if q.k ≤ i + j then
    hahnEntry a b (i + j) q.k i *
      (if s + q.r = (i + j - q.k) + l then
        transvectFactorialCoeff q.intermediate c q.r (i + j - q.k) l
      else 0)
  else 0

/-- The right coefficient with both its inner-order guard and its exact outer
output-shell guard visible. -/
def guardedRightFactorialCoefficient {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat) : Q' :=
  if q.p ≤ j + l then
    hahnEntry b c (j + l) q.p j *
      (if s + q.r = i + (j + l - q.p) then
        transvectFactorialCoeff a q.intermediate q.r i (j + l - q.p)
      else 0)
  else 0

theorem guardedLeftHahnCoefficient_eq_factorial {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (i j l s : Nat) :
    guardedLeftHahnCoefficient q i j l s ≈
      guardedLeftFactorialCoefficient q i j l s := by
  unfold guardedLeftHahnCoefficient guardedLeftFactorialCoefficient
  by_cases h : q.k ≤ i + j
  · rw [if_pos h, if_pos h]
    exact Q'.mul_eqv_congr_left _ _ _
      (transvect_monomial_factorial_formula q.intermediate c q.r
        (i + j - q.k) l s)
  · rw [if_neg h, if_neg h]
    exact Q'.eqv_refl 0

theorem guardedRightHahnCoefficient_eq_factorial {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat) :
    guardedRightHahnCoefficient q i j l s ≈
      guardedRightFactorialCoefficient q i j l s := by
  unfold guardedRightHahnCoefficient guardedRightFactorialCoefficient
  by_cases h : q.p ≤ j + l
  · rw [if_pos h, if_pos h]
    exact Q'.mul_eqv_congr_left _ _ _
      (transvect_monomial_factorial_formula a q.intermediate q.r
        i (j + l - q.p) s)
  · rw [if_neg h, if_neg h]
    exact Q'.eqv_refl 0

/-! ## The finite cross-Gram carrier -/

def triCrossChannelWeight {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Q' :=
  triMapInner a b c d (triLeft a b c d qL.intermediate)
    (triRight a b c d qR.intermediate)

def guardedHahnCrossSummand {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d)
    (i j l s : Nat) : Q' :=
  tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
    symMonomialNormSq d s *
      (guardedLeftHahnCoefficient qL i j l s *
        guardedRightHahnCoefficient qR i j l s)

/-- A completely finite, division-free, exactly guarded Hahn carrier for one
left/right cross-Gram entry. -/
def guardedHahnCrossSum {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Q' :=
  finSum (fun i => finSum (fun j => finSum (fun l => finSum (fun s =>
    guardedHahnCrossSummand qL qR i j l s) (d + 1)) (c + 1))
      (b + 1)) (a + 1)

/-- **Arbitrary-label finite Hahn expansion of the physical cross Gram.**
All four sums have exact degree bounds, and both inner contractions have
literal support guards. -/
theorem triCrossChannelWeight_eq_guardedHahnCrossSum {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    triCrossChannelWeight qL qR ≈ guardedHahnCrossSum qL qR := by
  unfold triCrossChannelWeight guardedHahnCrossSum triMapInner
  refine finSum_eqv_congr _ _ (fun i => ?_) (a + 1)
  refine finSum_eqv_congr _ _ (fun j => ?_) (b + 1)
  refine finSum_eqv_congr _ _ (fun l => ?_) (c + 1)
  refine finSum_eqv_congr _ _ (fun s => ?_) (d + 1)
  unfold guardedHahnCrossSummand
  exact Q'.mul_eqv_congr_left
    (tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
      symMonomialNormSq d s) _ _
    (mul_eqv_congr
      (triLeft_monomial_eq_guardedHahn qL i j l s)
      (triRight_monomial_eq_guardedHahn qR i j l s))

/-- The same carrier after eliminating the remaining outer transvectants in
favor of their exact all-order factorial coefficients. -/
def guardedFactorialCrossSummand {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d)
    (i j l s : Nat) : Q' :=
  tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
    symMonomialNormSq d s *
      (guardedLeftFactorialCoefficient qL i j l s *
        guardedRightFactorialCoefficient qR i j l s)

def guardedFactorialCrossSum {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Q' :=
  finSum (fun i => finSum (fun j => finSum (fun l => finSum (fun s =>
    guardedFactorialCrossSummand qL qR i j l s) (d + 1)) (c + 1))
      (b + 1)) (a + 1)

theorem guardedHahnCrossSum_eq_factorialCrossSum {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    guardedHahnCrossSum qL qR ≈ guardedFactorialCrossSum qL qR := by
  unfold guardedHahnCrossSum guardedFactorialCrossSum
  refine finSum_eqv_congr _ _ (fun i => ?_) (a + 1)
  refine finSum_eqv_congr _ _ (fun j => ?_) (b + 1)
  refine finSum_eqv_congr _ _ (fun l => ?_) (c + 1)
  refine finSum_eqv_congr _ _ (fun s => ?_) (d + 1)
  unfold guardedHahnCrossSummand guardedFactorialCrossSummand
  exact Q'.mul_eqv_congr_left
    (tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
      symMonomialNormSq d s) _ _
    (mul_eqv_congr
      (guardedLeftHahnCoefficient_eq_factorial qL i j l s)
      (guardedRightHahnCoefficient_eq_factorial qR i j l s))

/-- **Final arbitrary-label factorial carrier.**  The physical cross Gram is
the fourfold finite sum of explicit factorial coefficients with exact inner
and output-shell support guards. -/
theorem triCrossChannelWeight_eq_guardedFactorialCrossSum {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    triCrossChannelWeight qL qR ≈ guardedFactorialCrossSum qL qR :=
  Q'.eqv_trans _ _ _
    (triCrossChannelWeight_eq_guardedHahnCrossSum qL qR)
    (guardedHahnCrossSum_eq_factorialCrossSum qL qR)

/-! ## Zero-leg, parity, and fundamental normalization audits -/

/-- Physical channel records expose both parity equations exactly: each
intermediate degree is the external degree sum minus twice its contraction
order. -/
theorem fixed_channels_parity_audit {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    qL.intermediate + 2 * qL.k = a + b ∧
    qR.intermediate + 2 * qR.p = b + c := by
  constructor
  · unfold FixedLeftCGChannel.intermediate
    have hk := Nat.le_min.mp qL.k_le
    omega
  · unfold FixedRightCGChannel.intermediate
    have hp := Nat.le_min.mp qR.p_le
    omega

theorem zero_leg_guarded_cross_exact :
    guardedHahnCrossSum zeroLeft zeroRight ≈ 2 := by
  decide

theorem zero_leg_guarded_factorial_cross_exact :
    guardedFactorialCrossSum zeroLeft zeroRight ≈ 2 := by
  decide

theorem fundamental_guarded_cross_entries :
    guardedHahnCrossSum fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet ≈ -2 ∧
    guardedHahnCrossSum fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet ≈ 6 ∧
    guardedHahnCrossSum fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet ≈ 6 ∧
    guardedHahnCrossSum fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet ≈ 6 := by
  decide

theorem fundamental_guarded_factorial_cross_entries :
    guardedFactorialCrossSum fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet ≈ -2 ∧
    guardedFactorialCrossSum fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet ≈ 6 ∧
    guardedFactorialCrossSum fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet ≈ 6 ∧
    guardedFactorialCrossSum fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet ≈ 6 := by
  decide

/-- The zero-leg cross entry has the source-weight orientation
`cross = W_left * F_raw`; this is the orientation used before squaring. -/
theorem zero_leg_cross_fixedF_normalization :
    guardedHahnCrossSum zeroLeft zeroRight ≈
      triLeftChannelWeight 0 1 1 0 zeroLeft.intermediate *
        fixedOrderedFCoefficient zeroLeft zeroRight := by
  decide

/-- All four fundamental entries confirm the same source-weight orientation.
In particular the off-diagonal values are both `6`; dividing by the unequal
left weights `4,12` produces the ordered raw entries `3/2,1/2`. -/
theorem fundamental_cross_fixedF_normalization :
    guardedHahnCrossSum fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet ≈
      triLeftChannelWeight 1 1 1 1 0 *
        fixedOrderedFCoefficient fundamentalFixedLeftSinglet
          fundamentalFixedRightSinglet ∧
    guardedHahnCrossSum fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet ≈
      triLeftChannelWeight 1 1 1 1 0 *
        fixedOrderedFCoefficient fundamentalFixedLeftSinglet
          fundamentalFixedRightTriplet ∧
    guardedHahnCrossSum fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet ≈
      triLeftChannelWeight 1 1 1 1 2 *
        fixedOrderedFCoefficient fundamentalFixedLeftTriplet
          fundamentalFixedRightSinglet ∧
    guardedHahnCrossSum fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet ≈
      triLeftChannelWeight 1 1 1 1 2 *
        fixedOrderedFCoefficient fundamentalFixedLeftTriplet
          fundamentalFixedRightTriplet := by
  decide

end YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier

#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.triLeft_monomial_zero_below_inner_order
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.triRight_monomial_zero_below_inner_order
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.triLeft_monomial_eq_guardedHahn
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.triRight_monomial_eq_guardedHahn
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.guardedLeftHahnCoefficient_eq_factorial
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.guardedRightHahnCoefficient_eq_factorial
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.triCrossChannelWeight_eq_guardedHahnCrossSum
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.guardedHahnCrossSum_eq_factorialCrossSum
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.triCrossChannelWeight_eq_guardedFactorialCrossSum
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.fixed_channels_parity_audit
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.zero_leg_guarded_cross_exact
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.fundamental_guarded_cross_entries
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.zero_leg_guarded_factorial_cross_exact
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.fundamental_guarded_factorial_cross_entries
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.zero_leg_cross_fixedF_normalization
#print axioms YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier.fundamental_cross_fixedF_normalization
