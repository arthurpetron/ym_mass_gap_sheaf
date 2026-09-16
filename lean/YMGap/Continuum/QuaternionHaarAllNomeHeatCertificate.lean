/-
# Late original heat prefixes of any supported Haar-unit quaternion word

The existing Jacobi positive polynomial and its finite-weight deficit give
the SAME headFloor/headCutoff for any supported Haar-unit word. The sharp
character interval controls every deficit term on the original carrier;
no pointwise-to-Haar inference or independence of spectators is used.

This is a finite positive certificate at each 0<w<1, not a centered
contraction, a coupling-uniform floor, or a physical spectral-gap claim.
-/

import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
import YMGap.Continuum.QuaternionHaarHeatCertificate

namespace YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval
open YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval (deficit deficit_bounds deficit_abs_small)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.JacobiWeightedHeatPolynomial (weight weightedPolynomial)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (pointwiseHeatMajorant)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound

def heatTerm (w : Q') (x : RatPoly) (n : Nat) : RatPoly :=
  polySmul (coeffW w n) (characterPolynomial x n)

/-- Actual sharp character certificates, not just scalar evaluation bounds. -/
def termInterval {w : Q'} (hw : (0 : Q') ≤ w) {blocks : Nat} {x : RatPoly}
    (P : SquareBound blocks x 1) (n : Nat) :
    Interval blocks (heatTerm w x n) (pointwiseHeatMajorant w n) :=
  ((sharpCharacterInterval P n).smul (coeffW w n) (coeffW_nonneg hw n)).changeCap
    (heat_dimension_majorant w n)

def prefixInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1) (K : Nat) :
    Interval blocks (heatPrefix w K x) (prefixCap w) :=
  (Interval.finiteRange (heatTerm w x) (pointwiseHeatMajorant w)
    (termInterval (Q'.le_of_lt hw0) P) (K+1)).weaken (majorant_prefix_bound hw0 hw1 (K+1))

def deficitPolynomial (w : Q') (N : Nat) (x : RatPoly) : RatPoly :=
  finitePolySum (fun r => polySmul (deficit w N r) (heatTerm w x r)) (List.range N)

theorem prefix_eq_weighted_add_deficit (w : Q') (K : Nat) (x : RatPoly) :
    RatPolyCoeffEqv (heatPrefix w K x)
      (polyAdd (weightedPolynomial w (K+1) x) (deficitPolynomial w (K+1) x)) :=
  (PolynomialWeightedSumBounds.weighted_recombine (heatTerm w x) (weight w (K+1)) (List.range (K+1))).symm

private def weightedRangeInterval {blocks : Nat} (f : Nat → RatPoly) (c a : Nat → Q')
    (hI : ∀ r, Interval blocks (f r) (c r)) (ha : ∀ r, (0 : Q') ≤ a r)
    (N : Nat) (A : Q') (hA : ∀ r, r < N → a r ≤ A) :
    Interval blocks (finitePolySum (fun r => polySmul (a r) (f r)) (List.range N)) (A * finSum c N) :=
  (Interval.finiteRange _ _ (fun r => (hI r).smul (a r) (ha r)) N).weaken
    (Q'.le_trans' _ _ _ (finSum_le_lt _ _ N (fun r hr =>
      Q'.mul_le_mul_of_nonneg_right _ _ _ (hA r hr) (hI r).nonnegative))
      (Q'.ge_of_eqv (const_mul_finSum c A N)))

private theorem majorant_tail_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat) (hK : tailCutoff w epsilon ≤ K) :
    finSum (fun r => pointwiseHeatMajorant w (K+1+r)) L ≤ epsilon := by
  have hN : spacingLabelCutoff w ≤ K+1 := by unfold tailCutoff at hK; omega
  have hM : spacingTailCauchyCutoff w epsilon ≤ K+1-spacingLabelCutoff w := by
    unfold tailCutoff at hK
    omega
  have h := shiftedMajorant_block hw0 hw1 (K+1-spacingLabelCutoff w) L
  simp only [← Nat.add_assoc, Nat.add_sub_of_le hN] at h
  exact Q'.le_trans' _ _ _ h (closedTail_small hw0 hw1 epsilon he _ hM)

/-- The existing explicit deficit cutoff is independent of this word/carrier. -/
def deficitInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (N : Nat) (hN : deficitCutoff w epsilon ≤ N) :
    Interval blocks (deficitPolynomial w N x) epsilon := by
  let J := bandSize w epsilon
  let delta := weightTolerance w epsilon
  have hd : (0 : Q') < delta := weightTolerance_positive w he
  have hJN : J ≤ N := Nat.le_trans (bandSize_le_deficitCutoff w epsilon) hN
  let head := weightedRangeInterval (heatTerm w x) (pointwiseHeatMajorant w) (deficit w N)
    (termInterval (Q'.le_of_lt hw0) P) (fun r => (deficit_bounds hw0 hw1 N r).1)
    J delta (fun r hr => Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (deficit_abs_small hw0 hw1 J hd N r hN hr))
  have hhead : delta * finSum (pointwiseHeatMajorant w) J ≤ HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (majorant_prefix_bound hw0 hw1 J) (Q'.le_of_lt hd)) (weightTolerance_budget hw0 he)
  let tail := weightedRangeInterval (fun r => heatTerm w x (J+r))
    (fun r => pointwiseHeatMajorant w (J+r)) (fun r => deficit w N (J+r))
    (fun r => termInterval (Q'.le_of_lt hw0) P (J+r))
    (fun r => (deficit_bounds hw0 hw1 N (J+r)).1) (N-J) 1
    (fun r _ => (deficit_bounds hw0 hw1 N (J+r)).2)
  have htail : (1 : Q') * finSum (fun r => pointwiseHeatMajorant w (J+r)) (N-J) ≤ HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (majorant_tail_small hw0 hw1 (HalfPow.half*epsilon) (ExpNeg.half_mul_pos _ he)
        (tailCutoff w (HalfPow.half*epsilon)) (N-J) (Nat.le_refl _))
  have hsplit := PolynomialWeightedSumBounds.sum_range_add
    (fun r => polySmul (deficit w N r) (heatTerm w x r)) J (N-J)
  rw [Nat.add_sub_of_le hJN] at hsplit
  unfold deficitPolynomial
  rw [hsplit]
  exact ((head.weaken hhead).add (tail.weaken htail)).changeCap (ExpNeg.two_halves epsilon)

/-- Jacobi's constant coefficient is a square-certificate floor for this word. -/
def weightedFloorCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {blocks : Nat} {p : PolyQuaternion} (hp : Supported blocks p)
    (hu : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) (N : Nat) (hN : 1 ≤ N) :
    Certificate blocks (polyAdd (weightedPolynomial w N p.scalar)
      (polyNeg (cap (SU2PointwiseHeatStrictFloor.floor w)))) :=
  .ofCoeff ((JacobiWeightedHeatPolynomial.shiftedHeat_subst_coeffEqv_weightedPolynomial
      hw0 hw1 N p.scalar).symm.add (RatPolyCoeffEqv.refl _))
    (QPolyHaarPositiveSubstitution.certificate_sub_constant (oneAddScalar_certificate hp hu)
      (JacobiShiftedPositiveCoefficients.heat w N)
      (JacobiShiftedPositiveCoefficients.heat_nonnegative hw0 hw1 N)
      (SU2PointwiseHeatStrictFloor.floor w)
      (JacobiShiftedPositiveCoefficients.floor_le_heat_constant hw0 hw1 N hN))

/-- SAME original unweighted prefix and SAME computed late-cutoff threshold. -/
def prefixFloorCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {blocks : Nat} {p : PolyQuaternion} (hp : Supported blocks p)
    (hu : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne)
    (K : Nat) (hK : headCutoff w ≤ K) :
    Certificate blocks (polyAdd (heatPrefix w K p.scalar) (polyNeg (cap (headFloor w)))) := by
  let H := cap (headFloor w)
  let W := weightedPolynomial w (K+1) p.scalar
  let D := deficitPolynomial w (K+1) p.scalar
  have hc : RatPolyCoeffEqv (polyAdd H H) (cap (SU2PointwiseHeatStrictFloor.floor w)) :=
    (cap_add _ _).trans (RatPolyCoeffEqv.smul_coefficient
      (ExpNeg.two_halves (SU2PointwiseHeatStrictFloor.floor w)) polyOne)
  let C : Certificate blocks (polyAdd W (polyNeg (polyAdd H H))) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hc))
      (weightedFloorCertificate hw0 hw1 hp hu (K+1) (Nat.succ_le_succ (Nat.zero_le _)))
  let R := deficitInterval hw0 hw1 (.scalar hp hu) (headFloor w) (headFloor_positive hw0 hw1)
    (K+1) (Nat.le_trans hK (Nat.le_succ K))
  exact .ofCoeff (((prefix_eq_weighted_add_deficit w K p.scalar).add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.add (.var 2) (.var 2)))) (.add (.var 2) (.var 1)))
      (by decide) (fun | 0 => W | 1 => D | _ => H))) (C.add R.lower)

def prefixCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {blocks : Nat} {p : PolyQuaternion} (hp : Supported blocks p)
    (hu : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne)
    (K : Nat) (hK : headCutoff w ≤ K) : Certificate blocks (heatPrefix w K p.scalar) :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
    (fun | 0 => heatPrefix w K p.scalar | _ => cap (headFloor w)))
    ((prefixFloorCertificate hw0 hw1 hp hu K hK).add
      (.constant _ (headFloor w) (Q'.le_of_lt (headFloor_positive hw0 hw1))))

end YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate

#print axioms YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate.heatTerm
#print axioms YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate.termInterval
#print axioms YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate.prefixInterval
#print axioms YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate.deficitPolynomial
#print axioms YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate.prefix_eq_weighted_add_deficit
#print axioms YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate.deficitInterval
#print axioms YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate.weightedFloorCertificate
#print axioms YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate
#print axioms YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate.prefixCertificate
