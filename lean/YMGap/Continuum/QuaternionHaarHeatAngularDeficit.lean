/-
# Angular Jacobi-weight deficit for the original SU(2) heat polynomial

The literal differentiated deficit is split into a finite label band and a
quartic high-spin tail.  Jacobi-weight convergence pays the finite band, while
the explicit quartic-tail modulus pays the remainder.  The resulting cutoff
depends only on the nome, derivative cap, and requested tolerance, not on the
carrier, coordinates, or substituted quaternion polynomial.

This is finite original-polynomial weight removal.  It does not assert a
continuum derivative or an interacting-action estimate.
-/

import YMGap.Continuum.QuaternionHaarHeatAngularDerivative
import YMGap.Continuum.SU2HeatQuarticTailCutoff
import YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval

namespace YMGap.Continuum.QuaternionHaarHeatAngularDeficit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval
  (deficit deficit_bounds deficit_abs_small)
open YMGap.Continuum.FiniteJacobiWeightConvergence (centeredCutoff)
open YMGap.Continuum.PolynomialWeightedSumBounds (sum_range_add)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
  (heatTerm deficitPolynomial)
open YMGap.Continuum.QuaternionHaarHeatAngularDerivative
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.SU2HeatQuarticPrefixBound
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

/-- Tolerance assigned to the quartic derivative tail. -/
def tailTolerance (d epsilon : Q') : Q' :=
  HKConv.divPos (HalfPow.half * epsilon) (2 * d + 1)

/-- Tolerance assigned to convergence of the finite Jacobi-weight band. -/
def headTolerance (w d epsilon : Q') : Q' :=
  HKConv.divPos (HalfPow.half * epsilon) (heatDerivativeCap w d + 1)

/-- The finite band extends one label beyond the explicit quartic-tail cutoff. -/
def bandSize (w d epsilon : Q') : Nat :=
  SU2HeatQuarticTailCutoff.tailCutoff w (tailTolerance d epsilon) + 1

/-- Computable Jacobi cutoff for the differentiated deficit. -/
def deficitCutoff (w d epsilon : Q') : Nat :=
  centeredCutoff (w * w) (bandSize w d epsilon) (headTolerance w d epsilon)

theorem tailTolerance_positive (d : Q') {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < tailTolerance d epsilon :=
  HKConv.divPos_pos (CReal.num_pos_of_pos (ExpNeg.half_mul_pos _ hepsilon))

theorem headTolerance_positive (w d : Q') {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < headTolerance w d epsilon :=
  HKConv.divPos_pos (CReal.num_pos_of_pos (ExpNeg.half_mul_pos _ hepsilon))

private theorem scaledTolerance_budget (a epsilon : Q')
    (ha : (0 : Q') ≤ a) (hepsilon : (0 : Q') < epsilon) :
    a * HKConv.divPos (HalfPow.half * epsilon) (a + 1) ≤ HalfPow.half * epsilon := by
  have hd : (0 : Q') < HKConv.divPos (HalfPow.half * epsilon) (a + 1) :=
    HKConv.divPos_pos (CReal.num_pos_of_pos (ExpNeg.half_mul_pos _ hepsilon))
  have hp : (0 : Q') < a + 1 := Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ ha)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  have hle : a * HKConv.divPos (HalfPow.half * epsilon) (a + 1) ≤
      (a + 1) * HKConv.divPos (HalfPow.half * epsilon) (a + 1) :=
    Q'.mul_le_mul_of_nonneg_right a (a + 1)
      (HKConv.divPos (HalfPow.half * epsilon) (a + 1))
      (Q'.add_le_self_of_nonneg a 1 Q'.zero_le_one) (Q'.le_of_lt hd)
  have heq : (a + 1) * HKConv.divPos (HalfPow.half * epsilon) (a + 1) ≈
      HalfPow.half * epsilon :=
    Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (a + 1) (HKConv.divPos (HalfPow.half * epsilon) (a + 1)))
      (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hp))
  exact Q'.le_trans' _ _ _ hle (Q'.le_of_eqv heq)

theorem bandSize_le_deficitCutoff (w d epsilon : Q') :
    bandSize w d epsilon ≤ deficitCutoff w d epsilon :=
  Nat.le_add_right _ _

private def weightedRangeInterval {blocks : Nat} (f : Nat → RatPoly) (c a : Nat → Q')
    (hI : ∀ r, Interval blocks (f r) (c r)) (ha : ∀ r, (0 : Q') ≤ a r)
    (N : Nat) (A : Q') (hA : ∀ r, r < N → a r ≤ A) :
    Interval blocks (finitePolySum (fun r => polySmul (a r) (f r)) (List.range N))
      (A * finSum c N) :=
  (Interval.finiteRange _ _ (fun r => (hI r).smul (a r) (ha r)) N).weaken
    (Q'.le_trans' _ _ _ (finSum_le_lt _ _ N (fun r hr =>
      Q'.mul_le_mul_of_nonneg_right _ _ _ (hA r hr) (hI r).nonnegative))
      (Q'.ge_of_eqv (const_mul_finSum c A N)))

private theorem finitePolySum_coeff_congr {A : Type} (f g : A → RatPoly)
    (h : ∀ a, RatPolyCoeffEqv (f a) (g a)) : ∀ xs : List A,
    RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => (h a).add (finitePolySum_coeff_congr f g h xs)

private theorem finitePolySum_supported {A : Type} {blocks : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) : ∀ xs : List A,
    SupportedQuaternionBlocks blocks (finitePolySum f xs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | a :: xs => polyAdd_supported (h a) (finitePolySum_supported f h xs)

private theorem derivative_prefix_bound {w d : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hd : (0 : Q') ≤ d) (J : Nat) :
    finSum (fun r => (2 * d) * tailTerm w 4 r) J ≤ heatDerivativeCap w d := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (const_mul_finSum (tailTerm w 4) (2 * d) J)))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (prefix_bound hw0 hw1 J)
      (Q'.mul_nonneg _ _ (by decide) hd))

private theorem derivative_tail_bound {w d epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hd : (0 : Q') ≤ d)
    (hepsilon : (0 : Q') < epsilon) (J L : Nat)
    (hJ : SU2HeatQuarticTailCutoff.tailCutoff w (tailTolerance d epsilon) ≤ J) :
    finSum (fun r => (2 * d) * tailTerm w 4 (J + r)) L ≤ HalfPow.half * epsilon := by
  have htail := SU2HeatQuarticTailCutoff.finite_shifted_tail_le hw0 hw1
    (tailTolerance_positive d hepsilon) J L hJ
  have hscaled : (2 * d) * finSum (fun r => tailTerm w 4 (J + r)) L ≤
      (2 * d) * tailTolerance d epsilon :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ htail
      (Q'.mul_nonneg _ _ (by decide) hd)
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm
        (const_mul_finSum (fun r => tailTerm w 4 (J + r)) (2 * d) L))) hscaled)
    (scaledTolerance_budget (2 * d) epsilon
      (Q'.mul_nonneg _ _ (by decide) hd) hepsilon)

/-- The differentiated literal Jacobi deficit has the requested two-sided
Haar interval after the explicit cutoff. -/
def angularDeficitInterval {blocks i j : Nat} {x : RatPoly} {w d epsilon : Q'}
    (hi : i < 4 * blocks) (hj : j < 4 * blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (X : SquareBound blocks x 1)
    (DX : Interval blocks (angularDerivative i j x) d)
    (hepsilon : (0 : Q') < epsilon) (N : Nat)
    (hN : deficitCutoff w d epsilon ≤ N) :
    Interval blocks (angularDerivative i j (deficitPolynomial w N x)) epsilon := by
  let J := bandSize w d epsilon
  let delta := headTolerance w d epsilon
  have hdelta : (0 : Q') < delta := headTolerance_positive w d hepsilon
  have hJN : J ≤ N := Nat.le_trans (bandSize_le_deficitCutoff w d epsilon) hN
  let derivativeTerm := fun r => angularDerivative i j (heatTerm w x r)
  let derivativeCap := fun r => (2 * d) * tailTerm w 4 r
  have hterm : ∀ r, Interval blocks (derivativeTerm r) (derivativeCap r) :=
    fun r => heatDerivativeTermIntervalAt hi hj (Q'.le_of_lt hw0) X DX r
  let head := weightedRangeInterval derivativeTerm derivativeCap (deficit w N)
    hterm (fun r => (deficit_bounds hw0 hw1 N r).1) J delta
    (fun r hr => Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (deficit_abs_small hw0 hw1 J hdelta N r hN hr))
  have hhead : delta * finSum derivativeCap J ≤ HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (derivative_prefix_bound hw0 hw1 DX.nonnegative J) (Q'.le_of_lt hdelta))
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_comm_eqv delta (heatDerivativeCap w d)))
        (scaledTolerance_budget (heatDerivativeCap w d) epsilon
          (Q'.mul_nonneg _ _
            (Q'.mul_nonneg _ _ (by decide) DX.nonnegative)
            (prefixBudget_nonnegative hw0)) hepsilon))
  let tail := weightedRangeInterval (fun r => derivativeTerm (J + r))
    (fun r => derivativeCap (J + r)) (fun r => deficit w N (J + r))
    (fun r => hterm (J + r)) (fun r => (deficit_bounds hw0 hw1 N (J + r)).1)
    (N - J) 1 (fun r _ => (deficit_bounds hw0 hw1 N (J + r)).2)
  have htail : (1 : Q') * finSum (fun r => derivativeCap (J + r)) (N - J) ≤
      HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (derivative_tail_bound hw0 hw1 DX.nonnegative hepsilon J (N - J)
        (by unfold J bandSize; omega))
  have hsplit := sum_range_add
    (fun r => polySmul (deficit w N r) (derivativeTerm r)) J (N - J)
  rw [Nat.add_sub_of_le hJN] at hsplit
  have hp : SupportedQuaternionBlocks blocks (deficitPolynomial w N x) := by
    unfold deficitPolynomial
    exact finitePolySum_supported _
      (fun r => polySmul_supported
        (QuaternionHaarAllNomeHeatCertificate.termInterval (Q'.le_of_lt hw0) X r).support _)
      (List.range N)
  have hdiff := angularDerivative_finitePolySum i j
    (fun r => polySmul (deficit w N r) (heatTerm w x r)) (List.range N)
  have hsmul := finitePolySum_coeff_congr
    (fun r => angularDerivative i j (polySmul (deficit w N r) (heatTerm w x r)))
    (fun r => polySmul (deficit w N r) (derivativeTerm r))
    (fun r => angularDerivative_smul i j (deficit w N r) (heatTerm w x r))
    (List.range N)
  have total : Interval blocks
      (finitePolySum (fun r => polySmul (deficit w N r) (derivativeTerm r)) (List.range N)) epsilon := by
    rw [hsplit]
    exact ((head.weaken hhead).add (tail.weaken htail)).changeCap (ExpNeg.two_halves epsilon)
  exact Interval.ofCoeff (angularDerivative_supported_at hi hj hp) (hdiff.trans hsmul) total

end YMGap.Continuum.QuaternionHaarHeatAngularDeficit

#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDeficit.tailTolerance
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDeficit.headTolerance
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDeficit.bandSize
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDeficit.deficitCutoff
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDeficit.tailTolerance_positive
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDeficit.headTolerance_positive
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDeficit.bandSize_le_deficitCutoff
#print axioms YMGap.Continuum.QuaternionHaarHeatAngularDeficit.angularDeficitInterval
