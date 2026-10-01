/-
# Tangent comparison on the original maximal physical graph

The constructed Cayley limit has a fourth-order squared tangent remainder on
the represented second core.  Subtracting two ACTUAL derivative-domain points
and applying the original graph displacement bound controls the difference
of their tangent errors by the squared distance of their graph OUTPUTS,
times the square of the rational parameter. No input approximation is
divided by the parameter.

This fixed-nome, fixed-width comparison does not calibrate lattice spacing
or identify a physical Hamiltonian mass.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDomainDisplacement
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInfinitesimal
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitLinear
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedNeg completedSmul completedZero)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedAdd_assoc completedNeg_add completedZero_add completedSmul_zero
    completedAdd_zero completedSmul_add)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_smul bondValue_sub bondValue_negate bondValue_realSmul)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (rationalCauchy completedRealSmul_ofQ')
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments
  (scale_add)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (cneg imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
  (add_assoc add_comm add_zero zero_add neg_add add_neg add_right_cancel
    normSq_imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq normSq_add_le fourCopies fourCopies_eq_scale_four)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (distance_eq_norm_difference)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitLinear
  (limitMap_add)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDomainDisplacement
  (limitMap_domain_distance_le_eight)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "S" => BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1
local notation "N" => normSq hw0 hw1
local notation "F" => limitMap hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "Neg" => cneg hw0 hw1
local notation "I" => imagScale hw0 hw1
local notation "Dist" => distance hw0 hw1
local notation "YType" =>
  CRealSeminormCompletion.SquaredSeminorm.Cauchy
    (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)) ×
  CRealSeminormCompletion.SquaredSeminorm.Cauchy
    (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width))

private theorem real_scale_add (t : Q')
    (x y : BF4WilsonAllNomeBondOSCompletion.BondCompletion
      hw0 hw1 (width := width)) :
    BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t
      (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x y) =
    BF4WilsonAllNomeBondOSLinear.add hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t x)
      (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact completedSmul_add hw0 hw1 t _ _

private theorem real_neg_additive
    (x y : BF4WilsonAllNomeBondOSCompletion.BondCompletion
      hw0 hw1 (width := width)) :
    BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x y) =
    BF4WilsonAllNomeBondOSLinear.add hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x)
      (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_add,bondValue_negate]
  exact completedSmul_add hw0 hw1 (-1) _ _

private theorem imag_add (t : Q') (x y : H) :
    I t (A x y) = A (I t x) (I t y) := by
  apply Prod.ext
  · exact (congrArg (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1)
      (real_scale_add hw0 hw1 t x.2 y.2)).trans
      (real_neg_additive hw0 hw1 _ _)
  · exact real_scale_add hw0 hw1 t x.1 y.1

private theorem cneg_smul (x : H) :
    Neg x = S (ofQ' (-1)) (ofQ' 0)
      (rationalCauchy (-1)) (rationalCauchy 0) x := by
  apply Prod.ext
  · apply bondValue_injective hw0 hw1
    simp only [cneg, BF4WilsonAllNomeComplexBondOSTime.smul,
      bondValue_negate,bondValue_sub,bondValue_realSmul,
      completedRealSmul_ofQ',completedSmul_zero]
    change completedNeg hw0 hw1 (bondValue hw0 hw1 x.1) =
      completedAdd hw0 hw1 (completedNeg hw0 hw1 (bondValue hw0 hw1 x.1))
        (completedNeg hw0 hw1 (completedZero hw0 hw1 width))
    have hz : completedNeg hw0 hw1 (completedZero hw0 hw1 width) =
        completedZero hw0 hw1 width := by
      have h := completedNeg_add hw0 hw1 (completedZero hw0 hw1 width)
      rw [completedAdd_zero] at h
      exact h
    rw [hz,completedAdd_zero]
  · apply bondValue_injective hw0 hw1
    simp only [cneg, BF4WilsonAllNomeComplexBondOSTime.smul,
      bondValue_negate,bondValue_add,bondValue_realSmul,
      completedRealSmul_ofQ',completedSmul_zero]
    exact (completedZero_add hw0 hw1 _).symm

private def negativeDomain (d : D) : D :=
  BF4WilsonAllNomeComplexBondOSDerivative.smul hw0 hw1
    (ofQ' (-1)) (ofQ' 0) (rationalCauchy (-1)) (rationalCauchy 0) d

private theorem negativeDomain_input (d : D) :
    In (negativeDomain hw0 hw1 d) = Neg (In d) := by
  rw [negativeDomain,BF4WilsonAllNomeComplexBondOSDerivative.smul_input]
  exact (cneg_smul hw0 hw1 (In d)).symm

private theorem negativeDomain_output (d : D) :
    Out (negativeDomain hw0 hw1 d) = Neg (Out d) := by
  rw [negativeDomain,BF4WilsonAllNomeComplexBondOSDerivative.smul_output]
  exact (cneg_smul hw0 hw1 (Out d)).symm

/-- Actual graph subtraction, formed within the original physical domain. -/
def graphDifference (d e : D) : D :=
  BF4WilsonAllNomeComplexBondOSDerivative.add hw0 hw1 d
    (negativeDomain hw0 hw1 e)

theorem graphDifference_input (d e : D) :
    In (graphDifference hw0 hw1 d e) = diff hw0 hw1 (In d) (In e) := by
  rw [graphDifference,BF4WilsonAllNomeComplexBondOSDerivative.add_input,
    negativeDomain_input]
  rfl

theorem graphDifference_output (d e : D) :
    Out (graphDifference hw0 hw1 d e) = diff hw0 hw1 (Out d) (Out e) := by
  rw [graphDifference,BF4WilsonAllNomeComplexBondOSDerivative.add_output,
    negativeDomain_output]
  rfl

private theorem add_exchange (a b c d : H) :
    A (A a b) (A c d) = A (A a c) (A b d) := by
  calc
    A (A a b) (A c d) = A a (A b (A c d)) := add_assoc hw0 hw1 a b (A c d)
    _ = A a (A c (A b d)) := by
      rw [← add_assoc hw0 hw1 b c d,add_comm hw0 hw1 b c,
        add_assoc hw0 hw1 c b d]
    _ = A (A a c) (A b d) := (add_assoc hw0 hw1 a c (A b d)).symm

private theorem neg_additive (x y : H) :
    Neg (A x y) = A (Neg x) (Neg y) := by
  apply add_right_cancel hw0 hw1 _ _ (A x y)
  have hzero : A (Neg x) x =
      A (A (Neg x) x) (A (Neg y) y) := by
    rw [neg_add,neg_add,add_zero]
  calc
    A (Neg (A x y)) (A x y) = A (Neg x) x := by
      rw [neg_add,neg_add]
    _ = A (A (Neg x) x) (A (Neg y) y) := hzero
    _ = A (A (Neg x) (Neg y)) (A x y) :=
      (add_exchange hw0 hw1 (Neg x) (Neg y) x y).symm

private theorem diff_add (a b c d : H) :
    diff hw0 hw1 (A a b) (A c d) =
      A (diff hw0 hw1 a c) (diff hw0 hw1 b d) := by
  unfold diff
  rw [neg_additive,add_exchange]

theorem graphDifference_reconstruct (d e : D) :
    BF4WilsonAllNomeComplexBondOSDerivative.add hw0 hw1
      (graphDifference hw0 hw1 d e) e = d := by
  apply BF4WilsonAllNomeComplexBondOSDerivative.input_injective
  rw [BF4WilsonAllNomeComplexBondOSDerivative.add_input,graphDifference_input]
  unfold diff
  rw [add_assoc,neg_add,add_zero]

/-- The exact factor-two imaginary phase is additive on the ACTUAL graph. -/
def tangentError (t : Q') (ht : (0 : Q') < t) (d : D) : H :=
  A (diff hw0 hw1 (F t ht (In d)) (In d))
    (I t (A (Out d) (Out d)))

theorem tangentError_add (t : Q') (ht : (0 : Q') < t) (d e : D) :
    tangentError hw0 hw1 t ht
      (BF4WilsonAllNomeComplexBondOSDerivative.add hw0 hw1 d e) =
      A (tangentError hw0 hw1 t ht d)
        (tangentError hw0 hw1 t ht e) := by
  unfold tangentError
  rw [BF4WilsonAllNomeComplexBondOSDerivative.add_input,
    BF4WilsonAllNomeComplexBondOSDerivative.add_output,
    limitMap_add, diff_add,
    add_exchange hw0 hw1 (Out d) (Out e) (Out d) (Out e),
    imag_add]
  exact add_exchange hw0 hw1
    (diff hw0 hw1 (F t ht (In d)) (In d))
    (diff hw0 hw1 (F t ht (In e)) (In e))
    (I t (A (Out d) (Out d))) (I t (A (Out e) (Out e)))

private def sumCeiling (a b : RC) : RC :=
  RCadd (RCadd a a) (RCadd b b)

private theorem add_norm_le (x y : H) (a b : RC)
    (hx : RCle (N x) a) (hy : RCle (N y) b) :
    RCle (N (A x y)) (sumCeiling a b) :=
  RCle_trans (normSq_add_le hw0 hw1 x y)
    (RCadd_le_add (RCadd_le_add hx hx) (RCadd_le_add hy hy))

private theorem twice_scale (c : Q') (a : RC) :
    RCadd (RCscale c a) (RCscale c a) = RCscale (2*c) a := by
  refine Quotient.inductionOn a ?_
  intro Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.const 2) (.var 0)) (.var 1))
      (by decide) (fun | 0 => c | _ => Z.approx n)))

private theorem sumCeiling_scales (c d : Q') (a b : RC) :
    sumCeiling (RCscale c a) (RCscale d b) =
      RCadd (RCscale (2*c) a) (RCscale (2*d) b) := by
  unfold sumCeiling
  rw [twice_scale,twice_scale]

private theorem square_nonnegative (t : Q') (ht : (0 : Q') < t) :
    (0 : Q') ≤ t*t := Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht)

private theorem phase_norm_le (t : Q') (ht : (0 : Q') < t) (z : H) :
    RCle (N (I t (A z z))) (RCscale (4*(t*t)) (N z)) := by
  have hdouble := normSq_add_le hw0 hw1 z z
  change RCle (N (A z z)) (fourCopies (N z)) at hdouble
  rw [fourCopies_eq_scale_four] at hdouble
  have hscaled := RCscale_mono (square_nonnegative t ht) hdouble
  rw [RCscale_RCscale] at hscaled
  have hcoef : Q'.eqv ((t*t)*4) (4*(t*t)) :=
    Q'.mul_comm_eqv _ _
  rw [normSq_imagScale]
  rw [YMGap.Continuum.RCSignedPairBudget.scale_congr hcoef] at hscaled
  exact hscaled

private theorem tangentError_graph_bound (t : Q') (ht : (0 : Q') < t)
    (d : D) :
    RCle (N (tangentError hw0 hw1 t ht d))
      (RCscale (24*(t*t)) (N (Out d))) := by
  have hdisp := limitMap_domain_distance_le_eight hw0 hw1 t ht d
  rw [distance_eq_norm_difference] at hdisp
  have hphase := phase_norm_le hw0 hw1 t ht (Out d)
  have h := add_norm_le hw0 hw1
    (diff hw0 hw1 (F t ht (In d)) (In d))
    (I t (A (Out d) (Out d)))
    (RCscale (8*(t*t)) (N (Out d)))
    (RCscale (4*(t*t)) (N (Out d))) hdisp hphase
  change RCle (N (tangentError hw0 hw1 t ht d)) _ at h
  rw [sumCeiling_scales] at h
  rw [← scale_add] at h
  have hcoef : Q'.eqv ((2*(8*(t*t)))+(2*(4*(t*t)))) (24*(t*t)) :=
    poly_identity_of_normal_eq
      (.add
        (.mul (.const 2) (.mul (.const 8) (.mul (.var 0) (.var 0))))
        (.mul (.const 2) (.mul (.const 4) (.mul (.var 0) (.var 0)))))
      (.mul (.const 24) (.mul (.var 0) (.var 0)))
      (by decide) (fun _ => t)
  rw [YMGap.Continuum.RCSignedPairBudget.scale_congr hcoef] at h
  exact h

/-- Actual maximal-domain tangent error compared with an actual represented
second-core point. The only proximity cost is the ORIGINAL output distance. -/
theorem graph_tangent_comparison (t : Q') (ht : (0 : Q') < t)
    (d : D) (Y : YType) :
    let d₀ := BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y
    let e₀ := BF4WilsonAllNomeComplexBondOSSecondCore.second hw0 hw1 Y
    RCle (N (tangentError hw0 hw1 t ht d))
      (RCadd
        (RCscale (736*((t*t)*(t*t))) (N (Out e₀)))
        (RCscale (48*(t*t)) (Dist (Out d) (Out d₀)))) := by
  dsimp only
  let d₀ := BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y
  let e₀ := BF4WilsonAllNomeComplexBondOSSecondCore.second hw0 hw1 Y
  let hDiff := graphDifference hw0 hw1 d d₀
  have hreconstruct : BF4WilsonAllNomeComplexBondOSDerivative.add hw0 hw1 hDiff d₀ = d :=
    graphDifference_reconstruct hw0 hw1 d d₀
  have hsplit : tangentError hw0 hw1 t ht d =
      A (tangentError hw0 hw1 t ht d₀) (tangentError hw0 hw1 t ht hDiff) := by
    rw [← hreconstruct]
    exact (tangentError_add hw0 hw1 t ht hDiff d₀).trans
      (add_comm hw0 hw1 _ _)
  have hcore := BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInfinitesimal.limitMap_secondCore_tangent
    hw0 hw1 Y t ht
  change RCle (N (tangentError hw0 hw1 t ht d₀))
    (RCscale (368*((t*t)*(t*t))) (N (Out e₀))) at hcore
  have hnear := tangentError_graph_bound hw0 hw1 t ht hDiff
  have hbudget := add_norm_le hw0 hw1
    (tangentError hw0 hw1 t ht d₀) (tangentError hw0 hw1 t ht hDiff)
    (RCscale (368*((t*t)*(t*t))) (N (Out e₀)))
    (RCscale (24*(t*t)) (N (Out hDiff))) hcore hnear
  rw [← hsplit,sumCeiling_scales] at hbudget
  dsimp only [hDiff] at hbudget
  rw [graphDifference_output,← distance_eq_norm_difference] at hbudget
  have hleft : Q'.eqv (2*(24*(t*t))) (48*(t*t)) :=
    poly_identity_of_normal_eq
      (.mul (.const 2) (.mul (.const 24) (.mul (.var 0) (.var 0))))
      (.mul (.const 48) (.mul (.var 0) (.var 0)))
      (by decide) (fun _ => t)
  have hright : Q'.eqv (2*(368*((t*t)*(t*t))))
      (736*((t*t)*(t*t))) :=
    poly_identity_of_normal_eq
      (.mul (.const 2) (.mul (.const 368)
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))))
      (.mul (.const 736)
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))))
      (by decide) (fun _ => t)
  rw [YMGap.Continuum.RCSignedPairBudget.scale_congr hleft,
    YMGap.Continuum.RCSignedPairBudget.scale_congr hright] at hbudget
  exact hbudget

#print axioms graphDifference
#print axioms graphDifference_input
#print axioms graphDifference_output
#print axioms graphDifference_reconstruct
#print axioms tangentError
#print axioms tangentError_add
#print axioms graph_tangent_comparison

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison
