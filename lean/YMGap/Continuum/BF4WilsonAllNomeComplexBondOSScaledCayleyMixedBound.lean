/-
# Fourth-degree mixed Cayley defect on the original linked graph

The exact mixed defect is bounded against the second output of two linked
points of the SAME physical Wilson-bond derivative graph.  The explicit
coefficient is homogeneous of degree four in the two positive rational
parameters.  No third-domain witness, full product law, physical time or
continuum statement is inferred.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedIdentity

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (cneg imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff graphError)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation
  (graphMap graphMap_input graphMap_output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq normSq_add_le fourCopies fourCopies_eq_scale_four linked_error_norm_le_four)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
  (normSq_neg normSq_imagScale cayley_domain_difference_norm_le_four)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedIdentity
  (mixed_error_identity)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "N" => normSq hw0 hw1

private def sumCeiling (a b : RC) : RC := RCadd (RCadd a a) (RCadd b b)

private theorem add_norm_le_of_bounds (x y : H) (a b : RC)
    (hx : RCle (N x) a) (hy : RCle (N y) b) :
    RCle (N (A x y)) (sumCeiling a b) :=
  RCle_trans (normSq_add_le hw0 hw1 x y)
    (RCadd_le_add (RCadd_le_add hx hx) (RCadd_le_add hy hy))

private theorem sumCeiling_scales (s t : Q') (z : RC) :
    sumCeiling (RCscale s z) (RCscale t z) = RCscale (2*s+2*t) z := by
  refine Quotient.inductionOn z ?_
  intro Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2)))
        (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (.mul (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1))) (.var 2))
      (by decide) (fun | 0 => s | 1 => t | _ => Z.approx n)))

private theorem cayley_norm (t : Q') (ht : (0 : Q') < t) (x : H) :
    N (C t ht x) = N x :=
  congrArg Prod.fst
    (BF4WilsonAllNomeComplexBondOSScaledCayley.pairing_preserved
      hw0 hw1 t ht x x)

private theorem graphError_norm_le (t : Q') (ht : (0 : Q') < t)
    (d e : D) (hlink : Out d = In e) :
    RCle (N (graphError hw0 hw1 t ht d))
      (RCscale ((4 : Q')*((t*t)*(t*t))) (N (Out e))) :=
  linked_error_norm_le_four hw0 hw1 t ht d e hlink

private theorem correction_norm_le (a b : Q') (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) (e : D) :
    RCle (N (imagScale hw0 hw1 b
      (A (diff hw0 hw1 (In e) (C a ha (In e)))
         (diff hw0 hw1 (In e) (C a ha (In e))))))
      (RCscale (((b*b)*4)*(4*(a*a))) (N (Out e))) := by
  let delta := diff hw0 hw1 (In e) (C a ha (In e))
  have hdelta := cayley_domain_difference_norm_le_four hw0 hw1 a ha e
  change RCle (N delta) (RCscale (4*(a*a)) (N (Out e))) at hdelta
  have hsum := normSq_add_le hw0 hw1 delta delta
  change RCle (N (A delta delta)) (fourCopies (N delta)) at hsum
  rw [fourCopies_eq_scale_four] at hsum
  have hb2 : (0 : Q') ≤ b*b :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hb) (Q'.le_of_lt hb)
  have hfirst := RCscale_mono hb2 hsum
  rw [RCscale_RCscale] at hfirst
  have hnonneg : (0 : Q') ≤ (b*b)*4 :=
    Q'.mul_nonneg _ _ hb2 (by decide)
  have hsecond := RCscale_mono hnonneg hdelta
  rw [RCscale_RCscale] at hsecond
  change RCle (N (imagScale hw0 hw1 b (A delta delta))) _
  rw [normSq_imagScale]
  exact RCle_trans hfirst hsecond

/-- An explicit homogeneous degree-four local budget.  This nested form
records the three squared-triangle applications without a scalar rounding. -/
def mixedCoefficient (a b : Q') : Q' :=
  let a4 := (a*a)*(a*a)
  let b4 := (b*b)*(b*b)
  let c4 := ((a+b)*(a+b))*((a+b)*(a+b))
  let cross := ((b*b)*4)*(4*(a*a))
  2*(2*(2*(4*b4)+2*(4*a4))+2*(4*c4))+2*cross

private theorem total_ceiling (a b : Q') (z : RC) :
    sumCeiling
      (sumCeiling
        (sumCeiling
          (RCscale (4*((b*b)*(b*b))) z)
          (RCscale (4*((a*a)*(a*a))) z))
        (RCscale (4*(((a+b)*(a+b))*((a+b)*(a+b)))) z))
      (RCscale (((b*b)*4)*(4*(a*a))) z) =
    RCscale (mixedCoefficient a b) z := by
  rw [sumCeiling_scales,sumCeiling_scales,sumCeiling_scales]
  rfl

/-- The genuine mixed-step squared defect of the original Cayley family.
The second-output norm is from the supplied linked actual graph point. -/
theorem mixed_error_norm_le (a b : Q') (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) (hc : (0 : Q') < a+b)
    (d e : D) (hlink : Out d = In e) :
    RCle
      (N (diff hw0 hw1 (C b hb (C a ha (In d))) (C (a+b) hc (In d))))
      (RCscale (mixedCoefficient a b) (N (Out e))) := by
  let da := graphMap hw0 hw1 a ha d
  let ea := graphMap hw0 hw1 a ha e
  let u := graphError hw0 hw1 b hb da
  let v := graphError hw0 hw1 a ha d
  let j := cneg hw0 hw1 (graphError hw0 hw1 (a+b) hc d)
  let delta := diff hw0 hw1 (Out d) (C a ha (Out d))
  let k := imagScale hw0 hw1 b (A delta delta)
  let z := N (Out e)
  have hmap : Out da = In ea := by
    dsimp only [da,ea]
    rw [graphMap_output,graphMap_input,hlink]
  have hu : RCle (N u) (RCscale (4*((b*b)*(b*b))) z) := by
    have h := graphError_norm_le hw0 hw1 b hb da ea hmap
    dsimp only [ea] at h
    rw [graphMap_output,cayley_norm] at h
    exact h
  have hv : RCle (N v) (RCscale (4*((a*a)*(a*a))) z) :=
    graphError_norm_le hw0 hw1 a ha d e hlink
  have hj : RCle (N j)
      (RCscale (4*(((a+b)*(a+b))*((a+b)*(a+b)))) z) := by
    have h := graphError_norm_le hw0 hw1 (a+b) hc d e hlink
    change RCle (N (graphError hw0 hw1 (a+b) hc d)) _ at h
    rw [normSq_neg]
    exact h
  have hk : RCle (N k) (RCscale (((b*b)*4)*(4*(a*a))) z) := by
    have h := correction_norm_le hw0 hw1 a b ha hb e
    change RCle (N (imagScale hw0 hw1 b
      (A (diff hw0 hw1 (In e) (C a ha (In e)))
        (diff hw0 hw1 (In e) (C a ha (In e)))))) _ at h
    rw [← hlink] at h
    exact h
  have huv := add_norm_le_of_bounds hw0 hw1 u v _ _ hu hv
  have huvj := add_norm_le_of_bounds hw0 hw1 (A u v) j _ _ huv hj
  have huvaj := add_norm_le_of_bounds hw0 hw1 (A (A u v) j) k _ _ huvj hk
  rw [total_ceiling] at huvaj
  rw [mixed_error_identity]
  exact huvaj

#print axioms mixedCoefficient
#print axioms mixed_error_norm_le

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedBound
