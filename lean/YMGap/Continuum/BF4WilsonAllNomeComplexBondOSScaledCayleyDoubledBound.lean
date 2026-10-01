/-
# Fourth-order doubled-step error on the original physical Cayley graph

The exact four-error identity is consumed on two linked, actual original
graph points. Cayley graph preservation and unitarity keep the second-output
norm unchanged. The squared triangle gives an explicit rational ceiling
352*h^4, without an A^3 point, an analytic hypothesis or a spectral theorem.

The represented second core retains its ORIGINAL Cauchy preimage norm.
This local refinement is not yet a product Cauchy proof or a physical-time
identification, and proves no continuum mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (cneg imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq normSq_add_le linked_error_norm_le_four preimageNorm)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
  (normSq_neg normSq_imagScale cayley_domain_difference_norm_le_four)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation
  (graphMap graphMap_input graphMap_output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff graphError doubled_error_identity)

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

private theorem cayley_norm (t : Q') (ht : (0 : Q') < t) (x : H) :
    N (C t ht x) = N x :=
  congrArg Prod.fst
    (BF4WilsonAllNomeComplexBondOSScaledCayley.pairing_preserved hw0 hw1 t ht x x)

private theorem doubled_fourth (h : Q') :
    Q'.eqv ((4 : Q')*(((2*h)*(2*h))*((2*h)*(2*h))))
      ((64 : Q')*((h*h)*(h*h))) :=
  poly_identity_of_normal_eq
    (.mul (.const 4)
      (.mul (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
        (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))))
    (.mul (.const 64) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))))
    (by decide) (fun _ => h)

private theorem doubled_first (h : Q') :
    Q'.eqv (((2*h)*(2*h))*((4 : Q')*(h*h)))
      ((16 : Q')*((h*h)*(h*h))) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
      (.mul (.const 4) (.mul (.var 0) (.var 0))))
    (.mul (.const 16) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))))
    (by decide) (fun _ => h)

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

private theorem total_ceiling (p : Q') (z : RC) :
    sumCeiling
      (sumCeiling (sumCeiling (RCscale (4*p) z) (RCscale (4*p) z))
        (RCscale (64*p) z)) (RCscale (16*p) z) = RCscale (352*p) z := by
  rw [sumCeiling_scales,sumCeiling_scales,sumCeiling_scales]
  exact scale_congr (poly_identity_of_normal_eq
    (.add
      (.mul (.const 2)
        (.add
          (.mul (.const 2)
            (.add (.mul (.const 2) (.mul (.const 4) (.var 0)))
              (.mul (.const 2) (.mul (.const 4) (.var 0)))))
          (.mul (.const 2) (.mul (.const 64) (.var 0)))))
      (.mul (.const 2) (.mul (.const 16) (.var 0))))
    (.mul (.const 352) (.var 0)) (by decide) (fun _ => p)) z

private theorem graphError_norm_le (t : Q') (ht : (0 : Q') < t)
    (d e : D) (hlink : Out d = In e) :
    RCle (N (graphError hw0 hw1 t ht d))
      (RCscale ((4 : Q')*((t*t)*(t*t))) (N (Out e))) :=
  linked_error_norm_le_four hw0 hw1 t ht d e hlink

/-- The actual doubled-step error is fourth order in squared norm.
The two linked original domain points are data, not assumed A^3 regularity. -/
theorem doubled_error_norm_le (h : Q') (hh : (0 : Q') < h)
    (h2 : (0 : Q') < 2*h) (d e : D) (hlink : Out d = In e) :
    RCle (N (diff hw0 hw1 (C h hh (C h hh (In d))) (C (2*h) h2 (In d))))
      (RCscale ((352 : Q')*((h*h)*(h*h))) (N (Out e))) := by
  let dh := graphMap hw0 hw1 h hh d
  let eh := graphMap hw0 hw1 h hh e
  let a := graphError hw0 hw1 h hh dh
  let b := graphError hw0 hw1 h hh d
  let c := cneg hw0 hw1 (graphError hw0 hw1 (2*h) h2 d)
  let v := imagScale hw0 hw1 (2*h) (diff hw0 hw1 (Out d) (C h hh (Out d)))
  let p := (h*h)*(h*h)
  let z := N (Out e)
  have hmap : Out dh = In eh := by
    dsimp only [dh,eh]
    rw [graphMap_output,graphMap_input,hlink]
  have ha : RCle (N a) (RCscale (4*p) z) := by
    have ht := graphError_norm_le hw0 hw1 h hh dh eh hmap
    dsimp only [eh] at ht
    rw [graphMap_output,cayley_norm] at ht
    exact ht
  have hb : RCle (N b) (RCscale (4*p) z) :=
    graphError_norm_le hw0 hw1 h hh d e hlink
  have hc : RCle (N c) (RCscale (64*p) z) := by
    have ht := graphError_norm_le hw0 hw1 (2*h) h2 d e hlink
    rw [scale_congr (doubled_fourth h)] at ht
    change RCle (N (cneg hw0 hw1 (graphError hw0 hw1 (2*h) h2 d))) _
    rw [normSq_neg]
    exact ht
  have hv : RCle (N v) (RCscale (16*p) z) := by
    have ht := cayley_domain_difference_norm_le_four hw0 hw1 h hh e
    have hs : (0 : Q') ≤ (2*h)*(2*h) :=
      Q'.mul_nonneg _ _ (Q'.le_of_lt h2) (Q'.le_of_lt h2)
    have hscaled := RCscale_mono hs ht
    rw [RCscale_RCscale,scale_congr (doubled_first h)] at hscaled
    change RCle (N (imagScale hw0 hw1 (2*h)
      (diff hw0 hw1 (Out d) (C h hh (Out d))))) _
    rw [normSq_imagScale,hlink]
    exact hscaled
  have hab := add_norm_le_of_bounds hw0 hw1 a b _ _ ha hb
  have habc := add_norm_le_of_bounds hw0 hw1 (A a b) c _ _ hab hc
  have habcv := add_norm_le_of_bounds hw0 hw1 (A (A a b) c) v _ _ habc hv
  rw [total_ceiling] at habcv
  rw [doubled_error_identity]
  exact habcv

/-- The represented-core doubled-step ceiling retains the original input
representatives, not the norm of a smoothed physical input. -/
theorem secondCore_doubled_error_norm_le (h : Q') (hh : (0 : Q') < h)
    (h2 : (0 : Q') < 2*h)
    (Y : (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy ×
      (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy) :
    RCle
      (N (diff hw0 hw1
        (C h hh (C h hh (In (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y))))
        (C (2*h) h2 (In (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y)))))
      (RCscale ((352 : Q')*((h*h)*(h*h))) (preimageNorm hw0 hw1 Y)) := by
  have hlocal := doubled_error_norm_le hw0 hw1 h hh h2
    (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y)
    (BF4WilsonAllNomeComplexBondOSSecondCore.second hw0 hw1 Y)
    (BF4WilsonAllNomeComplexBondOSSecondCore.first_output_eq_second_input hw0 hw1 Y)
  have hsource := BF4WilsonAllNomeComplexBondOSSecondCore.second_output_norm_le hw0 hw1 Y
  have hs : (0 : Q') ≤ (h*h)*(h*h) := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.le_of_lt hh) (Q'.le_of_lt hh))
    (Q'.mul_nonneg _ _ (Q'.le_of_lt hh) (Q'.le_of_lt hh))
  exact RCle_trans hlocal (RCscale_mono
    (Q'.mul_nonneg _ _ (by decide) hs) hsource)

#print axioms doubled_error_norm_le
#print axioms secondCore_doubled_error_norm_le

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledBound
