/-
# Lower log-Hessian of the actual finite normalized Jacobi heat

On x >= 0 the actual logarithmic product terms satisfy 0 <= r_i <= 1
and r_i <= 2*w^(2*i+1). Thus M2 <= M1 <= transverseCap, uniformly in
the finite prefix, including zero. The exact formal heat jets reduce the
cleared lower log-Hessian to a sum paid by this ceiling and finite variance.

This is the LOWER scalar half, on the nonnegative half-line (hence also
0 <= x <= 1). No heat value or moment is inverted. The polynomial is the
existing inverse-nome/half-normalized Jacobi heat, not an original character
cutoff. No intrinsic angular/Haar certificate, paired-generator identity,
interacting normalization, continuum estimate or physical gap is asserted.
The same finite moments also bound its first derivative by transverseCap
times the heat itself, including the zero and constant prefixes.
-/

import YMGap.Continuum.JacobiHeatRadialMomentJets

namespace YMGap.Continuum.JacobiHeatNearFlatLogHessian

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative (pderiv)
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.JacobiShiftedPositiveCoefficients (heat)
open YMGap.Continuum.JacobiHeatRadialMixtureCancellation
open YMGap.Continuum.JacobiHeatRadialMomentJets
open YMGap.Continuum.JacobiHeatTransverseCurvature

local infix:50 " ≈ " => Q'.eqv

private theorem add_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) : a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a b c h) (Q'.add_eqv_congr_left b c d g)

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a b c h) (Q'.mul_eqv_congr_left b c d g)

private theorem nonneg_of_eqv {p q : Q'} (h : p ≈ q) (hq : (0 : Q') ≤ q) :
    (0 : Q') ≤ p :=
  Q'.le_trans' _ _ _ hq (Q'.ge_of_eqv h)

private theorem sum_mono (f g : Nat → Q') (h : ∀ i, f i ≤ g i) :
    ∀ N, finSum f N ≤ finSum g N
  | 0 => Q'.le_refl' 0
  | N+1 => Q'.add_le_add (sum_mono f g h N) (h N)

private theorem factor_ge_one {c x : Q'} (hc : (0 : Q') ≤ c)
    (hx : (0 : Q') ≤ x) : (1 : Q') ≤ HKPos.factor c x :=
  Q'.add_le_self_of_nonneg 1 _ (Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (HKPos.two_nonneg hc) hx) (SumOfSquares.q_mul_self_nonneg c))

private theorem factor_ge_two {c x : Q'} (hc : (0 : Q') ≤ c)
    (hx : (0 : Q') ≤ x) : HKPos.two c ≤ HKPos.factor c x := by
  have hpin : HKPos.factor c x ≈ HKPos.two c +
      ((1 + -c)*(1 + -c) + HKPos.two c*x) :=
    poly_identity_of_normal_eq
      (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.var 1))
        (.mul (.var 0) (.var 0))))
      (.add (.add (.var 0) (.var 0))
        (.add (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))
          (.mul (.add (.var 0) (.var 0)) (.var 1))))
      (by decide) (fun | 0 => c | _ => x)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (Q'.zero_le_add _ _
      (SumOfSquares.q_mul_self_nonneg (1 + -c))
      (Q'.mul_nonneg _ _ (HKPos.two_nonneg hc) hx))) (Q'.ge_of_eqv hpin)

/-- Every actual logarithmic product summand is at most one on x >= 0. -/
theorem sTerm_le_one {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx0 : (0 : Q') ≤ x) (i : Nat) :
    HKConv.sTerm w x i ≤ (1 : Q') := by
  have hx : (-1 : Q') ≤ x := Q'.le_trans' _ _ _ (by decide) hx0
  have hc := Q'.le_of_lt (HKPos.pow_succ_pos_lt_one hw0 hw1 (2*i)).1
  apply HKConv.divPos_le_of_le (HKConv.factor_num_pos hw0 hw1 hx i)
  exact Q'.le_trans' _ _ _ (factor_ge_two hc hx0)
    (Q'.ge_of_eqv (Q'.one_mul_eqv _))

/-- The actual summand is bounded by its geometric transverse rate;
the denominator floor used here is one, not a weak-nome heat floor. -/
theorem sTerm_le_transverseRate {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx0 : (0 : Q') ≤ x) (i : Nat) :
    HKConv.sTerm w x i ≤ transverseRate w i := by
  have hx : (-1 : Q') ≤ x := Q'.le_trans' _ _ _ (by decide) hx0
  have hc := Q'.le_of_lt (HKPos.pow_succ_pos_lt_one hw0 hw1 (2*i)).1
  apply HKConv.divPos_le_of_le (HKConv.factor_num_pos hw0 hw1 hx i)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (factor_ge_one hc hx0) (HKPos.two_nonneg hc))

/-- Produced finite first-moment ceiling for the literal Jacobi terms. -/
theorem firstMoment_le_cap {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx0 : (0 : Q') ≤ x) (N : Nat) :
    firstMoment w x N ≤ transverseCap w :=
  Q'.le_trans' _ _ _
    (sum_mono (HKConv.sTerm w x) (transverseRate w)
      (sTerm_le_transverseRate hw0 hw1 hx0) N)
    (transversePrefixCost_le_cap hw0 hw1 N)

/-- Produced second-moment domination, retaining every diagonal term. -/
theorem secondMoment_le_first {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx0 : (0 : Q') ≤ x) (N : Nat) :
    secondMoment w x N ≤ firstMoment w x N := by
  have hx : (-1 : Q') ≤ x := Q'.le_trans' _ _ _ (by decide) hx0
  exact sum_mono (fun i => HKConv.sTerm w x i*HKConv.sTerm w x i)
    (HKConv.sTerm w x) (fun i => Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (sTerm_le_one hw0 hw1 hx0 i)
      (HKConv.sTerm_nonneg hw0 hw1 hx i))
    (Q'.le_of_eqv (Q'.one_mul_eqv _))) N

/-- Actual first heat derivative bounded without dividing by the heat.
Valid on x >= 0 for every finite prefix, including N=0 and N=1. -/
theorem heat_first_le_cap {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx0 : (0 : Q') ≤ x) (N : Nat) :
    QPoly.eval (pderiv (heat w N)) (1+x) ≤
      transverseCap w * QPoly.eval (heat w N) (1+x) := by
  have hx : (-1 : Q') ≤ x := Q'.le_trans' _ _ _ (by decide) hx0
  have hP : (0 : Q') ≤ normalizedProduct w x N :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (SU2PointwiseHeatPositiveCompletion.inverseNome_nonnegative w)
        HalfPow.half_nonneg) (ThetaConv.Ppart_nonneg hw0 hw1 hx N)
  have hM := M1_nonneg (HKConv.sTerm w x) N
    (fun i _ => HKConv.sTerm_nonneg hw0 hw1 hx i)
  have hneg : -(secondMoment w x N) ≤ (0 : Q') :=
    Q'.neg_le_neg (M2_nonneg (HKConv.sTerm w x) N)
  have hdrop := Q'.add_le_add_left
    (firstMoment w x N*firstMoment w x N) _ _ hneg
  rw [Q'.add_zero'] at hdrop
  have hbound := Q'.le_trans' _ _ _ hdrop
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (firstMoment_le_cap hw0 hw1 hx0 N) hM)
  have hreorder : normalizedProduct w x N * (transverseCap w * firstMoment w x N) ≈
      transverseCap w * (normalizedProduct w x N * firstMoment w x N) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => normalizedProduct w x N | 1 => transverseCap w | _ => firstMoment w x N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (heat_first_moment_pin hw0 hw1 hx N))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hbound hP)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hreorder
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (heat_eval_moment_pin hw0 hw1 hx N))))))

private theorem moment_payment {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx0 : (0 : Q') ≤ x) (N : Nat) :
    (0 : Q') ≤ (transverseCap w + -(secondMoment w x N)) *
        (firstMoment w x N*firstMoment w x N) +
      ((2*firstMoment w x N)*thirdMoment w x N +
        -(secondMoment w x N*secondMoment w x N)) := by
  have hx : (-1 : Q') ≤ x := Q'.le_trans' _ _ _ (by decide) hx0
  have hceiling := Q'.le_trans' _ _ _ (secondMoment_le_first hw0 hw1 hx0 N)
    (firstMoment_le_cap hw0 hw1 hx0 N)
  have hv := moment_variance_nonneg (HKConv.sTerm w x) N
    (fun i _ => HKConv.sTerm_nonneg hw0 hw1 hx i)
  have hsplit : (2*firstMoment w x N)*thirdMoment w x N +
      -(secondMoment w x N*secondMoment w x N) ≈
      2*(firstMoment w x N*thirdMoment w x N +
        -(secondMoment w x N*secondMoment w x N)) +
      secondMoment w x N*secondMoment w x N :=
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 2) (.var 0)) (.var 2)) (.neg (.mul (.var 1) (.var 1))))
      (.add (.mul (.const 2) (.add (.mul (.var 0) (.var 2))
        (.neg (.mul (.var 1) (.var 1))))) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => firstMoment w x N | 1 => secondMoment w x N | _ => thirdMoment w x N)
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hceiling)
      (SumOfSquares.q_mul_self_nonneg _))
    (nonneg_of_eqv hsplit (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) hv)
      (SumOfSquares.q_mul_self_nonneg _)))

/-- Denominator-cleared LOWER log-Hessian of the literal normalized heat and
its first two actual formal derivatives. Includes N=0; x <= 1 is unnecessary.
Neither heat positivity nor a reciprocal of the heat or M1 is a premise. -/
theorem heat_logHessian_lower {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx0 : (0 : Q') ≤ x) (N : Nat) :
    let h := QPoly.eval (heat w N) (1+x)
    let h1 := QPoly.eval (pderiv (heat w N)) (1+x)
    let h2 := QPoly.eval (pderiv (pderiv (heat w N))) (1+x)
    (0 : Q') ≤ transverseCap w*(h*h) + h*h2 + -(h1*h1) := by
  have hx : (-1 : Q') ≤ x := Q'.le_trans' _ _ _ (by decide) hx0
  have h := heat_eval_moment_pin hw0 hw1 hx N
  have h1 := heat_first_moment_pin hw0 hw1 hx N
  have h2 := heat_second_moment_pin hw0 hw1 hx N
  have hsub := add_congr (add_congr
    (mul_congr (Q'.eqv_refl (transverseCap w)) (mul_congr h h)) (mul_congr h h2))
    (Q'.neg_eqv_congr _ _ (mul_congr h1 h1))
  let q : PolyExpr := .var 0
  let s : PolyExpr := .var 1
  let t : PolyExpr := .var 2
  let u : PolyExpr := .var 3
  let hh : PolyExpr := .mul q s
  let hd : PolyExpr := .mul q (.add (.mul s s) (.neg t))
  let hdd : PolyExpr := .mul q
    (.add (.add (.mul (.mul s s) s) (.neg (.mul (.mul (.const 3) s) t))) (.mul (.const 2) u))
  have hpin := poly_identity_of_normal_eq
    (.add (.add (.mul (.var 4) (.mul hh hh)) (.mul hh hdd)) (.neg (.mul hd hd)))
    (.mul (.mul q q) (.add (.mul (.add (.var 4) (.neg t)) (.mul s s))
      (.add (.mul (.mul (.const 2) s) u) (.neg (.mul t t)))))
    (by decide) (fun
      | 0 => normalizedProduct w x N
      | 1 => firstMoment w x N
      | 2 => secondMoment w x N
      | 3 => thirdMoment w x N
      | _ => transverseCap w)
  exact nonneg_of_eqv (Q'.eqv_trans _ _ _ hsub hpin)
    (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _)
      (moment_payment hw0 hw1 hx0 N))

#print axioms sTerm_le_one
#print axioms sTerm_le_transverseRate
#print axioms firstMoment_le_cap
#print axioms secondMoment_le_first
#print axioms heat_first_le_cap
#print axioms heat_logHessian_lower

end YMGap.Continuum.JacobiHeatNearFlatLogHessian
