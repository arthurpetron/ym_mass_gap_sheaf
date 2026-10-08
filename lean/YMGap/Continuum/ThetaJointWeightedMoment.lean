/-
# The actual signed-box theta moment and bare angular jet

The literal coefficient (m^2+n^2) on the original signed box is retained.
Second-coordinate reflection and the checked signed Chebyshev product law
factor its sum into twice the original bare prefix times its squared-mode
prefix. The latter is the negative ACTUAL formal angular jet of the bare
polynomial. Thus the finite moment is -2 F L(F), for all rational w,x and
all N, including zero. No Euler product, finite Jacobi approximation,
analytic guard, completed addition identity or curvature input is used.
-/

import YMGap.Continuum.ThetaJointAngularPin
import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.ThetaJointWeightedMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly (eval)
open YMGap.Continuum.ThetaParityConvolution (SignedPair signedIndices boxIndices)
open YMGap.Continuum.ThetaJointValuePin
open YMGap.Continuum.ThetaJointAngularPin (barePolynomial)
open YMGap.Continuum.FiniteJacobiAngularComparison
open YMGap.Continuum.ChebTFwdBoundClose (ofNat_mul_eqv)
open YMGap.Continuum.FiniteWeightedCartesianInjection (listQSum_cartesian_product)
open YMGap.Continuum.FiniteDeterministicKernelPushforward (listQSum_add listQSum_mul_left)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm (listQSum_append)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Actual signed even Gaussian coefficient weighted by its squared mode. -/
def weightedBareTerm (w x : Q') (k : Int) : Q' :=
  Q'.ofNat (k.natAbs*k.natAbs)*bareTerm w x k

/-- Literal total exponent moment on the original signed box. -/
def momentCell (w x : Q') (z : SignedPair) : Q' :=
  Q'.ofNat (z.1.natAbs*z.1.natAbs+z.2.natAbs*z.2.natAbs)*
    w^(z.1.natAbs*z.1.natAbs+z.2.natAbs*z.2.natAbs)*Cheb.T (z.1+z.2).natAbs x

def momentSum (w x : Q') (N : Nat) : Q' :=
  listQSum (momentCell w x) (boxIndices N)

private theorem add_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) :
    a+c ≈ b+d := QPoly.q_add_congr h g

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ g)

private theorem sum_singleton {A : Type} (f : A → Q') (a : A) :
    listQSum f [a] ≈ f a := QPoly.q_add_zero_eqv _

private theorem weighted_pair_pin (w x : Q') (m n : Int) :
    momentCell w x (m,n)+momentCell w x (m,-n) ≈
      2*(weightedBareTerm w x m*bareTerm w x n +
        bareTerm w x m*weightedBareTerm w x n) := by
  unfold momentCell
  rw [Int.natAbs_neg, show m + -n = m-n by omega]
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (product_sum_signed m n x)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (mul_congr (Q'.ofNat_add_eqv (m.natAbs*m.natAbs) (n.natAbs*n.natAbs))
      (Q'.pow_add_eqv w _ _))) ?_
  exact poly_identity_of_normal_eq
    (.mul (.mul (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.const 2) (.mul (.var 4) (.var 5))))
    (.mul (.const 2)
      (.add
        (.mul (.mul (.var 0) (.mul (.var 2) (.var 4))) (.mul (.var 3) (.var 5)))
        (.mul (.mul (.var 2) (.var 4)) (.mul (.var 1) (.mul (.var 3) (.var 5))))))
    (by decide) (fun
      | 0 => Q'.ofNat (m.natAbs*m.natAbs)
      | 1 => Q'.ofNat (n.natAbs*n.natAbs)
      | 2 => w^(m.natAbs*m.natAbs)
      | 3 => w^(n.natAbs*n.natAbs)
      | 4 => Cheb.T m.natAbs x
      | _ => Cheb.T n.natAbs x)

private theorem cancel_two {a b : Q'} (h : 2*a ≈ 2*b) : a ≈ b := by
  change (2*a.num)*(1*(b.den : Int)) = (2*b.num)*(1*(a.den : Int)) at h
  rw [Int.one_mul, Int.one_mul, Int.mul_assoc, Int.mul_assoc] at h
  change a.num*(b.den : Int) = b.num*(a.den : Int)
  omega

/-- The actual moment factors into the two actual bilateral prefixes. -/
theorem moment_sum_factor_pin (w x : Q') (N : Nat) :
    momentSum w x N ≈
      2*listQSum (bareTerm w x) (signedIndices N)*
        listQSum (weightedBareTerm w x) (signedIndices N) := by
  let J := momentSum w x N
  let B := listQSum (bareTerm w x) (signedIndices N)
  let D := listQSum (weightedBareTerm w x) (signedIndices N)
  have hd : J+J ≈ 2*(D*B+B*D) := by
    refine Q'.eqv_trans _ _ _ (add_congr (Q'.eqv_refl _)
      (Q'.eqv_symm (box_neg_sum (momentCell w x) N))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_add (momentCell w x)
      (fun z : SignedPair => momentCell w x (z.1,-z.2)) (boxIndices N))) ?_
    refine Q'.eqv_trans _ _ _
      (listQSum_congr (fun z : SignedPair => weighted_pair_pin w x z.1 z.2) _) ?_
    refine Q'.eqv_trans _ _ _ (listQSum_mul_left 2
      (fun z : SignedPair => weightedBareTerm w x z.1*bareTerm w x z.2 +
        bareTerm w x z.1*weightedBareTerm w x z.2) (boxIndices N)) ?_
    apply Q'.mul_eqv_congr_left 2
    exact Q'.eqv_trans _ _ _ (listQSum_add _ _ _)
      (add_congr
        (listQSum_cartesian_product (weightedBareTerm w x) (bareTerm w x) _ _)
        (listQSum_cartesian_product (bareTerm w x) (weightedBareTerm w x) _ _))
  apply cancel_two
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (poly_identity_of_normal_eq
      (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0)) (by decide) (fun _ => J)))
    (Q'.eqv_trans _ _ _ hd (poly_identity_of_normal_eq
      (.mul (.const 2) (.add (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1))))
      (.mul (.const 2) (.mul (.mul (.const 2) (.var 0)) (.var 1)))
      (by decide) (fun
        | 0 => B
        | _ => D)))

private theorem weighted_sum_negative_angularSum (w x : Q') : ∀ N,
    listQSum (weightedBareTerm w x) (signedIndices N) ≈
      -(angularSum (fun j => w^(j*j)) x N)
  | 0 => by
      change ((0 : Q')*1+0) ≈ -(0 : Q')
      decide
  | N+1 => by
      let v := weightedBareTerm w x ((N+1 : Nat) : Int)
      have hneg : weightedBareTerm w x (-((N+1 : Nat) : Int)) = v := by
        simp only [weightedBareTerm, bareTerm, Int.natAbs_neg]
        rfl
      have hp : listQSum (weightedBareTerm w x) (signedIndices (N+1)) ≈
          v + (-(angularSum (fun j => w^(j*j)) x N)+v) := by
        refine Q'.eqv_trans _ _ _ (sum_perm (weightedBareTerm w x) (signed_succ_perm N)) ?_
        change weightedBareTerm w x (-((N+1 : Nat) : Int)) +
          listQSum (weightedBareTerm w x) (signedIndices N ++ [((N+1 : Nat) : Int)]) ≈ _
        rw [hneg]
        exact add_congr (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (listQSum_append _ _ _)
            (add_congr (weighted_sum_negative_angularSum w x N) (sum_singleton _ _)))
      have hv : v ≈ (Q'.ofNat (N+1)*Q'.ofNat (N+1))*
          (w^((N+1)*(N+1))*Cheb.T (N+1) x) :=
        Q'.mul_eqv_congr_right _ _ _ (ofNat_mul_eqv (N+1) (N+1))
      exact Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _
        (add_congr hv (add_congr (Q'.eqv_refl _) hv))
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
            (.add (.neg (.var 3)) (.mul (.var 0) (.mul (.var 1) (.var 2)))))
          (.neg (.add (.var 3)
            (.neg (.mul (.mul (.mul (.const 2) (.var 1)) (.var 0)) (.var 2)))))
          (by decide) (fun
            | 0 => Q'.ofNat (N+1)*Q'.ofNat (N+1)
            | 1 => w^((N+1)*(N+1))
            | 2 => Cheb.T (N+1) x
            | _ => angularSum (fun j => w^(j*j)) x N)))

/-- The actual bilateral weighted mode sum is the negative formal angular
jet of the original bare polynomial, without any supplied derivative pin. -/
theorem weighted_sum_angular_pin (w x : Q') (N : Nat) :
    listQSum (weightedBareTerm w x) (signedIndices N) ≈
      -(angularEval (barePolynomial w N) x) :=
  Q'.eqv_trans _ _ _ (weighted_sum_negative_angularSum w x N)
    (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (angular_seriesPoly (fun j => w^(j*j)) x N)))

/-- Exact actual moment/jet relation for the original finite bare prefix.
N=0 is zero; no nome or coordinate guard is required. -/
theorem moment_sum_angular_pin (w x : Q') (N : Nat) :
    momentSum w x N ≈
      (-2 : Q')*eval (barePolynomial w N) x*angularEval (barePolynomial w N) x := by
  have hB : listQSum (bareTerm w x) (signedIndices N) ≈ eval (barePolynomial w N) x :=
    Q'.eqv_trans _ _ _ (bareTheta_signed_pin w x N)
      (Q'.eqv_symm (eval_seriesPoly (fun j => w^(j*j)) x N))
  exact Q'.eqv_trans _ _ _ (moment_sum_factor_pin w x N)
    (Q'.eqv_trans _ _ _
      (mul_congr (Q'.mul_eqv_congr_left 2 _ _ hB) (weighted_sum_angular_pin w x N))
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.var 0)) (.neg (.var 1)))
        (.mul (.mul (.const (-2)) (.var 0)) (.var 1))
        (by decide) (fun
          | 0 => eval (barePolynomial w N) x
          | _ => angularEval (barePolynomial w N) x)))

end YMGap.Continuum.ThetaJointWeightedMoment

#print axioms YMGap.Continuum.ThetaJointWeightedMoment.weightedBareTerm
#print axioms YMGap.Continuum.ThetaJointWeightedMoment.momentCell
#print axioms YMGap.Continuum.ThetaJointWeightedMoment.momentSum
#print axioms YMGap.Continuum.ThetaJointWeightedMoment.moment_sum_factor_pin
#print axioms YMGap.Continuum.ThetaJointWeightedMoment.weighted_sum_angular_pin
#print axioms YMGap.Continuum.ThetaJointWeightedMoment.moment_sum_angular_pin
