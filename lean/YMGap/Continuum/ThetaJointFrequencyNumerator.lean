/-
# Signed endpoint frequency numerator of the original finite theta box

The difference-frequency-square sum is the exact first/angular numerator
of the original bare polynomial. All rational w,x and N=0 are included.
No finite Euler-product substitution, positivity, differentiation of a
limit, curvature bound, or physical spectral claim is made.
-/

import YMGap.Continuum.ThetaJointWeightedMoment
import YMGap.Continuum.IntRingNormaliser
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.ThetaJointFrequencyNumerator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly (eval)
open YMGap.Constructive.QPolyFormalDerivative (pderiv)
open YMGap.Continuum.ThetaParityConvolution (SignedPair boxIndices)
open YMGap.Continuum.ThetaParityWeights (frequencyCell)
open YMGap.Continuum.ThetaJointValuePin (cell_endpoint_pin)
open YMGap.Continuum.ThetaJointAngularPin
open YMGap.Continuum.ThetaJointWeightedMoment
open YMGap.Continuum.FiniteJacobiAngularComparison (angularEval)
open YMGap.Continuum.FiniteDeterministicKernelPushforward (listQSum_add listQSum_mul_left)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem add_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) :
    a+c ≈ b+d := Q'.add_eqv_congr' h g

private theorem natAbs_square_cast (j : Int) :
    ((j.natAbs*j.natAbs : Nat) : Int) = j*j := by
  rw [Int.natCast_mul]
  rcases Int.le_total 0 j with hj | hj
  · rw [Int.natAbs_of_nonneg hj]
  · rw [Int.ofNat_natAbs_of_nonpos hj]
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]

/-- Exact rational signed-frequency square balance; no truncated natural
subtraction or sign restriction appears. -/
theorem frequency_square_balance (m n : Int) :
    Q'.ofNat ((m-n).natAbs*(m-n).natAbs) +
      Q'.ofNat ((m+n).natAbs*(m+n).natAbs) ≈
        2*Q'.ofNat (m.natAbs*m.natAbs+n.natAbs*n.natAbs) := by
  unfold Q'.eqv
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    show Q'.num (2 : Q') = 2 by rfl,
    show (Q'.den (2 : Q') : Int) = 1 by rfl, Int.mul_one]
  change (((m-n).natAbs*(m-n).natAbs : Nat) : Int) +
    (((m+n).natAbs*(m+n).natAbs : Nat) : Int) =
      2*((m.natAbs*m.natAbs+n.natAbs*n.natAbs : Nat) : Int)
  rw [Int.natCast_add, natAbs_square_cast, natAbs_square_cast,
    natAbs_square_cast, natAbs_square_cast]
  simp only [Int.sub_eq_add_neg]
  exact IntRingNormaliser.poly_identity_of_normal_eq
    (.add (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))))
    (.mul (.const 2) (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))
    (by decide) (fun | 0 => m | _ => n)

private theorem cell_frequency_balance (w x : Q') (z : SignedPair) :
    frequencyCell w x z + plusFrequencyCell w x z ≈ 2*momentCell w x z := by
  let D := Q'.ofNat ((z.1-z.2).natAbs*(z.1-z.2).natAbs)
  let S := Q'.ofNat ((z.1+z.2).natAbs*(z.1+z.2).natAbs)
  let C := w^(z.1.natAbs*z.1.natAbs+z.2.natAbs*z.2.natAbs)
  let T := Cheb.T (z.1+z.2).natAbs x
  have hf : frequencyCell w x z ≈ D*(C*T) :=
    Q'.mul_eqv_congr_left D _ _ (cell_endpoint_pin w x z)
  have hregroup : D*(C*T)+(S*C)*T ≈ (D+S)*(C*T) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (by decide) (fun | 0 => D | 1 => S | 2 => C | _ => T)
  refine Q'.eqv_trans _ _ _ (add_congr hf (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _ _ _ hregroup ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (C*T)
    (frequency_square_balance z.1 z.2)) ?_
  exact poly_identity_of_normal_eq
    (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 2)))
    (.mul (.const 2) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
    (by decide) (fun
      | 0 => Q'.ofNat (z.1.natAbs*z.1.natAbs+z.2.natAbs*z.2.natAbs)
      | 1 => C
      | _ => T)

/-- Actual finite box-frequency balance before taking any limits. -/
theorem frequency_plus_moment_pin (w x : Q') (N : Nat) :
    listQSum (frequencyCell w x) (boxIndices N) +
      listQSum (plusFrequencyCell w x) (boxIndices N) ≈ 2*momentSum w x N :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_add _ _ _))
    (Q'.eqv_trans _ _ _ (listQSum_congr (cell_frequency_balance w x) _)
      (listQSum_mul_left 2 (momentCell w x) _))

/-- Endpoint frequency numerator of the ORIGINAL finite bare theta
polynomial, with its actual formal first and angular jets. It may be signed. -/
theorem frequency_box_numerator_pin (w x : Q') (N : Nat) :
    listQSum (frequencyCell w x) (boxIndices N) ≈
      2*((1 + -(x*x))*(eval (pderiv (barePolynomial w N)) x *
        eval (pderiv (barePolynomial w N)) x) +
        -(eval (barePolynomial w N) x*angularEval (barePolynomial w N) x)) := by
  let Q := listQSum (frequencyCell w x) (boxIndices N)
  let S := listQSum (plusFrequencyCell w x) (boxIndices N)
  have hstart : Q ≈ (Q+S)+-S :=
    poly_identity_of_normal_eq (.var 0)
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
      (by decide) (fun | 0 => Q | _ => S)
  have hbalance : Q ≈ 2*momentSum w x N + angularEval (jointPolynomial w N) x :=
    Q'.eqv_trans _ _ _ hstart (add_congr (frequency_plus_moment_pin w x N)
      (Q'.eqv_symm (joint_angular_frequency_pin w x N)))
  refine Q'.eqv_trans _ _ _ hbalance ?_
  refine Q'.eqv_trans _ _ _ (add_congr
    (Q'.mul_eqv_congr_left 2 _ _ (moment_sum_angular_pin w x N))
    (joint_angular_pin w x N)) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.const 2) (.mul (.mul (.const (-2)) (.var 0)) (.var 1)))
      (.add (.mul (.const 2) (.mul (.var 0) (.var 1)))
        (.mul (.const 2) (.mul (.var 2) (.mul (.var 3) (.var 3))))))
    (.mul (.const 2) (.add (.mul (.var 2) (.mul (.var 3) (.var 3)))
      (.neg (.mul (.var 0) (.var 1))))) (by decide)
    (fun
      | 0 => eval (barePolynomial w N) x
      | 1 => angularEval (barePolynomial w N) x
      | 2 => 1 + -(x*x)
      | _ => eval (pderiv (barePolynomial w N)) x)

end YMGap.Continuum.ThetaJointFrequencyNumerator

#print axioms YMGap.Continuum.ThetaJointFrequencyNumerator.frequency_square_balance
#print axioms YMGap.Continuum.ThetaJointFrequencyNumerator.frequency_plus_moment_pin
#print axioms YMGap.Continuum.ThetaJointFrequencyNumerator.frequency_box_numerator_pin
