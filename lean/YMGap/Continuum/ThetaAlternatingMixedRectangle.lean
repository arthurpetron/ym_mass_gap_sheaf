/-
# Exact factorization of the actual mixed theta rectangle

The odd prefix is one-sided, h=0 through N. The even prefix is the literal
bilateral signed interval -N through N. The mixed rectangle factors into
their endpoint determinant, retaining the actual nome coefficients. No
factor two from an unbalanced or bilateral odd cutoff is silently inserted.

Consumer: the alternating half-diamond square and its checked omitted tail.
This is finite algebra for arbitrary rational w,x, including N=0; no
convergence, theta addition, or curvature premise is used.
-/

import YMGap.Continuum.ThetaAlternatingMixedTail
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.ThetaAlternatingMixedRectangle

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaParityConvolution (signedIndices)
open YMGap.Continuum.ThetaParityWeights (evenThetaTerm)
open YMGap.Continuum.ThetaAlternatingMixedTail (mixedCell mixedRectangleIndices)
open YMGap.Continuum.FiniteWeightedCartesianInjection (listQSum_cartesian_product)
open YMGap.Continuum.FiniteDeterministicKernelPushforward (listQSum_add listQSum_mul_left)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Literal one-sided odd nome coefficient and coordinate. -/
def oddTerm (w x : Q') (h : Nat) : Q' :=
  w^(2*(h*(h+1)))*Cheb.T (2*h+1) x

def oddPartial (w x : Q') (N : Nat) : Q' :=
  listQSum (oddTerm w x) (List.range (N+1))

/-- The original bilateral even theta terms, not a modified observable. -/
def evenPartial (w x : Q') (N : Nat) : Q' :=
  listQSum (evenThetaTerm w x) (signedIndices N)

private theorem add_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a+c ≈ b+d := QPoly.q_add_congr hab hcd

private theorem mul_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
      (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem T_at_one : ∀ n, Cheb.T n 1 ≈ 1 ∧ Cheb.T (n+1) 1 ≈ 1
  | 0 => ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩
  | n+1 => by
      have h := T_at_one n
      refine ⟨h.2, ?_⟩
      rw [Cheb.T_succ_succ]
      exact Q'.eqv_trans _ _ _
        (add_congr (Q'.mul_eqv_congr_left _ _ _ h.2)
          (Q'.neg_eqv_congr _ _ h.1))
        (by decide : ((2 : Q')*1)*1 + -1 ≈ (1 : Q'))

private theorem oddTerm_at_one (w : Q') (h : Nat) :
    oddTerm w 1 h ≈ w^(2*(h*(h+1))) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (T_at_one (2*h+1)).1)
    (Q'.mul_one_eqv _)

private theorem evenTerm_at_one (w : Q') (k : Int) :
    evenThetaTerm w 1 k ≈ w^(2*(k.natAbs*k.natAbs)) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (T_at_one (2*k).natAbs).1)
    (Q'.mul_one_eqv _)

/-- The actual cell is the exact odd/even endpoint determinant cell. -/
theorem mixedCell_factor_pin (w x : Q') (h : Nat) (k : Int) :
    mixedCell w x (h,k) ≈
      oddTerm w x h*evenThetaTerm w 1 k + -(oddTerm w 1 h*evenThetaTerm w x k) := by
  have hp : mixedCell w x (h,k) ≈
      oddTerm w x h*w^(2*(k.natAbs*k.natAbs)) +
        -(w^(2*(h*(h+1)))*evenThetaTerm w x k) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.pow_add_eqv w (2*(h*(h+1))) (2*(k.natAbs*k.natAbs)))) ?_
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.add (.var 2) (.neg (.var 3))))
      (.add (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (.neg (.mul (.var 0) (.mul (.var 1) (.var 3)))))
      (by decide) (fun
        | 0 => w^(2*(h*(h+1)))
        | 1 => w^(2*(k.natAbs*k.natAbs))
        | 2 => Cheb.T (2*h+1) x
        | _ => Cheb.T (2*k).natAbs x)
  exact Q'.eqv_trans _ _ _ hp
    (add_congr (mul_congr (Q'.eqv_refl _) (Q'.eqv_symm (evenTerm_at_one w k)))
      (Q'.neg_eqv_congr _ _ (mul_congr (Q'.eqv_symm (oddTerm_at_one w h)) (Q'.eqv_refl _))))

private theorem neg_one_mul (a : Q') : (-1 : Q')*a ≈ -a :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 a)
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))

private theorem sum_neg {A : Type} (f : A → Q') (xs : List A) :
    listQSum (fun a => -(f a)) xs ≈ -(listQSum f xs) :=
  Q'.eqv_trans _ _ _ (listQSum_congr (fun a => Q'.eqv_symm (neg_one_mul (f a))) xs)
    (Q'.eqv_trans _ _ _ (listQSum_mul_left (-1) f xs) (neg_one_mul _))

/-- Literal mixed rectangle factorization with the actual one-sided odd and
bilateral even prefixes, including their original endpoint coefficients. -/
theorem mixed_rectangle_factored_pin (w x : Q') (N : Nat) :
    listQSum (mixedCell w x) (mixedRectangleIndices N) ≈
      evenPartial w 1 N*oddPartial w x N + -(oddPartial w 1 N*evenPartial w x N) := by
  let f := fun p : Nat × Int => oddTerm w x p.1*evenThetaTerm w 1 p.2
  let g := fun p : Nat × Int => oddTerm w 1 p.1*evenThetaTerm w x p.2
  have hp : listQSum (mixedCell w x) (mixedRectangleIndices N) ≈
      listQSum f (mixedRectangleIndices N) + -(listQSum g (mixedRectangleIndices N)) :=
    Q'.eqv_trans _ _ _
      (listQSum_congr (fun p : Nat × Int => mixedCell_factor_pin w x p.1 p.2) _)
      (Q'.eqv_trans _ _ _ (listQSum_add f (fun p => -(g p)) _)
        (add_congr (Q'.eqv_refl _) (sum_neg g _)))
  exact Q'.eqv_trans _ _ _ hp
    (add_congr
      (Q'.eqv_trans _ _ _
        (listQSum_cartesian_product (oddTerm w x) (evenThetaTerm w 1) _ _)
        (Q'.mul_comm_eqv _ _))
      (Q'.neg_eqv_congr _ _
        (listQSum_cartesian_product (oddTerm w 1) (evenThetaTerm w x) _ _)))

end YMGap.Continuum.ThetaAlternatingMixedRectangle

#print axioms YMGap.Continuum.ThetaAlternatingMixedRectangle.oddTerm
#print axioms YMGap.Continuum.ThetaAlternatingMixedRectangle.oddPartial
#print axioms YMGap.Continuum.ThetaAlternatingMixedRectangle.evenPartial
#print axioms YMGap.Continuum.ThetaAlternatingMixedRectangle.mixedCell_factor_pin
#print axioms YMGap.Continuum.ThetaAlternatingMixedRectangle.mixed_rectangle_factored_pin
