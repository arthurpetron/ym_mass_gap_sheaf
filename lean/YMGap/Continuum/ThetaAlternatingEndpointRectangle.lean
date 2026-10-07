/-
# Literal endpoint determinant of the mixed theta rectangle

The odd endpoint frequency sum is one-sided, h=0 through N; the even
endpoint frequency sum uses the actual bilateral signed interval. The
existing mixed endpoint cell factors into their determinant, with the
original nome coefficients and no hidden factor two. This is finite
rational algebra for every w and N, including N=0. The separate actual
polynomial-jet consumer supplies the derivative interpretation; no
completed addition formula or analytic bound is asserted here.
-/

import YMGap.Continuum.ThetaAlternatingMixedRectangle
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.ThetaAlternatingEndpointRectangle

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaParityConvolution (signedIndices)
open YMGap.Continuum.ThetaParityWeights (evenThetaTerm)
open YMGap.Continuum.ThetaAlternatingMixedTail (endpointCell mixedRectangleIndices)
open YMGap.Continuum.ThetaAlternatingMixedRectangle (oddTerm oddPartial evenPartial)
open YMGap.Continuum.FiniteWeightedCartesianInjection (listQSum_cartesian_product)
open YMGap.Continuum.FiniteDeterministicKernelPushforward (listQSum_add listQSum_mul_left)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Literal one-sided odd endpoint frequency coefficient. -/
def oddEndpointTerm (w : Q') (h : Nat) : Q' :=
  w^(2*(h*(h+1)))*Q'.ofNat ((2*h+1)*(2*h+1))

def oddEndpointJet (w : Q') (N : Nat) : Q' :=
  listQSum (oddEndpointTerm w) (List.range (N+1))

/-- Literal bilateral even endpoint frequency coefficient, including zero. -/
def evenEndpointTerm (w : Q') (k : Int) : Q' :=
  w^(2*(k.natAbs*k.natAbs))*Q'.ofNat ((2*k).natAbs*(2*k).natAbs)

def evenEndpointJet (w : Q') (N : Nat) : Q' :=
  listQSum (evenEndpointTerm w) (signedIndices N)

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

/-- Exact ordered endpoint cell, retaining its rational signed subtraction. -/
theorem endpointCell_factor_pin (w : Q') (h : Nat) (k : Int) :
    endpointCell w (h,k) ≈
      oddEndpointTerm w h*evenThetaTerm w 1 k +
        -(oddTerm w 1 h*evenEndpointTerm w k) := by
  have hp : endpointCell w (h,k) ≈
      oddEndpointTerm w h*w^(2*(k.natAbs*k.natAbs)) +
        -(w^(2*(h*(h+1)))*evenEndpointTerm w k) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.pow_add_eqv w (2*(h*(h+1))) (2*(k.natAbs*k.natAbs)))) ?_
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.add (.var 2) (.neg (.var 3))))
      (.add (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (.neg (.mul (.var 0) (.mul (.var 1) (.var 3)))))
      (by decide) (fun
        | 0 => w^(2*(h*(h+1)))
        | 1 => w^(2*(k.natAbs*k.natAbs))
        | 2 => Q'.ofNat ((2*h+1)*(2*h+1))
        | _ => Q'.ofNat ((2*k).natAbs*(2*k).natAbs))
  exact Q'.eqv_trans _ _ _ hp
    (add_congr (mul_congr (Q'.eqv_refl _) (Q'.eqv_symm (evenTerm_at_one w k)))
      (Q'.neg_eqv_congr _ _
        (mul_congr (Q'.eqv_symm (oddTerm_at_one w h)) (Q'.eqv_refl _))))

private theorem neg_one_mul (a : Q') : (-1 : Q')*a ≈ -a :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 a)
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))

private theorem sum_neg {A : Type} (f : A → Q') (xs : List A) :
    listQSum (fun a => -(f a)) xs ≈ -(listQSum f xs) :=
  Q'.eqv_trans _ _ _ (listQSum_congr (fun a => Q'.eqv_symm (neg_one_mul (f a))) xs)
    (Q'.eqv_trans _ _ _ (listQSum_mul_left (-1) f xs) (neg_one_mul _))

/-- Actual finite endpoint determinant with one-sided odd normalization.
There are no nome guards, approximation parameters or derivative premises. -/
theorem endpoint_rectangle_factored_pin (w : Q') (N : Nat) :
    listQSum (endpointCell w) (mixedRectangleIndices N) ≈
      evenPartial w 1 N*oddEndpointJet w N +
        -(oddPartial w 1 N*evenEndpointJet w N) := by
  let f := fun p : Nat × Int => oddEndpointTerm w p.1*evenThetaTerm w 1 p.2
  let g := fun p : Nat × Int => oddTerm w 1 p.1*evenEndpointTerm w p.2
  have hp : listQSum (endpointCell w) (mixedRectangleIndices N) ≈
      listQSum f (mixedRectangleIndices N) + -(listQSum g (mixedRectangleIndices N)) :=
    Q'.eqv_trans _ _ _
      (listQSum_congr (fun p : Nat × Int => endpointCell_factor_pin w p.1 p.2) _)
      (Q'.eqv_trans _ _ _ (listQSum_add f (fun p => -(g p)) _)
        (add_congr (Q'.eqv_refl _) (sum_neg g _)))
  exact Q'.eqv_trans _ _ _ hp
    (add_congr
      (Q'.eqv_trans _ _ _
        (listQSum_cartesian_product (oddEndpointTerm w) (evenThetaTerm w 1) _ _)
        (Q'.mul_comm_eqv _ _))
      (Q'.neg_eqv_congr _ _
        (listQSum_cartesian_product (oddTerm w 1) (evenEndpointTerm w) _ _)))

end YMGap.Continuum.ThetaAlternatingEndpointRectangle

#print axioms YMGap.Continuum.ThetaAlternatingEndpointRectangle.oddEndpointTerm
#print axioms YMGap.Continuum.ThetaAlternatingEndpointRectangle.oddEndpointJet
#print axioms YMGap.Continuum.ThetaAlternatingEndpointRectangle.evenEndpointTerm
#print axioms YMGap.Continuum.ThetaAlternatingEndpointRectangle.evenEndpointJet
#print axioms YMGap.Continuum.ThetaAlternatingEndpointRectangle.endpointCell_factor_pin
#print axioms YMGap.Continuum.ThetaAlternatingEndpointRectangle.endpoint_rectangle_factored_pin
