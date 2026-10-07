/-
# Exact finite alternating half-shift square kernel

The literal alternating prefix is squared on its actual Cartesian index
list. The checked half-shift Chebyshev product identity supplies every
pair cell, with both signed nome powers combined by the finite power law.
All rational nomes and coordinates, and N=0, are covered.

Consumer: the geometric half-diamond reindex and its omitted-cell tail.
No reindex, same-cutoff rectangle identity, approximation, infinite addition
formula, or curvature ceiling is asserted in this algebraic leaf.
-/

import YMGap.Continuum.ChebyshevHalfShiftProduct
import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.KPLimit

namespace YMGap.Continuum.ThetaAlternatingKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ChebyshevHalfShiftProduct (halfShiftCoord natDist halfShift_product)
open YMGap.Continuum.FiniteWeightedCartesianInjection (cartesian listQSum_cartesian_product)
open YMGap.Continuum.FiniteDeterministicKernelPushforward (listQSum_mul_left)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Actual alternating coefficient and original half-shift coordinate. -/
def alternatingTerm (w x : Q') (n : Nat) : Q' :=
  (-1 : Q')^n*w^(n*(n+1))*halfShiftCoord n x

/-- Prefix 0 through N, including the constant half-shift term. -/
def alternatingPartial (w x : Q') (N : Nat) : Q' :=
  listQSum (alternatingTerm w x) (List.range (N+1))

/-- The literal ordered-pair kernel, retaining the alternating sign. -/
def alternatingPairCell (w x : Q') (z : Nat × Nat) : Q' :=
  (-1 : Q')^(z.1+z.2)*w^(z.1*(z.1+1)+z.2*(z.2+1))*
    (Cheb.T (z.1+z.2+1) x + -(Cheb.T (natDist z.1 z.2) x))

private theorem mul_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
      (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem reversed_halfShift_product (n m : Nat) (x : Q') :
    (x + -(1 : Q'))*(halfShiftCoord n x*halfShiftCoord m x) ≈
      Cheb.T (n+m+1) x + -(Cheb.T (natDist n m) x) := by
  have hfirst : (x + -(1 : Q'))*(halfShiftCoord n x*halfShiftCoord m x) ≈
      -((1 + -x)*halfShiftCoord n x*halfShiftCoord m x) :=
    poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.neg (.const 1))) (.mul (.var 1) (.var 2)))
      (.neg (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)) (.var 2)))
      (by decide) (fun
        | 0 => x
        | 1 => halfShiftCoord n x
        | _ => halfShiftCoord m x)
  exact Q'.eqv_trans _ _ _ hfirst (Q'.eqv_trans _ _ _
    (Q'.neg_eqv_congr _ _ (halfShift_product n m x))
    (poly_identity_of_normal_eq
      (.neg (.add (.var 0) (.neg (.var 1))))
      (.add (.var 1) (.neg (.var 0))) (by decide) (fun
        | 0 => Cheb.T (natDist n m) x
        | _ => Cheb.T (n+m+1) x)))

/-- Each actual prefix pair supplies exactly the specified alternating cell. -/
theorem alternatingPairCell_product_pin (w x : Q') (n m : Nat) :
    (x + -(1 : Q'))*(alternatingTerm w x n*alternatingTerm w x m) ≈
      alternatingPairCell w x (n,m) := by
  have hregroup :
      (x + -(1 : Q'))*(alternatingTerm w x n*alternatingTerm w x m) ≈
        ((-1 : Q')^n*(-1 : Q')^m)*(w^(n*(n+1))*w^(m*(m+1)))*
          ((x + -(1 : Q'))*(halfShiftCoord n x*halfShiftCoord m x)) :=
    poly_identity_of_normal_eq
      (.mul (.var 0)
        (.mul (.mul (.mul (.var 1) (.var 2)) (.var 3))
          (.mul (.mul (.var 4) (.var 5)) (.var 6))))
      (.mul (.mul (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 5)))
        (.mul (.var 0) (.mul (.var 3) (.var 6))))
      (by decide) (fun
        | 0 => x + -(1 : Q')
        | 1 => (-1 : Q')^n
        | 2 => w^(n*(n+1))
        | 3 => halfShiftCoord n x
        | 4 => (-1 : Q')^m
        | 5 => w^(m*(m+1))
        | _ => halfShiftCoord m x)
  exact Q'.eqv_trans _ _ _ hregroup
    (mul_congr
      (mul_congr (Q'.eqv_symm (Q'.pow_add_eqv (-1) n m))
        (Q'.eqv_symm (Q'.pow_add_eqv w (n*(n+1)) (m*(m+1)))))
      (reversed_halfShift_product n m x))

/-- Exact finite square expansion on the actual Cartesian prefix, before
any geometric reindex. No positivity or convergence premise is required. -/
theorem alternatingPartial_square_expansion (w x : Q') (N : Nat) :
    (x + -(1 : Q'))*(alternatingPartial w x N*alternatingPartial w x N) ≈
      listQSum (alternatingPairCell w x)
        (cartesian (List.range (N+1)) (List.range (N+1))) := by
  have hp : listQSum
      (fun z : Nat × Nat => alternatingTerm w x z.1*alternatingTerm w x z.2)
      (cartesian (List.range (N+1)) (List.range (N+1))) ≈
        alternatingPartial w x N*alternatingPartial w x N :=
    listQSum_cartesian_product (alternatingTerm w x) (alternatingTerm w x) _ _
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hp)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_mul_left (x + -(1 : Q'))
    (fun z : Nat × Nat => alternatingTerm w x z.1*alternatingTerm w x z.2)
    (cartesian (List.range (N+1)) (List.range (N+1))))) ?_
  exact listQSum_congr
    (fun z : Nat × Nat => alternatingPairCell_product_pin w x z.1 z.2) _

end YMGap.Continuum.ThetaAlternatingKernel

#print axioms YMGap.Continuum.ThetaAlternatingKernel.alternatingTerm
#print axioms YMGap.Continuum.ThetaAlternatingKernel.alternatingPartial
#print axioms YMGap.Continuum.ThetaAlternatingKernel.alternatingPairCell
#print axioms YMGap.Continuum.ThetaAlternatingKernel.alternatingPairCell_product_pin
#print axioms YMGap.Continuum.ThetaAlternatingKernel.alternatingPartial_square_expansion
