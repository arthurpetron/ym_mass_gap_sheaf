/-
# Original finite heat deficit near the identity

The first-kind Chebyshev forward difference has bound (2n+1)(1-x).
Telescoping gives 1-T_n(x) <= n^2(1-x). The bounded second-kind
recurrence then gives the EXACT Casimir slope
3*((n+1)-U_n(x)) <= n*(n+1)*(n+2)*(1-x).
Summation retains the original finite heat coefficients and nome.

This quantitative scalar producer is for the localized partition lower
bound. It neither restricts the interacting law nor asserts typical raw-link
concentration, entropy payment, physical scaling, H1 or a mass gap.
-/

import YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
import YMGap.Continuum.ChebyshevU
import YMGap.Continuum.HeatKernelNodeQuad
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2HeatFiniteCasimirDeficit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.Cheb (T U)
open YMGap.Continuum.ChebU (Tabs_le_one Ushift)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport (dimQ)
open YMGap.Continuum.BondMovingStep (coeffW coeffW_nonneg)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (pointwiseHeatTerm standardPointwiseHeatPartial)

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := RingNormaliser.PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩
private def v (i : Nat) : PE := .var i

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem sc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a-c ≈ b-d :=
  Q'.add_eqv_congr' h (Q'.neg_eqv_congr _ _ k)

private theorem add_le_add {a b c d : Q'} (h : a ≤ b) (k : c ≤ d) : a+c ≤ b+d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h) (Q'.add_le_add_left _ _ _ k)

private theorem cast_succ (n : Nat) : Q'.ofNat (n+1) ≈ Q'.ofNat n+1 :=
  Q'.ofNat_add_eqv n 1

private def forwardWeight (n : Nat) : Q' := 2*Q'.ofNat n+1
private def squareDegree (n : Nat) : Q' := Q'.ofNat n*Q'.ofNat n

/-- Literal rational n*(n+1)*(n+2), with no division or opaque constant. -/
def casimirSlope (n : Nat) : Q' := Q'.ofNat n*(Q'.ofNat n+1)*(Q'.ofNat n+2)

private theorem forward_step (n : Nat) : forwardWeight n+2 ≈ forwardWeight (n+1) := by
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _ (cast_succ n)) (Q'.eqv_refl _)))
  exact poly_identity_of_normal_eq ((2*v 0+1)+2) (2*(v 0+1)+1) (by decide) (fun _ => Q'.ofNat n)

private theorem square_step (n : Nat) : squareDegree n+forwardWeight n ≈ squareDegree (n+1) := by
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (mc (cast_succ n) (cast_succ n)))
  exact poly_identity_of_normal_eq (v 0*v 0+(2*v 0+1)) ((v 0+1)*(v 0+1))
    (by decide) (fun _ => Q'.ofNat n)

private theorem casimir_step (n : Nat) : casimirSlope n+6*squareDegree (n+2) ≈ casimirSlope (n+2) := by
  have hc : Q'.ofNat (n+2) ≈ Q'.ofNat n+2 := Q'.ofNat_add_eqv n 2
  have hs := mc hc hc
  have hd := mc (mc hc (Q'.add_eqv_congr' hc (Q'.eqv_refl 1)))
    (Q'.add_eqv_congr' hc (Q'.eqv_refl 2))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_left _ _ _ hs)) (Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hd))
  exact poly_identity_of_normal_eq
    (v 0*(v 0+1)*(v 0+2)+6*((v 0+2)*(v 0+2)))
    ((v 0+2)*((v 0+2)+1)*((v 0+2)+2)) (by decide) (fun _ => Q'.ofNat n)

private theorem forward_identity (n : Nat) (x : Q') :
    T (n+1) x-T (n+2) x ≈ (T n x-T (n+1) x)+2*(1-x)*T (n+1) x := by
  rw [Cheb.T_succ_succ]
  exact poly_identity_of_normal_eq
    (v 1+ -((2*v 2)*v 1+ -(v 0)))
    ((v 0+ -(v 1))+2*(1+ -(v 2))*v 1)
    (by decide) (fun | 0 => T n x | 1 => T (n+1) x | _ => x)

private theorem forward_bound (x : Q') (hx : x ≤ (1 : Q')) (hl : (-1 : Q') ≤ x) :
    ∀ n, T n x-T (n+1) x ≤ forwardWeight n*(1-x)
  | 0 => Q'.le_of_eqv (poly_identity_of_normal_eq (1+ -(v 0)) ((2*0+1)*(1+ -(v 0)))
      (by decide) (fun _ => x))
  | n+1 => by
      have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (2*(1-x))
        (Tabs_le_one n x hx hl).2 (Q'.mul_nonneg _ _ (by decide) (Q'.sub_nonneg_of_le hx))
      have h := add_le_add (forward_bound x hx hl n) hmul
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (forward_identity n x))
        (Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_))
      exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (v 0*v 1+(2*v 1)*1) ((v 0+2)*v 1)
        (by decide) (fun | 0 => forwardWeight n | _ => 1-x))
        (Q'.mul_eqv_congr_right _ _ _ (forward_step n))

/-- Sharp polynomial degree-squared deficit, including n=0 and x=-1,1. -/
theorem T_deficit (x : Q') (hx : x ≤ (1 : Q')) (hl : (-1 : Q') ≤ x) :
    ∀ n, 1-T n x ≤ squareDegree n*(1-x)
  | 0 => Q'.le_of_eqv (poly_identity_of_normal_eq (1+ -1) ((0*0)*v 0)
      (by decide) (fun _ => 1-x))
  | n+1 => by
      have h := add_le_add (T_deficit x hx hl n) (forward_bound x hx hl n)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_))
      · exact poly_identity_of_normal_eq (1+ -(v 1)) ((1+ -(v 0))+(v 0+ -(v 1)))
          (by decide) (fun | 0 => T n x | _ => T (n+1) x)
      · exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
          (Q'.mul_eqv_congr_right _ _ _ (square_step n))

private theorem dim_step (n : Nat) : dimQ (n+2) ≈ dimQ n+2 := by
  have hn : n+2+1=n+1+2 := by omega
  unfold dimQ
  rw [hn]
  exact Q'.ofNat_add_eqv (n+1) 2

private theorem U_deficit_step (n : Nat) (x : Q') :
    3*(dimQ (n+2)-U (n+2) x) ≈ 3*(dimQ n-U n x)+6*(1-T (n+2) x) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (sc (dim_step n) (Ushift n x))) ?_
  exact poly_identity_of_normal_eq
    (3*((v 0+2)+ -(v 1+2*v 2)))
    (3*(v 0+ -(v 1))+6*(1+ -(v 2)))
    (by decide) (fun | 0 => dimQ n | 1 => U n x | _ => T (n+2) x)

/-- Exact dimension-times-Casimir slope for every finite character. -/
theorem U_deficit (x : Q') (hx : x ≤ (1 : Q')) (hl : (-1 : Q') ≤ x) :
    ∀ n, 3*(dimQ n-U n x) ≤ casimirSlope n*(1-x)
  | 0 => Q'.le_of_eqv (poly_identity_of_normal_eq (3*(1+ -1)) ((0*(0+1)*(0+2))*v 0)
      (by decide) (fun _ => 1-x))
  | 1 => Q'.le_of_eqv (poly_identity_of_normal_eq (3*(2+ -(2*v 0)))
      ((1*(1+1)*(1+2))*(1+ -(v 0))) (by decide) (fun _ => x))
  | n+2 => by
      have ht := Q'.mul_le_mul_of_nonneg_left _ _ (6 : Q') (T_deficit x hx hl (n+2)) (by decide)
      have h := add_le_add (U_deficit x hx hl n) ht
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (U_deficit_step n x))
        (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq (v 0*v 2+6*(v 1*v 2)) ((v 0+6*v 1)*v 2)
            (by decide) (fun | 0 => casimirSlope n | 1 => squareDegree (n+2) | _ => 1-x))
          (Q'.mul_eqv_congr_right _ _ _ (casimir_step n)))))

/-- Original unnormalized finite heat Casimir moment, with the cutoff retained. -/
def casimirMoment (w : Q') (N : Nat) : Q' :=
  finSum (fun n => coeffW w n*casimirSlope n) N

/-- The original heat deficit is paid by its literal finite Casimir moment.
No Gaussian replacement or infinite-kernel limit is involved. -/
theorem heat_deficit {w : Q'} (hw : (0 : Q') ≤ w) (x : Q')
    (hx : x ≤ (1 : Q')) (hl : (-1 : Q') ≤ x) : ∀ N,
    3*(standardPointwiseHeatPartial w 1 N-standardPointwiseHeatPartial w x N) ≤
      casimirMoment w N*(1-x)
  | 0 => Q'.le_of_eqv (poly_identity_of_normal_eq (3*(0+ -0)) (0*v 0)
      (by decide) (fun _ => 1-x))
  | N+1 => by
      have hu := Q'.mul_le_mul_of_nonneg_left _ _ (coeffW w N) (U_deficit x hx hl N) (coeffW_nonneg hw N)
      have ht : 3*(pointwiseHeatTerm w 1 N-pointwiseHeatTerm w x N) ≤
          (coeffW w N*casimirSlope N)*(1-x) := by
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ hu (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (sc (Q'.mul_eqv_congr_left _ _ _ (HeatKernelNodeQuad.U_at_one N)) (Q'.eqv_refl _))) ?_
        exact poly_identity_of_normal_eq (3*(v 0*v 1+ -(v 0*v 2)))
          (v 0*(3*(v 1+ -(v 2))))
          (by decide) (fun | 0 => coeffW w N | 1 => dimQ N | _ => U N x)
      have h := add_le_add (heat_deficit hw x hx hl N) ht
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_))
      · exact poly_identity_of_normal_eq (3*((v 0+v 1)+ -(v 2+v 3)))
          (3*(v 0+ -(v 2))+3*(v 1+ -(v 3)))
          (by decide) (fun
            | 0 => standardPointwiseHeatPartial w 1 N
            | 1 => pointwiseHeatTerm w 1 N
            | 2 => standardPointwiseHeatPartial w x N
            | _ => pointwiseHeatTerm w x N)
      · exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)

end YMGap.Continuum.SU2HeatFiniteCasimirDeficit

#print axioms YMGap.Continuum.SU2HeatFiniteCasimirDeficit.casimirSlope
#print axioms YMGap.Continuum.SU2HeatFiniteCasimirDeficit.T_deficit
#print axioms YMGap.Continuum.SU2HeatFiniteCasimirDeficit.U_deficit
#print axioms YMGap.Continuum.SU2HeatFiniteCasimirDeficit.casimirMoment
#print axioms YMGap.Continuum.SU2HeatFiniteCasimirDeficit.heat_deficit
