/-
# Actual finite endpoint jets for the alternating half-diamond

The finite scalar half-diamond identity is first reflected into coefficient
polynomials, and only then formally differentiated. This pins the actual
endpoint-cell sum to the square of the literal alternating prefix. It is a
finite identity only: no limit/derivative interchange or radial estimate is
claimed.
-/

import YMGap.Continuum.ThetaAlternatingMixedPin
import YMGap.Continuum.ThetaAlternatingEndpointRectangle
import YMGap.Continuum.ChebyshevFormalJets
import YMGap.Constructive.QPolyCoefficientEvaluation
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ThetaAlternatingEndpointJets

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyCoefficientEvaluation
open YMGap.Continuum.ChebyshevFormalJets
open YMGap.Continuum.ThetaAlternatingKernel
open YMGap.Continuum.ThetaAlternatingMixedPin
open YMGap.Continuum.ThetaAlternatingMixedTail
open YMGap.Continuum.ThetaAlternatingMixedRectangle (evenPartial oddPartial)
open YMGap.Continuum.ThetaAlternatingEndpointRectangle
  (evenEndpointJet oddEndpointJet endpoint_rectangle_factored_pin)
open YMGap.Continuum.ThetaParityDiamondTail (omittedBudget)
open YMGap.Continuum.ThetaAngularShellTail (shellTailCutoff)
open YMGap.Continuum.ChebyshevHalfShiftProduct (halfShiftCoord)
open YMGap.Continuum.ChebyshevEvenSOS (sinCoord)
open YMGap.Continuum.SU2ClassPolynomialAlgebra (chebPoly eval_chebPoly)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)
open YMGap.Continuum.ChebTFwdBoundClose (ofNat_mul_eqv)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
      (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem add_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a+c ≈ b+d := Q'.add_eqv_congr' hab hcd

/-- Finite coefficient representative of the sine coordinate. -/
def sinPoly : Nat → Poly
  | 0 => []
  | n+1 => chebPoly n

/-- Polynomial representative of the actual half-shift coordinate. -/
def halfPoly (n : Nat) : Poly := padd (chebPoly n) (sinPoly n)

/-- One weighted term in the actual alternating prefix. -/
def alternatingTermPoly (w : Q') (n : Nat) : Poly :=
  pscale (((-1 : Q')^n) * w^(n*(n+1))) (halfPoly n)

/-- Right-associated polynomial sum, parallel to `listQSum`. -/
def polySum : List Poly → Poly
  | [] => []
  | p::ps => padd p (polySum ps)

/-- Actual coefficient polynomial for the prefix `0,...,N`. -/
def alternatingPolynomial (w : Q') (N : Nat) : Poly :=
  polySum ((List.range (N+1)).map (alternatingTermPoly w))

/-- Polynomial representative of a mixed endpoint cell before taking its
endpoint derivative. -/
def mixedCellPolynomial (w : Q') (p : Nat × Int) : Poly :=
  pscale (w^(2*(p.1*(p.1+1))+2*(p.2.natAbs*p.2.natAbs)))
    (psub (Tpoly (2*p.1+1)) (Tpoly (2*p.2).natAbs))

/-- Finite polynomial sum over the actual half-diamond. -/
def halfDiamondPolynomial (w : Q') (N : Nat) : Poly :=
  polySum ((mixedDiamondIndices N).map (mixedCellPolynomial w))

/-- Actual rectangular polynomial, including cells omitted by the diamond. -/
def mixedRectanglePolynomial (w : Q') (N : Nat) : Poly :=
  polySum ((mixedRectangleIndices N).map (mixedCellPolynomial w))

/-- Polynomial whose scalar value is the finite alternating square identity. -/
def squareKernelPolynomial (w : Q') (N : Nat) : Poly :=
  pmul [-1,1] (pmul (alternatingPolynomial w N) (alternatingPolynomial w N))

private theorem eval_sinPoly : ∀ n x, eval (sinPoly n) x ≈ sinCoord n x
  | 0, _ => Q'.eqv_refl 0
  | n+1, x => eval_chebPoly n x

private theorem eval_halfPoly (n : Nat) (x : Q') :
    eval (halfPoly n) x ≈ halfShiftCoord n x := by
  exact Q'.eqv_trans _ _ _ (eval_padd _ _ x)
    (add_congr (eval_chebPoly n x) (eval_sinPoly n x))

private theorem eval_alternatingTermPoly (w x : Q') (n : Nat) :
    eval (alternatingTermPoly w n) x ≈ alternatingTerm w x n := by
  unfold alternatingTermPoly alternatingTerm
  exact Q'.eqv_trans _ _ _ (eval_pscale _ _ x)
    (Q'.mul_eqv_congr_left _ _ _ (eval_halfPoly n x))

private theorem eval_polySum (ps : List Poly) (x : Q') :
    eval (polySum ps) x ≈ listQSum (fun p => eval p x) ps := by
  induction ps with
  | nil => exact Q'.eqv_refl 0
  | cons p ps ih =>
      change eval (padd p (polySum ps)) x ≈ eval p x + listQSum (fun q => eval q x) ps
      exact Q'.eqv_trans _ _ _ (eval_padd _ _ x)
        (add_congr (Q'.eqv_refl _) ih)

private theorem listQSum_mapPoly {A B : Type} (f : A → B) (g : B → Q') :
    ∀ xs, listQSum g (xs.map f) ≈ listQSum (fun a => g (f a)) xs
  | [] => Q'.eqv_refl 0
  | a::xs => by
      change g (f a) + listQSum g (xs.map f) ≈
        g (f a) + listQSum (fun a => g (f a)) xs
      exact Q'.add_eqv_congr_left _ _ _ (listQSum_mapPoly f g xs)

private theorem eval_polySum_map (A : Type) (f : A → Poly) (xs : List A) (x : Q') :
    eval (polySum (xs.map f)) x ≈ listQSum (fun a => eval (f a) x) xs := by
  exact Q'.eqv_trans _ _ _ (eval_polySum _ x)
    (listQSum_mapPoly f (fun p => eval p x) xs)

private theorem alternatingPolynomial_eval (w x : Q') (N : Nat) :
    eval (alternatingPolynomial w N) x ≈ alternatingPartial w x N := by
  unfold alternatingPolynomial alternatingPartial
  exact Q'.eqv_trans _ _ _ (eval_polySum_map _ (alternatingTermPoly w) _ x)
    (listQSum_congr (eval_alternatingTermPoly w x) _)

private theorem mixedCellPolynomial_eval (w x : Q') (p : Nat × Int) :
    eval (mixedCellPolynomial w p) x ≈ mixedCell w x p := by
  unfold mixedCellPolynomial mixedCell
  exact Q'.eqv_trans _ _ _ (eval_pscale _ _ x)
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (eval_psub _ _ x)
        (add_congr (eval_Tpoly _ x)
          (Q'.neg_eqv_congr _ _ (eval_Tpoly _ x)))))

private theorem halfDiamondPolynomial_eval (w x : Q') (N : Nat) :
    eval (halfDiamondPolynomial w N) x ≈
      listQSum (mixedCell w x) (mixedDiamondIndices N) := by
  unfold halfDiamondPolynomial
  exact Q'.eqv_trans _ _ _ (eval_polySum_map _ (mixedCellPolynomial w) _ x)
    (listQSum_congr (mixedCellPolynomial_eval w x) _)

private theorem eval_linearFactor (x : Q') : eval [-1,1] x ≈ x + -(1 : Q') :=
  poly_identity_of_normal_eq
    (.add (.const (-1))
      (.mul (.var 0) (.add (.const 1) (.mul (.var 0) (.const 0)))))
    (.add (.var 0) (.neg (.const 1))) (by decide) (fun _ => x)

/-- The scalar finite identity is promoted to a coefficient identity before
formal differentiation. -/
theorem squareKernel_coeff_pin (w : Q') (N : Nat) :
    CoeffEqv (squareKernelPolynomial w N) (halfDiamondPolynomial w N) := by
  apply ChebyshevFormalJets.coefficients_of_eval_eqv
  intro x
  have hleft : eval (squareKernelPolynomial w N) x ≈
      (x + -(1 : Q'))*(alternatingPartial w x N*alternatingPartial w x N) := by
    unfold squareKernelPolynomial
    exact Q'.eqv_trans _ _ _ (eval_pmul _ _ x)
      (mul_congr (eval_linearFactor x)
        (Q'.eqv_trans _ _ _ (eval_pmul _ _ x)
          (mul_congr (alternatingPolynomial_eval w x N)
            (alternatingPolynomial_eval w x N)))
      )
  have hright := halfDiamondPolynomial_eval w x N
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ (alternatingPartial_halfDiamond_square w x N) (Q'.eqv_symm hright))

private theorem pderiv_psub (p q : Poly) :
    CoeffEqv (pderiv (psub p q)) (psub (pderiv p) (pderiv q)) := by
  exact (pderiv_padd p (pneg q)).trans
    ((CoeffEqv.refl (pderiv p)).padd (pderiv_pscale (-1) q))

private theorem pderiv_polySum : ∀ ps : List Poly,
    CoeffEqv (pderiv (polySum ps)) (polySum (ps.map pderiv))
  | [] => CoeffEqv.refl []
  | p::ps => by
      change CoeffEqv (pderiv (padd p (polySum ps)))
        (padd (pderiv p) (polySum (ps.map pderiv)))
      exact (pderiv_padd p (polySum ps)).trans
        ((CoeffEqv.refl (pderiv p)).padd (pderiv_polySum ps))

private theorem eval_polySum_map_derivative (A : Type) (f : A → Poly)
    (xs : List A) (x : Q') :
    eval (polySum ((xs.map f).map pderiv)) x ≈
      listQSum (fun a => eval (pderiv (f a)) x) xs := by
  induction xs with
  | nil => exact Q'.eqv_refl 0
  | cons a xs ih =>
      change eval (padd (pderiv (f a))
          (polySum ((xs.map f).map pderiv))) x ≈
        eval (pderiv (f a)) x + listQSum (fun a => eval (pderiv (f a)) x) xs
      exact Q'.eqv_trans _ _ _ (eval_padd _ _ x)
        (add_congr (Q'.eqv_refl _) ih)

private theorem eval_derivative_polySum_map (A : Type) (f : A → Poly)
    (xs : List A) (x : Q') :
    eval (pderiv (polySum (xs.map f))) x ≈
      listQSum (fun a => eval (pderiv (f a)) x) xs := by
  exact Q'.eqv_trans _ _ _
    (coefficient_eval (pderiv_polySum (xs.map f)) x)
    (eval_polySum_map_derivative A f xs x)

private theorem eval_mixedCellPolynomial_derivative (w : Q') (p : Nat × Int) :
    eval (pderiv (mixedCellPolynomial w p)) 1 ≈ endpointCell w p := by
  let c := w^(2*(p.1*(p.1+1))+2*(p.2.natAbs*p.2.natAbs))
  let odd := 2*p.1+1
  let even := (2*p.2).natAbs
  have hscale := pderiv_pscale c (psub (Tpoly odd) (Tpoly even))
  have hsub := pderiv_psub (Tpoly odd) (Tpoly even)
  have h := Q'.eqv_trans _ _ _
    (coefficient_eval hscale 1)
    (Q'.eqv_trans _ _ _ (eval_pscale c _ 1)
      (Q'.mul_eqv_congr_left c _ _
        (Q'.eqv_trans _ _ _ (coefficient_eval hsub 1)
          (Q'.eqv_trans _ _ _ (eval_psub _ _ 1)
            (add_congr (ChebyshevFormalJets.first_derivative_at_one odd)
              (Q'.neg_eqv_congr _ _ (ChebyshevFormalJets.first_derivative_at_one even)))))))
  have ho : Q'.ofNat odd * Q'.ofNat odd ≈ Q'.ofNat (odd*odd) :=
    Q'.eqv_symm (ofNat_mul_eqv odd odd)
  have he : Q'.ofNat even * Q'.ofNat even ≈ Q'.ofNat (even*even) :=
    Q'.eqv_symm (ofNat_mul_eqv even even)
  unfold endpointCell
  dsimp [c, odd, even] at h
  exact Q'.eqv_trans _ _ _ h
    (mul_congr (Q'.eqv_refl _) (add_congr ho (Q'.neg_eqv_congr _ _ he)))

/-- Actual endpoint jet of the coefficient-pinned half-diamond polynomial. -/
theorem endpointCell_sum_eq_alternating_square (w : Q') (N : Nat) :
    listQSum (endpointCell w) (mixedDiamondIndices N) ≈
      alternatingPartial w 1 N * alternatingPartial w 1 N := by
  have hpoly := squareKernel_coeff_pin w N
  have hderiv := hpoly.pderiv
  have hleft := coefficient_eval hderiv 1
  have hright := eval_derivative_polySum_map _ (mixedCellPolynomial w)
    (mixedDiamondIndices N) 1
  have hcell : listQSum (fun p => eval (pderiv (mixedCellPolynomial w p)) 1)
      (mixedDiamondIndices N) ≈ listQSum (endpointCell w)
      (mixedDiamondIndices N) :=
    listQSum_congr (fun p => eval_mixedCellPolynomial_derivative w p) _
  have hsum := Q'.eqv_trans _ _ _ hright hcell
  have hkernel : eval (pderiv (squareKernelPolynomial w N)) 1 ≈
      alternatingPartial w 1 N * alternatingPartial w 1 N := by
    unfold squareKernelPolynomial
    have hp := pderiv_pmul [-1,1]
      (pmul (alternatingPolynomial w N) (alternatingPolynomial w N))
    have heval := coefficient_eval hp 1
    have hfirst : eval (pderiv [-1,1]) 1 ≈ 1 := by
      change eval [1*1] 1 ≈ 1
      exact poly_identity_of_normal_eq
        (.add (.mul (.const 1) (.const 1)) (.mul (.var 0) (.const 0)))
        (.const 1) (by decide) (fun _ => 1)
    have hzero : eval [-1,1] 1 ≈ 0 := by
      exact Q'.eqv_trans _ _ _ (eval_linearFactor 1) (by decide)
    have hA := alternatingPolynomial_eval w 1 N
    have hprod := eval_pmul (alternatingPolynomial w N) (alternatingPolynomial w N) 1
    have hfirstTerm : eval (pmul (pderiv [-1,1])
        (pmul (alternatingPolynomial w N) (alternatingPolynomial w N))) 1 ≈
        alternatingPartial w 1 N * alternatingPartial w 1 N := by
      exact Q'.eqv_trans _ _ _ (eval_pmul _ _ 1)
        (Q'.eqv_trans _ _ _ (mul_congr hfirst
          (Q'.eqv_trans _ _ _ hprod (mul_congr hA hA)))
          (Q'.one_mul_eqv _))
    have hsecondTerm : eval (pmul [-1,1]
        (pderiv (pmul (alternatingPolynomial w N) (alternatingPolynomial w N)))) 1 ≈ 0 := by
      exact Q'.eqv_trans _ _ _ (eval_pmul _ _ 1)
        (Q'.eqv_trans _ _ _
          (mul_congr hzero (Q'.eqv_refl _)) (Q'.zero_mul_eqv _))
    have hsplit : eval (padd
        (pmul (pderiv [-1,1])
          (pmul (alternatingPolynomial w N) (alternatingPolynomial w N)))
        (pmul [-1,1]
          (pderiv (pmul (alternatingPolynomial w N) (alternatingPolynomial w N))))) 1 ≈
        alternatingPartial w 1 N * alternatingPartial w 1 N := by
      exact Q'.eqv_trans _ _ _ (eval_padd _ _ 1)
        (Q'.eqv_trans _ _ _ (add_congr hfirstTerm hsecondTerm)
          (QPoly.q_add_zero_eqv _))
    exact Q'.eqv_trans _ _ _ heval hsplit
  have hcombine := Q'.eqv_trans _ _ _ hleft hsum
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hcombine) hkernel

/-- Formal endpoint derivative of the ACTUAL rectangle, not of a substituted
square. Its omitted cells are retained. -/
theorem mixedRectanglePolynomial_endpoint_derivative (w : Q') (N : Nat) :
    eval (pderiv (mixedRectanglePolynomial w N)) 1 ≈
      listQSum (endpointCell w) (mixedRectangleIndices N) :=
  Q'.eqv_trans _ _ _
    (eval_derivative_polySum_map _ (mixedCellPolynomial w) (mixedRectangleIndices N) 1)
    (listQSum_congr (fun p => eval_mixedCellPolynomial_derivative w p) _)

/-- The actual endpoint rectangle approaches the literal endpoint square;
the finite rectangle is NOT asserted to equal that square. -/
theorem endpoint_rectangle_square_error_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N : Nat) :
    Q'.abs (listQSum (endpointCell w) (mixedRectangleIndices N) +
      -(alternatingPartial w 1 N * alternatingPartial w 1 N)) ≤ omittedBudget w N :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (TsumDeriv.Q'.abs_eqv_congr (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (endpointCell_sum_eq_alternating_square w N))))))
    (endpoint_rectangle_error_le hw0 hw1 N)

/-- SAME explicit cutoff pays the ACTUAL formal endpoint jet against the
endpoint square, without differentiating any limit. -/
theorem endpoint_rectangle_formal_jet_close {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (he : (0 : Q') < epsilon)
    (N : Nat) (hN : shellTailCutoff w epsilon ≤ N) :
    Q'.abs (eval (pderiv (mixedRectanglePolynomial w N)) 1 +
      -(alternatingPartial w 1 N * alternatingPartial w 1 N)) ≤ epsilon :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (TsumDeriv.Q'.abs_eqv_congr (add_congr
      (mixedRectanglePolynomial_endpoint_derivative w N)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (endpointCell_sum_eq_alternating_square w N))))))
    (endpoint_rectangle_error_le_epsilon hw0 hw1 he N hN)

/-- Actual endpoint determinant versus the SAME endpoint square, with no
finite equality or limit-derivative interchange imposed. -/
theorem endpoint_determinant_square_close {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (he : (0 : Q') < epsilon)
    (N : Nat) (hN : shellTailCutoff w epsilon ≤ N) :
    Q'.abs ((evenPartial w 1 N*oddEndpointJet w N +
      -(oddPartial w 1 N*evenEndpointJet w N)) +
      -(alternatingPartial w 1 N * alternatingPartial w 1 N)) ≤ epsilon :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (TsumDeriv.Q'.abs_eqv_congr (add_congr
      (Q'.eqv_symm (endpoint_rectangle_factored_pin w N))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (endpointCell_sum_eq_alternating_square w N))))))
    (endpoint_rectangle_error_le_epsilon hw0 hw1 he N hN)

end YMGap.Continuum.ThetaAlternatingEndpointJets

#print axioms YMGap.Continuum.ThetaAlternatingEndpointJets.mixedRectanglePolynomial
#print axioms YMGap.Continuum.ThetaAlternatingEndpointJets.squareKernel_coeff_pin
#print axioms YMGap.Continuum.ThetaAlternatingEndpointJets.endpointCell_sum_eq_alternating_square
#print axioms YMGap.Continuum.ThetaAlternatingEndpointJets.mixedRectanglePolynomial_endpoint_derivative
#print axioms YMGap.Continuum.ThetaAlternatingEndpointJets.endpoint_rectangle_square_error_le
#print axioms YMGap.Continuum.ThetaAlternatingEndpointJets.endpoint_rectangle_formal_jet_close
#print axioms YMGap.Continuum.ThetaAlternatingEndpointJets.endpoint_determinant_square_close
