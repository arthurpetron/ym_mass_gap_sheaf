/-
# Coupling comparison localized to a finite ORIGINAL observation window

Compare the two full original expectations through their two smaller-window
expectations. The middle comparison uses the constructed two-nome path;
the two outer comparisons use the existing original-action boundary decay
with its already constructed placement, probe and geometric size witnesses.

The bound contains the number of faces in the INNER window only. It holds
for every further outer padding, after the heat cutoff has been removed.
Both small-nome spatial guards remain explicit. This is not a coupling-
uniform continuum modulus, a same-OS cross-scale identification, or survival.
-/
import YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound
import YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay

namespace YMGap.Continuum.BF4ExactSlabLocalizedCouplingBound

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (odd_expectation_pin)
open YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private theorem abs_chain {a b c : CReal} {x y : Q'}
    (hab : leEv (CReal.abs (CReal.sub a b)) (ofQ' x))
    (hbc : leEv (CReal.abs (CReal.sub b c)) (ofQ' y)) :
    leEv (CReal.abs (CReal.sub a c)) (ofQ' (x+y)) := by
  have hsum := leRat_add hab hbc
  intro epsilon he
  obtain ⟨N, hN⟩ := hsum epsilon he
  refine ⟨N, fun n hn => ?_⟩
  have ht : Q'.eqv (a.approx n + -c.approx n)
      ((a.approx n + -b.approx n)+(b.approx n + -c.approx n)) :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2)))) (by decide)
      (fun | 0 => a.approx n | 1 => b.approx n | _ => c.approx n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr ht))
    (Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (hN n hn))

private theorem abs_reverse {a b : CReal} {x : Q'}
    (h : leEv (CReal.abs (CReal.sub a b)) (ofQ' x)) :
    leEv (CReal.abs (CReal.sub b a)) (ofQ' x) := by
  have heq : Equiv (CReal.abs (CReal.sub b a)) (CReal.abs (CReal.sub a b)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => ExpNeg.abs_sub_comm (b.approx n) (a.approx n))
  exact leEv_trans (leEv_of_equiv heq) h

def windowCouplingCap (W u v : Q') {base : Nat} (e : PlaquetteExpression base) (margin : Nat) : Q' :=
  finiteSetCap W u v (bound e+1) (slabPhysicalFaceEdges (centralExtent (base+margin)))

variable {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v) (hvW : v ≤ W) (hW1 : W < (1 : Q'))

local notation "hv0" => Q'.pos_of_lt_of_le hu0 huv
local notation "hv1" => Q'.lt_of_le_of_lt hvW hW1
local notation "hu1" => Q'.lt_of_le_of_lt huv hv1

include hu0 huv hvW hW1 in
/-- Every original finite plaquette expression, same inner placement at both nomes. -/
theorem expressionMean_coupling_bound {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    leEv (CReal.abs (CReal.sub (expressionMean v hv0 hv1 e margin)
      (expressionMean u hu0 hu1 e margin))) (ofQ' (windowCouplingCap W u v e margin)) := by
  have h := expectation_difference_bound hu0 huv hvW hW1 (centralExtent (base+margin))
    (slabPhysicalFaceEdges (centralExtent (base+margin))) (fun _ h => h)
    (Interval.ofSquare (shiftedExpressionBound margin e))
  have hp := (CReal.sub_congr_left (odd_expectation_pin v hv0 hv1 (base+margin) (shiftedExpression margin e))).trans
    (CReal.sub_congr_right (odd_expectation_pin u hu0 hu1 (base+margin) (shiftedExpression margin e)))
  exact leEv_trans (leEv_of_equiv (abs_equiv_congr hp.symm)) h

def boundaryCap (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (e : PlaquetteExpression base) (margin : Nat) : Q' :=
  expressionAmplitude w hd hs e * (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize base)

def localizedCap (W u v : Q') (hdu : heatRemainderBound u < 1) (hdv : heatRemainderBound v < 1)
    (hsu : entropyRate 625 (adjustedCoreRate u hdu) < 1) (hsv : entropyRate 625 (adjustedCoreRate v hdv) < 1)
    {base : Nat} (e : PlaquetteExpression base) (margin : Nat) : Q' :=
  (boundaryCap v hdv hsv e margin + windowCouplingCap W u v e margin) + boundaryCap u hdu hsu e margin

include hu0 huv hvW hW1 in
/-- Uniform in OUTER padding: no count of the exterior faces occurs.
The inner-window count and both coupling-dependent boundary rates remain. -/
theorem localized_coupling_bound
    (hsmallu : heatRatio u ≤ HalfPow.half) (hsmallv : heatRatio v ≤ HalfPow.half)
    (hdu : heatRemainderBound u < 1) (hdv : heatRemainderBound v < 1)
    (hsu : entropyRate 625 (adjustedCoreRate u hdu) < 1) (hsv : entropyRate 625 (adjustedCoreRate v hdv) < 1)
    {base : Nat} (e : PlaquetteExpression base) (margin padding : Nat) :
    leEv (CReal.abs (CReal.sub (expressionMean v hv0 hv1 e (margin+padding))
      (expressionMean u hu0 hu1 e (margin+padding))))
      (ofQ' (localizedCap W u v hdu hdv hsu hsv e margin)) :=
  abs_chain
    (abs_chain (expressionMean_difference_bound v hv0 hv1 hsmallv hdv hsv e margin padding)
      (expressionMean_coupling_bound hu0 huv hvW hW1 e margin))
    (abs_reverse (expressionMean_difference_bound u hu0 hu1 hsmallu hdu hsu e margin padding))

end YMGap.Continuum.BF4ExactSlabLocalizedCouplingBound

#print axioms YMGap.Continuum.BF4ExactSlabLocalizedCouplingBound.windowCouplingCap
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedCouplingBound.expressionMean_coupling_bound
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedCouplingBound.boundaryCap
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedCouplingBound.localizedCap
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedCouplingBound.localized_coupling_bound
