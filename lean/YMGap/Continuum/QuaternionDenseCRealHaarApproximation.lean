/-
A constructive real candidate obtained by applying the ORIGINAL one-block
polynomial Haar to computed approximants of supplied dense-carrier CReal data.
The function bound, continuity radius, and inner regularity are actual input
data; no estimate on arbitrary completed Point functions is postulated.
This is not a continuous Haar functional on all Point functions, nor J04.
-/

import YMGap.Continuum.QuaternionPointBernsteinCRealApproximation
import YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid

namespace YMGap.Continuum.QuaternionDenseCRealHaarApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialGrid
open YMGap.Continuum.QuaternionPointBernsteinCRealApproximation
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets

local infix:50 " ≈ " => Q'.eqv

variable (F : UnitNorm → CReal) (R : ∀ q, InnerRegularity (F q))
variable (M : Q') (radius : Q' → Q')
variable (radius_positive : ∀ e, (0 : Q') < e → (0 : Q') < radius e)
variable (hM : ∀ q, leRat (CReal.abs (F q)) M)
variable (hmod : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ radius e →
    leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)

/-- At stage `k`, both the sample precision and polynomial degree are
computed from the positive rational tolerance `1/(k+1)`. -/
def haarApproximationPolynomial (k : Nat) : RatPoly :=
  realApproximationPolynomial F R (Q'.invSucc k)
    (realApproximationCutoff M radius (Q'.invSucc k))

/-- Only the original polynomial quaternion Haar is applied. -/
def haarApproximationValue (k : Nat) : Q' :=
  quaternionHaar 1 (haarApproximationPolynomial F R M radius k)

private theorem supported_neg {p : RatPoly}
    (hp : SupportedQuaternionBlocks 1 p) :
    SupportedQuaternionBlocks 1 (polyNeg p) := by
  intro term hterm
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  exact hp source hsource

private theorem haar_neg : ∀ p : RatPoly,
    quaternionHaar 1 (polyNeg p) ≈ -quaternionHaar 1 p
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono 1 t.1))
        (haar_neg rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem eval_difference (q : UnitNorm) (p s : RatPoly) :
    evalRatPoly (environmentOf q.val) (polyAdd p (polyNeg s)) ≈
      evalRatPoly (environmentOf q.val) p +
        -(evalRatPoly (environmentOf q.val) s) :=
  Q'.eqv_trans _ _ _ (evalRatPoly_add _ _ _)
    (Q'.add_eqv_congr_left _ _ _ (evalRatPoly_neg _ s))

private theorem haar_difference (p s : RatPoly) :
    quaternionHaar 1 (polyAdd p (polyNeg s)) ≈
      quaternionHaar 1 p + -(quaternionHaar 1 s) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append 1 _ _)
    (Q'.add_eqv_congr_left _ _ _ (haar_neg s))

include radius_positive hM hmod in
/-- Two computed ORIGINAL Haar stages differ by the sum of their requested
pointwise errors. The output-row index at each test quaternion is the maximum
of two computed rates, not an existential index extracted from `CReal.cauchy`. -/
theorem haarApproximation_difference (m n : Nat) :
    Q'.abs (haarApproximationValue F R M radius m +
      -(haarApproximationValue F R M radius n)) ≤
      Q'.invSucc m + Q'.invSucc n := by
  let pm := haarApproximationPolynomial F R M radius m
  let pn := haarApproximationPolynomial F R M radius n
  let em := Q'.invSucc m
  let en := Q'.invSucc n
  let d := polyAdd pm (polyNeg pn)
  have hd : SupportedQuaternionBlocks 1 d :=
    supported_add (realApproximation_supported F R em _)
      (supported_neg (realApproximation_supported F R en _))
  have hpoint (q : UnitNorm) :
      Q'.abs (evalRatPoly (environmentOf q.val) d) ≤ em+en := by
    let j := max (realApproximationOutputRate F R em q)
      (realApproximationOutputRate F R en q)
    have hm : Q'.abs (evalRatPoly (environmentOf q.val) pm + -(F q).approx j) ≤ em :=
      realApproximation_error_at_index F R M radius radius_positive hM hmod
        em (Q'.invSucc_pos m) _ (Nat.le_refl _) q j (Nat.le_max_left _ _)
    have hn : Q'.abs (evalRatPoly (environmentOf q.val) pn + -(F q).approx j) ≤ en :=
      realApproximation_error_at_index F R M radius radius_positive hM hmod
        en (Q'.invSucc_pos n) _ (Nat.le_refl _) q j (Nat.le_max_right _ _)
    have hpin : evalRatPoly (environmentOf q.val) pm +
        -(evalRatPoly (environmentOf q.val) pn) ≈
        (evalRatPoly (environmentOf q.val) pm + -(F q).approx j) +
          ((F q).approx j + -(evalRatPoly (environmentOf q.val) pn)) :=
      poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.var 1)))
        (.add (.add (.var 0) (.neg (.var 2)))
          (.add (.var 2) (.neg (.var 1))))
        (by decide)
        (fun | 0 => evalRatPoly (environmentOf q.val) pm
             | 1 => evalRatPoly (environmentOf q.val) pn
             | _ => (F q).approx j)
    have hback : Q'.abs ((F q).approx j +
        -(evalRatPoly (environmentOf q.val) pn)) ≤ en :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hn
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_eqv_congr (Q'.eqv_trans _ _ _
        (eval_difference q pm pn) hpin)))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
        (Q'.add_le_add hm hback))
  have hhaar := haar_abs_le_unit_bound d hd (em+en) hpoint
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr (Q'.eqv_symm (haar_difference pm pn))))
    hhaar

/-- A recoverable Cauchy cutoff for the original-Haar approximant sequence. -/
def haarApproximationRate (epsilon : Q') : Nat :=
  (HalfPow.half*epsilon).den

include radius_positive hM hmod in
theorem haarApproximation_regular (epsilon : Q')
    (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : haarApproximationRate epsilon ≤ m)
    (hn : haarApproximationRate epsilon ≤ n) :
    haarApproximationValue F R M radius m ≤
      haarApproximationValue F R M radius n + epsilon ∧
    haarApproximationValue F R M radius n ≤
      haarApproximationValue F R M radius m + epsilon := by
  have hhalf : (0 : Q') < HalfPow.half*epsilon := Q'.mul_pos (by decide) he
  have hfloor := HalfPow.invSucc_den_le (HalfPow.half*epsilon) hhalf
  have hmm : Q'.invSucc m ≤ HalfPow.half*epsilon :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hm) hfloor
  have hnn : Q'.invSucc n ≤ HalfPow.half*epsilon :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn) hfloor
  have hdiff : Q'.abs (haarApproximationValue F R M radius m +
      -(haarApproximationValue F R M radius n)) ≤ epsilon :=
    Q'.le_trans' _ _ _
      (haarApproximation_difference F R M radius radius_positive hM hmod m n)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hmm hnn)
        (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))
  exact ⟨ExpNeg.le_add_of_abs_sub_le hdiff,
    ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hdiff)⟩

include radius_positive hM hmod in
/-- The computed original-Haar values form an actual constructive real.
Only the legacy `CReal.cauchy` proof field is propositional; the recoverable
rate is separately retained below as `InnerRegularity`. -/
def haarApproximationReal : CReal where
  approx := haarApproximationValue F R M radius
  cauchy := fun epsilon he => ⟨haarApproximationRate epsilon,
    haarApproximation_regular F R M radius radius_positive hM hmod epsilon he⟩

include radius_positive hM hmod in
def haarApproximationInnerRegularity :
    InnerRegularity
      (haarApproximationReal F R M radius radius_positive hM hmod) where
  rate := haarApproximationRate
  regular := haarApproximation_regular F R M radius radius_positive hM hmod

#print axioms haarApproximationPolynomial
#print axioms haarApproximationValue
#print axioms haarApproximation_difference
#print axioms haarApproximationRate
#print axioms haarApproximation_regular
#print axioms haarApproximationReal
#print axioms haarApproximationInnerRegularity

end YMGap.Continuum.QuaternionDenseCRealHaarApproximation
