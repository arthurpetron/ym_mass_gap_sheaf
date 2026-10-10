/-
Original polynomial comparison on the SAME completed quaternion carrier.
Sound dense error passes to the actual sampled extension, first at supplied
rows and then in the genuine RC order at EVERY Point. Zero dense error gives
equality with the existing pointEval. The already constructed Bernstein
polynomial is an actual quantitative instance, not an assumed approximation.
This is not continuous Haar, compactness, scaling or a mass-gap theorem.
-/

import YMGap.Continuum.QuaternionDenseCRealPointExtension
import YMGap.Continuum.QuaternionPointBernsteinCRealApproximation
import YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation

namespace YMGap.Continuum.QuaternionCompletedPolynomialApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionPointBernsteinCRealApproximation
open YMGap.Continuum.QuaternionDenseCRealPointExtension
open YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation
open YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionNormRepair
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup

local infix:50 " ≈ " => Q'.eqv

variable (F : UnitNorm → CReal) (R : ∀ q, InnerRegularity (F q))
variable (radius : Q' → Q')
variable (radius_positive : ∀ e, (0 : Q') < e → (0 : Q') < radius e)
variable (hmod : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ radius e →
    leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)

private theorem environment_pin (q : RationalQuaternion) :
    quaternionCoordinates q = environmentOf q := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | k+4 =>
      have hk : ¬ k+4 < 4 := by omega
      simp [quaternionCoordinates, environmentOf, hk]

private theorem rowPolynomial_environment (X : CauchyPoint) (p : RatPoly) (n : Nat) :
    (rowPolynomialEval X p).approx n =
      evalRatPoly (environmentOf (X.seq n).val) p := by
  rw [rowPolynomialEval_approx, environment_pin]

private theorem distance_symm {x y : CReal} {eta : Q'}
    (h : leRat (CReal.abs (CReal.add x (CReal.neg y))) eta) :
    leRat (CReal.abs (CReal.add y (CReal.neg x))) eta := by
  intro e he
  obtain ⟨K, hK⟩ := h e he
  refine ⟨K, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) (hK n hn)

private theorem sample_budget (eta e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : (HalfPow.half*e).den ≤ n) :
    (eta + Q'.invSucc n) + Q'.invSucc n ≤ eta + e := by
  have hs : Q'.invSucc n ≤ HalfPow.half*e :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
      (HalfPow.invSucc_den_le _ (Q'.mul_pos (by decide) he))
  have ht : Q'.invSucc n + Q'.invSucc n ≤ e :=
    Q'.le_trans' _ _ _ (Q'.add_le_add hs hs)
      (Q'.le_of_eqv (ExpNeg.two_halves e))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_assoc_eqv eta (Q'.invSucc n) (Q'.invSucc n)))
    (Q'.add_le_add_left _ _ _ ht)

/-- The computed row value is close to the ACTUAL original polynomial row.
Both sampling errors are retained; the polynomial constant is not a new
target-output hypothesis. -/
theorem rowPolynomial_distance_at_index (X : CauchyPoint) (p : RatPoly) (eta : Q')
    (hclose : ∀ q : UnitNorm,
      leRat (CReal.abs (CReal.add (F q)
        (CReal.neg (CReal.ofQ' (evalRatPoly (environmentOf q.val) p))))) eta)
    (n : Nat) :
    Q'.abs ((rowImage F R radius radius_positive hmod X).approx n +
      -((rowPolynomialEval X p).approx n)) ≤
        (eta + Q'.invSucc n) + Q'.invSucc n := by
  rw [rowPolynomial_environment]
  exact sample_difference_le_asymmetric
    (F (X.seq n)) (CReal.ofQ' (evalRatPoly (environmentOf (X.seq n).val) p))
    (R (X.seq n)) (InnerRegularity.ofQ' _)
    eta (Q'.invSucc n) (Q'.invSucc n) (hclose (X.seq n))
    (Q'.invSucc_pos n) (Q'.invSucc_pos n)

/-- Sound dense error eta survives on every supplied completion row.
Only the sample tail vanishes, at the computed cutoff (epsilon/2).den. -/
theorem rowPolynomial_distance (X : CauchyPoint) (p : RatPoly) (eta : Q')
    (hclose : ∀ q : UnitNorm,
      leRat (CReal.abs (CReal.add (F q)
        (CReal.neg (CReal.ofQ' (evalRatPoly (environmentOf q.val) p))))) eta) :
    leRat (CReal.abs (CReal.add
      (rowImage F R radius radius_positive hmod X)
      (CReal.neg (rowPolynomialEval X p)))) eta := by
  intro e he
  refine ⟨(HalfPow.half*e).den, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _
    (rowPolynomial_distance_at_index F R radius radius_positive hmod X p eta hclose n)
    (sample_budget eta e he n hn)

private theorem order_pair {a b : CReal} {eta : Q'}
    (h : leRat (CReal.abs (CReal.add a (CReal.neg b))) eta) :
    leEv a (CReal.add b (CReal.ofQ' eta)) ∧
      leEv b (CReal.add a (CReal.ofQ' eta)) := by
  have forward (u v : CReal)
      (hu : leRat (CReal.abs (CReal.add u (CReal.neg v))) eta) :
      leEv u (CReal.add v (CReal.ofQ' eta)) := by
    intro e he
    obtain ⟨K, hK⟩ := hu e he
    refine ⟨K, fun n hn => ?_⟩
    exact Q'.le_trans' _ _ _ (ExpNeg.le_add_of_abs_sub_le (hK n hn))
      (Q'.ge_of_eqv (Q'.add_assoc_eqv (v.approx n) eta e))
  exact ⟨forward a b h, forward b a (distance_symm h)⟩

/-- Genuine RC-valued two-sided approximation at EVERY completed Point,
on the EXISTING pointEval. This is not a representative-row-only claim. -/
theorem pointPolynomial_distance (p : RatPoly) (eta : Q')
    (hclose : ∀ q : UnitNorm,
      leRat (CReal.abs (CReal.add (F q)
        (CReal.neg (CReal.ofQ' (evalRatPoly (environmentOf q.val) p))))) eta)
    (x : Point) :
    RCle (pointExtension F R radius radius_positive hmod x)
      (RCadd (pointEval x p) (rational eta)) ∧
    RCle (pointEval x p)
      (RCadd (pointExtension F R radius radius_positive hmod x) (rational eta)) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [pointExtension_mk, pointEval_rowPolynomialEval]
  exact order_pair (rowPolynomial_distance F R radius radius_positive hmod X p eta hclose)

/-- Exact dense INPUT values force equality with the SAME polynomial
evaluation on all completed Points, not merely on embedded rationals. -/
theorem pointPolynomial_compatible (p : RatPoly)
    (hpin : ∀ q : UnitNorm,
      leRat (CReal.abs (CReal.add (F q)
        (CReal.neg (CReal.ofQ' (evalRatPoly (environmentOf q.val) p))))) 0)
    (x : Point) :
    pointExtension F R radius radius_positive hmod x = pointEval x p := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [pointExtension_mk, pointEval_rowPolynomialEval]
  apply Quotient.sound
  apply Equiv_of_abs_sub_le_all_pos
  intro e he
  exact leRat_mono (rowPolynomial_distance F R radius radius_positive hmod X p 0 hpin)
    (Q'.le_of_lt he)

/-- The ACTUAL constructed Bernstein polynomial approximates the extension
uniformly on every Point at the existing computed degree cutoff. All function
bounds and moduli are input data; completed approximation is an output. -/
theorem pointBernstein_approximation (M : Q') (hM : ∀ q, leRat (CReal.abs (F q)) M)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : realApproximationCutoff M radius epsilon ≤ n) (x : Point) :
    RCle (pointExtension F R radius radius_positive hmod x)
      (RCadd (pointEval x (realApproximationPolynomial F R epsilon n)) (rational epsilon)) ∧
    RCle (pointEval x (realApproximationPolynomial F R epsilon n))
      (RCadd (pointExtension F R radius radius_positive hmod x) (rational epsilon)) := by
  apply pointPolynomial_distance F R radius radius_positive hmod _ epsilon _ x
  intro q
  exact distance_symm (realApproximation_error F R M radius radius_positive hM hmod
    epsilon he n hn q)

#print axioms rowPolynomial_distance_at_index
#print axioms rowPolynomial_distance
#print axioms pointPolynomial_distance
#print axioms pointPolynomial_compatible
#print axioms pointBernstein_approximation

end YMGap.Continuum.QuaternionCompletedPolynomialApproximation
