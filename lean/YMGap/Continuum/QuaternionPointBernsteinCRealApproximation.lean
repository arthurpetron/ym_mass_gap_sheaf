/-
Polynomial approximation of supplied constructive-real functions on the dense
rational quaternion carrier. Each finite sample is taken at its OWN explicit
inner rate. A fixed sampling-noise floor is retained, not silently treated as
an all-tolerance rational continuity modulus. Both polynomial degree and
target-output row stage are computed. No continuous Haar, completed-function
representative choice, or physical mass-gap assertion occurs here.
-/

import YMGap.Constructive.CRealStableSampling
import YMGap.Continuum.QuaternionPointBernsteinApproximation

namespace YMGap.Continuum.QuaternionPointBernsteinCRealApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionPointBernsteinApproximation
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionNormRepair

local infix:50 " ≈ " => Q'.eqv

/-- One quarter of the requested total error is reserved for continuity. -/
def continuityTolerance (epsilon : Q') : Q' :=
  HalfPow.half * (HalfPow.half * epsilon)

/-- Each of the three sampling contributions is one twelfth of total error. -/
def sampleTolerance (epsilon : Q') : Q' := Q'.mkPos 1 12 (by decide) * epsilon

theorem continuityTolerance_positive (epsilon : Q') (he : (0 : Q') < epsilon) :
    (0 : Q') < continuityTolerance epsilon :=
  Q'.mul_pos (by decide) (Q'.mul_pos (by decide) he)

theorem sampleTolerance_positive (epsilon : Q') (he : (0 : Q') < epsilon) :
    (0 : Q') < sampleTolerance epsilon := Q'.mul_pos (by decide) he

/-- No modulus is extracted from the legacy propositional Cauchy field. -/
def sampledFunction (F : UnitNorm → CReal) (R : ∀ q, InnerRegularity (F q))
    (epsilon : Q') (q : UnitNorm) : Q' :=
  sample (F q) (R q) (sampleTolerance epsilon)

/-- Actual polynomial samples, with no nonpolynomial integration. -/
def realApproximationPolynomial (F : UnitNorm → CReal)
    (R : ∀ q, InnerRegularity (F q)) (epsilon : Q') (n : Nat) : RatPoly :=
  approximationPolynomial (sampledFunction F R epsilon) n

theorem realApproximation_supported (F : UnitNorm → CReal)
    (R : ∀ q, InnerRegularity (F q)) (epsilon : Q') (n : Nat) :
    SupportedQuaternionBlocks 1 (realApproximationPolynomial F R epsilon n) :=
  approximationPolynomial_supported _ n

/-- Degree stage uses the sampled bound, not the unsampled bound alone. -/
def realApproximationCutoff (M : Q') (radius : Q' → Q') (epsilon : Q') : Nat :=
  approximationCutoff (M + sampleTolerance epsilon)
    (radius (continuityTolerance epsilon)) epsilon

/-- Explicit target-output row stage, allowed to vary with the input point. -/
def realApproximationOutputRate (F : UnitNorm → CReal)
    (R : ∀ q, InnerRegularity (F q)) (epsilon : Q') (q : UnitNorm) : Nat :=
  (R q).rate (sampleTolerance epsilon)

private theorem errorBudget_pin (epsilon : Q') :
    ((continuityTolerance epsilon + 2*sampleTolerance epsilon) +
      HalfPow.half*epsilon) + sampleTolerance epsilon ≈ epsilon := by
  let H := HalfPow.half
  let T := Q'.mkPos 1 12 (by decide)
  have hring : ((H*(H*epsilon)+2*(T*epsilon))+H*epsilon)+T*epsilon ≈
      ((H*H+2*T)+H+T)*epsilon :=
    poly_identity_of_normal_eq
      (.add (.add
        (.add (.mul (.var 0) (.mul (.var 0) (.var 2)))
          (.mul (.const 2) (.mul (.var 1) (.var 2))))
        (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 2)))
      (.mul (.add (.add (.add (.mul (.var 0) (.var 0))
        (.mul (.const 2) (.var 1))) (.var 0)) (.var 1)) (.var 2))
      (by decide) (fun | 0 => H | 1 => T | _ => epsilon)
  exact Q'.eqv_trans _ _ _ hring
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ epsilon
        (by decide : (HalfPow.half*HalfPow.half +
          2*Q'.mkPos 1 12 (by decide) + HalfPow.half +
          Q'.mkPos 1 12 (by decide)) ≈ (1 : Q')))
      (Q'.one_mul_eqv epsilon))

/-- A rational estimate against every sufficiently late ACTUAL output row.
Only sound limit-level bounds and supplied data-level regularity are used;
arbitrarily irregular initial approximants are permitted. -/
theorem realApproximation_error_at_index (F : UnitNorm → CReal)
    (R : ∀ q, InnerRegularity (F q)) (M : Q') (radius : Q' → Q')
    (radius_positive : ∀ e, (0 : Q') < e → (0 : Q') < radius e)
    (hM : ∀ q, leRat (CReal.abs (F q)) M)
    (hmod : ∀ e, (0 : Q') < e → ∀ q x,
      distSq q.val x.val ≤ radius e →
        leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : realApproximationCutoff M radius epsilon ≤ n) (x : UnitNorm)
    (k : Nat) (hk : realApproximationOutputRate F R epsilon x ≤ k) :
    Q'.abs (evalRatPoly (environmentOf x.val)
      (realApproximationPolynomial F R epsilon n) + -(F x).approx k) ≤ epsilon := by
  let eta := continuityTolerance epsilon
  let tau := sampleTolerance epsilon
  let f := sampledFunction F R epsilon
  let p := realApproximationPolynomial F R epsilon n
  have heta : (0 : Q') < eta := continuityTolerance_positive epsilon he
  have htau : (0 : Q') < tau := sampleTolerance_positive epsilon he
  have hbound : ∀ q, Q'.abs (f q) ≤ M+tau :=
    fun q => sample_abs_le (F q) (R q) M tau (hM q) htau
  have hlocal : ∀ q x, distSq q.val x.val ≤ radius eta →
      Q'.abs (f q + -(f x)) ≤ eta+2*tau :=
    fun q x hqx => sample_difference_le (F q) (F x) (R q) (R x)
      eta tau (hmod eta heta q x hqx) htau
  have hnoise : (0 : Q') ≤ eta+2*tau :=
    Q'.le_trans' _ _ _ (Q'.le_of_lt heta)
      (Q'.add_le_self_of_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt htau)))
  have hkernel : Q'.abs (evalRatPoly (environmentOf x.val) p + -(f x)) ≤
      (eta+2*tau)+HalfPow.half*epsilon :=
    approximation_error_at_cutoff f (M+tau) (radius eta) (eta+2*tau)
      (radius_positive eta heta) hnoise hbound hlocal epsilon he n hn x
  have hsample : Q'.abs (f x + -(F x).approx k) ≤ tau :=
    sample_error_bound (F x) (R x) tau htau k hk
  have hpin : (evalRatPoly (environmentOf x.val) p + -(F x).approx k) ≈
      (evalRatPoly (environmentOf x.val) p + -(f x)) +
        (f x + -(F x).approx k) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 1) (.neg (.var 2))))
      (by decide) (fun
        | 0 => evalRatPoly (environmentOf x.val) p
        | 1 => f x
        | _ => (F x).approx k)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hkernel hsample)
        (Q'.le_of_eqv (errorBudget_pin epsilon))))

/-- Uniform finite polynomial approximation of the ACTUAL constructive-real
values. The target-row stage is the named data above, not an extracted witness.
This still does not assert approximation on every completed Point or Haar. -/
theorem realApproximation_error (F : UnitNorm → CReal)
    (R : ∀ q, InnerRegularity (F q)) (M : Q') (radius : Q' → Q')
    (radius_positive : ∀ e, (0 : Q') < e → (0 : Q') < radius e)
    (hM : ∀ q, leRat (CReal.abs (F q)) M)
    (hmod : ∀ e, (0 : Q') < e → ∀ q x,
      distSq q.val x.val ≤ radius e →
        leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : realApproximationCutoff M radius epsilon ≤ n) (x : UnitNorm) :
    leRat (CReal.abs (CReal.add
      (CReal.ofQ' (evalRatPoly (environmentOf x.val)
        (realApproximationPolynomial F R epsilon n))) (CReal.neg (F x)))) epsilon :=
  leRat_of_eventually ⟨realApproximationOutputRate F R epsilon x,
    fun k hk => realApproximation_error_at_index F R M radius radius_positive
      hM hmod epsilon he n hn x k hk⟩

end YMGap.Continuum.QuaternionPointBernsteinCRealApproximation

#print axioms YMGap.Continuum.QuaternionPointBernsteinCRealApproximation.continuityTolerance
#print axioms YMGap.Continuum.QuaternionPointBernsteinCRealApproximation.sampleTolerance
#print axioms YMGap.Continuum.QuaternionPointBernsteinCRealApproximation.continuityTolerance_positive
#print axioms YMGap.Continuum.QuaternionPointBernsteinCRealApproximation.sampleTolerance_positive
#print axioms YMGap.Continuum.QuaternionPointBernsteinCRealApproximation.sampledFunction
#print axioms YMGap.Continuum.QuaternionPointBernsteinCRealApproximation.realApproximationPolynomial
#print axioms YMGap.Continuum.QuaternionPointBernsteinCRealApproximation.realApproximation_supported
#print axioms YMGap.Continuum.QuaternionPointBernsteinCRealApproximation.realApproximationCutoff
#print axioms YMGap.Continuum.QuaternionPointBernsteinCRealApproximation.realApproximationOutputRate
#print axioms YMGap.Continuum.QuaternionPointBernsteinCRealApproximation.realApproximation_error_at_index
#print axioms YMGap.Continuum.QuaternionPointBernsteinCRealApproximation.realApproximation_error
