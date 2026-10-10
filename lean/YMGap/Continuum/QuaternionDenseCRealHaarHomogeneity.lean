/-
Actual signed scalar multiplication of admissible dense CReal data, with
produced bounds, continuity radii and inner rates. Original polynomial
evaluation and Haar scalar pins compare the independently constructed stages;
the explicit full-error cutoff gives their scalar law. No sampled-polynomial
identity or proposed integral answer is assumed. Continuous invariance, J04,
MAIN scaling and all physical/Clay conclusions remain open.
-/

import YMGap.Constructive.CRealInnerRegularity
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealLe
import YMGap.Constructive.CRealExp
import YMGap.Constructive.ExpAdd
import YMGap.Continuum.QuaternionDenseCRealHaarNormalization

namespace YMGap.Continuum.QuaternionDenseCRealHaarHomogeneity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionPointBernsteinCRealApproximation
open YMGap.Continuum.QuaternionDenseCRealHaarApproximation
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets

local infix:50 " ≈ " => Q'.eqv

/-- Signed scalar multiplication preserves a sound absolute bound, including
zero and negative scalars.  The error is paid at the computed tolerance for
the nonnegative Lipschitz constant `abs c`. -/
theorem scale_abs_bound (c : Q') {x : CReal} {M : Q'}
    (h : leRat (CReal.abs x) M) :
    leRat (CReal.abs (CReal.mul (CReal.ofQ' c) x)) (Q'.abs c * M) := by
  intro epsilon hepsilon
  let theta := InnerRegularity.scaleTolerance (Q'.abs c) epsilon
  have htheta : (0 : Q') < theta :=
    InnerRegularity.scaleTolerance_pos (Q'.abs c) epsilon hepsilon
  have hscale : Q'.abs c * theta ≤ epsilon :=
    InnerRegularity.mul_scaleTolerance_le (Q'.abs c) epsilon
      (Q'.abs_nonneg c) hepsilon
  obtain ⟨N, hN⟩ := h theta htheta
  refine ⟨N, fun n hn => ?_⟩
  change Q'.abs (c * x.approx n) ≤ Q'.abs c * M + epsilon
  have hxn : Q'.abs (x.approx n) ≤ M + theta := by
    simpa only [CReal.abs_approx] using hN n hn
  have hprod : Q'.abs (c * x.approx n) ≤ Q'.abs c * Q'.abs (x.approx n) :=
    ExpNeg.abs_mul_le c (x.approx n)
  have hbound : Q'.abs c * Q'.abs (x.approx n) ≤ Q'.abs c * (M + theta) :=
    Q'.mul_le_mul_of_nonneg_left (Q'.abs (x.approx n)) (M + theta)
      (Q'.abs c) hxn (Q'.abs_nonneg c)
  have hdist : (Q'.abs c * (M + theta)).eqv
      (Q'.abs c * M + Q'.abs c * theta) :=
    Q'.mul_add_eqv (Q'.abs c) M theta
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_trans' _ _ _ hbound
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hdist)
        (Q'.add_le_add_left (Q'.abs c * M) (Q'.abs c * theta) epsilon hscale)))

/-- Absolute distance between the actual scalar-multiplied inputs is bounded
by `abs c` times the original sound distance. -/
theorem scale_distance (c : Q') {u v : CReal} {eta : Q'}
    (h : leRat (CReal.abs (CReal.add u (CReal.neg v))) eta) :
    leRat
      (CReal.abs (CReal.add (CReal.mul (CReal.ofQ' c) u)
        (CReal.neg (CReal.mul (CReal.ofQ' c) v))))
      (Q'.abs c * eta) := by
  have heq : CReal.Equiv
      (CReal.add (CReal.mul (CReal.ofQ' c) u)
        (CReal.neg (CReal.mul (CReal.ofQ' c) v)))
      (CReal.mul (CReal.ofQ' c) (CReal.add u (CReal.neg v))) := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    show (c * u.approx n + -(c * v.approx n)).eqv
      (c * (u.approx n + -(v.approx n)))
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.mul_neg_eqv c (v.approx n))))
      (Q'.eqv_symm (Q'.mul_add_eqv c (u.approx n) (-(v.approx n))))
  exact CReal.leRat_of_equiv (CReal.abs_equiv_congr heq)
    (scale_abs_bound c h)

/-- Actual pointwise scalar multiple on the dense rational unit carrier. -/
def scaleInput (c : Q') (F : UnitNorm → CReal) (q : UnitNorm) : CReal :=
  CReal.mul (CReal.ofQ' c) (F q)

/-- The scalar-multiplied input retains a computed Type-level inner rate. -/
def scaleInner (c : Q') (F : UnitNorm → CReal)
    (R : ∀ q, InnerRegularity (F q)) :
    ∀ q, InnerRegularity (scaleInput c F q) :=
  fun q => InnerRegularity.scaleLeftSigned (R q) c

/-- Rescaled radius pays the existing modulus at the computed smaller tolerance. -/
def scaleRadius (c : Q') (radius : Q' → Q') (epsilon : Q') : Q' :=
  radius (InnerRegularity.scaleTolerance (Q'.abs c) epsilon)

theorem scaleRadius_positive (c : Q') (radius : Q' → Q')
    (radius_positive : ∀ e, (0 : Q') < e → (0 : Q') < radius e)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < scaleRadius c radius epsilon :=
  radius_positive _ (InnerRegularity.scaleTolerance_pos (Q'.abs c) epsilon hepsilon)

/-- Sound absolute bound for the actual scalar-multiplied input. -/
theorem scale_bound (c : Q') (F : UnitNorm → CReal) (M : Q')
    (bound : ∀ q, leRat (CReal.abs (F q)) M) (q : UnitNorm) :
    leRat (CReal.abs (scaleInput c F q)) (Q'.abs c * M) :=
  scale_abs_bound c (bound q)

/-- The computed scaled radius yields the sound requested continuity error. -/
theorem scale_modulus (c : Q') (F : UnitNorm → CReal) (radius : Q' → Q')
    (modulus : ∀ e, (0 : Q') < e → ∀ q x,
      distSq q.val x.val ≤ radius e →
        leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (q x : UnitNorm)
    (hd : distSq q.val x.val ≤ scaleRadius c radius epsilon) :
    leRat (CReal.abs (CReal.add (scaleInput c F q)
      (CReal.neg (scaleInput c F x)))) epsilon := by
  have hscaled := scale_distance c
    (modulus (InnerRegularity.scaleTolerance (Q'.abs c) epsilon)
      (InnerRegularity.scaleTolerance_pos (Q'.abs c) epsilon hepsilon)
      q x hd)
  exact leRat_mono hscaled
    (InnerRegularity.mul_scaleTolerance_le (Q'.abs c) epsilon
      (Q'.abs_nonneg c) hepsilon)

private theorem distance_symm {a b : CReal} {eta : Q'}
    (h : leRat (CReal.abs (CReal.add a (CReal.neg b))) eta) :
    leRat (CReal.abs (CReal.add b (CReal.neg a))) eta := by
  intro e he
  obtain ⟨K, hK⟩ := h e he
  refine ⟨K, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) (hK n hn)

variable (c : Q') (F : UnitNorm → CReal) (R : ∀ q, InnerRegularity (F q))
variable (M : Q') (radius : Q' → Q')
variable (radius_positive : ∀ e, (0 : Q') < e → (0 : Q') < radius e)
variable (hM : ∀ q, leRat (CReal.abs (F q)) M)
variable (hmod : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ radius e →
    leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)

/-- ORIGINAL Haar applied to the actual scaled input with only produced data. -/
def scaleHaar : CReal :=
  haarApproximationReal (scaleInput c F) (scaleInner c F R) (Q'.abs c * M)
    (scaleRadius c radius) (scaleRadius_positive c radius radius_positive)
    (scale_bound c F M hM) (scale_modulus c F radius hmod)

/-- The actual scaled candidate retains its computed den(epsilon/2) inner rate. -/
def scaleHaarInnerRegularity :
    InnerRegularity (scaleHaar c F R M radius radius_positive hM hmod) :=
  haarApproximationInnerRegularity (scaleInput c F) (scaleInner c F R) (Q'.abs c * M)
    (scaleRadius c radius) (scaleRadius_positive c radius radius_positive)
    (scale_bound c F M hM) (scale_modulus c F radius hmod)

include radius_positive hM hmod in
/-- The independently constructed stages agree up to their FULL scalar error.
Only original polynomial evaluation and moment identities are used. -/
theorem scaleHaar_stage (n : Nat) :
    Q'.abs (haarApproximationValue (scaleInput c F) (scaleInner c F R)
      (Q'.abs c * M) (scaleRadius c radius) n +
      -(c * haarApproximationValue F R M radius n)) ≤
      Q'.invSucc n + Q'.abs c * Q'.invSucc n := by
  let tau := Q'.invSucc n
  let pf := haarApproximationPolynomial F R M radius n
  let p := polySmul c pf
  have hpf : SupportedQuaternionBlocks 1 pf :=
    realApproximation_supported F R tau _
  have hp : SupportedQuaternionBlocks 1 p := by
    intro term ht
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
    exact hpf source hs
  have hclose (q : UnitNorm) :
      leRat (CReal.abs (CReal.add (scaleInput c F q)
        (CReal.neg (CReal.ofQ' (evalRatPoly (environmentOf q.val) p)))))
        (Q'.abs c * tau) := by
    have hf := distance_symm
      (realApproximation_error F R M radius radius_positive hM hmod
        tau (Q'.invSucc_pos n) _ (Nat.le_refl _) q)
    have hs := scale_distance c hf
    intro e he
    obtain ⟨K, hK⟩ := hs e he
    refine ⟨K, fun j hj => ?_⟩
    have hpin : c * (F q).approx j + -(evalRatPoly (environmentOf q.val) p) ≈
        c * (F q).approx j + -(c * evalRatPoly (environmentOf q.val) pf) :=
      Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (evalRatPoly_smul _ c pf))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin)) (hK j hj)
  have hb := haarApproximation_polynomial_distance
    (scaleInput c F) (scaleInner c F R) (Q'.abs c * M) (scaleRadius c radius)
    (scaleRadius_positive c radius radius_positive) (scale_bound c F M hM)
    (scale_modulus c F radius hmod) p hp (Q'.abs c * tau) hclose n
  have hpin : haarApproximationValue (scaleInput c F) (scaleInner c F R)
      (Q'.abs c * M) (scaleRadius c radius) n + -(quaternionHaar 1 p) ≈
      haarApproximationValue (scaleInput c F) (scaleInner c F R)
        (Q'.abs c * M) (scaleRadius c radius) n +
        -(c * haarApproximationValue F R M radius n) :=
    Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (quaternionHaar_polySmul 1 c pf))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr (Q'.eqv_symm hpin))) hb

/-- Recoverable cutoff for the FULL stage error, valid for any signed scalar. -/
def scaleHaarEqualityRate (c epsilon : Q') : Nat :=
  (InnerRegularity.scaleTolerance (1 + Q'.abs c) epsilon).den

private theorem scale_tail_budget (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : scaleHaarEqualityRate c epsilon ≤ n) :
    Q'.invSucc n + Q'.abs c * Q'.invSucc n ≤ epsilon := by
  let A := (1 : Q') + Q'.abs c
  let theta := InnerRegularity.scaleTolerance A epsilon
  have hA : (0 : Q') ≤ A :=
    Q'.zero_le_add 1 (Q'.abs c) (by decide) (Q'.abs_nonneg c)
  have ht : (0 : Q') < theta :=
    InnerRegularity.scaleTolerance_pos A epsilon he
  have hs : Q'.invSucc n ≤ theta :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
      (HalfPow.invSucc_den_le theta ht)
  have hpin : Q'.invSucc n + Q'.abs c * Q'.invSucc n ≈ A * Q'.invSucc n :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _)))
      (Q'.eqv_symm (Q'.add_mul_eqv 1 (Q'.abs c) (Q'.invSucc n)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ A hs hA)
      (InnerRegularity.mul_scaleTolerance_le A epsilon hA he))

/-- Actual signed rational homogeneity; no scalar admissibility or integral
identity is assumed. The explicit rate removes both approximation errors. -/
theorem scaleHaar_homogeneous :
    Equiv (scaleHaar c F R M radius radius_positive hM hmod)
      (CReal.mul (CReal.ofQ' c)
        (haarApproximationReal F R M radius radius_positive hM hmod)) := by
  intro epsilon he
  refine ⟨scaleHaarEqualityRate c epsilon, fun n hn => ?_⟩
  have hb := Q'.le_trans' _ _ _
    (scaleHaar_stage c F R M radius radius_positive hM hmod n)
    (scale_tail_budget c epsilon he n hn)
  exact ⟨ExpNeg.le_add_of_abs_sub_le hb,
    ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hb)⟩

#print axioms scale_abs_bound
#print axioms scale_distance
#print axioms scaleInput
#print axioms scaleInner
#print axioms scaleRadius
#print axioms scaleRadius_positive
#print axioms scale_bound
#print axioms scale_modulus
#print axioms scaleHaar
#print axioms scaleHaarInnerRegularity
#print axioms scaleHaar_stage
#print axioms scaleHaarEqualityRate
#print axioms scaleHaar_homogeneous

end YMGap.Continuum.QuaternionDenseCRealHaarHomogeneity
