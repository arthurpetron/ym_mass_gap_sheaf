/-
ACTUAL rational constant input for the original-Haar candidate: its bound,
inner rate and continuity radius are produced, not assumed. Original constant
polynomial moments and dense approximation give its value; the actual Point
extension is also constant on EVERY supplied row, without representative
choice. This proves normalization, not continuous invariance, compact matrix
realization, J04 or any physical/Clay closure.
-/

import YMGap.Constructive.TrigAdd
import YMGap.Continuum.QuaternionDenseCRealHaarComparison

namespace YMGap.Continuum.QuaternionDenseCRealHaarNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionDenseCRealHaarApproximation
open YMGap.Continuum.QuaternionDenseCRealHaarComparison
open YMGap.Continuum.QuaternionDenseCRealPointExtension
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup

local infix:50 " ≈ " => Q'.eqv

/-- Constant VALUES on the actual dense rational quaternion carrier. -/
def constantInput (c : Q') (_q : UnitNorm) : CReal := CReal.ofQ' c

/-- The explicit inner rate is zero at every tolerance and every point. -/
def constantInner (c : Q') : ∀ q, InnerRegularity (constantInput c q) :=
  fun _ => InnerRegularity.ofQ' c

/-- A positive radius is produced even for zero/negative constant inputs. -/
def constantRadius (_epsilon : Q') : Q' := 1

theorem constantRadius_positive (e : Q') (_he : (0 : Q') < e) :
    (0 : Q') < constantRadius e := by
  change (0 : Q') < 1
  decide

theorem constant_bound (c : Q') (q : UnitNorm) :
    leRat (CReal.abs (constantInput c q)) (Q'.abs c) :=
  leRat_ofQ' (Q'.le_refl' _)

/-- The radius produces sound continuity; no polynomial or integral equality
is an input. Constant values have zero distance at every approximation. -/
theorem constant_modulus (c : Q') (e : Q') (he : (0 : Q') < e)
    (q x : UnitNorm) (_hd : distSq q.val x.val ≤ constantRadius e) :
    leRat (CReal.abs (CReal.add (constantInput c q)
      (CReal.neg (constantInput c x)))) e :=
  leRat_mono (self_input_distance_zero (CReal.ofQ' c)) (Q'.le_of_lt he)

theorem constantPolynomial_supported (c : Q') :
    SupportedQuaternionBlocks 1 (polyConst c) := by
  intro term hterm
  have h : term = ([], c) := List.mem_singleton.mp hterm
  subst term
  exact Nat.zero_le _

/-- Setoid evaluation pin; no canonical representation of c is required. -/
theorem constantPolynomial_eval (rho : Nat → Q') (c : Q') :
    evalRatPoly rho (polyConst c) ≈ c := by
  change c*1+0 ≈ c
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ 0 (Q'.mul_one_eqv c)) (QPoly.q_add_zero_eqv c)

/-- The ORIGINAL polynomial moments, not an assumed continuous integral. -/
theorem constantPolynomial_haar (blocks : Nat) (c : Q') :
    quaternionHaar blocks (polyConst c) ≈ c := by
  change c*quaternionHaarMono blocks []+0 ≈ c
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ 0
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left c _ _ (quaternionHaarMono_one blocks))
        (Q'.mul_one_eqv c))) (QPoly.q_add_zero_eqv c)

/-- Exact INPUT identification with the constant polynomial, derived here.
This is not an assumed identity for the proposed integral's output. -/
theorem constantPolynomial_distance_zero (c : Q') (q : UnitNorm) :
    leRat (CReal.abs (CReal.add (constantInput c q)
      (CReal.neg (CReal.ofQ' (evalRatPoly (environmentOf q.val) (polyConst c)))))) 0 := by
  apply leRat_of_eventually
  refine ⟨0, fun _ _ => ?_⟩
  have hzero : c + -(evalRatPoly (environmentOf q.val) (polyConst c)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left c _ _
        (Q'.neg_eqv_congr _ _ (constantPolynomial_eval _ c)))
      (Q'.add_neg_self_eqv c)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hzero))
    (by decide : Q'.abs (0 : Q') ≤ 0)

/-- Apply the existing ORIGINAL-Haar construction using only produced data. -/
def constantHaar (c : Q') : CReal :=
  haarApproximationReal (constantInput c) (constantInner c) (Q'.abs c)
    constantRadius constantRadius_positive (constant_bound c) (constant_modulus c)

/-- Retained candidate rate: den(epsilon/2), not extracted from Prop. -/
def constantHaarInnerRegularity (c : Q') : InnerRegularity (constantHaar c) :=
  haarApproximationInnerRegularity (constantInput c) (constantInner c) (Q'.abs c)
    constantRadius constantRadius_positive (constant_bound c) (constant_modulus c)

/-- ACTUAL constant-input normalization, including arbitrary signed c.
The candidate value is a conclusion, never a premise. -/
theorem constantHaar_value (c : Q') : Equiv (constantHaar c) (CReal.ofQ' c) :=
  Equiv.trans
    (haarApproximation_polynomial_compatible (constantInput c) (constantInner c)
      (Q'.abs c) constantRadius constantRadius_positive (constant_bound c)
      (constant_modulus c) (polyConst c) (constantPolynomial_supported c)
      (constantPolynomial_distance_zero c))
    (TrigAdd.equiv_ofQ'_of_eqv (constantPolynomial_haar 1 c))

/-- Genuine quotient equality; c=1 is the unital normalization instance. -/
theorem constantHaar_quotient_value (c : Q') :
    Quotient.mk crealSetoid (constantHaar c) =
      Quotient.mk crealSetoid (CReal.ofQ' c) :=
  Quotient.sound (constantHaar_value c)

/-- The ACTUAL completed map is constant at every Point, not only at dense
embeddings. Its row image literally samples the constant at the produced rate. -/
theorem constantExtension_value (c : Q') (x : Point) :
    pointExtension (constantInput c) (constantInner c) constantRadius
      constantRadius_positive (constant_modulus c) x =
        Quotient.mk crealSetoid (CReal.ofQ' c) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [pointExtension_mk]
  apply Quotient.sound
  exact Equiv_of_approx_eq (fun _ => rfl)

#print axioms constantInput
#print axioms constantInner
#print axioms constantRadius
#print axioms constantRadius_positive
#print axioms constant_bound
#print axioms constant_modulus
#print axioms constantPolynomial_supported
#print axioms constantPolynomial_eval
#print axioms constantPolynomial_haar
#print axioms constantPolynomial_distance_zero
#print axioms constantHaar
#print axioms constantHaarInnerRegularity
#print axioms constantHaar_value
#print axioms constantHaar_quotient_value
#print axioms constantExtension_value

end YMGap.Continuum.QuaternionDenseCRealHaarNormalization
