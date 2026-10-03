/-
# A negative cleared Ricci-two expression for the ORIGINAL guarded heat

On two explicit unit quaternions (identity, antipode), the SAME actual
heatAt and its selected upper angular jets satisfy h>0, Dh=0, D^2h>2h.
Consequently 2h^2+(Dh)^2-h D^2h is strictly negative at every K>=4,
including a computed K beyond the existing relative-derivative/head guards.
This is an evaluated ORIGINAL polynomial, not an inference about the
sign of curvature from a negative lower-bound coefficient.

The algebraic expression is the denominator-cleared Ricci-two test in
the unit-S^3 convention. No logarithm, division, analytic geometric
identification, or pointwise soundness of a Haar certificate is assumed.
No statement about the complete BF4 interacting weight, averaged signed
cost, physical generator or continuum theory follows from this example.
-/

import YMGap.Continuum.SU2QuaternionAntipodalHeatJets
import YMGap.Continuum.SU2QuaternionHeatLogCurvature
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.SU2QuaternionAntipodalCurvatureObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.HeatKernelRGStep (lt_of_lt_of_le)
open YMGap.Continuum.SU2HeatAntipodalPrefixBounds
open YMGap.Continuum.SU2QuaternionAntipodalHeatJets
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.RationalQuaternionRatPoly (evalRatPoly_neg)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (heatAt)
open YMGap.Continuum.SU2QuaternionHeatLogCurvature (logHessianNumerator)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv

/-- The literal original two-quaternion relative heat at the fixed nome. -/
def originalHeat (K : Nat) : RatPoly := heatAt 0 1 witnessNome K

/-- Original evaluated value, not an independently supplied scalar. -/
def originalValue (K : Nat) : Q' := evalRatPoly antipodalEnvironment (originalHeat K)

/-- Original evaluated second angular derivative in the selected upper plane. -/
def originalSecond (K : Nat) : Q' :=
  evalRatPoly antipodalEnvironment (upperAngular (upperAngular (originalHeat K)))

/-- The SAME polynomial log-Hessian numerator plus the Ricci-two term. -/
def clearedRicciTwo (K : Nat) : RatPoly :=
  polyAdd (polySmul 2 (polyMul (originalHeat K) (originalHeat K)))
    (polyNeg (logHessianNumerator (originalHeat K) 4 5 4 5))

theorem originalValue_positive (K : Nat) (hK : 4 ≤ K) :
    (0 : Q') < originalValue K :=
  lt_of_lt_of_le (endpointValue_positive K hK)
    (Q'.ge_of_eqv (heatAt_antipodal_value witnessNome K))

/-- The actual second jet crosses twice the actual positive heat value. -/
theorem originalSecond_gt_twice (K : Nat) (hK : 4 ≤ K) :
    2*originalValue K < originalSecond K := by
  apply Int.not_le.mp
  intro he
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ 3 he (by decide)
  have hbad : endpointSecondThree witnessNome K ≤ 6*endpointValue witnessNome K :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (heatAt_antipodal_second_three witnessNome K))
      (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.const 3) (.mul (.const 2) (.var 0)))
          (.mul (.const 6) (.var 0)) (by decide) (fun _ => originalValue K))
        (Q'.mul_eqv_congr_left 6 _ _ (heatAt_antipodal_value witnessNome K)))))
  exact (Int.not_le.mpr (endpointSecondThree_gt_six_value K hK)) hbad

private theorem clearedRicciTwo_eval (K : Nat) :
    evalRatPoly antipodalEnvironment (clearedRicciTwo K) ≈
      2*(originalValue K*originalValue K) + -(originalValue K*originalSecond K) := by
  unfold clearedRicciTwo logHessianNumerator
  have h0 := heatAt_antipodal_first witnessNome K
  have hs : evalRatPoly antipodalEnvironment
      (polyMul (upperAngular (originalHeat K)) (upperAngular (originalHeat K))) ≈ 0 :=
    Q'.eqv_trans _ _ _ (evalRatPoly_mul _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h0)
          (Q'.mul_eqv_congr_left _ _ _ h0)) (by decide))
  exact Q'.eqv_trans _ _ _ (evalRatPoly_add _ _ _)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (evalRatPoly_smul _ _ _)
        (Q'.mul_eqv_congr_left 2 _ _ (evalRatPoly_mul _ _ _)))
      (Q'.eqv_trans _ _ _ (evalRatPoly_neg _ _)
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (evalRatPoly_add _ _ _)
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (evalRatPoly_mul _ _ _)
              (Q'.eqv_trans _ _ _ (evalRatPoly_neg _ _)
                (Q'.neg_eqv_congr _ _ hs)))
            (poly_identity_of_normal_eq
              (.add (.var 0) (.neg (.const 0))) (.var 0)
              (by decide) (fun _ => originalValue K*originalSecond K)))))))

/-- An actual negative evaluation, uniformly in every later finite cutoff. -/
theorem clearedRicciTwo_negative (K : Nat) (hK : 4 ≤ K) :
    evalRatPoly antipodalEnvironment (clearedRicciTwo K) < (0 : Q') := by
  have hm := Q'.mul_lt_mul_of_pos_left (originalValue_positive K hK)
    (originalSecond_gt_twice K hK)
  have hmul : 2*(originalValue K*originalValue K) < originalValue K*originalSecond K :=
    Q'.lt_of_le_of_lt (Q'.ge_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.const 2) (.var 0)))
      (.mul (.const 2) (.mul (.var 0) (.var 0))) (by decide)
      (fun _ => originalValue K))) hm
  apply Int.not_le.mp
  intro hn
  have hh : (0 : Q') ≤
      2*(originalValue K*originalValue K) + -(originalValue K*originalSecond K) :=
    Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (clearedRicciTwo_eval K))
  have hbad : originalValue K*originalSecond K ≤ 2*(originalValue K*originalValue K) :=
    Q'.le_of_sub_nonneg hh
  exact (Int.not_le.mpr hmul) hbad

/-- Explicit admissible cutoff; no reduction of the potentially large guard is needed. -/
def guardedCutoff : Nat := max 4 (relativeCutoff witnessNome 32)

theorem guardedCutoff_relative : relativeCutoff witnessNome 32 ≤ guardedCutoff :=
  Nat.le_max_right _ _

theorem guardedCutoff_head : headCutoff witnessNome ≤ guardedCutoff :=
  Nat.le_trans (headCutoff_le_relativeCutoff witnessNome 32) guardedCutoff_relative

/-- The counterexample remains inside both existing original heat cutoff guards. -/
theorem guarded_original_negative :
    evalRatPoly antipodalEnvironment (clearedRicciTwo guardedCutoff) < (0 : Q') :=
  clearedRicciTwo_negative guardedCutoff (Nat.le_max_left _ _)

/-- Pointwise nonnegativity at even this literal admissible configuration is false. -/
theorem not_guarded_original_nonnegative :
    ¬ (0 : Q') ≤ evalRatPoly antipodalEnvironment (clearedRicciTwo guardedCutoff) :=
  Int.not_le.mpr guarded_original_negative

#print axioms originalValue_positive
#print axioms originalSecond_gt_twice
#print axioms clearedRicciTwo_negative
#print axioms guardedCutoff_relative
#print axioms guardedCutoff_head
#print axioms guarded_original_negative
#print axioms not_guarded_original_nonnegative

end YMGap.Continuum.SU2QuaternionAntipodalCurvatureObstruction
