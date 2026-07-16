/-
# CReal Cauchy--Schwarz and radical descent for the strict OS cylinder form

Each rational approximant of the strict limiting form is a normalized finite
reflection-positive Gram form.  We package that stage as the already proved
constructive `PreInnerForm`, obtain its sharp rational Cauchy--Schwarz
inequality, and use local boundedness of the second diagonal together with a
division-free product modulus to pass the radical estimate to `CReal`.

The terminal theorem proves the replacement law needed by the generic
`CRealSeminormCompletion`: replacing either endpoint by a zero-distance
endpoint preserves the limiting squared distance.  No square root, choice,
classical logic, or rationalization of the limiting form is used.
-/

import YMGap.Continuum.CRealSeminormCompletion
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSYoung
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSYoung
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

/-! ## 1. Every normalized support Gram is a constructive pre-inner form -/

def normalizedSupportPreInnerForm
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat) : PreInnerForm (List Nat → Q') where
  B := centralNormalizedSupportReflectionBilinear
    coupling hcoupling cutoff half
  nonnegQuad := by
    intro s r left right
    let combination : List Nat → Q' := fun support =>
      s * left support + r * right support
    let B := centralNormalizedSupportReflectionBilinear
      coupling hcoupling cutoff half
    have hleftRight :
        B left combination ≈
          s * B left left + r * B left right := by
      have hadd := centralNormalizedSupportReflectionBilinear_add_right
        coupling hcoupling cutoff half left
        (fun support => s * left support)
        (fun support => r * right support)
      have hs := centralNormalizedSupportReflectionBilinear_smul_right
        coupling hcoupling cutoff half s left left
      have hr := centralNormalizedSupportReflectionBilinear_smul_right
        coupling hcoupling cutoff half r left right
      exact Q'.eqv_trans _ _ _ hadd (Q'.add_eqv_congr' hs hr)
    have hrightRight :
        B right combination ≈
          s * B left right + r * B right right := by
      have hadd := centralNormalizedSupportReflectionBilinear_add_right
        coupling hcoupling cutoff half right
        (fun support => s * left support)
        (fun support => r * right support)
      have hs0 := centralNormalizedSupportReflectionBilinear_smul_right
        coupling hcoupling cutoff half s right left
      have hsymm := centralNormalizedSupportReflectionBilinear_symm
        coupling hcoupling cutoff half right left
      have hs : B right (fun support => s * left support) ≈
          s * B left right :=
        Q'.eqv_trans _ _ _ hs0
          (Q'.mul_eqv_congr_left s _ _ hsymm)
      have hr := centralNormalizedSupportReflectionBilinear_smul_right
        coupling hcoupling cutoff half r right right
      exact Q'.eqv_trans _ _ _ hadd (Q'.add_eqv_congr' hs hr)
    have hscaledLeft :
        B (fun support => s * left support) combination ≈
          s * (s * B left left + r * B left right) := by
      exact Q'.eqv_trans _ _ _
        (centralNormalizedSupportReflectionBilinear_smul_left
          coupling hcoupling cutoff half s left combination)
        (Q'.mul_eqv_congr_left s _ _ hleftRight)
    have hscaledRight :
        B (fun support => r * right support) combination ≈
          r * (s * B left right + r * B right right) := by
      exact Q'.eqv_trans _ _ _
        (centralNormalizedSupportReflectionBilinear_smul_left
          coupling hcoupling cutoff half r right combination)
        (Q'.mul_eqv_congr_left r _ _ hrightRight)
    have hexpand :
        B combination combination ≈
          s * (s * B left left + r * B left right) +
            r * (s * B left right + r * B right right) := by
      exact Q'.eqv_trans _ _ _
        (centralNormalizedSupportReflectionBilinear_add_left
          coupling hcoupling cutoff half
          (fun support => s * left support)
          (fun support => r * right support) combination)
        (Q'.add_eqv_congr' hscaledLeft hscaledRight)
    have hring :
        s * (s * B left left + r * B left right) +
            r * (s * B left right + r * B right right) ≈
          s * s * B left left +
            2 * (s * r) * B left right +
              r * r * B right right := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv s (s * B left left) (r * B left right))
          (Q'.mul_add_eqv r (s * B left right) (r * B right right))) ?_
      exact YMGap.Continuum.GNSQuotient.GNSData.quad_regroup
        s r (B left left) (B left right) (B right right)
    have hself := centralNormalizedSupportReflectionBilinear_self
      coupling hcoupling cutoff half combination
    have hpoly :
        s * s * B left left +
            2 * (s * r) * B left right +
              r * r * B right right ≈
          centralNormalizedSupportReflectionQuadratic
            coupling hcoupling cutoff half combination :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm hring)
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm hexpand) hself)
    exact Q'.le_trans' _ _ _
      (centralNormalizedSupportReflectionQuadratic_nonnegative
        coupling hcoupling cutoff half combination)
      (Q'.ge_of_eqv hpoly)

/-- Sharp rational Cauchy--Schwarz for one normalized complete-support Gram. -/
theorem centralNormalizedSupportReflectionBilinear_cauchy_schwarz
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat) (left right : List Nat → Q') :
    centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half left right *
      centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half left right ≤
      centralNormalizedSupportReflectionQuadratic
          coupling hcoupling cutoff half left *
        centralNormalizedSupportReflectionQuadratic
          coupling hcoupling cutoff half right := by
  let F := normalizedSupportPreInnerForm coupling hcoupling cutoff half
  have hcs := F.cauchy_schwarz left right
  have hleft := centralNormalizedSupportReflectionBilinear_self
    coupling hcoupling cutoff half left
  have hright := centralNormalizedSupportReflectionBilinear_self
    coupling hcoupling cutoff half right
  exact Q'.le_trans' _ _ _ hcs
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hleft)
      (Q'.mul_eqv_congr_left _ _ _ hright)))

/-! ## 2. Sharp Cauchy--Schwarz at every strict rational stage -/

theorem strictJointCylinderReflectionBilinear_approx_cauchy_schwarz
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} (left right : StrictJointCylinderVector base) :
    (strictJointCylinderReflectionBilinear
        hcoupling hle left right).approx stage *
      (strictJointCylinderReflectionBilinear
        hcoupling hle left right).approx stage ≤
      (left.reflectionQuadratic hcoupling hle).approx stage *
        (right.reflectionQuadratic hcoupling hle).approx stage := by
  let radius := strictQueryBase base + stage
  let cutoff := centralStrictJointCenteredStageCutoff base stage
  let leftCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base left.roots)
    left.coefficient
  let rightCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base right.roots)
    right.coefficient
  have hbilinear :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) left right
  have hleft :=
    centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
      coupling hcoupling base left.roots left.coefficient stage
  have hright :=
    centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
      coupling hcoupling base right.roots right.coefficient stage
  have hcs := centralNormalizedSupportReflectionBilinear_cauchy_schwarz
    coupling hcoupling cutoff radius leftCoefficient rightCoefficient
  have hlhs :
      (strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx stage *
        (strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx stage ≈
      centralNormalizedSupportReflectionBilinear
          coupling hcoupling cutoff radius leftCoefficient rightCoefficient *
        centralNormalizedSupportReflectionBilinear
          coupling hcoupling cutoff radius leftCoefficient rightCoefficient :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hbilinear)
      (Q'.mul_eqv_congr_left _ _ _ hbilinear)
  have hrhs :
      centralNormalizedSupportReflectionQuadratic
          coupling hcoupling cutoff radius leftCoefficient *
        centralNormalizedSupportReflectionQuadratic
          coupling hcoupling cutoff radius rightCoefficient ≈
      (left.reflectionQuadratic hcoupling hle).approx stage *
        (right.reflectionQuadratic hcoupling hle).approx stage :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hleft))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hright))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hlhs)
    (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv hrhs))

/-! ## 3. The limiting radical kills every cross form -/

/-- If a strict cylinder vector has zero limiting reflection quadratic, its
limiting bilinear pairing with every vector is zero.  The proof is the sharp
stagewise Cauchy--Schwarz estimate plus a division-free product modulus. -/
theorem strictJointCylinderReflectionBilinear_equiv_czero_of_quadratic_equiv_czero
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base)
    (hnull : CReal.Equiv
      (left.reflectionQuadratic hcoupling hle) CReal.czero) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle left right)
      CReal.czero := by
  intro epsilon hepsilon
  let rightQuadratic := right.reflectionQuadratic hcoupling hle
  obtain ⟨Nbound, bound, hbound, hrightBound⟩ :=
    CReal.localBound rightQuadratic
  have hepsilonSq : (0 : Q') < epsilon * epsilon :=
    Q'.mul_pos hepsilon hepsilon
  obtain ⟨delta, hdelta, hbudget⟩ :=
    CReal.exists_mul_le hbound hepsilonSq
  obtain ⟨Nnull, hnullAt⟩ := hnull delta hdelta
  refine ⟨max Nbound Nnull, fun stage hstage => ?_⟩
  have hstageBound : Nbound ≤ stage :=
    Nat.le_trans (Nat.le_max_left _ _) hstage
  have hstageNull : Nnull ≤ stage :=
    Nat.le_trans (Nat.le_max_right _ _) hstage
  have hleftUpper :
      (left.reflectionQuadratic hcoupling hle).approx stage ≤ delta := by
    exact Q'.le_trans' _ _ _ (hnullAt stage hstageNull).1
      (Q'.le_of_eqv (QPoly.q_zero_add_eqv delta))
  have hrightUpper : rightQuadratic.approx stage ≤ bound :=
    (hrightBound stage hstageBound).2
  have hleftNonnegative :
      (0 : Q') ≤ (left.reflectionQuadratic hcoupling hle).approx stage :=
    centralNormalizedStrictJointFixedQuadraticSequence_nonnegative
      coupling hcoupling base left.roots left.coefficient stage
  have hrightNonnegative : (0 : Q') ≤ rightQuadratic.approx stage :=
    centralNormalizedStrictJointFixedQuadraticSequence_nonnegative
      coupling hcoupling base right.roots right.coefficient stage
  have hproduct :
      (left.reflectionQuadratic hcoupling hle).approx stage *
          rightQuadratic.approx stage ≤
        delta * bound :=
    Q'.mul_le_mul_of_nonneg hleftUpper hrightUpper
      (Q'.le_of_lt hdelta) hrightNonnegative
  have hdeltaBound : delta * bound ≤ epsilon * epsilon :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv delta bound)) hbudget
  have hcs :=
    strictJointCylinderReflectionBilinear_approx_cauchy_schwarz
      hcoupling hle left right (stage := stage)
  have hsquare :
      (strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx stage *
        (strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx stage ≤
        epsilon * epsilon :=
    Q'.le_trans' _ _ _ hcs
      (Q'.le_trans' _ _ _ hproduct hdeltaBound)
  have habs : Q'.abs
      ((strictJointCylinderReflectionBilinear
        hcoupling hle left right).approx stage) ≤ epsilon :=
    Q'.abs_le_of_sq_le_sq hepsilon hsquare
  have hzeroSub :
      ((strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx stage + (-(0 : Q'))).eqv
        ((strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx stage) := by
    rw [show (-(0 : Q')) = 0 from rfl, Q'.add_zero']
    exact Q'.eqv_refl _
  have habsSub : Q'.abs
      ((strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx stage + (-(0 : Q'))) ≤
      epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hzeroSub)) habs
  exact Q'.two_sided_of_abs_sub_le habsSub

/-! ## 4. Exact semantic algebra of presentation differences -/

private theorem neg_one_mul_eqv_local (value : Q') :
    ((-1 : Q') * value).eqv (-value) := by
  ring_qeqv

private theorem q_sub_add_cancel_eqv (a b : Q') :
    ((a + -b) + b).eqv a := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a (-b + b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact QPoly.q_add_zero_eqv a

private theorem q_sub_chain_eqv (a b c : Q') :
    (a + -c).eqv ((a + -b) + (b + -c)) := by
  apply Q'.eqv_symm
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (a + -b) b (-c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right
      ((a + -b) + b) a (-c) (q_sub_add_cancel_eqv a b)) ?_
  exact Q'.eqv_refl _

theorem strictJointCylinderDifference_coefficient_code
    {base : Nat} (left right : StrictJointCylinderVector base)
    (radius : Nat) (support : List Nat) :
    (strictJointCylinderDifference left right).coefficient
        (centralStrictLocalQueryCode radius base
          (strictJointCylinderDifference left right).roots support) ≈
      left.coefficient
          (centralStrictLocalQueryCode radius base left.roots support) +
        (-right.coefficient
          (centralStrictLocalQueryCode radius base right.roots support)) := by
  have hadd := StrictJointCylinderVector.add_coefficient_code
    left (right.smul (-1)) radius support
  refine Q'.eqv_trans _ _ _ hadd ?_
  exact Q'.add_eqv_congr_left _ _ _
    (neg_one_mul_eqv_local
      (right.coefficient
        (centralStrictLocalQueryCode radius base right.roots support)))

/-- `x - x` is semantically the zero scalar multiple of `x`. -/
theorem strictJointCylinderDifference_self_equivalent_zero_smul
    {base : Nat} (vector : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (strictJointCylinderDifference vector vector)
      (vector.smul 0) := by
  intro radius support
  have hdiff := strictJointCylinderDifference_coefficient_code
    vector vector radius support
  refine Q'.eqv_trans _ _ _ hdiff ?_
  change
    vector.coefficient
          (centralStrictLocalQueryCode radius base vector.roots support) +
        (-vector.coefficient
          (centralStrictLocalQueryCode radius base vector.roots support)) ≈
      (0 : Q') * vector.coefficient
        (centralStrictLocalQueryCode radius base vector.roots support)
  exact Q'.eqv_trans _ _ _
    (Q'.add_neg_self_eqv
      (vector.coefficient
        (centralStrictLocalQueryCode radius base vector.roots support)))
    (Q'.eqv_symm (Q'.zero_mul_eqv
      (vector.coefficient
        (centralStrictLocalQueryCode radius base vector.roots support))))

/-- Reversing a presentation difference multiplies it by `-1`. -/
theorem strictJointCylinderDifference_symm_equivalent_neg
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (strictJointCylinderDifference right left)
      ((strictJointCylinderDifference left right).smul (-1)) := by
  intro radius support
  have hleft := strictJointCylinderDifference_coefficient_code
    right left radius support
  have hright := strictJointCylinderDifference_coefficient_code
    left right radius support
  refine Q'.eqv_trans _ _ _ hleft ?_
  change
    right.coefficient
          (centralStrictLocalQueryCode radius base right.roots support) +
        (-left.coefficient
          (centralStrictLocalQueryCode radius base left.roots support)) ≈
      (-1 : Q') *
        (strictJointCylinderDifference left right).coefficient
          (centralStrictLocalQueryCode radius base
            (strictJointCylinderDifference left right).roots support)
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.mul_eqv_congr_left (-1) _ _ (Q'.eqv_symm hright))
  ring_qeqv

/-- Telescoping of presentation differences. -/
theorem strictJointCylinderDifference_chain_equivalent
    {base : Nat} (first middle last : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (strictJointCylinderDifference first last)
      ((strictJointCylinderDifference first middle).add
        (strictJointCylinderDifference middle last)) := by
  intro radius support
  have hdirect := strictJointCylinderDifference_coefficient_code
    first last radius support
  have hadd := StrictJointCylinderVector.add_coefficient_code
    (strictJointCylinderDifference first middle)
    (strictJointCylinderDifference middle last) radius support
  have hfirst := strictJointCylinderDifference_coefficient_code
    first middle radius support
  have hlast := strictJointCylinderDifference_coefficient_code
    middle last radius support
  refine Q'.eqv_trans _ _ _ hdirect ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hadd)
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.add_eqv_congr' (Q'.eqv_symm hfirst) (Q'.eqv_symm hlast))
  exact q_sub_chain_eqv
    (first.coefficient
      (centralStrictLocalQueryCode radius base first.roots support))
    (middle.coefficient
      (centralStrictLocalQueryCode radius base middle.roots support))
    (last.coefficient
      (centralStrictLocalQueryCode radius base last.roots support))

/-- Difference of two differences, regrouped by endpoints. -/
theorem strictJointCylinderDifference_difference_equivalent
    {base : Nat}
    (left left' right right' : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (strictJointCylinderDifference
        (strictJointCylinderDifference left right)
        (strictJointCylinderDifference left' right'))
      (strictJointCylinderDifference
        (strictJointCylinderDifference left left')
        (strictJointCylinderDifference right right')) := by
  intro radius support
  have houterLeft := strictJointCylinderDifference_coefficient_code
    (strictJointCylinderDifference left right)
    (strictJointCylinderDifference left' right') radius support
  have houterRight := strictJointCylinderDifference_coefficient_code
    (strictJointCylinderDifference left left')
    (strictJointCylinderDifference right right') radius support
  have hlr := strictJointCylinderDifference_coefficient_code
    left right radius support
  have hlr' := strictJointCylinderDifference_coefficient_code
    left' right' radius support
  have hll' := strictJointCylinderDifference_coefficient_code
    left left' radius support
  have hrr' := strictJointCylinderDifference_coefficient_code
    right right' radius support
  refine Q'.eqv_trans _ _ _ houterLeft ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hlr (Q'.neg_eqv_congr _ _ hlr')) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.eqv_trans _ _ _ houterRight
      (Q'.add_eqv_congr' hll' (Q'.neg_eqv_congr _ _ hrr'))))
  ring_qeqv

/-- `(a-b)+b` semantically recovers `a`. -/
theorem strictJointCylinderDifference_add_right_equivalent
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent left
      ((strictJointCylinderDifference left right).add right) := by
  intro radius support
  have hadd := StrictJointCylinderVector.add_coefficient_code
    (strictJointCylinderDifference left right) right radius support
  have hdiff := strictJointCylinderDifference_coefficient_code
    left right radius support
  have hcombined :
      (strictJointCylinderDifference left right).coefficient
            (centralStrictLocalQueryCode radius base
              (strictJointCylinderDifference left right).roots support) +
          right.coefficient
            (centralStrictLocalQueryCode radius base right.roots support) ≈
        left.coefficient
          (centralStrictLocalQueryCode radius base left.roots support) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hdiff) ?_
    exact q_sub_add_cancel_eqv
      (left.coefficient
        (centralStrictLocalQueryCode radius base left.roots support))
      (right.coefficient
        (centralStrictLocalQueryCode radius base right.roots support))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hcombined) (Q'.eqv_symm hadd)

/-! ## 5. Squared-pseudometric laws of the strict reflection distance -/

private theorem cadd_zero_equiv (value : CReal) :
    CReal.Equiv (CReal.add value CReal.czero) value :=
  SumOfSquares.Equiv_of_approx_eqv (fun stage => by
    exact QPoly.q_add_zero_eqv (value.approx stage))

private theorem czero_add_equiv (value : CReal) :
    CReal.Equiv (CReal.add CReal.czero value) value :=
  SumOfSquares.Equiv_of_approx_eqv (fun stage => by
    exact QPoly.q_zero_add_eqv (value.approx stage))

private theorem cmul_ofQ_zero_equiv (value : CReal) :
    CReal.Equiv (CReal.mul (CReal.ofQ' 0) value) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun stage => by
    exact Q'.zero_mul_eqv (value.approx stage))

private theorem creal_mul_congr_right_local
    {scalar left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  CReal.Equiv.trans (CRealAlg.cmul_comm scalar left)
    (CReal.Equiv.trans (CReal.mul_congr_left h)
      (CRealAlg.cmul_comm right scalar))

private theorem cmul_neg_one_twice_equiv (value : CReal) :
    CReal.Equiv
      (CReal.mul (CReal.ofQ' (-1))
        (CReal.mul (CReal.ofQ' (-1)) value)) value :=
  SumOfSquares.Equiv_of_approx_eqv (fun stage => by
    show ((-1 : Q') * ((-1 : Q') * value.approx stage)).eqv
      (value.approx stage)
    ring_qeqv)

private theorem cmul_czero_equiv (scalar : CReal) :
    CReal.Equiv (CReal.mul scalar CReal.czero) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun stage => by
    exact Q'.mul_zero_eqv (scalar.approx stage))

private theorem cadd_right_equiv_of_zero {left zeroLike : CReal}
    (hzero : CReal.Equiv zeroLike CReal.czero) :
    CReal.Equiv (CReal.add left zeroLike) left :=
  CReal.Equiv.trans (CReal.add_congr_right hzero)
    (cadd_zero_equiv left)

private theorem cadd_left_equiv_of_zero {zeroLike right : CReal}
    (hzero : CReal.Equiv zeroLike CReal.czero) :
    CReal.Equiv (CReal.add zeroLike right) right :=
  CReal.Equiv.trans (CReal.add_congr_left hzero)
    (czero_add_equiv right)

/-- The reflection quadratic of a zero scalar multiple vanishes. -/
theorem reflectionQuadratic_smul_zero_equiv_czero
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      ((vector.smul 0).reflectionQuadratic hcoupling hle)
      CReal.czero := by
  let scaled := vector.smul 0
  have hself := strictJointCylinderReflectionBilinear_self
    hcoupling hle scaled
  have hsmul := strictJointCylinderReflectionBilinear_smul_left
    hcoupling hle 0 vector scaled
  exact CReal.Equiv.trans (CReal.Equiv.symm hself)
    (CReal.Equiv.trans hsmul
      (cmul_ofQ_zero_equiv
        (strictJointCylinderReflectionBilinear
          hcoupling hle vector scaled)))

/-- Scaling by `-1` preserves the reflection quadratic. -/
theorem reflectionQuadratic_smul_neg_one_equiv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      ((vector.smul (-1)).reflectionQuadratic hcoupling hle)
      (vector.reflectionQuadratic hcoupling hle) := by
  let scaled := vector.smul (-1)
  let diagonal := strictJointCylinderReflectionBilinear
    hcoupling hle vector vector
  have hselfScaled := strictJointCylinderReflectionBilinear_self
    hcoupling hle scaled
  have hleft := strictJointCylinderReflectionBilinear_smul_left
    hcoupling hle (-1) vector scaled
  have hright := strictJointCylinderReflectionBilinear_smul_right
    hcoupling hle (-1) vector vector
  have houter : CReal.Equiv
      (CReal.mul (CReal.ofQ' (-1))
        (strictJointCylinderReflectionBilinear
          hcoupling hle vector scaled))
      (CReal.mul (CReal.ofQ' (-1))
        (CReal.mul (CReal.ofQ' (-1)) diagonal)) :=
    creal_mul_congr_right_local hright
  have hself := strictJointCylinderReflectionBilinear_self
    hcoupling hle vector
  exact CReal.Equiv.trans (CReal.Equiv.symm hselfScaled)
    (CReal.Equiv.trans hleft
      (CReal.Equiv.trans houter
        (CReal.Equiv.trans (cmul_neg_one_twice_equiv diagonal) hself)))

/-- Reflexivity of the strict squared OS distance. -/
theorem strictJointCylinderReflectionDistSq_refl
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionDistSq hcoupling hle vector vector)
      CReal.czero := by
  have hpresentation := StrictJointCylinderVector.reflectionQuadratic_equiv
    hcoupling hle
    (strictJointCylinderDifference_self_equivalent_zero_smul vector)
  exact CReal.Equiv.trans hpresentation
    (reflectionQuadratic_smul_zero_equiv_czero hcoupling hle vector)

/-- Symmetry of the strict squared OS distance. -/
theorem strictJointCylinderReflectionDistSq_symm
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionDistSq hcoupling hle left right)
      (strictJointCylinderReflectionDistSq hcoupling hle right left) := by
  have hpresentation := StrictJointCylinderVector.reflectionQuadratic_equiv
    hcoupling hle
    (strictJointCylinderDifference_symm_equivalent_neg left right)
  have hneg := reflectionQuadratic_smul_neg_one_equiv
    hcoupling hle (strictJointCylinderDifference left right)
  exact CReal.Equiv.symm (CReal.Equiv.trans hpresentation hneg)

/-- Sqrt-free quadratic triangle for two strict presentation vectors. -/
theorem reflectionQuadratic_add_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    CReal.leEv
      ((left.add right).reflectionQuadratic hcoupling hle)
      (CReal.add
        (CReal.add
          (left.reflectionQuadratic hcoupling hle)
          (left.reflectionQuadratic hcoupling hle))
        (CReal.add
          (right.reflectionQuadratic hcoupling hle)
          (right.reflectionQuadratic hcoupling hle))) := by
  let Qleft := left.reflectionQuadratic hcoupling hle
  let Qright := right.reflectionQuadratic hcoupling hle
  let cross := strictJointCylinderReflectionBilinear
    hcoupling hle left right
  have hselfAdd := strictJointCylinderReflectionBilinear_self
    hcoupling hle (left.add right)
  have haddLeft := strictJointCylinderReflectionBilinear_add_left
    hcoupling hle left right (left.add right)
  have haddRightLeft := strictJointCylinderReflectionBilinear_add_right
    hcoupling hle left left right
  have haddRightRight := strictJointCylinderReflectionBilinear_add_right
    hcoupling hle right left right
  have hselfLeft := strictJointCylinderReflectionBilinear_self
    hcoupling hle left
  have hselfRight := strictJointCylinderReflectionBilinear_self
    hcoupling hle right
  have hsymm := StrictJointCylinderVector.reflectionBilinear_symm
    hcoupling hle right left
  have hfirst : CReal.Equiv
      (strictJointCylinderReflectionBilinear
        hcoupling hle left (left.add right))
      (CReal.add Qleft cross) :=
    CReal.Equiv.trans haddRightLeft
      (CReal.Equiv_add hselfLeft (CReal.Equiv.refl _))
  have hsecond : CReal.Equiv
      (strictJointCylinderReflectionBilinear
        hcoupling hle right (left.add right))
      (CReal.add cross Qright) :=
    CReal.Equiv.trans haddRightRight
      (CReal.Equiv_add hsymm hselfRight)
  have hexpand : CReal.Equiv
      ((left.add right).reflectionQuadratic hcoupling hle)
      (CReal.add
        (CReal.add Qleft Qright)
        (CReal.mul (CReal.ofQ' 2) cross)) := by
    refine CReal.Equiv.trans (CReal.Equiv.symm hselfAdd) ?_
    refine CReal.Equiv.trans haddLeft ?_
    refine CReal.Equiv.trans (CReal.Equiv_add hfirst hsecond) ?_
    exact SumOfSquares.Equiv_of_approx_eqv (fun stage => by
      show
        ((Qleft.approx stage + cross.approx stage) +
            (cross.approx stage + Qright.approx stage)).eqv
          ((Qleft.approx stage + Qright.approx stage) +
            (2 : Q') * cross.approx stage)
      refine Q'.eqv_trans _ _ _
        (Q'.rearr_ABXY
          (Qleft.approx stage) (cross.approx stage)
          (cross.approx stage) (Qright.approx stage)) ?_
      exact Q'.add_eqv_congr_left
        (Qleft.approx stage + Qright.approx stage)
        (cross.approx stage + cross.approx stage)
        ((2 : Q') * cross.approx stage)
        (q_two_mul (cross.approx stage)))
  have hyoung := strictJointCylinderReflectionBilinear_young
    hcoupling hle left right
  have hmiddle : CReal.leEv
      (CReal.add
        (CReal.add Qleft Qright)
        (CReal.mul (CReal.ofQ' 2) cross))
      (CReal.add
        (CReal.add Qleft Qright)
        (CReal.add Qleft Qright)) :=
    CReal.leEv_add (CReal.leEv_refl _) hyoung
  have hrearrange : CReal.Equiv
      (CReal.add
        (CReal.add Qleft Qright)
        (CReal.add Qleft Qright))
      (CReal.add
        (CReal.add Qleft Qleft)
        (CReal.add Qright Qright)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun stage => by
      show
        ((Qleft.approx stage + Qright.approx stage) +
            (Qleft.approx stage + Qright.approx stage)).eqv
          ((Qleft.approx stage + Qleft.approx stage) +
            (Qright.approx stage + Qright.approx stage))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (Qleft.approx stage + Qright.approx stage)
          (Qleft.approx stage + Qright.approx stage)
          (Qright.approx stage + Qleft.approx stage)
          (Q'.add_comm_eqv (Qleft.approx stage) (Qright.approx stage))) ?_
      exact Q'.rearr_ABXY
        (Qleft.approx stage) (Qright.approx stage)
        (Qright.approx stage) (Qleft.approx stage))
  exact CReal.leEv_trans (CReal.leEv_of_equiv hexpand)
    (CReal.leEv_trans hmiddle (CReal.leEv_of_equiv hrearrange))

/-- Sqrt-free triangle inequality for the strict squared OS distance. -/
theorem strictJointCylinderReflectionDistSq_triangle
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat}
    (first middle last : StrictJointCylinderVector base) :
    CReal.leEv
      (strictJointCylinderReflectionDistSq hcoupling hle first last)
      (CReal.add
        (CReal.add
          (strictJointCylinderReflectionDistSq hcoupling hle first middle)
          (strictJointCylinderReflectionDistSq hcoupling hle first middle))
        (CReal.add
          (strictJointCylinderReflectionDistSq hcoupling hle middle last)
          (strictJointCylinderReflectionDistSq hcoupling hle middle last))) := by
  have hpresentation := StrictJointCylinderVector.reflectionQuadratic_equiv
    hcoupling hle
    (strictJointCylinderDifference_chain_equivalent first middle last)
  exact CReal.leEv_trans (CReal.leEv_of_equiv hpresentation)
    (reflectionQuadratic_add_le hcoupling hle
      (strictJointCylinderDifference first middle)
      (strictJointCylinderDifference middle last))

/-! ## 6. Closure of the radical and endpoint replacement -/

/-- The difference of two null vectors is null. -/
theorem reflectionQuadratic_difference_equiv_czero_of_null
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base)
    (hleft : CReal.Equiv
      (left.reflectionQuadratic hcoupling hle) CReal.czero)
    (hright : CReal.Equiv
      (right.reflectionQuadratic hcoupling hle) CReal.czero) :
    CReal.Equiv
      ((strictJointCylinderDifference left right).reflectionQuadratic
        hcoupling hle)
      CReal.czero := by
  let difference := strictJointCylinderDifference left right
  have hradLeft :=
    strictJointCylinderReflectionBilinear_equiv_czero_of_quadratic_equiv_czero
      hcoupling hle left difference hleft
  have hradRight :=
    strictJointCylinderReflectionBilinear_equiv_czero_of_quadratic_equiv_czero
      hcoupling hle right difference hright
  have hscaled := strictJointCylinderReflectionBilinear_smul_left
    hcoupling hle (-1) right difference
  have hscaledZero : CReal.Equiv
      (strictJointCylinderReflectionBilinear
        hcoupling hle (right.smul (-1)) difference)
      CReal.czero :=
    CReal.Equiv.trans hscaled
      (CReal.Equiv.trans (creal_mul_congr_right_local hradRight)
        (cmul_czero_equiv (CReal.ofQ' (-1))))
  have hadd := strictJointCylinderReflectionBilinear_add_left
    hcoupling hle left (right.smul (-1)) difference
  have hsumZero : CReal.Equiv
      (CReal.add
        (strictJointCylinderReflectionBilinear
          hcoupling hle left difference)
        (strictJointCylinderReflectionBilinear
          hcoupling hle (right.smul (-1)) difference))
      CReal.czero :=
    CReal.Equiv.trans (CReal.Equiv_add hradLeft hscaledZero)
      (czero_add_equiv CReal.czero)
  have hself := strictJointCylinderReflectionBilinear_self
    hcoupling hle difference
  exact CReal.Equiv.trans (CReal.Equiv.symm hself)
    (CReal.Equiv.trans hadd hsumZero)

/-- **Strict CReal radical descent / endpoint replacement.**  If both source
endpoints move by null vectors, the squared distance is unchanged. -/
theorem strictJointCylinderReflectionDistSq_null_congr
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat}
    {left left' right right' : StrictJointCylinderVector base}
    (hleft : CReal.Equiv
      (strictJointCylinderReflectionDistSq
        hcoupling hle left left') CReal.czero)
    (hright : CReal.Equiv
      (strictJointCylinderReflectionDistSq
        hcoupling hle right right') CReal.czero) :
    CReal.Equiv
      (strictJointCylinderReflectionDistSq hcoupling hle left right)
      (strictJointCylinderReflectionDistSq hcoupling hle left' right') := by
  let firstDifference := strictJointCylinderDifference left right
  let secondDifference := strictJointCylinderDifference left' right'
  let leftChange := strictJointCylinderDifference left left'
  let rightChange := strictJointCylinderDifference right right'
  let changeDifference := strictJointCylinderDifference leftChange rightChange
  let totalChange := strictJointCylinderDifference firstDifference secondDifference
  have hchangeNull : CReal.Equiv
      (changeDifference.reflectionQuadratic hcoupling hle) CReal.czero :=
    reflectionQuadratic_difference_equiv_czero_of_null
      hcoupling hle leftChange rightChange hleft hright
  have hregroup : StrictJointCylinderVectorEquivalent
      totalChange changeDifference :=
    strictJointCylinderDifference_difference_equivalent
      left left' right right'
  have htotalNull : CReal.Equiv
      (totalChange.reflectionQuadratic hcoupling hle) CReal.czero :=
    CReal.Equiv.trans
      (StrictJointCylinderVector.reflectionQuadratic_equiv
        hcoupling hle hregroup)
      hchangeNull
  have hdecompose : StrictJointCylinderVectorEquivalent
      firstDifference (totalChange.add secondDifference) :=
    strictJointCylinderDifference_add_right_equivalent
      firstDifference secondDifference
  have hradFirst :=
    strictJointCylinderReflectionBilinear_equiv_czero_of_quadratic_equiv_czero
      hcoupling hle totalChange firstDifference htotalNull
  have hradSecond :=
    strictJointCylinderReflectionBilinear_equiv_czero_of_quadratic_equiv_czero
      hcoupling hle totalChange secondDifference htotalNull
  have hfirstRadRight : CReal.Equiv
      (strictJointCylinderReflectionBilinear
        hcoupling hle firstDifference totalChange)
      CReal.czero :=
    CReal.Equiv.trans
      (StrictJointCylinderVector.reflectionBilinear_symm
        hcoupling hle firstDifference totalChange)
      hradFirst
  have hdiagToCross : CReal.Equiv
      (strictJointCylinderReflectionBilinear
        hcoupling hle firstDifference firstDifference)
      (strictJointCylinderReflectionBilinear
        hcoupling hle firstDifference secondDifference) := by
    have hpresentation :=
      StrictJointCylinderVector.reflectionBilinear_equiv
        hcoupling hle
        (strictJointCylinderVectorEquivalent_refl firstDifference)
        hdecompose
    have hadd := strictJointCylinderReflectionBilinear_add_right
      hcoupling hle firstDifference totalChange secondDifference
    exact CReal.Equiv.trans hpresentation
      (CReal.Equiv.trans hadd
        (cadd_left_equiv_of_zero hfirstRadRight))
  have hcrossToDiag : CReal.Equiv
      (strictJointCylinderReflectionBilinear
        hcoupling hle firstDifference secondDifference)
      (strictJointCylinderReflectionBilinear
        hcoupling hle secondDifference secondDifference) := by
    have hpresentation :=
      StrictJointCylinderVector.reflectionBilinear_equiv
        hcoupling hle hdecompose
        (strictJointCylinderVectorEquivalent_refl secondDifference)
    have hadd := strictJointCylinderReflectionBilinear_add_left
      hcoupling hle totalChange secondDifference secondDifference
    exact CReal.Equiv.trans hpresentation
      (CReal.Equiv.trans hadd
        (cadd_left_equiv_of_zero hradSecond))
  have hselfFirst := strictJointCylinderReflectionBilinear_self
    hcoupling hle firstDifference
  have hselfSecond := strictJointCylinderReflectionBilinear_self
    hcoupling hle secondDifference
  exact CReal.Equiv.trans (CReal.Equiv.symm hselfFirst)
    (CReal.Equiv.trans hdiagToCross
      (CReal.Equiv.trans hcrossToDiag hselfSecond))

/-- Nonnegativity in the eventual order, in the exact shape consumed by the
generic squared-seminorm completion. -/
theorem strictJointCylinderReflectionDistSq_nonneg
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    CReal.leEv CReal.czero
      (strictJointCylinderReflectionDistSq hcoupling hle left right) :=
  (strictJointCylinderDifference left right).reflectionQuadratic_geRat_zero
    hcoupling hle

/-- The fully discharged fixed-base `CReal` squared seminorm. -/
def strictJointCylinderSquaredSeminorm
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (base : Nat) :
    CRealSeminormCompletion.SquaredSeminorm where
  Carrier := StrictJointCylinderVector base
  distSq := strictJointCylinderReflectionDistSq hcoupling hle
  distSq_refl := strictJointCylinderReflectionDistSq_refl hcoupling hle
  distSq_symm := strictJointCylinderReflectionDistSq_symm hcoupling hle
  distSq_nonneg := strictJointCylinderReflectionDistSq_nonneg hcoupling hle
  distSq_triangle := strictJointCylinderReflectionDistSq_triangle hcoupling hle
  null_congr := strictJointCylinderReflectionDistSq_null_congr hcoupling hle

#print axioms normalizedSupportPreInnerForm
#print axioms centralNormalizedSupportReflectionBilinear_cauchy_schwarz
#print axioms strictJointCylinderReflectionBilinear_approx_cauchy_schwarz
#print axioms strictJointCylinderReflectionBilinear_equiv_czero_of_quadratic_equiv_czero
#print axioms strictJointCylinderDifference_coefficient_code
#print axioms strictJointCylinderDifference_self_equivalent_zero_smul
#print axioms strictJointCylinderDifference_symm_equivalent_neg
#print axioms strictJointCylinderDifference_chain_equivalent
#print axioms strictJointCylinderDifference_difference_equivalent
#print axioms strictJointCylinderDifference_add_right_equivalent
#print axioms reflectionQuadratic_smul_zero_equiv_czero
#print axioms reflectionQuadratic_smul_neg_one_equiv
#print axioms strictJointCylinderReflectionDistSq_refl
#print axioms strictJointCylinderReflectionDistSq_symm
#print axioms reflectionQuadratic_add_le
#print axioms strictJointCylinderReflectionDistSq_triangle
#print axioms reflectionQuadratic_difference_equiv_czero_of_null
#print axioms strictJointCylinderReflectionDistSq_null_congr
#print axioms strictJointCylinderReflectionDistSq_nonneg
#print axioms strictJointCylinderSquaredSeminorm

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
