/-
# The doubled-time OS identity as a constructive Young/chessboard seed

Reflection positivity gives the elementary Gram inequality

  2 B(left,right) <= Q(left) + Q(right).

Combining it with the derived doubled-time mixed OS identity gives the first
unconditional norm-comparison consequence of that identity.  The source norm
is kept in its honest common-box transported presentation; identifying it with
the original source norm is a separate base-cofinality step and is not assumed
here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSIdentity
import YMGap.Continuum.GNSDynamics
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSYoung

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSIdentity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite and normalized Gram Young identities -/

private def youngDifferenceIntegrandL : PolyExpr :=
  let a := PolyExpr.var 0
  let b := PolyExpr.var 1
  let c := PolyExpr.var 2
  let d := PolyExpr.var 3
  let kernel := PolyExpr.var 4
  .add
    (.mul (.add (.mul a d) (.mul b c)) kernel)
    (.mul (.mul (.add a (.neg b)) (.add c (.neg d))) kernel)

private def youngDifferenceIntegrandR : PolyExpr :=
  let a := PolyExpr.var 0
  let b := PolyExpr.var 1
  let c := PolyExpr.var 2
  let d := PolyExpr.var 3
  let kernel := PolyExpr.var 4
  .add (.mul (.mul a c) kernel) (.mul (.mul b d) kernel)

private theorem youngDifferenceIntegrand_normal :
    normalize youngDifferenceIntegrandL =
      normalize youngDifferenceIntegrandR := by
  decide

private theorem young_difference_integrand_algebra
    (a b c d kernel : Q') :
    ((a * d + b * c) * kernel) +
        (((a + (-b)) * (c + (-d))) * kernel) ≈
      (a * c) * kernel + (b * d) * kernel := by
  let ρ : Nat → Q' := fun n =>
    if n = 0 then a else if n = 1 then b else if n = 2 then c
    else if n = 3 then d else kernel
  have h := poly_identity_of_normal_eq
    youngDifferenceIntegrandL youngDifferenceIntegrandR
    youngDifferenceIntegrand_normal ρ
  simpa [youngDifferenceIntegrandL, youngDifferenceIntegrandR,
    RingNormaliser.eval, ρ] using h

private theorem two_mul_eqv_local (value : Q') :
    (2 : Q') * value ≈ value + value := by
  refine Q'.eqv_trans _ ((Q'.ofNat 1 + Q'.ofNat 1) * value) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv 1 1)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 1 * value + Q'.ofNat 1 * value) _
    (Q'.add_mul_eqv (Q'.ofNat 1) (Q'.ofNat 1) value) ?_
  exact Q'.add_eqv_congr' (Q'.one_mul_eqv value) (Q'.one_mul_eqv value)

/-- Move the elementary identity `2 * cross + difference = left + right`
through one finite exact-rational sum. -/
private theorem listQSum_twice_add_eqv
    {State : Type} (states : List State)
    (cross difference left right : State → Q')
    (hpoint : ∀ state, state ∈ states →
      (2 : Q') * cross state + difference state ≈
        left state + right state) :
    (2 : Q') * listQSum cross states + listQSum difference states ≈
      listQSum left states + listQSum right states := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_symm (listQSum_mul_left (2 : Q') cross states))
      (Q'.eqv_refl (listQSum difference states))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_add (fun state => (2 : Q') * cross state)
        difference states)) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_congr_on
      (fun state => (2 : Q') * cross state + difference state)
      (fun state => left state + right state)
      states hpoint) ?_
  exact listQSum_add left right states

/-- Twice the symmetric polarized cross form plus the difference quadratic is
the sum of the two diagonal quadratics.  This is a termwise rational identity
and does not require symmetry of the input kernel. -/
theorem finiteJointPolarizedBilinear_twice_add_difference_eqv
    {State : Type} (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q') :
    (2 : Q') *
          finiteJointPolarizedBilinear states
            leftCoefficient rightCoefficient joint +
        finiteJointQuadratic states
          (fun state => leftCoefficient state + (-rightCoefficient state))
          joint ≈
      finiteJointQuadratic states leftCoefficient joint +
        finiteJointQuadratic states rightCoefficient joint := by
  unfold finiteJointPolarizedBilinear finiteJointQuadratic
  apply listQSum_twice_add_eqv
  intro left hleft
  apply listQSum_twice_add_eqv
  intro right hright
  let cross :=
    (((strictJointPolarizationQuarter + strictJointPolarizationQuarter) *
        (leftCoefficient left * rightCoefficient right +
          rightCoefficient left * leftCoefficient right)) *
      joint left right)
  have hdouble : (2 : Q') * cross ≈ cross + cross :=
    two_mul_eqv_local cross
  let paired :=
    ((leftCoefficient left * rightCoefficient right +
        rightCoefficient left * leftCoefficient right) *
      joint left right)
  have hcross : cross ≈
      (strictJointPolarizationQuarter + strictJointPolarizationQuarter) *
        paired := by
    exact Q'.mul_assoc_eqv
      (strictJointPolarizationQuarter + strictJointPolarizationQuarter)
      (leftCoefficient left * rightCoefficient right +
        rightCoefficient left * leftCoefficient right)
      (joint left right)
  have hhalf :
      (strictJointPolarizationQuarter + strictJointPolarizationQuarter) +
          (strictJointPolarizationQuarter + strictJointPolarizationQuarter) ≈
        (1 : Q') := by
    decide
  have hcrossDouble : cross + cross ≈ paired := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hcross hcross) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (strictJointPolarizationQuarter + strictJointPolarizationQuarter)
          (strictJointPolarizationQuarter + strictJointPolarizationQuarter)
          paired)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ paired hhalf) ?_
    exact Q'.one_mul_eqv paired
  refine Q'.eqv_trans _
    ((cross + cross) +
      (((leftCoefficient left + (-rightCoefficient left)) *
          (leftCoefficient right + (-rightCoefficient right))) *
        joint left right)) _
    (Q'.add_eqv_congr' hdouble (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _
    (paired +
      (((leftCoefficient left + (-rightCoefficient left)) *
          (leftCoefficient right + (-rightCoefficient right))) *
        joint left right)) _
    (Q'.add_eqv_congr' hcrossDouble (Q'.eqv_refl _)) ?_
  unfold paired
  exact young_difference_integrand_algebra
    (leftCoefficient left) (rightCoefficient left)
    (leftCoefficient right) (rightCoefficient right) (joint left right)

/-- Normalized complete-support Gram identity underlying Young's inequality. -/
theorem centralNormalizedSupportReflectionBilinear_twice_add_difference_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCoefficient rightCoefficient : List Nat → Q') :
    (2 : Q') *
          centralNormalizedSupportReflectionBilinear
            coupling hcoupling cutoff half
            leftCoefficient rightCoefficient +
        centralNormalizedSupportReflectionQuadratic
          coupling hcoupling cutoff half
          (fun support =>
            leftCoefficient support + (-rightCoefficient support)) ≈
      centralNormalizedSupportReflectionQuadratic
          coupling hcoupling cutoff half leftCoefficient +
        centralNormalizedSupportReflectionQuadratic
          coupling hcoupling cutoff half rightCoefficient := by
  let denominator := slabParametricKPhysicalPartition
    coupling cutoff (centralExtent half)
  have hdenominator : (0 : Q') < denominator :=
    slabParametricKPhysicalPartition_pos
      hcoupling cutoff (centralExtent half)
  let reciprocal := Q'.recipPos denominator hdenominator
  let cross := finiteJointPolarizedBilinear
    (centralHalfSupportSpace half)
    leftCoefficient rightCoefficient
    (centralSupportReflectedKernel coupling cutoff half)
  let difference := finiteJointQuadratic
    (centralHalfSupportSpace half)
    (fun support => leftCoefficient support + (-rightCoefficient support))
    (centralSupportReflectedKernel coupling cutoff half)
  let leftDiagonal := finiteJointQuadratic
    (centralHalfSupportSpace half) leftCoefficient
    (centralSupportReflectedKernel coupling cutoff half)
  let rightDiagonal := finiteJointQuadratic
    (centralHalfSupportSpace half) rightCoefficient
    (centralSupportReflectedKernel coupling cutoff half)
  have hfinite :
      (2 : Q') * cross + difference ≈
        leftDiagonal + rightDiagonal := by
    simpa only [cross, difference, leftDiagonal, rightDiagonal] using
      (finiteJointPolarizedBilinear_twice_add_difference_eqv
        (centralHalfSupportSpace half)
        leftCoefficient rightCoefficient
        (centralSupportReflectedKernel coupling cutoff half))
  have hscaled :
      ((2 : Q') * cross + difference) * reciprocal ≈
        (leftDiagonal + rightDiagonal) * reciprocal :=
    Q'.mul_eqv_congr_right _ _ reciprocal hfinite
  unfold centralNormalizedSupportReflectionBilinear
    centralNormalizedSupportReflectionQuadratic
    centralSupportReflectionQuadratic Q'.divPos
  change
    (2 : Q') * (cross * reciprocal) + difference * reciprocal ≈
      leftDiagonal * reciprocal + rightDiagonal * reciprocal
  refine Q'.eqv_trans _
    (((2 : Q') * cross + difference) * reciprocal) _ ?_
    (Q'.eqv_trans _ _ _ hscaled ?_)
  · refine Q'.eqv_trans _
      (((2 : Q') * cross) * reciprocal + difference * reciprocal) _
      (Q'.add_eqv_congr'
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv (2 : Q') cross reciprocal))
        (Q'.eqv_refl _)) ?_
    exact Q'.eqv_symm
      (Q'.add_mul_eqv ((2 : Q') * cross) difference reciprocal)
  · exact Q'.add_mul_eqv leftDiagonal rightDiagonal reciprocal

/-- Rational Young inequality for the normalized support reflection form. -/
theorem centralNormalizedSupportReflectionBilinear_young
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCoefficient rightCoefficient : List Nat → Q') :
    (2 : Q') *
        centralNormalizedSupportReflectionBilinear
          coupling hcoupling cutoff half
          leftCoefficient rightCoefficient ≤
      centralNormalizedSupportReflectionQuadratic
          coupling hcoupling cutoff half leftCoefficient +
        centralNormalizedSupportReflectionQuadratic
          coupling hcoupling cutoff half rightCoefficient := by
  have hdifference : (0 : Q') ≤
      centralNormalizedSupportReflectionQuadratic
        coupling hcoupling cutoff half
        (fun support =>
          leftCoefficient support + (-rightCoefficient support)) :=
    centralNormalizedSupportReflectionQuadratic_nonnegative
      coupling hcoupling cutoff half
      (fun support =>
        leftCoefficient support + (-rightCoefficient support))
  have hadd := Q'.add_le_self_of_nonneg
    ((2 : Q') * centralNormalizedSupportReflectionBilinear
      coupling hcoupling cutoff half leftCoefficient rightCoefficient)
    (centralNormalizedSupportReflectionQuadratic
      coupling hcoupling cutoff half
      (fun support =>
        leftCoefficient support + (-rightCoefficient support)))
    hdifference
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv
      (centralNormalizedSupportReflectionBilinear_twice_add_difference_eqv
        coupling hcoupling cutoff half leftCoefficient rightCoefficient))

/-! ## 2. Sound constructive-real Young inequality -/

/-- At every common stage, the strict-cylinder polarized approximant obeys
Young's inequality against its two diagonal approximants. -/
theorem strictJointCylinderReflectionBilinear_approx_young
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat}
    (left right : StrictJointCylinderVector base) :
    (2 : Q') *
        (strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx stage ≤
      (left.reflectionQuadratic hcoupling hle).approx stage +
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
  have hyoung := centralNormalizedSupportReflectionBilinear_young
    coupling hcoupling cutoff radius leftCoefficient rightCoefficient
  have hleftSide :
      (2 : Q') *
          (strictJointCylinderReflectionBilinear
            hcoupling hle left right).approx stage ≈
        (2 : Q') * centralNormalizedSupportReflectionBilinear
          coupling hcoupling cutoff radius
          leftCoefficient rightCoefficient :=
    Q'.mul_eqv_congr_left (2 : Q') _ _ hbilinear
  have hrightSide :
      (left.reflectionQuadratic hcoupling hle).approx stage +
          (right.reflectionQuadratic hcoupling hle).approx stage ≈
        centralNormalizedSupportReflectionQuadratic
            coupling hcoupling cutoff radius leftCoefficient +
          centralNormalizedSupportReflectionQuadratic
            coupling hcoupling cutoff radius rightCoefficient := by
    exact Q'.add_eqv_congr' hleft hright
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hleftSide)
    (Q'.le_trans' _ _ _ hyoung (Q'.ge_of_eqv hrightSide))

/-- Sound eventual-order Young inequality for the limiting strict-cylinder
reflection form. -/
theorem strictJointCylinderReflectionBilinear_young
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat}
    (left right : StrictJointCylinderVector base) :
    CReal.leEv
      (CReal.mul (CReal.ofQ' 2)
        (strictJointCylinderReflectionBilinear
          hcoupling hle left right))
      (CReal.add
        (left.reflectionQuadratic hcoupling hle)
        (right.reflectionQuadratic hcoupling hle)) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  exact Q'.le_trans' _ _ _
    (strictJointCylinderReflectionBilinear_approx_young
      hcoupling hle left right (stage := stage))
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

/-! ## 3. The exact doubled-time chessboard seed -/

private theorem leEv_mul_left_of_equiv
    (scale left left' right : CReal)
    (hequivalent : CReal.Equiv left left')
    (hle : CReal.leEv (CReal.mul scale left') right) :
    CReal.leEv (CReal.mul scale left) right := by
  have hmul : CReal.Equiv
      (CReal.mul scale left) (CReal.mul scale left') :=
    CReal.Equiv.trans
      (CRealAlg.cmul_comm scale left)
      (CReal.Equiv.trans
        (CReal.mul_congr_left hequivalent)
        (CRealAlg.cmul_comm left' scale))
  exact
    (CReal.leEv_congr
      hmul
      (CReal.Equiv.refl right)).mpr hle

/-- The derived doubled-time OS identity turns Young's inequality into the
honest common-box norm recurrence.  No source-box invariance, contraction, or
continuum reconstruction is smuggled into this statement. -/
theorem timeTranslatedStrictJointReflectionQuadratic_transportYoung
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.leEv
      (CReal.mul (CReal.ofQ' 2)
        ((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
          hcoupling hle))
      (CReal.add
        ((strictJointDoubledTimeMixedSource shift vector).reflectionQuadratic
          hcoupling hle)
        ((strictJointDoubledTimeMixedTarget shift vector).reflectionQuadratic
          hcoupling hle)) := by
  have hidentity :
      CReal.Equiv
        ((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
          hcoupling hle)
        (strictJointDoubledTimeMixedOSBilinear
          hcoupling hle shift vector) :=
    strictJointDoubledTimeMixedOSIdentity_derived
      hcoupling hle (Nat.le_refl (shift + shift)) vector
      (fixedStage := shift + shift)
  apply leEv_mul_left_of_equiv
    (CReal.ofQ' 2)
    ((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
      hcoupling hle)
    (strictJointDoubledTimeMixedOSBilinear hcoupling hle shift vector)
    (CReal.add
      ((strictJointDoubledTimeMixedSource shift vector).reflectionQuadratic
        hcoupling hle)
      ((strictJointDoubledTimeMixedTarget shift vector).reflectionQuadratic
        hcoupling hle))
    hidentity
  exact strictJointCylinderReflectionBilinear_young
    hcoupling hle
    (strictJointDoubledTimeMixedSource shift vector)
    (strictJointDoubledTimeMixedTarget shift vector)

#print axioms finiteJointPolarizedBilinear_twice_add_difference_eqv
#print axioms centralNormalizedSupportReflectionBilinear_twice_add_difference_eqv
#print axioms centralNormalizedSupportReflectionBilinear_young
#print axioms strictJointCylinderReflectionBilinear_approx_young
#print axioms strictJointCylinderReflectionBilinear_young
#print axioms timeTranslatedStrictJointReflectionQuadratic_transportYoung

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSYoung
