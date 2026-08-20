/-
# Quantitative Cauchy--Schwarz bounds on the staged strict-cylinder carrier

This file turns the sharp rational Cauchy--Schwarz inequality at every inner
approximation into a sound `CReal.leRat` bound for the maximum-common-base
staged pairing.  The input diagonal bounds live in the transitive eventual
order.  A positive rational slack on each diagonal makes the result usable
without extracting any hidden convergence modulus from `Prop`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStageBilinearGeometry

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStageBilinearBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStageBilinearGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Eventual diagonal bounds imply a two-sided rational pairing bound -/

/-- A quantitative staged Cauchy--Schwarz bound.

The eventual diagonal bounds are sampled with slacks `u` and `1`, so the
finite-stage bounds are `2u` and `v+1`.  The displayed rational budget is
therefore sufficient to bound both the pairing and its negation by `e` in
`leRat`.  This formulation is deliberately division-free and choice-free. -/
theorem strictJointCylinderStageReflectionBilinear_twoSided_leRat
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage)
    (u v e : Q') (hu : (0 : Q') < u)
    (he : (0 : Q') < e)
    (hleft : CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle left left)
      (CReal.ofQ' u))
    (hright : CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle right right)
      (CReal.ofQ' v))
    (hbudget : (u + u) * (v + 1) <= e * e) :
    CReal.leRat
        (strictJointCylinderStageReflectionBilinear hcoupling hle left right) e ∧
      CReal.leRat
        (CReal.neg
          (strictJointCylinderStageReflectionBilinear hcoupling hle left right)) e := by
  let outer := max left.base right.base
  have hleftBase : left.base <= outer := Nat.le_max_left _ _
  have hrightBase : right.base <= outer := Nat.le_max_right _ _
  let Left := boxTransportStrictJointCylinderVector hleftBase left.vector
  let Right := boxTransportStrictJointCylinderVector hrightBase right.vector
  let leftQuadratic := Left.reflectionQuadratic hcoupling hle
  let rightQuadratic := Right.reflectionQuadratic hcoupling hle
  let fixedPair := strictJointCylinderReflectionBilinear hcoupling hle Left Right
  let stagePair := strictJointCylinderStageReflectionBilinear
    hcoupling hle left right
  have hpair : CReal.Equiv fixedPair stagePair :=
    strictJointCylinderStageReflectionBilinear_at_common
      hcoupling hle left right hleftBase hrightBase
  have hleftAtCommon := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle left left hleftBase hleftBase
  have hrightAtCommon := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle right right hrightBase hrightBase
  have hleftSelf := strictJointCylinderReflectionBilinear_self
    hcoupling hle Left
  have hrightSelf := strictJointCylinderReflectionBilinear_self
    hcoupling hle Right
  have hleftQuadraticStage : CReal.Equiv leftQuadratic
      (strictJointCylinderStageReflectionBilinear hcoupling hle left left) :=
    CReal.Equiv.trans (CReal.Equiv.symm hleftSelf) hleftAtCommon
  have hrightQuadraticStage : CReal.Equiv rightQuadratic
      (strictJointCylinderStageReflectionBilinear hcoupling hle right right) :=
    CReal.Equiv.trans (CReal.Equiv.symm hrightSelf) hrightAtCommon
  have hleftBound : CReal.leEv leftQuadratic (CReal.ofQ' u) :=
    CReal.leEv_trans (CReal.leEv_of_equiv hleftQuadraticStage) hleft
  have hrightBound : CReal.leEv rightQuadratic (CReal.ofQ' v) :=
    CReal.leEv_trans (CReal.leEv_of_equiv hrightQuadraticStage) hright
  obtain ⟨Nleft, hNleft⟩ := hleftBound u hu
  have hone : (0 : Q') < 1 := by decide
  obtain ⟨Nright, hNright⟩ := hrightBound 1 hone
  have hfixedAbs : ∃ N : Nat, ∀ stage : Nat, N <= stage ->
      Q'.abs (fixedPair.approx stage) <= e := by
    refine ⟨max Nleft Nright, fun stage hstage => ?_⟩
    have hsleft : Nleft <= stage :=
      Nat.le_trans (Nat.le_max_left _ _) hstage
    have hsright : Nright <= stage :=
      Nat.le_trans (Nat.le_max_right _ _) hstage
    have hleftUpper : leftQuadratic.approx stage <= u + u := by
      simpa [leftQuadratic] using hNleft stage hsleft
    have hrightUpper : rightQuadratic.approx stage <= v + 1 := by
      simpa [rightQuadratic] using hNright stage hsright
    have hleftNonnegative : (0 : Q') <= leftQuadratic.approx stage :=
      centralNormalizedStrictJointFixedQuadraticSequence_nonnegative
        coupling hcoupling outer Left.roots Left.coefficient stage
    have hrightNonnegative : (0 : Q') <= rightQuadratic.approx stage :=
      centralNormalizedStrictJointFixedQuadraticSequence_nonnegative
        coupling hcoupling outer Right.roots Right.coefficient stage
    have huNonnegative : (0 : Q') <= u + u :=
      Q'.zero_le_add u u (Q'.le_of_lt hu) (Q'.le_of_lt hu)
    have hproduct : leftQuadratic.approx stage * rightQuadratic.approx stage <=
        (u + u) * (v + 1) :=
      Q'.mul_le_mul_of_nonneg hleftUpper hrightUpper
        huNonnegative hrightNonnegative
    have hcs :=
      strictJointCylinderReflectionBilinear_approx_cauchy_schwarz
        hcoupling hle Left Right (stage := stage)
    have hsquare : fixedPair.approx stage * fixedPair.approx stage <= e * e :=
      Q'.le_trans' _ _ _ hcs
        (Q'.le_trans' _ _ _ hproduct hbudget)
    exact Q'.abs_le_of_sq_le_sq he hsquare
  obtain ⟨Nfixed, hNfixed⟩ := hfixedAbs
  have hfixedUpper : CReal.leRat fixedPair e :=
    CReal.leRat_of_eventually ⟨Nfixed, fun stage hstage =>
      Q'.le_trans' _ _ _ (Q'.le_abs_self (fixedPair.approx stage))
        (hNfixed stage hstage)⟩
  have hfixedNegUpper : CReal.leRat (CReal.neg fixedPair) e :=
    CReal.leRat_of_eventually ⟨Nfixed, fun stage hstage =>
      Q'.le_trans' _ _ _ (Q'.neg_le_abs (fixedPair.approx stage))
        (hNfixed stage hstage)⟩
  refine ⟨CReal.leRat_of_equiv (CReal.Equiv.symm hpair) hfixedUpper, ?_⟩
  exact CReal.leRat_of_equiv
    (CReal.neg_congr (CReal.Equiv.symm hpair)) hfixedNegUpper

#print axioms strictJointCylinderStageReflectionBilinear_twoSided_leRat

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStageBilinearBounds
