/-
# Cauchy--Schwarz for the completed strict-cylinder OS inner form

The fixed finite-support reflection form satisfies sharp rational
Cauchy--Schwarz at every inner approximation.  This file first transports the
inequality to the maximum-common-base staged pairing and then passes it through
the choice-free outer pairing limits.

The analytic ingredient is a general multiplication-continuity theorem for
convergent `CReal` sequences which derives the needed eventual bounds from the
two limits.  It does not assume the unnecessarily strong global bound on every
approximation of every sequence term.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
import YMGap.Continuum.RCCauchySchwarz

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem min'_le_left_local (p q : Q') : Q'.min' p q <= p := by
  unfold Q'.min'
  split
  · exact Q'.le_refl' p
  · exact Q'.le_of_not_le' ‹¬ p <= q›

private theorem min'_le_right_local (p q : Q') : Q'.min' p q <= q := by
  unfold Q'.min'
  split
  · exact ‹p <= q›
  · exact Q'.le_refl' q

private theorem min'_pos_local {p q : Q'}
    (hp : (0 : Q') < p) (hq : (0 : Q') < q) :
    (0 : Q') < Q'.min' p q := by
  unfold Q'.min'
  split
  · exact hp
  · exact hq

/-! ## 1. Multiplication is continuous without a supplied global bound -/

/-- Multiplication preserves convergence for arbitrary convergent constructive
real sequences.  Only eventual bounds on the two limits are used. -/
theorem CReal.convergesTo_mul_general
    {u v : Nat -> CReal} {U V : CReal}
    (hu : CReal.ConvergesTo u U) (hv : CReal.ConvergesTo v V) :
    CReal.ConvergesTo (fun k => CReal.mul (u k) (v k))
      (CReal.mul U V) := by
  intro epsilon hepsilon
  obtain ⟨NU, BU, hBU, hUbound⟩ := CReal.localBound U
  obtain ⟨NV, BV, hBV, hVbound⟩ := CReal.localBound V
  let q := Q'.min' epsilon 1
  have hqpos : (0 : Q') < q :=
    min'_pos_local hepsilon (by decide)
  have hqepsilon : q <= epsilon := min'_le_left_local epsilon 1
  have hqone : q <= (1 : Q') := min'_le_right_local epsilon 1
  let B := (BU + 1) + BV
  have hBUone : (0 : Q') <= BU + 1 :=
    Q'.zero_le_add BU 1 hBU (by decide)
  have hB : (0 : Q') <= B :=
    Q'.zero_le_add (BU + 1) BV hBUone hBV
  have honeB : (1 : Q') <= B := by
    refine Q'.le_trans' _ (BU + 1) _ ?_ ?_
    · have hcomm : Q'.eqv (BU + 1) (1 + BU) := Q'.add_comm_eqv BU 1
      exact Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg 1 BU hBU) (Q'.ge_of_eqv hcomm)
    · exact Q'.add_le_self_of_nonneg (BU + 1) BV hBV
  obtain ⟨delta, hdeltaPos, hdeltaBudget⟩ :=
    CReal.exists_mul_le hB hqpos
  have hdeltaQ : delta <= q := by
    have hdeltaB : delta <= B * delta := by
      refine Q'.le_trans' _ (1 * delta) _ ?_ ?_
      · exact Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv delta))
      · exact Q'.mul_le_mul_of_nonneg_right
          1 B delta honeB (Q'.le_of_lt hdeltaPos)
    exact Q'.le_trans' _ _ _ hdeltaB hdeltaBudget
  have hdeltaOne : delta <= (1 : Q') :=
    Q'.le_trans' _ _ _ hdeltaQ hqone
  obtain ⟨NstU, hstU⟩ := hu delta hdeltaPos
  obtain ⟨NstV, hstV⟩ := hv delta hdeltaPos
  refine ⟨max NstU NstV, fun N hN => ?_⟩
  obtain ⟨NapxU, hclU⟩ := hstU N
    (Nat.le_trans (Nat.le_max_left _ _) hN)
  obtain ⟨NapxV, hclV⟩ := hstV N
    (Nat.le_trans (Nat.le_max_right _ _) hN)
  refine ⟨max (max NapxU NapxV) (max NU NV), fun n hn => ?_⟩
  have hnUClose : NapxU <= n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnVClose : NapxV <= n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnU : NU <= n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hnV : NV <= n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  obtain ⟨huForward, huBackward⟩ := hclU n hnUClose
  obtain ⟨hvForward, hvBackward⟩ := hclV n hnVClose
  obtain ⟨hUlower, hUupper⟩ := hUbound n hnU
  obtain ⟨hVlower, hVupper⟩ := hVbound n hnV
  have huForwardOne : (u N).approx n <= U.approx n + 1 :=
    Q'.le_trans' _ _ _ huForward
      (Q'.add_le_add_left (U.approx n) delta 1 hdeltaOne)
  have huBackwardOne : U.approx n <= (u N).approx n + 1 :=
    Q'.le_trans' _ _ _ huBackward
      (Q'.add_le_add_left ((u N).approx n) delta 1 hdeltaOne)
  have huAbs : Q'.abs ((u N).approx n) <= BU + 1 := by
    refine Q'.le_trans' _ (Q'.abs (U.approx n) + 1) _ ?_ ?_
    · exact Q'.abs_le_abs_add_one_of_bounds huForwardOne huBackwardOne
    · exact Q'.add_le_add_right _ _ 1 (Q'.abs_le hUlower hUupper)
  have hVAbs : Q'.abs (V.approx n) <= BV :=
    Q'.abs_le hVlower hVupper
  have hproductDifference :
      Q'.abs ((u N).approx n * (v N).approx n +
        -(U.approx n * V.approx n)) <= epsilon := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr
        (CReal.mul_sub_decomp
          ((u N).approx n) ((v N).approx n)
          (U.approx n) (V.approx n)))) ?_
    refine Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) ?_
    have hfirst :
        Q'.abs ((u N).approx n *
          ((v N).approx n + -(V.approx n))) <= (BU + 1) * delta :=
      Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
        (Q'.mul_le_mul_of_nonneg huAbs
          (CReal.abs_sub_le_of_bounds hvForward hvBackward)
          hBUone (Q'.abs_nonneg _))
    have hsecond :
        Q'.abs (V.approx n *
          ((u N).approx n + -(U.approx n))) <= BV * delta :=
      Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
        (Q'.mul_le_mul_of_nonneg hVAbs
          (CReal.abs_sub_le_of_bounds huForward huBackward)
          hBV (Q'.abs_nonneg _))
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add hfirst hsecond) ?_
    refine Q'.le_trans' _ (B * delta) _ ?_ ?_
    · exact Q'.le_of_eqv (Q'.eqv_symm
        (Q'.add_mul_eqv (BU + 1) BV delta))
    · exact Q'.le_trans' _ _ _ hdeltaBudget hqepsilon
  exact
    ⟨ExpNeg.le_add_of_abs_sub_le hproductDifference,
      ExpNeg.le_add_of_abs_sub_le
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (ExpNeg.abs_sub_comm
              (U.approx n * V.approx n)
              ((u N).approx n * (v N).approx n)))
          hproductDifference)⟩

/-! ## 2. Cauchy--Schwarz on the staged carrier -/

theorem strictJointCylinderStageReflectionBilinear_cauchy_schwarz
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.leEv
      (CReal.mul
        (strictJointCylinderStageReflectionBilinear hcoupling hle left right)
        (strictJointCylinderStageReflectionBilinear hcoupling hle left right))
      (CReal.mul
        (strictJointCylinderStageReflectionBilinear hcoupling hle left left)
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle right right)) := by
  let outer := max left.base right.base
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hright : right.base <= outer := Nat.le_max_right _ _
  let L := boxTransportStrictJointCylinderVector hleft left.vector
  let R := boxTransportStrictJointCylinderVector hright right.vector
  let fixedPair := strictJointCylinderReflectionBilinear hcoupling hle L R
  let leftQuadratic := L.reflectionQuadratic hcoupling hle
  let rightQuadratic := R.reflectionQuadratic hcoupling hle
  have hpair := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle left right hleft hright
  have hleftCommon := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle left left hleft hleft
  have hrightCommon := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle right right hright hright
  have hleftDiagonal : CReal.Equiv leftQuadratic
      (strictJointCylinderStageReflectionBilinear hcoupling hle left left) :=
    CReal.Equiv.trans
      (CReal.Equiv.symm
        (strictJointCylinderReflectionBilinear_self hcoupling hle L))
      hleftCommon
  have hrightDiagonal : CReal.Equiv rightQuadratic
      (strictJointCylinderStageReflectionBilinear hcoupling hle right right) :=
    CReal.Equiv.trans
      (CReal.Equiv.symm
        (strictJointCylinderReflectionBilinear_self hcoupling hle R))
      hrightCommon
  have hfixed : CReal.leEv
      (CReal.mul fixedPair fixedPair)
      (CReal.mul leftQuadratic rightQuadratic) := by
    intro epsilon hepsilon
    refine ⟨0, fun stage _ => ?_⟩
    exact Q'.le_trans' _ _ _
      (strictJointCylinderReflectionBilinear_approx_cauchy_schwarz
        hcoupling hle L R (stage := stage))
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))
  exact (CReal.leEv_congr
    (YMGap.Continuum.Pivot2.mul_congr hpair hpair)
    (YMGap.Continuum.Pivot2.mul_congr
      hleftDiagonal hrightDiagonal)).mp hfixed

/-! ## 3. Passage to the completed inner form -/

theorem cauchyPairingLimit_cauchy_schwarz
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.leEv
      (CReal.mul (cauchyPairingLimit hcoupling hle X Y)
        (cauchyPairingLimit hcoupling hle X Y))
      (CReal.mul (cauchyPairingLimit hcoupling hle X X)
        (cauchyPairingLimit hcoupling hle Y Y)) := by
  apply CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_mul_general
      (cauchyPairingSeq_converges hcoupling hle X Y)
      (cauchyPairingSeq_converges hcoupling hle X Y))
    (CReal.convergesTo_mul_general
      (cauchyPairingSeq_converges hcoupling hle X X)
      (cauchyPairingSeq_converges hcoupling hle Y Y))
  intro n
  exact strictJointCylinderStageReflectionBilinear_cauchy_schwarz
    hcoupling hle (X.seq n) (Y.seq n)

/-- Sharp Cauchy--Schwarz for the `RC`-valued inner form on the actual strict OS
completion. -/
theorem strictJointCylinderCompletedInner_cauchy_schwarz
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCle
      (CReal.RCmul
        (strictJointCylinderCompletedInner hcoupling hle left right)
        (strictJointCylinderCompletedInner hcoupling hle left right))
      (CReal.RCmul
        (strictJointCylinderCompletedInner hcoupling hle left left)
        (strictJointCylinderCompletedInner hcoupling hle right right)) := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact cauchyPairingLimit_cauchy_schwarz hcoupling hle X Y

#print axioms CReal.convergesTo_mul_general
#print axioms strictJointCylinderStageReflectionBilinear_cauchy_schwarz
#print axioms cauchyPairingLimit_cauchy_schwarz
#print axioms strictJointCylinderCompletedInner_cauchy_schwarz

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
