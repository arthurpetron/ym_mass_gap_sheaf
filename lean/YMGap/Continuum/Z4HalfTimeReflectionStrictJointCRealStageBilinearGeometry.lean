/-
# Bilinear geometry on the staged strict-cylinder OS carrier

This file lifts the fixed-base symmetry, additivity, homogeneity, and diagonal
identities of the strict reflection form to the maximum-common-base staged
carrier.  These are the pointwise identities needed to prove that pairings of
Cauchy representatives form a Cauchy sequence and later descend the completed
inner form.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalarLaws
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealBilinearInnerRegularity

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStageBilinearGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdd
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveLaws
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalar
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionZeroNeg
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem creal_mul_congr_right
    {scalar left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  CReal.Equiv.trans (CRealAlg.cmul_comm scalar left)
    (CReal.Equiv.trans (CReal.mul_congr_left h)
      (CRealAlg.cmul_comm right scalar))

private theorem ofQ'_neg_one_mul_equiv_neg (value : CReal) :
    CReal.Equiv (CReal.mul (CReal.ofQ' (-1)) value) (CReal.neg value) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (value.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (value.approx n))))

private theorem boxTransportStrictJointCylinderVector_smul_of_le
    {base outer : Nat} (hbase : base <= outer)
    (scalar : Q') (vector : StrictJointCylinderVector base) :
    boxTransportStrictJointCylinderVector hbase (vector.smul scalar) =
      (boxTransportStrictJointCylinderVector hbase vector).smul scalar := by
  obtain ⟨padding, rfl⟩ := Nat.exists_eq_add_of_le hbase
  exact boxTransportStrictJointCylinderVector_smul padding scalar vector

/-! ## 1. Fixed-base diagonal identification -/

/-- The diagonal pairing is the squared distance to any semantically zero
presentation at the same base. -/
theorem strictJointCylinderReflectionBilinear_self_equiv_distSq_zeroLike
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector zeroLike : StrictJointCylinderVector base)
    (hzero : forall bits, zeroLike.coefficient bits ≈ 0) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle vector vector)
      (strictJointCylinderReflectionDistSq
        hcoupling hle vector zeroLike) := by
  have hrecover : StrictJointCylinderVectorEquivalent vector
      ((strictJointCylinderDifference vector zeroLike).add zeroLike) :=
    strictJointCylinderDifference_add_right_equivalent vector zeroLike
  have hdrop : StrictJointCylinderVectorEquivalent
      ((strictJointCylinderDifference vector zeroLike).add zeroLike)
      (strictJointCylinderDifference vector zeroLike) :=
    strictJointCylinderVector_add_zeroLike_equivalent
      (strictJointCylinderDifference vector zeroLike) zeroLike hzero
  have hdiff : StrictJointCylinderVectorEquivalent
      (strictJointCylinderDifference vector zeroLike) vector :=
    strictJointCylinderVectorEquivalent_symm
      (strictJointCylinderVectorEquivalent_trans hrecover hdrop)
  have hquadratic := StrictJointCylinderVector.reflectionQuadratic_equiv
    hcoupling hle hdiff
  exact CReal.Equiv.trans
    (strictJointCylinderReflectionBilinear_self hcoupling hle vector)
    (CReal.Equiv.symm hquadratic)

/-! ## 2. Staged symmetry and diagonal -/

/-- Algebraic subtraction on the staged carrier. -/
def strictJointCylinderStageSub
    (left right : StrictJointCylinderStage) : StrictJointCylinderStage :=
  strictJointCylinderStageAdd left (strictJointCylinderStageNeg right)

theorem strictJointCylinderStageReflectionBilinear_symm
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle left right)
      (strictJointCylinderStageReflectionBilinear hcoupling hle right left) := by
  let outer := max left.base right.base
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hright : right.base <= outer := Nat.le_max_right _ _
  have hforward := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle left right hleft hright
  have hbackward := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle right left hright hleft
  exact CReal.Equiv.trans (CReal.Equiv.symm hforward)
    (CReal.Equiv.trans
      (StrictJointCylinderVector.reflectionBilinear_symm hcoupling hle _ _)
      hbackward)

theorem strictJointCylinderStageReflectionBilinear_self_equiv_distSq_zero
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle stage stage)
      (strictJointCylinderStageReflectionDistSq
        hcoupling hle stage strictJointCylinderStageZero) := by
  have hstage := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle stage stage (Nat.le_refl _) (Nat.le_refl _)
  have hdist := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle stage strictJointCylinderStageZero
      (Nat.le_refl _) (Nat.zero_le _)
  have hfixed :=
    strictJointCylinderReflectionBilinear_self_equiv_distSq_zeroLike
      hcoupling hle
      (boxTransportStrictJointCylinderVector
        (Nat.le_refl _) stage.vector)
      (boxTransportStrictJointCylinderVector
        (Nat.zero_le _) strictJointCylinderStageZero.vector)
      (fun bits => Q'.eqv_refl 0)
  exact CReal.Equiv.trans (CReal.Equiv.symm hstage)
    (CReal.Equiv.trans hfixed hdist)

/-- The diagonal pairing of the staged algebraic difference is exactly the
squared OS distance between its endpoints. -/
theorem strictJointCylinderStageReflectionBilinear_sub_self_equiv_distSq
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (strictJointCylinderStageSub left right)
        (strictJointCylinderStageSub left right))
      (strictJointCylinderStageReflectionDistSq
        hcoupling hle left right) := by
  let outer := max left.base right.base
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hright : right.base <= outer := Nat.le_max_right _ _
  have hsub : (strictJointCylinderStageSub left right).base <= outer := by
    exact Nat.max_le.mpr ⟨hleft, hright⟩
  have hstage := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle (strictJointCylinderStageSub left right)
      (strictJointCylinderStageSub left right) hsub hsub
  have hdist := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle left right hleft hright
  have htransportRaw := strictJointCylinderStage_add_transport
    left (strictJointCylinderStageNeg right) hleft hright
  have hnegTransport := boxTransportStrictJointCylinderVector_smul_of_le
    hright (-1) right.vector
  change boxTransportStrictJointCylinderVector hright
      (strictJointCylinderStageNeg right).vector =
    (boxTransportStrictJointCylinderVector hright right.vector).smul (-1)
    at hnegTransport
  have htransport :
      boxTransportStrictJointCylinderVector hsub
          (strictJointCylinderStageSub left right).vector =
        (boxTransportStrictJointCylinderVector hleft left.vector).add
          ((boxTransportStrictJointCylinderVector hright right.vector).smul (-1)) := by
    exact Eq.trans (by
      simpa [strictJointCylinderStageSub] using htransportRaw)
      (congrArg
        (fun value =>
          (boxTransportStrictJointCylinderVector hleft left.vector).add value)
        hnegTransport)
  have hself := strictJointCylinderReflectionBilinear_self hcoupling hle
    (boxTransportStrictJointCylinderVector hsub
      (strictJointCylinderStageSub left right).vector)
  rw [htransport] at hstage
  rw [htransport] at hself
  exact CReal.Equiv.trans (CReal.Equiv.symm hstage)
    (CReal.Equiv.trans hself hdist)

/-! ## 3. Staged additivity and homogeneity -/

theorem strictJointCylinderStageReflectionBilinear_add_left
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (first second right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (strictJointCylinderStageAdd first second) right)
      (CReal.add
        (strictJointCylinderStageReflectionBilinear hcoupling hle first right)
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle second right)) := by
  let outer := max (max first.base second.base) right.base
  have hfirst : first.base <= outer := Nat.le_trans
    (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hsecond : second.base <= outer := Nat.le_trans
    (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hright : right.base <= outer := Nat.le_max_right _ _
  have hsum : (strictJointCylinderStageAdd first second).base <= outer :=
    Nat.max_le.mpr ⟨hfirst, hsecond⟩
  have hsumPair := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle (strictJointCylinderStageAdd first second) right hsum hright
  have hfirstPair := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle first right hfirst hright
  have hsecondPair := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle second right hsecond hright
  have htransport := strictJointCylinderStage_add_transport
    first second hfirst hsecond
  have hadd := strictJointCylinderReflectionBilinear_add_left
    hcoupling hle
    (boxTransportStrictJointCylinderVector hfirst first.vector)
    (boxTransportStrictJointCylinderVector hsecond second.vector)
    (boxTransportStrictJointCylinderVector hright right.vector)
  rw [← htransport] at hadd
  exact CReal.Equiv.trans (CReal.Equiv.symm hsumPair)
    (CReal.Equiv.trans hadd (CReal.Equiv_add hfirstPair hsecondPair))

theorem strictJointCylinderStageReflectionBilinear_add_right
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left first second : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle left
        (strictJointCylinderStageAdd first second))
      (CReal.add
        (strictJointCylinderStageReflectionBilinear hcoupling hle left first)
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle left second)) := by
  exact CReal.Equiv.trans
    (strictJointCylinderStageReflectionBilinear_symm
      hcoupling hle left (strictJointCylinderStageAdd first second))
    (CReal.Equiv.trans
      (strictJointCylinderStageReflectionBilinear_add_left
        hcoupling hle first second left)
      (CReal.Equiv_add
        (strictJointCylinderStageReflectionBilinear_symm
          hcoupling hle first left)
        (strictJointCylinderStageReflectionBilinear_symm
          hcoupling hle second left)))

theorem strictJointCylinderStageReflectionBilinear_smul_left
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (scalar : Q') (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (strictJointCylinderStageSmul scalar left) right)
      (CReal.mul (CReal.ofQ' scalar)
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle left right)) := by
  let outer := max left.base right.base
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hright : right.base <= outer := Nat.le_max_right _ _
  have hscaled := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle (strictJointCylinderStageSmul scalar left) right hleft hright
  have horiginal := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle left right hleft hright
  have hfixed := strictJointCylinderReflectionBilinear_smul_left
    hcoupling hle scalar
    (boxTransportStrictJointCylinderVector hleft left.vector)
    (boxTransportStrictJointCylinderVector hright right.vector)
  rw [← boxTransportStrictJointCylinderVector_smul_of_le hleft] at hfixed
  exact CReal.Equiv.trans (CReal.Equiv.symm hscaled)
    (CReal.Equiv.trans hfixed (creal_mul_congr_right horiginal))

theorem strictJointCylinderStageReflectionBilinear_smul_right
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (scalar : Q') (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle left
        (strictJointCylinderStageSmul scalar right))
      (CReal.mul (CReal.ofQ' scalar)
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle left right)) := by
  exact CReal.Equiv.trans
    (strictJointCylinderStageReflectionBilinear_symm
      hcoupling hle left (strictJointCylinderStageSmul scalar right))
    (CReal.Equiv.trans
      (strictJointCylinderStageReflectionBilinear_smul_left
        hcoupling hle scalar right left)
      (creal_mul_congr_right
        (strictJointCylinderStageReflectionBilinear_symm
          hcoupling hle right left)))

/-- Subtraction in the left argument becomes subtraction of pairings. -/
theorem strictJointCylinderStageReflectionBilinear_sub_left
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (first second right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (strictJointCylinderStageSub first second) right)
      (CReal.add
        (strictJointCylinderStageReflectionBilinear hcoupling hle first right)
        (CReal.neg
          (strictJointCylinderStageReflectionBilinear
            hcoupling hle second right))) := by
  have hadd := strictJointCylinderStageReflectionBilinear_add_left
    hcoupling hle first (strictJointCylinderStageNeg second) right
  have hsmul := strictJointCylinderStageReflectionBilinear_smul_left
    hcoupling hle (-1) second right
  change CReal.Equiv
    (strictJointCylinderStageReflectionBilinear hcoupling hle
      (strictJointCylinderStageNeg second) right)
    (CReal.mul (CReal.ofQ' (-1))
      (strictJointCylinderStageReflectionBilinear hcoupling hle second right))
    at hsmul
  have hneg := CReal.Equiv.trans hsmul
    (ofQ'_neg_one_mul_equiv_neg
      (strictJointCylinderStageReflectionBilinear hcoupling hle second right))
  exact CReal.Equiv.trans hadd (CReal.add_congr_right hneg)

/-- Bilinear telescope for two staged endpoint pairs. -/
theorem strictJointCylinderStageReflectionBilinear_diff_split
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left left' right right' : StrictJointCylinderStage) :
    CReal.Equiv
      (CReal.add
        (strictJointCylinderStageReflectionBilinear hcoupling hle left right)
        (CReal.neg
          (strictJointCylinderStageReflectionBilinear
            hcoupling hle left' right')))
      (CReal.add
        (strictJointCylinderStageReflectionBilinear hcoupling hle
          (strictJointCylinderStageSub left left') right)
        (strictJointCylinderStageReflectionBilinear hcoupling hle
          (strictJointCylinderStageSub right right') left')) := by
  let P := strictJointCylinderStageReflectionBilinear hcoupling hle left right
  let Q := strictJointCylinderStageReflectionBilinear hcoupling hle left' right
  let R := strictJointCylinderStageReflectionBilinear hcoupling hle left' right'
  have hfirst := strictJointCylinderStageReflectionBilinear_sub_left
    hcoupling hle left left' right
  have hsecondRaw := strictJointCylinderStageReflectionBilinear_sub_left
    hcoupling hle right right' left'
  have hsecond : CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (strictJointCylinderStageSub right right') left')
      (CReal.add Q (CReal.neg R)) := by
    have hQ : CReal.Equiv
        (strictJointCylinderStageReflectionBilinear hcoupling hle right left') Q :=
      CReal.Equiv.symm
        (strictJointCylinderStageReflectionBilinear_symm
          hcoupling hle left' right)
    have hR : CReal.Equiv
        (strictJointCylinderStageReflectionBilinear hcoupling hle right' left') R :=
      strictJointCylinderStageReflectionBilinear_symm
        hcoupling hle right' left'
    exact CReal.Equiv.trans hsecondRaw
      (CReal.Equiv.trans (CReal.add_congr_left hQ)
        (CReal.add_congr_right (CReal.neg_congr hR)))
  have hterms : CReal.Equiv
      (CReal.add
        (strictJointCylinderStageReflectionBilinear hcoupling hle
          (strictJointCylinderStageSub left left') right)
        (strictJointCylinderStageReflectionBilinear hcoupling hle
          (strictJointCylinderStageSub right right') left'))
      (CReal.add (CReal.add P (CReal.neg Q))
        (CReal.add Q (CReal.neg R))) :=
    CReal.Equiv.trans (CReal.add_congr_left hfirst)
      (CReal.add_congr_right hsecond)
  have htelescope : CReal.Equiv
      (CReal.add (CReal.add P (CReal.neg Q))
        (CReal.add Q (CReal.neg R)))
      (CReal.add P (CReal.neg R)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => by
      refine Q'.eqv_trans _ _ _
        (Q'.rearr_ABXY (P.approx n) (-(Q.approx n))
          (Q.approx n) (-(R.approx n))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ 0
          (Q'.neg_add_self_eqv (Q.approx n))) ?_
      exact QPoly.q_add_zero_eqv _)
  exact CReal.Equiv.trans (CReal.Equiv.symm htelescope)
    (CReal.Equiv.symm hterms)

#print axioms strictJointCylinderReflectionBilinear_self_equiv_distSq_zeroLike
#print axioms strictJointCylinderStageReflectionBilinear_symm
#print axioms strictJointCylinderStageReflectionBilinear_self_equiv_distSq_zero
#print axioms strictJointCylinderStageReflectionBilinear_sub_self_equiv_distSq
#print axioms strictJointCylinderStageReflectionBilinear_add_left
#print axioms strictJointCylinderStageReflectionBilinear_add_right
#print axioms strictJointCylinderStageReflectionBilinear_smul_left
#print axioms strictJointCylinderStageReflectionBilinear_smul_right
#print axioms strictJointCylinderStageReflectionBilinear_sub_left
#print axioms strictJointCylinderStageReflectionBilinear_diff_split

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStageBilinearGeometry
