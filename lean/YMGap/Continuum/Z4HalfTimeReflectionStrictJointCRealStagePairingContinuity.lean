/-
# Four-stage continuity of the strict reflection pairing

This leaf lifts the fixed-common-box estimate from
`Z4HalfTimeReflectionStrictJointCRealPairingContinuity` to the quotient-free
staged direct carrier.  Four independently based stage representatives are
transported into one common box.  The two squared-distance hypotheses and the
two diagonal bounds are stated using the regularity-free `CReal.leRat`
predicate, so the proof reserves an explicit positive rational slack before
applying the approximation-level estimate.

The conclusion is deliberately two-sided.  Since `leRat` is a one-sided
rational upper-bound predicate, the conjunction below is the direct staged
analogue of an absolute-value continuity estimate and is the form needed by
later constructive Cauchy arguments.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingContinuity
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
import YMGap.Constructive.ExpAdd

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStagePairingContinuity

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingContinuity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-!
## The common-box `leRat` continuity theorem

The `slack` parameter is mathematically essential at this API boundary:
`CReal.leRat X delta` supplies eventual inequalities
`X.approx n <= delta + eta`, not eventual exact inequalities
`X.approx n <= delta`.  Thus the finite-stage estimate is invoked with
`delta + slack` and `bound + slack`, and the caller certifies the corresponding
product budget.
-/

/-- Four-stage, common-box, sqrt-free continuity of the strict reflection
pairing.

Both input displacements are controlled by the staged OS squared distance.
The two undifferenced factors required by the bilinear difference split are
controlled invariantly as staged self-pairings.  An explicit positive rational
`slack` converts all four `leRat` hypotheses into simultaneous eventual
approximation bounds.
-/
theorem strictJointCylinderStageReflectionBilinear_difference_leRat
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left left' right right' : StrictJointCylinderStage)
    (epsilon delta bound slack : Q')
    (hepsilon : (0 : Q') < epsilon)
    (hdelta : (0 : Q') < delta)
    (hslack : (0 : Q') < slack)
    (hleftDist :
      CReal.leRat
        (strictJointCylinderStageReflectionDistSq
          hcoupling hle left left') delta)
    (hrightDist :
      CReal.leRat
        (strictJointCylinderStageReflectionDistSq
          hcoupling hle right right') delta)
    (hrightBound :
      CReal.leRat
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle right right) bound)
    (hleft'Bound :
      CReal.leRat
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle left' left') bound)
    (hbudget :
      (delta + slack) * (bound + slack) <=
        (HalfPow.half * epsilon) * (HalfPow.half * epsilon)) :
    CReal.leRat
        (CReal.add
          (strictJointCylinderStageReflectionBilinear
            hcoupling hle left right)
          (CReal.neg
            (strictJointCylinderStageReflectionBilinear
              hcoupling hle left' right'))) epsilon
      /\
    CReal.leRat
        (CReal.add
          (strictJointCylinderStageReflectionBilinear
            hcoupling hle left' right')
          (CReal.neg
            (strictJointCylinderStageReflectionBilinear
              hcoupling hle left right))) epsilon := by
  let outer : Nat :=
    max (max left.base left'.base) (max right.base right'.base)
  have hleft : left.base <= outer := by
    dsimp [outer]
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hleft' : left'.base <= outer := by
    dsimp [outer]
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hright : right.base <= outer := by
    dsimp [outer]
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hright' : right'.base <= outer := by
    dsimp [outer]
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

  let leftCommon : StrictJointCylinderVector outer :=
    boxTransportStrictJointCylinderVector hleft left.vector
  let left'Common : StrictJointCylinderVector outer :=
    boxTransportStrictJointCylinderVector hleft' left'.vector
  let rightCommon : StrictJointCylinderVector outer :=
    boxTransportStrictJointCylinderVector hright right.vector
  let right'Common : StrictJointCylinderVector outer :=
    boxTransportStrictJointCylinderVector hright' right'.vector

  have hleftDistCommon :
      CReal.leRat
        (strictJointCylinderReflectionDistSq
          hcoupling hle leftCommon left'Common) delta := by
    exact CReal.leRat_of_equiv
      (strictJointCylinderStageReflectionDistSq_at_common
        hcoupling hle left left' hleft hleft') hleftDist
  have hrightDistCommon :
      CReal.leRat
        (strictJointCylinderReflectionDistSq
          hcoupling hle rightCommon right'Common) delta := by
    exact CReal.leRat_of_equiv
      (strictJointCylinderStageReflectionDistSq_at_common
        hcoupling hle right right' hright hright') hrightDist

  have hrightPairCommon : CReal.Equiv
      (strictJointCylinderReflectionBilinear
        hcoupling hle rightCommon rightCommon)
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle right right) := by
    exact strictJointCylinderStageReflectionBilinear_at_common
      hcoupling hle right right hright hright
  have hleft'PairCommon : CReal.Equiv
      (strictJointCylinderReflectionBilinear
        hcoupling hle left'Common left'Common)
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left' left') := by
    exact strictJointCylinderStageReflectionBilinear_at_common
      hcoupling hle left' left' hleft' hleft'
  have hrightQuadraticToStage : CReal.Equiv
      (rightCommon.reflectionQuadratic hcoupling hle)
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle right right) :=
    CReal.Equiv.trans
      (CReal.Equiv.symm
        (strictJointCylinderReflectionBilinear_self
          hcoupling hle rightCommon))
      hrightPairCommon
  have hleft'QuadraticToStage : CReal.Equiv
      (left'Common.reflectionQuadratic hcoupling hle)
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left' left') :=
    CReal.Equiv.trans
      (CReal.Equiv.symm
        (strictJointCylinderReflectionBilinear_self
          hcoupling hle left'Common))
      hleft'PairCommon
  have hrightBoundCommon :
      CReal.leRat
        (rightCommon.reflectionQuadratic hcoupling hle) bound :=
    CReal.leRat_of_equiv hrightQuadraticToStage hrightBound
  have hleft'BoundCommon :
      CReal.leRat
        (left'Common.reflectionQuadratic hcoupling hle) bound :=
    CReal.leRat_of_equiv hleft'QuadraticToStage hleft'Bound

  obtain ⟨nLeftDist, hnLeftDist⟩ := hleftDistCommon slack hslack
  obtain ⟨nRightDist, hnRightDist⟩ := hrightDistCommon slack hslack
  obtain ⟨nRightBound, hnRightBound⟩ := hrightBoundCommon slack hslack
  obtain ⟨nLeft'Bound, hnLeft'Bound⟩ := hleft'BoundCommon slack hslack
  let cutoff : Nat :=
    max (max nLeftDist nRightDist) (max nRightBound nLeft'Bound)

  have hcommonEventually : forall stage : Nat, cutoff <= stage ->
      (CReal.add
          (strictJointCylinderReflectionBilinear
            hcoupling hle leftCommon rightCommon)
          (CReal.neg
            (strictJointCylinderReflectionBilinear
              hcoupling hle left'Common right'Common))).approx stage <= epsilon
        /\
      (CReal.add
          (strictJointCylinderReflectionBilinear
            hcoupling hle left'Common right'Common)
          (CReal.neg
            (strictJointCylinderReflectionBilinear
              hcoupling hle leftCommon rightCommon))).approx stage <= epsilon := by
    intro stage hstage
    have hnLeftDistStage : nLeftDist <= stage :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hstage
    have hnRightDistStage : nRightDist <= stage :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hstage
    have hnRightBoundStage : nRightBound <= stage :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hstage
    have hnLeft'BoundStage : nLeft'Bound <= stage :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hstage
    have hleftDistStage :
        ((strictJointCylinderDifference leftCommon left'Common).reflectionQuadratic
          hcoupling hle).approx stage <= delta + slack := by
      simpa only [strictJointCylinderReflectionDistSq] using
        (hnLeftDist stage hnLeftDistStage)
    have hrightDistStage :
        ((strictJointCylinderDifference rightCommon right'Common).reflectionQuadratic
          hcoupling hle).approx stage <= delta + slack := by
      simpa only [strictJointCylinderReflectionDistSq] using
        (hnRightDist stage hnRightDistStage)
    have habs :=
      strictJointCylinderReflectionBilinear_approx_abs_sub_le
        hcoupling hle (stage := stage)
        leftCommon left'Common rightCommon right'Common
        epsilon (delta + slack) (bound + slack)
        hepsilon (Q'.add_pos hdelta hslack)
        hleftDistStage hrightDistStage
        (hnRightBound stage hnRightBoundStage)
        (hnLeft'Bound stage hnLeft'BoundStage)
        hbudget
    have htwo := Q'.two_sided_of_abs_sub_le habs
    change
      ((strictJointCylinderReflectionBilinear
          hcoupling hle leftCommon rightCommon).approx stage +
        -(strictJointCylinderReflectionBilinear
          hcoupling hle left'Common right'Common).approx stage <= epsilon)
        /\
      ((strictJointCylinderReflectionBilinear
          hcoupling hle left'Common right'Common).approx stage +
        -(strictJointCylinderReflectionBilinear
          hcoupling hle leftCommon rightCommon).approx stage <= epsilon)
    exact ⟨Q'.sub_le_of_le_add htwo.1, Q'.sub_le_of_le_add htwo.2⟩

  have hforwardCommon :
      CReal.leRat
        (CReal.add
          (strictJointCylinderReflectionBilinear
            hcoupling hle leftCommon rightCommon)
          (CReal.neg
            (strictJointCylinderReflectionBilinear
              hcoupling hle left'Common right'Common))) epsilon :=
    CReal.leRat_of_eventually
      ⟨cutoff, fun stage hstage => (hcommonEventually stage hstage).1⟩
  have hbackwardCommon :
      CReal.leRat
        (CReal.add
          (strictJointCylinderReflectionBilinear
            hcoupling hle left'Common right'Common)
          (CReal.neg
            (strictJointCylinderReflectionBilinear
              hcoupling hle leftCommon rightCommon))) epsilon :=
    CReal.leRat_of_eventually
      ⟨cutoff, fun stage hstage => (hcommonEventually stage hstage).2⟩

  have hleftRightCommon : CReal.Equiv
      (strictJointCylinderReflectionBilinear
        hcoupling hle leftCommon rightCommon)
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left right) := by
    exact strictJointCylinderStageReflectionBilinear_at_common
      hcoupling hle left right hleft hright
  have hleft'Right'Common : CReal.Equiv
      (strictJointCylinderReflectionBilinear
        hcoupling hle left'Common right'Common)
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left' right') := by
    exact strictJointCylinderStageReflectionBilinear_at_common
      hcoupling hle left' right' hleft' hright'
  have hforwardStageToCommon : CReal.Equiv
      (CReal.add
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle left right)
        (CReal.neg
          (strictJointCylinderStageReflectionBilinear
            hcoupling hle left' right')))
      (CReal.add
        (strictJointCylinderReflectionBilinear
          hcoupling hle leftCommon rightCommon)
        (CReal.neg
          (strictJointCylinderReflectionBilinear
            hcoupling hle left'Common right'Common))) :=
    CReal.Equiv_add
      (CReal.Equiv.symm hleftRightCommon)
      (CReal.neg_congr (CReal.Equiv.symm hleft'Right'Common))
  have hbackwardStageToCommon : CReal.Equiv
      (CReal.add
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle left' right')
        (CReal.neg
          (strictJointCylinderStageReflectionBilinear
            hcoupling hle left right)))
      (CReal.add
        (strictJointCylinderReflectionBilinear
          hcoupling hle left'Common right'Common)
        (CReal.neg
          (strictJointCylinderReflectionBilinear
            hcoupling hle leftCommon rightCommon))) :=
    CReal.Equiv_add
      (CReal.Equiv.symm hleft'Right'Common)
      (CReal.neg_congr (CReal.Equiv.symm hleftRightCommon))
  exact
    ⟨CReal.leRat_of_equiv hforwardStageToCommon hforwardCommon,
      CReal.leRat_of_equiv hbackwardStageToCommon hbackwardCommon⟩

#print axioms strictJointCylinderStageReflectionBilinear_difference_leRat

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStagePairingContinuity
