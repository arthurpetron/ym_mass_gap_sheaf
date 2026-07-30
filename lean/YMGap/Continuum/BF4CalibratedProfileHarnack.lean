/-
# Harnack windows for the calibrated empty BF4 profile

The rational empty-feature factorization has a left prefix profile `L` and a
right image profile `R`.  This module proves that two pointwise relative
windows

  |L(x)-pi(x)| <= (1/64) pi(x),
  |R(x)-pi(x)| <= (1/64) pi(x)

on the retained physical carrier imply the complete empty-profile `1/16`
row budget.

The proof uses only positivity and `sum pi = 1`.  The right window gives

  sum |R-pi| <= 1/64,
  sum |R| <= 65/64,

so the profile cost is at most

  (1/64)(65/64) + 1/64 = 129/4096 < 1/16.

No minimum marginal and no carrier cardinality enter.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CalibratedEmptyProfileWindow

namespace YMGap.Continuum.BF4CalibratedProfileHarnack

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4CalibratedEmptyProfileWindow
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-- Common local Harnack tolerance. -/
def profileHarnackSixtyFourth : Q' :=
  Q'.mkPos 1 64 (by decide)

/-- The resulting right-image absolute-mass ceiling. -/
def profileHarnackRightMassCeiling : Q' :=
  Q'.mkPos 65 64 (by decide)

/-- Exact combined prefix/image cost. -/
def profileHarnackCombinedCost : Q' :=
  profileHarnackSixtyFourth *
      profileHarnackRightMassCeiling +
    profileHarnackSixtyFourth

theorem profileHarnackCombinedCost_le_sixteenth :
    profileHarnackCombinedCost ≤
      Q'.mkPos 1 16 (by decide) := by
  decide

/-- Pointwise Yang--Mills prefix/image Harnack data at one finite scale. -/
structure CalibratedEmptyProfileHarnackData
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) : Type where
  left_relative :
    ∀ source,
      source ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        calibratedEmptyLeftProfileMismatch
            w hw K halfExtent diagonalOrder crossOrder source ≤
          profileHarnackSixtyFourth *
            centralPhysicalRowMarginal
              w hw K halfExtent source
  right_relative :
    ∀ state,
      state ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        Q'.abs
            (calibratedEmptyRightProfile
                  w hw K halfExtent diagonalOrder state +
              (-centralPhysicalRowMarginal
                w hw K halfExtent state)) ≤
          profileHarnackSixtyFourth *
            centralPhysicalRowMarginal
              w hw K halfExtent state

namespace CalibratedEmptyProfileHarnackData

/-- The right pointwise window sums to a global mismatch at most `1/64`. -/
theorem rightMismatchMass_le_sixtyFourth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    (harnack :
      CalibratedEmptyProfileHarnackData
        w hw K halfExtent diagonalOrder crossOrder) :
    calibratedEmptyRightProfileMismatchMass
        w hw K halfExtent diagonalOrder ≤
      profileHarnackSixtyFourth := by
  let states :=
    centralPositiveHalfStates w hw K halfExtent
  let marginal :=
    centralPhysicalRowMarginal w hw K halfExtent
  let mismatch := fun state =>
    Q'.abs
      (calibratedEmptyRightProfile
            w hw K halfExtent diagonalOrder state +
        (-marginal state))
  unfold calibratedEmptyRightProfileMismatchMass
  refine Q'.le_trans' _ _ _
    (listQSum_mono
      mismatch
      (fun state =>
        profileHarnackSixtyFourth * marginal state)
      states
      (fun state hstate =>
        harnack.right_relative state hstate)) ?_
  refine Q'.le_of_eqv
    (Q'.eqv_trans _
      (profileHarnackSixtyFourth *
        listQSum marginal states) _
      (listQSum_mul_left
        profileHarnackSixtyFourth marginal states)
      ?_)
  exact Q'.eqv_trans _
    (profileHarnackSixtyFourth * 1) _
    (Q'.mul_eqv_congr_left
      profileHarnackSixtyFourth _ _
      (centralPositiveRowMarginal_total_one
        w hw K halfExtent))
    (Q'.mul_one_eqv profileHarnackSixtyFourth)

/-- The same pointwise window bounds the complete right-profile absolute
mass by `65/64`. -/
theorem rightAbsMass_le_ceiling
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    (harnack :
      CalibratedEmptyProfileHarnackData
        w hw K halfExtent diagonalOrder crossOrder) :
    calibratedEmptyRightProfileAbsMass
        w hw K halfExtent diagonalOrder ≤
      profileHarnackRightMassCeiling := by
  let states :=
    centralPositiveHalfStates w hw K halfExtent
  let marginal :=
    centralPhysicalRowMarginal w hw K halfExtent
  let right :=
    calibratedEmptyRightProfile
      w hw K halfExtent diagonalOrder
  have hpoint :
      ∀ state,
        state ∈ states →
          Q'.abs (right state) ≤
            profileHarnackRightMassCeiling *
              marginal state := by
    intro state hstate
    have htriangle :=
      Q'.abs_le_abs_add_abs_sub
        (right state) (marginal state)
    have hmarginal :
        (0 : Q') ≤ marginal state :=
      centralPhysicalRowMarginal_nonnegative
        hw K halfExtent state
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
      hmarginal] at htriangle
    have hwindow :=
      harnack.right_relative state hstate
    refine Q'.le_trans' _ _ _ htriangle
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_left _ _ _
          hwindow) ?_)
    exact Q'.le_of_eqv (by
      calc
        marginal state +
              profileHarnackSixtyFourth *
                marginal state ≈
            1 * marginal state +
              profileHarnackSixtyFourth *
                marginal state :=
          Q'.add_eqv_congr_right _ _ _
            (Q'.eqv_symm
              (Q'.one_mul_eqv (marginal state)))
        _ ≈
            (1 + profileHarnackSixtyFourth) *
              marginal state :=
          Q'.eqv_symm
            (Q'.add_mul_eqv
              1 profileHarnackSixtyFourth
              (marginal state))
        _ ≈ profileHarnackRightMassCeiling *
              marginal state :=
          Q'.mul_eqv_congr_right _ _ _
            (by decide))
  unfold calibratedEmptyRightProfileAbsMass
  refine Q'.le_trans' _ _ _
    (listQSum_mono
      (fun state => Q'.abs (right state))
      (fun state =>
        profileHarnackRightMassCeiling *
          marginal state)
      states hpoint) ?_
  refine Q'.le_of_eqv
    (Q'.eqv_trans _
      (profileHarnackRightMassCeiling *
        listQSum marginal states) _
      (listQSum_mul_left
        profileHarnackRightMassCeiling
        marginal states)
      ?_)
  exact Q'.eqv_trans _
    (profileHarnackRightMassCeiling * 1) _
    (Q'.mul_eqv_congr_left
      profileHarnackRightMassCeiling _ _
      (centralPositiveRowMarginal_total_one
        w hw K halfExtent))
    (Q'.mul_one_eqv profileHarnackRightMassCeiling)

/-- **Harnack-to-profile theorem.**  The two pointwise `1/64` windows pay
the complete empty-channel `1/16` row. -/
theorem profile_sixteenth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    (harnack :
      CalibratedEmptyProfileHarnackData
        w hw K halfExtent diagonalOrder crossOrder)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        centralPositiveHalfStates
          w hw K halfExtent) :
    calibratedEmptyLeftProfileMismatch
            w hw K halfExtent diagonalOrder crossOrder source *
          calibratedEmptyRightProfileAbsMass
            w hw K halfExtent diagonalOrder +
        centralPhysicalRowMarginal
            w hw K halfExtent source *
          calibratedEmptyRightProfileMismatchMass
            w hw K halfExtent diagonalOrder ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  let pi :=
    centralPhysicalRowMarginal
      w hw K halfExtent source
  let leftMismatch :=
    calibratedEmptyLeftProfileMismatch
      w hw K halfExtent diagonalOrder crossOrder source
  let rightMass :=
    calibratedEmptyRightProfileAbsMass
      w hw K halfExtent diagonalOrder
  let rightMismatch :=
    calibratedEmptyRightProfileMismatchMass
      w hw K halfExtent diagonalOrder
  have hpi : (0 : Q') ≤ pi :=
    centralPhysicalRowMarginal_nonnegative
      hw K halfExtent source
  have hleftNonnegative :
      (0 : Q') ≤ leftMismatch :=
    Q'.abs_nonneg _
  have hfirstA :
      leftMismatch * rightMass ≤
        leftMismatch *
          profileHarnackRightMassCeiling :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      harnack.rightAbsMass_le_ceiling
      hleftNonnegative
  have hceilingNonnegative :
      (0 : Q') ≤
        profileHarnackRightMassCeiling := by
    decide
  have hfirstB :
      leftMismatch *
          profileHarnackRightMassCeiling ≤
        (profileHarnackSixtyFourth * pi) *
          profileHarnackRightMassCeiling :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (harnack.left_relative source hsource)
      hceilingNonnegative
  have hsecond :
      pi * rightMismatch ≤
        pi * profileHarnackSixtyFourth :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      harnack.rightMismatchMass_le_sixtyFourth
      hpi
  have hcombined :
      leftMismatch * rightMass +
          pi * rightMismatch ≤
        (profileHarnackSixtyFourth * pi) *
            profileHarnackRightMassCeiling +
          pi * profileHarnackSixtyFourth :=
    Q'.add_le_add
      (Q'.le_trans' _ _ _ hfirstA hfirstB)
      hsecond
  have hcost :
      (profileHarnackSixtyFourth * pi) *
            profileHarnackRightMassCeiling +
          pi * profileHarnackSixtyFourth ≈
        profileHarnackCombinedCost * pi := by
    unfold profileHarnackCombinedCost
    q_ring
  refine Q'.le_trans' _ _ _ hcombined
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hcost) ?_)
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    profileHarnackCombinedCost_le_sixteenth
    hpi

end CalibratedEmptyProfileHarnackData

end YMGap.Continuum.BF4CalibratedProfileHarnack

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CalibratedProfileHarnack.CalibratedEmptyProfileHarnackData.rightMismatchMass_le_sixtyFourth
#print axioms YMGap.Continuum.BF4CalibratedProfileHarnack.CalibratedEmptyProfileHarnackData.rightAbsMass_le_ceiling
#print axioms YMGap.Continuum.BF4CalibratedProfileHarnack.CalibratedEmptyProfileHarnackData.profile_sixteenth
