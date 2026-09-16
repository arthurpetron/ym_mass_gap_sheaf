/-
# Explicit representative families for the original transfer cutoff limit

Every supplied ordinary-Haar Cauchy representative gives a concrete outer
Cauchy family of the SAME finite-cutoff transfer maps. An eventual rational
norm ceiling computes the outer tolerance; the existing constructive
diagonal supplies the limit representative and its modulus. No quotient
representative is selected and the transfer is not rescaled.

This module supplies the family consumed by quotient descent. It does not
define the limiting operator, a stationary state, a physical OS carrier,
or a strict gap. Nome and spatial width remain fixed parameters.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCutoffControl
import YMGap.Continuum.GNSJointPairingContinuity
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSJointPairingContinuity
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCutoffControl
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionHaarBoundedCompletion

local notation:max "N" width:arg => List.length (baseLinks width)

/-- The actual cutoff, with the finite head threshold enforced. -/
def lateCutoff (w : Q') (n : Nat) : Nat := max (headCutoff w) n

theorem lateCutoff_ge_head (w : Q') (n : Nat) : headCutoff w ≤ lateCutoff w n :=
  Nat.le_max_left _ _

theorem lateCutoff_ge_index (w : Q') (n : Nat) : n ≤ lateCutoff w n :=
  Nat.le_max_right _ _

theorem lateCutoff_eq (w : Q') (n : Nat) (hn : headCutoff w ≤ n) :
    lateCutoff w n = n := Nat.max_eq_right hn

/-- A positive unit-fraction budget computed from the input norm ceiling. -/
def familyDelta (width : Nat) (X : CauchyGNS (sliceData width).toGNSData)
    (epsilon : Q') : Q' :=
  Q'.invSucc (max epsilon.den ((sliceData width).toGNSData.normCeil X))

theorem familyDelta_positive (width : Nat)
    (X : CauchyGNS (sliceData width).toGNSData) (epsilon : Q') :
    (0 : Q') < familyDelta width X epsilon := Q'.invSucc_pos _

/-- The squared transfer tolerance pays the full eventual input norm ceiling. -/
theorem familyDelta_budget (width : Nat)
    (X : CauchyGNS (sliceData width).toGNSData) (epsilon : Q')
    (he : (0 : Q') < epsilon) :
    (familyDelta width X epsilon * familyDelta width X epsilon) *
      Q'.ofNat ((sliceData width).toGNSData.normCeil X) ≤ epsilon := by
  let a := (sliceData width).toGNSData.normCeil X
  let m := max epsilon.den a
  let delta := Q'.invSucc m
  have hd0 : (0 : Q') ≤ delta := Q'.invSucc_nonneg m
  have hd : delta ≤ epsilon :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le (Nat.le_max_left _ _))
      (HalfPow.invSucc_den_le epsilon he)
  have ha : Q'.ofNat a ≤ Q'.ofNat (m + 1) :=
    Q'.ofNat_le_ofNat (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ m))
  have had : Q'.ofNat a * delta ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ha hd0)
      (Q'.le_of_eqv (Q'.ofNat_succ_mul_invSucc m))
  have hr : ((delta * delta) * Q'.ofNat a).eqv (delta * (Q'.ofNat a * delta)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))
  change (delta * delta) * Q'.ofNat a ≤ epsilon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hr)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ had hd0)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv delta)) hd))

/-- Direct transport of the actual signed polynomial estimate to the dense carrier. -/
private theorem dense_difference_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) (epsilon : Q') (he : (0 : Q') < epsilon)
    (K J : Nat) (hK : transferCutoff w width epsilon ≤ K)
    (hJ : transferCutoff w width epsilon ≤ J) (f : (sliceData width).toGNSData.V) :
    (sliceData width).toGNSData.distSqQ
      ((denseTransfer hw0 hw1 J width (Nat.le_trans (Nat.le_max_left _ _) hJ)).toFun f)
      ((denseTransfer hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK)).toFun f) ≤
      (epsilon * epsilon) * (sliceData width).toGNSData.B f f := by
  let D := (sliceData width).toGNSData
  let a := (denseTransfer hw0 hw1 J width (Nat.le_trans (Nat.le_max_left _ _) hJ)).toFun f
  let b := (denseTransfer hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK)).toFun f
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haarData_pair (N width) (D.sub a b) (D.sub a b)))
    (Q'.le_trans' _ _ _
      (transferStep_difference_bound hw0 hw1 width epsilon he K J
        (Nat.le_trans (Nat.le_max_right _ _) hK) (Nat.le_trans (Nat.le_max_right _ _) hJ) f.property)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (haarData_pair (N width) f f)))))

/-- The computed outer modulus for the actual cutoff representatives. -/
def cutoffFamily {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (X : CauchyGNS (sliceData width).toGNSData) :
    GeneralCompletionCauchy (sliceData width).toGNSData where
  pt n := (denseTransfer hw0 hw1 (lateCutoff w n) width (lateCutoff_ge_head w n)).mapCauchy X
  mod epsilon := transferCutoff w width (familyDelta width X epsilon)
  cauchy := by
    intro epsilon he p q hp hq
    let D := (sliceData width).toGNSData
    let delta := familyDelta width X epsilon
    have hd : (0 : Q') < delta := familyDelta_positive width X epsilon
    have hp' : transferCutoff w width delta ≤ lateCutoff w p :=
      Nat.le_trans hp (lateCutoff_ge_index w p)
    have hq' : transferCutoff w width delta ≤ lateCutoff w q :=
      Nat.le_trans hq (lateCutoff_ge_index w q)
    refine ⟨D.normBase X, fun n hn => ?_⟩
    exact Q'.le_trans' _ _ _
      (dense_difference_bound hw0 hw1 width delta hd
        (lateCutoff w q) (lateCutoff w p) hq' hp' (X.seq n))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (D.normCeil_bound X n hn)
          (Q'.mul_nonneg _ _ (Q'.le_of_lt hd) (Q'.le_of_lt hd)))
        (familyDelta_budget width X epsilon he))

theorem cutoffFamily_seq {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (X : CauchyGNS (sliceData width).toGNSData) (p n : Nat) :
    (((cutoffFamily hw0 hw1 width X).pt p).seq n) =
      (denseTransfer hw0 hw1 (lateCutoff w p) width (lateCutoff_ge_head w p)).toFun (X.seq n) := rfl

/-- The existing explicit constructive diagonal, with no representative choice. -/
def limitRep {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (X : CauchyGNS (sliceData width).toGNSData) :
    CauchyGNS (sliceData width).toGNSData := (cutoffFamily hw0 hw1 width X).lim

theorem limitRep_modulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (X : CauchyGNS (sliceData width).toGNSData) (epsilon : Q') :
    (limitRep hw0 hw1 width X).modulus epsilon = gMod epsilon := rfl

/-- The outer convergence rate, still literal computable natural-number data. -/
def familyRate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (X : CauchyGNS (sliceData width).toGNSData) (epsilon : Q') : Nat :=
  limitRate (cutoffFamily hw0 hw1 width X) epsilon

theorem familyRate_eq {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (X : CauchyGNS (sliceData width).toGNSData) (epsilon : Q') :
    familyRate hw0 hw1 width X epsilon =
      transferCutoff w width (familyDelta width X (HalfPow.half * (HalfPow.half * epsilon))) := rfl

theorem head_le_familyRate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (X : CauchyGNS (sliceData width).toGNSData) (epsilon : Q') :
    headCutoff w ≤ familyRate hw0 hw1 width X epsilon := Nat.le_max_left _ _

/-- Eventual representative closeness at the supplied explicit cutoff rate. -/
theorem family_close_at {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (X : CauchyGNS (sliceData width).toGNSData) (epsilon : Q')
    (he : (0 : Q') < epsilon) (p : Nat) (hp : familyRate hw0 hw1 width X epsilon ≤ p) :
    ∃ innerCutoff, ∀ n, innerCutoff ≤ n → (sliceData width).toGNSData.distSqQ
      (((cutoffFamily hw0 hw1 width X).pt p).seq n) ((limitRep hw0 hw1 width X).seq n) ≤ epsilon :=
  limit_close_at (cutoffFamily hw0 hw1 width X) epsilon he p hp

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.lateCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.lateCutoff_ge_head
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.lateCutoff_ge_index
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.lateCutoff_eq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.familyDelta
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.familyDelta_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.familyDelta_budget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.cutoffFamily
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.cutoffFamily_seq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.limitRep
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.limitRep_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.familyRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.familyRate_eq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.head_le_familyRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily.family_close_at
