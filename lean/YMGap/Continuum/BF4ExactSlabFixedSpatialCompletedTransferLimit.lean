/-
# The actual fixed-spatial cutoff-limit operator on ordinary Haar completion

The supplied cutoff-Cauchy family has a computed diagonal representative.
A same-cutoff three-hop comparison proves null descent, so the operator is
defined on the EXISTING completion without choosing representatives. The
original finite-cutoff norm cap and norm-relative cutoff rate pass to it.

No rescaling, layer normalization, stationary state or physical OS
identification is introduced. Nome/width dependence remains explicit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily
import YMGap.Continuum.GNSNullModulusRecovery

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSNullModulusRecovery
open YMGap.Continuum.GNSJointPairingContinuity
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (stepCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCutoffControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionHaarBoundedCompletion

private theorem tiny_budget (epsilon : Q') : treeval (nullTolerance epsilon) ≤ epsilon := by
  refine Q'.le_trans' _ _ _ (treeval_le_ten _) (Q'.le_of_eqv ?_)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (by decide : Q'.eqv ((10 : Q') * Q'.mkPos 1 10 (by decide)) 1)) (Q'.one_mul_eqv _))

/-- Same-cutoff comparison makes the constructed diagonal respect null representatives. -/
theorem limitRep_null {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) {X Y : CauchyGNS (sliceData width).toGNSData}
    (h : CauchyNull (sliceData width).toGNSData X Y) :
    CauchyNull (sliceData width).toGNSData
      (limitRep hw0 hw1 width X) (limitRep hw0 hw1 width Y) := by
  intro epsilon he
  let D := (sliceData width).toGNSData
  let tiny := nullTolerance epsilon
  have htiny : (0 : Q') < tiny := nullTolerance_pos he
  let p := max (familyRate hw0 hw1 width X tiny) (familyRate hw0 hw1 width Y tiny)
  obtain ⟨NX, hNX⟩ := family_close_at hw0 hw1 width X tiny htiny p (Nat.le_max_left _ _)
  obtain ⟨NY, hNY⟩ := family_close_at hw0 hw1 width Y tiny htiny p (Nat.le_max_right _ _)
  let T := denseTransfer hw0 hw1 (lateCutoff w p) width (Nat.le_max_left _ _)
  obtain ⟨NM, hNM⟩ := T.mapCauchy_null h tiny htiny
  refine ⟨max (max NX NY) NM, fun n hn => ?_⟩
  have hx := hNX n (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn)
  have hy := hNY n (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn)
  have hm := hNM n (Nat.le_trans (Nat.le_max_right _ _) hn)
  exact Q'.le_trans' _ _ _
    (D.quad3 ((limitRep hw0 hw1 width X).seq n) ((T.mapCauchy X).seq n)
      ((T.mapCauchy Y).seq n) ((limitRep hw0 hw1 width Y).seq n) tiny
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (D.distSqQ_comm _ _)) hx) hm hy)
    (tiny_budget epsilon)

/-- The actual unrescaled cutoff-limit map on the existing ordinary-Haar completion. -/
def completedLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) :
    GNSCompletionSpace (sliceData width).toGNSData →
      GNSCompletionSpace (sliceData width).toGNSData :=
  Quotient.lift (fun X => Quotient.mk (cauchySetoid (sliceData width).toGNSData)
    (limitRep hw0 hw1 width X))
    (fun _ _ h => Quotient.sound (limitRep_null hw0 hw1 width h))

theorem completedLimit_mk {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (X : CauchyGNS (sliceData width).toGNSData) :
    completedLimit hw0 hw1 width (Quotient.mk (cauchySetoid (sliceData width).toGNSData) X) =
      Quotient.mk (cauchySetoid (sliceData width).toGNSData) (limitRep hw0 hw1 width X) := rfl

/-- The SAME finite-cutoff norm cap passes to the constructed map on every vector. -/
theorem completedLimit_norm_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (x : GNSCompletionSpace (sliceData width).toGNSData) :
    CReal.RCle ((sliceData width).toGNSData.cinnerCompl
      (completedLimit hw0 hw1 width x) (completedLimit hw0 hw1 width x))
      (CReal.RCscale (stepCap w width * stepCap w width)
        ((sliceData width).toGNSData.cinnerCompl x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  let D := (sliceData width).toGNSData
  change CReal.leEv (D.cinnerRep (limitRep hw0 hw1 width X) (limitRep hw0 hw1 width X))
    (CReal.mul (CReal.ofQ' (stepCap w width * stepCap w width)) (D.cinnerRep X X))
  exact CReal.leEv_of_convergesTo_le
    (pairing_converges (cutoffFamily hw0 hw1 width X) (cutoffFamily hw0 hw1 width X))
    (CReal.convergesTo_const _)
    (fun p => (denseTransfer hw0 hw1 (lateCutoff w p) width (Nat.le_max_left _ _)).completionMap_norm_bound
      (Quotient.mk (cauchySetoid D) X))

/-- The same Lipschitz constant controls arbitrary pairs of completed inputs. -/
theorem completedLimit_distance_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (x y : GNSCompletionSpace (sliceData width).toGNSData) :
    CReal.RCle ((sliceData width).toGNSData.cinnerCompl
      ((sliceData width).toGNSData.cSub (completedLimit hw0 hw1 width x) (completedLimit hw0 hw1 width y))
      ((sliceData width).toGNSData.cSub (completedLimit hw0 hw1 width x) (completedLimit hw0 hw1 width y)))
      (CReal.RCscale (stepCap w width * stepCap w width)
        ((sliceData width).toGNSData.cinnerCompl ((sliceData width).toGNSData.cSub x y)
          ((sliceData width).toGNSData.cSub x y))) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  let D := (sliceData width).toGNSData
  change CReal.leEv (D.cinnerRep
    (D.subCauchy (limitRep hw0 hw1 width X) (limitRep hw0 hw1 width Y))
    (D.subCauchy (limitRep hw0 hw1 width X) (limitRep hw0 hw1 width Y)))
    (CReal.mul (CReal.ofQ' (stepCap w width * stepCap w width))
      (D.cinnerRep (D.subCauchy X Y) (D.subCauchy X Y)))
  exact CReal.leEv_of_convergesTo_le
    (difference_converges (cutoffFamily hw0 hw1 width X) (cutoffFamily hw0 hw1 width Y))
    (CReal.convergesTo_const _)
    (fun p => (denseTransfer hw0 hw1 (lateCutoff w p) width (Nat.le_max_left _ _)).completionMap_distance_bound
      (Quotient.mk (cauchySetoid D) X) (Quotient.mk (cauchySetoid D) Y))

private theorem converges_sub {a b : Nat → CReal} {A B : CReal}
    (ha : CReal.ConvergesTo a A) (hb : CReal.ConvergesTo b B) :
    CReal.ConvergesTo (fun n => CReal.sub (a n) (b n)) (CReal.sub A B) :=
  CReal.convergesTo_add ha (CReal.convergesTo_neg hb)

private theorem fixed_difference_converges {D : GNSData}
    (X : GeneralCompletionCauchy D) (Y : CauchyGNS D) :
    CReal.ConvergesTo (fun p => D.cinnerRep (D.subCauchy (X.pt p) Y) (D.subCauchy (X.pt p) Y))
      (D.cinnerRep (D.subCauchy X.lim Y) (D.subCauchy X.lim Y)) := by
  have h := converges_sub
    (converges_sub (pairing_converges X X) (D.cinnerRep_continuous_right X Y))
    (converges_sub (D.cinnerRep_continuous_left X Y) (CReal.convergesTo_const (D.cinnerRep Y Y)))
  exact TrigAddCReal.convergesTo_congr_seq
    (fun p => (difference_pairing (X.pt p) Y (X.pt p) Y).symm)
    (CReal.convergesTo_limit_congr h (difference_pairing X.lim Y X.lim Y).symm)

/-- The original norm-relative cutoff rate controls distance to the ACTUAL limit,
uniformly in the input vector at fixed nome and width. -/
theorem completedLimit_cutoff_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat)
    (hK : transferCutoff w width epsilon ≤ K)
    (x : GNSCompletionSpace (sliceData width).toGNSData) :
    CReal.RCle ((sliceData width).toGNSData.cinnerCompl
      ((sliceData width).toGNSData.cSub (completedLimit hw0 hw1 width x)
        (completedTransfer hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK) x))
      ((sliceData width).toGNSData.cSub (completedLimit hw0 hw1 width x)
        (completedTransfer hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK) x)))
      (CReal.RCscale (epsilon*epsilon) ((sliceData width).toGNSData.cinnerCompl x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  let D := (sliceData width).toGNSData
  let N := transferCutoff w width epsilon
  let Y := (denseTransfer hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK)).mapCauchy X
  have hconv := fixed_difference_converges (cutoffFamily hw0 hw1 width X) Y
  have hshift : CReal.ConvergesTo (fun p => D.cinnerRep
      (D.subCauchy ((cutoffFamily hw0 hw1 width X).pt (max p N)) Y)
      (D.subCauchy ((cutoffFamily hw0 hw1 width X).pt (max p N)) Y))
      (D.cinnerRep (D.subCauchy (limitRep hw0 hw1 width X) Y)
        (D.subCauchy (limitRep hw0 hw1 width X) Y)) := by
    intro delta hd
    obtain ⟨P, hP⟩ := hconv delta hd
    exact ⟨P, fun p hp => hP (max p N) (Nat.le_trans hp (Nat.le_max_left _ _))⟩
  change CReal.leEv (D.cinnerRep
    (D.subCauchy (limitRep hw0 hw1 width X) Y) (D.subCauchy (limitRep hw0 hw1 width X) Y))
    (CReal.mul (CReal.ofQ' (epsilon*epsilon)) (D.cinnerRep X X))
  exact CReal.leEv_of_convergesTo_le hshift (CReal.convergesTo_const _)
    (fun p => completedTransfer_difference_bound hw0 hw1 width epsilon he K (lateCutoff w (max p N))
      hK (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (Quotient.mk (cauchySetoid D) X))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimit.limitRep_null
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimit.completedLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimit.completedLimit_mk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimit.completedLimit_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimit.completedLimit_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimit.completedLimit_cutoff_bound
