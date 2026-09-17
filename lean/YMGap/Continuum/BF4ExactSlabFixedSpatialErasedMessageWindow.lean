/-
# Explicit positive bounds for the actual erased terminal message

Write t=Tg, g=T^n1, M=m(g)>0, d=conditionalMessage, h=headFloor,
U=prefixCap, L=kineticFloor*M and B=kineticCap*M. The existing original
transfer and one-factor message certificates give
  L/U <= d <= B/h < B/h+L/U+1.
These are finite construction bounds for a polynomial reciprocal. Their
width/depth dependence must NOT be used as the desired gap coefficient.
All weights and messages are the original ones. No inverse or final
actual-marginal dual bound is asserted by this window alone.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap majorant_prefix_bound)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks weightedMass

private theorem cap_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < prefixCap w := by
  have h := majorant_prefix_bound hw0 hw1 1
  change (1 : Q') ≤ prefixCap w at h
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) h

private theorem smul_neg (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul c (polyNeg p)) (polyNeg (polySmul c p)) :=
  (cap_mul_left c (polyNeg p)).symm.trans
    ((coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.neg (.var 1)))
      (.neg (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => cap c | _ => p)).trans
      (RatPolyCoeffEqv.neg (cap_mul_left c p)))

private theorem smul_sub (c : Q') (p q : RatPoly) :
    RatPolyCoeffEqv (polySmul c (polyAdd p (polyNeg q)))
      (polyAdd (polySmul c p) (polyNeg (polySmul c q))) :=
  (RatPolyCoeffEqv.smul_add c p (polyNeg q)).trans ((RatPolyCoeffEqv.refl _).add (smul_neg c q))

private theorem reciprocal_left (c : Q') (hc : (0 : Q') < c) : Q'.recipPos c hc * c ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv c hc)

private def unscaleLower {blocks : Nat} (d : RatPoly) (c L : Q') (hc : (0 : Q') < c)
    (P : Certificate blocks (polyAdd (polySmul c d) (polyNeg (cap L)))) :
    Certificate blocks (polyAdd d (polyNeg (cap (Q'.recipPos c hc * L)))) := by
  let s := Q'.recipPos c hc
  have he : RatPolyCoeffEqv (polySmul s (polyAdd (polySmul c d) (polyNeg (cap L))))
      (polyAdd d (polyNeg (cap (s*L)))) :=
    (smul_sub s _ _).trans
      (((RatPolyCoeffEqv.smul_assoc s c d).trans
        ((RatPolyCoeffEqv.smul_coefficient (reciprocal_left c hc) d).trans (RatPolyCoeffEqv.one_smul d))).add
        (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.smul_assoc s L polyOne)))
  exact .ofCoeff he.symm (.smul s (Q'.le_of_lt (Q'.recipPos_pos c hc)) P)

private def unscaleUpper {blocks : Nat} (d : RatPoly) (c B : Q') (hc : (0 : Q') < c)
    (P : Certificate blocks (polyAdd (cap B) (polyNeg (polySmul c d)))) :
    Certificate blocks (polyAdd (cap (Q'.recipPos c hc * B)) (polyNeg d)) := by
  let s := Q'.recipPos c hc
  have he : RatPolyCoeffEqv (polySmul s (polyAdd (cap B) (polyNeg (polySmul c d))))
      (polyAdd (cap (s*B)) (polyNeg d)) :=
    (smul_sub s _ _).trans
      ((RatPolyCoeffEqv.smul_assoc s B polyOne).add
        (RatPolyCoeffEqv.neg ((RatPolyCoeffEqv.smul_assoc s c d).trans
          ((RatPolyCoeffEqv.smul_coefficient (reciprocal_left c hc) d).trans (RatPolyCoeffEqv.one_smul d)))))
  exact .ofCoeff he.symm (.smul s (Q'.le_of_lt (Q'.recipPos_pos c hc)) P)

def lower {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width n : Nat) : Q' :=
  Q'.recipPos (prefixCap w) (cap_positive hw0 hw1) *
    (kineticFloor w width * weightedMass w K width (terminalMessage w K width n))

def upperBase {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width n : Nat) : Q' :=
  Q'.recipPos (headFloor w) (headFloor_positive hw0 hw1) *
    (kineticCap w width * weightedMass w K width (terminalMessage w K width n))

def upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width n : Nat) : Q' :=
  upperBase hw0 hw1 K width n + lower hw0 hw1 K width n + 1

theorem lower_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < lower hw0 hw1 K width n :=
  Q'.mul_pos (Q'.recipPos_pos _ _) (Q'.mul_pos (kineticFloor_positive hw0 hw1 width)
    (terminalMessage_mass_positive hw0 hw1 K width hK n))

private theorem upperBase_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') ≤ upperBase hw0 hw1 K width n :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.recipPos_pos _ _))
    (Q'.mul_nonneg _ _ (kineticCap_nonnegative hw0 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK n)))

theorem lower_le_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    lower hw0 hw1 K width n ≤ upper hw0 hw1 K width n :=
  Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ (upperBase_nonnegative hw0 hw1 K width hK n))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
    (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)

theorem upper_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < upper hw0 hw1 K width n :=
  Q'.pos_of_lt_of_le (lower_positive hw0 hw1 K width hK n) (lower_le_upper hw0 hw1 K width hK n)

/-- Strict lower certificate for the actual erased message; not a supplied
inverse hypothesis. The full previous message enters its explicit constant. -/
def lowerCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n i : Nat) (hi : i ∈ activeBlocks width) :
    Certificate (N width) (polyAdd (conditionalMessage w K width n i)
      (polyNeg (cap (lower hw0 hw1 K width n)))) := by
  let d := conditionalMessage w K width n i
  let t := terminalMessage w K width (n+1)
  let L := kineticFloor w width * weightedMass w K width (terminalMessage w K width n)
  have ht := transferStepLowerCertificate hw0 hw1 K width hK
    (terminalMessage_supported w K width n) (terminalMessage_certificate hw0 hw1 K width hK n)
  rw [terminalMessage_next] at ht
  have hp : Certificate (N width) (polyAdd (polySmul (prefixCap w) d) (polyNeg (cap L))) :=
    .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
      (by decide) (fun | 0 => polySmul (prefixCap w) d | 1 => t | _ => cap L))
      ((conditionalMessage_capCertificate hw0 hw1 K width hK n i hi).add ht)
  exact unscaleLower d (prefixCap w) L (cap_positive hw0 hw1) hp

/-- Matching explicit upper certificate. Its slack separates the positive
construction radius from the actual one-factor gap coefficient. -/
def upperCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n i : Nat) (hi : i ∈ activeBlocks width) :
    Certificate (N width) (polyAdd (cap (upper hw0 hw1 K width n))
      (polyNeg (conditionalMessage w K width n i))) := by
  let d := conditionalMessage w K width n i
  let t := terminalMessage w K width (n+1)
  let B := kineticCap w width * weightedMass w K width (terminalMessage w K width n)
  have ht := transferStepUpperCertificate hw0 hw1 K width hK
    (terminalMessage_supported w K width n) (terminalMessage_certificate hw0 hw1 K width hK n)
  rw [terminalMessage_next] at ht
  have hp : Certificate (N width) (polyAdd (cap B) (polyNeg (polySmul (headFloor w) d))) :=
    .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
      (by decide) (fun | 0 => cap B | 1 => t | _ => polySmul (headFloor w) d))
      (ht.add (conditionalMessage_lowerCertificate hw0 hw1 K width hK n i hi))
  have hb := unscaleUpper d (headFloor w) B (headFloor_positive hw0 hw1) hp
  let ell := lower hw0 hw1 K width n
  have hs := Certificate.constant (N width) (ell+1)
    (Q'.zero_le_add _ _ (Q'.le_of_lt (lower_positive hw0 hw1 K width hK n)) Q'.zero_le_one)
  have he : RatPolyCoeffEqv
      (polyAdd (polyAdd (cap (upperBase hw0 hw1 K width n)) (polyNeg d)) (cap (ell+1)))
      (polyAdd (cap (upper hw0 hw1 K width n)) (polyNeg d)) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.add (.var 0) (.var 2)) (.neg (.var 1))) (by decide)
      (fun | 0 => cap (upperBase hw0 hw1 K width n) | 1 => d | _ => cap (ell+1))).trans
      (((cap_add _ _).trans (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) polyOne)).add (.refl _))
  exact .ofCoeff he.symm (hb.add hs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow.lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow.upper
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow.lower_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow.lower_le_upper
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow.upper_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow.lowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow.upperCertificate
