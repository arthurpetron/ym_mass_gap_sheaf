/-
# The same two-link form comparison on the actual completions

Both directions preserve the literal polynomial sequence and change only
its explicit Cauchy modulus. The inverse maps and both original constants
are proved, not supplied as hypotheses. This is an equivalence of ordinary
weighted GNS carriers, not an isometry, an OS construction, or a gap.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeCollarComparison
import YMGap.Continuum.BF4ExactSlabStarConditionalProjection
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.BF4ExactSlabTwoLinkCompletionComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabSmallNomePairCalibration
open YMGap.Continuum.BF4ExactSlabSmallNomeCollarComparison
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (K extent : Nat) (hK : headCutoff w ≤ K) (left right : Z4Link)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "B0" => twoLinkBackgroundData (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
  hsmall (Q'.le_of_lt hd) K extent left right
local notation "L" => twoLinkLower w
local notation "U" => twoLinkUpper w

/-- The literal difference has the same polynomial carrier in both forms. -/
theorem distance_bounds (p q : (F).V) :
    L * (B0).distSqQ p q ≤ (F).distSqQ p q ∧
      (F).distSqQ p q ≤ U * (B0).distSqQ p q :=
  two_link_fullData_bounds (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall
    (Q'.le_of_lt hd) hw0 hw1 K extent hK left right ((F).sub p q)

private theorem background_close (p q : (F).V) (epsilon : Q')
    (h : (F).distSqQ p q ≤ L * epsilon) : (B0).distSqQ p q ≤ epsilon :=
  Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (distance_bounds hw0 hw1 hsmall hd K extent hK left right p q).1 h)
    (twoLinkLower_positive hd)

private def fullTolerance (w epsilon : Q') : Q' :=
  epsilon * ExpUBInstance.oneOver1p (twoLinkUpper w)

private theorem fullTolerance_positive {w epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < fullTolerance w epsilon := Q'.mul_pos he (oneOver1p_pos _)

private theorem full_close (p q : (F).V) (epsilon : Q') (he : (0 : Q') < epsilon)
    (h : (B0).distSqQ p q ≤ fullTolerance w epsilon) : (F).distSqQ p q ≤ epsilon :=
  Q'.le_trans' _ _ _ (distance_bounds hw0 hw1 hsmall hd K extent hK left right p q).2
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h
      (Q'.le_of_lt (twoLinkUpper_positive (Q'.le_of_lt hw0))))
      (key_bound _ _ (Q'.le_of_lt (twoLinkUpper_positive (Q'.le_of_lt hw0))) (Q'.le_of_lt he)))

/-- Explicit original-to-background sequence map; only its modulus changes. -/
def toBackgroundCauchy (X : CauchyGNS F) : CauchyGNS B0 where
  seq := X.seq
  modulus epsilon := X.modulus (L * epsilon)
  isCauchy := fun epsilon he p q hp hq =>
    background_close hw0 hw1 hsmall hd K extent hK left right _ _ epsilon
      (X.isCauchy _ (Q'.mul_pos (twoLinkLower_positive hd) he) p q hp hq)

/-- Explicit background-to-original sequence map, on the same polynomials. -/
def toFullCauchy (X : CauchyGNS B0) : CauchyGNS F where
  seq := X.seq
  modulus epsilon := X.modulus (fullTolerance w epsilon)
  isCauchy := fun epsilon he p q hp hq =>
    full_close hw0 hw1 hsmall hd K extent hK left right _ _ epsilon he
      (X.isCauchy _ (fullTolerance_positive he) p q hp hq)

/-- Null witnesses keep their computational moduli in the same direction. -/
def toBackgroundNullModulus {X Y : CauchyGNS F} (h : CauchyNullModulus F X Y) :
    CauchyNullModulus B0 (toBackgroundCauchy hw0 hw1 hsmall hd K extent hK left right X)
      (toBackgroundCauchy hw0 hw1 hsmall hd K extent hK left right Y) where
  modulus epsilon := h.modulus (L * epsilon)
  close := fun epsilon he n hn =>
    background_close hw0 hw1 hsmall hd K extent hK left right _ _ epsilon
      (h.close _ (Q'.mul_pos (twoLinkLower_positive hd) he) n hn)

def toFullNullModulus {X Y : CauchyGNS B0} (h : CauchyNullModulus B0 X Y) :
    CauchyNullModulus F (toFullCauchy hw0 hw1 hsmall hd K extent hK left right X)
      (toFullCauchy hw0 hw1 hsmall hd K extent hK left right Y) where
  modulus epsilon := h.modulus (fullTolerance w epsilon)
  close := fun epsilon he n hn =>
    full_close hw0 hw1 hsmall hd K extent hK left right _ _ epsilon he
      (h.close _ (fullTolerance_positive he) n hn)

private theorem toBackground_null {X Y : CauchyGNS F} (h : CauchyNull F X Y) :
    CauchyNull B0 (toBackgroundCauchy hw0 hw1 hsmall hd K extent hK left right X)
      (toBackgroundCauchy hw0 hw1 hsmall hd K extent hK left right Y) := by
  intro epsilon he
  obtain ⟨n, hn⟩ := h (L * epsilon) (Q'.mul_pos (twoLinkLower_positive hd) he)
  exact ⟨n, fun k hk => background_close hw0 hw1 hsmall hd K extent hK left right _ _ epsilon (hn k hk)⟩

private theorem toFull_null {X Y : CauchyGNS B0} (h : CauchyNull B0 X Y) :
    CauchyNull F (toFullCauchy hw0 hw1 hsmall hd K extent hK left right X)
      (toFullCauchy hw0 hw1 hsmall hd K extent hK left right Y) := by
  intro epsilon he
  obtain ⟨n, hn⟩ := h (fullTolerance w epsilon) (fullTolerance_positive he)
  exact ⟨n, fun k hk => full_close hw0 hw1 hsmall hd K extent hK left right _ _ epsilon he (hn k hk)⟩

/-- Canonical comparison map on the already constructed original completion. -/
def toBackground : GNSCompletionSpace F → GNSCompletionSpace B0 :=
  Quotient.lift (fun X => Quotient.mk (cauchySetoid B0)
    (toBackgroundCauchy hw0 hw1 hsmall hd K extent hK left right X))
    (fun _ _ h => Quotient.sound (toBackground_null hw0 hw1 hsmall hd K extent hK left right h))

def toFull : GNSCompletionSpace B0 → GNSCompletionSpace F :=
  Quotient.lift (fun X => Quotient.mk (cauchySetoid F)
    (toFullCauchy hw0 hw1 hsmall hd K extent hK left right X))
    (fun _ _ h => Quotient.sound (toFull_null hw0 hw1 hsmall hd K extent hK left right h))

local notation "J" => toBackground hw0 hw1 hsmall hd K extent hK left right
local notation "I" => toFull hw0 hw1 hsmall hd K extent hK left right

theorem toBackground_embed (p : (F).V) : J (embedV F p) = embedV B0 p := by
  apply Quotient.sound
  exact cauchyNull_refl B0 (constCauchy B0 p)

theorem toFull_embed (p : (B0).V) : I (embedV B0 p) = embedV F p := by
  apply Quotient.sound
  exact cauchyNull_refl F (constCauchy F p)

/-- No quotient representative is selected: the composite keeps each sequence. -/
theorem toFull_toBackground (x : GNSCompletionSpace F) : I (J x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (cauchyNull_refl F X)

theorem toBackground_toFull (x : GNSCompletionSpace B0) : J (I x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (cauchyNull_refl B0 X)

/-- BOTH near-one constants hold for EVERY vector of the original completion. -/
theorem completed_form_bounds (x : GNSCompletionSpace F) :
    CReal.RCle (CReal.RCscale L ((B0).cinnerCompl (J x) (J x))) ((F).cinnerCompl x x) ∧
      CReal.RCle ((F).cinnerCompl x x) (CReal.RCscale U ((B0).cinnerCompl (J x) (J x))) := by
  refine Quotient.inductionOn x ?_
  intro X
  let Y := toBackgroundCauchy hw0 hw1 hsmall hd K extent hK left right X
  change CReal.leEv (CReal.mul (CReal.ofQ' L) ((B0).cinnerRep Y Y)) ((F).cinnerRep X X) ∧
    CReal.leEv ((F).cinnerRep X X) (CReal.mul (CReal.ofQ' U) ((B0).cinnerRep Y Y))
  have hf := CReal.convergesTo_ofQ'CauchySeq _ ((F).cInnerQCauchy X X)
  have hb := CReal.convergesTo_ofQ'CauchySeq _ ((B0).cInnerQCauchy Y Y)
  have h n := two_link_fullData_bounds (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall
    (Q'.le_of_lt hd) hw0 hw1 K extent hK left right (X.seq n)
  constructor
  · exact CReal.leEv_of_convergesTo_le (CReal.convergesTo_const_mul (CReal.ofQ' L) hb) hf
      (fun n => CReal.leEv_of_le (fun k => Q'.le_trans' _ _ _ (h n).1
        (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos k)))))
  · exact CReal.leEv_of_convergesTo_le hf (CReal.convergesTo_const_mul (CReal.ofQ' U) hb)
      (fun n => CReal.leEv_of_le (fun k => Q'.le_trans' _ _ _ (h n).2
        (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos k)))))

/-- Residual differences are transported literally, not just their norms. -/
theorem toBackground_sub (x y : GNSCompletionSpace F) :
    J ((F).cSub x y) = (B0).cSub (J x) (J y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (cauchyNull_refl B0
    ((B0).subCauchy (toBackgroundCauchy hw0 hw1 hsmall hd K extent hK left right X)
      (toBackgroundCauchy hw0 hw1 hsmall hd K extent hK left right Y)))

theorem toFull_sub (x y : GNSCompletionSpace B0) :
    I ((B0).cSub x y) = (F).cSub (I x) (I y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (cauchyNull_refl F
    ((F).subCauchy (toFullCauchy hw0 hw1 hsmall hd K extent hK left right X)
      (toFullCauchy hw0 hw1 hsmall hd K extent hK left right Y)))

#print axioms distance_bounds
#print axioms toBackgroundCauchy
#print axioms toFullCauchy
#print axioms toBackgroundNullModulus
#print axioms toFullNullModulus
#print axioms toBackground
#print axioms toFull
#print axioms toBackground_embed
#print axioms toFull_embed
#print axioms toFull_toBackground
#print axioms toBackground_toFull
#print axioms completed_form_bounds
#print axioms toBackground_sub
#print axioms toFull_sub

end YMGap.Continuum.BF4ExactSlabTwoLinkCompletionComparison
