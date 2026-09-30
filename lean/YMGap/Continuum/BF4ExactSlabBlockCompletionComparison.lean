/-
# Original/block-background completion comparison at every positive nome

The two forms have the identical supported polynomial carrier. Their
identity maps retain the literal Cauchy sequences and transform only
explicit moduli using the proved block-collar lower and upper constants.
This is ordinary weighted GNS geometry, not OS time or a gap estimate.
-/

import YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.BF4ExactSlabBlockCompletionComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
  (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => BF4ExactSlabBlockNormalizerMap.backgroundData hw0 hw1 K extent hK links
local notation "L" => blockLower w links.length
local notation "U" => blockUpper w links.length

include hl

/-- Every supported polynomial, with the literal original action retained. -/
theorem norm_bounds (p : (F).V) :
    L * (G).B p p ≤ (F).B p p ∧ (F).B p p ≤ U * (G).B p p := by
  exact collar_weighted_bounds hw0 hw1 K extent hK links links.length
    (Nat.le_refl _) (Certificate.square p.val p.property)

/-- Both squared-distance comparisons hold on the common dense carrier. -/
theorem distance_bounds (p q : (F).V) :
    L * (G).distSqQ p q ≤ (F).distSqQ p q ∧
      (F).distSqQ p q ≤ U * (G).distSqQ p q := by
  change L * (G).B ((G).sub p q) ((G).sub p q) ≤
      (F).B ((F).sub p q) ((F).sub p q) ∧
    (F).B ((F).sub p q) ((F).sub p q) ≤
      U * (G).B ((G).sub p q) ((G).sub p q)
  exact norm_bounds hw0 hw1 K extent hK links hl ((F).sub p q)

private theorem background_close (p q : (F).V) (epsilon : Q')
    (h : (F).distSqQ p q ≤ L * epsilon) : (G).distSqQ p q ≤ epsilon :=
  Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (distance_bounds hw0 hw1 K extent hK links hl p q).1 h)
    (blockLower_positive hw0 hw1 links.length)

/-- The original-to-background Cauchy map changes only the modulus. -/
def toBackgroundCauchy (X : CauchyGNS F) : CauchyGNS G where
  seq := X.seq
  modulus epsilon := X.modulus (L * epsilon)
  isCauchy := fun epsilon he p q hp hq =>
    background_close hw0 hw1 K extent hK links hl _ _ epsilon
      (X.isCauchy _ (Q'.mul_pos (blockLower_positive hw0 hw1 links.length) he)
        p q hp hq)

/-- Original-to-background transport of supplied null witnesses. -/
def toBackgroundNullModulus {X Y : CauchyGNS F} (h : CauchyNullModulus F X Y) :
    CauchyNullModulus G
      (toBackgroundCauchy hw0 hw1 K extent hK links hl X)
      (toBackgroundCauchy hw0 hw1 K extent hK links hl Y) where
  modulus epsilon := h.modulus (L * epsilon)
  close := fun epsilon he n hn =>
    background_close hw0 hw1 K extent hK links hl _ _ epsilon
      (h.close _ (Q'.mul_pos (blockLower_positive hw0 hw1 links.length) he) n hn)

private theorem toBackground_null {X Y : CauchyGNS F} (h : CauchyNull F X Y) :
    CauchyNull G
      (toBackgroundCauchy hw0 hw1 K extent hK links hl X)
      (toBackgroundCauchy hw0 hw1 K extent hK links hl Y) := by
  intro epsilon he
  obtain ⟨n, hn⟩ := h (L * epsilon)
    (Q'.mul_pos (blockLower_positive hw0 hw1 links.length) he)
  exact ⟨n, fun k hk => background_close hw0 hw1 K extent hK links hl
    _ _ epsilon (hn k hk)⟩

/-- Canonical identity-on-sequences map into the actual detached background. -/
def toBackground : GNSCompletionSpace F → GNSCompletionSpace G :=
  Quotient.lift (fun X => Quotient.mk (cauchySetoid G)
    (toBackgroundCauchy hw0 hw1 K extent hK links hl X))
    (fun _ _ h => Quotient.sound (toBackground_null hw0 hw1 K extent hK links hl h))

/-- The already constructed, explicit upper-bound map back to full action. -/
def toFull : GNSCompletionSpace G → GNSCompletionSpace F :=
  BF4ExactSlabBlockOriginalConditional.toFullCompletion hw0 hw1 K extent hK links hl

local notation "J" => toBackground hw0 hw1 K extent hK links hl
local notation "I" => toFull hw0 hw1 K extent hK links hl

theorem toBackground_embed (p : (F).V) : J (embedV F p) = embedV G p := by
  apply Quotient.sound
  exact cauchyNull_refl G (constCauchy G p)

theorem toFull_embed (p : (G).V) : I (embedV G p) = embedV F p := by
  exact BF4ExactSlabBlockOriginalConditional.toFullCompletion_embed
    hw0 hw1 K extent hK links hl p

/-- Both composites retain every polynomial term of every representative. -/
theorem toFull_toBackground (x : GNSCompletionSpace F) : I (J x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (cauchyNull_refl F X)

theorem toBackground_toFull (x : GNSCompletionSpace G) : J (I x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (cauchyNull_refl G X)

/-- Both block-collar constants pass to every original completed vector. -/
theorem completed_form_bounds (x : GNSCompletionSpace F) :
    CReal.RCle (CReal.RCscale L ((G).cinnerCompl (J x) (J x)))
      ((F).cinnerCompl x x) ∧
    CReal.RCle ((F).cinnerCompl x x)
      (CReal.RCscale U ((G).cinnerCompl (J x) (J x))) := by
  refine Quotient.inductionOn x ?_
  intro X
  let Y := toBackgroundCauchy hw0 hw1 K extent hK links hl X
  change CReal.leEv (CReal.mul (CReal.ofQ' L) ((G).cinnerRep Y Y))
      ((F).cinnerRep X X) ∧
    CReal.leEv ((F).cinnerRep X X)
      (CReal.mul (CReal.ofQ' U) ((G).cinnerRep Y Y))
  have hf := CReal.convergesTo_ofQ'CauchySeq _ ((F).cInnerQCauchy X X)
  have hg := CReal.convergesTo_ofQ'CauchySeq _ ((G).cInnerQCauchy Y Y)
  have h n := norm_bounds hw0 hw1 K extent hK links hl (X.seq n)
  constructor
  · exact CReal.leEv_of_convergesTo_le (CReal.convergesTo_const_mul (CReal.ofQ' L) hg) hf
      (fun n => CReal.leEv_of_le (fun k => Q'.le_trans' _ _ _ (h n).1
        (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos k)))))
  · exact CReal.leEv_of_convergesTo_le hf (CReal.convergesTo_const_mul (CReal.ofQ' U) hg)
      (fun n => CReal.leEv_of_le (fun k => Q'.le_trans' _ _ _ (h n).2
        (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos k)))))

/-- Subtraction is transported literally on the common original carrier. -/
theorem toBackground_sub (x y : GNSCompletionSpace F) :
    J ((F).cSub x y) = (G).cSub (J x) (J y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (cauchyNull_refl G
    ((G).subCauchy (toBackgroundCauchy hw0 hw1 K extent hK links hl X)
      (toBackgroundCauchy hw0 hw1 K extent hK links hl Y)))

theorem toFull_sub (x y : GNSCompletionSpace G) :
    I ((G).cSub x y) = (F).cSub (I x) (I y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (cauchyNull_refl F
    ((F).subCauchy
      (BF4ExactSlabBlockOriginalConditional.toFullCauchy
        hw0 hw1 K extent hK links hl X)
      (BF4ExactSlabBlockOriginalConditional.toFullCauchy
        hw0 hw1 K extent hK links hl Y)))

#print axioms norm_bounds
#print axioms distance_bounds
#print axioms toBackgroundCauchy
#print axioms toBackgroundNullModulus
#print axioms toBackground
#print axioms toFull
#print axioms toBackground_embed
#print axioms toFull_embed
#print axioms toFull_toBackground
#print axioms toBackground_toFull
#print axioms completed_form_bounds
#print axioms toBackground_sub
#print axioms toFull_sub

end YMGap.Continuum.BF4ExactSlabBlockCompletionComparison
