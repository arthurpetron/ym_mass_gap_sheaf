/-
# Torus RP bridge, item 1: the crossing-link split at an arbitrary block

This generalises `SU2TorusRPHaar.split_cut1/2` from the first block to any selected block (the crossing link L) with
any distinct multiplier block (the split variable A). The existing selected shears
(`selectedLeft/RightTranslatedPolynomial_haar`, which expose the pair by a block involution, apply the head shear,
then restore) are composed with the conj flip of the multiplier:
* `split_sel_cut1`: `∫ f(A*·L, A*) = ∫ f(L, A)`;
* `split_sel_cut2`: `∫ f(L·A*, A*) = ∫ f(L, A)`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (bridge item 4 is not landed). Valid for every coupling.
-/

import YMGap.Continuum.SU2TorusRPHaar

namespace YMGap.Continuum.SU2TorusRPSplitSel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
  (selectedLeftTranslatedPolynomial selectedRightTranslatedPolynomial)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (signSelectedPolynomial)
open YMGap.Continuum.SU2TorusRPHaar (conjSel conj_haar)

theorem split_sel_cut1 (tailBlocks selected multiplier : Nat) (hblocks : 0 < tailBlocks)
    (hs : selected < tailBlocks + 1) (hm : multiplier < tailBlocks + 1) (hd : selected ≠ multiplier)
    (p : RatPoly)
    (hsupport : YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks
      (tailBlocks + 1) p) :
    (quaternionHaar (tailBlocks + 1) (signSelectedPolynomial (4 * (tailBlocks + 1))
        (conjSel fun k => k == multiplier)
        (selectedLeftTranslatedPolynomial tailBlocks selected multiplier hblocks hs hm hd p))).eqv
      (quaternionHaar (tailBlocks + 1) p) :=
  Q'.eqv_trans _ _ _ (conj_haar _ _ _)
    (YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.selectedLeftTranslatedPolynomial_haar
      tailBlocks selected multiplier hblocks hs hm hd p hsupport)

theorem split_sel_cut2 (tailBlocks selected multiplier : Nat) (hblocks : 0 < tailBlocks)
    (hs : selected < tailBlocks + 1) (hm : multiplier < tailBlocks + 1) (hd : selected ≠ multiplier)
    (p : RatPoly)
    (hsupport : YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks
      (tailBlocks + 1) p) :
    (quaternionHaar (tailBlocks + 1) (signSelectedPolynomial (4 * (tailBlocks + 1))
        (conjSel fun k => k == multiplier)
        (selectedRightTranslatedPolynomial tailBlocks selected multiplier hblocks hs hm hd p))).eqv
      (quaternionHaar (tailBlocks + 1) p) :=
  Q'.eqv_trans _ _ _ (conj_haar _ _ _)
    (YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.selectedRightTranslatedPolynomial_haar
      tailBlocks selected multiplier hblocks hs hm hd p hsupport)

end YMGap.Continuum.SU2TorusRPSplitSel

#print axioms YMGap.Continuum.SU2TorusRPSplitSel.split_sel_cut1
#print axioms YMGap.Continuum.SU2TorusRPSplitSel.split_sel_cut2
