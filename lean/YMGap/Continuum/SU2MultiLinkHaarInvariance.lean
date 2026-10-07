/-
# Left/right shear invariance of `multiLinkHaar` (head link, all degrees)

For `n = blocks + 1` links with `blocks ≥ 1`, substituting the head link
`u ↦ a·u` (left) or `u ↦ u·a` (right), with `a` the second quaternion block,
leaves `multiLinkHaar n` unchanged on every polynomial.  Direct reuse of
`SU2QuaternionAllDegreeHaarTranslation.translatedHeadPolynomial_haar`.

OPEN: invariance for translating an arbitrary link `k` (not the head) by an
arbitrary other block needs a block-permutation invariance lemma for
`quaternionHaar` (relabelling blocks), not yet in the tree.
-/

import YMGap.Continuum.SU2TorusMultiLinkPolyGibbs
import YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation

namespace YMGap.Continuum.SU2MultiLinkHaarInvariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs

theorem multiLinkHaar_left_shear_invariant (blocks : Nat) (hb : 0 < blocks) (p : RatPoly) :
    ((multiLinkHaar (blocks + 1)).h
        (translatedHeadPolynomial leftTranslatedHeadQuaternion p)).eqv
      ((multiLinkHaar (blocks + 1)).h p) :=
  YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.translatedHeadPolynomial_haar
    false blocks hb p

theorem multiLinkHaar_right_shear_invariant (blocks : Nat) (hb : 0 < blocks) (p : RatPoly) :
    ((multiLinkHaar (blocks + 1)).h
        (translatedHeadPolynomial rightTranslatedHeadQuaternion p)).eqv
      ((multiLinkHaar (blocks + 1)).h p) :=
  YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.translatedHeadPolynomial_haar
    true blocks hb p

end YMGap.Continuum.SU2MultiLinkHaarInvariance

#print axioms YMGap.Continuum.SU2MultiLinkHaarInvariance.multiLinkHaar_left_shear_invariant
#print axioms YMGap.Continuum.SU2MultiLinkHaarInvariance.multiLinkHaar_right_shear_invariant
