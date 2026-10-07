/-
# Torus RP, step 3: the crossing-link split Haar lemmas (polynomial form, all degrees)

Formulation (see `docs/J04-TORUS-RP-SCOPE-2026-10-07.md`): there is no gauge fixing. Each crossing temporal link L
is split by Haar invariance into a Λ₊ variable and its reflected copy:
* cut 1: `∫ f(L) = ∫∫ f(A*·L) dA dL` (`split_cut1`). This is the left head shear followed by the conj flip of the
  multiplier block.
* cut 2: `∫ f(L) = ∫∫ f(L·A*) dA dL` (`split_cut2`), the right head shear followed by the same conj flip.
* `conj_haar`: `U ↦ U*` on any selected set of blocks preserves `quaternionHaar`. It is the sign flip of
  components 1..3, and is used to store reflected temporal links as `conj(shift U)`.

The head block is the crossing link and block 1 is the multiplier. Reaching an arbitrary block uses
`quaternionHaar_reindex`; that composition is still OPEN.

`signSelectedPolynomial` is literally the coordinate substitution `x_i ↦ -x_i` (coefficient sign = parity of the
flipped exponents). Applied after the head substitution, it gives the polynomial of `f(A*·L)`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.** These are the Haar ingredients of the bridge only. Valid for every coupling.
-/

import YMGap.Continuum.SU2MultiLinkHaarInvariance
import YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection

namespace YMGap.Continuum.SU2TorusRPHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (signSelectedPolynomial quaternionHaar_signSelected)

/-- Coordinates flipped by `U ↦ U*` on the blocks selected by `S`: components 1, 2, 3 of each selected block. -/
def conjSel (S : Nat → Bool) (i : Nat) : Bool := S (i / 4) && (i % 4 != 0)

/-- `U ↦ U*` on the selected blocks preserves the product Haar functional. -/
theorem conj_haar (blocks : Nat) (S : Nat → Bool) (p : RatPoly) :
    (quaternionHaar blocks (signSelectedPolynomial (4 * blocks) (conjSel S) p)).eqv (quaternionHaar blocks p) :=
  quaternionHaar_signSelected blocks (conjSel S) p

/-- Conjugate the multiplier block 1. -/
def mult1 : Nat → Bool := fun k => k == 1

/-- **Cut-1 split:** `∫ f(A*·L, A*) = ∫ f(L, A)` with L the head block and A block 1. -/
theorem split_cut1 (blocks : Nat) (hb : 0 < blocks) (p : RatPoly) :
    (quaternionHaar (blocks + 1) (signSelectedPolynomial (4 * (blocks + 1)) (conjSel mult1)
        (translatedHeadPolynomial leftTranslatedHeadQuaternion p))).eqv
      (quaternionHaar (blocks + 1) p) :=
  Q'.eqv_trans _ _ _ (conj_haar (blocks + 1) mult1 _)
    (YMGap.Continuum.SU2MultiLinkHaarInvariance.multiLinkHaar_left_shear_invariant blocks hb p)

/-- **Cut-2 split:** `∫ f(L·A*, A*) = ∫ f(L, A)`. -/
theorem split_cut2 (blocks : Nat) (hb : 0 < blocks) (p : RatPoly) :
    (quaternionHaar (blocks + 1) (signSelectedPolynomial (4 * (blocks + 1)) (conjSel mult1)
        (translatedHeadPolynomial rightTranslatedHeadQuaternion p))).eqv
      (quaternionHaar (blocks + 1) p) :=
  Q'.eqv_trans _ _ _ (conj_haar (blocks + 1) mult1 _)
    (YMGap.Continuum.SU2MultiLinkHaarInvariance.multiLinkHaar_right_shear_invariant blocks hb p)

end YMGap.Continuum.SU2TorusRPHaar

#print axioms YMGap.Continuum.SU2TorusRPHaar.conj_haar
#print axioms YMGap.Continuum.SU2TorusRPHaar.split_cut1
#print axioms YMGap.Continuum.SU2TorusRPHaar.split_cut2
