/-
# Torus RP assembly (d3c): Θpoly is conj ∘ shift on the first half

* `sign_invol`: the sign flip is an involution up to `PE`.
* `theta_shift`: for `links = L ++ L.map f` and `X` supported in the first `|L|` blocks,
  `sign(conjSel tSel) (thetaPoly X) ≈PE shiftPoly |L| X`. Undoing the temporal conjugation (a Haar-invariant
  `RingSub`, `conj_haar` / `conj_ringSub`) turns the geometric reflection into the abstract `shiftPoly` of `rp_full`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (still to do: the crossing split, the pos/neg/cross factorisation and `hW`).
-/

import YMGap.Continuum.SU2TorusRPHalfOrder

namespace YMGap.Continuum.SU2TorusRPThetaShift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (signSelectedPolynomial reindexQuaternionPolynomial)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans)
open YMGap.Continuum.SU2TorusRPConj (sg)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (shiftPoly)
open YMGap.Continuum.SU2TorusRPCore (Sup)

theorem sg_sg (b : Bool) (x : Q') : (sg b (sg b x)).eqv x := by
  cases b
  · exact Q'.eqv_refl _
  · exact Q'.neg_neg_eqv x

theorem sign_invol (n N : Nat) (S : Nat → Bool) (X : RatPoly) :
    PE n (signSelectedPolynomial N S (signSelectedPolynomial N S X)) X := fun m =>
  Q'.eqv_trans _ _ _ (SU2TorusRPConjCongr.phi_sign n N S _ m)
    (Q'.eqv_trans _ _ _ (SU2TorusRPConjCongr.sg_congr _ (SU2TorusRPConjCongr.phi_sign n N S X m)) (sg_sg _ _))

/-- For any block involution `σ` agreeing with the half shift, `sign (sign (reindex σ X)) ≈ shiftPoly`. -/
theorem theta_shift {a : Nat} (σ : YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.QuaternionBlockInvolution (a + a))
    (hσ : ∀ k, k < a → σ.map k = k + a) (N : Nat) (S : Nat → Bool) (X : RatPoly) (hX : Sup a X) :
    PE (a + a) (signSelectedPolynomial N S (signSelectedPolynomial N S (reindexQuaternionPolynomial σ X)))
      (shiftPoly a X) :=
  pe_trans _ (sign_invol _ N S _) (SU2TorusRPShiftBridge.reindex_shift σ hσ X hX)

end YMGap.Continuum.SU2TorusRPThetaShift

#print axioms YMGap.Continuum.SU2TorusRPThetaShift.sign_invol
#print axioms YMGap.Continuum.SU2TorusRPThetaShift.theta_shift
