/-
# Quantitative pairing data for the same limiting Wilson-window form

Sharp Cauchy--Schwarz of the actual limiting reflected form turns the
explicit squared-distance tolerance epsilon^2/(8*(B+1)) into two-sided
pairing error epsilon. Only the two unchanged diagonals require ceilings.
The actual sum bound and literal difference cancellation give the anchor
estimate needed to compute ceilings for supplied Cauchy representatives.

Every field of the existing PairingData interface is discharged for the
same window seminorm, including the actual scalar approximation modulus.
There is no new analytical premise or alternative completed carrier. The
intrinsic carrier can consume these estimates in a common finite horizon;
no enlarged transfer bound, spacing limit or continuum theory is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm
import YMGap.Continuum.CRealSeminormPairingCompletionBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowPairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (smallTolerance smallTolerance_pos smallTolerance_budget signed_small_of_square
    pairingTolerance)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem mul_mono_right {F a b : CReal}
    (hF : leEv czero F) (hab : leEv a b) :
    leEv (mul a F) (mul b F) :=
  leEv_trans (leEv_of_equiv (CRealAlg.cmul_comm a F))
    (leEv_trans (leEv_mul_nonneg_left hF hab)
      (leEv_of_equiv (CRealAlg.cmul_comm F b)))

private theorem sub_add_sub (a b c : CReal) :
    Equiv (add (sub a b) (sub b c)) (sub a c) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
    (.add (.var 0) (.neg (.var 2))) (by decide)
    (fun | 0 => a.approx n | 1 => b.approx n | _ => c.approx n)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base) (H : Nat)

local notation "P" => pairing hw0 hw1 hsmall hd hs hb H
local notation "d" => distSq hw0 hw1 hsmall hd hs hb H

/-- The already proved sharp CS supplies the displayed scalar tolerance. -/
theorem pairing_small (x y : Carrier base H) (B : Q') (hB : (0 : Q') ≤ B)
    (r : Q') (hr : (0 : Q') < r)
    (hx : leEv (P x x) (ofQ' (smallTolerance B hB r)))
    (hy : leEv (P y y) (ofQ' B)) :
    leRat (P x y) r ∧ leRat (neg (P x y)) r := by
  apply signed_small_of_square _ r hr
  have hcs := spatialLimit_cauchySchwarz hw0 hw1 hsmall hd hs hb H
    x.val y.val x.property y.property
  have hdelta : leEv czero (ofQ' (smallTolerance B hB r)) :=
    leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt (smallTolerance_pos B hB hr))
  have hprod := leEv_trans
    (mul_mono_right (form_nonnegative hw0 hw1 hsmall hd hs hb H y.val y.property) hx)
    (leEv_mul_nonneg_left hdelta hy)
  exact leEv_trans hcs (leEv_trans hprod
    (leEv_le_ofQ'_of_approx_le (fun _ => smallTolerance_budget B hB hr)))

/-- Both differences are actual signed expressions in the same window. -/
theorem pairing_difference_split (x x' y y' : Carrier base H) :
    Equiv (sub (P x y) (P x' y'))
      (add (P (difference x x') y) (P (difference y y') x')) := by
  have hleft := pairing_difference_left hw0 hw1 hsmall hd hs hb H x x' y
  have hright := (form_symm hw0 hw1 hsmall hd hs hb H
    (difference y y').val x'.val (difference y y').property x'.property).trans
      (form_difference_right hw0 hw1 hsmall hd hs hb H x'.val y.val y'.val
        x'.property y.property y'.property)
  exact ((Equiv_add hleft hright).trans (sub_add_sub _ _ _)).symm

/-- Only y and x' need norm ceilings, computed downstream from their anchors. -/
theorem pairing_close (x x' y y' : Carrier base H) (B : Q') (hB : (0 : Q') ≤ B)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hx : leEv (d x x') (ofQ' (pairingTolerance B hB epsilon)))
    (hy : leEv (d y y') (ofQ' (pairingTolerance B hB epsilon)))
    (hynorm : leEv (P y y) (ofQ' B)) (hxnorm : leEv (P x' x') (ofQ' B)) :
    leRat (sub (P x y) (P x' y')) epsilon ∧
      leRat (sub (P x' y') (P x y)) epsilon := by
  have hr := ExpNeg.half_mul_pos epsilon hepsilon
  have h1 := pairing_small hw0 hw1 hsmall hd hs hb H (difference x x') y B hB _ hr hx hynorm
  have h2 := pairing_small hw0 hw1 hsmall hd hs hb H (difference y y') x' B hB _ hr hy hxnorm
  have hsplit := pairing_difference_split hw0 hw1 hsmall hd hs hb H x x' y y'
  have hreverse : Equiv (sub (P x' y') (P x y))
      (add (neg (P (difference x x') y)) (neg (P (difference y y') x'))) :=
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_symm (Q'.neg_sub_eqv _ _))).trans
      ((CReal.neg_congr hsplit).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.neg_add_eqv _ _)))
  exact ⟨CReal.leRat_of_equiv hsplit
      (leRat_mono (leRat_add h1.1 h2.1) (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    CReal.leRat_of_equiv hreverse
      (leRat_mono (leRat_add h1.2 h2.2) (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

private theorem difference_add_anchor (x anchor u : Carrier base H) :
    Equiv (P (sum (difference x anchor) anchor) u) (P x u) :=
  (form_add_left hw0 hw1 hsmall hd hs hb H
    (difference x anchor).val anchor.val u.val
    (difference x anchor).property anchor.property u.property).trans
      ((Equiv_add (pairing_difference_left hw0 hw1 hsmall hd hs hb H x anchor u)
        (Equiv.refl (P anchor u))).trans
          (SumOfSquares.Equiv_of_approx_eqv (fun n =>
            Q'.sub_add_cancel_eqv ((P x u).approx n) ((P anchor u).approx n))))

/-- The actual norm ceiling follows from the same form, not a presentation cap. -/
theorem diagonal_anchor_bound (x anchor : Carrier base H) :
    leEv (P x x) (add (add (d x anchor) (d x anchor)) (add (P anchor anchor) (P anchor anchor))) := by
  let s := sum (difference x anchor) anchor
  have hpin : Equiv (P s s) (P x x) :=
    (difference_add_anchor hw0 hw1 hsmall hd hs hb H x anchor s).trans
      ((form_symm hw0 hw1 hsmall hd hs hb H x.val s.val x.property s.property).trans
        (difference_add_anchor hw0 hw1 hsmall hd hs hb H x anchor x))
  exact leEv_trans (leEv_of_equiv hpin.symm)
    (pairing_sum_bound hw0 hw1 hsmall hd hs hb H (difference x anchor) anchor)

/-- An actual instance; the dense scalar modulus is retained as Type data. -/
def pairingData :
    CRealSeminormPairingCompletion.PairingData (seminorm hw0 hw1 hsmall hd hs hb H) where
  pairing := P
  pairingCauchy := pairingCauchy hw0 hw1 hsmall hd hs hb H
  diagonal_anchor_bound := diagonal_anchor_bound hw0 hw1 hsmall hd hs hb H
  pairing_close := pairing_close hw0 hw1 hsmall hd hs hb H

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowPairingContinuity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowPairingContinuity.pairing_small
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowPairingContinuity.pairing_difference_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowPairingContinuity.pairing_close
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowPairingContinuity.diagonal_anchor_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowPairingContinuity.pairingData
