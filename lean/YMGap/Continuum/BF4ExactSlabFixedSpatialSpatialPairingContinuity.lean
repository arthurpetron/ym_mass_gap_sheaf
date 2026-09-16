/-
# Quantitative continuity of the actual spatial reflected pairing

Spatial-limit sharp Cauchy--Schwarz and literal difference identities give
two-sided error epsilon from the computed squared-distance tolerance
epsilon^2/(8*(B+1)). Only the displayed unchanged diagonals require the
ceiling, which the next consumer computes from supplied Cauchy anchors.
All distances and pairings belong to the SAME spatial limiting form.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
import YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws (differenceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (smallTolerance smallTolerance_pos smallTolerance_budget signed_small_of_square
    pairingTolerance)

open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

attribute [local irreducible] spatialPairing

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
    (fun
      | 0 => a.approx n
      | 1 => b.approx n
      | _ => c.approx n)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

/-- Sharp CS of the SAME spatial pairing turns small/bounded diagonals into
a signed pairing bound with the displayed explicit scalar tolerance. -/
theorem pairing_small (e f : PhysicalSpan base) (B : Q') (hB : (0 : Q') ≤ B)
    (r : Q') (hr : (0 : Q') < r)
    (he : leEv (spatialPairing hw0 hw1 base hsmall hd hs hb e e) (ofQ' (smallTolerance B hB r)))
    (hf : leEv (spatialPairing hw0 hw1 base hsmall hd hs hb f f) (ofQ' B)) :
    leRat (spatialPairing hw0 hw1 base hsmall hd hs hb e f) r ∧
    leRat (neg (spatialPairing hw0 hw1 base hsmall hd hs hb e f)) r := by
  apply signed_small_of_square _ r hr
  have hcs := spatialPairing_cauchySchwarz hw0 hw1 base hsmall hd hs hb e f
  have hdelta : leEv czero (ofQ' (smallTolerance B hB r)) :=
    leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt (smallTolerance_pos B hB hr))
  have hprod := leEv_trans
    (mul_mono_right (spatialPairing_nonnegative hw0 hw1 base hsmall hd hs hb f) he)
    (leEv_mul_nonneg_left hdelta hf)
  exact leEv_trans hcs (leEv_trans hprod
    (leEv_le_ofQ'_of_approx_le (fun _ => smallTolerance_budget B hB hr)))

theorem pairing_difference_split (x x' y y' : PhysicalSpan base) :
    Equiv (sub (spatialPairing hw0 hw1 base hsmall hd hs hb x y) (spatialPairing hw0 hw1 base hsmall hd hs hb x' y'))
      (add (spatialPairing hw0 hw1 base hsmall hd hs hb (differenceSpan x x') y)
        (spatialPairing hw0 hw1 base hsmall hd hs hb (differenceSpan y y') x')) := by
  have hleft := spatialPairing_difference_left hw0 hw1 base hsmall hd hs hb x x' y
  have hright := Equiv.trans
    (spatialPairing_symm hw0 hw1 base hsmall hd hs hb (differenceSpan y y') x')
    (spatialPairing_difference_right hw0 hw1 base hsmall hd hs hb x' y y')
  exact Equiv.symm (Equiv.trans (Equiv_add hleft hright) (sub_add_sub _ _ _))

/-- Quantitative continuity on the actual spatial-seminorm carrier. Only y
and x' require norm ceilings; these will be computed from Cauchy anchors. -/
theorem pairing_close (x x' y y' : PhysicalSpan base) (B : Q') (hB : (0 : Q') ≤ B)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hx : leEv (spatialDistSq hw0 hw1 base hsmall hd hs hb x x') (ofQ' (pairingTolerance B hB epsilon)))
    (hy : leEv (spatialDistSq hw0 hw1 base hsmall hd hs hb y y') (ofQ' (pairingTolerance B hB epsilon)))
    (hynorm : leEv (spatialPairing hw0 hw1 base hsmall hd hs hb y y) (ofQ' B))
    (hxnorm : leEv (spatialPairing hw0 hw1 base hsmall hd hs hb x' x') (ofQ' B)) :
    leRat (sub (spatialPairing hw0 hw1 base hsmall hd hs hb x y) (spatialPairing hw0 hw1 base hsmall hd hs hb x' y')) epsilon ∧
    leRat (sub (spatialPairing hw0 hw1 base hsmall hd hs hb x' y') (spatialPairing hw0 hw1 base hsmall hd hs hb x y)) epsilon := by
  let dx := differenceSpan x x'
  let dy := differenceSpan y y'
  have hr := ExpNeg.half_mul_pos epsilon hepsilon
  have h1 := pairing_small hw0 hw1 base hsmall hd hs hb dx y B hB _ hr hx hynorm
  have h2 := pairing_small hw0 hw1 base hsmall hd hs hb dy x' B hB _ hr hy hxnorm
  have hsplit := pairing_difference_split hw0 hw1 base hsmall hd hs hb x x' y y'
  have hreverse : Equiv
      (sub (spatialPairing hw0 hw1 base hsmall hd hs hb x' y') (spatialPairing hw0 hw1 base hsmall hd hs hb x y))
      (add (neg (spatialPairing hw0 hw1 base hsmall hd hs hb (differenceSpan x x') y))
        (neg (spatialPairing hw0 hw1 base hsmall hd hs hb (differenceSpan y y') x'))) :=
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_symm (Q'.neg_sub_eqv _ _))).trans
      ((CReal.neg_congr hsplit).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.neg_add_eqv _ _)))
  exact ⟨CReal.leRat_of_equiv hsplit
      (leRat_mono (leRat_add h1.1 h2.1) (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    CReal.leRat_of_equiv hreverse
      (leRat_mono (leRat_add h1.2 h2.2) (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingContinuity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingContinuity.pairing_small
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingContinuity.pairing_difference_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingContinuity.pairing_close
