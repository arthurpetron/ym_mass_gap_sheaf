/-
# Quantitative continuity of the actual cutoff-removed reflected pairing

Limiting sharp Cauchy--Schwarz and the literal difference identity give
two-sided pairing error epsilon from the existing computed squared-distance
tolerance epsilon^2/(8*(B+1)). Only the two displayed unchanged diagonals
need the supplied ceiling. The estimates use jointPairing and jointDistSq
throughout; no finite-stage smallness is inferred from limiting smallness.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
import YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (smallTolerance smallTolerance_pos smallTolerance_budget signed_small_of_square
    pairingTolerance)

attribute [local irreducible] jointPairing

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

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

/-- Sharp CS of the SAME joint pairing turns small/bounded diagonals into
a signed pairing bound with the displayed explicit scalar tolerance. -/
theorem pairing_small (e f : PhysicalSpan width) (B : Q') (hB : (0 : Q') ≤ B)
    (r : Q') (hr : (0 : Q') < r)
    (he : leEv (jointPairing hw0 hw1 width e e) (ofQ' (smallTolerance B hB r)))
    (hf : leEv (jointPairing hw0 hw1 width f f) (ofQ' B)) :
    leRat (jointPairing hw0 hw1 width e f) r ∧
    leRat (neg (jointPairing hw0 hw1 width e f)) r := by
  apply signed_small_of_square _ r hr
  have hcs := jointPairing_cauchySchwarz hw0 hw1 width e f
  have hdelta : leEv czero (ofQ' (smallTolerance B hB r)) :=
    leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt (smallTolerance_pos B hB hr))
  have hprod := leEv_trans
    (mul_mono_right (jointPairing_nonnegative hw0 hw1 width f) he)
    (leEv_mul_nonneg_left hdelta hf)
  exact leEv_trans hcs (leEv_trans hprod
    (leEv_le_ofQ'_of_approx_le (fun _ => smallTolerance_budget B hB hr)))

theorem pairing_difference_split (x x' y y' : PhysicalSpan width) :
    Equiv (sub (jointPairing hw0 hw1 width x y) (jointPairing hw0 hw1 width x' y'))
      (add (jointPairing hw0 hw1 width (differenceSpan x x') y)
        (jointPairing hw0 hw1 width (differenceSpan y y') x')) := by
  have hleft := jointPairing_difference_left hw0 hw1 width x x' y
  have hright := Equiv.trans
    (jointPairing_symm hw0 hw1 width (differenceSpan y y') x')
    (jointPairing_difference_right hw0 hw1 width x' y y')
  exact Equiv.symm (Equiv.trans (Equiv_add hleft hright) (sub_add_sub _ _ _))

/-- Quantitative continuity on the actual joint-seminorm carrier. Only y
and x' require norm ceilings; these will be computed from Cauchy anchors. -/
theorem pairing_close (x x' y y' : PhysicalSpan width) (B : Q') (hB : (0 : Q') ≤ B)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hx : leEv (jointDistSq hw0 hw1 width x x') (ofQ' (pairingTolerance B hB epsilon)))
    (hy : leEv (jointDistSq hw0 hw1 width y y') (ofQ' (pairingTolerance B hB epsilon)))
    (hynorm : leEv (jointPairing hw0 hw1 width y y) (ofQ' B))
    (hxnorm : leEv (jointPairing hw0 hw1 width x' x') (ofQ' B)) :
    leRat (sub (jointPairing hw0 hw1 width x y) (jointPairing hw0 hw1 width x' y')) epsilon ∧
    leRat (sub (jointPairing hw0 hw1 width x' y') (jointPairing hw0 hw1 width x y)) epsilon := by
  let dx := differenceSpan x x'
  let dy := differenceSpan y y'
  have hr := ExpNeg.half_mul_pos epsilon hepsilon
  have h1 := pairing_small hw0 hw1 width dx y B hB _ hr hx hynorm
  have h2 := pairing_small hw0 hw1 width dy x' B hB _ hr hy hxnorm
  have hsplit := pairing_difference_split hw0 hw1 width x x' y y'
  have hreverse : Equiv
      (sub (jointPairing hw0 hw1 width x' y') (jointPairing hw0 hw1 width x y))
      (add (neg (jointPairing hw0 hw1 width (differenceSpan x x') y))
        (neg (jointPairing hw0 hw1 width (differenceSpan y y') x'))) :=
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_symm (Q'.neg_sub_eqv _ _))).trans
      ((CReal.neg_congr hsplit).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.neg_add_eqv _ _)))
  exact ⟨CReal.leRat_of_equiv hsplit
      (leRat_mono (leRat_add h1.1 h2.1) (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    CReal.leRat_of_equiv hreverse
      (leRat_mono (leRat_add h1.2 h2.2) (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingContinuity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingContinuity.pairing_small
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingContinuity.pairing_difference_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingContinuity.pairing_close
