/-
# Explicit continuity of the actual intrinsic reflected pairing

The carrier is the original fixed-spatial physical-span subtype, and its
squared distance is the reflected diagonal of the literal signed difference.
Sharp Cauchy--Schwarz and the two-term difference identity give a two-sided
pairing error epsilon from squared-distance tolerance
epsilon^2/(8*(B+1)). Only the two unchanged diagonal forms require the
displayed ceiling B. All physical-face guards are retained in the subtype.

Only generic scalar tolerance estimates are reused from the older plaquette
continuity module. No old model's pairing, norm, or continuity theorem is
used. Nome, width and retained heat stage stay fixed. This is the continuity
input for constructing the SAME pairing on explicit-modulus Cauchy data;
no completed inner product, Hilbert laws or spectral estimate is claimed here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
import YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (smallTolerance smallTolerance_pos smallTolerance_budget signed_small_of_square
    pairingTolerance)

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

/-- Actual reflected CS converts a small diagonal and a bounded diagonal
into a two-sided rational bound on their SAME intrinsic pairing. -/
theorem pairing_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (e f : PhysicalSpan width) (B : Q') (hB : (0 : Q') ≤ B)
    (r : Q') (hr : (0 : Q') < r)
    (he : leEv (pairing hw0 hw1 width e.val e.val stage)
      (ofQ' (smallTolerance B hB r)))
    (hf : leEv (pairing hw0 hw1 width f.val f.val stage) (ofQ' B)) :
    leRat (pairing hw0 hw1 width e.val f.val stage) r ∧
    leRat (CReal.neg (pairing hw0 hw1 width e.val f.val stage)) r := by
  apply signed_small_of_square _ r hr
  have hcs := pairing_cauchySchwarz hw0 hw1 width e.val f.val
    e.property f.property stage
  have hdelta : leEv czero (ofQ' (smallTolerance B hB r)) :=
    leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt (smallTolerance_pos B hB hr))
  have hprod := leEv_trans
    (mul_mono_right
      (pairing_self_nonnegative hw0 hw1 width f.val f.property stage) he)
    (leEv_mul_nonneg_left hdelta hf)
  exact leEv_trans hcs (leEv_trans hprod
    (leEv_le_ofQ'_of_approx_le (fun _ => smallTolerance_budget B hB hr)))

/-- The pairing difference splits into the two actual signed-difference
terms. Symmetry is used only with the physical guards carried by the spans. -/
theorem pairing_difference_split {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x x' y y' : PhysicalSpan width) :
    Equiv
      (CReal.sub (pairing hw0 hw1 width x.val y.val stage)
        (pairing hw0 hw1 width x'.val y'.val stage))
      (CReal.add
        (pairing hw0 hw1 width (difference x.val x'.val) y.val stage)
        (pairing hw0 hw1 width (difference y.val y'.val) x'.val stage)) := by
  have hleft := pairing_difference_left hw0 hw1 width x.val x'.val y.val stage
  have hright := Equiv.trans
    (pairing_symm hw0 hw1 width (difference y.val y'.val) x'.val
      (physical_difference y.property y'.property) x'.property stage)
    (pairing_difference_right hw0 hw1 width x'.val y.val y'.val stage)
  exact Equiv.symm (Equiv.trans (Equiv_add hleft hright) (sub_add_sub _ _ _))

/-- Quantitative continuity on the actual reflected physical-span carrier.
Only y and x' need diagonal ceilings; no bound on every presentation is assumed. -/
theorem pairing_close {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x x' y y' : PhysicalSpan width) (B : Q') (hB : (0 : Q') ≤ B)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hx : leEv (distSq hw0 hw1 width stage x x')
      (ofQ' (pairingTolerance B hB epsilon)))
    (hy : leEv (distSq hw0 hw1 width stage y y')
      (ofQ' (pairingTolerance B hB epsilon)))
    (hynorm : leEv (pairing hw0 hw1 width y.val y.val stage) (ofQ' B))
    (hxnorm : leEv (pairing hw0 hw1 width x'.val x'.val stage) (ofQ' B)) :
    leRat (CReal.sub (pairing hw0 hw1 width x.val y.val stage)
      (pairing hw0 hw1 width x'.val y'.val stage)) epsilon ∧
    leRat (CReal.sub (pairing hw0 hw1 width x'.val y'.val stage)
      (pairing hw0 hw1 width x.val y.val stage)) epsilon := by
  let dx : PhysicalSpan width :=
    ⟨difference x.val x'.val, physical_difference x.property x'.property⟩
  let dy : PhysicalSpan width :=
    ⟨difference y.val y'.val, physical_difference y.property y'.property⟩
  have hr := ExpNeg.half_mul_pos epsilon hepsilon
  have h1 := pairing_small hw0 hw1 width stage dx y B hB _ hr hx hynorm
  have h2 := pairing_small hw0 hw1 width stage dy x' B hB _ hr hy hxnorm
  have hsplit := pairing_difference_split hw0 hw1 width stage x x' y y'
  have hreverse : Equiv
      (CReal.sub (pairing hw0 hw1 width x'.val y'.val stage)
        (pairing hw0 hw1 width x.val y.val stage))
      (CReal.add
        (CReal.neg (pairing hw0 hw1 width (difference x.val x'.val) y.val stage))
        (CReal.neg (pairing hw0 hw1 width (difference y.val y'.val) x'.val stage))) :=
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_symm (Q'.neg_sub_eqv _ _))).trans
      ((CReal.neg_congr hsplit).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.neg_add_eqv _ _)))
  exact ⟨CReal.leRat_of_equiv hsplit
      (leRat_mono (leRat_add h1.1 h2.1) (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    CReal.leRat_of_equiv hreverse
      (leRat_mono (leRat_add h1.2 h2.2) (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialPairingContinuity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingContinuity.pairing_small
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingContinuity.pairing_difference_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingContinuity.pairing_close
