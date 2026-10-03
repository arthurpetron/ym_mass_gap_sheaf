/-
# Exact symmetric-Hessian square on the ORIGINAL angular carrier

The six actual quaternion rotations have ordered commutator square 4*Gamma.
The complete ordered second-derivative square minus Gamma is one quarter
of the complete symmetric-second-derivative square. The latter is a
constructed positivity certificate, retaining arbitrary shared spectators.
No Casimir centrality, conditional Poincare bound, surviving-norm estimate,
changing family or continuum conclusion is assumed or asserted here.
-/

import YMGap.Continuum.SU2QuaternionAngularLieBracket
import YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.SU2QuaternionAngularHessianSquares

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.SU2QuaternionAngularLieBracket
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (angularSquare)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

attribute [local irreducible] angularDerivative

/-- Exactly the six ORIGINAL fields, in order 01,02,03,12,13,23. -/
def field (a : Nat) (p : RatPoly) : RatPoly :=
  match a with
  | 0 => angularDerivative 0 1 p
  | 1 => angularDerivative 0 2 p
  | 2 => angularDerivative 0 3 p
  | 3 => angularDerivative 1 2 p
  | 4 => angularDerivative 1 3 p
  | _ => angularDerivative 2 3 p

private def sum6 (f : Nat → RatPoly) : RatPoly :=
  polyAdd (f 0) (polyAdd (f 1) (polyAdd (f 2)
    (polyAdd (f 3) (polyAdd (f 4) (f 5)))))

private theorem sum6_carrier {blocks : Nat} {f g : Nat → RatPoly}
    (h : ∀ a, a < 6 → HaarCarrierEqv blocks (f a) (g a)) :
    HaarCarrierEqv blocks (sum6 f) (sum6 g) :=
  HaarCarrierEqv.add (h 0 (by decide))
    (HaarCarrierEqv.add (h 1 (by decide))
      (HaarCarrierEqv.add (h 2 (by decide))
        (HaarCarrierEqv.add (h 3 (by decide))
          (HaarCarrierEqv.add (h 4 (by decide)) (h 5 (by decide))))))

private def comm (i j k l : Nat) (p : RatPoly) : RatPoly :=
  polyAdd (angularDerivative i j (angularDerivative k l p))
    (polyNeg (angularDerivative k l (angularDerivative i j p)))

private theorem comm_reverse (i j k l : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (comm k l i j p) (polyNeg (comm i j k l p)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 1) (.neg (.var 0)))
    (.neg (.add (.var 0) (.neg (.var 1)))) (by decide)
    (fun | 0 => angularDerivative i j (angularDerivative k l p)
         | _ => angularDerivative k l (angularDerivative i j p))

private theorem comm_flip_left (i j k l : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (comm j i k l p) (polyNeg (comm i j k l p)) := by
  have h1 := angular_plane_antisymmetry i j (angularDerivative k l p)
  have h2 := (angularDerivative_congr k l (angular_plane_antisymmetry i j p)).trans
    (angularDerivative_neg k l (angularDerivative i j p))
  exact (h1.add (RatPolyCoeffEqv.neg h2)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.neg (.var 0)) (.neg (.neg (.var 1))))
      (.neg (.add (.var 0) (.neg (.var 1)))) (by decide)
      (fun | 0 => angularDerivative i j (angularDerivative k l p)
           | _ => angularDerivative k l (angularDerivative i j p)))

private theorem comm_flip_right (i j k l : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (comm i j l k p) (polyNeg (comm i j k l p)) := by
  have h1 := (angularDerivative_congr i j (angular_plane_antisymmetry k l p)).trans
    (angularDerivative_neg i j (angularDerivative k l p))
  have h2 := angular_plane_antisymmetry k l (angularDerivative i j p)
  exact (h1.add (RatPolyCoeffEqv.neg h2)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.neg (.var 0)) (.neg (.neg (.var 1))))
      (.neg (.add (.var 0) (.neg (.var 1)))) (by decide)
      (fun | 0 => angularDerivative i j (angularDerivative k l p)
           | _ => angularDerivative k l (angularDerivative i j p)))

private theorem same_left {blocks i j k : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : RatPoly) :
    HaarCarrierEqv blocks (comm i j i k p) (polyNeg (angularDerivative j k p)) :=
  (RatPolyCoeffEqv.haarCarrier (comm_flip_left j i i k p)).trans
    (HaarCarrierEqv.neg (overlapping_planes_bracket hb hj hi hk
      (Ne.symm hij) hjk hik p))

private theorem same_right {blocks i j k : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : RatPoly) :
    HaarCarrierEqv blocks (comm i k j k p) (polyNeg (angularDerivative i j p)) :=
  (RatPolyCoeffEqv.haarCarrier (comm_flip_right i k k j p)).trans
    (HaarCarrierEqv.neg (overlapping_planes_bracket hb hi hk hj
      hik hij (Ne.symm hjk) p))

private theorem neg_neg_coeff (p : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polyNeg p)) p :=
  coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0)
    (by decide) (fun _ => p)

private theorem same_left_reverse {blocks i j k : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : RatPoly) :
    HaarCarrierEqv blocks (comm i k i j p) (angularDerivative j k p) :=
  (RatPolyCoeffEqv.haarCarrier (comm_reverse i j i k p)).trans
    ((HaarCarrierEqv.neg (same_left hb hi hj hk hij hik hjk p)).trans
      (RatPolyCoeffEqv.haarCarrier (neg_neg_coeff _)))

private theorem same_right_reverse {blocks i j k : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : RatPoly) :
    HaarCarrierEqv blocks (comm j k i k p) (angularDerivative i j p) :=
  (RatPolyCoeffEqv.haarCarrier (comm_reverse i k j k p)).trans
    ((HaarCarrierEqv.neg (same_right hb hi hj hk hij hik hjk p)).trans
      (RatPolyCoeffEqv.haarCarrier (neg_neg_coeff _)))

private theorem adjacent_reverse {blocks i j k : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : RatPoly) :
    HaarCarrierEqv blocks (comm j k i j p) (polyNeg (angularDerivative i k p)) :=
  (RatPolyCoeffEqv.haarCarrier (comm_reverse i j j k p)).trans
    (HaarCarrierEqv.neg (overlapping_planes_bracket hb hi hj hk hij hik hjk p))

private theorem self_comm_at (blocks i j : Nat) (p : RatPoly) :
    HaarCarrierEqv blocks (comm i j i j p) (cap 0) :=
  RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide)
    (fun _ => angularDerivative i j (angularDerivative i j p)))

private theorem disjoint_comm {blocks i j k l : Nat}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (p : RatPoly) :
    HaarCarrierEqv blocks (comm i j k l p) (cap 0) :=
  RatPolyCoeffEqv.haarCarrier
    (((disjoint_planes_commute i j k l hik hil hjk hjl p).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide)
        (fun _ => angularDerivative k l (angularDerivative i j p))))

private def entry (a b : Nat) (p : RatPoly) : RatPoly :=
  match a,b with
  | 0, 1 => polyNeg (field 3 p)
  | 0, 2 => polyNeg (field 4 p)
  | 0, 3 => field 1 p
  | 0, 4 => field 2 p
  | 1, 0 => field 3 p
  | 1, 2 => polyNeg (field 5 p)
  | 1, 3 => polyNeg (field 0 p)
  | 1, 5 => field 2 p
  | 2, 0 => field 4 p
  | 2, 1 => field 5 p
  | 2, 4 => polyNeg (field 0 p)
  | 2, 5 => polyNeg (field 1 p)
  | 3, 0 => polyNeg (field 1 p)
  | 3, 1 => field 0 p
  | 3, 4 => polyNeg (field 5 p)
  | 3, 5 => field 4 p
  | 4, 0 => polyNeg (field 2 p)
  | 4, 2 => field 0 p
  | 4, 3 => field 5 p
  | 4, 5 => polyNeg (field 3 p)
  | 5, 1 => polyNeg (field 2 p)
  | 5, 2 => field 1 p
  | 5, 3 => polyNeg (field 4 p)
  | 5, 4 => field 3 p
  | _, _ => cap 0

private theorem entry_carrier {blocks : Nat} (hb : 0 < blocks)
    (a b : Nat) (ha : a < 6) (hb' : b < 6) (p : RatPoly) :
    HaarCarrierEqv blocks (polyAdd (field a (field b p)) (polyNeg (field b (field a p))))
      (entry a b p) := by
  have hcases (n : Nat) (hn : n < 6) :
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hcases a ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hcases b hb' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact self_comm_at blocks 0 1 p
  · exact same_left (i := 0) (j := 1) (k := 2) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact same_left (i := 0) (j := 1) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact overlapping_planes_bracket (i := 0) (j := 1) (k := 2) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact overlapping_planes_bracket (i := 0) (j := 1) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact disjoint_comm (i := 0) (j := 1) (k := 2) (l := 3) (by decide) (by decide) (by decide) (by decide) p
  · exact same_left_reverse (i := 0) (j := 1) (k := 2) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact self_comm_at blocks 0 2 p
  · exact same_left (i := 0) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact same_right (i := 0) (j := 1) (k := 2) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact disjoint_comm (i := 0) (j := 2) (k := 1) (l := 3) (by decide) (by decide) (by decide) (by decide) p
  · exact overlapping_planes_bracket (i := 0) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact same_left_reverse (i := 0) (j := 1) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact same_left_reverse (i := 0) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact self_comm_at blocks 0 3 p
  · exact disjoint_comm (i := 0) (j := 3) (k := 1) (l := 2) (by decide) (by decide) (by decide) (by decide) p
  · exact same_right (i := 0) (j := 1) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact same_right (i := 0) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact adjacent_reverse (i := 0) (j := 1) (k := 2) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact same_right_reverse (i := 0) (j := 1) (k := 2) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact disjoint_comm (i := 1) (j := 2) (k := 0) (l := 3) (by decide) (by decide) (by decide) (by decide) p
  · exact self_comm_at blocks 1 2 p
  · exact same_left (i := 1) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact overlapping_planes_bracket (i := 1) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact adjacent_reverse (i := 0) (j := 1) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact disjoint_comm (i := 1) (j := 3) (k := 0) (l := 2) (by decide) (by decide) (by decide) (by decide) p
  · exact same_right_reverse (i := 0) (j := 1) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact same_left_reverse (i := 1) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact self_comm_at blocks 1 3 p
  · exact same_right (i := 1) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact disjoint_comm (i := 2) (j := 3) (k := 0) (l := 1) (by decide) (by decide) (by decide) (by decide) p
  · exact adjacent_reverse (i := 0) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact same_right_reverse (i := 0) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact adjacent_reverse (i := 1) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact same_right_reverse (i := 1) (j := 2) (k := 3) hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p
  · exact self_comm_at blocks 2 3 p

/-- Complete ordered commutator square; no mixed term is dropped. -/
def commutatorSquare (p : RatPoly) : RatPoly :=
  sum6 fun a => sum6 fun b =>
    let z := polyAdd (field a (field b p)) (polyNeg (field b (field a p)))
    polyMul z z

/-- Complete ordered second-derivative square on the actual six fields. -/
def hessianSquare (p : RatPoly) : RatPoly :=
  sum6 fun a => sum6 fun b => polyMul (field a (field b p)) (field a (field b p))

/-- Complete ordered symmetric second-derivative square. -/
def symmetricSquare (p : RatPoly) : RatPoly :=
  sum6 fun a => sum6 fun b =>
    let z := polyAdd (field a (field b p)) (field b (field a p))
    polyMul z z

/-- Actual 36-pair SO(4) identity; the constant is FOUR, not a hidden count. -/
theorem commutator_square_carrier {blocks : Nat} (hb : 0 < blocks) (p : RatPoly) :
    HaarCarrierEqv blocks (commutatorSquare p) (polySmul 4 (angularSquare p)) := by
  have h := sum6_carrier (blocks := blocks) (fun a ha => sum6_carrier (fun b hb' =>
    HaarCarrierEqv.mul (entry_carrier hb a b ha hb' p) (entry_carrier hb a b ha hb' p)))
  have hn : RatPolyCoeffEqv
      (sum6 fun a => sum6 fun b => polyMul (entry a b p) (entry a b p))
      (polySmul 4 (angularSquare p)) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.const 0) (.const 0)) (.add (.mul (.neg (.var 3)) (.neg (.var 3))) (.add (.mul (.neg (.var 4)) (.neg (.var 4))) (.add (.mul (.var 1) (.var 1)) (.add (.mul (.var 2) (.var 2)) (.mul (.const 0) (.const 0))))))) (.add (.add (.mul (.var 3) (.var 3)) (.add (.mul (.const 0) (.const 0)) (.add (.mul (.neg (.var 5)) (.neg (.var 5))) (.add (.mul (.neg (.var 0)) (.neg (.var 0))) (.add (.mul (.const 0) (.const 0)) (.mul (.var 2) (.var 2))))))) (.add (.add (.mul (.var 4) (.var 4)) (.add (.mul (.var 5) (.var 5)) (.add (.mul (.const 0) (.const 0)) (.add (.mul (.const 0) (.const 0)) (.add (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.neg (.var 1)) (.neg (.var 1)))))))) (.add (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.add (.mul (.var 0) (.var 0)) (.add (.mul (.const 0) (.const 0)) (.add (.mul (.const 0) (.const 0)) (.add (.mul (.neg (.var 5)) (.neg (.var 5))) (.mul (.var 4) (.var 4))))))) (.add (.add (.mul (.neg (.var 2)) (.neg (.var 2))) (.add (.mul (.const 0) (.const 0)) (.add (.mul (.var 0) (.var 0)) (.add (.mul (.var 5) (.var 5)) (.add (.mul (.const 0) (.const 0)) (.mul (.neg (.var 3)) (.neg (.var 3)))))))) (.add (.mul (.const 0) (.const 0)) (.add (.mul (.neg (.var 2)) (.neg (.var 2))) (.add (.mul (.var 1) (.var 1)) (.add (.mul (.neg (.var 4)) (.neg (.var 4))) (.add (.mul (.var 3) (.var 3)) (.mul (.const 0) (.const 0))))))))))))
      (.mul (.const 4) (.add (.mul (.var 0) (.var 0)) (.add (.mul (.var 1) (.var 1)) (.add (.mul (.var 2) (.var 2)) (.add (.mul (.var 3) (.var 3)) (.add (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5))))))))
      (by decide) (fun a => field a p)).trans (cap_mul_left 4 (angularSquare p))
  exact HaarCarrierEqv.trans h (RatPolyCoeffEqv.haarCarrier hn)

private def quarter : Q' := HalfPow.half*HalfPow.half

set_option maxRecDepth 2048 in
private theorem matrix_four_identity (p : RatPoly) :
    RatPolyCoeffEqv (polySmul 4 (hessianSquare p))
      (polyAdd (commutatorSquare p) (symmetricSquare p)) :=
  (cap_mul_left 4 (hessianSquare p)).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.const 4) (.add (.add (.mul (.var 0) (.var 0)) (.add (.mul (.var 1) (.var 1)) (.add (.mul (.var 2) (.var 2)) (.add (.mul (.var 3) (.var 3)) (.add (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5))))))) (.add (.add (.mul (.var 6) (.var 6)) (.add (.mul (.var 7) (.var 7)) (.add (.mul (.var 8) (.var 8)) (.add (.mul (.var 9) (.var 9)) (.add (.mul (.var 10) (.var 10)) (.mul (.var 11) (.var 11))))))) (.add (.add (.mul (.var 12) (.var 12)) (.add (.mul (.var 13) (.var 13)) (.add (.mul (.var 14) (.var 14)) (.add (.mul (.var 15) (.var 15)) (.add (.mul (.var 16) (.var 16)) (.mul (.var 17) (.var 17))))))) (.add (.add (.mul (.var 18) (.var 18)) (.add (.mul (.var 19) (.var 19)) (.add (.mul (.var 20) (.var 20)) (.add (.mul (.var 21) (.var 21)) (.add (.mul (.var 22) (.var 22)) (.mul (.var 23) (.var 23))))))) (.add (.add (.mul (.var 24) (.var 24)) (.add (.mul (.var 25) (.var 25)) (.add (.mul (.var 26) (.var 26)) (.add (.mul (.var 27) (.var 27)) (.add (.mul (.var 28) (.var 28)) (.mul (.var 29) (.var 29))))))) (.add (.mul (.var 30) (.var 30)) (.add (.mul (.var 31) (.var 31)) (.add (.mul (.var 32) (.var 32)) (.add (.mul (.var 33) (.var 33)) (.add (.mul (.var 34) (.var 34)) (.mul (.var 35) (.var 35)))))))))))))
      (.add (.add (.add (.mul (.add (.var 0) (.neg (.var 0))) (.add (.var 0) (.neg (.var 0)))) (.add (.mul (.add (.var 1) (.neg (.var 6))) (.add (.var 1) (.neg (.var 6)))) (.add (.mul (.add (.var 2) (.neg (.var 12))) (.add (.var 2) (.neg (.var 12)))) (.add (.mul (.add (.var 3) (.neg (.var 18))) (.add (.var 3) (.neg (.var 18)))) (.add (.mul (.add (.var 4) (.neg (.var 24))) (.add (.var 4) (.neg (.var 24)))) (.mul (.add (.var 5) (.neg (.var 30))) (.add (.var 5) (.neg (.var 30))))))))) (.add (.add (.mul (.add (.var 6) (.neg (.var 1))) (.add (.var 6) (.neg (.var 1)))) (.add (.mul (.add (.var 7) (.neg (.var 7))) (.add (.var 7) (.neg (.var 7)))) (.add (.mul (.add (.var 8) (.neg (.var 13))) (.add (.var 8) (.neg (.var 13)))) (.add (.mul (.add (.var 9) (.neg (.var 19))) (.add (.var 9) (.neg (.var 19)))) (.add (.mul (.add (.var 10) (.neg (.var 25))) (.add (.var 10) (.neg (.var 25)))) (.mul (.add (.var 11) (.neg (.var 31))) (.add (.var 11) (.neg (.var 31))))))))) (.add (.add (.mul (.add (.var 12) (.neg (.var 2))) (.add (.var 12) (.neg (.var 2)))) (.add (.mul (.add (.var 13) (.neg (.var 8))) (.add (.var 13) (.neg (.var 8)))) (.add (.mul (.add (.var 14) (.neg (.var 14))) (.add (.var 14) (.neg (.var 14)))) (.add (.mul (.add (.var 15) (.neg (.var 20))) (.add (.var 15) (.neg (.var 20)))) (.add (.mul (.add (.var 16) (.neg (.var 26))) (.add (.var 16) (.neg (.var 26)))) (.mul (.add (.var 17) (.neg (.var 32))) (.add (.var 17) (.neg (.var 32))))))))) (.add (.add (.mul (.add (.var 18) (.neg (.var 3))) (.add (.var 18) (.neg (.var 3)))) (.add (.mul (.add (.var 19) (.neg (.var 9))) (.add (.var 19) (.neg (.var 9)))) (.add (.mul (.add (.var 20) (.neg (.var 15))) (.add (.var 20) (.neg (.var 15)))) (.add (.mul (.add (.var 21) (.neg (.var 21))) (.add (.var 21) (.neg (.var 21)))) (.add (.mul (.add (.var 22) (.neg (.var 27))) (.add (.var 22) (.neg (.var 27)))) (.mul (.add (.var 23) (.neg (.var 33))) (.add (.var 23) (.neg (.var 33))))))))) (.add (.add (.mul (.add (.var 24) (.neg (.var 4))) (.add (.var 24) (.neg (.var 4)))) (.add (.mul (.add (.var 25) (.neg (.var 10))) (.add (.var 25) (.neg (.var 10)))) (.add (.mul (.add (.var 26) (.neg (.var 16))) (.add (.var 26) (.neg (.var 16)))) (.add (.mul (.add (.var 27) (.neg (.var 22))) (.add (.var 27) (.neg (.var 22)))) (.add (.mul (.add (.var 28) (.neg (.var 28))) (.add (.var 28) (.neg (.var 28)))) (.mul (.add (.var 29) (.neg (.var 34))) (.add (.var 29) (.neg (.var 34))))))))) (.add (.mul (.add (.var 30) (.neg (.var 5))) (.add (.var 30) (.neg (.var 5)))) (.add (.mul (.add (.var 31) (.neg (.var 11))) (.add (.var 31) (.neg (.var 11)))) (.add (.mul (.add (.var 32) (.neg (.var 17))) (.add (.var 32) (.neg (.var 17)))) (.add (.mul (.add (.var 33) (.neg (.var 23))) (.add (.var 33) (.neg (.var 23)))) (.add (.mul (.add (.var 34) (.neg (.var 29))) (.add (.var 34) (.neg (.var 29)))) (.mul (.add (.var 35) (.neg (.var 35))) (.add (.var 35) (.neg (.var 35)))))))))))))) (.add (.add (.mul (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0))) (.add (.mul (.add (.var 1) (.var 6)) (.add (.var 1) (.var 6))) (.add (.mul (.add (.var 2) (.var 12)) (.add (.var 2) (.var 12))) (.add (.mul (.add (.var 3) (.var 18)) (.add (.var 3) (.var 18))) (.add (.mul (.add (.var 4) (.var 24)) (.add (.var 4) (.var 24))) (.mul (.add (.var 5) (.var 30)) (.add (.var 5) (.var 30)))))))) (.add (.add (.mul (.add (.var 6) (.var 1)) (.add (.var 6) (.var 1))) (.add (.mul (.add (.var 7) (.var 7)) (.add (.var 7) (.var 7))) (.add (.mul (.add (.var 8) (.var 13)) (.add (.var 8) (.var 13))) (.add (.mul (.add (.var 9) (.var 19)) (.add (.var 9) (.var 19))) (.add (.mul (.add (.var 10) (.var 25)) (.add (.var 10) (.var 25))) (.mul (.add (.var 11) (.var 31)) (.add (.var 11) (.var 31)))))))) (.add (.add (.mul (.add (.var 12) (.var 2)) (.add (.var 12) (.var 2))) (.add (.mul (.add (.var 13) (.var 8)) (.add (.var 13) (.var 8))) (.add (.mul (.add (.var 14) (.var 14)) (.add (.var 14) (.var 14))) (.add (.mul (.add (.var 15) (.var 20)) (.add (.var 15) (.var 20))) (.add (.mul (.add (.var 16) (.var 26)) (.add (.var 16) (.var 26))) (.mul (.add (.var 17) (.var 32)) (.add (.var 17) (.var 32)))))))) (.add (.add (.mul (.add (.var 18) (.var 3)) (.add (.var 18) (.var 3))) (.add (.mul (.add (.var 19) (.var 9)) (.add (.var 19) (.var 9))) (.add (.mul (.add (.var 20) (.var 15)) (.add (.var 20) (.var 15))) (.add (.mul (.add (.var 21) (.var 21)) (.add (.var 21) (.var 21))) (.add (.mul (.add (.var 22) (.var 27)) (.add (.var 22) (.var 27))) (.mul (.add (.var 23) (.var 33)) (.add (.var 23) (.var 33)))))))) (.add (.add (.mul (.add (.var 24) (.var 4)) (.add (.var 24) (.var 4))) (.add (.mul (.add (.var 25) (.var 10)) (.add (.var 25) (.var 10))) (.add (.mul (.add (.var 26) (.var 16)) (.add (.var 26) (.var 16))) (.add (.mul (.add (.var 27) (.var 22)) (.add (.var 27) (.var 22))) (.add (.mul (.add (.var 28) (.var 28)) (.add (.var 28) (.var 28))) (.mul (.add (.var 29) (.var 34)) (.add (.var 29) (.var 34)))))))) (.add (.mul (.add (.var 30) (.var 5)) (.add (.var 30) (.var 5))) (.add (.mul (.add (.var 31) (.var 11)) (.add (.var 31) (.var 11))) (.add (.mul (.add (.var 32) (.var 17)) (.add (.var 32) (.var 17))) (.add (.mul (.add (.var 33) (.var 23)) (.add (.var 33) (.var 23))) (.add (.mul (.add (.var 34) (.var 29)) (.add (.var 34) (.var 29))) (.mul (.add (.var 35) (.var 35)) (.add (.var 35) (.var 35))))))))))))))
      (by decide) (fun a => field (a/6) (field (a%6) p)))

private theorem matrix_identity (p : RatPoly) :
    RatPolyCoeffEqv (hessianSquare p)
      (polySmul quarter (polyAdd (commutatorSquare p) (symmetricSquare p))) :=
  ((RatPolyCoeffEqv.smul quarter (matrix_four_identity p).symm).trans
    ((RatPolyCoeffEqv.smul_assoc quarter 4 _).trans
      ((RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv (quarter*4) 1) _).trans
        (RatPolyCoeffEqv.one_smul _)))).symm

/-- The exact curvature margin is a symmetric-Hessian square under every
surviving Haar insertion, including arbitrary signed spectator coefficients. -/
theorem hessian_margin_carrier {blocks : Nat} (hb : 0 < blocks) (p : RatPoly) :
    HaarCarrierEqv blocks (polyAdd (hessianSquare p) (polyNeg (angularSquare p)))
      (polySmul quarter (symmetricSquare p)) := by
  have h := HaarCarrierEqv.add
    ((RatPolyCoeffEqv.haarCarrier (matrix_identity p)).trans
      (HaarCarrierEqv.smul quarter (HaarCarrierEqv.add
        (commutator_square_carrier hb p) (HaarCarrierEqv.refl blocks (symmetricSquare p)))))
    (HaarCarrierEqv.refl blocks (polyNeg (angularSquare p)))
  have hc : RatPolyCoeffEqv
      (polySmul quarter (polySmul 4 (angularSquare p))) (angularSquare p) :=
    (RatPolyCoeffEqv.smul_assoc quarter 4 _).trans
      ((RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv (quarter*4) 1) _).trans
        (RatPolyCoeffEqv.one_smul _))
  have hr := (((RatPolyCoeffEqv.smul_add quarter _ _).trans
    (hc.add (RatPolyCoeffEqv.refl (polySmul quarter (symmetricSquare p))))).add
      (RatPolyCoeffEqv.refl (polyNeg (angularSquare p)))).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => angularSquare p | _ => polySmul quarter (symmetricSquare p)))
  exact HaarCarrierEqv.trans h (RatPolyCoeffEqv.haarCarrier hr)

private theorem field_supported {blocks : Nat} (hb : 0 < blocks) (a : Nat)
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (field a p) := by
  unfold field
  split <;> exact angularDerivative_supported hb (by decide) (by decide) hp

private def sum6_certificate {blocks : Nat} {f : Nat → RatPoly}
    (C : ∀ a, Certificate blocks (f a)) : Certificate blocks (sum6 f) :=
  .add (C 0) (.add (C 1) (.add (C 2) (.add (C 3) (.add (C 4) (C 5)))))

/-- Constructed curvature square certificate, with the ORIGINAL input and
all 36 ordered signed Hessian terms. No Bochner/centrality premise is supplied. -/
def hessian_curvature_certificate {blocks : Nat} (hb : 0 < blocks) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    Certificate blocks (polyAdd (hessianSquare p) (polyNeg (angularSquare p))) :=
  .transport (hessian_margin_carrier hb p) (.smul quarter (by decide)
    (sum6_certificate (fun a => sum6_certificate (fun b =>
      .square (polyAdd (field a (field b p)) (field b (field a p)))
        (polyAdd_supported (field_supported hb a (field_supported hb b hp))
          (field_supported hb b (field_supported hb a hp)))))))

end YMGap.Continuum.SU2QuaternionAngularHessianSquares

#print axioms YMGap.Continuum.SU2QuaternionAngularHessianSquares.commutator_square_carrier
#print axioms YMGap.Continuum.SU2QuaternionAngularHessianSquares.hessian_margin_carrier
#print axioms YMGap.Continuum.SU2QuaternionAngularHessianSquares.hessian_curvature_certificate
