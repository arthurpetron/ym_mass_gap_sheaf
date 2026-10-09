/-
Ordered paired-source algebra for a head-linear quaternion polynomial.
The two derivative orders are retained; no commutation is asserted.
-/

import YMGap.Continuum.QuaternionHaarPairedLinearHessian
import YMGap.Continuum.QPolyHaarFrozenChain
import YMGap.Continuum.SU2QuaternionHaarAngularIBP

namespace YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport (angularDerivative_smul)
open YMGap.Continuum.SU2QuaternionHaarAngularIBP (angularDerivative_independent_zero)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets
  (pairedDerivative threeSum pairedDerivative_carrier)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QuaternionHaarPairedLinearHessian
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QPolyHaarFrozenChain (threeSum_congr threeSum_add)
open YMGap.Continuum.QPolyHaarAngularChain (paired_mul)

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

private theorem paired_add (j : Fin 3) (a b : RatPoly) :
    RatPolyCoeffEqv (pairedDerivative j (polyAdd a b))
      (polyAdd (pairedDerivative j a) (pairedDerivative j b)) := by
  rcases direction_cases j with rfl | rfl | rfl
  · exact ((angularDerivative_add 0 1 a b).add
      (angularDerivative_add 2 3 a b)).trans (RatPolyCoeffEqv.four_add_swap _ _ _ _)
  · refine (RatPolyCoeffEqv.add (angularDerivative_add 0 2 a b)
      (RatPolyCoeffEqv.neg (angularDerivative_add 1 3 a b))).trans ?_
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
      (by decide) (fun
        | 0 => angularDerivative 0 2 a | 1 => angularDerivative 0 2 b
        | 2 => angularDerivative 1 3 a | _ => angularDerivative 1 3 b)
  · exact ((angularDerivative_add 0 3 a b).add
      (angularDerivative_add 1 2 a b)).trans (RatPolyCoeffEqv.four_add_swap _ _ _ _)

private theorem paired_threeSum (j : Fin 3) (f : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (pairedDerivative j (threeSum f))
      (threeSum (fun i => pairedDerivative j (f i))) :=
  (paired_add j (f 0) (polyAdd (f 1) (f 2))).trans
    ((RatPolyCoeffEqv.refl _).add (paired_add j (f 1) (f 2)))

private theorem paired_independent_zero (j : Fin 3) (A : RatPoly)
    (hA : HasQuaternionBlockDegree 0 0 A) :
    RatPolyCoeffEqv (pairedDerivative j A) polyZero := by
  rcases direction_cases j with rfl | rfl | rfl
  · exact (angularDerivative_independent_zero (by decide) (by decide) A hA).add
      (angularDerivative_independent_zero (by decide) (by decide) A hA)
  · exact (angularDerivative_independent_zero (by decide) (by decide) A hA).add
      (RatPolyCoeffEqv.neg (angularDerivative_independent_zero
        (by decide) (by decide) A hA))
  · exact (angularDerivative_independent_zero (by decide) (by decide) A hA).add
      (angularDerivative_independent_zero (by decide) (by decide) A hA)

private theorem smul_neg (c : Q') (a : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul c a)) (polySmul c (polyNeg a)) :=
  (neg_smul (polySmul c a)).trans
    ((RatPolyCoeffEqv.smul_assoc (-1) c a).trans
      ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv (-1) c) a).trans
        ((RatPolyCoeffEqv.smul_assoc c (-1) a).symm.trans
          ((neg_smul a).symm.smul c))))

private theorem paired_smul (j : Fin 3) (c : Q') (a : RatPoly) :
    RatPolyCoeffEqv (pairedDerivative j (polySmul c a))
      (polySmul c (pairedDerivative j a)) := by
  rcases direction_cases j with rfl | rfl | rfl
  · exact ((angularDerivative_smul 0 1 c a).add
      (angularDerivative_smul 2 3 c a)).trans
      (RatPolyCoeffEqv.smul_add c _ _).symm
  · exact ((angularDerivative_smul 0 2 c a).add
      (RatPolyCoeffEqv.neg (angularDerivative_smul 1 3 c a))).trans
      (((RatPolyCoeffEqv.refl _).add (smul_neg c _)).trans
        (RatPolyCoeffEqv.smul_add c _ _).symm)
  · exact ((angularDerivative_smul 0 3 c a).add
      (angularDerivative_smul 1 2 c a)).trans
      (RatPolyCoeffEqv.smul_add c _ _).symm

def gradient (p : RatPoly) (i : Fin 3) : RatPoly := pairedDerivative i p

def gradientSquare (p : RatPoly) : RatPoly := threeSquare (gradient p)

def orderedContraction (p : RatPoly) (j : Fin 3) : RatPoly :=
  threeSum (fun i => polyMul (gradient p i) (pairedDerivative i (gradient p j)))

def reverseContraction (p : RatPoly) (j : Fin 3) : RatPoly :=
  threeSum (fun i => polyMul (gradient p i) (pairedDerivative j (gradient p i)))

def sourceInner (p : RatPoly) (j : Fin 3) : RatPoly :=
  threeSum (fun i => pairedDerivative i
    (polyMul (gradient p i) (gradient p j)))

def doubleIBPSource (p : RatPoly) : RatPoly :=
  threeSum (fun j => pairedDerivative j (sourceInner p j))

private def half : Q' := Q'.mkPos 1 2 (by decide)

private theorem half_double (a : RatPoly) :
    RatPolyCoeffEqv (polySmul half (polyAdd a a)) a := by
  have htwo : RatPolyCoeffEqv (polyAdd a a) (polySmul 2 a) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
      (by decide) (fun _ => a)).trans
        ((cap_mul_left (Q'.ofInt 2) a).trans (RatPolyCoeffEqv.smul_coefficient
          (by decide : Q'.eqv (Q'.ofInt 2) 2) a))
  exact (htwo.smul half).trans
    ((RatPolyCoeffEqv.smul_assoc half 2 a).trans
      ((RatPolyCoeffEqv.smul_coefficient
        (by decide : Q'.eqv (half * 2) 1) a).trans
        (RatPolyCoeffEqv.one_smul a)))

private theorem carrier_double_cancel {blocks : Nat} {a b : RatPoly}
    (h : HaarCarrierEqv blocks (polyAdd a a) (polyAdd b b)) :
    HaarCarrierEqv blocks a b :=
  (RatPolyCoeffEqv.haarCarrier (half_double a).symm).trans
    ((HaarCarrierEqv.smul half h).trans
      (RatPolyCoeffEqv.haarCarrier (half_double b)))

private theorem paired_gradientSquare (j : Fin 3) (p : RatPoly) :
    RatPolyCoeffEqv (pairedDerivative j (gradientSquare p))
      (polyAdd (reverseContraction p j) (reverseContraction p j)) := by
  let u := gradient p
  have hcell (i : Fin 3) : RatPolyCoeffEqv
      (pairedDerivative j (polyMul (u i) (u i)))
      (polyAdd (polyMul (u i) (pairedDerivative j (u i)))
        (polyMul (u i) (pairedDerivative j (u i)))) :=
    (paired_mul j (u i) (u i)).trans
      ((RatPolyCoeffEqv.mul_comm (pairedDerivative j (u i)) (u i)).add
        (RatPolyCoeffEqv.refl _))
  exact (paired_threeSum j (fun i => polyMul (u i) (u i))).trans
    ((threeSum_congr hcell).trans
      (threeSum_add _ _))

/-- The actual head-independent amplitude pin differentiates to the
contracted reverse Hessian. No amplitude value is assumed. -/
theorem reverse_contraction_of_amplitude {blocks : Nat} (hb : 0 < blocks)
    (p A : RatPoly) (hA : HasQuaternionBlockDegree 0 0 A)
    (hamp : HaarCarrierEqv blocks
      (polyAdd (polyMul p p) (gradientSquare p)) A) (j : Fin 3) :
    HaarCarrierEqv blocks (reverseContraction p j)
      (polyNeg (polyMul p (gradient p j))) := by
  let v := polyMul p (gradient p j)
  let R := reverseContraction p j
  have hzero : HaarCarrierEqv blocks
      (pairedDerivative j (polyAdd (polyMul p p) (gradientSquare p))) polyZero :=
    (pairedDerivative_carrier hb j hamp).trans
      (RatPolyCoeffEqv.haarCarrier (paired_independent_zero j A hA))
  have hexpand : RatPolyCoeffEqv
      (pairedDerivative j (polyAdd (polyMul p p) (gradientSquare p)))
      (polyAdd (polyAdd v v) (polyAdd R R)) :=
    (paired_add j (polyMul p p) (gradientSquare p)).trans
      (((paired_mul j p p).trans
        ((RatPolyCoeffEqv.mul_comm (gradient p j) p).add (RatPolyCoeffEqv.refl _))).add
        (paired_gradientSquare j p))
  have hdouble : HaarCarrierEqv blocks
      (polyAdd (polyAdd v R) (polyAdd v R)) (polyAdd polyZero polyZero) :=
    (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.var 0) (.var 0)) (.add (.var 1) (.var 1)))
      (by decide) (fun | 0 => v | _ => R))).trans
      ((RatPolyCoeffEqv.haarCarrier hexpand.symm).trans
        (hzero.trans (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.refl _))))
  have hvr : HaarCarrierEqv blocks (polyAdd v R) polyZero :=
    carrier_double_cancel hdouble
  have hneg := HaarCarrierEqv.add (HaarCarrierEqv.refl blocks (polyNeg v)) hvr
  have hl : RatPolyCoeffEqv (polyAdd (polyNeg v) (polyAdd v R)) R :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.neg (.var 0)) (.add (.var 0) (.var 1))) (.var 1)
      (by decide) (fun | 0 => v | _ => R)
  exact (RatPolyCoeffEqv.haarCarrier hl.symm).trans
    (hneg.trans (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_zero _)))

private theorem diagonal_cell {blocks : Nat} (hb : 0 < blocks)
    (p : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p) (j : Fin 3) :
    HaarCarrierEqv blocks
      (polyMul (gradient p j) (pairedDerivative j (gradient p j)))
      (polyNeg (polyMul p (gradient p j))) := by
  refine (HaarCarrierEqv.mul_left (gradient p j)
    (paired_linear_diagonal hb p hp j)).trans ?_
  exact RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 1) (.var 0)))
    (by decide) (fun | 0 => gradient p j | _ => p))

private theorem mixed_cell {blocks : Nat} (hb : 0 < blocks)
    (p : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p)
    (i j : Fin 3) (hij : i ≠ j) :
    HaarCarrierEqv blocks
      (polyAdd
        (polyMul (gradient p i) (pairedDerivative j (gradient p i)))
        (polyMul (gradient p i) (pairedDerivative i (gradient p j)))) polyZero := by
  refine (RatPolyCoeffEqv.haarCarrier
    (RatPolyCoeffEqv.mul_add_right (gradient p i) _ _).symm).trans ?_
  exact (HaarCarrierEqv.mul_left (gradient p i)
    (paired_linear_mixed hb p hp j i (Ne.symm hij))).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_right _))

/-- Symmetrized contraction of the two ACTUAL ordered Hessians. This is a
derived finite identity, not a commutation premise. -/
theorem ordered_reverse_contraction {blocks : Nat} (hb : 0 < blocks)
    (p : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p) (j : Fin 3) :
    HaarCarrierEqv blocks
      (polyAdd (reverseContraction p j) (orderedContraction p j))
      (polyAdd (polyNeg (polyMul p (gradient p j)))
        (polyNeg (polyMul p (gradient p j)))) := by
  let v := polyMul p (gradient p j)
  have hcell (i : Fin 3) : HaarCarrierEqv blocks
      (polyAdd
        (polyMul (gradient p i) (pairedDerivative j (gradient p i)))
        (polyMul (gradient p i) (pairedDerivative i (gradient p j))))
      (if i = j then polyAdd (polyNeg v) (polyNeg v) else polyZero) := by
    by_cases hij : i = j
    · subst i
      simpa only [if_pos rfl] using
        (HaarCarrierEqv.add (diagonal_cell hb p hp j) (diagonal_cell hb p hp j))
    · simpa only [if_neg hij] using mixed_cell hb p hp i j hij
  have hsum := (threeSum_add
    (fun i => polyMul (gradient p i) (pairedDerivative j (gradient p i)))
    (fun i => polyMul (gradient p i) (pairedDerivative i (gradient p j)))).symm
  refine (RatPolyCoeffEqv.haarCarrier hsum).trans
    ((HaarCarrierEqv.add (hcell 0)
      (HaarCarrierEqv.add (hcell 1) (hcell 2))).trans ?_)
  rcases direction_cases j with rfl | rfl | rfl
  · change HaarCarrierEqv blocks
      (polyAdd (polyAdd (polyNeg v) (polyNeg v))
        (polyAdd polyZero polyZero)) (polyAdd (polyNeg v) (polyNeg v))
    exact RatPolyCoeffEqv.haarCarrier
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.zero_add polyZero)).trans
        (RatPolyCoeffEqv.add_zero _))
  · change HaarCarrierEqv blocks
      (polyAdd polyZero
        (polyAdd (polyAdd (polyNeg v) (polyNeg v)) polyZero))
      (polyAdd (polyNeg v) (polyNeg v))
    exact RatPolyCoeffEqv.haarCarrier
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)).trans
        (RatPolyCoeffEqv.zero_add _))
  · change HaarCarrierEqv blocks
      (polyAdd polyZero
        (polyAdd polyZero (polyAdd (polyNeg v) (polyNeg v))))
      (polyAdd (polyNeg v) (polyNeg v))
    exact RatPolyCoeffEqv.haarCarrier
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.zero_add _)).trans
        (RatPolyCoeffEqv.zero_add _))

/-- One contracted ordered mixed jet, derived from the literal amplitude
and the symmetrized linear Hessian. -/
theorem ordered_contraction_of_amplitude {blocks : Nat} (hb : 0 < blocks)
    (p A : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p)
    (hA : HasQuaternionBlockDegree 0 0 A)
    (hamp : HaarCarrierEqv blocks
      (polyAdd (polyMul p p) (gradientSquare p)) A) (j : Fin 3) :
    HaarCarrierEqv blocks (orderedContraction p j)
      (polyNeg (polyMul p (gradient p j))) := by
  let v := polyMul p (gradient p j)
  let R := reverseContraction p j
  let S := orderedContraction p j
  have hr := reverse_contraction_of_amplitude hb p A hA hamp j
  have hm := ordered_reverse_contraction hb p hp j
  have hleft : HaarCarrierEqv blocks (polyAdd v (polyAdd R S)) S :=
    (HaarCarrierEqv.add (HaarCarrierEqv.refl blocks v)
      (HaarCarrierEqv.add hr (HaarCarrierEqv.refl blocks S))).trans
      (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 0) (.add (.neg (.var 0)) (.var 1))) (.var 1)
        (by decide) (fun | 0 => v | _ => S)))
  have hright : RatPolyCoeffEqv
      (polyAdd v (polyAdd (polyNeg v) (polyNeg v))) (polyNeg v) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.add (.neg (.var 0)) (.neg (.var 0))))
      (.neg (.var 0)) (by decide) (fun _ => v)
  exact hleft.symm.trans
    ((HaarCarrierEqv.add (HaarCarrierEqv.refl blocks v) hm).trans
      (RatPolyCoeffEqv.haarCarrier hright))

/-- First ordered product derivative: all three diagonal jets are -p,
and the contracted mixed term is separately produced above. -/
theorem sourceInner_of_amplitude {blocks : Nat} (hb : 0 < blocks)
    (p A : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p)
    (hA : HasQuaternionBlockDegree 0 0 A)
    (hamp : HaarCarrierEqv blocks
      (polyAdd (polyMul p p) (gradientSquare p)) A) (j : Fin 3) :
    HaarCarrierEqv blocks (sourceInner p j)
      (polySmul (-4) (polyMul p (gradient p j))) := by
  let v := polyMul p (gradient p j)
  let D := threeSum (fun i => polyMul
    (pairedDerivative i (gradient p i)) (gradient p j))
  let S := orderedContraction p j
  have hexpand : RatPolyCoeffEqv (sourceInner p j) (polyAdd D S) :=
    (threeSum_congr (fun i => paired_mul i (gradient p i) (gradient p j))).trans
      (threeSum_add _ _)
  have hdcell (i : Fin 3) : HaarCarrierEqv blocks
      (polyMul (pairedDerivative i (gradient p i)) (gradient p j)) (polyNeg v) :=
    (HaarCarrierEqv.mul_right (gradient p j)
      (paired_linear_diagonal hb p hp i)).trans
      (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.neg (.var 0)) (.var 1)) (.neg (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => p | _ => gradient p j)))
  have hd : HaarCarrierEqv blocks D
      (polyAdd (polyNeg v) (polyAdd (polyNeg v) (polyNeg v))) :=
    HaarCarrierEqv.add (hdcell 0) (HaarCarrierEqv.add (hdcell 1) (hdcell 2))
  have hs := ordered_contraction_of_amplitude hb p A hp hA hamp j
  have hfour : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyNeg v) (polyAdd (polyNeg v) (polyNeg v)))
        (polyNeg v)) (polySmul (-4) v) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.neg (.var 0))
        (.add (.neg (.var 0)) (.neg (.var 0)))) (.neg (.var 0)))
      (.mul (.const (-4)) (.var 0)) (by decide) (fun _ => v)).trans
      (cap_mul_left (-4) v)
  exact (RatPolyCoeffEqv.haarCarrier hexpand).trans
    ((HaarCarrierEqv.add hd hs).trans (RatPolyCoeffEqv.haarCarrier hfour))

/-- The complete ordered double-IBP source, before any integration, is the
literal quadratic combination of the original head-linear source and its
three paired first jets. -/
theorem doubleIBPSource_pin {blocks : Nat} (hb : 0 < blocks)
    (p A : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p)
    (hA : HasQuaternionBlockDegree 0 0 A)
    (hamp : HaarCarrierEqv blocks
      (polyAdd (polyMul p p) (gradientSquare p)) A) :
    HaarCarrierEqv blocks (doubleIBPSource p)
      (polyAdd (polySmul (-4) (gradientSquare p))
        (polySmul 12 (polyMul p p))) := by
  let u := gradient p
  let v := polyMul p p
  have hj (j : Fin 3) : HaarCarrierEqv blocks
      (pairedDerivative j (sourceInner p j))
      (polySmul (-4) (polyAdd (polyMul (u j) (u j)) (polyNeg v))) := by
    have hs := pairedDerivative_carrier hb j
      (sourceInner_of_amplitude hb p A hp hA hamp j)
    have hd := paired_linear_diagonal hb p hp j
    have hcell : HaarCarrierEqv blocks
        (polyAdd (polyMul (u j) (u j))
          (polyMul p (pairedDerivative j (u j))))
        (polyAdd (polyMul (u j) (u j)) (polyNeg v)) :=
      (HaarCarrierEqv.add (HaarCarrierEqv.refl blocks _)
        (HaarCarrierEqv.mul_left p hd)).trans
        (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.refl _).add
          (coeffEvalExpr_eqv_of_normalize_eq
            (.mul (.var 0) (.neg (.var 0))) (.neg (.mul (.var 0) (.var 0)))
            (by decide) (fun _ => p))))
    exact hs.trans
      ((RatPolyCoeffEqv.haarCarrier
        ((paired_smul j (-4) (polyMul p (u j))).trans
          ((paired_mul j p (u j)).smul (-4)))).trans
        (HaarCarrierEqv.smul (-4) hcell))
  have hcap (j : Fin 3) : RatPolyCoeffEqv
      (polySmul (-4) (polyAdd (polyMul (u j) (u j)) (polyNeg v)))
      (polyMul (cap (-4)) (polyAdd (polyMul (u j) (u j)) (polyNeg v))) :=
    (cap_mul_left (-4) _).symm
  have hnorm : RatPolyCoeffEqv
      (threeSum (fun j => polyMul (cap (-4))
        (polyAdd (polyMul (u j) (u j)) (polyNeg v))))
      (polyAdd (polyMul (cap (-4)) (gradientSquare p))
        (polyMul (cap 12) v)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.mul (.const (-4)) (.add (.mul (.var 0) (.var 0))
          (.neg (.mul (.var 3) (.var 3)))))
        (.add
          (.mul (.const (-4)) (.add (.mul (.var 1) (.var 1))
            (.neg (.mul (.var 3) (.var 3)))))
          (.mul (.const (-4)) (.add (.mul (.var 2) (.var 2))
            (.neg (.mul (.var 3) (.var 3)))))))
      (.add
        (.mul (.const (-4))
          (.add (.mul (.var 0) (.var 0))
            (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))))
        (.mul (.const 12) (.mul (.var 3) (.var 3))))
      (by decide) (fun | 0 => u 0 | 1 => u 1 | 2 => u 2 | _ => p)
  exact (HaarCarrierEqv.add (hj 0) (HaarCarrierEqv.add (hj 1) (hj 2))).trans
    ((RatPolyCoeffEqv.haarCarrier (threeSum_congr hcap)).trans
      ((RatPolyCoeffEqv.haarCarrier hnorm).trans
        (RatPolyCoeffEqv.haarCarrier
          ((cap_mul_left (-4) (gradientSquare p)).add (cap_mul_left 12 v)))))

/-- If the actual amplitude is carried by a head-independent polynomial A,
the ordered source is 12A-16Γ. The premise is an actual amplitude equality,
not a replacement for the desired source identity. -/
theorem doubleIBPSource_amplitude_pin {blocks : Nat} (hb : 0 < blocks)
    (p A : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p)
    (hA : HasQuaternionBlockDegree 0 0 A)
    (hamp : HaarCarrierEqv blocks
      (polyAdd (polyMul p p) (gradientSquare p)) A) :
    HaarCarrierEqv blocks (doubleIBPSource p)
      (polyAdd (polySmul 12 A) (polySmul (-16) (gradientSquare p))) := by
  let G := gradientSquare p
  let V := polyMul p p
  have halgebra : RatPolyCoeffEqv
      (polyAdd (polySmul (-4) G) (polySmul 12 V))
      (polyAdd (polySmul 12 (polyAdd V G)) (polySmul (-16) G)) :=
    (((cap_mul_left (-4) G).symm.add (cap_mul_left 12 V).symm).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.const (-4)) (.var 1)) (.mul (.const 12) (.var 0)))
        (.add (.mul (.const 12) (.add (.var 0) (.var 1)))
          (.mul (.const (-16)) (.var 1)))
        (by decide) (fun | 0 => V | _ => G))).trans
      ((cap_mul_left 12 (polyAdd V G)).add (cap_mul_left (-16) G))
  exact (doubleIBPSource_pin hb p A hp hA hamp).trans
    ((RatPolyCoeffEqv.haarCarrier halgebra).trans
      (HaarCarrierEqv.add (HaarCarrierEqv.smul 12 hamp)
        (HaarCarrierEqv.refl blocks (polySmul (-16) G))))

end YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP

#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.gradient
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.gradientSquare
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.orderedContraction
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.reverseContraction
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.sourceInner
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.doubleIBPSource
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.reverse_contraction_of_amplitude
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.ordered_reverse_contraction
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.ordered_contraction_of_amplitude
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.sourceInner_of_amplitude
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.doubleIBPSource_pin
#print axioms YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP.doubleIBPSource_amplitude_pin
