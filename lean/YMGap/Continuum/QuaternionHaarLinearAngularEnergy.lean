/-
# Exact six-direction angular energy of a head-linear polynomial

The six coordinate-plane rotations have summed second derivative -3 on
polynomials homogeneous of degree one in the selected quaternion. Haar
integration by parts therefore identifies their summed square energy with
three times the original square, retaining any head-independent background.

This is a local algebraic identity, not an interacting spectral gap. Its
consumer is the incident-plaquette Ward energy: heat comparison and an actual
head-linear source pin are still needed before applying a coercivity bound.
-/

import YMGap.Continuum.QuaternionHaarCoordinateAngularInterval

namespace YMGap.Continuum.QuaternionHaarLinearAngularEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval

local infix:50 " ≈ " => Q'.eqv

/-- Each unoriented coordinate plane occurs exactly once. -/
def six (f : Nat → Nat → RatPoly) : RatPoly :=
  polyAdd (f 0 1) (polyAdd (f 0 2) (polyAdd (f 0 3)
    (polyAdd (f 1 2) (polyAdd (f 1 3) (f 2 3)))))

def angularLaplacian (p : RatPoly) : RatPoly :=
  six (fun i j => angularDerivative i j (angularDerivative i j p))

def angularSquare (p : RatPoly) : RatPoly :=
  six (fun i j => polyMul (angularDerivative i j p) (angularDerivative i j p))

def sixValue (f : Nat → Nat → Q') : Q' :=
  f 0 1 + (f 0 2 + (f 0 3 + (f 1 2 + (f 1 3 + f 2 3))))

theorem sixValue_congr (f g : Nat → Nat → Q')
    (h : ∀ i j, i < 4 → j < 4 → f i j ≈ g i j) : sixValue f ≈ sixValue g :=
  Q'.add_eqv_congr' (h 0 1 (by decide) (by decide))
    (Q'.add_eqv_congr' (h 0 2 (by decide) (by decide))
      (Q'.add_eqv_congr' (h 0 3 (by decide) (by decide))
        (Q'.add_eqv_congr' (h 1 2 (by decide) (by decide))
          (Q'.add_eqv_congr' (h 1 3 (by decide) (by decide)) (h 2 3 (by decide) (by decide))))))

theorem sixValue_mono (f g : Nat → Nat → Q')
    (h : ∀ i j, i < 4 → j < 4 → f i j ≤ g i j) : sixValue f ≤ sixValue g :=
  Q'.add_le_add (h 0 1 (by decide) (by decide))
    (Q'.add_le_add (h 0 2 (by decide) (by decide))
      (Q'.add_le_add (h 0 3 (by decide) (by decide))
        (Q'.add_le_add (h 1 2 (by decide) (by decide))
          (Q'.add_le_add (h 1 3 (by decide) (by decide)) (h 2 3 (by decide) (by decide))))))

theorem sixValue_mul_left (c : Q') (f : Nat → Nat → Q') :
    c*sixValue f ≈ sixValue (fun i j => c*f i j) := by
  have h (a b v : Q') (hv : c*b ≈ v) : c*(a+b) ≈ c*a+v :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c a b) (Q'.add_eqv_congr' (Q'.eqv_refl _) hv)
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _ (Q'.mul_add_eqv c (f 1 3) (f 2 3)))))

theorem sixValue_mul_right (c : Q') (f : Nat → Nat → Q') :
    sixValue f*c ≈ sixValue (fun i j => f i j*c) :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.eqv_trans _ _ _ (sixValue_mul_left c f)
      (sixValue_congr _ _ (fun _ _ _ _ => Q'.mul_comm_eqv _ _)))

private theorem sixValue_neg (f : Nat → Nat → Q') :
    sixValue (fun i j => -(f i j)) ≈ -(sixValue f) := by
  have h (a b c : Q') (hbc : b ≈ -c) : -a+b ≈ -(a+c) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hbc)
      (Q'.eqv_symm (Q'.neg_add_eqv a c))
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _
    (Q'.eqv_symm (Q'.neg_add_eqv (f 1 3) (f 2 3))))))

private theorem haar_mul_add (blocks : Nat) (r p q : RatPoly) :
    quaternionHaar blocks (polyMul r (polyAdd p q)) ≈
      quaternionHaar blocks (polyMul r p) + quaternionHaar blocks (polyMul r q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right r p q))
    (quaternionHaar_append blocks _ _)

/-- Expand exactly the six original Haar moments, retaining their weight. -/
theorem haar_six (blocks : Nat) (r : RatPoly) (f : Nat → Nat → RatPoly) :
    quaternionHaar blocks (polyMul r (six f)) ≈
      sixValue (fun i j => quaternionHaar blocks (polyMul r (f i j))) := by
  have h (p q : RatPoly) (v : Q') (hq : quaternionHaar blocks (polyMul r q) ≈ v) :
      quaternionHaar blocks (polyMul r (polyAdd p q)) ≈
        quaternionHaar blocks (polyMul r p) + v :=
    Q'.eqv_trans _ _ _ (haar_mul_add blocks r p q) (Q'.add_eqv_congr' (Q'.eqv_refl _) hq)
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _ (haar_mul_add blocks r (f 1 3) (f 2 3)))))

/-- The derivative of a head-linear polynomial is head-independent.
The active representative removes zero-coefficient terms before degree use. -/
theorem angular_partial_zero {i j k : Nat} (hi : i < 4) (hj : j < 4)
    (hk : k < 4) (p : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p) :
    RatPolyCoeffEqv (angularDerivative i j (ratDerivative k p)) polyZero :=
  (angularDerivative_congr i j (activeDerivative_coeff k p).symm).trans
    (angularDerivative_independent_zero hi hj (activeDerivative k p)
      (activeDerivative_degree hk hp))

private theorem coordinate_left {blocks i j : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    HaarCarrierEqv blocks (angularDerivative i j (polyVar i))
      (polySmul (-1) (polyVar j)) := by
  have hz := ((ratDerivative_polyVar_ne j i (Ne.symm hij)).mul_left (polyVar i)).trans
    (RatPolyCoeffEqv.mul_zero_right _)
  exact HaarCarrierEqv.trans
    (HaarCarrierEqv.add (RatPolyCoeffEqv.haarCarrier hz)
      (HaarCarrierEqv.smul (-1) (derivativeFactor_self_carrier blocks j i hb hj hi)))
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.zero_add _))

private theorem coordinate_right {blocks i j : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    HaarCarrierEqv blocks (angularDerivative i j (polyVar j)) (polyVar i) := by
  have hz := ((((ratDerivative_polyVar_ne i j hij).mul_left (polyVar j)).trans
    (RatPolyCoeffEqv.mul_zero_right _)).smul (-1)).trans (RatPolyCoeffEqv.smul_zero _)
  exact HaarCarrierEqv.trans
    (HaarCarrierEqv.add (derivativeFactor_self_carrier blocks i j hb hi hj) (RatPolyCoeffEqv.haarCarrier hz))
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_zero _))

/-- The two-coordinate contribution, on the original padded Haar carrier. -/
theorem linear_second_angular {blocks i j : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hij : i ≠ j)
    (p : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p) :
    HaarCarrierEqv blocks (angularDerivative i j (angularDerivative i j p))
      (polySmul (-1) (polyAdd (polyMul (polyVar i) (ratDerivative i p))
        (polyMul (polyVar j) (ratDerivative j p)))) := by
  have hm (k l : Nat) (hl : l < 4) :
      RatPolyCoeffEqv (angularDerivative i j (polyMul (polyVar k) (ratDerivative l p)))
        (polyMul (angularDerivative i j (polyVar k)) (ratDerivative l p)) :=
    (angularDerivative_mul i j _ _).trans
      (((RatPolyCoeffEqv.refl _).add
        (((angular_partial_zero hi hj hl p hp).mul_left _).trans
          (RatPolyCoeffEqv.mul_zero_right _))).trans (RatPolyCoeffEqv.add_zero _))
  have he := (angularDerivative_add i j
      (polyMul (polyVar i) (ratDerivative j p))
      (polySmul (-1) (polyMul (polyVar j) (ratDerivative i p)))).trans
    ((hm i j hj).add ((angularDerivative_smul i j (-1) _).trans ((hm j i hi).smul (-1))))
  have hc := HaarCarrierEqv.add
    (HaarCarrierEqv.mul_right (ratDerivative j p) (coordinate_left hb hi hj hij))
    (HaarCarrierEqv.smul (-1)
      (HaarCarrierEqv.mul_right (ratDerivative i p) (coordinate_right hb hi hj hij)))
  exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier he) (HaarCarrierEqv.trans hc
    (RatPolyCoeffEqv.haarCarrier (((RatPolyCoeffEqv.polyMul_smul_left (-1) (polyVar j) (ratDerivative j p)).add
      (RatPolyCoeffEqv.refl _)).trans
      ((RatPolyCoeffEqv.smul_add (-1) _ _).symm.trans
        ((RatPolyCoeffEqv.add_comm _ _).smul (-1))))))

/-- The actual angular Casimir on head-linear polynomials is -3.
No eigenvalue assumption, numerical oracle or field bundle is supplied. -/
theorem linear_angularLaplacian {blocks : Nat} (hb : 0 < blocks)
    (p : RatPoly) (hp : HasQuaternionBlockDegree 0 1 p) :
    HaarCarrierEqv blocks (angularLaplacian p) (polySmul (-3) p) := by
  have h (i j : Nat) (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :=
    linear_second_angular hb hi hj hij p hp
  have hs := HaarCarrierEqv.add (h 0 1 (by decide) (by decide) (by decide))
    (HaarCarrierEqv.add (h 0 2 (by decide) (by decide) (by decide))
      (HaarCarrierEqv.add (h 0 3 (by decide) (by decide) (by decide))
        (HaarCarrierEqv.add (h 1 2 (by decide) (by decide) (by decide))
          (HaarCarrierEqv.add (h 1 3 (by decide) (by decide) (by decide))
            (h 2 3 (by decide) (by decide) (by decide))))))
  have hc : RatPolyCoeffEqv
      (six (fun i j => polySmul (-1) (polyAdd
        (polyMul (polyVar i) (ratDerivative i p)) (polyMul (polyVar j) (ratDerivative j p)))))
      (polySmul (-3) (headEuler p)) := by
    let t := fun k => polyMul (polyVar k) (ratDerivative k p)
    have hm (i j : Nat) := (cap_mul_left (-1) (polyAdd (t i) (t j))).symm
    refine ((hm 0 1).add ((hm 0 2).add ((hm 0 3).add
      ((hm 1 2).add ((hm 1 3).add (hm 2 3)))))).trans ?_
    exact (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.const (-1)) (.add (.var 0) (.var 1)))
        (.add (.mul (.const (-1)) (.add (.var 0) (.var 2)))
          (.add (.mul (.const (-1)) (.add (.var 0) (.var 3)))
            (.add (.mul (.const (-1)) (.add (.var 1) (.var 2)))
              (.add (.mul (.const (-1)) (.add (.var 1) (.var 3)))
                (.mul (.const (-1)) (.add (.var 2) (.var 3))))))))
      (.mul (.const (-3)) (.add (.var 0) (.add (.var 1) (.add (.var 2) (.var 3)))))
      (by decide) t).trans (cap_mul_left (-3) (headEuler p))
  have he : RatPolyCoeffEqv (headEuler p) p :=
    (headEuler_of_blockDegree 1 p hp).trans
      ((cap_mul_left 1 p).symm.trans (RatPolyCoeffEqv.one_mul p))
  exact HaarCarrierEqv.trans hs (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier hc)
    (HaarCarrierEqv.smul (-3) (RatPolyCoeffEqv.haarCarrier he)))

private theorem energy_pair (tail : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (r p : RatPoly) (hr : HasQuaternionBlockDegree 0 0 r) :
    quaternionHaar (tail+1) (polyMul r
      (polyMul (angularDerivative i j p) (angularDerivative i j p))) ≈
      -(quaternionHaar (tail+1) (polyMul (polyMul r p)
        (angularDerivative i j (angularDerivative i j p)))) := by
  let d := angularDerivative i j p
  let dd := angularDerivative i j d
  have hz := quaternionHaar_retained_background tail hi hj r p d hr
  have he : quaternionHaar (tail+1) (polyMul r (polyMul d d)) +
      quaternionHaar (tail+1) (polyMul (polyMul r p) dd) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (haar_of_coeff (RatPolyCoeffEqv.mul_assoc r p dd)))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_mul_add (tail+1) r _ _)) hz)
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
      (.add (.var 0) (.var 1)) (by decide)
      (fun n => if n = 0 then quaternionHaar (tail+1) (polyMul r (polyMul d d))
        else quaternionHaar (tail+1) (polyMul (polyMul r p) dd))) he

/-- Exact coercive identity with EVERY head-independent background retained.
All six rotations are essential; no analogous single-plane floor is claimed. -/
theorem retained_linear_energy (tail : Nat) (r p : RatPoly)
    (hr : HasQuaternionBlockDegree 0 0 r) (hp : HasQuaternionBlockDegree 0 1 p) :
    quaternionHaar (tail+1) (polyMul r (angularSquare p)) ≈
      3 * quaternionHaar (tail+1) (polyMul r (polyMul p p)) := by
  let m := fun i j => quaternionHaar (tail+1) (polyMul (polyMul r p)
    (angularDerivative i j (angularDerivative i j p)))
  have hpair := sixValue_congr
    (fun i j => quaternionHaar (tail+1) (polyMul r
      (polyMul (angularDerivative i j p) (angularDerivative i j p))))
    (fun i j => -(m i j)) (fun _ _ hi hj => energy_pair tail hi hj r p hr)
  have hscale : quaternionHaar (tail+1) (polyMul (polyMul r p) (polySmul (-3) p)) ≈
      (-3) * quaternionHaar (tail+1) (polyMul r (polyMul p p)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right (-3) _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (tail+1) (-3) _)
        (Q'.mul_eqv_congr_left (-3) _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc r p p))))
  have hm : sixValue m ≈ (-3) * quaternionHaar (tail+1) (polyMul r (polyMul p p)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_six (tail+1) (polyMul r p) _))
      (Q'.eqv_trans _ _ _ (linear_angularLaplacian (Nat.zero_lt_succ tail) p hp (polyMul r p)) hscale)
  exact Q'.eqv_trans _ _ _ (haar_six (tail+1) r _)
    (Q'.eqv_trans _ _ _ hpair (Q'.eqv_trans _ _ _ (sixValue_neg m)
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hm)
        (poly_identity_of_normal_eq (.neg (.mul (.const (-3)) (.var 0)))
          (.mul (.const 3) (.var 0)) (by decide)
          (fun _ => quaternionHaar (tail+1) (polyMul r (polyMul p p)))))))

end YMGap.Continuum.QuaternionHaarLinearAngularEnergy

#print axioms YMGap.Continuum.QuaternionHaarLinearAngularEnergy.angular_partial_zero
#print axioms YMGap.Continuum.QuaternionHaarLinearAngularEnergy.linear_second_angular
#print axioms YMGap.Continuum.QuaternionHaarLinearAngularEnergy.linear_angularLaplacian
#print axioms YMGap.Continuum.QuaternionHaarLinearAngularEnergy.haar_six
#print axioms YMGap.Continuum.QuaternionHaarLinearAngularEnergy.retained_linear_energy
#print axioms YMGap.Continuum.QuaternionHaarLinearAngularEnergy.sixValue_congr
#print axioms YMGap.Continuum.QuaternionHaarLinearAngularEnergy.sixValue_mono
#print axioms YMGap.Continuum.QuaternionHaarLinearAngularEnergy.sixValue_mul_left
#print axioms YMGap.Continuum.QuaternionHaarLinearAngularEnergy.sixValue_mul_right
