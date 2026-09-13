/-
# Original quaternion-Haar moment products as bounded two-slot forms

Both slots use the existing original Haar integral. Additivity and interval
bounds are proved from polynomial certificates, retaining shared variables
within each moment. The connected form keeps all four moments and both
partition factors; this construction is not a change of probability law.
-/

import YMGap.Continuum.PolynomialBiadditiveMobius

namespace YMGap.Continuum.QuaternionHaarBiadditive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.PolynomialBiadditive
open YMGap.Continuum.PolynomialBiadditiveMobius
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_insert_add (blocks : Nat) (p a b : RatPoly) :
    quaternionHaar blocks (polyMul p (polyAdd a b)) ≈
      quaternionHaar blocks (polyMul p a) + quaternionHaar blocks (polyMul p b) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right p a b)) (quaternionHaar_append _ _ _)

def haarProduct (blocks : Nat) (p q : RatPoly) : Biadditive where
  value := fun a b => quaternionHaar blocks (polyMul p a) * quaternionHaar blocks (polyMul q b)
  congr := fun ha hb => qmul (haar_of_coeff ((RatPolyCoeffEqv.refl p).mul ha))
    (haar_of_coeff ((RatPolyCoeffEqv.refl q).mul hb))
  add_left := fun a b c => Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (quaternionHaar blocks (polyMul q c)) (haar_insert_add blocks p a b)) (Q'.add_mul_eqv _ _ _)
  add_right := fun a b c => Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (quaternionHaar blocks (polyMul p a)) _ _ (haar_insert_add blocks q b c)) (Q'.mul_add_eqv _ _ _)

theorem abs_product_bound {u v a b : Q'} (hu : Q'.abs u ≤ a) (hv : Q'.abs v ≤ b) :
    Q'.abs (u*v) ≤ a*b :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le u v)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hu (Q'.abs_nonneg v))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hv (Q'.le_trans' _ _ _ (Q'.abs_nonneg u) hu)))

theorem haarProduct_bound {blocks : Nat} {p q : RatPoly} {c d : Q'}
    (P : Interval blocks p c) (Q : Interval blocks q d) : IntervalBound (haarProduct blocks p q) blocks (c*d) := by
  intro a b x y A B
  exact Q'.le_trans' _ _ _ (abs_product_bound (P.mul A).haar_bound (Q.mul B).haar_bound)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3)) (by decide)
      (fun i => if i = 0 then c else if i = 1 then d else if i = 2 then x else y)))

theorem bound_add {B D : Biadditive} {blocks : Nat} {c d : Q'}
    (hB : IntervalBound B blocks c) (hD : IntervalBound D blocks d) : IntervalBound (B.add D) blocks (c+d) := by
  intro p q a b P Q
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) (Q'.add_le_add (hB P Q) (hD P Q)))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.var 2)) (.var 3)) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.mul (.add (.var 0) (.var 1)) (.var 2)) (.var 3)) (by decide)
      (fun i => if i = 0 then c else if i = 1 then d else if i = 2 then a else b)))

theorem bound_neg {B : Biadditive} {blocks : Nat} {c : Q'}
    (hB : IntervalBound B blocks c) : IntervalBound B.neg blocks c :=
  fun P Q => Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _)) (hB P Q)

theorem bound_change {B : Biadditive} {blocks : Nat} {c d : Q'}
    (h : c ≈ d) (hB : IntervalBound B blocks c) : IntervalBound B blocks d :=
  fun P Q => Q'.le_trans' _ _ _ (hB P Q)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)))

def connected (blocks : Nat) (p q : RatPoly) : Biadditive :=
  (haarProduct blocks (polyMul p q) polyOne).add (haarProduct blocks p q).neg

theorem connected_diagonal (blocks : Nat) (p q a : RatPoly) :
    (connected blocks p q).value a a ≈
      quaternionHaar blocks (polyMul (polyMul p q) a) * quaternionHaar blocks a +
        -(quaternionHaar blocks (polyMul p a) * quaternionHaar blocks (polyMul q a)) :=
  Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul a))) (Q'.eqv_refl _)

theorem connected_bound {blocks : Nat} {p q : RatPoly} {c d : Q'}
    (P : Interval blocks p c) (Q : Interval blocks q d) : IntervalBound (connected blocks p q) blocks (c*d+c*d) :=
  bound_change (Q'.add_eqv_congr' (Q'.mul_one_eqv (c*d)) (Q'.eqv_refl _))
    (bound_add (haarProduct_bound (P.mul Q) (Interval.one blocks)) (bound_neg (haarProduct_bound P Q)))

end YMGap.Continuum.QuaternionHaarBiadditive

#print axioms YMGap.Continuum.QuaternionHaarBiadditive.haarProduct
#print axioms YMGap.Continuum.QuaternionHaarBiadditive.abs_product_bound
#print axioms YMGap.Continuum.QuaternionHaarBiadditive.haarProduct_bound
#print axioms YMGap.Continuum.QuaternionHaarBiadditive.bound_add
#print axioms YMGap.Continuum.QuaternionHaarBiadditive.bound_neg
#print axioms YMGap.Continuum.QuaternionHaarBiadditive.bound_change
#print axioms YMGap.Continuum.QuaternionHaarBiadditive.connected
#print axioms YMGap.Continuum.QuaternionHaarBiadditive.connected_diagonal
#print axioms YMGap.Continuum.QuaternionHaarBiadditive.connected_bound
