/-
# The actual limiting Wilson-window squared seminorm

The carrier contains the original signed expressions with their lower-window
guards. Distance is the already constructed limiting reflected form of the
literal difference. The parallelogram identity and positivity give the
sqrt-free triangle bound. The proved LIMITING radical theorem gives null
replacement, without inferring finite-chart nullity.

This supplies every field of the existing explicit-modulus quotient/completion
interface. A fixed-window completion is not yet the intrinsic full observable
carrier, its time action or strict bound, or a continuum QFT.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws
import YMGap.Continuum.CRealSeminormCompletion
import YMGap.Continuum.BoundedRationalCauchyProduct

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

abbrev Carrier (base H : Nat) := {e : WindowExpression base // Within H e}

def sum {base H : Nat} (x y : Carrier base H) : Carrier base H :=
  ⟨.add x.val y.val, x.property, y.property⟩

def difference {base H : Nat} (x y : Carrier base H) : Carrier base H :=
  ⟨.add x.val (.smul (-1) y.val), x.property, y.property⟩

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base) (H : Nat)

def pairing (x y : Carrier base H) : CReal :=
  form hw0 hw1 hsmall hd hs hb H x.val y.val x.property y.property

def pairingCauchy (x y : Carrier base H) :
    QCauchy (pairing hw0 hw1 hsmall hd hs hb H x y).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _
    (spatialCauchy hw0 hw1 H (.mul (mirror H x.val) y.val)
      ⟨mirror_within H x.val, within_mono (by omega : H ≤ 2*H) y.val y.property⟩
      hsmall hd hs hb)

local notation "P" => pairing hw0 hw1 hsmall hd hs hb H

def distSq (x y : Carrier base H) : CReal := P (difference x y) (difference x y)

def distSqCauchy (x y : Carrier base H) :
    QCauchy (distSq hw0 hw1 hsmall hd hs hb H x y).approx :=
  pairingCauchy hw0 hw1 hsmall hd hs hb H (difference x y) (difference x y)

attribute [local irreducible] form spatialLimit

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add ha (neg_congr hc)

theorem pairing_difference_left (x y z : Carrier base H) :
    Equiv (P (difference x y) z) (sub (P x z) (P y z)) :=
  form_difference_left hw0 hw1 hsmall hd hs hb H x.val y.val z.val
    x.property y.property z.property

theorem pairing_difference_diagonal (x y : Carrier base H) :
    Equiv (P (difference x y) (difference x y))
      (sub (sub (P x x) (P x y)) (sub (P y x) (P y y))) :=
  form_difference_diagonal hw0 hw1 hsmall hd hs hb H x.val y.val x.property y.property

theorem distSq_refl (x : Carrier base H) :
    Equiv (distSq hw0 hw1 hsmall hd hs hb H x x) czero :=
  (pairing_difference_left hw0 hw1 hsmall hd hs hb H x x (difference x x)).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv ((P x (difference x x)).approx n)))

theorem distSq_symm (x y : Carrier base H) :
    Equiv (distSq hw0 hw1 hsmall hd hs hb H x y)
      (distSq hw0 hw1 hsmall hd hs hb H y x) := by
  refine (pairing_difference_diagonal hw0 hw1 hsmall hd hs hb H x y).trans
    (Equiv.trans ?_ (pairing_difference_diagonal hw0 hw1 hsmall hd hs hb H y x).symm)
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
    (.add (.add (.var 3) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 0)))))
    (by decide) (fun
      | 0 => (P x x).approx n
      | 1 => (P x y).approx n
      | 2 => (P y x).approx n
      | _ => (P y y).approx n)

theorem distSq_nonnegative (x y : Carrier base H) :
    leEv czero (distSq hw0 hw1 hsmall hd hs hb H x y) :=
  form_nonnegative hw0 hw1 hsmall hd hs hb H (difference x y).val (difference x y).property

/-- Parallelogram order uses positivity of the literal difference, not a
postulated triangle axiom or a replacement weighted-L2 form. -/
theorem pairing_sum_bound (x y : Carrier base H) :
    leEv (P (sum x y) (sum x y))
      (add (add (P x x) (P x x)) (add (P y y) (P y y))) := by
  have hsum := (form_add_left hw0 hw1 hsmall hd hs hb H x.val y.val (sum x y).val
    x.property y.property (sum x y).property).trans
      (Equiv_add
        (form_add_right hw0 hw1 hsmall hd hs hb H x.val x.val y.val x.property x.property y.property)
        (form_add_right hw0 hw1 hsmall hd hs hb H y.val x.val y.val y.property x.property y.property))
  have hpar : Equiv (add (P (sum x y) (sum x y)) (P (difference x y) (difference x y)))
      (add (add (P x x) (P x x)) (add (P y y) (P y y))) := by
    refine (Equiv_add hsum (pairing_difference_diagonal hw0 hw1 hsmall hd hs hb H x y)).trans ?_
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3))))))
      (.add (.add (.var 0) (.var 0)) (.add (.var 3) (.var 3))) (by decide)
      (fun
        | 0 => (P x x).approx n
        | 1 => (P x y).approx n
        | 2 => (P y x).approx n
        | _ => (P y y).approx n)
  have hzero : Equiv (add (P (sum x y) (sum x y)) czero) (P (sum x y) (sum x y)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => QPoly.q_add_zero_eqv _)
  exact leEv_trans (leEv_of_equiv hzero.symm)
    (leEv_trans (leEv_add (leEv_refl _) (distSq_nonnegative hw0 hw1 hsmall hd hs hb H x y))
      (leEv_of_equiv hpar))

private theorem difference_chain (x y z u : Carrier base H) :
    Equiv (P (sum (difference x y) (difference y z)) u) (P (difference x z) u) := by
  refine (form_add_left hw0 hw1 hsmall hd hs hb H (difference x y).val (difference y z).val
    u.val (difference x y).property (difference y z).property u.property).trans
      ((Equiv_add (pairing_difference_left hw0 hw1 hsmall hd hs hb H x y u)
        (pairing_difference_left hw0 hw1 hsmall hd hs hb H y z u)).trans
          (Equiv.trans ?_ (pairing_difference_left hw0 hw1 hsmall hd hs hb H x z u).symm))
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
    (.add (.var 0) (.neg (.var 2))) (by decide)
    (fun | 0 => (P x u).approx n | 1 => (P y u).approx n | _ => (P z u).approx n)

theorem distSq_triangle (x y z : Carrier base H) :
    leEv (distSq hw0 hw1 hsmall hd hs hb H x z)
      (add (add (distSq hw0 hw1 hsmall hd hs hb H x y) (distSq hw0 hw1 hsmall hd hs hb H x y))
        (add (distSq hw0 hw1 hsmall hd hs hb H y z) (distSq hw0 hw1 hsmall hd hs hb H y z))) := by
  let s := sum (difference x y) (difference y z)
  let d := difference x z
  have hpin : Equiv (P s s) (P d d) :=
    (difference_chain hw0 hw1 hsmall hd hs hb H x y z s).trans
      ((form_symm hw0 hw1 hsmall hd hs hb H d.val s.val d.property s.property).trans
        (difference_chain hw0 hw1 hsmall hd hs hb H x y z d))
  exact leEv_trans (leEv_of_equiv hpin.symm)
    (pairing_sum_bound hw0 hw1 hsmall hd hs hb H (difference x y) (difference y z))

theorem pairing_null_congr {x x' y y' : Carrier base H}
    (hx : Equiv (distSq hw0 hw1 hsmall hd hs hb H x x') czero)
    (hy : Equiv (distSq hw0 hw1 hsmall hd hs hb H y y') czero) :
    Equiv (P x y) (P x' y') :=
  form_null_congr hw0 hw1 hsmall hd hs hb H x.val x'.val y.val y'.val
    x.property x'.property y.property y'.property hx hy

theorem distSq_null_congr {x x' y y' : Carrier base H}
    (hx : Equiv (distSq hw0 hw1 hsmall hd hs hb H x x') czero)
    (hy : Equiv (distSq hw0 hw1 hsmall hd hs hb H y y') czero) :
    Equiv (distSq hw0 hw1 hsmall hd hs hb H x y)
      (distSq hw0 hw1 hsmall hd hs hb H x' y') :=
  (pairing_difference_diagonal hw0 hw1 hsmall hd hs hb H x y).trans
    ((sub_congr
      (sub_congr (pairing_null_congr hw0 hw1 hsmall hd hs hb H hx hx)
        (pairing_null_congr hw0 hw1 hsmall hd hs hb H hx hy))
      (sub_congr (pairing_null_congr hw0 hw1 hsmall hd hs hb H hy hx)
        (pairing_null_congr hw0 hw1 hsmall hd hs hb H hy hy))).trans
      (pairing_difference_diagonal hw0 hw1 hsmall hd hs hb H x' y').symm)

/-- All fields are proved for the actual Wilson limit; no new analytic input. -/
def seminorm : SquaredSeminorm where
  Carrier := Carrier base H
  distSq := distSq hw0 hw1 hsmall hd hs hb H
  distSq_refl := distSq_refl hw0 hw1 hsmall hd hs hb H
  distSq_symm := distSq_symm hw0 hw1 hsmall hd hs hb H
  distSq_nonneg := distSq_nonnegative hw0 hw1 hsmall hd hs hb H
  distSq_triangle := distSq_triangle hw0 hw1 hsmall hd hs hb H
  null_congr := distSq_null_congr hw0 hw1 hsmall hd hs hb H

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.Carrier
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.pairingCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSqCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.pairing_difference_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.pairing_difference_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq_refl
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.pairing_sum_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq_triangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.pairing_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm.seminorm
