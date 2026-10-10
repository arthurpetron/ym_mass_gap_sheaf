/-
Choice-free extension of supplied uniformly continuous dense quaternion data.
The image of a supplied Cauchy row is computed using shrinking rational
sampling tolerances and retains its explicit inner regularity. Equivalent
source rows yield equivalent output reals, so the map descends to the SAME
Point quotient with values in RC, not chosen CReal representatives.
No boundedness, continuous Haar, functional laws or physical gap is assumed
or constructed by this extension alone.
-/

import YMGap.Constructive.CRealStableSampling
import YMGap.RepTheory.RationalQuaternionCauchyGroup

namespace YMGap.Continuum.QuaternionDenseCRealPointExtension

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup

local infix:50 " ≈ " => Q'.eqv

variable (F : UnitNorm → CReal) (R : ∀ q, InnerRegularity (F q))
variable (radius : Q' → Q')
variable (radius_positive : ∀ e, (0 : Q') < e → (0 : Q') < radius e)
variable (hmod : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ radius e →
    leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)

private def halfTolerance (e : Q') : Q' := HalfPow.half * e
private def quarterTolerance (e : Q') : Q' := HalfPow.half * halfTolerance e

private theorem half_positive (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < halfTolerance e := Q'.mul_pos (by decide) he

private theorem quarter_positive (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < quarterTolerance e :=
  Q'.mul_pos (by decide) (half_positive e he)

private theorem budget_pin (e : Q') :
    (halfTolerance e + quarterTolerance e) + quarterTolerance e ≈ e := by
  have hring :
      (HalfPow.half*e + HalfPow.half*(HalfPow.half*e)) +
          HalfPow.half*(HalfPow.half*e) ≈
        ((HalfPow.half + HalfPow.half*HalfPow.half) +
          HalfPow.half*HalfPow.half)*e :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1))
        (.mul (.var 0) (.mul (.var 0) (.var 1))))
        (.mul (.var 0) (.mul (.var 0) (.var 1))))
      (.mul (.add (.add (.var 0) (.mul (.var 0) (.var 0)))
        (.mul (.var 0) (.var 0))) (.var 1))
      (by decide) (fun | 0 => HalfPow.half | _ => e)
  exact Q'.eqv_trans _ _ _ hring
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ e
        (by decide : ((HalfPow.half + HalfPow.half*HalfPow.half) +
          HalfPow.half*HalfPow.half) ≈ (1 : Q')))
      (Q'.one_mul_eqv e))

private theorem constant_le_reflect {a b : Q'}
    (h : leEv (ofQ' a) (ofQ' b)) : a ≤ b := by
  apply Q'.le_of_le_add_mul_invSucc a b 1
  intro N
  obtain ⟨K, hK⟩ := h (Q'.invSucc N) (Q'.invSucc_pos N)
  exact Q'.le_trans' _ _ _ (hK K (Nat.le_refl _))
    (Q'.ge_of_eqv
      (Q'.add_eqv_congr_left b _ _ (Q'.one_mul_eqv (Q'.invSucc N))))

private theorem sample_tail (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : (quarterTolerance e).den ≤ n) :
    Q'.invSucc n ≤ quarterTolerance e :=
  Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
    (HalfPow.invSucc_den_le _ (quarter_positive e he))

private theorem paid_budget (e a b : Q')
    (ha : a ≤ quarterTolerance e) (hb : b ≤ quarterTolerance e) :
    (halfTolerance e + a) + b ≤ e :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add (Q'.add_le_add_left _ _ _ ha) hb)
    (Q'.le_of_eqv (budget_pin e))

private theorem bounds_of_abs {a b e : Q'} (h : Q'.abs (a + -b) ≤ e) :
    a ≤ b + e ∧ b ≤ a + e :=
  ⟨ExpNeg.le_add_of_abs_sub_le h,
    ExpNeg.le_add_of_abs_sub_le
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) h)⟩

/-- Actual sampled image of the supplied source row. -/
def rowImageApprox (X : CauchyPoint) (n : Nat) : Q' :=
  sample (F (X.seq n)) (R (X.seq n)) (Q'.invSucc n)

/-- A computed modulus; no modulus is extracted from a propositional bound. -/
def rowImageRate (X : CauchyPoint) (e : Q') : Nat :=
  max (X.modulus (radius (halfTolerance e))) (quarterTolerance e).den

include radius_positive hmod in
/-- Continuity and the two separately shrinking sample errors pay the
regularity of the ACTUAL output row. -/
theorem rowImage_regular (X : CauchyPoint) (e : Q') (he : (0 : Q') < e)
    (m n : Nat) (hm : rowImageRate radius X e ≤ m)
    (hn : rowImageRate radius X e ≤ n) :
    rowImageApprox F R X m ≤ rowImageApprox F R X n + e ∧
      rowImageApprox F R X n ≤ rowImageApprox F R X m + e := by
  have hsource : distSq (X.seq m).val (X.seq n).val ≤
      radius (halfTolerance e) :=
    constant_le_reflect (X.isCauchy _
      (radius_positive _ (half_positive e he)) m n
      (Nat.le_trans (Nat.le_max_left _ _) hm)
      (Nat.le_trans (Nat.le_max_left _ _) hn))
  have hsample := sample_difference_le_asymmetric
    (F (X.seq m)) (F (X.seq n)) (R (X.seq m)) (R (X.seq n))
    (halfTolerance e) (Q'.invSucc m) (Q'.invSucc n)
    (hmod _ (half_positive e he) _ _ hsource)
    (Q'.invSucc_pos m) (Q'.invSucc_pos n)
  exact bounds_of_abs (Q'.le_trans' _ _ _ hsample
    (paid_budget e _ _
      (sample_tail e he m (Nat.le_trans (Nat.le_max_right _ _) hm))
      (sample_tail e he n (Nat.le_trans (Nat.le_max_right _ _) hn))))

/-- A real constructed from the supplied Cauchy row, not from a chosen Point
representative. Its approximation is literally rowImageApprox. -/
def rowImage (X : CauchyPoint) : CReal where
  approx := rowImageApprox F R X
  cauchy := fun e he => ⟨rowImageRate radius X e,
    rowImage_regular F R radius radius_positive hmod X e he⟩

/-- The output row retains its explicit computable inner rate as data. -/
def rowImageInnerRegularity (X : CauchyPoint) :
    InnerRegularity (rowImage F R radius radius_positive hmod X) where
  rate := rowImageRate radius X
  regular := rowImage_regular F R radius radius_positive hmod X

include radius_positive hmod in
/-- Equivalent source rows have equivalent output VALUES. Close's modulus is
used only inside this proof, not extracted into the quotient map. -/
theorem rowImage_congr {X Y : CauchyPoint}
    (h : chordSeminorm.CompletionRel X Y) :
    Equiv (rowImage F R radius radius_positive hmod X)
      (rowImage F R radius radius_positive hmod Y) := by
  obtain ⟨h⟩ := h
  intro e he
  refine ⟨max (h.modulus (radius (halfTolerance e)))
    (quarterTolerance e).den, fun n hn => ?_⟩
  have hsource : distSq (X.seq n).val (Y.seq n).val ≤
      radius (halfTolerance e) :=
    constant_le_reflect (h.close _ (radius_positive _ (half_positive e he)) n
      (Nat.le_trans (Nat.le_max_left _ _) hn))
  have hsample := sample_difference_le_asymmetric
    (F (X.seq n)) (F (Y.seq n)) (R (X.seq n)) (R (Y.seq n))
    (halfTolerance e) (Q'.invSucc n) (Q'.invSucc n)
    (hmod _ (half_positive e he) _ _ hsource)
    (Q'.invSucc_pos n) (Q'.invSucc_pos n)
  have htail := sample_tail e he n (Nat.le_trans (Nat.le_max_right _ _) hn)
  exact bounds_of_abs (Q'.le_trans' _ _ _ hsample (paid_budget e _ _ htail htail))

include radius_positive hmod in
/-- Constants recover the supplied dense values even when the varying
sampling rate is not bounded by the outer row index. -/
theorem rowImage_constant (q : UnitNorm) :
    Equiv (rowImage F R radius radius_positive hmod (chordSeminorm.constant q))
      (F q) := by
  intro e he
  let eta := halfTolerance e
  have heta : (0 : Q') < eta := half_positive e he
  refine ⟨max ((R q).rate eta) eta.den, fun n hn => ?_⟩
  let j := max ((R q).rate (Q'.invSucc n)) n
  have hjn : n ≤ j := Nat.le_max_right _ _
  have hfixed : (R q).rate eta ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hs := sample_error_bound (F q) (R q) (Q'.invSucc n)
    (Q'.invSucc_pos n) j (Nat.le_max_left _ _)
  obtain ⟨h1, h2⟩ := (R q).regular eta heta j n
    (Nat.le_trans hfixed hjn) hfixed
  have hr : Q'.abs ((F q).approx j + -((F q).approx n)) ≤ eta :=
    abs_sub_le_of_bounds h1 h2
  have hpin : (sample (F q) (R q) (Q'.invSucc n) + -((F q).approx n)) ≈
      (sample (F q) (R q) (Q'.invSucc n) + -((F q).approx j)) +
        ((F q).approx j + -((F q).approx n)) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 1)))
      (.add (.add (.var 0) (.neg (.var 2)))
        (.add (.var 2) (.neg (.var 1))))
      (by decide)
      (fun | 0 => sample (F q) (R q) (Q'.invSucc n)
           | 1 => (F q).approx n
           | _ => (F q).approx j)
  have htail : Q'.invSucc n ≤ eta :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_right _ _) hn))
      (HalfPow.invSucc_den_le eta heta)
  have hsum : Q'.abs (sample (F q) (R q) (Q'.invSucc n) + -((F q).approx n)) ≤ e :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
        (Q'.le_trans' _ _ _ (Q'.add_le_add hs hr)
          (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ eta htail)
            (Q'.le_of_eqv (ExpNeg.two_halves e)))))
  exact bounds_of_abs hsum

/-- A choice-free map on the existing Point quotient with genuine real
quotient values. No arbitrary CReal representative is selected. -/
def pointExtension : Point → RC :=
  Quotient.lift
    (fun X => Quotient.mk crealSetoid (rowImage F R radius radius_positive hmod X))
    (fun _ _ h => Quotient.sound (rowImage_congr F R radius radius_positive hmod h))

theorem pointExtension_mk (X : CauchyPoint) :
    pointExtension F R radius radius_positive hmod
      (Quotient.mk chordSeminorm.completionSetoid X) =
        Quotient.mk crealSetoid (rowImage F R radius radius_positive hmod X) := rfl

theorem pointExtension_embed (q : UnitNorm) :
    pointExtension F R radius radius_positive hmod (embed q) =
      Quotient.mk crealSetoid (F q) :=
  Quotient.sound (rowImage_constant F R radius radius_positive hmod q)

#print axioms rowImageApprox
#print axioms rowImageRate
#print axioms rowImage_regular
#print axioms rowImage
#print axioms rowImageInnerRegularity
#print axioms rowImage_congr
#print axioms rowImage_constant
#print axioms pointExtension
#print axioms pointExtension_mk
#print axioms pointExtension_embed

end YMGap.Continuum.QuaternionDenseCRealPointExtension
