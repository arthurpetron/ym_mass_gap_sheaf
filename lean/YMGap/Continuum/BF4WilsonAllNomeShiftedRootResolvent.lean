/-
Constructed inverses of `(delta+b)I-bR` on the ORIGINAL Wilson completion,
for delta>0 and b>=0. The normalized geometric series gives the sharp cap
1/delta without a spectral theorem. Actual output representatives are data.
The adjacent-dyadic limit and generator equation are separate obligations;
this file supplies neither physical OS identification nor a scaling gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootResolvent

namespace YMGap.Continuum.BF4WilsonAllNomeShiftedRootResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics
open YMGap.Continuum.BF4WilsonAllNomeTimeAverages (smul_sub)

open BF4WilsonAllNomeRootResolvent
  (resolvent resolvent_right_normalized resolvent_left_normalized
   resolvent_smul resolvent_sub resolvent_norm_bound outputRepresentative
   outputRepresentative_pin)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "R" => root hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- The actual shifted root denominator. -/
def denominator (depth : Nat) (delta b : Q') (x : V) : V :=
  Sub (S (delta+b) x) (S b (R depth x))

/-- Explicit geometric-series ratio; both parameters remain visible. -/
def ratio (delta b : Q') (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) : Q' :=
  Q'.divPos b (delta+b) (Q'.pos_add_nonneg hd hb)

theorem ratio_nonnegative (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ ratio delta b hd hb :=
  Q'.mul_nonneg _ _ hb (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem below_sum (delta b : Q') (hd : (0 : Q') < delta) :
    b < delta+b := by
  show b.num * ((delta+b).den : Int) < (delta+b).num * (b.den : Int)
  rw [Q'.add_den_cast, Q'.add_num_cast]
  simp only [Int.add_mul, Int.mul_assoc]
  have hp : (0 : Int) < delta.num * ((b.den : Int) * (b.den : Int)) :=
    Int.mul_pos (Q'.num_pos_of_pos hd)
      (Int.mul_pos (by exact_mod_cast b.den_pos) (by exact_mod_cast b.den_pos))
  omega

theorem ratio_lt_one (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) :
    ratio delta b hd hb < (1 : Q') := by
  let hsum := Q'.pos_add_nonneg hd hb
  have h := Q'.mul_lt_mul_of_pos_left (Q'.recipPos_pos (delta+b) hsum)
    (below_sum delta b hd)
  have hc : Q'.eqv (Q'.recipPos (delta+b) hsum * (delta+b)) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  exact ContinuumClosureProgram.q'_lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) h)
    (Q'.le_of_eqv hc)

private theorem ratio_cancel (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) :
    Q'.eqv ((delta+b)*ratio delta b hd hb) b :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _)

private theorem gap_cancel (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) :
    Q'.eqv ((delta+b)*(1-ratio delta b hd hb)) delta := by
  have hp (d c r : Q') : Q'.eqv ((d+c)*(1-r)) ((d+c) + -((d+c)*r)) :=
    poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.const 1) (.neg (.var 2))))
      (.add (.add (.var 0) (.var 1))
        (.neg (.mul (.add (.var 0) (.var 1)) (.var 2))))
      (by decide) (fun | 0 => d | 1 => c | _ => r)
  have he := Q'.add_eqv_congr_left (delta+b) _ _
    (Q'.neg_eqv_congr _ _ (ratio_cancel delta b hd hb))
  exact Q'.eqv_trans _ _ _ (hp delta b _) (Q'.eqv_trans _ _ _ he
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => delta | _ => b)))

theorem denominator_normalized (depth : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (x : V) :
    denominator hw0 hw1 depth delta b x =
      S (delta+b) (BF4WilsonAllNomeRootResolvent.defect hw0 hw1 depth (ratio delta b hd hb) x) := by
  unfold denominator BF4WilsonAllNomeRootResolvent.defect
  rw [smul_sub, completedSmul_mul,
    completedSmul_congr hw0 hw1 (ratio_cancel delta b hd hb)]

theorem denominator_smul (depth : Nat) (delta b c : Q') (x : V) :
    denominator hw0 hw1 depth delta b (S c x) =
      S c (denominator hw0 hw1 depth delta b x) := by
  unfold denominator
  rw [root_smul, smul_sub]
  simp only [completedSmul_mul]
  rw [completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv (delta+b) c),
    completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv b c)]

/-- The inverse is a normalized contraction scaled by the explicit gap. -/
def inverse (depth : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (x : V) : V :=
  S (Q'.recipPos delta hd)
    (resolvent hw0 hw1 depth (ratio delta b hd hb)
      (ratio_nonnegative delta b hd hb) (ratio_lt_one delta b hd hb) x)

private theorem inverse_cancel (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) :
    Q'.eqv ((Q'.recipPos delta hd * (delta+b))*(1-ratio delta b hd hb)) 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (gap_cancel delta b hd hb))
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)))

theorem inverse_right (depth : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (x : V) :
    denominator hw0 hw1 depth delta b (inverse hw0 hw1 depth delta b hd hb x) = x := by
  unfold inverse
  rw [denominator_smul, denominator_normalized hw0 hw1 depth delta b hd hb,
    resolvent_right_normalized, completedSmul_mul,
    completedSmul_mul, completedSmul_congr hw0 hw1 (inverse_cancel delta b hd hb),
    completedSmul_one]

theorem inverse_left (depth : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (x : V) :
    inverse hw0 hw1 depth delta b hd hb (denominator hw0 hw1 depth delta b x) = x := by
  unfold inverse
  rw [denominator_normalized hw0 hw1 depth delta b hd hb, resolvent_smul,
    resolvent_left_normalized, completedSmul_mul, completedSmul_mul,
    completedSmul_congr hw0 hw1 (inverse_cancel delta b hd hb), completedSmul_one]

theorem inverse_norm_bound (depth : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (x : V) :
    RCle (B (inverse hw0 hw1 depth delta b hd hb x)
      (inverse hw0 hw1 depth delta b hd hb x))
      (RCscale (Q'.recipPos delta hd * Q'.recipPos delta hd) (B x x)) := by
  unfold inverse
  rw [completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
  exact RCscale_mono (Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.recipPos_pos _ _))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))) (resolvent_norm_bound hw0 hw1 _ _ _ _ x)

theorem inverse_smul (depth : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (c : Q') (x : V) :
    inverse hw0 hw1 depth delta b hd hb (S c x) =
      S c (inverse hw0 hw1 depth delta b hd hb x) := by
  unfold inverse
  rw [resolvent_smul, completedSmul_mul, completedSmul_mul,
    completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv _ c)]

theorem inverse_sub (depth : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (x y : V) :
    inverse hw0 hw1 depth delta b hd hb (Sub x y) =
      Sub (inverse hw0 hw1 depth delta b hd hb x)
        (inverse hw0 hw1 depth delta b hd hb y) := by
  unfold inverse
  rw [resolvent_sub, smul_sub]

theorem inverse_unique (depth : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (x y : V)
    (hy : denominator hw0 hw1 depth delta b y = x) :
    y = inverse hw0 hw1 depth delta b hd hb x := by
  rw [← hy, inverse_left]

theorem inverse_commutes (depth : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (L : V → V)
    (hL : ∀ x, denominator hw0 hw1 depth delta b (L x) =
      L (denominator hw0 hw1 depth delta b x)) (x : V) :
    inverse hw0 hw1 depth delta b hd hb (L x) =
      L (inverse hw0 hw1 depth delta b hd hb x) := by
  apply Eq.symm
  apply inverse_unique hw0 hw1 depth delta b hd hb
  rw [hL, inverse_right]

def inverseRepresentative (depth : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (X : (D).Cauchy) : (D).Cauchy :=
  (scalarContinuous hw0 hw1 (Q'.recipPos delta hd)).mapCauchy
    (outputRepresentative hw0 hw1 depth (ratio delta b hd hb)
      (ratio_nonnegative delta b hd hb) (ratio_lt_one delta b hd hb) X)

theorem inverseRepresentative_pin (depth : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (X : (D).Cauchy) :
    Class (inverseRepresentative hw0 hw1 depth delta b hd hb X) =
      inverse hw0 hw1 depth delta b hd hb (Class X) := by
  change S (Q'.recipPos delta hd) (Class (outputRepresentative hw0 hw1
    depth (ratio delta b hd hb) (ratio_nonnegative delta b hd hb)
      (ratio_lt_one delta b hd hb) X)) = _
  rw [outputRepresentative_pin]
  rfl

#print axioms ratio_nonnegative
#print axioms ratio_lt_one
#print axioms denominator_normalized
#print axioms denominator_smul
#print axioms inverse
#print axioms inverse_right
#print axioms inverse_left
#print axioms inverse_norm_bound
#print axioms inverse_smul
#print axioms inverse_sub
#print axioms inverse_unique
#print axioms inverse_commutes
#print axioms inverseRepresentative
#print axioms inverseRepresentative_pin

end YMGap.Continuum.BF4WilsonAllNomeShiftedRootResolvent
