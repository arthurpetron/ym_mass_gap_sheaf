/-
# Actual linear time combinations on the all-nome joint carrier

Rational bilinearity passes through the existing representative pairing
limits. Literal physical time preserves the new modulus-bearing completed
operations on this SAME JointCompletion. Finite signed time combinations
are therefore actual states, and their pairings are exactly the double
sum of the original time correlators, with all cross terms retained.

The unit complement is closed under these combinations. Its existing
strict two-step bound still applies; no nonzero filtered state, near-one
Rayleigh quotient, metric completeness, real scalar extension, or continuum
scaling estimate is inferred. Nome and spatial width remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse
import YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (addSpan smulSpan PairingEq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
  (advanceSpan_append advanceSpan_scale)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
  (completedTime_preserves_orthogonal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap (completed_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse (completedInner_time_sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "A" => completedAdd hw0 hw1 width
local notation "S" => completedSmul hw0 hw1 width
local notation "Z" => completedZero hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width

theorem representativeInner_add_left (X Y Z' : (D).Cauchy) :
    Equiv (representativeInner hw0 hw1 width ((addition hw0 hw1 width).mapCauchy X Y) Z')
      (add (representativeInner hw0 hw1 width X Z') (representativeInner hw0 hw1 width Y Z')) :=
  Equiv_of_limit_of_equal
    (fun n => jointPairing_add_left hw0 hw1 width (X.seq n) (Y.seq n) (Z'.seq n))
    (pairSequence_converges hw0 hw1 width ((addition hw0 hw1 width).mapCauchy X Y) Z')
    (TrigAddCReal.convergesTo_add (pairSequence_converges hw0 hw1 width X Z')
      (pairSequence_converges hw0 hw1 width Y Z'))

theorem representativeInner_smul_left (c : Q') (X Y : (D).Cauchy) :
    Equiv (representativeInner hw0 hw1 width ((scalarContinuous hw0 hw1 width c).mapCauchy X) Y)
      (mul (ofQ' c) (representativeInner hw0 hw1 width X Y)) :=
  Equiv_of_limit_of_equal
    (fun n => jointPairing_smul_left hw0 hw1 width c (X.seq n) (Y.seq n))
    (pairSequence_converges hw0 hw1 width ((scalarContinuous hw0 hw1 width c).mapCauchy X) Y)
    (convergesTo_const_mul (ofQ' c) (pairSequence_converges hw0 hw1 width X Y))

theorem completedInner_add_left (x y z : V) : B (A x y) z = RCadd (B x z) (B y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact fun X Y Z' => Quotient.sound (representativeInner_add_left hw0 hw1 width X Y Z')

theorem completedInner_add_right (x y z : V) : B x (A y z) = RCadd (B x y) (B x z) := by
  rw [completedInner_symm hw0 hw1 width x, completedInner_add_left,
    completedInner_symm hw0 hw1 width y x, completedInner_symm hw0 hw1 width z x]

theorem completedInner_smul_left (c : Q') (x y : V) : B (S c x) y = RCscale c (B x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_smul_left hw0 hw1 width c X Y)

theorem completedInner_smul_right (c : Q') (x y : V) : B x (S c y) = RCscale c (B x y) := by
  rw [completedInner_symm hw0 hw1 width x, completedInner_smul_left,
    completedInner_symm hw0 hw1 width y x]

theorem completedInner_zero_left (x : V) : B Z x = RCzero := by
  rw [← completedSmul_zero hw0 hw1 width x, completedInner_smul_left]
  refine Quotient.inductionOn (B x x) ?_
  exact fun A' => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv (A'.approx n)))

theorem completedInner_zero_right (x : V) : B x Z = RCzero := by
  rw [completedInner_symm, completedInner_zero_left]

private theorem physicalTime_addSpan (n : Nat) (x y : PhysicalSpan width) :
    physicalTime n (addSpan x y) = addSpan (physicalTime n x) (physicalTime n y) :=
  Subtype.ext (advanceSpan_append n x.val y.val)

private theorem physicalTime_smulSpan (n : Nat) (c : Q') (x : PhysicalSpan width) :
    physicalTime n (smulSpan c x) = smulSpan c (physicalTime n x) :=
  Subtype.ext (advanceSpan_scale n c x.val)

/-- Addition of vectors, distinct from addition of time indices. -/
theorem completedTime_additive (n : Nat) (x y : V) : T n (A x y) = A (T n x) (T n y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply completion_eq_of_pointwise hw0 hw1 width
  intro k stage
  change PairingEq hw0 hw1 width stage (physicalTime n (addSpan (X.seq k) (Y.seq k)))
    (addSpan (physicalTime n (X.seq k)) (physicalTime n (Y.seq k)))
  rw [physicalTime_addSpan]
  exact fun _ => Equiv.refl _

theorem completedTime_smul (n : Nat) (c : Q') (x : V) : T n (S c x) = S c (T n x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completion_eq_of_pointwise hw0 hw1 width
  intro k stage
  change PairingEq hw0 hw1 width stage (physicalTime n (smulSpan c (X.seq k)))
    (smulSpan c (physicalTime n (X.seq k)))
  rw [physicalTime_smulSpan]
  exact fun _ => Equiv.refl _

theorem completedTime_zero_element (n : Nat) : T n Z = Z := by
  unfold completedZero
  rw [jointCompletedTime_embedSpan]
  rfl

theorem completedTime_sub (n : Nat) (x y : V) :
    T n (completedSub hw0 hw1 width x y) = completedSub hw0 hw1 width (T n x) (T n y) := by
  unfold completedSub completedNeg
  rw [completedTime_additive, completedTime_smul]

/-- A finite signed sum of actual time-translated states, with the Cauchy
moduli supplied by the constructed operations. Repeated lags are allowed. -/
def orbitSum (x : V) : List (Q' × Nat) → V
  | [] => Z
  | (c,n)::cs => A (S c (T n x)) (orbitSum x cs)

/-- Scalar evaluation of the same finite rational coefficient list. -/
def responseSum : List (Q' × Nat) → (Nat → RC) → RC
  | [], _ => RCzero
  | (c,n)::cs, f => RCadd (RCscale c (f n)) (responseSum cs f)

theorem orbitSum_inner_left (x y : V) (cs : List (Q' × Nat)) :
    B (orbitSum hw0 hw1 width x cs) y = responseSum cs (fun n => B (T n x) y) := by
  induction cs with
  | nil => exact completedInner_zero_left hw0 hw1 width y
  | cons a cs ih =>
      rcases a with ⟨c,n⟩
      simp only [orbitSum, responseSum, completedInner_add_left, completedInner_smul_left, ih]

theorem orbitSum_inner_right (x y : V) (cs : List (Q' × Nat)) :
    B x (orbitSum hw0 hw1 width y cs) = responseSum cs (fun n => B x (T n y)) := by
  induction cs with
  | nil => exact completedInner_zero_right hw0 hw1 width x
  | cons a cs ih =>
      rcases a with ⟨c,n⟩
      simp only [orbitSum, responseSum, completedInner_add_right, completedInner_smul_right, ih]

/-- All signed cross terms remain in the original same-object moments. -/
theorem orbitSum_pairing (x y : V) (cs ds : List (Q' × Nat)) :
    B (orbitSum hw0 hw1 width x cs) (orbitSum hw0 hw1 width y ds) =
      responseSum cs (fun m => responseSum ds (fun n => B x (T (m+n) y))) := by
  rw [orbitSum_inner_left]
  apply congrArg (responseSum cs)
  funext m
  rw [orbitSum_inner_right]
  exact congrArg (responseSum ds) (funext (fun n => completedInner_time_sum hw0 hw1 width m n x y))

theorem orbitSum_time (x : V) (cs : List (Q' × Nat)) (m : Nat) :
    T m (orbitSum hw0 hw1 width x cs) = orbitSum hw0 hw1 width (T m x) cs := by
  induction cs with
  | nil => exact completedTime_zero_element hw0 hw1 width m
  | cons a cs ih =>
      rcases a with ⟨c,n⟩
      simp only [orbitSum, completedTime_additive, completedTime_smul, ih]
      rw [← jointCompletedTime_add, ← jointCompletedTime_add, Nat.add_comm m n]

theorem orbitSum_orthogonal (x : V) (hx : B x U = RCzero) (cs : List (Q' × Nat)) :
    B (orbitSum hw0 hw1 width x cs) U = RCzero := by
  induction cs with
  | nil => exact completedInner_zero_left hw0 hw1 width U
  | cons a cs ih =>
      rcases a with ⟨c,n⟩
      rw [orbitSum, completedInner_add_left, completedInner_smul_left,
        completedTime_preserves_orthogonal hw0 hw1 width n x hx, RCscale_RCzero, ih]
      rfl

/-- Finite time filtering cannot bypass the existing strict bound on this
same sector. This theorem does not assert that the filtered vector is nonzero. -/
theorem orbitSum_twoStep_form_gap (x : V) (hx : B x U = RCzero) (cs : List (Q' × Nat)) :
    let y := orbitSum hw0 hw1 width x cs
    RCle (B y (T 2 y)) (RCscale (twoStepRate hw0 hw1 width) (B y y)) :=
  completed_twoStep_form_gap hw0 hw1 width (orbitSum hw0 hw1 width x cs)
    (orbitSum_orthogonal hw0 hw1 width x hx cs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.representativeInner_add_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.representativeInner_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.completedInner_add_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.completedInner_add_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.completedInner_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.completedInner_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.completedInner_zero_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.completedInner_zero_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.completedTime_additive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.completedTime_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.completedTime_zero_element
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.completedTime_sub
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.orbitSum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.responseSum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.orbitSum_inner_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.orbitSum_inner_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.orbitSum_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.orbitSum_time
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.orbitSum_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime.orbitSum_twoStep_form_gap
