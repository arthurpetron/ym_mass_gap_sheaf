/-
# RatPoly realization of every truncated anchor-face SOS feature

The finite weighted SOS certificate for the adjacent-even anchor face stores
its features as functions on rational unit quaternions.  This leaf realizes
each such function by explicit finite-support rational polynomial data.

The fixed coordinate vector is

    [x, y1, y2, y3],

extended by zero outside its four active entries.  The sphere proof carried by
the input is not needed for polynomial realization; it enters only in the
separate identity identifying the odd quaternion squares with the shifted
character.

The construction is fully computational:

* a Horner recursion embeds every univariate `QPoly.Poly` into `RatPoly` at a
  selected coordinate;
* the existing all-order second-kind polynomial `chebPoly` is reused;
* first-kind and odd half-angle polynomials are built by the proved Chebyshev
  identities;
* an indexed `RatPolyFeatures` witness is closed under constant features,
  nonnegative scaling, and offset-packed direct sums;
* a final finite polynomial sum realizes the complete weighted SOS value.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
All finite objects are explicit `List`/`Nat` recursions.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceSOS
import YMGap.Continuum.SU2QuaternionWilsonWeightSOS
import YMGap.Continuum.SU2ClassPolynomialAlgebra

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceRatPolyRealization

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebU
open YMGap.Continuum.ChebOddFaceSOS
open YMGap.Continuum.FiniteWeightedRationalSOSProduct
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceReserve
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceWeightDecomposition
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceSOS

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The fixed four-coordinate environment -/

/-- The exact finite coordinate vector underlying an anchor quaternion. -/
def anchorCoordinateList (input : AnchorQuaternionInput) : List Q' :=
  [input.x, input.y1, input.y2, input.y3]

/-- Evaluate raw `RatPoly` variables on the four anchor coordinates and send
every coordinate beyond index three to zero. -/
def anchorEnvironment (input : AnchorQuaternionInput) (coordinate : Nat) : Q' :=
  (anchorCoordinateList input).getD coordinate 0

@[simp] theorem anchorCoordinateList_length (input : AnchorQuaternionInput) :
    (anchorCoordinateList input).length = 4 := rfl

@[simp] theorem anchorEnvironment_x (input : AnchorQuaternionInput) :
    anchorEnvironment input 0 = input.x := rfl

@[simp] theorem anchorEnvironment_y1 (input : AnchorQuaternionInput) :
    anchorEnvironment input 1 = input.y1 := rfl

@[simp] theorem anchorEnvironment_y2 (input : AnchorQuaternionInput) :
    anchorEnvironment input 2 = input.y2 := rfl

@[simp] theorem anchorEnvironment_y3 (input : AnchorQuaternionInput) :
    anchorEnvironment input 3 = input.y3 := rfl

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-! ## 2. Constructive univariate-to-multivariate polynomial lift -/

/-- Horner embedding of a univariate `QPoly` into `RatPoly`, using the chosen
raw coordinate as its variable. -/
def qPolyToRatPolyAt (coordinate : Nat) : QPoly.Poly → RatPoly
  | [] => polyZero
  | coefficient :: tail =>
      polyAdd (polySmul coefficient polyOne)
        (polyMul (polyVar coordinate) (qPolyToRatPolyAt coordinate tail))

/-- The Horner embedding evaluates exactly at the selected coordinate. -/
theorem eval_qPolyToRatPolyAt (rho : Nat → Q') (coordinate : Nat) :
    ∀ polynomial : QPoly.Poly,
      evalRatPoly rho (qPolyToRatPolyAt coordinate polynomial) ≈
        QPoly.eval polynomial (rho coordinate)
  | [] => Q'.eqv_refl _
  | coefficient :: tail => by
      calc
        evalRatPoly rho
            (qPolyToRatPolyAt coordinate (coefficient :: tail))
            ≈ evalRatPoly rho (polySmul coefficient polyOne) +
                evalRatPoly rho
                  (polyMul (polyVar coordinate)
                    (qPolyToRatPolyAt coordinate tail)) :=
              evalRatPoly_add rho _ _
        _ ≈ (coefficient * evalRatPoly rho polyOne) +
              (evalRatPoly rho (polyVar coordinate) *
                evalRatPoly rho (qPolyToRatPolyAt coordinate tail)) :=
            q_add_congr
              (evalRatPoly_smul rho coefficient polyOne)
              (evalRatPoly_mul rho (polyVar coordinate)
                (qPolyToRatPolyAt coordinate tail))
        _ ≈ (coefficient * (1 : Q')) +
              ((rho coordinate) * QPoly.eval tail (rho coordinate)) :=
            q_add_congr
              (Q'.mul_eqv_congr_left coefficient _ _
                (evalRatPoly_one rho))
              (q_mul_congr (evalRatPoly_var rho coordinate)
                (eval_qPolyToRatPolyAt rho coordinate tail))
        _ ≈ coefficient +
              (rho coordinate) * QPoly.eval tail (rho coordinate) :=
            q_add_congr (Q'.mul_one_eqv coefficient) (Q'.eqv_refl _)

/-! ## 3. First-kind and odd half-angle Chebyshev polynomials -/

/-- The ordinary class coordinate as a one-variable coefficient polynomial. -/
def classXQPoly : QPoly.Poly := [0, 1]

theorem eval_classXQPoly (x : Q') :
    QPoly.eval classXQPoly x ≈ x := by
  change ((0 : Q') + x * ((1 : Q') + x * (0 : Q'))) ≈ x
  calc
    (0 : Q') + x * ((1 : Q') + x * (0 : Q'))
        ≈ x * ((1 : Q') + x * (0 : Q')) := q_zero_add_eqv _
    _ ≈ x * (1 : Q') :=
      Q'.mul_eqv_congr_left x _ _
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (1 : Q') _ _ (q_mul_zero x))
          (q_add_zero_eqv (1 : Q')))
    _ ≈ x := Q'.mul_one_eqv x

/-- A coefficient polynomial for every first-kind Chebyshev mode.

For levels at least two we reuse the existing second-kind polynomial and the
proved identity `T_{n+2} = x U_{n+1} - U_n`. -/
def chebTQPoly : Nat → QPoly.Poly
  | 0 => pone
  | 1 => classXQPoly
  | n + 2 =>
      psub (pmul classXQPoly (chebPoly (n + 1))) (chebPoly n)

theorem eval_chebTQPoly : ∀ (n : Nat) (x : Q'),
    QPoly.eval (chebTQPoly n) x ≈ T n x
  | 0, x => by
      rw [T_zero]
      exact eval_pone x
  | 1, x => by
      rw [T_one]
      exact eval_classXQPoly x
  | n + 2, x => by
      calc
        QPoly.eval (chebTQPoly (n + 2)) x
            ≈ QPoly.eval (pmul classXQPoly (chebPoly (n + 1))) x +
                (-(QPoly.eval (chebPoly n) x)) :=
              eval_psub _ _ x
        _ ≈ (QPoly.eval classXQPoly x *
                QPoly.eval (chebPoly (n + 1)) x) +
              (-(QPoly.eval (chebPoly n) x)) :=
            q_add_congr (eval_pmul _ _ x) (Q'.eqv_refl _)
        _ ≈ (x * U (n + 1) x) + (-(U n x)) :=
            q_add_congr
              (q_mul_congr (eval_classXQPoly x)
                (eval_chebPoly (n + 1) x))
              (Q'.neg_eqv_congr _ _ (eval_chebPoly n x))
        _ ≈ T (n + 2) x := Q'.eqv_symm (Tshift n x)

/-- A coefficient polynomial for the odd half-angle feature
`C_0=1`, `C_{k+1}=U_{k+1}-U_k`. -/
def chebCQPoly : Nat → QPoly.Poly
  | 0 => pone
  | k + 1 => psub (chebPoly (k + 1)) (chebPoly k)

theorem eval_chebCQPoly : ∀ (k : Nat) (x : Q'),
    QPoly.eval (chebCQPoly k) x ≈ C k x
  | 0, x => by
      rw [C_zero]
      exact eval_pone x
  | k + 1, x => by
      change QPoly.eval (psub (chebPoly (k + 1)) (chebPoly k)) x ≈
        U (k + 1) x + (-(U k x))
      exact Q'.eqv_trans _ _ _ (eval_psub _ _ x)
        (q_add_congr (eval_chebPoly (k + 1) x)
          (Q'.neg_eqv_congr _ _ (eval_chebPoly k x)))

/-- First-kind mode embedded at the anchor class coordinate `x_0`. -/
def chebTRatPoly (n : Nat) : RatPoly :=
  qPolyToRatPolyAt 0 (chebTQPoly n)

/-- Odd half-angle mode embedded at the anchor class coordinate `x_0`. -/
def chebCRatPoly (k : Nat) : RatPoly :=
  qPolyToRatPolyAt 0 (chebCQPoly k)

theorem eval_chebTRatPoly (n : Nat) (input : AnchorQuaternionInput) :
    evalRatPoly (anchorEnvironment input) (chebTRatPoly n) ≈ T n input.x := by
  have hlift := eval_qPolyToRatPolyAt
    (anchorEnvironment input) 0 (chebTQPoly n)
  rw [anchorEnvironment_x] at hlift
  exact Q'.eqv_trans _ _ _ hlift (eval_chebTQPoly n input.x)

theorem eval_chebCRatPoly (k : Nat) (input : AnchorQuaternionInput) :
    evalRatPoly (anchorEnvironment input) (chebCRatPoly k) ≈ C k input.x := by
  have hlift := eval_qPolyToRatPolyAt
    (anchorEnvironment input) 0 (chebCQPoly k)
  rw [anchorEnvironment_x] at hlift
  exact Q'.eqv_trans _ _ _ hlift (eval_chebCQPoly k input.x)

/-! ## 4. Polynomial realizations of finite SOS feature families -/

/-- Type-level evidence that every feature in a finite weighted SOS has an
explicit `RatPoly` representative in the fixed anchor environment. -/
structure RatPolyFeatures (data : AnchorFaceSOS) where
  featurePoly : Nat → RatPoly
  eval_featurePoly : ∀ (term : Nat) (input : AnchorQuaternionInput),
    evalRatPoly (anchorEnvironment input) (featurePoly term) ≈
      data.feature term input

/-- Constant SOS features are represented by the polynomial unit.  The
constant coefficient itself remains a weight, exactly as in the SOS data. -/
def constantRatPolyFeatures (q : Q') (hq : (0 : Q') ≤ q) :
    RatPolyFeatures (constant AnchorQuaternionInput q hq) where
  featurePoly := fun _ => polyOne
  eval_featurePoly := by
    intro _ input
    exact evalRatPoly_one (anchorEnvironment input)

/-- Scaling changes weights but not features. -/
def scaleRatPolyFeatures (q : Q') (hq : (0 : Q') ≤ q)
    (data : AnchorFaceSOS) (realization : RatPolyFeatures data) :
    RatPolyFeatures (scale q hq data) where
  featurePoly := realization.featurePoly
  eval_featurePoly := realization.eval_featurePoly

/-- Offset-packed direct sums select the same polynomial branch as the
underlying finite weighted SOS construction. -/
def addRatPolyFeatures (left right : AnchorFaceSOS)
    (leftRealization : RatPolyFeatures left)
    (rightRealization : RatPolyFeatures right) :
    RatPolyFeatures (add left right) where
  featurePoly := fun term =>
    if term < left.termCount then leftRealization.featurePoly term
    else rightRealization.featurePoly (term - left.termCount)
  eval_featurePoly := by
    intro term input
    change
      evalRatPoly (anchorEnvironment input)
          (if term < left.termCount
            then leftRealization.featurePoly term
            else rightRealization.featurePoly (term - left.termCount)) ≈
        (if term < left.termCount then left.feature term input
         else right.feature (term - left.termCount) input)
    split
    · exact leftRealization.eval_featurePoly term input
    · exact rightRealization.eval_featurePoly (term - left.termCount) input

/-- A direct unit-square family is polynomial whenever its supplied feature
family has explicit polynomial representatives. -/
def unitSquareSumRatPolyFeatures (count : Nat)
    (feature : Nat → AnchorQuaternionInput → Q')
    (featurePoly : Nat → RatPoly)
    (hfeature : ∀ term input,
      evalRatPoly (anchorEnvironment input) (featurePoly term) ≈
        feature term input) :
    RatPolyFeatures (unitSquareSumSOS count feature) where
  featurePoly := featurePoly
  eval_featurePoly := hfeature

/-! ## 5. Even and odd feature packets -/

def evenModeSquareRatPolyFeatures (m : Nat) :
    RatPolyFeatures (evenModeSquareSOS m) :=
  unitSquareSumRatPolyFeatures m
    (fun k input => T (k + 1) input.x)
    (fun k => chebTRatPoly (k + 1))
    (fun k input => eval_chebTRatPoly (k + 1) input)

def evenShiftedCharacterRatPolyFeatures (m : Nat) :
    RatPolyFeatures (evenShiftedCharacterSOS m) := by
  unfold evenShiftedCharacterSOS
  exact addRatPolyFeatures _ _
    (constantRatPolyFeatures (2 : Q') (by decide))
    (scaleRatPolyFeatures (4 : Q') (by decide) _
      (evenModeSquareRatPolyFeatures m))

/-- The polynomial `1+x`, used by the zeroth odd quaternion feature. -/
def oneAddXPoly : RatPoly := polyAdd polyOne (polyVar 0)

theorem eval_anchorXPoly (input : AnchorQuaternionInput) :
    evalRatPoly (anchorEnvironment input) (polyVar 0) ≈ input.x := by
  simpa only [anchorEnvironment_x] using
    (evalRatPoly_var (anchorEnvironment input) 0)

theorem eval_anchorY1Poly (input : AnchorQuaternionInput) :
    evalRatPoly (anchorEnvironment input) (polyVar 1) ≈ input.y1 := by
  simpa only [anchorEnvironment_y1] using
    (evalRatPoly_var (anchorEnvironment input) 1)

theorem eval_anchorY2Poly (input : AnchorQuaternionInput) :
    evalRatPoly (anchorEnvironment input) (polyVar 2) ≈ input.y2 := by
  simpa only [anchorEnvironment_y2] using
    (evalRatPoly_var (anchorEnvironment input) 2)

theorem eval_anchorY3Poly (input : AnchorQuaternionInput) :
    evalRatPoly (anchorEnvironment input) (polyVar 3) ≈ input.y3 := by
  simpa only [anchorEnvironment_y3] using
    (evalRatPoly_var (anchorEnvironment input) 3)

theorem eval_oneAddXPoly (input : AnchorQuaternionInput) :
    evalRatPoly (anchorEnvironment input) oneAddXPoly ≈
      (1 : Q') + input.x := by
  exact Q'.eqv_trans _ _ _
    (evalRatPoly_add (anchorEnvironment input) polyOne (polyVar 0))
    (q_add_congr (evalRatPoly_one (anchorEnvironment input))
      (eval_anchorXPoly input))

/-- Polynomial representative of one of the four features at odd level `k`. -/
def oddQuaternionFeatureRatPoly (k term : Nat) : RatPoly :=
  match term with
  | 0 => polyMul oneAddXPoly (chebCRatPoly k)
  | 1 => polyMul (polyVar 1) (chebCRatPoly k)
  | 2 => polyMul (polyVar 2) (chebCRatPoly k)
  | _ => polyMul (polyVar 3) (chebCRatPoly k)

theorem eval_oddQuaternionFeatureRatPoly
    (k term : Nat) (input : AnchorQuaternionInput) :
    evalRatPoly (anchorEnvironment input)
        (oddQuaternionFeatureRatPoly k term) ≈
      oddQuaternionFeature k term input := by
  rcases term with _ | term
  · exact Q'.eqv_trans _ _ _
      (evalRatPoly_mul (anchorEnvironment input) oneAddXPoly (chebCRatPoly k))
      (q_mul_congr (eval_oneAddXPoly input) (eval_chebCRatPoly k input))
  · rcases term with _ | term
    · exact Q'.eqv_trans _ _ _
        (evalRatPoly_mul (anchorEnvironment input) (polyVar 1) (chebCRatPoly k))
        (q_mul_congr (eval_anchorY1Poly input) (eval_chebCRatPoly k input))
    · rcases term with _ | term
      · exact Q'.eqv_trans _ _ _
          (evalRatPoly_mul (anchorEnvironment input) (polyVar 2) (chebCRatPoly k))
          (q_mul_congr (eval_anchorY2Poly input) (eval_chebCRatPoly k input))
      · exact Q'.eqv_trans _ _ _
          (evalRatPoly_mul (anchorEnvironment input) (polyVar 3) (chebCRatPoly k))
          (q_mul_congr (eval_anchorY3Poly input) (eval_chebCRatPoly k input))

def oddQuaternionChannelRatPolyFeatures (k : Nat) :
    RatPolyFeatures (oddQuaternionChannelSOS k) :=
  unitSquareSumRatPolyFeatures 4
    (oddQuaternionFeature k) (oddQuaternionFeatureRatPoly k)
    (eval_oddQuaternionFeatureRatPoly k)

def oddShiftedCharacterRatPolyFeatures : ∀ m : Nat,
    RatPolyFeatures (oddShiftedCharacterSOS m)
  | 0 => oddQuaternionChannelRatPolyFeatures 0
  | m + 1 =>
      addRatPolyFeatures _ _
        (oddShiftedCharacterRatPolyFeatures m)
        (oddQuaternionChannelRatPolyFeatures (m + 1))

def shiftedCharacterRatPolyFeatures (rank : Nat) :
    RatPolyFeatures (shiftedCharacterSOS rank) := by
  unfold shiftedCharacterSOS
  split
  · exact evenShiftedCharacterRatPolyFeatures (rank / 2)
  · exact oddShiftedCharacterRatPolyFeatures (rank / 2)

/-! ## 6. The complete anchor-face realization -/

def anchorRankRatPolyFeatures (index : Nat) :
    RatPolyFeatures (anchorRankSOS index) := by
  unfold anchorRankSOS
  exact scaleRatPolyFeatures _ _ _
    (shiftedCharacterRatPolyFeatures (1 + index))

def anchorExcitedRatPolyFeatures : ∀ cutoff : Nat,
    RatPolyFeatures (anchorExcitedSOS cutoff)
  | 0 => constantRatPolyFeatures (0 : Q') (by decide)
  | cutoff + 1 =>
      addRatPolyFeatures _ _
        (anchorExcitedRatPolyFeatures cutoff)
        (anchorRankRatPolyFeatures cutoff)

/-- Every feature in the complete truncated anchor-face SOS has a literal
finite-support rational polynomial representative. -/
def anchorFaceRatPolyFeatures (cutoff : Nat) :
    RatPolyFeatures (anchorFaceSOS cutoff) := by
  unfold anchorFaceSOS
  exact addRatPolyFeatures _ _
    (constantRatPolyFeatures (anchorVacuumReserve cutoff)
      (anchorVacuumReserve_nonnegative cutoff))
    (anchorExcitedRatPolyFeatures cutoff)

/-- The concrete polynomial representing a selected complete-face feature. -/
def anchorFaceFeaturePolynomial (cutoff term : Nat) : RatPoly :=
  (anchorFaceRatPolyFeatures cutoff).featurePoly term

theorem eval_anchorFaceFeaturePolynomial
    (cutoff term : Nat) (input : AnchorQuaternionInput) :
    evalRatPoly (anchorEnvironment input)
        (anchorFaceFeaturePolynomial cutoff term) ≈
      (anchorFaceSOS cutoff).feature term input :=
  (anchorFaceRatPolyFeatures cutoff).eval_featurePoly term input

/-! ## 7. The polynomial of a complete weighted SOS value -/

/-- Finite sum in the `RatPoly` carrier. -/
def ratPolyFinSum (polynomial : Nat → RatPoly) : Nat → RatPoly
  | 0 => polyZero
  | count + 1 => polyAdd (ratPolyFinSum polynomial count) (polynomial count)

theorem eval_ratPolyFinSum (rho : Nat → Q') (polynomial : Nat → RatPoly) :
    ∀ count : Nat,
      evalRatPoly rho (ratPolyFinSum polynomial count) ≈
        finSum (fun term => evalRatPoly rho (polynomial term)) count
  | 0 => Q'.eqv_refl _
  | count + 1 => by
      exact Q'.eqv_trans _ _ _
        (evalRatPoly_add rho (ratPolyFinSum polynomial count)
          (polynomial count))
        (q_add_congr (eval_ratPolyFinSum rho polynomial count)
          (Q'.eqv_refl _))

/-- Turn a polynomially-realized finite weighted SOS into the literal
polynomial sum `sum_t w_t p_t^2`. -/
def weightedSOSPolynomial (data : AnchorFaceSOS)
    (realization : RatPolyFeatures data) : RatPoly :=
  ratPolyFinSum
    (fun term =>
      polySmul (data.weight term)
        (polyMul (realization.featurePoly term)
          (realization.featurePoly term)))
    data.termCount

/-- Evaluation of the assembled polynomial is exactly the finite weighted SOS
value. -/
theorem eval_weightedSOSPolynomial (data : AnchorFaceSOS)
    (realization : RatPolyFeatures data) (input : AnchorQuaternionInput) :
    evalRatPoly (anchorEnvironment input)
        (weightedSOSPolynomial data realization) ≈ value data input := by
  unfold weightedSOSPolynomial value
  refine Q'.eqv_trans _
    (finSum (fun term =>
      evalRatPoly (anchorEnvironment input)
        (polySmul (data.weight term)
          (polyMul (realization.featurePoly term)
            (realization.featurePoly term)))) data.termCount) _
    (eval_ratPolyFinSum _ _ _) ?_
  exact finSum_eqv_congr _ _ (fun term => by
    calc
      evalRatPoly (anchorEnvironment input)
          (polySmul (data.weight term)
            (polyMul (realization.featurePoly term)
              (realization.featurePoly term)))
          ≈ data.weight term *
              evalRatPoly (anchorEnvironment input)
                (polyMul (realization.featurePoly term)
                  (realization.featurePoly term)) :=
            evalRatPoly_smul _ _ _
      _ ≈ data.weight term *
            (evalRatPoly (anchorEnvironment input)
                (realization.featurePoly term) *
              evalRatPoly (anchorEnvironment input)
                (realization.featurePoly term)) :=
          Q'.mul_eqv_congr_left _ _ _
            (evalRatPoly_mul _ _ _)
      _ ≈ data.weight term *
            (data.feature term input * data.feature term input) :=
          Q'.mul_eqv_congr_left _ _ _
            (q_mul_congr
              (realization.eval_featurePoly term input)
              (realization.eval_featurePoly term input))) data.termCount

/-- The complete truncated anchor-face weight as one concrete `RatPoly`. -/
def anchorFaceWeightedSOSPolynomial (cutoff : Nat) : RatPoly :=
  weightedSOSPolynomial (anchorFaceSOS cutoff)
    (anchorFaceRatPolyFeatures cutoff)

theorem eval_anchorFaceWeightedSOSPolynomial
    (cutoff : Nat) (input : AnchorQuaternionInput) :
    evalRatPoly (anchorEnvironment input)
        (anchorFaceWeightedSOSPolynomial cutoff) ≈
      value (anchorFaceSOS cutoff) input :=
  eval_weightedSOSPolynomial _ _ input

theorem anchorTruncatedFaceClassValue_eqv_eval_anchorFacePolynomial
    (cutoff : Nat) (input : AnchorQuaternionInput) :
    anchorTruncatedFaceClassValue cutoff input.x ≈
      evalRatPoly (anchorEnvironment input)
        (anchorFaceWeightedSOSPolynomial cutoff) := by
  exact Q'.eqv_trans _ _ _
    (anchorTruncatedFaceClassValue_eqv_anchorFaceSOS cutoff input)
    (Q'.eqv_symm (eval_anchorFaceWeightedSOSPolynomial cutoff input))

#print axioms eval_qPolyToRatPolyAt
#print axioms eval_chebTQPoly
#print axioms eval_chebCQPoly
#print axioms eval_anchorFaceFeaturePolynomial
#print axioms eval_weightedSOSPolynomial
#print axioms anchorTruncatedFaceClassValue_eqv_eval_anchorFacePolynomial

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceRatPolyRealization
