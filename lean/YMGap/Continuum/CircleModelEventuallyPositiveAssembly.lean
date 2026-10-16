/-
# Circle-model assembly with stable eventual positivity

`CircleModelAssembly.CircleData` asks for multiplication and zero cancellation
for the one-slack predicate `CReal.IsPositive`.  That predicate is useful for
specific regular representatives, but its all-index definition is not stable
enough to make arbitrary pointwise CReal products positive: finitely many early
approximations may have opposite signs.

This leaf uses the representation-invariant fact actually needed by the
Gaussian-integer direction argument.  A radius is `EventuallyPositive` when it
is bounded below by one positive rational after an explicit existential stage.
This predicate is closed under pointwise multiplication, and an eventually
positive factor cancels constructively from an `Equiv` product with zero.

The resulting `StableCircleData` retains only the two honest transcendental base
direction links.  From those links this file constructs an actual
`ArctanTanInversion.CircleModel` and hence the existing conditional `sin pi = 0`
conclusion.  It does not construct either base link and therefore does not close
the arctan-series/trig-series residual, the transverse-mode rows, or any
continuum/Clay-facing statement.
-/

import YMGap.Continuum.CircleModelAssembly
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.CircleModelEventuallyPositiveAssembly

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ArctanTanInversion
open YMGap.Continuum.CircleModelAssembly

/-- A CReal radius with a positive rational lower bound after some stage. -/
def EventuallyPositive (radius : CReal) : Prop :=
  ∃ lower : Q', (0 : Q') < lower ∧
    ∃ stage : Nat, ∀ approximation : Nat, stage ≤ approximation →
      lower ≤ radius.approx approximation

/-- The legacy one-slack positivity predicate supplies stable eventual
positivity, but the new assembly uses only the latter. -/
theorem eventuallyPositive_of_isPositive {radius : CReal}
    (hpositive : CReal.IsPositive radius) : EventuallyPositive radius :=
  CReal.eventually_ge_of_isPositive hpositive

/-- Stable eventual positivity is closed under the pointwise CReal product. -/
theorem eventuallyPositive_mul {left right : CReal}
    (hleft : EventuallyPositive left)
    (hright : EventuallyPositive right) :
    EventuallyPositive (CReal.mul left right) := by
  obtain ⟨leftLower, hleftLower, leftStage, hleftStage⟩ := hleft
  obtain ⟨rightLower, hrightLower, rightStage, hrightStage⟩ := hright
  refine ⟨leftLower * rightLower, Q'.mul_pos hleftLower hrightLower,
    max leftStage rightStage, ?_⟩
  intro approximation happroximation
  have hleftApproximation : leftStage ≤ approximation :=
    Nat.le_trans (Nat.le_max_left _ _) happroximation
  have hrightApproximation : rightStage ≤ approximation :=
    Nat.le_trans (Nat.le_max_right _ _) happroximation
  have hleftBound := hleftStage approximation hleftApproximation
  have hrightBound := hrightStage approximation hrightApproximation
  exact Q'.mul_le_mul_of_nonneg hleftBound hrightBound
    (Q'.le_trans' _ _ _ (Q'.le_of_lt hleftLower) hleftBound)
    (Q'.le_of_lt hrightLower)

/-- An eventually positive CReal factor cancels from a product equivalent to
zero.  The proof uses tolerance `lower * epsilon` and rational positive-factor
cancellation after splitting on the sign of the other approximation. -/
theorem equiv_czero_of_eventuallyPositive_mul
    {radius value : CReal}
    (hpositive : EventuallyPositive radius)
    (hzero : CReal.Equiv (CReal.mul radius value) CReal.czero) :
    CReal.Equiv value CReal.czero := by
  obtain ⟨lower, hlower, positiveStage, hpositiveStage⟩ := hpositive
  intro epsilon hepsilon
  have hscaledPositive : (0 : Q') < lower * epsilon :=
    Q'.mul_pos hlower hepsilon
  obtain ⟨zeroStage, hzeroStage⟩ := hzero (lower * epsilon) hscaledPositive
  refine ⟨max positiveStage zeroStage, fun approximation happroximation => ?_⟩
  have hpositiveApproximation : positiveStage ≤ approximation :=
    Nat.le_trans (Nat.le_max_left _ _) happroximation
  have hzeroApproximation : zeroStage ≤ approximation :=
    Nat.le_trans (Nat.le_max_right _ _) happroximation
  have hlowerApproximation :=
    hpositiveStage approximation hpositiveApproximation
  have hzeroBounds := hzeroStage approximation hzeroApproximation
  have hproductUpper :
      radius.approx approximation * value.approx approximation ≤
        lower * epsilon := by
    have h := hzeroBounds.1
    change radius.approx approximation * value.approx approximation ≤
      (0 : Q') + lower * epsilon at h
    rw [Q'.zero_add'] at h
    exact h
  have hproductLower :
      -(lower * epsilon) ≤
        radius.approx approximation * value.approx approximation := by
    have h := hzeroBounds.2
    change (0 : Q') ≤
      radius.approx approximation * value.approx approximation +
        lower * epsilon at h
    exact Q'.neg_le_of_zero_le_add h
  by_cases hvalueNonnegative : (0 : Q') ≤ value.approx approximation
  · have hscaledValue :
        lower * value.approx approximation ≤
          radius.approx approximation * value.approx approximation :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        hlowerApproximation hvalueNonnegative
    have hupper : value.approx approximation ≤ epsilon :=
      Q'.le_of_mul_le_mul_left
        (Q'.le_trans' _ _ _ hscaledValue hproductUpper) hlower
    refine ⟨?_, ?_⟩
    · change value.approx approximation ≤ (0 : Q') + epsilon
      rw [Q'.zero_add']
      exact hupper
    · exact Q'.zero_le_add _ _ hvalueNonnegative (Q'.le_of_lt hepsilon)
  · have hvalueNonpositive : value.approx approximation ≤ (0 : Q') :=
      Q'.nonpos_of_not_nonneg hvalueNonnegative
    have hnegativeValue : (0 : Q') ≤ -(value.approx approximation) :=
      Q'.neg_nonneg_of_not_nonneg hvalueNonnegative
    have hscaledNegative :
        lower * (-(value.approx approximation)) ≤
          radius.approx approximation * (-(value.approx approximation)) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        hlowerApproximation hnegativeValue
    have hnegativeProduct :
        -(radius.approx approximation * value.approx approximation) ≤
          lower * epsilon := by
      have hnegated := Q'.neg_le_neg hproductLower
      exact Q'.le_trans' _ _ _ hnegated
        (Q'.le_of_eqv (Q'.neg_neg_eqv (lower * epsilon)))
    have hnegativeUpper :
        -(value.approx approximation) ≤ epsilon := by
      apply Q'.le_of_mul_le_mul_left (c := lower) _ hlower
      exact Q'.le_trans' _ _ _ hscaledNegative
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (Q'.mul_neg_eqv
              (radius.approx approximation)
              (value.approx approximation)))
          hnegativeProduct)
    refine ⟨?_, ?_⟩
    · change value.approx approximation ≤ (0 : Q') + epsilon
      rw [Q'.zero_add']
      exact Q'.le_trans' _ _ _ hvalueNonpositive (Q'.le_of_lt hepsilon)
    · have hlowerValue : -epsilon ≤ value.approx approximation := by
        have hnegated := Q'.neg_le_neg hnegativeUpper
        exact Q'.le_trans' _ _ _ hnegated
          (Q'.le_of_eqv (Q'.neg_neg_eqv (value.approx approximation)))
      have hadd := Q'.add_le_add_right (-epsilon)
        (value.approx approximation) epsilon hlowerValue
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.neg_add_self_eqv epsilon)) hadd

/-- A Gaussian integer points in a direction through an eventually positive
radius. -/
def stableRepDir (direction : CReal × CReal) (integer : GaussInt) : Prop :=
  ∃ radius : CReal, EventuallyPositive radius
    ∧ CReal.Equiv (CReal.ofQ' (Q'.ofInt integer.re))
        (CReal.mul radius direction.2)
    ∧ CReal.Equiv (CReal.ofQ' (Q'.ofInt integer.im))
        (CReal.mul radius direction.1)

/-- The stable direction representation is closed under complex product. -/
theorem stableRepDir_add
    {leftDirection rightDirection : CReal × CReal}
    {leftInteger rightInteger : GaussInt}
    (hleft : stableRepDir leftDirection leftInteger)
    (hright : stableRepDir rightDirection rightInteger) :
    stableRepDir (dadd leftDirection rightDirection)
      (gMul leftInteger rightInteger) := by
  obtain ⟨leftRadius, hleftPositive, hleftReal, hleftImaginary⟩ := hleft
  obtain ⟨rightRadius, hrightPositive, hrightReal, hrightImaginary⟩ := hright
  refine ⟨CReal.mul leftRadius rightRadius,
    eventuallyPositive_mul hleftPositive hrightPositive, ?_, ?_⟩
  · have hrealLeft :
        CReal.Equiv (CReal.ofQ' (Q'.ofInt (leftInteger.re * rightInteger.re)))
          (CReal.mul (CReal.mul leftRadius rightRadius)
            (CReal.mul leftDirection.2 rightDirection.2)) :=
      prodLemma leftInteger.re rightInteger.re
        leftRadius leftDirection.2 rightRadius rightDirection.2
        hleftReal hrightReal
    have hrealRight :
        CReal.Equiv (CReal.ofQ' (Q'.ofInt (leftInteger.im * rightInteger.im)))
          (CReal.mul (CReal.mul leftRadius rightRadius)
            (CReal.mul leftDirection.1 rightDirection.1)) :=
      prodLemma leftInteger.im rightInteger.im
        leftRadius leftDirection.1 rightRadius rightDirection.1
        hleftImaginary hrightImaginary
    refine (realHom leftInteger rightInteger).trans ?_
    refine ((CReal.sub_congr_left hrealLeft).trans
      (CReal.sub_congr_right hrealRight)).trans ?_
    exact (cmul_sub (CReal.mul leftRadius rightRadius)
      (CReal.mul leftDirection.2 rightDirection.2)
      (CReal.mul leftDirection.1 rightDirection.1)).symm
  · have himaginaryLeft :
        CReal.Equiv (CReal.ofQ' (Q'.ofInt (leftInteger.im * rightInteger.re)))
          (CReal.mul (CReal.mul leftRadius rightRadius)
            (CReal.mul leftDirection.1 rightDirection.2)) :=
      prodLemma leftInteger.im rightInteger.re
        leftRadius leftDirection.1 rightRadius rightDirection.2
        hleftImaginary hrightReal
    have himaginaryRight :
        CReal.Equiv (CReal.ofQ' (Q'.ofInt (leftInteger.re * rightInteger.im)))
          (CReal.mul (CReal.mul leftRadius rightRadius)
            (CReal.mul leftDirection.2 rightDirection.1)) :=
      prodLemma leftInteger.re rightInteger.im
        leftRadius leftDirection.2 rightRadius rightDirection.1
        hleftReal hrightImaginary
    refine (imagHom leftInteger rightInteger).trans ?_
    refine ((CReal.add_congr_left himaginaryLeft).trans
      (CReal.add_congr_right himaginaryRight)).trans ?_
    exact (YMGap.Constructive.TrigSignedAddFull.cmul_add
      (CReal.mul leftRadius rightRadius)
      (CReal.mul leftDirection.1 rightDirection.2)
      (CReal.mul leftDirection.2 rightDirection.1)).symm

/-- A represented direction with zero Gaussian-integer imaginary part has zero
sine coordinate, by stable positive-factor cancellation. -/
theorem stableSinZero
    {direction : CReal × CReal} {integer : GaussInt}
    (hrepresentation : stableRepDir direction integer)
    (himaginary : integer.im = 0) :
    CReal.Equiv direction.1 CReal.czero := by
  obtain ⟨radius, hpositive, _, himaginaryRepresentation⟩ := hrepresentation
  have hzero : CReal.Equiv (CReal.mul radius direction.1) CReal.czero := by
    have h := himaginaryRepresentation.symm
    rw [himaginary] at h
    exact h
  exact equiv_czero_of_eventuallyPositive_mul hpositive hzero

/-- Only the two transcendental base-direction links remain as data. -/
structure StableCircleData : Type where
  baseP : CReal × CReal
  repBaseP : stableRepDir baseP gi5
  baseM : CReal × CReal
  repBaseM : stableRepDir baseM gi239m

/-- The concrete circle model assembled from stable base-direction links. -/
def toModel (data : StableCircleData) : CircleModel where
  Angle := CReal × CReal
  add := dadd
  sinOf := fun direction => direction.1
  rep := stableRepDir
  rep_add := fun hleft hright => stableRepDir_add hleft hright
  baseP := data.baseP
  repBaseP := data.repBaseP
  baseM := data.baseM
  repBaseM := data.repBaseM
  sin_zero_of_rep_im_zero := fun hrepresentation himaginary =>
    stableSinZero hrepresentation himaginary

/-- The existing Gaussian-integer Machin telescoping now depends only on the
two stable base-direction links. -/
theorem sinPi_eqv_zero (data : StableCircleData) :
    CReal.Equiv ((toModel data).sinOf (toModel data).piAngle) CReal.czero :=
  ArctanTanInversion.CircleModel.sinMachinAngle_eqv_zero (toModel data)

end YMGap.Continuum.CircleModelEventuallyPositiveAssembly

#print axioms
  YMGap.Continuum.CircleModelEventuallyPositiveAssembly.eventuallyPositive_mul
#print axioms
  YMGap.Continuum.CircleModelEventuallyPositiveAssembly.equiv_czero_of_eventuallyPositive_mul
#print axioms
  YMGap.Continuum.CircleModelEventuallyPositiveAssembly.stableRepDir_add
#print axioms
  YMGap.Continuum.CircleModelEventuallyPositiveAssembly.stableSinZero
#print axioms
  YMGap.Continuum.CircleModelEventuallyPositiveAssembly.toModel
#print axioms
  YMGap.Continuum.CircleModelEventuallyPositiveAssembly.sinPi_eqv_zero
