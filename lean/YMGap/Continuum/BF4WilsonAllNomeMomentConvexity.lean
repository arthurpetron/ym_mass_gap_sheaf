/-
# Discrete convexity of ORIGINAL fixed-width Wilson time moments

Site and bond reflection positivity are applied to the literal adjacent-time
difference. Signed linearity expands their four cross terms; the existing
joint-limit padding theorem identifies each with the SAME lag moment.
Both parities give nonnegative second differences for every 0<w<1.

This is an original-state theorem at fixed spatial width and lattice spacing.
It adds no positive response floor, spatial limit or physical mass claim.
-/
import YMGap.Continuum.BF4WilsonJointFunctionalLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
import YMGap.Continuum.BF4WilsonAllNomeKineticIncrement
import YMGap.Continuum.CRealDiscreteConvexity

namespace YMGap.Continuum.BF4WilsonAllNomeMomentConvexity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow (reverse oddPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive (originalJoint_odd_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity (originalJoint_padding)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws
open YMGap.Continuum.BF4WilsonAllNomeKineticIncrement (differenceExpression)

attribute [local irreducible] originalJointLimit

/-- Upper insertion first, with the same literal fundamental Wilson source. -/
def lagExpression {width : Nat} (loop : SourceLoop width) (n : Nat) : WindowExpression width :=
  .mul (.loop n loop 1) (.loop 0 loop 1)

theorem lag_within {width : Nat} (loop : SourceLoop width) (n : Nat) :
    Within n (lagExpression loop n) := ⟨Nat.le_refl _, Nat.zero_le _⟩

def lagMoment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (n : Nat) : CReal :=
  originalJointLimit hw0 hw1 n (lagExpression loop n) (lag_within loop n)

/-- Stationarity here follows from the EXISTING joint-limit padding law,
not from a stationary measure or Perron vector supplied as an assumption. -/
theorem pair_lag {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (L s t : Nat) (hst : s ≤ t) (ht : t ≤ L) :
    Equiv (originalJointLimit hw0 hw1 L (.mul (.loop t loop 1) (.loop s loop 1))
      ⟨ht, Nat.le_trans hst ht⟩) (lagMoment hw0 hw1 loop (t-s)) := by
  have h := originalJoint_padding hw0 hw1 (t-s) s (L-t)
    (lagExpression loop (t-s)) (lag_within loop (t-s))
  have htime : (t-s)+s+(L-t)=L := by omega
  have hsource : shift s (lagExpression loop (t-s)) =
      .mul (.loop t loop 1) (.loop s loop 1) := by
    simp only [shift, lagExpression, mapOffsets, Nat.zero_add, Nat.sub_add_cancel hst]
  simpa only [htime, hsource, lagMoment] using h

/-- Literal signed expression whose expectation is the second time difference. -/
def secondDifferenceExpression {width : Nat} (loop : SourceLoop width) (n : Nat) :
    WindowExpression width :=
  .mul (difference (.loop (n+2) loop 1) (.loop (n+1) loop 1))
    (difference (.loop 0 loop 1) (.loop 1 loop 1))

theorem secondDifference_within {width : Nat} (loop : SourceLoop width) (n : Nat) :
    Within (n+2) (secondDifferenceExpression loop n) := by
  exact ⟨⟨Nat.le_refl _, Nat.le_succ _⟩, ⟨Nat.zero_le _, by change 1 ≤ n+2; omega⟩⟩

theorem secondDifference_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (n : Nat) :
    Equiv (originalJointLimit hw0 hw1 (n+2) (secondDifferenceExpression loop n)
      (secondDifference_within loop n))
      (CRealDiscreteConvexity.curvature (lagMoment hw0 hw1 loop) n) := by
  have he := joint_difference_product hw0 hw1 (n+2)
    (.loop (n+2) loop 1) (.loop (n+1) loop 1) (.loop 0 loop 1) (.loop 1 loop 1)
    (Nat.le_refl _) (by change n+1 ≤ n+2; omega) (Nat.zero_le _)
    (by change 1 ≤ n+2; omega)
  have hp := equiv_add
    (equiv_sub (pair_lag hw0 hw1 loop (n+2) 0 (n+2) (by omega) (Nat.le_refl _))
      (pair_lag hw0 hw1 loop (n+2) 1 (n+2) (by omega) (Nat.le_refl _)))
    (equiv_sub (pair_lag hw0 hw1 loop (n+2) 1 (n+1) (by omega) (by omega))
      (pair_lag hw0 hw1 loop (n+2) 0 (n+1) (by omega) (by omega)))
  exact Equiv.trans he (Equiv.trans hp
    (SumOfSquares.Equiv_of_approx_eqv (fun k => Q'.add_comm_eqv _ _)))

private theorem difference_within_succ {width : Nat} (loop : SourceLoop width) (k : Nat) :
    Within (k+1) (differenceExpression loop) := by
  exact ⟨Nat.zero_le _, Nat.succ_le_succ (Nat.zero_le _)⟩

private theorem even_expression {width : Nat} (loop : SourceLoop width) (k : Nat) :
    WindowExpression.mul (mirror (k+1) (differenceExpression loop)) (differenceExpression loop) =
      secondDifferenceExpression loop (2*k) := by
  simp only [mirror, differenceExpression, secondDifferenceExpression, difference, mapOffsets, Nat.sub_zero]
  rw [show 2*(k+1)=2*k+2 by omega, show 2*k+2-1=2*k+1 by omega]

private theorem odd_expression {width : Nat} (loop : SourceLoop width) (k : Nat) :
    oddPair (k+1) (differenceExpression loop) = secondDifferenceExpression loop (2*k+1) := by
  simp only [oddPair, reverse, shift, differenceExpression, secondDifferenceExpression,
    difference, mapOffsets, Nat.sub_zero, Nat.add_sub_cancel]
  rw [show k+1+(k+1+1)=2*k+1+2 by omega,
    show k+(k+1+1)=2*k+1+1 by omega]

/-- Both even and odd lags use their ACTUAL original reflection-positive
window; the small-nome guards of spatial completion are not present here. -/
theorem secondDifference_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (n : Nat) :
    leEv (ofQ' 0) (originalJointLimit hw0 hw1 (n+2) (secondDifferenceExpression loop n)
      (secondDifference_within loop n)) := by
  by_cases hn : n % 2 = 0
  · have h := originalJoint_reflected_nonnegative hw0 hw1 (n/2+1)
      (differenceExpression loop) (difference_within_succ loop (n/2))
    have he : n=2*(n/2) := by omega
    simpa only [even_expression, show 2*(n/2+1)=2*(n/2)+2 by omega, ←he] using h
  · have h := originalJoint_odd_nonnegative hw0 hw1 (n/2+1)
      (differenceExpression loop) (difference_within_succ loop (n/2))
    have he : n=2*(n/2)+1 := by omega
    simpa only [odd_expression, show 2*(n/2+1)+1=(2*(n/2)+1)+2 by omega, ←he] using h

theorem lagMoment_convex {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (n : Nat) :
    leEv (ofQ' 0) (CRealDiscreteConvexity.curvature (lagMoment hw0 hw1 loop) n) :=
  leEv_trans (secondDifference_nonnegative hw0 hw1 loop n)
    (leEv_of_equiv (secondDifference_pin hw0 hw1 loop n))

/-- A proved endpoint bound for this SAME Wilson moment, not an abstract
convexity input. Centering by a constant leaves this endpoint difference unchanged. -/
theorem lagMoment_endpoint_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (n : Nat) :
    leEv (CReal.sub (lagMoment hw0 hw1 loop 0) (lagMoment hw0 hw1 loop n))
      (CReal.mul (ofQ' (Q'.ofNat n))
        (CReal.sub (lagMoment hw0 hw1 loop 0) (lagMoment hw0 hw1 loop 1))) :=
  CRealDiscreteConvexity.endpoint_drop_le_nat_mul_first (lagMoment hw0 hw1 loop)
    (lagMoment_convex hw0 hw1 loop) n

end YMGap.Continuum.BF4WilsonAllNomeMomentConvexity

#print axioms YMGap.Continuum.BF4WilsonAllNomeMomentConvexity.lagExpression
#print axioms YMGap.Continuum.BF4WilsonAllNomeMomentConvexity.lag_within
#print axioms YMGap.Continuum.BF4WilsonAllNomeMomentConvexity.lagMoment
#print axioms YMGap.Continuum.BF4WilsonAllNomeMomentConvexity.pair_lag
#print axioms YMGap.Continuum.BF4WilsonAllNomeMomentConvexity.secondDifferenceExpression
#print axioms YMGap.Continuum.BF4WilsonAllNomeMomentConvexity.secondDifference_within
#print axioms YMGap.Continuum.BF4WilsonAllNomeMomentConvexity.secondDifference_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeMomentConvexity.secondDifference_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeMomentConvexity.lagMoment_convex
#print axioms YMGap.Continuum.BF4WilsonAllNomeMomentConvexity.lagMoment_endpoint_bound
