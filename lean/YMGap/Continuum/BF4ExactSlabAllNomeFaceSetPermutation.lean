/-
# Permutation invariance of normalized all-nome face-set laws

The original finite numerator and partition are invariant under a permutation
of their physical face list.  The reciprocal term therefore respects the same
permutation, so finite normalized values, finite covariances, their completed
expectations, and completed covariances are presentation-order invariant.

This removes only a finite-list presentation artifact.  It does not compare
different face multisets, change the action, take a volume or continuum limit,
or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabMixedAction
import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
import YMGap.Constructive.CRealLogRatCongruence

namespace YMGap.Continuum.BF4ExactSlabAllNomeFaceSetPermutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (eqv_close)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'}
    (hleft : a ≈ b) (hright : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

/-- Finite normalized values depend on the physical face multiset, not its
presentation order. -/
theorem finiteValue_perm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (extent : Nat) (left right : List Nat)
    (hleft : ∀ id, id ∈ left → id ∈ slabPhysicalFaceEdges extent)
    (hright : ∀ id, id ∈ right → id ∈ slabPhysicalFaceEdges extent)
    (hperm : left.Perm right) (p : RatPoly) (stage : Nat) :
    finiteValue w hw0 hw1 extent left hleft p stage ≈
      finiteValue w hw0 hw1 extent right hright p stage := by
  unfold finiteValue
  apply qmul (BF4ExactSlabMixedAction.moment_perm w _ extent p hperm)
  unfold reciprocalTerm PositiveRationalCauchyReciprocal.term partitionSample
  exact Q'.recipPos_eqv_congr _ _ _ _
    (BF4ExactSlabMixedAction.partition_perm w _ extent hperm)

/-- Connected finite covariances inherit face-order invariance. -/
theorem finiteCovariance_perm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (extent : Nat) (left right : List Nat)
    (hleft : ∀ id, id ∈ left → id ∈ slabPhysicalFaceEdges extent)
    (hright : ∀ id, id ∈ right → id ∈ slabPhysicalFaceEdges extent)
    (hperm : left.Perm right) (p q : RatPoly) (stage : Nat) :
    finiteCovariance w hw0 hw1 extent left hleft p q stage ≈
      finiteCovariance w hw0 hw1 extent right hright p q stage :=
  Q'.add_eqv_congr'
    (finiteValue_perm hw0 hw1 extent left right hleft hright hperm
      (polyMul p q) stage)
    (Q'.neg_eqv_congr _ _
      (qmul
        (finiteValue_perm hw0 hw1 extent left right hleft hright hperm p stage)
        (finiteValue_perm hw0 hw1 extent left right hleft hright hperm q stage)))

/-- Completed normalized expectations inherit the same exact finite-order
pin. -/
theorem expectation_perm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (extent : Nat) (left right : List Nat)
    (hleft : ∀ id, id ∈ left → id ∈ slabPhysicalFaceEdges extent)
    (hright : ∀ id, id ∈ right → id ∈ slabPhysicalFaceEdges extent)
    (hperm : left.Perm right) (p : RatPoly) :
    Equiv (expectation w hw0 hw1 extent left hleft p)
      (expectation w hw0 hw1 extent right hright p) :=
  Equiv_of_ofQ'_limit_close
    (finite_converges w hw0 hw1 extent left hleft p)
    (finite_converges w hw0 hw1 extent right hright p)
    (fun epsilon hepsilon =>
      ⟨0, fun stage _ => eqv_close
        (finiteValue_perm hw0 hw1 extent left right hleft hright hperm p stage)
        epsilon hepsilon⟩)

/-- Completed connected covariances are independent of physical face-list
presentation order. -/
theorem covariance_perm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (extent : Nat) (left right : List Nat)
    (hleft : ∀ id, id ∈ left → id ∈ slabPhysicalFaceEdges extent)
    (hright : ∀ id, id ∈ right → id ∈ slabPhysicalFaceEdges extent)
    (hperm : left.Perm right) (p q : RatPoly) :
    Equiv (covariance w hw0 hw1 extent left hleft p q)
      (covariance w hw0 hw1 extent right hright p q) :=
  Equiv_of_ofQ'_limit_close
    (finite_covariance_converges w hw0 hw1 extent left hleft p q)
    (finite_covariance_converges w hw0 hw1 extent right hright p q)
    (fun epsilon hepsilon =>
      ⟨0, fun stage _ => eqv_close
        (finiteCovariance_perm hw0 hw1 extent left right hleft hright hperm
          p q stage)
        epsilon hepsilon⟩)

end YMGap.Continuum.BF4ExactSlabAllNomeFaceSetPermutation

#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetPermutation.finiteValue_perm
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetPermutation.finiteCovariance_perm
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetPermutation.expectation_perm
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetPermutation.covariance_perm
