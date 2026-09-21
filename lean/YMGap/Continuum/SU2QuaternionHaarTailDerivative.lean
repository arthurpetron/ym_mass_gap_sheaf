/-
# Tail angular derivatives commute with constructive head Haar integration

Integrating an ordered quaternion head deletes four coordinates per block.
Consequently a derivative in surviving coordinate `i` is the image of the
original derivative in coordinate `4*n+i`.  This file proves that statement
coefficientwise, first for one head and then for an arbitrary number of heads,
and packages the corresponding angular-vector-field identity.  No support or
positivity hypothesis is involved.
-/

import YMGap.Continuum.SU2QuaternionAngularDerivative
import YMGap.Continuum.SU2QuaternionCoordinateColumnLift
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
import YMGap.Continuum.QuaternionHaarAngularCarrier
import YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini

namespace YMGap.Continuum.SU2QuaternionHaarTailDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer

local infix:50 " ≈ " => Q'.eqv

private theorem lowerExponentAt_drop_four (coordinate : Nat) (monomial : List Nat) :
    lowerExponentAt coordinate (monomial.drop 4) =
      (lowerExponentAt (4 + coordinate) monomial).drop 4 := by
  rw [Nat.add_comm 4 coordinate]
  cases monomial with
  | nil => cases coordinate <;> rfl
  | cons a rest =>
      cases rest with
      | nil => cases coordinate <;> rfl
      | cons b rest =>
          cases rest with
          | nil => cases coordinate <;> rfl
          | cons c rest =>
              cases rest with
              | nil => cases coordinate <;> rfl
              | cons d rest => rfl

private theorem exponentAt_drop_four (coordinate : Nat) (monomial : List Nat) :
    exponentAt (monomial.drop 4) coordinate =
      exponentAt monomial (4 + coordinate) := by
  simpa [Nat.add_comm] using exponentAt_drop monomial 4 coordinate

private theorem headQuaternionMoment_lower_tail (coordinate : Nat) (monomial : List Nat) :
    headQuaternionMoment (lowerExponentAt (4 + coordinate) monomial) =
      headQuaternionMoment monomial := by
  rw [Nat.add_comm 4 coordinate]
  cases monomial with
  | nil => rfl
  | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b rest =>
          cases rest with
          | nil => rfl
          | cons c rest =>
              cases rest with
              | nil => rfl
              | cons d rest => rfl

private theorem oneHead_derivative_termwise (coordinate : Nat) : ∀ polynomial : RatPoly,
    RatPolyTermwiseEqv
      (ratDerivative coordinate (partialHaarHead polynomial))
      (partialHaarHead (ratDerivative (4 + coordinate) polynomial))
  | [] => True.intro
  | term :: rest => by
      change
        lowerExponentAt coordinate (term.1.drop 4) =
            (lowerExponentAt (4 + coordinate) term.1).drop 4 ∧
          Q'.ofNat (exponentAt (term.1.drop 4) coordinate) *
              (term.2 * headQuaternionMoment term.1) ≈
            (Q'.ofNat (exponentAt term.1 (4 + coordinate)) * term.2) *
              headQuaternionMoment (lowerExponentAt (4 + coordinate) term.1) ∧
          RatPolyTermwiseEqv
            (ratDerivative coordinate (partialHaarHead rest))
            (partialHaarHead (ratDerivative (4 + coordinate) rest))
      refine ⟨lowerExponentAt_drop_four coordinate term.1, ?_,
        oneHead_derivative_termwise coordinate rest⟩
      rw [exponentAt_drop_four, headQuaternionMoment_lower_tail]
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- One integrated quaternion head shifts every surviving derivative index by
exactly four.  Zero-exponent derivative terms are handled by coefficient
equivalence rather than deleted from the polynomial list. -/
theorem ratDerivative_partialHaarHead (coordinate : Nat) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (ratDerivative coordinate (partialHaarHead polynomial))
      (partialHaarHead (ratDerivative (4 + coordinate) polynomial)) := by
  intro weight
  exact ratWeightedSum_termwise_eqv weight
    (oneHead_derivative_termwise coordinate polynomial)

/-- Differentiation in an arbitrary surviving coordinate commutes through an
arbitrary ordered head-Haar prefix, with the original coordinate shifted by
`4 * heads`. -/
theorem ratDerivative_partialHaarHeads : ∀ (heads coordinate : Nat) (polynomial : RatPoly),
    RatPolyCoeffEqv
      (ratDerivative coordinate (partialHaarHeads heads polynomial))
      (partialHaarHeads heads (ratDerivative (4 * heads + coordinate) polynomial))
  | 0, coordinate, polynomial => by
      simpa only [partialHaarHeads, Nat.mul_zero, Nat.zero_add] using
        (RatPolyCoeffEqv.refl (ratDerivative coordinate polynomial))
  | heads + 1, coordinate, polynomial => by
      refine (ratDerivative_partialHaarHeads heads coordinate
        (partialHaarHead polynomial)).trans ?_
      refine (partialHaarHeads_congr heads
        (ratDerivative_partialHaarHead (4 * heads + coordinate) polynomial)).trans ?_
      rw [show 4 + (4 * heads + coordinate) = 4 * (heads + 1) + coordinate by omega]
      exact RatPolyCoeffEqv.refl _

/-- Ordered head integration distributes exactly over polynomial addition. -/
theorem partialHaarHeads_add : ∀ (heads : Nat) (left right : RatPoly),
    partialHaarHeads heads (polyAdd left right) =
      polyAdd (partialHaarHeads heads left) (partialHaarHeads heads right)
  | 0, _, _ => rfl
  | heads + 1, left, right => by
      simp only [partialHaarHeads, partialHaarHead_add,
        partialHaarHeads_add heads]

/-- Ordered head integration commutes coefficientwise with rational scaling. -/
theorem partialHaarHeads_smul : ∀ (heads : Nat) (scale : Q') (polynomial : RatPoly),
    RatPolyCoeffEqv
      (partialHaarHeads heads (polySmul scale polynomial))
      (polySmul scale (partialHaarHeads heads polynomial))
  | 0, _, _ => RatPolyCoeffEqv.refl _
  | heads + 1, scale, polynomial =>
      (partialHaarHeads_congr heads
        (partialHaarHead_smul scale polynomial)).trans
          (partialHaarHeads_smul heads scale (partialHaarHead polynomial))

/-- Ordered head integration commutes coefficientwise with negation. -/
theorem partialHaarHeads_neg (heads : Nat) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads (polyNeg polynomial))
      (polyNeg (partialHaarHeads heads polynomial)) :=
  (partialHaarHeads_congr heads (neg_smul polynomial)).trans
    ((partialHaarHeads_smul heads (-1) polynomial).trans
      (neg_smul (partialHaarHeads heads polynomial)).symm)

private theorem partialHaarHeads_tail_var (heads coordinate : Nat) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads
        (polyMul (polyVar (4 * heads + coordinate)) polynomial))
      (polyMul (polyVar coordinate) (partialHaarHeads heads polynomial)) := by
  rw [← lift_var heads coordinate]
  exact (partialHaarHeads_congr heads (RatPolyCoeffEqv.mul_comm _ _)).trans
    ((partialHaarHeads_mul_lift heads polynomial (polyVar coordinate)).trans
      (RatPolyCoeffEqv.mul_comm _ _))

/-- The tail angular vector field commutes with arbitrary ordered head-Haar
integration.  Both original coordinate indices are shifted past all integrated
quaternion blocks. -/
theorem angularDerivative_partialHaarHeads
    (heads i j : Nat) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (partialHaarHeads heads polynomial))
      (partialHaarHeads heads
        (angularDerivative (4 * heads + i) (4 * heads + j) polynomial)) := by
  unfold angularDerivative
  let di := ratDerivative_partialHaarHeads heads i polynomial
  let dj := ratDerivative_partialHaarHeads heads j polynomial
  refine ((dj.mul_left (polyVar i)).add
    ((di.mul_left (polyVar j)).smul (-1))).trans ?_
  let tj := polyMul (polyVar (4 * heads + j))
    (ratDerivative (4 * heads + i) polynomial)
  have hti := partialHaarHeads_tail_var heads i
    (ratDerivative (4 * heads + j) polynomial)
  have htj := partialHaarHeads_tail_var heads j
    (ratDerivative (4 * heads + i) polynomial)
  refine (hti.symm.add (((htj.symm).smul (-1)).trans
    (partialHaarHeads_smul heads (-1) tj).symm)).trans ?_
  rw [← partialHaarHeads_add]
  exact RatPolyCoeffEqv.refl _

private theorem ratDerivative_blockIndependent_zero
    (block component : Nat) (hcomponent : component < 4) :
    ∀ (polynomial : RatPoly), QuaternionBlockIndependent block polynomial →
      RatPolyCoeffEqv
        (ratDerivative (4 * block + component) polynomial) polyZero
  | [], _ => RatPolyCoeffEqv.refl polyZero
  | term :: rest, hindependent => by
      have hzero : exponentAt term.1 (4 * block + component) = 0 := by
        have h := exponentAt_clearQuaternionBlock_self term.1 block component hcomponent
        rw [hindependent term List.mem_cons_self] at h
        exact h
      have hrest : QuaternionBlockIndependent block rest := by
        intro other hother
        exact hindependent other (List.mem_cons_of_mem term hother)
      intro weight
      change
        (Q'.ofNat (exponentAt term.1 (4 * block + component)) * term.2) *
              weight (lowerExponentAt (4 * block + component) term.1) +
            ratWeightedSum weight
              (ratDerivative (4 * block + component) rest) ≈ 0
      rw [hzero]
      have hcoefficient :
          (Q'.ofNat 0 * term.2) *
              weight (lowerExponentAt (4 * block + component) term.1) ≈ 0 := by
        refine Q'.eqv_trans _
          (0 * weight (lowerExponentAt (4 * block + component) term.1)) _ ?_
          (Q'.zero_mul_eqv _)
        exact Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_trans _ (0 * term.2) _
            (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
            (Q'.zero_mul_eqv _))
      refine Q'.eqv_trans _
        (0 + ratWeightedSum weight
          (ratDerivative (4 * block + component) rest)) _
        (Q'.add_eqv_congr' hcoefficient (Q'.eqv_refl _)) ?_
      exact Q'.eqv_trans _ _ _
        (QPoly.q_zero_add_eqv _)
        (ratDerivative_blockIndependent_zero block component hcomponent rest hrest weight)

/-- An angular vector field in a quaternion block annihilates every polynomial
independent of that block.  The conclusion is coefficientwise, so retained
zero-coefficient derivative terms cause no syntactic obstruction. -/
theorem angularDerivative_blockIndependent_zero
    {block i j : Nat} {polynomial : RatPoly}
    (hi : i < 4) (hj : j < 4)
    (hp : QuaternionBlockIndependent block polynomial) :
    RatPolyCoeffEqv
      (angularDerivative (4 * block + i) (4 * block + j) polynomial)
      polyZero := by
  unfold angularDerivative
  have hfirst : RatPolyCoeffEqv
      (polyMul (polyVar (4 * block + i))
        (ratDerivative (4 * block + j) polynomial)) polyZero :=
    ((ratDerivative_blockIndependent_zero block j hj polynomial hp).mul_left
      (polyVar (4 * block + i))).trans
        (RatPolyCoeffEqv.mul_zero_right _)
  have hsecond : RatPolyCoeffEqv
      (polySmul (-1) (polyMul (polyVar (4 * block + j))
        (ratDerivative (4 * block + i) polynomial))) polyZero :=
    ((((ratDerivative_blockIndependent_zero block i hi polynomial hp).mul_left
      (polyVar (4 * block + j))).trans
        (RatPolyCoeffEqv.mul_zero_right _)).smul (-1)).trans
          (RatPolyCoeffEqv.smul_zero (-1))
  exact (hfirst.add hsecond).trans (RatPolyCoeffEqv.zero_add polyZero)

end YMGap.Continuum.SU2QuaternionHaarTailDerivative

#print axioms YMGap.Continuum.SU2QuaternionHaarTailDerivative.ratDerivative_partialHaarHead
#print axioms YMGap.Continuum.SU2QuaternionHaarTailDerivative.ratDerivative_partialHaarHeads
#print axioms YMGap.Continuum.SU2QuaternionHaarTailDerivative.partialHaarHeads_add
#print axioms YMGap.Continuum.SU2QuaternionHaarTailDerivative.partialHaarHeads_smul
#print axioms YMGap.Continuum.SU2QuaternionHaarTailDerivative.partialHaarHeads_neg
#print axioms YMGap.Continuum.SU2QuaternionHaarTailDerivative.angularDerivative_partialHaarHeads
#print axioms YMGap.Continuum.SU2QuaternionHaarTailDerivative.angularDerivative_blockIndependent_zero
