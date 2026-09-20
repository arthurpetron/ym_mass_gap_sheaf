/-
# Common-offset streams for original finite expectations

Different nomes may start their normalized cutoff streams at different head
cutoffs.  This file reindexes both streams at one common physical cutoff
without changing the existing expectation or its Cauchy modulus.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
import YMGap.Constructive.CRealLogRatCongruence

namespace YMGap.Continuum.BF4ExactSlabCommonCutoffExpectations

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

def commonValue (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (K0 n : Nat) : Q' :=
  finiteValue w hw0 hw1 extent ids hids p (K0 - headCutoff w + n)

theorem common_cutoff_identity {w : Q'} {K0 n : Nat}
    (hK0 : headCutoff w ≤ K0) :
    headCutoff w + (K0 - headCutoff w + n) = K0 + n := by
  omega

theorem commonValue_formula (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (K0 n : Nat) (hK0 : headCutoff w ≤ K0) :
    Q'.eqv (commonValue w hw0 hw1 extent ids hids p K0 n)
      (numerator w (blocks extent) extent ids p (K0+n) *
        Q'.recipPos (heatProductHaar w (blocks extent) extent ids (K0+n))
          (Q'.pos_of_lt_of_le
            (partitionFloor_pos hw0 hw1 ids)
            (partition_floor hw0 hw1 extent ids hids (K0+n)
              (Nat.le_trans hK0 (Nat.le_add_right _ _))))) := by
  unfold commonValue finiteValue reciprocalTerm
  unfold PositiveRationalCauchyReciprocal.term partitionSample
  apply Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_of_eq (congrArg (numerator w (blocks extent) extent ids p) (common_cutoff_identity hK0))))
  apply Q'.mul_eqv_congr_left
  apply Q'.recipPos_eqv_congr
  exact Q'.eqv_of_eq (congrArg (heatProductHaar w (blocks extent) extent ids) (common_cutoff_identity hK0))

def commonCauchy (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (K0 : Nat) :
    QCauchy (commonValue w hw0 hw1 extent ids hids p K0) where
  M := (finiteCauchy w hw0 hw1 extent ids hids p).M
  bound := by
    intro epsilon he i j hi hj
    exact (finiteCauchy w hw0 hw1 extent ids hids p).bound epsilon he
      (K0 - headCutoff w + i) (K0 - headCutoff w + j)
      (Nat.le_trans hi (Nat.le_add_left _ _))
      (Nat.le_trans hj (Nat.le_add_left _ _))

theorem commonValue_converges (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (K0 : Nat) :
    ConvergesTo
      (fun n => ofQ' (commonValue w hw0 hw1 extent ids hids p K0 n))
      (expectation w hw0 hw1 extent ids hids p) := by
  intro epsilon he
  obtain ⟨M, hM⟩ := finite_converges w hw0 hw1 extent ids hids p epsilon he
  refine ⟨M, fun n hn => ?_⟩
  exact hM (K0 - headCutoff w + n)
    (Nat.le_trans hn (Nat.le_add_left _ _))

#print axioms YMGap.Continuum.BF4ExactSlabCommonCutoffExpectations.commonValue
#print axioms YMGap.Continuum.BF4ExactSlabCommonCutoffExpectations.common_cutoff_identity
#print axioms YMGap.Continuum.BF4ExactSlabCommonCutoffExpectations.commonValue_formula
#print axioms YMGap.Continuum.BF4ExactSlabCommonCutoffExpectations.commonCauchy
#print axioms YMGap.Continuum.BF4ExactSlabCommonCutoffExpectations.commonValue_converges

end YMGap.Continuum.BF4ExactSlabCommonCutoffExpectations
