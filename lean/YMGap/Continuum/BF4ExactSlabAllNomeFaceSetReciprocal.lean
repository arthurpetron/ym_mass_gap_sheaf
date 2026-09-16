/-
# Reciprocal of each selected physical-face action at every positive nome

The original unweighted heat prefixes have a positive certified floor
after headCutoff(w). For any physical face list, their product therefore
has floor headFloor(w)^length, retaining all shared Haar variables.
Sampling only this explicit tail gives a positive rational Cauchy stream.
Its reciprocal has an explicit modulus and cancels the ORIGINAL selected
action limit, not merely a newly introduced shifted limit.

The floor depends on the nome and face count. No small-nome guard, spatial
decay, uniform thermodynamic bound, or physical mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
import YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
import YMGap.Continuum.PositiveRationalCauchyReciprocal
import YMGap.Continuum.BoundedRationalCauchyProduct

namespace YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- Computed floor for the chosen list; repeated faces count repeatedly. -/
def partitionFloor (w : Q') (ids : List Nat) : Q' := (headFloor w) ^ ids.length

theorem partitionFloor_pos {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (ids : List Nat) : (0 : Q') < partitionFloor w ids :=
  HKPos.pow_pos (headFloor_positive hw0 hw1) ids.length

/-- Late original partitions, with every selected physical heat factor retained. -/
theorem partition_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (K : Nat) (hK : headCutoff w ≤ K) :
    partitionFloor w ids ≤ heatProductHaar w (blocks extent) extent ids K := by
  have h := headProduct_weighted_floor hw0 hw1 K extent hK (Certificate.one (blocks extent)) ids hids
  have he : (headFloor w) ^ ids.length * quaternionHaar (blocks extent) polyOne ≈
      partitionFloor w ids :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (QPolyHaarPositiveSubstitution.haar_one _))
      (Q'.mul_one_eqv _)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.one_mul _))))

/-- The fixed explicit cutoff removes no face and changes no action factor. -/
def partitionSample (w : Q') (extent : Nat) (ids : List Nat) (n : Nat) : Q' :=
  heatProductHaar w (blocks extent) extent ids (headCutoff w + n)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent : Nat) (ids : List Nat)

/-- The existing partition modulus suffices for the shifted cutoff stream. -/
def partitionSampleCauchy : CReal.QCauchy (partitionSample w extent ids) where
  M := (heatProductHaarCauchy w hw0 hw1 (blocks extent) extent ids).M
  bound := by
    intro epsilon he p q hp hq
    exact (heatProductHaarCauchy w hw0 hw1 (blocks extent) extent ids).bound epsilon he
      (headCutoff w + p) (headCutoff w + q)
      (Nat.le_trans hp (Nat.le_add_left _ _))
      (Nat.le_trans hq (Nat.le_add_left _ _))

/-- Direct Cauchy comparison pins the shifted limit to the original one. -/
theorem partitionSampleLimit_eq_partition : CReal.Equiv
    (CReal.ofQ'CauchySeq _ (partitionSampleCauchy w hw0 hw1 extent ids))
    (heatProductHaarLimit w hw0 hw1 (blocks extent) extent ids) := by
  let c := heatProductHaarCauchy w hw0 hw1 (blocks extent) extent ids
  intro epsilon he
  refine ⟨c.M epsilon, fun n hn => ?_⟩
  exact c.bound epsilon he
    (headCutoff w + CReal.QMhat _ (partitionSampleCauchy w hw0 hw1 extent ids) n)
    (CReal.QMhat _ c n)
    (Nat.le_trans hn (Nat.le_trans (CReal.self_le_QMhat _ _ n) (Nat.le_add_left _ _)))
    (Nat.le_trans hn (CReal.self_le_QMhat _ _ n))

variable (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)

include hw0 hw1 hids in
theorem partitionSample_floor (n : Nat) : partitionFloor w ids ≤ partitionSample w extent ids n :=
  partition_floor hw0 hw1 extent ids hids (headCutoff w + n) (Nat.le_add_right _ _)

/-- Computed reciprocals of the original late-cutoff partitions. -/
def reciprocalTerm (n : Nat) : Q' :=
  PositiveRationalCauchyReciprocal.term (partitionFloor w ids) (partitionFloor_pos hw0 hw1 ids)
    (partitionSample_floor w hw0 hw1 extent ids hids) n

/-- Source reciprocal-stream modulus, with tolerance scaled by the squared inverse floor. -/
def reciprocalStreamCauchy : CReal.QCauchy (reciprocalTerm w hw0 hw1 extent ids hids) :=
  PositiveRationalCauchyReciprocal.reciprocalCauchy (partitionSampleCauchy w hw0 hw1 extent ids)
    (partitionFloor w ids) (partitionFloor_pos hw0 hw1 ids)
    (partitionSample_floor w hw0 hw1 extent ids hids)

def reciprocal : CReal :=
  PositiveRationalCauchyReciprocal.value (partitionSampleCauchy w hw0 hw1 extent ids)
    (partitionFloor w ids) (partitionFloor_pos hw0 hw1 ids)
    (partitionSample_floor w hw0 hw1 extent ids hids)

/-- Explicit modulus for the ACTUAL completed reciprocal's approximation stream. -/
def reciprocalCauchy : CReal.QCauchy (reciprocal w hw0 hw1 extent ids hids).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _
    (reciprocalStreamCauchy w hw0 hw1 extent ids hids)

theorem reciprocal_approx_pos (n : Nat) : (0 : Q') < (reciprocal w hw0 hw1 extent ids hids).approx n :=
  PositiveRationalCauchyReciprocal.value_approx_pos _ _ _ _ n

/-- Exact cancellation against the EXISTING original selected-face partition limit. -/
theorem partition_cancellation : CReal.Equiv
    (CReal.mul (heatProductHaarLimit w hw0 hw1 (blocks extent) extent ids)
      (reciprocal w hw0 hw1 extent ids hids)) CReal.cone :=
  (Pivot2.mul_congr_left (partitionSampleLimit_eq_partition w hw0 hw1 extent ids).symm).trans
    (PositiveRationalCauchyReciprocal.mul_value _ _ _ _)

end YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal

#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.partitionFloor
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.partitionFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.partition_floor
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.partitionSample
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.partitionSampleCauchy
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.partitionSampleLimit_eq_partition
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.partitionSample_floor
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.reciprocalTerm
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.reciprocalStreamCauchy
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.reciprocal
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.reciprocalCauchy
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.reciprocal_approx_pos
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal.partition_cancellation
