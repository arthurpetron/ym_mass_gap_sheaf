/-
# Rational operations on the same spatial union Cauchy carrier

Dense linearity is transported to a computed common support base. The checked
fixed-stage distance estimates pass through the existing cutoff and spatial
limits, then through the same common-base pins. They supply the existing
explicit-modulus completion maps for literal addition and rational scaling.

No bound on the support bases of a whole stream is chosen. The resulting
operations use the existing UnionCompletion; completed bilinearity and real
scalar extension are subsequent consumers, not hypotheses here.
-/

import YMGap.Continuum.BF4SpatialUnionPairingData
import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear

namespace YMGap.Continuum.BF4SpatialUnionLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4SpatialUnion
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData (pairing_symm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (addSpan smulSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth recenter)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "P" => pairing hw0 hw1 hsmall hd hs
local notation "d" => distSq hw0 hw1 hsmall hd hs
local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs

attribute [local irreducible] pairing distSq spatialPairing spatialDistSq jointDistSq

theorem pairing_add_left (x y z : Stage) :
    Equiv (P (addStage x y) z) (add (P x z) (P y z)) := by
  let N := max (max x.base y.base) z.base
  have hx : x.base ≤ N := by omega
  have hy : y.base ≤ N := by omega
  have hz : z.base ≤ N := by omega
  have h := pairing_at_base hw0 hw1 hsmall hd hs (addStage x y) z N
    (Nat.max_le.mpr ⟨hx, hy⟩) hz
  exact h.trans ((spatialPairing_add_left hw0 hw1 N hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (atBase y hy) (atBase z hz)).trans
      (Equiv_add (pairing_at_base hw0 hw1 hsmall hd hs x z N hx hz)
        (pairing_at_base hw0 hw1 hsmall hd hs y z N hy hz)).symm)

theorem pairing_add_right (x y z : Stage) :
    Equiv (P x (addStage y z)) (add (P x y) (P x z)) :=
  (pairing_symm hw0 hw1 hsmall hd hs x (addStage y z)).trans
    ((pairing_add_left hw0 hw1 hsmall hd hs y z x).trans
      (Equiv_add (pairing_symm hw0 hw1 hsmall hd hs y x)
        (pairing_symm hw0 hw1 hsmall hd hs z x)))

theorem pairing_smul_left (c : Q') (x y : Stage) :
    Equiv (P (smulStage c x) y) (mul (ofQ' c) (P x y)) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have h := pairing_at_base hw0 hw1 hsmall hd hs (smulStage c x) y N hx hy
  simp only [atBase_smul] at h
  exact h.trans ((spatialPairing_smul_left hw0 hw1 N hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) c (atBase x hx) (atBase y hy)).trans
      (TrigSignedAdd.mul_congr_right
        (pairing_at_base hw0 hw1 hsmall hd hs x y N hx hy)).symm)

theorem pairing_smul_right (c : Q') (x y : Stage) :
    Equiv (P x (smulStage c y)) (mul (ofQ' c) (P x y)) :=
  (pairing_symm hw0 hw1 hsmall hd hs x (smulStage c y)).trans
    ((pairing_smul_left hw0 hw1 hsmall hd hs c y x).trans
      (TrigSignedAdd.mul_congr_right (pairing_symm hw0 hw1 hsmall hd hs y x)))

theorem pairing_zero_left (x : Stage) : Equiv (P zeroStage x) czero := by
  have h := pairing_at_base hw0 hw1 hsmall hd hs zeroStage x x.base
    x.positive (Nat.le_refl _)
  simp only [atBase_zero, atBase_self] at h
  have hz := spatialPairing_difference_left hw0 hw1 x.base hsmall hd hs x.positive
    (zero x.base) (zero x.base) x.value
  change Equiv (spatialPairing hw0 hw1 x.base hsmall hd hs x.positive (zero x.base) x.value)
    (sub (spatialPairing hw0 hw1 x.base hsmall hd hs x.positive (zero x.base) x.value)
      (spatialPairing hw0 hw1 x.base hsmall hd hs x.positive (zero x.base) x.value)) at hz
  exact h.trans (hz.trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv _)))

theorem pairing_zero_right (x : Stage) : Equiv (P x zeroStage) czero :=
  (pairing_symm hw0 hw1 hsmall hd hs x zeroStage).trans
    (pairing_zero_left hw0 hw1 hsmall hd hs x)

/-- The literal union difference has exactly the original squared distance. -/
theorem distance_difference (x y : Stage) :
    Equiv (d x y) (P (difference x y) (difference x y)) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have hp : Equiv (P (difference x y) (difference x y))
      (spatialDistSq hw0 hw1 N hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
        (atBase x hx) (atBase y hy)) := by
    unfold spatialDistSq
    simpa only [atBase_difference] using
      pairing_at_base hw0 hw1 hsmall hd hs (difference x y) (difference x y) N
        (Nat.max_le.mpr ⟨hx, hy⟩) (Nat.max_le.mpr ⟨hx, hy⟩)
  exact (distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy).trans hp.symm

private theorem joint_distance_add (width : Nat) (x x' y y' : PhysicalSpan width) :
    leEv (jointDistSq hw0 hw1 width (addSpan x y) (addSpan x' y'))
      (add (add (jointDistSq hw0 hw1 width x x') (jointDistSq hw0 hw1 width x x'))
        (add (jointDistSq hw0 hw1 width y y') (jointDistSq hw0 hw1 width y y'))) :=
  leEv_of_convergesTo_le
    (distSq_converges_joint hw0 hw1 width (addSpan x y) (addSpan x' y'))
    (TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (distSq_converges_joint hw0 hw1 width x x')
        (distSq_converges_joint hw0 hw1 width x x'))
      (TrigAddCReal.convergesTo_add (distSq_converges_joint hw0 hw1 width y y')
        (distSq_converges_joint hw0 hw1 width y y')))
    (fun stage => BF4ExactSlabFixedSpatialIntrinsicLinear.distSq_add
      hw0 hw1 width stage x x' y y')

private theorem joint_distance_smul (width : Nat) (c : Q') (x y : PhysicalSpan width) :
    Equiv (jointDistSq hw0 hw1 width (smulSpan c x) (smulSpan c y))
      (mul (ofQ' (c*c)) (jointDistSq hw0 hw1 width x y)) :=
  Equiv_of_limit_of_equal
    (fun stage => BF4ExactSlabFixedSpatialIntrinsicLinear.distSq_smul hw0 hw1 width stage c x y)
    (distSq_converges_joint hw0 hw1 width (smulSpan c x) (smulSpan c y))
    (convergesTo_const_mul (ofQ' (c*c)) (distSq_converges_joint hw0 hw1 width x y))

private theorem spatial_distance_add (base : Nat) (hb : 0 < base)
    (x x' y y' : PhysicalSpan base) :
    leEv (spatialDistSq hw0 hw1 base hsmall hd hs hb (addSpan x y) (addSpan x' y'))
      (add
        (add (spatialDistSq hw0 hw1 base hsmall hd hs hb x x')
          (spatialDistSq hw0 hw1 base hsmall hd hs hb x x'))
        (add (spatialDistSq hw0 hw1 base hsmall hd hs hb y y')
          (spatialDistSq hw0 hw1 base hsmall hd hs hb y y'))) :=
  leEv_of_convergesTo_le
    (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb (addSpan x y) (addSpan x' y'))
    (TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x x')
        (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x x'))
      (TrigAddCReal.convergesTo_add (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb y y')
        (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb y y')))
    (fun r => by
      simp only [recenter_add]
      exact joint_distance_add hw0 hw1 (paddedWidth base r)
        (recenter r x) (recenter r x') (recenter r y) (recenter r y'))

private theorem spatial_distance_smul (base : Nat) (hb : 0 < base)
    (c : Q') (x y : PhysicalSpan base) :
    Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb (smulSpan c x) (smulSpan c y))
      (mul (ofQ' (c*c)) (spatialDistSq hw0 hw1 base hsmall hd hs hb x y)) :=
  Equiv_of_limit_of_equal
    (fun r => by
      simp only [recenter_smul]
      exact joint_distance_smul hw0 hw1 (paddedWidth base r) c (recenter r x) (recenter r y))
    (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb (smulSpan c x) (smulSpan c y))
    (convergesTo_const_mul (ofQ' (c*c)) (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x y))

theorem distSq_add (x x' y y' : Stage) :
    leEv (d (addStage x y) (addStage x' y'))
      (add (add (d x x') (d x x')) (add (d y y') (d y y'))) := by
  let N := max (max x.base x'.base) (max y.base y'.base)
  have hx : x.base ≤ N := by omega
  have hx' : x'.base ≤ N := by omega
  have hy : y.base ≤ N := by omega
  have hy' : y'.base ≤ N := by omega
  have hsum := distSq_at_base hw0 hw1 hsmall hd hs (addStage x y) (addStage x' y') N
    (Nat.max_le.mpr ⟨hx, hy⟩) (Nat.max_le.mpr ⟨hx', hy'⟩)
  have hxx := distSq_at_base hw0 hw1 hsmall hd hs x x' N hx hx'
  have hyy := distSq_at_base hw0 hw1 hsmall hd hs y y' N hy hy'
  exact leEv_trans (leEv_of_equiv hsum)
    (leEv_trans (spatial_distance_add hw0 hw1 hsmall hd hs N
      (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (atBase x' hx')
      (atBase y hy) (atBase y' hy'))
      (leEv_of_equiv (Equiv_add (Equiv_add hxx hxx) (Equiv_add hyy hyy)).symm))

theorem distSq_smul (c : Q') (x y : Stage) :
    Equiv (d (smulStage c x) (smulStage c y)) (mul (ofQ' (c*c)) (d x y)) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have h := distSq_at_base hw0 hw1 hsmall hd hs (smulStage c x) (smulStage c y) N hx hy
  simp only [atBase_smul] at h
  exact h.trans ((spatial_distance_smul hw0 hw1 hsmall hd hs N
    (Nat.lt_of_lt_of_le x.positive hx) c (atBase x hx) (atBase y hy)).trans
      (TrigSignedAdd.mul_congr_right
        (distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy)).symm)

def addition : (D).BinaryQuadraticLipschitz where
  toFun := addStage
  contraction := distSq_add hw0 hw1 hsmall hd hs

def scalarContinuous (c : Q') : (D).ModulusContinuous where
  toFun := smulStage c
  tolerance := scalarTolerance c
  tolerance_pos := fun _ => scalarTolerance_pos c
  contraction := by
    intro epsilon he x y h
    have hc : leEv czero (ofQ' (c*c)) :=
      leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg c)
    exact leEv_trans (leEv_of_equiv (distSq_smul hw0 hw1 hsmall hd hs c x y))
      (leEv_trans (leEv_mul_nonneg_left hc h)
        (leEv_le_ofQ'_of_approx_le (fun _ => scalarTolerance_bound c he)))

def addCauchy (X Y : (D).Cauchy) : (D).Cauchy :=
  (addition hw0 hw1 hsmall hd hs).mapCauchy X Y

def smulCauchy (c : Q') (X : (D).Cauchy) : (D).Cauchy :=
  (scalarContinuous hw0 hw1 hsmall hd hs c).mapCauchy X

theorem addCauchy_seq (X Y : (D).Cauchy) (n : Nat) :
    (addCauchy hw0 hw1 hsmall hd hs X Y).seq n = addStage (X.seq n) (Y.seq n) := rfl

theorem smulCauchy_seq (c : Q') (X : (D).Cauchy) (n : Nat) :
    (smulCauchy hw0 hw1 hsmall hd hs c X).seq n = smulStage c (X.seq n) := rfl

/-- Both input moduli remain data, evaluated at the explicit quarter tolerance. -/
theorem addCauchy_modulus (X Y : (D).Cauchy) (epsilon : Q') :
    (addCauchy hw0 hw1 hsmall hd hs X Y).modulus epsilon =
      max (X.modulus (HalfPow.half*(HalfPow.half*epsilon)))
        (Y.modulus (HalfPow.half*(HalfPow.half*epsilon))) := rfl

theorem smulCauchy_modulus (c : Q') (X : (D).Cauchy) (epsilon : Q') :
    (smulCauchy hw0 hw1 hsmall hd hs c X).modulus epsilon =
      X.modulus (scalarTolerance c epsilon) := rfl

def completedAdd : UnionCompletion hw0 hw1 hsmall hd hs →
    UnionCompletion hw0 hw1 hsmall hd hs → UnionCompletion hw0 hw1 hsmall hd hs :=
  (addition hw0 hw1 hsmall hd hs).completionMap

def completedSmul (c : Q') : UnionCompletion hw0 hw1 hsmall hd hs →
    UnionCompletion hw0 hw1 hsmall hd hs :=
  (scalarContinuous hw0 hw1 hsmall hd hs c).completionMap

def completedNeg : UnionCompletion hw0 hw1 hsmall hd hs → UnionCompletion hw0 hw1 hsmall hd hs :=
  completedSmul hw0 hw1 hsmall hd hs (-1)

theorem completedAdd_mk (X Y : (D).Cauchy) :
    completedAdd hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X)
      (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk (D).completionSetoid (addCauchy hw0 hw1 hsmall hd hs X Y) := rfl

theorem completedSmul_mk (c : Q') (X : (D).Cauchy) :
    completedSmul hw0 hw1 hsmall hd hs c (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (smulCauchy hw0 hw1 hsmall hd hs c X) := rfl

theorem completedAdd_embedStage (x y : Stage) :
    completedAdd hw0 hw1 hsmall hd hs (embedStage hw0 hw1 hsmall hd hs x)
      (embedStage hw0 hw1 hsmall hd hs y) = embedStage hw0 hw1 hsmall hd hs (addStage x y) := rfl

theorem completedSmul_embedStage (c : Q') (x : Stage) :
    completedSmul hw0 hw1 hsmall hd hs c (embedStage hw0 hw1 hsmall hd hs x) =
      embedStage hw0 hw1 hsmall hd hs (smulStage c x) := rfl

#print axioms pairing_add_left
#print axioms pairing_add_right
#print axioms pairing_smul_left
#print axioms pairing_smul_right
#print axioms pairing_zero_left
#print axioms pairing_zero_right
#print axioms distance_difference
#print axioms distSq_add
#print axioms distSq_smul
#print axioms addition
#print axioms scalarContinuous
#print axioms addCauchy
#print axioms smulCauchy
#print axioms addCauchy_seq
#print axioms smulCauchy_seq
#print axioms addCauchy_modulus
#print axioms smulCauchy_modulus
#print axioms completedAdd
#print axioms completedSmul
#print axioms completedNeg
#print axioms completedAdd_mk
#print axioms completedSmul_mk
#print axioms completedAdd_embedStage
#print axioms completedSmul_embedStage

end YMGap.Continuum.BF4SpatialUnionLinear
