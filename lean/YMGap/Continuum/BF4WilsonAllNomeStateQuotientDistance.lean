/-
# Explicit distance control for the original dyadic state quotients

The normalized unshifted root defects are Lipschitz in the original
completed squared distance, with an explicit rational cap. The supplied
preimage representatives pin to these exact states on the same carrier.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativeEquation
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear
import YMGap.Continuum.BF4WilsonAllNomeGraphDistance
import YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial

namespace YMGap.Continuum.BF4WilsonAllNomeStateQuotientDistance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (completedDist_sub_le)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility (root_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay (defect)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeEquation (stateQuotient)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity
  (preimageRepresentative preimageRepresentative_pin)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear (completedDist_smul)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (four_copies)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "d" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (YMGap.Continuum.BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)))

/-- Four times the square of the dyadic normalization, an explicit positive
rational cap for the squared-distance Lipschitz estimate. -/
def quotientCap (depth : Nat) : Q' :=
  ((Q'.ofNat (2^depth) * Q'.ofNat (2^depth)) * 4)

private theorem ofNat_pos_of_pos (n : Nat) (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

theorem quotientCap_positive (depth : Nat) : (0 : Q') < quotientCap depth := by
  unfold quotientCap
  have hc : (0 : Q') < Q'.ofNat (2^depth) :=
    ofNat_pos_of_pos (2^depth) (Nat.pow_pos (by decide))
  exact Q'.mul_pos (Q'.mul_pos hc hc) (by decide)

theorem quotientCap_nonnegative (depth : Nat) :
    (0 : Q') ≤ quotientCap depth :=
  Q'.le_of_lt (quotientCap_positive depth)

/-- The identity-minus-root part is Lipschitz with factor four in squared
distance: the two difference slots each contribute the original contraction
and the root contraction. -/
private theorem defect_distance_bound (depth : Nat) (x y : V) :
    RCle (d (defect hw0 hw1 depth x) (defect hw0 hw1 depth y))
      (RCscale 4 (d x y)) := by
  have hsub := completedDist_sub_le hw0 hw1 x y
    (root hw0 hw1 depth x) (root hw0 hw1 depth y)
  have hroot := root_distance_bound hw0 hw1 depth x y
  have hfour : RCle
      (RCadd (RCadd (d x y) (d x y)) (RCadd (d x y) (d x y)))
      (RCscale 4 (d x y)) := by
    rw [← four_copies]
    exact RCle_refl _
  unfold defect
  have hcombine := RCadd_le_add
    (RCadd_le_add (RCle_refl (d x y)) (RCle_refl (d x y)))
    (RCadd_le_add hroot hroot)
  exact RCle_trans hsub (RCle_trans hcombine hfour)

/-- Squared-distance Lipschitz control for the actual unshifted state
quotients `2^k (I-R_k)u` on the original completion. -/
theorem stateQuotient_distance_bound (depth : Nat) (x y : V) :
    RCle (d (stateQuotient hw0 hw1 depth x) (stateQuotient hw0 hw1 depth y))
      (RCscale (quotientCap depth) (d x y)) := by
  let c : Q' := Q'.ofNat (2^depth)
  have hc : (0 : Q') ≤ c*c := SumOfSquares.q_mul_self_nonneg c
  rw [show stateQuotient hw0 hw1 depth x =
      completedSmul hw0 hw1 c (defect hw0 hw1 depth x) by rfl,
    show stateQuotient hw0 hw1 depth y =
      completedSmul hw0 hw1 c (defect hw0 hw1 depth y) by rfl,
    completedDist_smul]
  have h := RCscale_mono hc (defect_distance_bound hw0 hw1 depth x y)
  rw [RCscale_RCscale] at h
  exact h

/-- The concrete Cauchy preimage used by derivative continuity represents
exactly the same unshifted state quotient. -/
theorem preimageRepresentative_stateQuotient (depth : Nat)
    (X : (YMGap.Continuum.BF4WilsonAllNomeSeminorm.seminorm hw0 hw1
      (width := width)).Cauchy) :
    Class (preimageRepresentative hw0 hw1 depth X) =
      stateQuotient hw0 hw1 depth (Class X) := by
  rw [preimageRepresentative_pin]
  rfl

#print axioms quotientCap
#print axioms quotientCap_positive
#print axioms quotientCap_nonnegative
#print axioms defect_distance_bound
#print axioms stateQuotient_distance_bound
#print axioms preimageRepresentative_stateQuotient

end YMGap.Continuum.BF4WilsonAllNomeStateQuotientDistance
