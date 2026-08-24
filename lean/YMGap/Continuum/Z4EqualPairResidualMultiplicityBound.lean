/-
# Spin-uniform fusion bounds after exposing an equal source pair

The generic local fusion bound charges every incident spin.  That is too
coarse for the BF4 all-spin cube row: the two equal source labels at a
touched link have already paid their heat-kernel activity, and charging them
again leaves a polynomial loss in the source spin.

This file removes that false loss.  Reading the sequential fusion constraints
backwards from the vacuum endpoint shows that every internal channel is
bounded by the sum of the labels *other than* the leading equal pair.  Thus
the one-, two-, and three-channel multiplicities are bounded by the same
cubic envelope built only from the residual labels, independently of the
equal spin and independently of the auxiliary cutoff.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound

namespace YMGap.Continuum.Z4EqualPairResidualMultiplicityBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Backward triangle bounds -/

/-- In an admissible SU(2) triple, either input is no larger than the other
input plus the output. -/
theorem fusionOK_left_le_right_add_output
    {left right output : Nat}
    (hfusion : fusionOK left right output = true) :
    left <= right + output := by
  have hrotated : fusionOK right output left = true := by
    rw [<- fusionOK_symm_bt right left output,
      <- fusionOK_symm_ab left right output]
    exact hfusion
  exact fusionOK_output_le_add hrotated

private theorem linear_le_spinSumCube (sum : Nat) :
    sum + 1 <= spinSumCube sum := by
  unfold spinSumCube
  have hpositive : 0 < sum + 1 := by omega
  have hsquare : sum + 1 <= (sum + 1) * (sum + 1) :=
    Nat.le_mul_of_pos_right (sum + 1) hpositive
  exact Nat.le_trans hsquare
    (Nat.mul_le_mul_left (sum + 1) hsquare)

private theorem square_le_spinSumCube (sum : Nat) :
    (sum + 1) * (sum + 1) <= spinSumCube sum := by
  unfold spinSumCube
  exact Nat.mul_le_mul_left (sum + 1)
    (Nat.le_mul_of_pos_right (sum + 1) (by omega))

/-! ## 2. Equal-pair channel counts depend only on residual labels -/

/-- Once the leading labels are equal, a four-valent fusion count is bounded
only by the two residual labels. -/
theorem oneChannelMultiplicity_equalPair_le_residualSpinSumCube
    (cutoff spin a b : Nat) :
    oneChannelMultiplicity cutoff spin spin a b <=
      spinSumCube (a + b) := by
  let sum := a + b
  let allowed : Nat -> Bool := fun x =>
    fusionOK spin spin x && fusionOK x a b
  have hsupport : forall x, allowed x = true -> x <= sum := by
    intro x hx
    have htail := ((Bool.and_eq_true _ _).mp hx).2
    exact fusionOK_left_le_right_add_output htail
  by_cases hcutoff : cutoff <= sum
  · exact Nat.le_trans
      (oneChannelMultiplicity_le cutoff spin spin a b)
      (Nat.le_trans (by omega) (linear_le_spinSumCube sum))
  · have hsum : sum <= cutoff := by omega
    have hstable :
        oneChannelMultiplicity cutoff spin spin a b =
          oneChannelMultiplicity sum spin spin a b := by
      change filterRangeCount cutoff allowed =
        filterRangeCount sum allowed
      exact filterRangeCount_stable_of_le allowed hsum hsupport
    rw [hstable]
    exact Nat.le_trans
      (oneChannelMultiplicity_le sum spin spin a b)
      (linear_le_spinSumCube sum)

/-- Once the leading labels are equal, a five-valent fusion count is bounded
only by the three residual labels. -/
theorem twoChannelMultiplicity_equalPair_le_residualSpinSumCube
    (cutoff spin a b c : Nat) :
    twoChannelMultiplicity cutoff spin spin a b c <=
      spinSumCube (a + b + c) := by
  let sum := a + b + c
  let allowed : Nat × Nat -> Bool := fun xy =>
    fusionOK spin spin xy.1 &&
      (fusionOK xy.1 a xy.2 && fusionOK xy.2 b c)
  have hySupport : forall x y, allowed (x, y) = true -> y <= sum := by
    intro x y hxy
    have hparts := (Bool.and_eq_true _ _).mp hxy
    have htail := (Bool.and_eq_true _ _).mp hparts.2
    have hy := fusionOK_left_le_right_add_output htail.2
    unfold sum
    omega
  have hxSupport : forall x y, allowed (x, y) = true -> x <= sum := by
    intro x y hxy
    have hparts := (Bool.and_eq_true _ _).mp hxy
    have htail := (Bool.and_eq_true _ _).mp hparts.2
    have hy := fusionOK_left_le_right_add_output htail.2
    have hx := fusionOK_left_le_right_add_output htail.1
    unfold sum
    omega
  by_cases hcutoff : cutoff <= sum
  · have hraw := twoChannelMultiplicity_le cutoff spin spin a b c
    have hsquare : (cutoff + 1) * (cutoff + 1) <=
        (sum + 1) * (sum + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact Nat.le_trans hraw
      (Nat.le_trans hsquare (square_le_spinSumCube sum))
  · have hsum : sum <= cutoff := by omega
    have hinner := pairPathCount_inner_stable cutoff allowed hsum hySupport
    have houter := pairPathCount_outer_stable
      (innerCutoff := sum) allowed hsum hxSupport
    have hstable :
        twoChannelMultiplicity cutoff spin spin a b c =
          twoChannelMultiplicity sum spin spin a b c := by
      calc
        twoChannelMultiplicity cutoff spin spin a b c =
            pairPathCount cutoff cutoff allowed :=
          twoChannelMultiplicity_eq_pairPathCount _ _ _ _ _ _
        _ = pairPathCount cutoff sum allowed := hinner
        _ = pairPathCount sum sum allowed := houter
        _ = twoChannelMultiplicity sum spin spin a b c :=
          (twoChannelMultiplicity_eq_pairPathCount _ _ _ _ _ _).symm
    rw [hstable]
    exact Nat.le_trans
      (twoChannelMultiplicity_le sum spin spin a b c)
      (square_le_spinSumCube sum)

/-- Once the leading labels are equal, the maximal six-valent fusion count
is bounded only by the four residual labels.  In particular, neither the
equal source spin nor the production auxiliary cutoff occurs in the bound. -/
theorem threeChannelMultiplicity_equalPair_le_residualSpinSumCube
    (cutoff spin a b c d : Nat) :
    threeChannelMultiplicity cutoff spin spin a b c d <=
      spinSumCube (a + b + c + d) := by
  let sum := a + b + c + d
  let allowed : Nat × Nat × Nat -> Bool := fun xyz =>
    fusionOK spin spin xyz.1 &&
      (fusionOK xyz.1 a xyz.2.1 &&
        (fusionOK xyz.2.1 b xyz.2.2 &&
          fusionOK xyz.2.2 c d))
  have hzSupport : forall x y z,
      allowed (x, y, z) = true -> z <= sum := by
    intro x y z hxyz
    dsimp only [allowed] at hxyz
    have hparts := (Bool.and_eq_true _ _).mp hxyz
    have htail := (Bool.and_eq_true _ _).mp hparts.2
    have hlast := (Bool.and_eq_true _ _).mp htail.2
    have hz := fusionOK_left_le_right_add_output hlast.2
    unfold sum
    omega
  have hySupport : forall x y z,
      allowed (x, y, z) = true -> y <= sum := by
    intro x y z hxyz
    dsimp only [allowed] at hxyz
    have hparts := (Bool.and_eq_true _ _).mp hxyz
    have htail := (Bool.and_eq_true _ _).mp hparts.2
    have hlast := (Bool.and_eq_true _ _).mp htail.2
    have hz := fusionOK_left_le_right_add_output hlast.2
    have hy := fusionOK_left_le_right_add_output hlast.1
    unfold sum
    omega
  have hxSupport : forall x y z,
      allowed (x, y, z) = true -> x <= sum := by
    intro x y z hxyz
    dsimp only [allowed] at hxyz
    have hparts := (Bool.and_eq_true _ _).mp hxyz
    have htail := (Bool.and_eq_true _ _).mp hparts.2
    have hlast := (Bool.and_eq_true _ _).mp htail.2
    have hz := fusionOK_left_le_right_add_output hlast.2
    have hy := fusionOK_left_le_right_add_output hlast.1
    have hx := fusionOK_left_le_right_add_output htail.1
    unfold sum
    omega
  by_cases hcutoff : cutoff <= sum
  · have hraw := threeChannelMultiplicity_le cutoff spin spin a b c d
    have hcubic :
        (cutoff + 1) * ((cutoff + 1) * (cutoff + 1)) <=
          (sum + 1) * ((sum + 1) * (sum + 1)) :=
      Nat.mul_le_mul (by omega)
        (Nat.mul_le_mul (by omega) (by omega))
    exact Nat.le_trans hraw hcubic
  · have hsum : sum <= cutoff := by omega
    have hinner := triplePathCount_inner_stable
      cutoff cutoff allowed hsum hzSupport
    have hmiddle := triplePathCount_middle_stable
      (outerCutoff := cutoff) (innerCutoff := sum)
      allowed hsum hySupport
    have houter := triplePathCount_outer_stable
      (middleCutoff := sum) (innerCutoff := sum)
      allowed hsum hxSupport
    have hstable :
        threeChannelMultiplicity cutoff spin spin a b c d =
          threeChannelMultiplicity sum spin spin a b c d := by
      calc
        threeChannelMultiplicity cutoff spin spin a b c d =
            triplePathCount cutoff cutoff cutoff allowed :=
          threeChannelMultiplicity_eq_triplePathCount _ _ _ _ _ _ _
        _ = triplePathCount cutoff cutoff sum allowed := hinner
        _ = triplePathCount cutoff sum sum allowed := hmiddle
        _ = triplePathCount sum sum sum allowed := houter
        _ = threeChannelMultiplicity sum spin spin a b c d :=
          (threeChannelMultiplicity_eq_triplePathCount _ _ _ _ _ _ _).symm
    rw [hstable]
    exact threeChannelMultiplicity_le sum spin spin a b c d

end YMGap.Continuum.Z4EqualPairResidualMultiplicityBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4EqualPairResidualMultiplicityBound.fusionOK_left_le_right_add_output
#print axioms YMGap.Continuum.Z4EqualPairResidualMultiplicityBound.oneChannelMultiplicity_equalPair_le_residualSpinSumCube
#print axioms YMGap.Continuum.Z4EqualPairResidualMultiplicityBound.twoChannelMultiplicity_equalPair_le_residualSpinSumCube
#print axioms YMGap.Continuum.Z4EqualPairResidualMultiplicityBound.threeChannelMultiplicity_equalPair_le_residualSpinSumCube
