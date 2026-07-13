/-
From a vanishing rotation-breaking coefficient to observable-level symmetry.

`O4RestorationZero` proves that `ScalingDimensionDecay.breakCoeff` tends to
zero.  `RegularLinearGeometricSymmetry` proves exact continuum invariance from
an observable-level geometric defect.  This file supplies the missing typed
connector: if each selected observable's expectation defect is bounded by a
nonnegative response coefficient times `breakCoeff`, the scalar geometric
envelope induces the required observable geometric defect.
-/

import YMGap.Continuum.O4RestorationZero

namespace YMGap.Continuum.O4ObservableSymmetryBridge

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RegularCReal
open YMGap.Continuum
open YMGap.Continuum.RegularFunctional
open YMGap.Continuum.RegularLinearScalingLimit
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.RegularLinearGeometricSymmetry
open YMGap.Continuum.RegularLinearSymmetryLimit
open YMGap.Continuum.O4RestorationAF

/-- Observable response to the leading rotation-breaking coefficient.  This
is the precise estimate which the interacting RG must derive: the selected
rotation defect is Lipschitz in the anisotropy coefficient, uniformly in the
spacing index. -/
structure DecayControlledSymmetryResponse (A : LinearObsAlg)
    (L : LinearScalingLimitModulus A) (D : ScalingDimensionDecay) where
  map : A.carrier → A.carrier
  response : A.carrier → Q'
  response_nonneg : ∀ o, (0 : Q') ≤ response o
  stage_upper : ∀ o j,
    (L.atSpacing j).E (map o) ≤
      (L.atSpacing j).E o + response o * breakCoeff D j
  stage_lower : ∀ o j,
    (L.atSpacing j).E o ≤
      (L.atSpacing j).E (map o) + response o * breakCoeff D j

theorem response_mul_breakCoeff_le_geo
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    {D : ScalingDimensionDecay}
    (R : DecayControlledSymmetryResponse A L D) (o : A.carrier) (j : Nat) :
    R.response o * breakCoeff D j ≤
      geoIncr (R.response o * breakCoeff D 0) j := by
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (R.response o)
    (breakCoeff_le_geo D j) (R.response_nonneg o)
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (R.response o) (breakCoeff D 0) (half ^ j))))

/-- The scalar AF decay and observable response estimate synthesize the exact
geometric symmetry datum consumed by the continuum transport theorem. -/
def DecayControlledSymmetryResponse.toGeometricSymmetry
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    {D : ScalingDimensionDecay}
    (R : DecayControlledSymmetryResponse A L D) :
    LinearGeometricSymmetryFamily A L where
  map := R.map
  amplitude := fun o => R.response o * breakCoeff D 0
  amplitude_nonneg := fun o => Q'.mul_nonneg _ _
    (R.response_nonneg o) (breakCoeff_nonneg D 0)
  stage_upper := by
    intro o j
    exact Q'.le_trans' _ _ _ (R.stage_upper o j)
      (Q'.add_le_add_left _ _ _ (response_mul_breakCoeff_le_geo R o j))
  stage_lower := by
    intro o j
    exact Q'.le_trans' _ _ _ (R.stage_lower o j)
      (Q'.add_le_add_left _ _ _ (response_mul_breakCoeff_le_geo R o j))

/-- Main O(4)-transport connector: AF decay plus a uniform observable response
bound gives exact selected symmetry of the constructive continuum functional. -/
theorem limitE_invariant_of_decay_response
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    {D : ScalingDimensionDecay}
    (R : DecayControlledSymmetryResponse A L D) (o : A.carrier) :
    Equiv (limitE L (R.map o)) (limitE L o) :=
  limitE_invariant_of_geometric_defect R.toGeometricSymmetry o

/-! ## Non-exact validation on the moving plane family -/

open YMGap.Continuum.RegularLinearSymmetryLimit (planeLinearAlg planeFlip)
open YMGap.Continuum.RegularLinearGeometricSymmetry
  (tailPlaneScaling tailPlaneFlipGeometricSymmetry)

def halfScalingDecay : ScalingDimensionDecay where
  coeff := fun j => half ^ j
  coeff_nonneg := fun j => Q'.pow_nonneg half half_nonneg j
  degreeMargin := 2
  degreeMargin_ge_two := by decide
  decay := by
    intro j
    rw [Q'.pow_succ]
    exact Q'.le_refl' _

def tailPlaneFlipDecayResponse :
    DecayControlledSymmetryResponse planeLinearAlg tailPlaneScaling
      halfScalingDecay where
  map := planeFlip
  response := fun o => Q'.abs o.2 + Q'.abs o.2
  response_nonneg := fun o => Q'.zero_le_add _ _
    (Q'.abs_nonneg o.2) (Q'.abs_nonneg o.2)
  stage_upper := tailPlaneFlipGeometricSymmetry.stage_upper
  stage_lower := tailPlaneFlipGeometricSymmetry.stage_lower

theorem tailPlane_limit_flip_invariant_from_decay_response (o : Q' × Q') :
    Equiv (limitE tailPlaneScaling (planeFlip o))
      (limitE tailPlaneScaling o) :=
  limitE_invariant_of_decay_response tailPlaneFlipDecayResponse o

#print axioms DecayControlledSymmetryResponse
#print axioms response_mul_breakCoeff_le_geo
#print axioms DecayControlledSymmetryResponse.toGeometricSymmetry
#print axioms limitE_invariant_of_decay_response
#print axioms halfScalingDecay
#print axioms tailPlaneFlipDecayResponse
#print axioms tailPlane_limit_flip_invariant_from_decay_response

end YMGap.Continuum.O4ObservableSymmetryBridge
