/-
# Linear dyadic tolerance schedule for the physical SU(2) outer tail

The arbitrary-rational schedule in `SU2PhysicalOuterCutoffNomeTolerance`
pays a tensor coefficient by first scaling the requested rational tolerance
and then using the denominator of that scaled rational as a dyadic precision.
For a dyadic target this can hide a quadratic precision loss.

Here the tensor coefficient is paid once by an explicit, fixed natural-number
burn.  Every further unit of target precision then costs exactly one further
retained label.  Thus, at fixed nome and finite tensor dimension, the retained
cutoff is affine in the requested dyadic precision.

This is still a fixed-nome, fixed-finite-volume statement.  The burn may grow
with the nome and dimension; no spacing-uniform, thermodynamic, continuum, or
mass-gap conclusion is asserted.

## Axiom gate

Constructive `Nat`/`Q'` recursion only.  No `Classical.*`, `Real`, choice,
`native_decide`, `sorry`, custom axiom, functional extensionality, or
noncomputable declaration.
-/

import YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance

namespace YMGap.Continuum.SU2PhysicalOuterCutoffNomeDyadicTolerance

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pay the fixed tensor coefficient once -/

/-- Number of dyadic powers sufficient to pay the fixed-dimensional tensor
coefficient.  It depends on the nome and tensor dimension, but not on the
requested target precision. -/
def physicalNomeTensorDyadicBurn (w : Q') (dimension : Nat) : Nat :=
  (Q'.invSucc
    (physicalNomeTensorTailCoefficient w dimension).num.toNat).den

/-- The fixed dyadic burn times the tensor coefficient is at most one. -/
theorem physicalNomeTensorDyadicBurn_pays
    {w : Q'} (hw0 : (0 : Q') < w) (dimension : Nat) :
    dyad (physicalNomeTensorDyadicBurn w dimension) *
        physicalNomeTensorTailCoefficient w dimension <=
      1 := by
  let coefficient := physicalNomeTensorTailCoefficient w dimension
  let unit := Q'.invSucc coefficient.num.toNat
  have hcoefficient : (0 : Q') <= coefficient :=
    physicalNomeTensorTailCoefficient_nonnegative hw0 dimension
  have hunit : (0 : Q') < unit := Q'.invSucc_pos _
  have hdyad :
      dyad (physicalNomeTensorDyadicBurn w dimension) <= unit := by
    change HalfPow.half ^ unit.den <= unit
    exact HalfPow.pow_half_le unit hunit
  have hscaled :
      dyad (physicalNomeTensorDyadicBurn w dimension) * coefficient <=
        unit * coefficient :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdyad hcoefficient
  have hpay : unit * coefficient <= 1 := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv unit coefficient)) ?_
    exact YMGap.Constructive.ExpNeg.mul_invSucc_toNat_le_one
      coefficient hcoefficient
  exact Q'.le_trans' _ _ _ hscaled hpay

/-! ## 2. Affine dyadic precision and retained cutoff -/

/-- Source precision equals target precision plus one fixed coefficient burn. -/
def physicalNomeTensorDyadicPrecision
    (w : Q') (dimension targetPrecision : Nat) : Nat :=
  targetPrecision + physicalNomeTensorDyadicBurn w dimension

/-- The corresponding retained cutoff.  Unfolding this and
`physicalNomeRetainedCutoff` shows affine dependence on `targetPrecision`. -/
def physicalNomeTensorDyadicRetainedCutoff
    (w : Q') (dimension targetPrecision : Nat) : Nat :=
  physicalNomeRetainedCutoff w
    (physicalNomeTensorDyadicPrecision w dimension targetPrecision)

theorem physicalNomeTensorDyadicRetainedCutoff_eq
    (w : Q') (dimension targetPrecision : Nat) :
    physicalNomeTensorDyadicRetainedCutoff
        w dimension targetPrecision =
      physicalNomeBaseCutoff w - 1 +
        (targetPrecision + physicalNomeTensorDyadicBurn w dimension) := by
  rfl

/-- At the affine retained cutoff, the complete tensor envelope is at most
the requested dyadic target. -/
theorem physicalNomeTensorTailEnvelope_le_dyad_linear
    {w : Q'} (hw0 : (0 : Q') < w)
    (dimension targetPrecision : Nat) :
    su2PhysicalTensorTailEnvelope
        w (physicalNomeBaseCutoff w)
        (physicalNomeTensorDyadicRetainedCutoff
          w dimension targetPrecision)
        (physicalNomeTensorDyadicPrecision
          w dimension targetPrecision)
        dimension <=
      dyad targetPrecision := by
  let burn := physicalNomeTensorDyadicBurn w dimension
  let coefficient := physicalNomeTensorTailCoefficient w dimension
  have hfactor :=
    physicalNomeTensorTailEnvelope_eqv_coefficient
      w
      (physicalNomeTensorDyadicRetainedCutoff
        w dimension targetPrecision)
      (physicalNomeTensorDyadicPrecision
        w dimension targetPrecision)
      dimension
  have hsplit :
      dyad (physicalNomeTensorDyadicPrecision
          w dimension targetPrecision) ≈
        dyad targetPrecision * dyad burn := by
    unfold physicalNomeTensorDyadicPrecision dyad
    exact Q'.pow_add_eqv HalfPow.half targetPrecision burn
  have hreassociate :
      dyad (physicalNomeTensorDyadicPrecision
            w dimension targetPrecision) * coefficient ≈
        dyad targetPrecision * (dyad burn * coefficient) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (dyad (physicalNomeTensorDyadicPrecision
          w dimension targetPrecision))
        (dyad targetPrecision * dyad burn)
        coefficient hsplit) ?_
    exact Q'.mul_assoc_eqv
      (dyad targetPrecision) (dyad burn) coefficient
  have hburn : dyad burn * coefficient <= 1 := by
    exact physicalNomeTensorDyadicBurn_pays hw0 dimension
  have hscaled :
      dyad targetPrecision * (dyad burn * coefficient) <=
        dyad targetPrecision * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hburn
      (dyad_nonneg targetPrecision)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfactor hreassociate))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_one_eqv (dyad targetPrecision))))

/-! ## 3. Uniformity in the later cutoff and the interacting increment -/

theorem physicalNomeTensorOutsideUnionMass_le_dyad_linear
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (dimension targetPrecision K : Nat) :
    su2PhysicalTensorOutsideUnionMass
        w
        (physicalNomeTensorDyadicRetainedCutoff
          w dimension targetPrecision)
        K dimension <=
      dyad targetPrecision := by
  let precision :=
    physicalNomeTensorDyadicPrecision w dimension targetPrecision
  let retained :=
    physicalNomeTensorDyadicRetainedCutoff w dimension targetPrecision
  have henvelope :=
    su2PhysicalTensorOutsideUnionMass_le_envelope
      hw0 hw1
      (physicalNomeBaseCutoff w)
      precision
      (M := retained) (K := K)
      (physicalNomeBaseCondition hw0 hw1)
      (physicalNomeBaseHead hw0 hw1)
      (physicalNomeRetainedCondition hw0 hw1 precision)
      (physicalNomeRetainedHead hw0 hw1 precision)
      dimension
  exact Q'.le_trans' _ _ _ henvelope
    (physicalNomeTensorTailEnvelope_le_dyad_linear
      hw0 dimension targetPrecision)

theorem boundedSU2PhysicalOutsideFaceMass_le_dyad_linear
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (faces : List Nat) (hfaces : faces.Nodup)
    (targetPrecision : Nat) {K : Nat}
    (hK :
      physicalNomeTensorDyadicRetainedCutoff
          w faces.length targetPrecision <= K) :
    boundedSU2PhysicalOutsideFaceMass
        w
        (physicalNomeTensorDyadicRetainedCutoff
          w faces.length targetPrecision)
        K faces <=
      dyad targetPrecision := by
  exact Q'.le_trans' _ _ _
    (boundedSU2PhysicalOutsideFaceMass_le_unionMass
      hw0 hK faces hfaces)
    (physicalNomeTensorOutsideUnionMass_le_dyad_linear
      hw0 hw1 faces.length targetPrecision K)

private theorem range_nodup_local :
    forall N : Nat, (List.range N).Nodup
  | 0 => List.nodup_nil
  | N + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨range_nodup_local N,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl N) (List.mem_range.mp hleft)

/-- The genuine interacting fixed-volume cutoff increment inherits the affine
dyadic schedule, uniformly in every later cutoff containing the retained
window. -/
theorem physicalNomeCutoffIncrement_le_dyad_linear
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (volume targetPrecision : Nat) {K : Nat}
    (hK :
      physicalNomeTensorDyadicRetainedCutoff
          w (plaquetteEdgeCount volume) targetPrecision <= K) :
    parametricKCutoffIncrement
        w
        (physicalNomeTensorDyadicRetainedCutoff
          w (plaquetteEdgeCount volume) targetPrecision)
        K volume <=
      dyad targetPrecision := by
  let retained :=
    physicalNomeTensorDyadicRetainedCutoff
      w (plaquetteEdgeCount volume) targetPrecision
  refine Q'.le_trans' _ _ _
    (physicalCutoffIncrement_le_outsideFaceMass
      (Q'.le_of_lt hw0)
      (M := retained) (K := K) (n := volume)) ?_
  have hK' :
      physicalNomeTensorDyadicRetainedCutoff
          w
          (List.range (plaquetteEdgeCount volume)).length
          targetPrecision <= K := by
    simpa using hK
  dsimp only [retained]
  simpa using
    (boundedSU2PhysicalOutsideFaceMass_le_dyad_linear
      hw0 hw1
      (List.range (plaquetteEdgeCount volume))
      (range_nodup_local _)
      targetPrecision hK')

/-! ## Axiom audit -/

#print axioms physicalNomeTensorDyadicBurn_pays
#print axioms physicalNomeTensorDyadicRetainedCutoff_eq
#print axioms physicalNomeTensorTailEnvelope_le_dyad_linear
#print axioms physicalNomeTensorOutsideUnionMass_le_dyad_linear
#print axioms boundedSU2PhysicalOutsideFaceMass_le_dyad_linear
#print axioms physicalNomeCutoffIncrement_le_dyad_linear

end YMGap.Continuum.SU2PhysicalOuterCutoffNomeDyadicTolerance
