/-
# The exact-action discrepancy is visible in the current reflected completion

The literal root cylinder of the completed positive BF4 cube carrier has
squared norm strictly below the signed exact-Haar vacuum-delta value one.
Its explicit discrepancy is the same cutoff-independent floor proved from
the actual cube row. The source of the strict conditional gap is therefore
not an identity-on-observables realization of that signed exact-Haar form,
even after spin-cutoff removal and completion.

The root cylinder is NOT the stationary sector vacuum Omega. This theorem
does not change the proved isolation or decay of the conditional operator.
It rules out the literal identity bridge only, not an explicitly proved
different observable transport or a controlled nonzero-error comparison.
-/

import YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation
import YMGap.Continuum.BF4PhysicalCubeReflectedCompletion

namespace YMGap.Continuum.BF4PhysicalCubeExactActionFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RationalKernelSpan
open YMGap.Continuum.BF4ExactPhysicalCutoffLimitSeparation
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
open YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "root" => cubeReflectedEmbed rootVector
local notation "B" => cubeReflectedInner
local notation "Rq" => fun q : Q' => Quotient.mk CReal.crealSetoid (CReal.ofQ' q)

def anchorSeparation : Q' := vacuumSeparation anchorCoupling (by decide)

theorem anchorSeparation_pos : (0 : Q') < anchorSeparation :=
  vacuumSeparation_pos (w := anchorCoupling) (by decide)

/-- Exact arithmetic certificate for the pilot's rational discrepancy floor.
The physical inequality is proved separately from the literal cube row. -/
theorem anchorSeparation_eqv : anchorSeparation ≈
    Q'.mkPos 1 1073741824000000000000000000000000000000000001 (by decide) := by
  decide

/-- Pin the root norm in the actual completed reflected carrier to the
original normalized vacuum-pair limit, not to a new comparison norm. -/
theorem root_pairing_eq_normalizedLimit : B root root =
    Quotient.mk CReal.crealSetoid
      (normalizedKernelLimit (w := anchorCoupling) (by decide) (by decide) rootState rootState) := by
  rw [cubeReflectedInner_embed, cubeToCompleted_reflected_pairing]
  apply Quotient.sound
  refine CReal.Equiv.trans ?_ (CReal.Equiv.symm
    (normalizedKernelLimit_eq_scaled (w := anchorCoupling) (by decide) (by decide) rootState rootState))
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change form (kernel anchorCoupling) rootVector rootVector *
      (inversePartitionLimit (w := anchorCoupling) (by decide) (by decide)).approx n ≈
    (inversePartitionLimit (w := anchorCoupling) (by decide) (by decide)).approx n *
      kernel anchorCoupling rootState rootState
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (form_basis _ _ _))
    (Q'.mul_comm_eqv _ _)

/-- Positive separation from the signed exact-Haar value one on the SAME
literal observable in the current completed reflected carrier. -/
theorem root_pairing_separation :
    CReal.RCle (Rq anchorSeparation) (CReal.RCsub (Rq 1) (B root root)) := by
  rw [root_pairing_eq_normalizedLimit]
  exact cutoff_limit_separation (w := anchorCoupling) (by decide) (by decide)

/-- Completing the conditional model does not repair the refuted identity
with signed exact-Haar observables. -/
theorem root_pairing_ne_exact_one : B root root ≠ Rq 1 := by
  rw [root_pairing_eq_normalizedLimit]
  exact normalized_vacuum_limit_ne_one (w := anchorCoupling) (by decide) (by decide)

end YMGap.Continuum.BF4PhysicalCubeExactActionFence

#print axioms YMGap.Continuum.BF4PhysicalCubeExactActionFence.anchorSeparation
#print axioms YMGap.Continuum.BF4PhysicalCubeExactActionFence.anchorSeparation_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeExactActionFence.anchorSeparation_eqv
#print axioms YMGap.Continuum.BF4PhysicalCubeExactActionFence.root_pairing_eq_normalizedLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeExactActionFence.root_pairing_separation
#print axioms YMGap.Continuum.BF4PhysicalCubeExactActionFence.root_pairing_ne_exact_one
