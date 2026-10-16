/-
# Finite FREE-own center pin for the neighboring heat frontier

The supplied `CayleyTraceOldCenter` cannot remain arbitrary in a signed
neighboring theorem.  This leaf defines one honest fixed center available on
the current finite heat-Gaussian carrier: the three OWN source coefficients
at a selected center stage and history time.

At that same point the OLD residual products vanish exactly, so `P4`, `P5`
and `P6` reduce respectively to `R4`, zero and `R6`.  The neighboring
residual-free and actual cleared comparisons are then specialized to this
fixed center, and the existing Heron-tail sign transfer is reused verbatim.

This center is a finite FREE reference center, not the separately required
ORIGINAL interacting center.  No ORIGINAL-law identification, neighboring
margin, denominator positivity, higher-remainder estimate, continuum
Hamiltonian or Clay mass gap is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringClearedSignTransfer

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringFiniteOwnCenterPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatConnectedR6
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringResidualFreeFrontier
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringClearedSignTransfer

local infix:50 " ≈ " => Q'.eqv

/-- Fixed finite FREE-own center at one selected stage and history time. -/
def openCubeHeatCayleyTraceFiniteOwnCenter
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (centerStage centerTime : Nat) : CayleyTraceOldCenter :=
  { c2 := openCubeHeatCayleyTraceOwnA2Mean
      timeBonds side sidePositive centerStage centerTime
    c3 := openCubeHeatCayleyTraceOwnA3Mean
      timeBonds side sidePositive centerStage centerTime
    c4 := openCubeHeatCayleyTraceOwnA4Mean
      timeBonds side sidePositive centerStage centerTime }

/-- The cubic field of the finite FREE-own center vanishes by the checked
odd-row Gaussian parity theorem. -/
theorem openCubeHeatCayleyTraceFiniteOwnCenter_c3_zero
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (centerStage centerTime : Nat) :
    (openCubeHeatCayleyTraceFiniteOwnCenter
      timeBonds side sidePositive centerStage centerTime).c3 ≈ 0 := by
  exact openCubeHeatCayleyTraceOwnA3Mean_zero
    timeBonds side sidePositive centerStage centerTime

/-- At the pinning point, the finite FREE-own centered `P4` is exactly the
connected fourth coefficient. -/
theorem openCubeHeatCayleyTraceP4_self_finiteOwnCenter
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (centerStage centerTime : Nat) :
    openCubeHeatCayleyTraceP4
        timeBonds side sidePositive centerStage centerTime centerTime
        (openCubeHeatCayleyTraceFiniteOwnCenter
          timeBonds side sidePositive centerStage centerTime) ≈
      openCubeHeatCayleyTraceConnectedR4
        timeBonds side sidePositive centerStage centerTime centerTime := by
  unfold openCubeHeatCayleyTraceP4 openCubeHeatCayleyTraceFiniteOwnCenter
  dsimp only
  exact poly_identity_of_normal_eq
    (.add (.var 0)
      (.mul
        (.add (.var 1) (.neg (.var 1)))
        (.add (.var 1) (.neg (.var 1)))))
    (.var 0) (by decide) (fun
      | 0 => openCubeHeatCayleyTraceConnectedR4
          timeBonds side sidePositive centerStage centerTime centerTime
      | _ => openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive centerStage centerTime)

/-- At the pinning point, the finite FREE-own centered `P5` vanishes
exactly. -/
theorem openCubeHeatCayleyTraceP5_self_finiteOwnCenter
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (centerStage centerTime : Nat) :
    openCubeHeatCayleyTraceP5
        timeBonds side sidePositive centerStage centerTime centerTime
        (openCubeHeatCayleyTraceFiniteOwnCenter
          timeBonds side sidePositive centerStage centerTime) ≈ 0 := by
  unfold openCubeHeatCayleyTraceP5 openCubeHeatCayleyTraceFiniteOwnCenter
  dsimp only
  exact poly_identity_of_normal_eq
    (.add
      (.mul
        (.add (.var 0) (.neg (.var 0)))
        (.add (.var 1) (.neg (.var 1))))
      (.mul
        (.add (.var 1) (.neg (.var 1)))
        (.add (.var 0) (.neg (.var 0)))))
    (.const 0) (by decide) (fun
      | 0 => openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive centerStage centerTime
      | _ => openCubeHeatCayleyTraceOwnA3Mean
          timeBonds side sidePositive centerStage centerTime)

/-- At the pinning point, every finite FREE-own residual product in `P6`
vanishes and only the connected sixth coefficient remains. -/
theorem openCubeHeatCayleyTraceP6_self_finiteOwnCenter
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (centerStage centerTime : Nat) :
    openCubeHeatCayleyTraceP6
        timeBonds side sidePositive centerStage centerTime centerTime
        (openCubeHeatCayleyTraceFiniteOwnCenter
          timeBonds side sidePositive centerStage centerTime) ≈
      openCubeHeatCayleyTraceConnectedR6WickSum
        timeBonds side sidePositive centerStage centerTime centerTime := by
  unfold openCubeHeatCayleyTraceP6 openCubeHeatCayleyTraceFiniteOwnCenter
  dsimp only
  exact poly_identity_of_normal_eq
    (.add
      (.add
        (.add (.var 0)
          (.mul
            (.add (.var 1) (.neg (.var 1)))
            (.add (.var 3) (.neg (.var 3)))))
        (.mul
          (.add (.var 2) (.neg (.var 2)))
          (.add (.var 2) (.neg (.var 2)))))
      (.mul
        (.add (.var 3) (.neg (.var 3)))
        (.add (.var 1) (.neg (.var 1)))))
    (.var 0) (by decide) (fun
      | 0 => openCubeHeatCayleyTraceConnectedR6WickSum
          timeBonds side sidePositive centerStage centerTime centerTime
      | 1 => openCubeHeatCayleyTraceOwnA2Mean
          timeBonds side sidePositive centerStage centerTime
      | 2 => openCubeHeatCayleyTraceOwnA3Mean
          timeBonds side sidePositive centerStage centerTime
      | _ => openCubeHeatCayleyTraceOwnA4Mean
          timeBonds side sidePositive centerStage centerTime)

/-- Residual-free neighboring frontier with the arbitrary supplied center
replaced by one fixed finite FREE-own center. -/
def openCubeHeatCayleyTraceP6NeighboringFiniteOwnCenteredResidualFreeComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (centerStage centerTime stage baseTime lag : Nat) : Q' :=
  openCubeHeatCayleyTraceP6NeighboringResidualFreeComparison
    timeBonds side sidePositive stage baseTime lag
    (openCubeHeatCayleyTraceFiniteOwnCenter
      timeBonds side sidePositive centerStage centerTime)

/-- Actual cleared neighboring numerator with the same fixed finite FREE-own
center. -/
def openCubeHeatCayleyTraceP6NeighboringFiniteOwnCenteredClearedComparison
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (centerStage centerTime stage baseTime lag : Nat) : Q' :=
  openCubeHeatCayleyTraceP6NeighboringClearedComparison
    timeBonds side sidePositive stage baseTime lag
    (openCubeHeatCayleyTraceFiniteOwnCenter
      timeBonds side sidePositive centerStage centerTime)

/-- The existing Heron-tail sign consumer specialized to the fixed finite
FREE-own center.  The strict residual-free margin remains the missing
producer. -/
theorem openCubeHeatCayleyTraceP6NeighboringFiniteOwnCenteredClearedComparison_lt_zero_of_margin
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (centerStage centerTime stage baseTime lag : Nat)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hstage :
      bulkSourceHeatP6NeighboringClearedAdaptiveStage
          timeBonds side sidePositive baseTime lag
          (openCubeHeatCayleyTraceFiniteOwnCenter
            timeBonds side sidePositive centerStage centerTime)
          epsilon ≤ stage)
    (hmargin :
      openCubeHeatCayleyTraceP6NeighboringFiniteOwnCenteredResidualFreeComparison
          timeBonds side sidePositive centerStage centerTime
          stage baseTime lag + epsilon < 0) :
    openCubeHeatCayleyTraceP6NeighboringFiniteOwnCenteredClearedComparison
        timeBonds side sidePositive centerStage centerTime
        stage baseTime lag < 0 := by
  exact
    openCubeHeatCayleyTraceP6NeighboringClearedComparison_lt_zero_of_residualFree_margin
      timeBonds side sidePositive stage baseTime lag
      (openCubeHeatCayleyTraceFiniteOwnCenter
        timeBonds side sidePositive centerStage centerTime)
      epsilon hepsilon hstage hmargin

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringFiniteOwnCenterPin

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringFiniteOwnCenterPin.openCubeHeatCayleyTraceFiniteOwnCenter_c3_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringFiniteOwnCenterPin.openCubeHeatCayleyTraceP4_self_finiteOwnCenter
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringFiniteOwnCenterPin.openCubeHeatCayleyTraceP5_self_finiteOwnCenter
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringFiniteOwnCenterPin.openCubeHeatCayleyTraceP6_self_finiteOwnCenter
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNeighboringFiniteOwnCenterPin.openCubeHeatCayleyTraceP6NeighboringFiniteOwnCenteredClearedComparison_lt_zero_of_margin
