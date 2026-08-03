/-
# A centered vacuum probe for the exact/physical BF4 seam

The raw vacuum code delta refutes equality of the exact signed-Haar and
current positive physical quadratics on the full observable carrier.  It is
not, however, stationary-mean-zero.  This module constructs the canonical
centered version by subtracting its physical vacuum marginal and proves that
it lies in the exact consumer subspace.

Consequently every inhabitant of the weaker centered same-action seam must
identify the two quadratics on this explicit probe.  The theorem is a
necessary test, not an inhabitant or a no-go result: evaluating its exact
cross and constant moments remains open.

## Axiom gate

Finite lists and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute

namespace YMGap.Continuum.BF4ExactPhysicalCenteredVacuumProbe

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact physical centering -/

/-- The stationary expectation of the faithful vacuum code delta is exactly
the normalized physical vacuum row marginal. -/
theorem centralPhysicalStationaryMean_vacuumCodeDelta
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    centralPhysicalStationaryMean
        w hw K 0 (vacuumCodeDelta K) ≈
      centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling := by
  unfold centralPhysicalStationaryMean
  exact listQSum_value_mul_vacuumCodeDelta_positive
    hw K (centralPhysicalRowMarginal w hw K 0)

/-- Subtracting a constant from an observable subtracts that constant from
its normalized physical stationary mean. -/
private theorem centralPhysicalStationaryMean_add_neg_constant
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (observable : EdgeLabelling → Q') (constant : Q') :
    centralPhysicalStationaryMean
        w hw K 0 (fun state => observable state + (-constant)) ≈
      centralPhysicalStationaryMean w hw K 0 observable +
        (-constant) := by
  let states := centralPositiveHalfStates w hw K 0
  let marginal := centralPhysicalRowMarginal w hw K 0
  unfold centralPhysicalStationaryMean
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        marginal state * observable state +
          (-constant) * marginal state)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    exact Q'.eqv_trans _
      (marginal state * observable state +
        marginal state * (-constant)) _
      (Q'.mul_add_eqv
        (marginal state) (observable state) (-constant))
      (Q'.add_eqv_congr'
        (Q'.eqv_refl _)
        (Q'.mul_comm_eqv (marginal state) (-constant)))
  refine Q'.eqv_trans _
    (listQSum
        (fun state => marginal state * observable state)
        states +
      listQSum
        (fun state => (-constant) * marginal state)
        states) _
    (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (listQSum
        (fun state => marginal state * observable state)
        states +
      (-constant) * listQSum marginal states) _
    (Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (listQSum_mul_left (-constant) marginal states)) ?_
  refine Q'.eqv_trans _
    (listQSum
        (fun state => marginal state * observable state)
        states +
      (-constant) * 1) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left (-constant) _ _
        (centralPositiveRowMarginal_total_one w hw K 0))
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _)
    (Q'.mul_one_eqv (-constant))

/-- Vacuum point observable centered by its actual physical stationary
expectation. -/
def centeredVacuumCodeDelta
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (state : EdgeLabelling) : Q' :=
  vacuumCodeDelta K state +
    -centralPhysicalRowMarginal
      w hw K 0 zeroEdgeLabelling

/-- The centered vacuum probe belongs to the physical stationary-mean-zero
carrier consumed by the Perron contraction theorems. -/
theorem centeredVacuumCodeDelta_meanZero
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    CentralPhysicalMeanZero
      w hw K 0 (centeredVacuumCodeDelta w hw K) := by
  unfold CentralPhysicalMeanZero centeredVacuumCodeDelta
  let vacuumMass :=
    centralPhysicalRowMarginal w hw K 0 zeroEdgeLabelling
  refine Q'.eqv_trans _
    (centralPhysicalStationaryMean
        w hw K 0 (vacuumCodeDelta K) +
      (-vacuumMass)) _ ?_ ?_
  · exact centralPhysicalStationaryMean_add_neg_constant
      w hw K (vacuumCodeDelta K) vacuumMass
  refine Q'.eqv_trans _ (vacuumMass + (-vacuumMass)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (centralPhysicalStationaryMean_vacuumCodeDelta w hw K)
      (Q'.eqv_refl _)
  exact Q'.add_neg_self_eqv vacuumMass

/-! ## 2. Mandatory centered same-action test -/

/-- Any centered same-action certificate must identify the exact and physical
quadratics on the explicit centered vacuum probe.  This exposes the next
finite calculation without pretending that it is already solved. -/
theorem ExactHaarPhysicalPerronCenteredSameActionAt.vacuumProbe_same_action
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (identification :
      ExactHaarPhysicalPerronCenteredSameActionAt w hw K) :
    exactSlabAllCutoffQuadratic
        w K (centeredVacuumCodeDelta w hw K) ≈
      centralNormalizedFullPhysicalReflectionQuadratic
        w hw K 0 (centeredVacuumCodeDelta w hw K) :=
  identification.centered_same_action
    (centeredVacuumCodeDelta w hw K)
    (centeredVacuumCodeDelta_meanZero w hw K)

end YMGap.Continuum.BF4ExactPhysicalCenteredVacuumProbe

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumProbe.centralPhysicalStationaryMean_vacuumCodeDelta
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumProbe.centeredVacuumCodeDelta_meanZero
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumProbe.ExactHaarPhysicalPerronCenteredSameActionAt.vacuumProbe_same_action
