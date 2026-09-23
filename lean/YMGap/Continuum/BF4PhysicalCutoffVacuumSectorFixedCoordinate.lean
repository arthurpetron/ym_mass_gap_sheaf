/-
# Persistent coordinates of completed sector fixed vectors

A fixed vector of the actual completed sector transfer has zero completed
Dirichlet form.  The persistent endpoint estimate and the constructed
positive fixed-base edge floor then force any two retained coordinates on
the same finite canonical component to agree.

No coordinate-separation, vacuum-membership, or spectral-gap assumption is
used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedEndpointEnergy

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedCoordinate

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedEndpointEnergy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentCoordinate
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector

private theorem rc_add_neg_self (value : CReal.RC) :
    CReal.RCadd value (CReal.RCneg value) = CReal.RCzero := by
  refine Quotient.inductionOn value ?_
  intro representative
  exact Quotient.sound
    (Equiv_of_approx_eqv (fun _ => Q'.add_neg_self_eqv _))

private theorem rc_mul_zero (value : CReal.RC) :
    CReal.RCmul value CReal.RCzero = CReal.RCzero := by
  refine Quotient.inductionOn value ?_
  intro representative
  exact Quotient.sound
    (Equiv_of_approx_eqv (fun _ => Q'.mul_zero_eqv _))

private theorem weighted_square_zero
    (difference : CReal) (weight : Q') (hweight : (0 : Q') < weight)
    (hzero : Equiv
      (mul (ofQ' weight) (mul difference difference)) czero) :
    Equiv difference czero := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hzero
    (weight * (epsilon * epsilon))
    (Q'.mul_pos hweight (Q'.mul_pos hepsilon hepsilon))
  refine ⟨N, fun n hn => ?_⟩
  have hsquare : difference.approx n * difference.approx n ≤
      epsilon * epsilon := by
    apply Q'.le_of_mul_le_mul_left (c := weight) _ hweight
    have h := (hN n hn).1
    change weight * (difference.approx n * difference.approx n) ≤
      0 + weight * (epsilon * epsilon) at h
    rwa [Q'.zero_add'] at h
  have habs := Q'.abs_le_two_sided
    (Q'.abs_le_of_sq_le_sq hepsilon hsquare)
  constructor
  · exact Q'.le_trans' _ _ _ habs.1
      (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -difference.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact habs.2

private theorem rc_eq_of_positive_weighted_square_le_zero
    (weight : Q') (hweight : (0 : Q') < weight)
    (left right : CReal.RC)
    (hle : CReal.RCle
      (CReal.RCmul
        (Quotient.mk CReal.crealSetoid (ofQ' weight))
        (CReal.RCmul
          (CReal.RCadd left (CReal.RCneg right))
          (CReal.RCadd left (CReal.RCneg right))))
      CReal.RCzero) :
    left = right := by
  revert hle
  refine Quotient.inductionOn₂ left right ?_
  intro leftRepresentative rightRepresentative hle
  let difference := add leftRepresentative (neg rightRepresentative)
  change leEv (mul (ofQ' weight) (mul difference difference)) czero at hle
  have hnonnegative : leEv czero
      (mul (ofQ' weight) (mul difference difference)) :=
    CReal.leEv_ofQ'_of_approx_ge (fun n =>
      Q'.mul_nonneg _ _ (Q'.le_of_lt hweight)
        (q_mul_self_nonneg (difference.approx n)))
  have hweightedZero : Equiv
      (mul (ofQ' weight) (mul difference difference)) czero :=
    equiv_of_leEv_leEv hle hnonnegative
  exact Quotient.sound
    (Equiv_of_sub_eqv_zero
      (weighted_square_zero difference weight hweight hweightedZero))

/-- A fixed vector has vanishing actual completed sector Dirichlet form. -/
theorem completedDirichlet_eq_zero_of_fixed
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half)
    (hfixed : centralPhysicalVacuumSectorCylinderCompletedTransfer
      hw0 hw1 half vector = vector) :
    centralPhysicalVacuumSectorCompletedDirichlet
      hw0 hw1 half vector = CReal.RCzero := by
  unfold centralPhysicalVacuumSectorCompletedDirichlet
  rw [hfixed]
  exact rc_add_neg_self _

/-- Every two persistent coordinates on one fixed finite base component agree
for a completed sector transfer-fixed vector. -/
theorem completedCoordinates_eq_of_fixed
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half)
    (hfixed : centralPhysicalVacuumSectorCylinderCompletedTransfer
      hw0 hw1 half vector = vector) :
    completedCoordinate hw0 hw1 base half left hleft vector =
      completedCoordinate hw0 hw1 base half right hright vector := by
  let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
  have hbound :=
    fixedBaseFloor_mul_completedEndpointSq_le_completedDirichlet
      hw0 hw1 base half left right hleft hright vector
  rw [completedDirichlet_eq_zero_of_fixed hw0 hw1 half vector hfixed,
    rc_mul_zero] at hbound
  exact rc_eq_of_positive_weighted_square_le_zero
    certificate.floor certificate.floor_pos
    (completedCoordinate hw0 hw1 base half left hleft vector)
    (completedCoordinate hw0 hw1 base half right hright vector)
    hbound

/-- The distinguished root coordinate is independent of the finite base used
to present it: index zero is the same physical vacuum-labelled state at every
cutoff.  This is a state-coherence statement, not a claim that the global
vacuum vector belongs to the completed sector. -/
theorem completedRootCoordinate_eq_across_bases
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (firstBase secondBase half : Nat)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half) :
    completedCoordinate hw0 hw1 firstBase half 0
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw0) firstBase half) vector =
      completedCoordinate hw0 hw1 secondBase half 0
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw0) secondBase half) vector := by
  refine Quotient.inductionOn vector ?_
  intro X
  apply Quotient.sound
  apply Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ' (coordinate firstBase half 0 (X.seq n)))
    (bSeq := fun n => CReal.ofQ' (coordinate secondBase half 0 (X.seq n)))
  · intro stage
    apply CReal.ofQ'_equiv_of_eqv
    exact Q'.eqv_of_eq (by
      unfold coordinate
      rw [centralPhysicalFiniteStateAt_zero_eq_vacuum,
        centralPhysicalFiniteStateAt_zero_eq_vacuum])
  · exact coordinate_converges hw0 hw1 firstBase half 0
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) firstBase half) X
  · exact coordinate_converges hw0 hw1 secondBase half 0
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) secondBase half) X

/-- A completed transfer-fixed sector vector has one common coordinate across
all retained indices and all finite bases.  The common comparison point is
the coherent root state, not a presumed completed vacuum vector. -/
theorem completedCoordinates_eq_across_bases_of_fixed
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (firstBase secondBase half firstIndex secondIndex : Nat)
    (hfirst : firstIndex ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) firstBase half)
    (hsecond : secondIndex ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) secondBase half)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half)
    (hfixed : centralPhysicalVacuumSectorCylinderCompletedTransfer
      hw0 hw1 half vector = vector) :
    completedCoordinate hw0 hw1 firstBase half firstIndex hfirst vector =
      completedCoordinate hw0 hw1 secondBase half secondIndex hsecond vector := by
  let hfirstRoot := zero_mem_centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw0) firstBase half
  let hsecondRoot := zero_mem_centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw0) secondBase half
  exact Eq.trans
    (completedCoordinates_eq_of_fixed hw0 hw1
      firstBase half firstIndex 0 hfirst hfirstRoot vector hfixed)
    (Eq.trans
      (completedRootCoordinate_eq_across_bases
        hw0 hw1 firstBase secondBase half vector)
      (Eq.symm
        (completedCoordinates_eq_of_fixed hw0 hw1
          secondBase half secondIndex 0 hsecond hsecondRoot vector hfixed)))

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedCoordinate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedCoordinate.completedDirichlet_eq_zero_of_fixed
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedCoordinate.completedCoordinates_eq_of_fixed
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedCoordinate.completedRootCoordinate_eq_across_bases
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedCoordinate.completedCoordinates_eq_across_bases_of_fixed
