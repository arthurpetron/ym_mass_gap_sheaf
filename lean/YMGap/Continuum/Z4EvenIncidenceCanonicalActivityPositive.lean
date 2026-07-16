/-
# Strict positivity of every cutoff-one even-incidence carrier

At cutoff one every excited plaquette carries the fundamental SU(2)
representation.  The local Haar factor therefore depends only on the number
of excited plaquettes incident on the link.  In four dimensions this number
is at most six, and the exact invariant multiplicities at even incidence are
the positive Catalan values `1, 1, 2, 5`.

This module packages that local fact into a global statement: any finite
face support satisfying the geometric even-incidence equations has strictly
positive canonical activity at every strictly positive coupling.  No
connectedness hypothesis is needed for positivity; connectedness is a
separate condition when the support is used as one canonical polymer.
-/

import YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable

namespace YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Geometric incidence is the filter length -/

theorem geometricIncidentPlaquettes_length_eq_faceIncidenceCount
    (support : List Z4Plaq) (link : Z4Link) :
    (geometricIncidentPlaquettes support link).length =
      faceIncidenceCount link support := by
  induction support with
  | nil => rfl
  | cons plaquette rest ih =>
      have ih' :
          (rest.filter (fun p => decide (link ∈ edgesOf p))).length =
            faceIncidenceCount link rest := by
        simpa only [geometricIncidentPlaquettes] using ih
      unfold geometricIncidentPlaquettes faceIncidenceCount
      by_cases hlink : link ∈ edgesOf plaquette
      · simp [hlink, ih', Nat.add_comm]
      · simp [hlink, ih']

/-- A numerical cutoff-one face support has at most six excited plaquettes
at each physical link. -/
theorem geometricIncidentPlaquettes_length_le_six
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) (link : Z4Link) :
    (geometricIncidentPlaquettes
        (geometricPolymer n support) link).length ≤ 6 := by
  rw [← excitedIncidentPlaqIds_length_eq_geometric hsupport link]
  unfold excitedIncidentPlaqIds
  exact Nat.le_trans (List.length_filter_le _ _)
    (incidentPlaqIds_length_le_six n link)

/-! ## 2. Every permitted even local multiplicity is positive -/

theorem fundamentalInvariantMultiplicity_pos_of_even_le_six
    {count : Nat} (hcount : count ≤ 6) (heven : count % 2 = 0) :
    0 < fundamentalInvariantMultiplicity count := by
  have hcases : count = 0 ∨ count = 2 ∨ count = 4 ∨ count = 6 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl <;> decide

private theorem ofNat_pos_of_pos {count : Nat} (hcount : 0 < count) :
    (0 : Q') < Q'.ofNat count := by
  cases count with
  | zero => contradiction
  | succ count => exact Q'.ofNat_succ_pos count

theorem geometricLinkMultiplicityFactor_pos_of_evenIncidence
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hclosed : EvenFaceIncidence (geometricPolymer n support))
    (link : Z4Link) :
    (0 : Q') < geometricLinkMultiplicityFactor
      (geometricPolymer n support) link := by
  unfold geometricLinkMultiplicityFactor
  apply ofNat_pos_of_pos
  apply fundamentalInvariantMultiplicity_pos_of_even_le_six
  · exact geometricIncidentPlaquettes_length_le_six hsupport link
  · rw [geometricIncidentPlaquettes_length_eq_faceIncidenceCount]
    exact hclosed link

theorem geometricLinkMultiplicityProduct_pos_of_evenIncidence
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hclosed : EvenFaceIncidence (geometricPolymer n support))
    (links : List Z4Link) :
    (0 : Q') < geometricLinkMultiplicityProduct
      (geometricPolymer n support) links := by
  induction links with
  | nil =>
      change (0 : Q') < 1
      decide
  | cons link rest ih =>
      exact Q'.mul_pos
        (geometricLinkMultiplicityFactor_pos_of_evenIncidence
          hsupport hclosed link) ih

/-! ## 3. Positive physical link product and canonical activity -/

theorem explicitLinkMultiplicityProduct_componentLabel_pos_of_evenIncidence
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hclosed : EvenFaceIncidence (geometricPolymer n support)) :
    (0 : Q') < explicitLinkMultiplicityProduct 1 n
      (componentLabel support)
      (touchedIndexedLinks n (componentLabel support)) := by
  have hgeometric :=
    geometricLinkMultiplicityProduct_pos_of_evenIncidence
      hsupport hclosed
      (touchedPhysicalLinks n (componentLabel support))
  have heq :=
    explicitLinkMultiplicityProduct_componentLabel_eqv_geometric hsupport
  exact Q'.pos_of_lt_of_le hgeometric (Q'.ge_of_eqv heq)

theorem parametricPhysicalFaceFactor_componentLabel_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    (0 : Q') < parametricPhysicalFaceFactor coupling n
      (componentLabel support) := by
  have hcoefficient : (0 : Q') < coeffW coupling 1 :=
    YMGap.Continuum.FusionResidualBound.coeffW_pos hcoupling 1
  have hpower : (0 : Q') < (coeffW coupling 1) ^ support.length :=
    YMGap.Continuum.HKPos.pow_pos hcoefficient support.length
  have heq :=
    parametricPhysicalFaceFactor_componentLabel_eqv_pow coupling hsupport
  exact Q'.pos_of_lt_of_le hpower (Q'.ge_of_eqv heq)

/-- Exact positive-weight theorem for an arbitrary cutoff-one closed
geometric carrier.  This is the amplitude engine needed by multi-cube union
witnesses: their remaining obligations are purely geometric. -/
theorem canonicalSurfaceActivity_pos_of_evenIncidence
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hclosed : EvenFaceIncidence (geometricPolymer n support)) :
    (0 : Q') < canonicalSurfaceActivity coupling n support := by
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  exact Q'.mul_pos
    (parametricPhysicalFaceFactor_componentLabel_pos hcoupling hsupport)
    (explicitLinkMultiplicityProduct_componentLabel_pos_of_evenIncidence
      hsupport hclosed)

#print axioms geometricIncidentPlaquettes_length_eq_faceIncidenceCount
#print axioms geometricIncidentPlaquettes_length_le_six
#print axioms fundamentalInvariantMultiplicity_pos_of_even_le_six
#print axioms geometricLinkMultiplicityFactor_pos_of_evenIncidence
#print axioms geometricLinkMultiplicityProduct_pos_of_evenIncidence
#print axioms explicitLinkMultiplicityProduct_componentLabel_pos_of_evenIncidence
#print axioms parametricPhysicalFaceFactor_componentLabel_pos
#print axioms canonicalSurfaceActivity_pos_of_evenIncidence

end YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
