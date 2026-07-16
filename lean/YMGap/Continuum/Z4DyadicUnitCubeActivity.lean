/-
# Exact positive activity of the closed dyadic cube

The geometric dyadic cube is a closed connected canonical support, but that
alone does not exclude zero Haar activity.  This module performs the missing
local fusion audit.  Every one of its 48 touched links is incident on exactly
two fundamental plaquettes, hence every local invariant multiplicity is one.
Consequently the complete cutoff-one activity is exactly the twenty-fourth
power of the derived fundamental heat-kernel coefficient and is strictly
positive at every positive coupling.

This is a non-vacuity result for the finite polymer activity.  It is not yet a
uniform positive floor for its thermodynamic occurrence probability and is
not an RG comparison between two couplings.
-/

import YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
import YMGap.Continuum.FusionResidualBound

namespace YMGap.Continuum.Z4DyadicUnitCubeActivity

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

theorem dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports :
    dyadicUnitCubeSupportIds ∈ cutoffOneFaceSupports 4 :=
  canonicalSurfacePolymer_mem_faceSupports
    dyadicUnitCubeSupportIds_mem_canonicalSurfacePolymers

private theorem refinedCubeLink_mem_of_touched
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 4
      (componentLabel dyadicUnitCubeSupportIds)) :
    link ∈ geometricTouchedLinks refinedUnitCubeSurface := by
  have hgeometric :=
    (mem_touchedPhysicalLinks_iff_geometric
      dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports link).mp hlink
  obtain ⟨plaquette, hplaquette, hboundary⟩ :=
    mem_geometricTouchedLinks.mp hgeometric
  exact mem_geometricTouchedLinks.mpr
    ⟨plaquette,
      dyadicUnitCubeSupportIds_sameSupport.1 plaquette hplaquette,
      hboundary⟩

/-- Every touched link has exactly two incident faces in the numerical
canonical support as well as in its literal geometric realization. -/
theorem dyadicUnitCube_geometricIncidentPlaquettes_length_eq_two
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 4
      (componentLabel dyadicUnitCubeSupportIds)) :
    (geometricIncidentPlaquettes
      (geometricPolymer 4 dyadicUnitCubeSupportIds) link).length = 2 := by
  have hsame := geometricIncidentPlaquettes_sameSupport
    dyadicUnitCubeSupportIds_sameSupport link
  have hleftNodup := geometricIncidentPlaquettes_nodup
    dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports link
  have hrightNodup :
      (geometricIncidentPlaquettes refinedUnitCubeSurface link).Nodup := by
    unfold geometricIncidentPlaquettes
    exact List.filter_sublist.nodup refinedUnitCubeSurface_nodup
  have hlength := sameSupport_length_eq_of_nodup
    hsame hleftNodup hrightNodup
  exact hlength.trans
    (refinedUnitCube_geometricIncidentPlaquettes_length_eq_two
      (refinedCubeLink_mem_of_touched hlink))

/-- The local invariant multiplicity at every touched cube link is exactly
one. -/
theorem dyadicUnitCube_geometricLinkMultiplicityFactor_eq_one
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 4
      (componentLabel dyadicUnitCubeSupportIds)) :
    geometricLinkMultiplicityFactor
      (geometricPolymer 4 dyadicUnitCubeSupportIds) link = 1 := by
  unfold geometricLinkMultiplicityFactor
  rw [dyadicUnitCube_geometricIncidentPlaquettes_length_eq_two hlink]
  rfl

private theorem dyadicUnitCube_geometricLinkMultiplicityProduct_eqv_one_on :
    ∀ links : List Z4Link,
    (∀ link, link ∈ links →
      link ∈ touchedPhysicalLinks 4
        (componentLabel dyadicUnitCubeSupportIds)) →
    geometricLinkMultiplicityProduct
      (geometricPolymer 4 dyadicUnitCubeSupportIds) links ≈ 1
  | [], _ => Q'.eqv_refl _
  | link :: rest, hsubset => by
      change (geometricLinkMultiplicityFactor
          (geometricPolymer 4 dyadicUnitCubeSupportIds) link *
        geometricLinkMultiplicityProduct
          (geometricPolymer 4 dyadicUnitCubeSupportIds) rest) ≈ 1
      rw [dyadicUnitCube_geometricLinkMultiplicityFactor_eq_one
        (hsubset link List.mem_cons_self)]
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _
          (dyadicUnitCube_geometricLinkMultiplicityProduct_eqv_one_on
            rest (fun item hitem =>
              hsubset item (List.mem_cons_of_mem link hitem))))
        (Q'.one_mul_eqv 1)

theorem dyadicUnitCube_geometricLinkMultiplicityProduct_eqv_one :
    geometricLinkMultiplicityProduct
      (geometricPolymer 4 dyadicUnitCubeSupportIds)
      (touchedPhysicalLinks 4
        (componentLabel dyadicUnitCubeSupportIds)) ≈ 1 :=
  dyadicUnitCube_geometricLinkMultiplicityProduct_eqv_one_on _
    (fun _ hlink => hlink)

/-- The production link product, including the finite-box incident-list
encoding and all vacuum insertions, is exactly one. -/
theorem dyadicUnitCube_explicitLinkMultiplicityProduct_eqv_one :
    explicitLinkMultiplicityProduct 1 4
      (componentLabel dyadicUnitCubeSupportIds)
      (touchedIndexedLinks 4
        (componentLabel dyadicUnitCubeSupportIds)) ≈ 1 :=
  Q'.eqv_trans _ _ _
    (explicitLinkMultiplicityProduct_componentLabel_eqv_geometric
      dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports)
    dyadicUnitCube_geometricLinkMultiplicityProduct_eqv_one

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Exact non-vacuous activity formula for the 24-face closed block. -/
theorem dyadicUnitCube_canonicalSurfaceActivity_eqv
    (coupling : Q') :
    canonicalSurfaceActivity coupling 4 dyadicUnitCubeSupportIds ≈
      (coeffW coupling 1) ^ 24 := by
  have hface := parametricPhysicalFaceFactor_componentLabel_eqv_pow
    coupling dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports
  rw [dyadicUnitCubeSupportIds_length] at hface
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  change (parametricPhysicalFaceFactor coupling 4
      (componentLabel dyadicUnitCubeSupportIds) *
    explicitLinkMultiplicityProduct 1 4
      (componentLabel dyadicUnitCubeSupportIds)
      (touchedIndexedLinks 4
        (componentLabel dyadicUnitCubeSupportIds))) ≈
      (coeffW coupling 1) ^ 24
  exact Q'.eqv_trans _ ((coeffW coupling 1) ^ 24 * 1) _
    (qmul_congr_local hface
      dyadicUnitCube_explicitLinkMultiplicityProduct_eqv_one)
    (Q'.mul_one_eqv _)

private theorem qpow_pos_local {value : Q'}
    (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 => Q'.mul_pos hvalue (qpow_pos_local hvalue exponent)

/-- The closed dyadic cube has strictly positive interacting activity at
every strictly positive heat-kernel coupling. -/
theorem dyadicUnitCube_canonicalSurfaceActivity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') <
      canonicalSurfaceActivity coupling 4 dyadicUnitCubeSupportIds := by
  have hcoefficient : (0 : Q') < coeffW coupling 1 :=
    YMGap.Continuum.FusionResidualBound.coeffW_pos hcoupling 1
  have hpower := qpow_pos_local hcoefficient 24
  exact Q'.pos_of_lt_of_le hpower
    (Q'.ge_of_eqv
      (dyadicUnitCube_canonicalSurfaceActivity_eqv coupling))

theorem dyadicUnitCube_anchorActivity_pos :
    (0 : Q') < canonicalSurfaceActivity anchorCoupling 4
      dyadicUnitCubeSupportIds :=
  dyadicUnitCube_canonicalSurfaceActivity_pos (by decide)

/-! ## Positive finite-volume occurrence at every containing volume -/

private theorem nil_mem_sublists_local {A : Type} :
    ∀ ambient : List A, [] ∈ sublists ambient
  | [] => List.mem_cons_self
  | head :: tail => by
      rw [sublists_cons']
      exact List.mem_append_left _ (nil_mem_sublists_local tail)

private theorem singleton_mem_sublists_of_mem_local {A : Type} :
    ∀ (ambient : List A) (item : A), item ∈ ambient →
      [item] ∈ sublists ambient
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rw [sublists_cons']
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        apply List.mem_append_right
        exact List.mem_map.mpr
          ⟨[], nil_mem_sublists_local tail, rfl⟩
      · exact List.mem_append_left _
          (singleton_mem_sublists_of_mem_local tail item htail)

private theorem singleton_mem_canonicalCompatibleAmbientFamilies
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    [polymer] ∈ canonicalCompatibleAmbientFamilies n := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  exact ⟨singleton_mem_sublists_of_mem_local
      (canonicalSurfacePolymers n) polymer hpolymer,
    rfl⟩

/-- Any canonical polymer with strictly positive activity has strictly
positive normalized occurrence probability in its finite gas. -/
theorem anchorPolymerOccurrenceProbability_pos_of_activity
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (hactivity : (0 : Q') <
      canonicalSurfaceActivity anchorCoupling n polymer) :
    (0 : Q') < anchorPolymerOccurrenceProbability n polymer := by
  have hfamily : [polymer] ∈
      canonicalCompatibleAmbientFamilies n :=
    singleton_mem_canonicalCompatibleAmbientFamilies hpolymer
  have hevent : [polymer] ∈
      (canonicalCompatibleAmbientFamilies n).filter
        (familyContainsPolymerB polymer) := by
    apply List.mem_filter.mpr
    refine ⟨hfamily, ?_⟩
    simp [familyContainsPolymerB]
  have hfamilyPos : (0 : Q') <
      canonicalSurfaceFamilyActivity anchorCoupling n [polymer] := by
    change (0 : Q') <
      canonicalSurfaceActivity anchorCoupling n polymer * 1
    exact Q'.mul_pos hactivity (by decide)
  have hnumeratorLe := listQSum_member_le
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (canonicalSurfaceFamilyActivity_nonnegative n)
    ((canonicalCompatibleAmbientFamilies n).filter
      (familyContainsPolymerB polymer)) hevent
  have hnumeratorPos : (0 : Q') <
      anchorEventNumerator n (familyContainsPolymerB polymer) := by
    unfold anchorEventNumerator
    exact Q'.pos_of_lt_of_le hfamilyPos hnumeratorLe
  unfold anchorPolymerOccurrenceProbability anchorEventProbability Q'.divPos
  exact Q'.mul_pos hnumeratorPos
    (Q'.recipPos_pos (anchorCanonicalPartition n)
      (anchorCanonicalPartition_pos n))

/-- Re-encode the same side-two cube boundary in any larger finite box. -/
def dyadicUnitCubeSupportIdsAt (n : Nat) : List Nat :=
  transportPolymer 4 n dyadicUnitCubeSupportIds

theorem dyadicUnitCubeSupportIdsAt_mem_canonicalSurfacePolymers
    {n : Nat} (hn : 4 ≤ n) :
    dyadicUnitCubeSupportIdsAt n ∈ canonicalSurfacePolymers n := by
  unfold dyadicUnitCubeSupportIdsAt
  exact transportPolymer_mem_canonicalSurfacePolymers hn
    dyadicUnitCubeSupportIds_mem_canonicalSurfacePolymers

theorem dyadicUnitCubeSupportIdsAt_anchorActivity_pos
    {n : Nat} (hn : 4 ≤ n) :
    (0 : Q') < canonicalSurfaceActivity anchorCoupling n
      (dyadicUnitCubeSupportIdsAt n) := by
  have htransport := canonicalSurfaceActivity_transport
    anchorCoupling hn dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports
  exact Q'.pos_of_lt_of_le dyadicUnitCube_anchorActivity_pos
    (Q'.le_of_eqv htransport)

/-- Every finite box containing the refined cube gives its transported
occurrence event strictly positive probability.  This does not yet provide a
volume-independent numerical floor. -/
theorem dyadicUnitCubeSupportIdsAt_anchorOccurrenceProbability_pos
    {n : Nat} (hn : 4 ≤ n) :
    (0 : Q') < anchorPolymerOccurrenceProbability n
      (dyadicUnitCubeSupportIdsAt n) :=
  anchorPolymerOccurrenceProbability_pos_of_activity
    (dyadicUnitCubeSupportIdsAt_mem_canonicalSurfacePolymers hn)
    (dyadicUnitCubeSupportIdsAt_anchorActivity_pos hn)

#print axioms dyadicUnitCube_geometricIncidentPlaquettes_length_eq_two
#print axioms dyadicUnitCube_geometricLinkMultiplicityFactor_eq_one
#print axioms dyadicUnitCube_explicitLinkMultiplicityProduct_eqv_one
#print axioms dyadicUnitCube_canonicalSurfaceActivity_eqv
#print axioms dyadicUnitCube_canonicalSurfaceActivity_pos
#print axioms dyadicUnitCube_anchorActivity_pos
#print axioms anchorPolymerOccurrenceProbability_pos_of_activity
#print axioms dyadicUnitCubeSupportIdsAt_anchorActivity_pos
#print axioms dyadicUnitCubeSupportIdsAt_anchorOccurrenceProbability_pos

end YMGap.Continuum.Z4DyadicUnitCubeActivity
