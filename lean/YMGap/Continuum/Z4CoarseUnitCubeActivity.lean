/-
# Exact activity and block normalization of the elementary cube

The coarse six-face cube and its 24-face dyadic refinement are now canonical
polymers in the same support language.  This module audits the coarse Haar
factor: every touched link sees exactly two fundamental faces, so every local
invariant multiplicity is one.  The coarse activity is therefore exactly the
sixth power of the derived fundamental heat-kernel coefficient.

Combining this formula with the refined-cube formula proves the exact bare
block identity: at one coupling the refined activity is the fourth power of
the coarse activity.  This is the normalization identity an RG comparison
must perturb; it is not an equality of normalized Gibbs probabilities.
-/

import YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
import YMGap.Continuum.Z4DyadicUnitCubeActivity

namespace YMGap.Continuum.Z4CoarseUnitCubeActivity

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
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

theorem coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports :
    coarseUnitCubeSupportIds ∈ cutoffOneFaceSupports 2 :=
  canonicalSurfacePolymer_mem_faceSupports
    coarseUnitCubeSupportIds_mem_canonicalSurfacePolymers

private theorem coarseCubeLink_mem_of_touched
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 2
      (componentLabel coarseUnitCubeSupportIds)) :
    link ∈ geometricTouchedLinks unitCubeSurface := by
  have hgeometric :=
    (mem_touchedPhysicalLinks_iff_geometric
      coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports link).mp hlink
  obtain ⟨plaquette, hplaquette, hboundary⟩ :=
    mem_geometricTouchedLinks.mp hgeometric
  exact mem_geometricTouchedLinks.mpr
    ⟨plaquette,
      coarseUnitCubeSupportIds_sameSupport.1 plaquette hplaquette,
      hboundary⟩

/-- Every touched link has exactly two incident faces in the canonical
coarse support. -/
theorem coarseUnitCube_geometricIncidentPlaquettes_length_eq_two
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 2
      (componentLabel coarseUnitCubeSupportIds)) :
    (geometricIncidentPlaquettes
      (geometricPolymer 2 coarseUnitCubeSupportIds) link).length = 2 := by
  have hsame := geometricIncidentPlaquettes_sameSupport
    coarseUnitCubeSupportIds_sameSupport link
  have hleftNodup := geometricIncidentPlaquettes_nodup
    coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports link
  have hrightNodup :
      (geometricIncidentPlaquettes unitCubeSurface link).Nodup := by
    unfold geometricIncidentPlaquettes
    exact List.filter_sublist.nodup unitCubeSurface_nodup
  have hlength := sameSupport_length_eq_of_nodup
    hsame hleftNodup hrightNodup
  exact hlength.trans
    (unitCube_geometricIncidentPlaquettes_length_eq_two
      (coarseCubeLink_mem_of_touched hlink))

/-- The local invariant multiplicity at every touched coarse link is one. -/
theorem coarseUnitCube_geometricLinkMultiplicityFactor_eq_one
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 2
      (componentLabel coarseUnitCubeSupportIds)) :
    geometricLinkMultiplicityFactor
      (geometricPolymer 2 coarseUnitCubeSupportIds) link = 1 := by
  unfold geometricLinkMultiplicityFactor
  rw [coarseUnitCube_geometricIncidentPlaquettes_length_eq_two hlink]
  rfl

private theorem coarseUnitCube_geometricLinkMultiplicityProduct_eqv_one_on :
    ∀ links : List Z4Link,
    (∀ link, link ∈ links →
      link ∈ touchedPhysicalLinks 2
        (componentLabel coarseUnitCubeSupportIds)) →
    geometricLinkMultiplicityProduct
      (geometricPolymer 2 coarseUnitCubeSupportIds) links ≈ 1
  | [], _ => Q'.eqv_refl _
  | link :: rest, hsubset => by
      change (geometricLinkMultiplicityFactor
          (geometricPolymer 2 coarseUnitCubeSupportIds) link *
        geometricLinkMultiplicityProduct
          (geometricPolymer 2 coarseUnitCubeSupportIds) rest) ≈ 1
      rw [coarseUnitCube_geometricLinkMultiplicityFactor_eq_one
        (hsubset link List.mem_cons_self)]
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _
          (coarseUnitCube_geometricLinkMultiplicityProduct_eqv_one_on
            rest (fun item hitem =>
              hsubset item (List.mem_cons_of_mem link hitem))))
        (Q'.one_mul_eqv 1)

theorem coarseUnitCube_geometricLinkMultiplicityProduct_eqv_one :
    geometricLinkMultiplicityProduct
      (geometricPolymer 2 coarseUnitCubeSupportIds)
      (touchedPhysicalLinks 2
        (componentLabel coarseUnitCubeSupportIds)) ≈ 1 :=
  coarseUnitCube_geometricLinkMultiplicityProduct_eqv_one_on _
    (fun _ hlink => hlink)

/-- The production finite-box link product is exactly one. -/
theorem coarseUnitCube_explicitLinkMultiplicityProduct_eqv_one :
    explicitLinkMultiplicityProduct 1 2
      (componentLabel coarseUnitCubeSupportIds)
      (touchedIndexedLinks 2
        (componentLabel coarseUnitCubeSupportIds)) ≈ 1 :=
  Q'.eqv_trans _ _ _
    (explicitLinkMultiplicityProduct_componentLabel_eqv_geometric
      coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports)
    coarseUnitCube_geometricLinkMultiplicityProduct_eqv_one

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Exact non-vacuous activity formula for the six-face coarse block. -/
theorem coarseUnitCube_canonicalSurfaceActivity_eqv
    (coupling : Q') :
    canonicalSurfaceActivity coupling 2 coarseUnitCubeSupportIds ≈
      (coeffW coupling 1) ^ 6 := by
  have hface := parametricPhysicalFaceFactor_componentLabel_eqv_pow
    coupling coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports
  rw [coarseUnitCubeSupportIds_length] at hface
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  change (parametricPhysicalFaceFactor coupling 2
      (componentLabel coarseUnitCubeSupportIds) *
    explicitLinkMultiplicityProduct 1 2
      (componentLabel coarseUnitCubeSupportIds)
      (touchedIndexedLinks 2
        (componentLabel coarseUnitCubeSupportIds))) ≈
      (coeffW coupling 1) ^ 6
  exact Q'.eqv_trans _ ((coeffW coupling 1) ^ 6 * 1) _
    (qmul_congr_local hface
      coarseUnitCube_explicitLinkMultiplicityProduct_eqv_one)
    (Q'.mul_one_eqv _)

private theorem qpow_pos_local {value : Q'}
    (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 => Q'.mul_pos hvalue (qpow_pos_local hvalue exponent)

theorem coarseUnitCube_canonicalSurfaceActivity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') <
      canonicalSurfaceActivity coupling 2 coarseUnitCubeSupportIds := by
  have hcoefficient : (0 : Q') < coeffW coupling 1 :=
    YMGap.Continuum.FusionResidualBound.coeffW_pos hcoupling 1
  have hpower := qpow_pos_local hcoefficient 6
  exact Q'.pos_of_lt_of_le hpower
    (Q'.ge_of_eqv
      (coarseUnitCube_canonicalSurfaceActivity_eqv coupling))

theorem coarseUnitCube_anchorActivity_pos :
    (0 : Q') < canonicalSurfaceActivity anchorCoupling 2
      coarseUnitCubeSupportIds :=
  coarseUnitCube_canonicalSurfaceActivity_pos (by decide)

private theorem pow_pow_eqv (value : Q') (outer : Nat) :
    ∀ inner : Nat,
      ((value ^ outer) ^ inner) ≈ value ^ (outer * inner)
  | 0 => by
      simp only [Nat.mul_zero, Q'.pow_zero]
      exact Q'.eqv_refl 1
  | inner + 1 => by
      rw [Q'.pow_succ]
      refine Q'.eqv_trans _
        (value ^ outer * value ^ (outer * inner)) _
        (Q'.mul_eqv_congr_left _ _ _
          (pow_pow_eqv value outer inner)) ?_
      have hsum := Q'.eqv_symm
        (Q'.pow_add_eqv value outer (outer * inner))
      have hexponent : outer * (inner + 1) = outer + outer * inner := by
        rw [Nat.mul_succ, Nat.add_comm]
      rw [hexponent]
      exact hsum

/-- Exact bare block normalization: refining each of the six faces into four
faces raises the single-polymer activity to the fourth power. -/
theorem dyadicUnitCube_activity_eqv_coarse_activity_pow_four
    (coupling : Q') :
    canonicalSurfaceActivity coupling 4 dyadicUnitCubeSupportIds ≈
      (canonicalSurfaceActivity coupling 2
        coarseUnitCubeSupportIds) ^ 4 := by
  have hrefined := dyadicUnitCube_canonicalSurfaceActivity_eqv coupling
  have hcoarse := coarseUnitCube_canonicalSurfaceActivity_eqv coupling
  have hnested := pow_pow_eqv (coeffW coupling 1) 6 4
  have hexponent : 6 * 4 = 24 := by omega
  rw [hexponent] at hnested
  exact Q'.eqv_trans _ ((coeffW coupling 1) ^ 24) _ hrefined
    (Q'.eqv_trans _ (((coeffW coupling 1) ^ 6) ^ 4) _
      (Q'.eqv_symm hnested)
      (Q'.eqv_symm
        (YMGap.Continuum.ClusteringImpliesGap.pow_eqv_congr
          (canonicalSurfaceActivity coupling 2 coarseUnitCubeSupportIds)
          ((coeffW coupling 1) ^ 6) hcoarse 4)))

#print axioms coarseUnitCube_geometricIncidentPlaquettes_length_eq_two
#print axioms coarseUnitCube_geometricLinkMultiplicityFactor_eq_one
#print axioms coarseUnitCube_explicitLinkMultiplicityProduct_eqv_one
#print axioms coarseUnitCube_canonicalSurfaceActivity_eqv
#print axioms coarseUnitCube_canonicalSurfaceActivity_pos
#print axioms dyadicUnitCube_activity_eqv_coarse_activity_pow_four

end YMGap.Continuum.Z4CoarseUnitCubeActivity
