/-
# Exact cutoff-one activity with one four-valent boundary link

A cubical boundary need not be a combinatorial manifold: two sheets may meet
along one lattice link.  At cutoff one such a link carries four fundamental
representations and therefore contributes the exact SU(2) invariant
multiplicity two.  This module proves the corresponding support-wide product
formula.  Every other touched link is required to have incidence two.
-/

import YMGap.Continuum.Z4AxisCubeSixFaceActivity

namespace YMGap.Continuum.Z4SingleFourIncidenceActivity

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4AxisCubeSixFaceActivity
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

theorem geometricLinkMultiplicityFactor_eq_two_of_incidence_four
    {support : List Z4Plaq} {link : Z4Link}
    (hincidence :
      (geometricIncidentPlaquettes support link).length = 4) :
    geometricLinkMultiplicityFactor support link = 2 := by
  unfold geometricLinkMultiplicityFactor
  rw [hincidence]
  rfl

private theorem geometricLinkMultiplicityProduct_eqv_one_of_all_two
    (support : List Z4Plaq) : ∀ links : List Z4Link,
    (∀ link, link ∈ links →
      (geometricIncidentPlaquettes support link).length = 2) →
    geometricLinkMultiplicityProduct support links ≈ 1
  | [], _ => Q'.eqv_refl _
  | link :: rest, hincidence => by
      change (geometricLinkMultiplicityFactor support link *
        geometricLinkMultiplicityProduct support rest) ≈ 1
      have hhead : geometricLinkMultiplicityFactor support link = 1 := by
        unfold geometricLinkMultiplicityFactor
        rw [hincidence link List.mem_cons_self]
        rfl
      rw [hhead]
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _
          (geometricLinkMultiplicityProduct_eqv_one_of_all_two support rest
            (fun item hitem => hincidence item
              (List.mem_cons_of_mem link hitem))))
        (Q'.one_mul_eqv 1)

private theorem geometricLinkMultiplicityProduct_eqv_two_of_single_four
    (support : List Z4Plaq) (distinguished : Z4Link) :
    ∀ links : List Z4Link,
    links.Nodup →
    distinguished ∈ links →
    (geometricIncidentPlaquettes support distinguished).length = 4 →
    (∀ link, link ∈ links → link ≠ distinguished →
      (geometricIncidentPlaquettes support link).length = 2) →
    geometricLinkMultiplicityProduct support links ≈ 2
  | [], _, hmem, _, _ => absurd hmem List.not_mem_nil
  | link :: rest, hnodup, hmem, hfour, hother => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases heq : link = distinguished
      · subst link
        change (geometricLinkMultiplicityFactor support distinguished *
          geometricLinkMultiplicityProduct support rest) ≈ 2
        rw [geometricLinkMultiplicityFactor_eq_two_of_incidence_four hfour]
        have hrest : geometricLinkMultiplicityProduct support rest ≈ 1 :=
          geometricLinkMultiplicityProduct_eqv_one_of_all_two support rest
            (fun item hitem => hother item
              (List.mem_cons_of_mem distinguished hitem)
              (fun heq => hparts.1 (heq ▸ hitem)))
        exact Q'.eqv_trans _ (2 * 1) _
          (Q'.mul_eqv_congr_left 2 _ _ hrest)
          (Q'.mul_one_eqv 2)
      · have hheadIncidence := hother link List.mem_cons_self heq
        have hheadFactor :
            geometricLinkMultiplicityFactor support link = 1 := by
          unfold geometricLinkMultiplicityFactor
          rw [hheadIncidence]
          rfl
        change (geometricLinkMultiplicityFactor support link *
          geometricLinkMultiplicityProduct support rest) ≈ 2
        rw [hheadFactor]
        have hmemRest : distinguished ∈ rest :=
          (List.mem_cons.mp hmem).resolve_left (fun h => heq h.symm)
        have hrest := geometricLinkMultiplicityProduct_eqv_two_of_single_four
          support distinguished rest hparts.2 hmemRest hfour
          (fun item hitem hne => hother item
            (List.mem_cons_of_mem link hitem) hne)
        exact Q'.eqv_trans _ (1 * 2) _
          (Q'.mul_eqv_congr_left 1 _ _ hrest)
          (Q'.one_mul_eqv 2)

theorem explicitLinkMultiplicityProduct_eqv_two_of_single_four
    {n : Nat} {support : List Nat} (distinguished : Z4Link)
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hmem : distinguished ∈
      touchedPhysicalLinks n (componentLabel support))
    (hfour :
      (geometricIncidentPlaquettes
        (geometricPolymer n support) distinguished).length = 4)
    (hother : ∀ {link : Z4Link},
      link ∈ touchedPhysicalLinks n (componentLabel support) →
      link ≠ distinguished →
      (geometricIncidentPlaquettes
        (geometricPolymer n support) link).length = 2) :
    explicitLinkMultiplicityProduct 1 n (componentLabel support)
        (touchedIndexedLinks n (componentLabel support)) ≈ 2 :=
  Q'.eqv_trans _ _ _
    (explicitLinkMultiplicityProduct_componentLabel_eqv_geometric hsupport)
    (geometricLinkMultiplicityProduct_eqv_two_of_single_four
      (geometricPolymer n support) distinguished
      (touchedPhysicalLinks n (componentLabel support))
      (touchedPhysicalLinks_nodup n (componentLabel support))
      hmem hfour (fun _ hlink hne => hother hlink hne))

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- With one four-valent touched link and all other touched links bivalent,
the complete cutoff-one activity is exactly twice the face coefficient
monomial. -/
theorem canonicalSurfaceActivity_eqv_two_mul_pow_length_of_single_four
    (coupling : Q') {n : Nat} {support : List Nat}
    (distinguished : Z4Link)
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hmem : distinguished ∈
      touchedPhysicalLinks n (componentLabel support))
    (hfour :
      (geometricIncidentPlaquettes
        (geometricPolymer n support) distinguished).length = 4)
    (hother : ∀ {link : Z4Link},
      link ∈ touchedPhysicalLinks n (componentLabel support) →
      link ≠ distinguished →
      (geometricIncidentPlaquettes
        (geometricPolymer n support) link).length = 2) :
    canonicalSurfaceActivity coupling n support ≈
      (coeffW coupling 1) ^ support.length * 2 := by
  have hface :=
    parametricPhysicalFaceFactor_componentLabel_eqv_pow coupling hsupport
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  change (parametricPhysicalFaceFactor coupling n
      (componentLabel support) *
    explicitLinkMultiplicityProduct 1 n (componentLabel support)
      (touchedIndexedLinks n (componentLabel support))) ≈
      (coeffW coupling 1) ^ support.length * 2
  exact qmul_congr_local hface
    (explicitLinkMultiplicityProduct_eqv_two_of_single_four
      distinguished hsupport hmem hfour hother)

#print axioms geometricLinkMultiplicityFactor_eq_two_of_incidence_four
#print axioms explicitLinkMultiplicityProduct_eqv_two_of_single_four
#print axioms canonicalSurfaceActivity_eqv_two_mul_pow_length_of_single_four

end YMGap.Continuum.Z4SingleFourIncidenceActivity
