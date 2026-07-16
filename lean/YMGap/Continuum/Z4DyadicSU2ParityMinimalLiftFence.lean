/-
# A six-face degree-one lift in the dyadic parity fibre

The literal 24-face subdivision of the coarse unit-cube boundary is not the
smallest cutoff-one state in its global cellular-parity fibre.  The boundary
of the fine unit cube based at `(1,1,1,0)` has six faces, all nondegenerate
for the dyadic cellular map, and maps with degree one onto the same coarse
six-face boundary.

This module records that configuration exactly.  Its positive activity is
the sixth power of the fundamental heat-kernel coefficient.  In particular,
after the 24-face witness has been matched by the scalar block coupling
`2 * w^4`, the remaining fibre defect still contains this sixth-order term.
This is a checked obstruction to treating the full parity fibre as a small
multiplicative perturbation of the literal-refinement scalar coordinate.
-/

import YMGap.Continuum.Z4DyadicSU2ParityActivityMatchedDefect

namespace YMGap.Continuum.Z4DyadicSU2ParityMinimalLiftFence

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSU2ParityActivityMatchedDefect
open YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact six-face lift and its cellular image -/

/-- Numerical support of the fine unit-cube boundary based at
`(1,1,1,0)` in the size-four plaquette enumeration. -/
def oddFineUnitCubeSupportIds : List Nat :=
  [504, 505, 507, 528, 601, 891]

/-- The same carrier before finite-box numerical encoding. -/
def oddFineUnitCubeSurface : List Z4Plaq :=
  [((1, 1, 1, 0), .p01),
    ((1, 1, 1, 0), .p02),
    ((1, 1, 1, 0), .p12),
    ((1, 1, 2, 0), .p01),
    ((1, 2, 1, 0), .p02),
    ((2, 1, 1, 0), .p12)]

theorem oddFineUnitCubeSupportIds_length :
    oddFineUnitCubeSupportIds.length = 6 := rfl

theorem oddFineUnitCubeSupportIds_eq_geometric :
    oddFineUnitCubeSupportIds =
      geometricSupportIds 4 oddFineUnitCubeSurface := by
  decide

theorem oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports :
    oddFineUnitCubeSupportIds ∈ cutoffOneFaceSupports 4 := by
  rw [oddFineUnitCubeSupportIds_eq_geometric]
  exact geometricSupportIds_mem_cutoffOneFaceSupports
    4 oddFineUnitCubeSurface

/-- Every face of the odd-based fine cube is nondegenerate, and the six
faces map one-to-one to the six faces of the coarse unit cube. -/
theorem dyadicParityTargetSupportIds_oddFineUnitCube :
    dyadicParityTargetSupportIds 2
        (componentLabel oddFineUnitCubeSupportIds) =
      coarseUnitCubeSupportIds := by
  decide

theorem oddFineUnitCubeLabel_mem_fineStateSpace :
    componentLabel oddFineUnitCubeSupportIds ∈
      dyadicParityFineStateSpace 1 2 := by
  unfold dyadicParityFineStateSpace
  rw [explicitPhysicalLabellings_one_eq_supportIndicators]
  exact List.mem_map.mpr
    ⟨oddFineUnitCubeSupportIds,
      oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports, rfl⟩

theorem dyadicParityGlobalKernel_oddFineUnitCube_to_coarseCube :
    dyadicParityGlobalKernel 2
        (componentLabel oddFineUnitCubeSupportIds)
        (componentLabel coarseUnitCubeSupportIds) = 1 := by
  unfold dyadicParityGlobalKernel deterministicKernel
  rw [excitedPlaquetteIds_componentLabel_eq_support
    coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports]
  rw [dyadicParityTargetSupportIds_oddFineUnitCube]
  rfl

/-- The six-face lift is genuinely distinct from the literal 24-face
refinement already used to match the coarse activity. -/
theorem oddFineUnitCubeLabel_ne_refinedUnitCubeLabel :
    componentLabel oddFineUnitCubeSupportIds ≠
      componentLabel dyadicUnitCubeSupportIds := by
  intro heq
  have hids := congrArg (excitedPlaquetteIds 4) heq
  rw [excitedPlaquetteIds_componentLabel_eq_support
      oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports,
    excitedPlaquetteIds_componentLabel_eq_support
      dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports] at hids
  have hlength := congrArg List.length hids
  rw [oddFineUnitCubeSupportIds_length,
    dyadicUnitCubeSupportIds_length] at hlength
  omega

/-! ## 2. Exact local Haar normalization and activity -/

/-- Every link touched by the shifted elementary cube has exactly two
incident faces in that cube.  This proof exhausts the six faces and their
four boundary links; it does not appeal to a translated-surface axiom. -/
theorem oddFineUnitCube_geometricIncidentPlaquettes_length_eq_two
    {link : Z4Link}
    (hlink : link ∈ geometricTouchedLinks oddFineUnitCubeSurface) :
    (geometricIncidentPlaquettes oddFineUnitCubeSurface link).length = 2 := by
  rw [mem_geometricTouchedLinks] at hlink
  obtain ⟨plaquette, hplaquette, hboundary⟩ := hlink
  simp only [oddFineUnitCubeSurface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [edgesOf, dirsOf, addE] at hboundary
  all_goals rcases hboundary with rfl | rfl | rfl | rfl
  all_goals decide

/-- The numerical carrier decodes to precisely the shifted geometric cube. -/
theorem oddFineUnitCubeSupportIds_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 4 oddFineUnitCubeSupportIds)
      oddFineUnitCubeSurface := by
  rw [oddFineUnitCubeSupportIds_eq_geometric]
  apply geometricSupportIds_sameSupport
  intro plaquette hplaquette
  rw [mem_boxPlaquettes]
  simp only [oddFineUnitCubeSurface, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem oddFineUnitCube_geometricLinkMultiplicityFactor_eq_one
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 4
      (componentLabel oddFineUnitCubeSupportIds)) :
    geometricLinkMultiplicityFactor
      (geometricPolymer 4 oddFineUnitCubeSupportIds) link = 1 := by
  have hgeometric :=
    (mem_touchedPhysicalLinks_iff_geometric
      oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports link).mp hlink
  have hshifted : link ∈
      geometricTouchedLinks oddFineUnitCubeSurface := by
    obtain ⟨plaquette, hplaquette, hboundary⟩ :=
      mem_geometricTouchedLinks.mp hgeometric
    exact mem_geometricTouchedLinks.mpr
      ⟨plaquette,
        oddFineUnitCubeSupportIds_sameSupport.1 plaquette hplaquette,
        hboundary⟩
  have hsame := geometricIncidentPlaquettes_sameSupport
    oddFineUnitCubeSupportIds_sameSupport link
  have hleftNodup := geometricIncidentPlaquettes_nodup
    oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports link
  have hrightNodup :
      (geometricIncidentPlaquettes oddFineUnitCubeSurface link).Nodup := by
    unfold geometricIncidentPlaquettes
    exact List.filter_sublist.nodup (by decide)
  have hlength := sameSupport_length_eq_of_nodup
    hsame hleftNodup hrightNodup
  have htwo :
      (geometricIncidentPlaquettes
        (geometricPolymer 4 oddFineUnitCubeSupportIds) link).length = 2 :=
    hlength.trans
      (oddFineUnitCube_geometricIncidentPlaquettes_length_eq_two hshifted)
  unfold geometricLinkMultiplicityFactor
  rw [htwo]
  rfl

private theorem oddFineUnitCube_geometricLinkMultiplicityProduct_eqv_one_on :
    ∀ links : List Z4Link,
    (∀ link, link ∈ links →
      link ∈ touchedPhysicalLinks 4
        (componentLabel oddFineUnitCubeSupportIds)) →
    geometricLinkMultiplicityProduct
      (geometricPolymer 4 oddFineUnitCubeSupportIds) links ≈ 1
  | [], _ => Q'.eqv_refl _
  | link :: rest, hsubset => by
      change (geometricLinkMultiplicityFactor
          (geometricPolymer 4 oddFineUnitCubeSupportIds) link *
        geometricLinkMultiplicityProduct
          (geometricPolymer 4 oddFineUnitCubeSupportIds) rest) ≈ 1
      rw [oddFineUnitCube_geometricLinkMultiplicityFactor_eq_one
        (hsubset link List.mem_cons_self)]
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _
          (oddFineUnitCube_geometricLinkMultiplicityProduct_eqv_one_on
            rest (fun item hitem =>
              hsubset item (List.mem_cons_of_mem link hitem))))
        (Q'.one_mul_eqv 1)

/-- The six-face lift is a closed elementary cube: every touched link has
two fundamental incident faces, so the full explicit invariant-multiplicity
product is exactly one. -/
theorem oddFineUnitCube_explicitLinkMultiplicityProduct_eqv_one :
    explicitLinkMultiplicityProduct 1 4
      (componentLabel oddFineUnitCubeSupportIds)
      (touchedIndexedLinks 4
        (componentLabel oddFineUnitCubeSupportIds)) ≈ 1 :=
  Q'.eqv_trans _ _ _
    (explicitLinkMultiplicityProduct_componentLabel_eqv_geometric
      oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports)
    (oddFineUnitCube_geometricLinkMultiplicityProduct_eqv_one_on _
      (fun _ hlink => hlink))

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Exact weight of the non-witness lift, with no fitted normalization. -/
theorem oddFineUnitCube_canonicalSurfaceActivity_eqv
    (fineCoupling : Q') :
    canonicalSurfaceActivity fineCoupling 4
        oddFineUnitCubeSupportIds ≈
      (coeffW fineCoupling 1) ^ 6 := by
  have hface := parametricPhysicalFaceFactor_componentLabel_eqv_pow
    fineCoupling oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports
  rw [oddFineUnitCubeSupportIds_length] at hface
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  change (parametricPhysicalFaceFactor fineCoupling 4
      (componentLabel oddFineUnitCubeSupportIds) *
    explicitLinkMultiplicityProduct 1 4
      (componentLabel oddFineUnitCubeSupportIds)
      (touchedIndexedLinks 4
        (componentLabel oddFineUnitCubeSupportIds))) ≈
      (coeffW fineCoupling 1) ^ 6
  exact Q'.eqv_trans _ ((coeffW fineCoupling 1) ^ 6 * 1) _
    (qmul_congr_local hface
      oddFineUnitCube_explicitLinkMultiplicityProduct_eqv_one)
    (Q'.mul_one_eqv _)

/-- The actual cutoff-one fine spin-foam term has the same exact sixth-order
formula. -/
theorem oddFineUnitCubeTerm_eqv_sixthPower
    (fineCoupling : Q') :
    parametricKPhysicalTerm fineCoupling 1 4
        (componentLabel oddFineUnitCubeSupportIds) ≈
      (coeffW fineCoupling 1) ^ 6 :=
  Q'.eqv_trans _ _ _
    (parametricKPhysicalTerm_one_eqv_localized
      fineCoupling 4 (componentLabel oddFineUnitCubeSupportIds))
    (oddFineUnitCube_canonicalSurfaceActivity_eqv fineCoupling)

/-! ## 3. The sixth-order term remains after activity matching -/

private theorem listQSum_two_distinct_members_le {A : Type}
    (weight : A → Q') (hweight : ∀ item, (0 : Q') ≤ weight item) :
    ∀ (items : List A) {first second : A},
      first ∈ items → second ∈ items → first ≠ second →
        weight first + weight second ≤ listQSum weight items
  | [], _, _, hfirst, _, _ => absurd hfirst List.not_mem_nil
  | head :: rest, first, second, hfirst, hsecond, hne => by
      rcases List.mem_cons.mp hfirst with hfirstHead | hfirstRest
      · subst first
        have hsecondRest : second ∈ rest :=
          (List.mem_cons.mp hsecond).resolve_left
            (fun h => hne h.symm)
        exact Q'.add_le_add_left (weight head) _ _
          (listQSum_member_le weight hweight rest hsecondRest)
      · rcases List.mem_cons.mp hsecond with hsecondHead | hsecondRest
        · subst second
          have hrest := listQSum_member_le
            weight hweight rest hfirstRest
          have hordered := Q'.add_le_add_left
            (weight head) _ _ hrest
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.add_comm_eqv _ _)) hordered
        · have htail := listQSum_two_distinct_members_le
            weight hweight rest hfirstRest hsecondRest hne
          have hhead : listQSum weight rest ≤
              weight head + listQSum weight rest := by
            have h := Q'.add_le_add_right
              0 (weight head) (listQSum weight rest) (hweight head)
            rwa [Q'.zero_add'] at h
          exact Q'.le_trans' _ _ _ htail hhead

/-- Abstract two-state fibre lower bound.  Keeping the box variables
symbolic prevents theorem elaboration from evaluating the complete concrete
fine-state enumeration. -/
theorem dyadicParityParametricKernelPushforwardWeight_two_members_le
    {fineCoupling : Q'} (hfine : (0 : Q') ≤ fineCoupling)
    {K n : Nat} {first second coarsePhysical : EdgeLabelling}
    (hfirst : first ∈ dyadicParityFineStateSpace K n)
    (hsecond : second ∈ dyadicParityFineStateSpace K n)
    (hne : first ≠ second) :
    parametricKPhysicalTerm fineCoupling K (2 * n) first *
          dyadicParityGlobalKernel n first coarsePhysical +
        parametricKPhysicalTerm fineCoupling K (2 * n) second *
          dyadicParityGlobalKernel n second coarsePhysical ≤
      dyadicParityParametricKernelPushforwardWeight
        fineCoupling K n coarsePhysical := by
  unfold dyadicParityParametricKernelPushforwardWeight
  unfold kernelPushforwardWeight
  unfold dyadicParityGlobalKernel
  let fibreWeight : EdgeLabelling → Q' := fun finePhysical =>
    parametricKPhysicalTerm fineCoupling K (2 * n) finePhysical *
      deterministicKernel (dyadicParityTargetSupportIds n) finePhysical
        (excitedPlaquetteIds n coarsePhysical)
  have hfibreWeight : ∀ finePhysical, (0 : Q') ≤
      fibreWeight finePhysical := by
    intro finePhysical
    exact Q'.mul_nonneg _ _
      (parametricKPhysicalTerm_nonnegative
        hfine K (2 * n) finePhysical)
      (deterministicKernel_nonnegative
        (dyadicParityTargetSupportIds n) finePhysical
        (excitedPlaquetteIds n coarsePhysical))
  exact listQSum_two_distinct_members_le
    fibreWeight hfibreWeight (dyadicParityFineStateSpace K n)
    hfirst hsecond hne

/-- Both distinct fine configurations contribute simultaneously to the
same parity fibre. -/
theorem oddAndRefinedIntegrands_le_parityPushforward
    {fineCoupling : Q'} (hfine : (0 : Q') ≤ fineCoupling) :
    parametricKPhysicalTerm fineCoupling 1 4
          (componentLabel oddFineUnitCubeSupportIds) *
        dyadicParityGlobalKernel 2
          (componentLabel oddFineUnitCubeSupportIds)
          (componentLabel coarseUnitCubeSupportIds) +
      parametricKPhysicalTerm fineCoupling 1 4
          (componentLabel dyadicUnitCubeSupportIds) *
        dyadicParityGlobalKernel 2
          (componentLabel dyadicUnitCubeSupportIds)
          (componentLabel coarseUnitCubeSupportIds) ≤
      dyadicParityParametricKernelPushforwardWeight
        fineCoupling 1 2
        (componentLabel coarseUnitCubeSupportIds) := by
  exact dyadicParityParametricKernelPushforwardWeight_two_members_le
    (fineCoupling := fineCoupling) (K := 1) (n := 2)
    (first := componentLabel oddFineUnitCubeSupportIds)
    (second := componentLabel dyadicUnitCubeSupportIds)
    (coarsePhysical := componentLabel coarseUnitCubeSupportIds)
    hfine oddFineUnitCubeLabel_mem_fineStateSpace
    refinedUnitCubeLabel_mem_fineStateSpace
    oddFineUnitCubeLabel_ne_refinedUnitCubeLabel

theorem oddAndRefinedTerms_le_parityPushforward
    {fineCoupling : Q'} (hfine : (0 : Q') ≤ fineCoupling) :
    parametricKPhysicalTerm fineCoupling 1 4
          (componentLabel oddFineUnitCubeSupportIds) +
      parametricKPhysicalTerm fineCoupling 1 4
          (componentLabel dyadicUnitCubeSupportIds) ≤
      dyadicParityParametricKernelPushforwardWeight
        fineCoupling 1 2
        (componentLabel coarseUnitCubeSupportIds) := by
  have hsum := oddAndRefinedIntegrands_le_parityPushforward hfine
  have hodd :
      parametricKPhysicalTerm fineCoupling 1 4
            (componentLabel oddFineUnitCubeSupportIds) *
          dyadicParityGlobalKernel 2
            (componentLabel oddFineUnitCubeSupportIds)
            (componentLabel coarseUnitCubeSupportIds) ≈
        parametricKPhysicalTerm fineCoupling 1 4
          (componentLabel oddFineUnitCubeSupportIds) := by
    rw [dyadicParityGlobalKernel_oddFineUnitCube_to_coarseCube]
    exact Q'.mul_one_eqv _
  have hrefined :
      parametricKPhysicalTerm fineCoupling 1 4
            (componentLabel dyadicUnitCubeSupportIds) *
          dyadicParityGlobalKernel 2
            (componentLabel dyadicUnitCubeSupportIds)
            (componentLabel coarseUnitCubeSupportIds) ≈
        parametricKPhysicalTerm fineCoupling 1 4
          (componentLabel dyadicUnitCubeSupportIds) := by
    rw [dyadicParityGlobalKernel_refinedUnitCube_to_coarseCube]
    exact Q'.mul_one_eqv _
  have hsource := Q'.add_eqv_congr'
    (Q'.eqv_symm hodd) (Q'.eqv_symm hrefined)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsource) hsum

private theorem le_add_neg_of_add_le_local {a Y X : Q'}
    (h : a + Y ≤ X) : a ≤ X + -Y := by
  have hstep : (a + Y) + -Y ≤ X + -Y :=
    Q'.add_le_add h (Q'.le_refl' (-Y))
  have heq : ((a + Y) + -Y) ≈ a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a Y (-Y)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a (Y + -Y) 0
        (Q'.add_neg_self_eqv Y)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hstep

/-- The activity-matched additive defect contains the complete six-face
term, uniformly as an exact statement in the fine coupling. -/
theorem oddFineUnitCubeTerm_le_activityMatchedParityFibreDefect
    {fineCoupling : Q'} (hfine : (0 : Q') ≤ fineCoupling) :
    parametricKPhysicalTerm fineCoupling 1 4
        (componentLabel oddFineUnitCubeSupportIds) ≤
      activityMatchedParityFibreDefect fineCoupling := by
  have hpair := oddAndRefinedTerms_le_parityPushforward hfine
  have hreplace :
      parametricKPhysicalTerm fineCoupling 1 4
            (componentLabel oddFineUnitCubeSupportIds) +
          parametricKPhysicalTerm
            (unitCubeBlockCoupling fineCoupling) 1 2
            (componentLabel coarseUnitCubeSupportIds) ≈
        parametricKPhysicalTerm fineCoupling 1 4
            (componentLabel oddFineUnitCubeSupportIds) +
          parametricKPhysicalTerm fineCoupling 1 4
            (componentLabel dyadicUnitCubeSupportIds) :=
    Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (refinedCubeTerm_eqv_activityMatchedCoarseTerm fineCoupling))
  have hmatched :
      parametricKPhysicalTerm fineCoupling 1 4
            (componentLabel oddFineUnitCubeSupportIds) +
          parametricKPhysicalTerm
            (unitCubeBlockCoupling fineCoupling) 1 2
            (componentLabel coarseUnitCubeSupportIds) ≤
        dyadicParityParametricKernelPushforwardWeight
          fineCoupling 1 2
          (componentLabel coarseUnitCubeSupportIds) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hreplace) hpair
  unfold activityMatchedParityFibreDefect
  exact le_add_neg_of_add_le_local hmatched

/-- The obstruction retains a positive sixth power of the exact heat-kernel
coefficient, independent of ambient vacuum multiplicities. -/
theorem sixthPower_le_activityMatchedParityFibreDefect
    {fineCoupling : Q'} (hfine : (0 : Q') ≤ fineCoupling) :
    (coeffW fineCoupling 1) ^ 6 ≤
      activityMatchedParityFibreDefect fineCoupling := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (oddFineUnitCubeTerm_eqv_sixthPower fineCoupling)))
    (oddFineUnitCubeTerm_le_activityMatchedParityFibreDefect hfine)

#print axioms oddFineUnitCubeSupportIds_mem_cutoffOneFaceSupports
#print axioms dyadicParityTargetSupportIds_oddFineUnitCube
#print axioms oddFineUnitCubeLabel_mem_fineStateSpace
#print axioms dyadicParityGlobalKernel_oddFineUnitCube_to_coarseCube
#print axioms oddFineUnitCubeLabel_ne_refinedUnitCubeLabel
#print axioms oddFineUnitCube_geometricIncidentPlaquettes_length_eq_two
#print axioms oddFineUnitCube_geometricLinkMultiplicityFactor_eq_one
#print axioms oddFineUnitCube_explicitLinkMultiplicityProduct_eqv_one
#print axioms oddFineUnitCube_canonicalSurfaceActivity_eqv
#print axioms oddFineUnitCubeTerm_eqv_sixthPower
#print axioms dyadicParityParametricKernelPushforwardWeight_two_members_le
#print axioms oddAndRefinedIntegrands_le_parityPushforward
#print axioms oddAndRefinedTerms_le_parityPushforward
#print axioms oddFineUnitCubeTerm_le_activityMatchedParityFibreDefect
#print axioms sixthPower_le_activityMatchedParityFibreDefect

end YMGap.Continuum.Z4DyadicSU2ParityMinimalLiftFence
