/-
# Adjacent-even assembled physical-summand factorization

This leaf attaches the already proved endpoint-trajectory calculation to the
complete corrected-slab physical term.  It first splits every face and link
product into lower, fixed-interface, and upper parts.  At anchor coupling the
fixed part is then rewritten as the literal fixed-face coefficient times the
collapsed endpoint-trajectory sum.  Finally reflection identifies the upper
endpoint amplitude with the same lower-amplitude coordinate on the swapped
assembly.

This is an exact finite identity.  It does not assert that the remaining
directed interface kernel is Gram; that is the subsequent positivity
obligation.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedEndpointAmplitude

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAssembledSlabFactorization

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceCoefficientAttachment
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkGlobalTrajectoryIntegration
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedEndpointAmplitude
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTerminalDeltaCollapse
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal three-way adjacent-even factors -/

def adjacentEvenLowerLinks (radius : Nat) : List Z4Link :=
  (adjacentEvenSlabLinkParts radius).1

def adjacentEvenUpperLinks (radius : Nat) : List Z4Link :=
  (adjacentEvenSlabLinkParts radius).2.2

def adjacentEvenLowerFactor
    (w : Q') (K radius : Nat) (physical : EdgeLabelling) : Q' :=
  slabFaceFactorOn w K physical (adjacentEvenLowerFaceIds radius) *
    Q'.ofNat (slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
      physical (adjacentEvenLowerLinks radius))

def adjacentEvenFixedWeight
    (w : Q') (K radius : Nat) (physical : EdgeLabelling) : Q' :=
  slabFaceFactorOn w K physical (adjacentEvenFixedFaceIds radius) *
    Q'.ofNat (slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
      physical (adjacentEvenFixedLinks radius))

def adjacentEvenUpperFactor
    (w : Q') (K radius : Nat) (physical : EdgeLabelling) : Q' :=
  slabFaceFactorOn w K physical (adjacentEvenUpperFaceIds radius) *
    Q'.ofNat (slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
      physical (adjacentEvenUpperLinks radius))

private theorem eliminateLinks_append_local
    (value : Nat -> Q') : forall (left right : List Nat),
    eliminateLinks value (left ++ right) ≈
      eliminateLinks value left * eliminateLinks value right
  | [], right => Q'.eqv_symm (Q'.one_mul_eqv _)
  | head :: tail, right => by
      simp only [List.cons_append, eliminateLinks]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_append_local value tail right))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem natListProduct_append_local {A : Type}
    (value : A -> Nat) : forall (left right : List A),
    natListProduct value (left ++ right) =
      natListProduct value left * natListProduct value right
  | [], right => by simp [natListProduct]
  | _ :: tail, right => by
      simp only [List.cons_append, natListProduct]
      rw [natListProduct_append_local value tail right, Nat.mul_assoc]

private theorem ofNat_mul_eqv_local (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show (Q'.ofNat (a * b)).num *
      (((Q'.ofNat a * Q'.ofNat b).den) : Int) =
    (Q'.ofNat a * Q'.ofNat b).num *
      (((Q'.ofNat (a * b)).den) : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast]
  push_cast
  omega

private theorem rearrange_six_local
    (a b c d e f : Q') :
    (a * (b * c)) * (d * (e * f)) ≈
      (a * d) * ((b * e) * (c * f)) := by
  show ((a * (b * c)) * (d * (e * f))).num *
      ((((a * d) * ((b * e) * (c * f))).den) : Int) =
    ((a * d) * ((b * e) * (c * f))).num *
      ((((a * (b * c)) * (d * (e * f))).den) : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

/-- The complete corrected-slab physical term on the adjacent-even carrier
splits exactly into its lower, fixed-interface, and upper pieces. -/
theorem slabParametricKPhysicalTerm_adjacentEven_factorization
    (w : Q') (K radius : Nat) (physical : EdgeLabelling) :
    slabParametricKPhysicalTerm w K (adjacentEvenExtent radius) physical ≈
      adjacentEvenLowerFactor w K radius physical *
        (adjacentEvenFixedWeight w K radius physical *
          adjacentEvenUpperFactor w K radius physical) := by
  let faceValue : Nat -> Q' := fun id =>
    coeffAt (heatKernelPacket K w) (physical id)
  let linkValue : Z4Link -> Nat :=
    slabExplicitLinkMultiplicity K (adjacentEvenExtent radius) physical
  have hface :
      slabParametricKPhysicalFaceFactor w K
          (adjacentEvenExtent radius) physical ≈
        slabFaceFactorOn w K physical (adjacentEvenLowerFaceIds radius) *
          (slabFaceFactorOn w K physical
              (adjacentEvenFixedFaceIds radius) *
            slabFaceFactorOn w K physical
              (adjacentEvenUpperFaceIds radius)) := by
    unfold slabParametricKPhysicalFaceFactor slabFaceFactorOn
    calc
      eliminateLinks faceValue
          (slabPhysicalFaceEdges (adjacentEvenExtent radius)) ≈
        eliminateLinks faceValue
          (adjacentEvenLowerFaceIds radius ++
            adjacentEvenFixedFaceIds radius ++
            adjacentEvenUpperFaceIds radius) := by
          apply eliminateLinks_perm
          simpa only [adjacentEvenLowerFaceIds,
            adjacentEvenFixedFaceIds, adjacentEvenUpperFaceIds] using
            (adjacentEvenSlabFaceIdParts_perm radius).symm
      _ ≈ eliminateLinks faceValue (adjacentEvenLowerFaceIds radius) *
          eliminateLinks faceValue
            (adjacentEvenFixedFaceIds radius ++
              adjacentEvenUpperFaceIds radius) := by
        simpa only [List.append_assoc] using
          (eliminateLinks_append_local faceValue
            (adjacentEvenLowerFaceIds radius)
            (adjacentEvenFixedFaceIds radius ++
              adjacentEvenUpperFaceIds radius))
      _ ≈ eliminateLinks faceValue (adjacentEvenLowerFaceIds radius) *
          (eliminateLinks faceValue (adjacentEvenFixedFaceIds radius) *
            eliminateLinks faceValue
              (adjacentEvenUpperFaceIds radius)) :=
        Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_append_local faceValue
            (adjacentEvenFixedFaceIds radius)
            (adjacentEvenUpperFaceIds radius))
  have hlink :
      slabExplicitLinkMultiplicityProduct K
          (adjacentEvenExtent radius) physical =
        slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
            physical (adjacentEvenLowerLinks radius) *
          (slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
              physical (adjacentEvenFixedLinks radius) *
            slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
              physical (adjacentEvenUpperLinks radius)) := by
    unfold slabExplicitLinkMultiplicityProduct
      slabLinkMultiplicityProductOn
    calc
      natListProduct linkValue
          (boundaryCompleteSlabLinks (adjacentEvenExtent radius)) =
        natListProduct linkValue
          (adjacentEvenLowerLinks radius ++
            adjacentEvenFixedLinks radius ++
            adjacentEvenUpperLinks radius) := by
          apply natListProduct_perm
          simpa only [adjacentEvenLowerLinks, adjacentEvenFixedLinks,
            adjacentEvenUpperLinks] using
            (adjacentEvenSlabLinkParts_perm radius).symm
      _ = natListProduct linkValue (adjacentEvenLowerLinks radius) *
          natListProduct linkValue
            (adjacentEvenFixedLinks radius ++
              adjacentEvenUpperLinks radius) := by
        simpa only [List.append_assoc] using
          (natListProduct_append_local linkValue
            (adjacentEvenLowerLinks radius)
            (adjacentEvenFixedLinks radius ++
              adjacentEvenUpperLinks radius))
      _ = natListProduct linkValue (adjacentEvenLowerLinks radius) *
          (natListProduct linkValue (adjacentEvenFixedLinks radius) *
            natListProduct linkValue
              (adjacentEvenUpperLinks radius)) := by
        rw [natListProduct_append_local linkValue
          (adjacentEvenFixedLinks radius)
          (adjacentEvenUpperLinks radius)]
  unfold slabParametricKPhysicalTerm adjacentEvenLowerFactor
    adjacentEvenFixedWeight adjacentEvenUpperFactor
  rw [hlink]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hface) ?_
  let lowerLinks := slabLinkMultiplicityProductOn K
    (adjacentEvenExtent radius) physical (adjacentEvenLowerLinks radius)
  let fixedLinks := slabLinkMultiplicityProductOn K
    (adjacentEvenExtent radius) physical (adjacentEvenFixedLinks radius)
  let upperLinks := slabLinkMultiplicityProductOn K
    (adjacentEvenExtent radius) physical (adjacentEvenUpperLinks radius)
  have hlinkCast :
      Q'.ofNat (lowerLinks * (fixedLinks * upperLinks)) ≈
        Q'.ofNat lowerLinks *
          (Q'.ofNat fixedLinks * Q'.ofNat upperLinks) :=
    Q'.eqv_trans _ _ _
      (ofNat_mul_eqv_local lowerLinks (fixedLinks * upperLinks))
      (Q'.mul_eqv_congr_left _ _ _
        (ofNat_mul_eqv_local fixedLinks upperLinks))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ hlinkCast) ?_
  exact rearrange_six_local _ _ _ _ _ _

/-! ## 2. Attach the literal fixed-interface trajectory calculation -/

/-- At the anchor coupling, the fixed factor is exactly one fixed-face
coefficient product times the collapsed global endpoint-trajectory sum. -/
theorem adjacentEvenFixedWeight_anchor_eqv_coefficient_mul_collapsed
    {K radius : Nat} {physical : EdgeLabelling}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical) :
    adjacentEvenFixedWeight anchorCoupling K radius physical ≈
      adjacentEvenFixedFaceCoefficientProduct K radius physical *
        adjacentEvenCollapsedFixedLinkTrajectorySum K radius physical := by
  unfold adjacentEvenFixedWeight
    adjacentEvenFixedFaceCoefficientProduct
  apply Q'.mul_eqv_congr_left
  exact Q'.eqv_trans _ _ _
    (slabFixedLinkMultiplicityProduct_eqv_globalEndpointTrajectorySum
      hphysical)
    (adjacentEvenGlobalFixedLinkEndpointTrajectorySum_eqv_collapsed
      K radius physical)

/-- On an assembled labelling, the literal fixed-face heat-kernel coefficient
product reads only the common boundary coordinate. -/
theorem adjacentEvenFixedFaceCoefficientProduct_assemble_only_boundary
    (K radius : Nat) (left boundary right : EdgeLabelling) :
    adjacentEvenFixedFaceCoefficientProduct K radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right) =
      adjacentEvenFixedFaceCoefficientProduct K radius boundary := by
  unfold adjacentEvenFixedFaceCoefficientProduct
  rw [eliminateLinks_eq_listQProduct,
    eliminateLinks_eq_listQProduct]
  apply listQProduct_congr
  intro id hid
  rw [assembleAdjacentEvenReflectedSlabLabelling_fixed
    (mem_adjacentEvenFixedFaceIds.mp hid).1
    (mem_adjacentEvenFixedFaceIds.mp hid).2]

/-- The fixed-link trajectory contraction written on one common lower-half
endpoint coordinate on each side.  The middle transition still contains the
genuine directed interface kernel whose Gram representation is the remaining
finite positivity problem. -/
def adjacentEvenCommonLowerInterfaceSum
    (K radius : Nat) (physical reflected : EdgeLabelling) : Q' :=
  let sources := boundedLabellingsOn (linkAuxiliaryCutoff K)
    (adjacentEvenFixedLinks radius)
  let trajectories := adjacentEvenFixedIncidenceTrajectoryStates K radius
  listQSum (fun source =>
    listQSum (fun trajectory =>
      (adjacentEvenLowerAmplitudeProduct K radius physical source *
        adjacentEvenFaceTransitionProduct
          radius physical source trajectory) *
        adjacentEvenLowerAmplitudeProduct K radius reflected
          (fun link => adjacentEvenTrajectoryFinalChannel
            radius source trajectory link))
      trajectories) sources

def adjacentEvenAssembledPhysical
    (radius : Nat) (left boundary right : EdgeLabelling) : EdgeLabelling :=
  assembleAdjacentEvenReflectedSlabLabelling radius left boundary right

def adjacentEvenAssembledInterface
    (K radius : Nat) (left boundary right : EdgeLabelling) : Q' :=
  adjacentEvenFixedFaceCoefficientProduct K radius boundary *
    adjacentEvenCommonLowerInterfaceSum K radius
      (adjacentEvenAssembledPhysical radius left boundary right)
      (adjacentEvenAssembledPhysical radius right boundary left)

/-- The collapsed upper endpoint factor on an assembled physical labelling is
the same lower-amplitude map evaluated on the reflected/swapped assembly. -/
theorem adjacentEvenAssembledCollapsedSum_eqv_common_lower
    {K radius : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius))
    (hboundary : boundary ∈ boundedEdgeLabellings K
      (adjacentEvenFixedFaceIds radius))
    (hright : right ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius)) :
    adjacentEvenCollapsedFixedLinkTrajectorySum K radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right) ≈
      adjacentEvenCommonLowerInterfaceSum K radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right)
        (assembleAdjacentEvenReflectedSlabLabelling
          radius right boundary left) := by
  unfold adjacentEvenCollapsedFixedLinkTrajectorySum
    adjacentEvenCommonLowerInterfaceSum
  dsimp only
  apply listQSum_congr_on
  intro source hsource
  apply listQSum_congr_on
  intro trajectory htrajectory
  apply Q'.mul_eqv_congr_left
  exact adjacentEvenAssembledUpperAmplitude_eqv_commonLower
    hleft hboundary hright
    (fun link => adjacentEvenTrajectoryFinalChannel
      radius source trajectory link)

/-- The fixed part of an assembled physical term is the common-coordinate
interface factor. -/
theorem adjacentEvenAssembledFixedWeight_anchor_eqv_interface
    {K radius : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius))
    (hboundary : boundary ∈ boundedEdgeLabellings K
      (adjacentEvenFixedFaceIds radius))
    (hright : right ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius)) :
    adjacentEvenFixedWeight anchorCoupling K radius
        (adjacentEvenAssembledPhysical radius left boundary right) ≈
      adjacentEvenAssembledInterface K radius left boundary right := by
  let physical := adjacentEvenAssembledPhysical
    radius left boundary right
  have hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical := by
    unfold physical adjacentEvenAssembledPhysical
    exact assembleAdjacentEvenReflectedSlabLabelling_bounded
      hleft hboundary hright
  refine Q'.eqv_trans _ _ _
    (adjacentEvenFixedWeight_anchor_eqv_coefficient_mul_collapsed
      hphysical) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (adjacentEvenAssembledCollapsedSum_eqv_common_lower
        hleft hboundary hright)) ?_
  unfold adjacentEvenAssembledInterface adjacentEvenAssembledPhysical
  rw [adjacentEvenFixedFaceCoefficientProduct_assemble_only_boundary]
  exact Q'.eqv_refl _

/-- Load-bearing assembled identity for the positivity track: the entire
unnormalized adjacent-even slab summand is lower nonfixed weight, the literal
fixed-face/trajectory interface, and upper nonfixed weight.  The interface's
right endpoint is expressed in the same lower-half coordinate on the swapped
assembly. -/
theorem adjacentEvenAssembledSlabNumerator_eqv_lower_interface_upper
    {K radius : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius))
    (hboundary : boundary ∈ boundedEdgeLabellings K
      (adjacentEvenFixedFaceIds radius))
    (hright : right ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius)) :
    slabParametricKPhysicalTerm anchorCoupling K
        (adjacentEvenExtent radius)
        (adjacentEvenAssembledPhysical radius left boundary right) ≈
      adjacentEvenLowerFactor anchorCoupling K radius
          (adjacentEvenAssembledPhysical radius left boundary right) *
        (adjacentEvenAssembledInterface K radius left boundary right *
          adjacentEvenUpperFactor anchorCoupling K radius
            (adjacentEvenAssembledPhysical
              radius left boundary right)) := by
  have hfixed :=
    adjacentEvenAssembledFixedWeight_anchor_eqv_interface
      hleft hboundary hright
  refine Q'.eqv_trans _ _ _
    (slabParametricKPhysicalTerm_adjacentEven_factorization
      anchorCoupling K radius
      (adjacentEvenAssembledPhysical radius left boundary right)) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hfixed)

#print axioms slabParametricKPhysicalTerm_adjacentEven_factorization
#print axioms adjacentEvenFixedWeight_anchor_eqv_coefficient_mul_collapsed
#print axioms adjacentEvenFixedFaceCoefficientProduct_assemble_only_boundary
#print axioms adjacentEvenAssembledCollapsedSum_eqv_common_lower
#print axioms adjacentEvenAssembledFixedWeight_anchor_eqv_interface
#print axioms adjacentEvenAssembledSlabNumerator_eqv_lower_interface_upper

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAssembledSlabFactorization
