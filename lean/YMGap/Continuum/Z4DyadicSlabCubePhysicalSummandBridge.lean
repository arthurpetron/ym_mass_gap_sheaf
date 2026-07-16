/-
# Physical-summand audit for the six-face slab kernel

The closed cube conditional component contains every *coarse* production
link factor.  This does not yet make it the conditional law of the literal
fine spin foam: its six face packets came from four fine preimages apiece,
and the fine-link Haar factors among those preimages have not been inserted.

Two exact statements separate the issue.  For the common one-fundamental
source, the compatible cube raw term is precisely the existing coarse
six-face production activity.  But the corresponding fine source -- the
zeroth corrected-slab preimage on each cube face -- has an unpaired link, so
its actual finite-box spin-foam weight is zero while the cube raw term is
strictly positive.  Thus a physical bridge must add the fine-link recoupling
datum before normalization; no scalar renormalization can repair the missing
support projection.
-/

import YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
import YMGap.Continuum.Z4CoarseUnitCubeActivity
import YMGap.Continuum.Z4DyadicSU2ParityMinimalLiftFence
import YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection

namespace YMGap.Continuum.Z4DyadicSlabCubePhysicalSummandBridge

set_option maxRecDepth 16000
set_option maxHeartbeats 7000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicSU2ParityMinimalLiftFence
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Exact coarse summand matched by the compatible target -/

theorem stretchedPairChannelRawWeight_eqv_coarseCoefficient
    (w : Q') (packet : FaceSpinPacket) :
    packetPairChannelRawWeight w packet
        (stretchedPairChannelState packet) ≈
      coeffW w (faceSpinTotal packet) := by
  unfold packetPairChannelRawWeight stretchedPairChannelState faceSpinTotal
  change coeffW w
        (packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3) *
      (fusionInd packet.spin0 packet.spin1
          (packet.spin0 + packet.spin1) *
        (fusionInd packet.spin2 packet.spin3
            (packet.spin2 + packet.spin3) *
          fusionInd (packet.spin0 + packet.spin1)
            (packet.spin2 + packet.spin3)
            (packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3))) ≈
      coeffW w
        (packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3)
  rw [fusionInd_add_eq_one, fusionInd_add_eq_one]
  have htop :
      fusionInd (packet.spin0 + packet.spin1)
          (packet.spin2 + packet.spin3)
          (packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3) = 1 := by
    rw [show packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3 =
      (packet.spin0 + packet.spin1) +
        (packet.spin2 + packet.spin3) by omega]
    exact fusionInd_add_eq_one _ _
  rw [htop]
  exact Q'.mul_one_eqv _

theorem oneFundamentalCubeFaceRawProduct_eqv_pow_six (w : Q') :
    cubeFaceRawProduct w 1 oneFundamentalCubeCompatibleSource
        (compatibleCubeTarget oneFundamentalCubeCompatibleSource) ≈
      (coeffW w 1) ^ 6 := by
  unfold cubeFaceRawProduct
  change
    packetPairChannelRawWeight w oneFaceFundamentalPacket ((1, 0), 1) *
      (packetPairChannelRawWeight w oneFaceFundamentalPacket ((1, 0), 1) *
        (packetPairChannelRawWeight w oneFaceFundamentalPacket ((1, 0), 1) *
          (packetPairChannelRawWeight w oneFaceFundamentalPacket ((1, 0), 1) *
            (packetPairChannelRawWeight w oneFaceFundamentalPacket ((1, 0), 1) *
              (packetPairChannelRawWeight w oneFaceFundamentalPacket
                ((1, 0), 1) * 1))))) ≈
      (coeffW w 1) ^ 6
  rw [Q'.pow_succ, Q'.pow_succ, Q'.pow_succ,
    Q'.pow_succ, Q'.pow_succ, Q'.pow_succ, Q'.pow_zero]
  exact qmul_congr
    (stretchedPairChannelRawWeight_eqv_coarseCoefficient
      w oneFaceFundamentalPacket)
    (qmul_congr
      (stretchedPairChannelRawWeight_eqv_coarseCoefficient
        w oneFaceFundamentalPacket)
      (qmul_congr
        (stretchedPairChannelRawWeight_eqv_coarseCoefficient
          w oneFaceFundamentalPacket)
        (qmul_congr
          (stretchedPairChannelRawWeight_eqv_coarseCoefficient
            w oneFaceFundamentalPacket)
          (qmul_congr
            (stretchedPairChannelRawWeight_eqv_coarseCoefficient
              w oneFaceFundamentalPacket)
            (qmul_congr
              (stretchedPairChannelRawWeight_eqv_coarseCoefficient
                w oneFaceFundamentalPacket)
              (Q'.eqv_refl 1))))))

theorem oneFundamentalCubeRawWeight_eqv_pow_six (w : Q') :
    cubeCoupledRawWeight w 1 oneFundamentalCubeCompatibleSource
        (compatibleCubeTarget oneFundamentalCubeCompatibleSource) ≈
      (coeffW w 1) ^ 6 := by
  unfold cubeCoupledRawWeight
  exact Q'.eqv_trans _ ((coeffW w 1) ^ 6 * 1) _
    (qmul_congr
      (oneFundamentalCubeFaceRawProduct_eqv_pow_six w)
      (compatibleCubeProductionLinkProduct_eqv_one
        oneFundamentalCubeCompatibleSource))
    (Q'.mul_one_eqv _)

/-- The positive cube term is an exact coarse production summand: the
pre-existing canonical activity is definitionally the localized spin-foam
weight of the six-face component label. -/
theorem oneFundamentalCubeRawWeight_eqv_coarseProductionSummand
    (w : Q') :
    cubeCoupledRawWeight w 1 oneFundamentalCubeCompatibleSource
        (compatibleCubeTarget oneFundamentalCubeCompatibleSource) ≈
      parametricLocalizedSpinFoamWeight w 2
        (componentLabel coarseUnitCubeSupportIds) := by
  change cubeCoupledRawWeight w 1 oneFundamentalCubeCompatibleSource
        (compatibleCubeTarget oneFundamentalCubeCompatibleSource) ≈
      canonicalSurfaceActivity w 2 coarseUnitCubeSupportIds
  exact Q'.eqv_trans _ ((coeffW w 1) ^ 6) _
    (oneFundamentalCubeRawWeight_eqv_pow_six w)
    (Q'.eqv_symm (coarseUnitCube_canonicalSurfaceActivity_eqv w))

/-! ## 2. A non-vacuous closed fine support fibre

The packet slots matter.  Choosing slot one on each lower face and slot zero
on each upper face gives the six faces of the fine unit cube based at
`(1,1,1,0)`.  This is a genuine positive fine spin foam and its weight is
exactly the present cube raw term.  Thus the packet calculus does contain
physical sources, but physicality is a global restriction on the six slot
choices, not a property of each face packet separately.
-/

def shiftedOneFaceFundamentalPacket : FaceSpinPacket :=
  ⟨0, 1, 0, 0⟩

theorem shiftedOneFaceFundamentalPacket_mem :
    shiftedOneFaceFundamentalPacket ∈ faceSpinPacketStateSpace 1 := by
  apply (mem_faceSpinPacketStateSpace_iff 1 _).mpr
  change (0 : Nat) ≤ 1 ∧ 1 ≤ 1 ∧ 0 ≤ 1 ∧ 0 ≤ 1
  exact ⟨Nat.zero_le 1, Nat.le_refl 1,
    Nat.zero_le 1, Nat.zero_le 1⟩

def shiftedOneFaceFundamentalBoundedPacket :
    BoundedFaceSpinPacket 1 :=
  ⟨shiftedOneFaceFundamentalPacket,
    shiftedOneFaceFundamentalPacket_mem⟩

/-- The slot pattern cut out by the closed fine cube in the nondegenerate
six-face fibre. -/
def oddFineCubeCompatibleSource : CubeStretchedCompatibleSource 1 where
  packet
    | .bottomXY => shiftedOneFaceFundamentalBoundedPacket
    | .topXY => oneFaceFundamentalBoundedPacket
    | .frontXZ => shiftedOneFaceFundamentalBoundedPacket
    | .backXZ => oneFaceFundamentalBoundedPacket
    | .leftYZ => shiftedOneFaceFundamentalBoundedPacket
    | .rightYZ => oneFaceFundamentalBoundedPacket
  commonTotal := 1
  total_eq := by intro face; cases face <;> rfl

/-- Boolean carrier of the already-audited odd fine unit cube, written by
structural recursion so no ambient classical decidability instance enters
the critical path. -/
def oddFineCubeGeometricFaceB : Z4Plaq → Bool
  | ((1, 1, 1, 0), .p01) => true
  | ((1, 1, 1, 0), .p02) => true
  | ((1, 1, 1, 0), .p12) => true
  | ((1, 1, 2, 0), .p01) => true
  | ((1, 2, 1, 0), .p02) => true
  | ((2, 1, 1, 0), .p12) => true
  | _ => false

def oddFineCubeGeometricSpin (plaquette : Z4Plaq) : Nat :=
  match oddFineCubeGeometricFaceB plaquette with
  | true => 1
  | false => 0

theorem oddFineCubeGeometricSpin_bounded (plaquette : Z4Plaq) :
    oddFineCubeGeometricSpin plaquette ≤ 1 := by
  unfold oddFineCubeGeometricSpin
  cases hface : oddFineCubeGeometricFaceB plaquette <;>
    simp

/-- All six packets of the source are literally induced by one common fine
spin field.  This is the support-fibre datum absent from the raw kernel's
source type. -/
theorem oddFineCube_packet_is_geometric (face : CubeFaceIndex) :
    dyadicFaceSpinPacket oddFineCubeGeometricSpin (cubeFace face) =
      (oddFineCubeCompatibleSource.packet face).val := by
  cases face <;>
    rfl

theorem oddFineCubeFaceRawProduct_eqv_pow_six (w : Q') :
    cubeFaceRawProduct w 1 oddFineCubeCompatibleSource
        (compatibleCubeTarget oddFineCubeCompatibleSource) ≈
      (coeffW w 1) ^ 6 := by
  unfold cubeFaceRawProduct
  change
    packetPairChannelRawWeight w shiftedOneFaceFundamentalPacket
        ((1, 0), 1) *
      (packetPairChannelRawWeight w oneFaceFundamentalPacket ((1, 0), 1) *
        (packetPairChannelRawWeight w shiftedOneFaceFundamentalPacket
            ((1, 0), 1) *
          (packetPairChannelRawWeight w oneFaceFundamentalPacket
              ((1, 0), 1) *
            (packetPairChannelRawWeight w shiftedOneFaceFundamentalPacket
                ((1, 0), 1) *
              (packetPairChannelRawWeight w oneFaceFundamentalPacket
                ((1, 0), 1) * 1))))) ≈
      (coeffW w 1) ^ 6
  rw [Q'.pow_succ, Q'.pow_succ, Q'.pow_succ,
    Q'.pow_succ, Q'.pow_succ, Q'.pow_succ, Q'.pow_zero]
  exact qmul_congr
    (stretchedPairChannelRawWeight_eqv_coarseCoefficient
      w shiftedOneFaceFundamentalPacket)
    (qmul_congr
      (stretchedPairChannelRawWeight_eqv_coarseCoefficient
        w oneFaceFundamentalPacket)
      (qmul_congr
        (stretchedPairChannelRawWeight_eqv_coarseCoefficient
          w shiftedOneFaceFundamentalPacket)
        (qmul_congr
          (stretchedPairChannelRawWeight_eqv_coarseCoefficient
            w oneFaceFundamentalPacket)
          (qmul_congr
            (stretchedPairChannelRawWeight_eqv_coarseCoefficient
              w shiftedOneFaceFundamentalPacket)
            (qmul_congr
              (stretchedPairChannelRawWeight_eqv_coarseCoefficient
                w oneFaceFundamentalPacket)
              (Q'.eqv_refl 1))))))

theorem oddFineCubeRawWeight_eqv_pow_six (w : Q') :
    cubeCoupledRawWeight w 1 oddFineCubeCompatibleSource
        (compatibleCubeTarget oddFineCubeCompatibleSource) ≈
      (coeffW w 1) ^ 6 := by
  unfold cubeCoupledRawWeight
  exact Q'.eqv_trans _ ((coeffW w 1) ^ 6 * 1) _
    (qmul_congr
      (oddFineCubeFaceRawProduct_eqv_pow_six w)
      (compatibleCubeProductionLinkProduct_eqv_one
        oddFineCubeCompatibleSource))
    (Q'.mul_one_eqv _)

/-- Strongest exact physical identification presently available: on the
explicit closed fine support fibre, the six-face raw term is the actual
production spin-foam summand, with no extra scalar normalization. -/
theorem oddFineCubeRawWeight_eqv_fineProductionSummand (w : Q') :
    cubeCoupledRawWeight w 1 oddFineCubeCompatibleSource
        (compatibleCubeTarget oddFineCubeCompatibleSource) ≈
      parametricLocalizedSpinFoamWeight w 4
        (componentLabel oddFineUnitCubeSupportIds) := by
  change cubeCoupledRawWeight w 1 oddFineCubeCompatibleSource
        (compatibleCubeTarget oddFineCubeCompatibleSource) ≈
      canonicalSurfaceActivity w 4 oddFineUnitCubeSupportIds
  exact Q'.eqv_trans _ ((coeffW w 1) ^ 6) _
    (oddFineCubeRawWeight_eqv_pow_six w)
    (Q'.eqv_symm (oddFineUnitCube_canonicalSurfaceActivity_eqv w))

theorem oddFineCubeFineProductionSummand_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < parametricLocalizedSpinFoamWeight w 4
      (componentLabel oddFineUnitCubeSupportIds) := by
  change (0 : Q') < canonicalSurfaceActivity w 4
    oddFineUnitCubeSupportIds
  exact Q'.pos_of_lt_of_le
    (compatibleCubeRawWeight_pos hw 1 oddFineCubeCompatibleSource)
    (Q'.le_of_eqv
      (oddFineCubeRawWeight_eqv_fineProductionSummand w))

theorem oddFineCubeFineSupport_closed :
    ∀ link, link ∈ geometricTouchedLinks oddFineUnitCubeSurface →
      (geometricIncidentPlaquettes oddFineUnitCubeSurface link).length = 2 := by
  intro link hlink
  exact oddFineUnitCube_geometricIncidentPlaquettes_length_eq_two hlink

/-- The physical and nonphysical packet sources are distinct even though
their stretched channels coincide. -/
theorem oddFineCubeSource_ne_zeroSlotSource :
    (oddFineCubeCompatibleSource.packet .bottomXY).val ≠
      (oneFundamentalCubeCompatibleSource.packet .bottomXY).val := by
  intro heq
  have hspin := congrArg FaceSpinPacket.spin0 heq
  change (0 : Nat) = 1 at hspin
  omega

theorem oddFineCubeTarget_eq_zeroSlotTarget :
    compatibleCubeTarget oddFineCubeCompatibleSource =
      compatibleCubeTarget oneFundamentalCubeCompatibleSource := by
  rfl

/-- The current coarse raw statistic cannot detect fine closure: a closed
fine cube source and the incidence-one source receive exactly the same raw
mass and the same target.  A repaired law therefore needs a genuine global
fine-support projector (or equivalent recoupling coordinate). -/
theorem cubeRawWeight_physical_nonphysical_sources_eqv (w : Q') :
    cubeCoupledRawWeight w 1 oddFineCubeCompatibleSource
        (compatibleCubeTarget oddFineCubeCompatibleSource) ≈
      cubeCoupledRawWeight w 1 oneFundamentalCubeCompatibleSource
        (compatibleCubeTarget oneFundamentalCubeCompatibleSource) :=
  Q'.eqv_trans _ ((coeffW w 1) ^ 6) _
    (oddFineCubeRawWeight_eqv_pow_six w)
    (Q'.eqv_symm (oneFundamentalCubeRawWeight_eqv_pow_six w))

/-! ## 3. A packet source with no physical fine support fibre -/

/-- Zeroth corrected-slab preimage of each of the six cube faces, in cube
face order. -/
def zeroPreimageCubeFineSupport : List Z4Plaq :=
  [((1, 1, 0, 0), .p01), ((1, 1, 2, 0), .p01),
   ((1, 0, 1, 0), .p02), ((1, 2, 1, 0), .p02),
   ((0, 1, 1, 0), .p12), ((2, 1, 1, 0), .p12)]

theorem cubeFace_zeroPreimages_eq_fineSupport :
    cubeFaceIndices.map (fun face =>
      (dyadicFacePreimages (cubeFace face)).getD 0 fallbackPlaquette) =
        zeroPreimageCubeFineSupport := by
  rfl

theorem zeroPreimageCubeFineSupport_nodup :
    zeroPreimageCubeFineSupport.Nodup := by
  simp [zeroPreimageCubeFineSupport]

theorem zeroPreimageCubeFineSupport_subset_box_four :
    ∀ plaquette, plaquette ∈ zeroPreimageCubeFineSupport →
      plaquette ∈ boxPlaquettes 4 := by
  intro plaquette hplaquette
  apply (mem_boxPlaquettes plaquette 4).2
  simp only [zeroPreimageCubeFineSupport, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp
  all_goals exact ⟨by omega, by omega, by omega, by omega⟩

def zeroPreimageCubeFineSupportIds : List Nat :=
  geometricSupportIds 4 zeroPreimageCubeFineSupport

theorem zeroPreimageCubeFineSupportIds_mem_cutoffOneFaceSupports :
    zeroPreimageCubeFineSupportIds ∈ cutoffOneFaceSupports 4 := by
  unfold zeroPreimageCubeFineSupportIds
  exact geometricSupportIds_mem_cutoffOneFaceSupports 4
    zeroPreimageCubeFineSupport

theorem zeroPreimageCubeFineSupportIds_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 4 zeroPreimageCubeFineSupportIds)
      zeroPreimageCubeFineSupport := by
  unfold zeroPreimageCubeFineSupportIds
  exact geometricSupportIds_sameSupport
    zeroPreimageCubeFineSupport_subset_box_four

def zeroPreimageCubeFenceLink : Z4Link :=
  ((1, 1, 0, 0), .x0)

theorem zeroPreimageCubeFineSupport_fence_incidence_one :
    (geometricIncidentPlaquettes zeroPreimageCubeFineSupport
      zeroPreimageCubeFenceLink).length = 1 := by
  rfl

theorem zeroPreimageCubeFineSupportIds_fence_incidence_one :
    (geometricIncidentPlaquettes
      (geometricPolymer 4 zeroPreimageCubeFineSupportIds)
      zeroPreimageCubeFenceLink).length = 1 := by
  have hsame := geometricIncidentPlaquettes_sameSupport
    zeroPreimageCubeFineSupportIds_sameSupport
    zeroPreimageCubeFenceLink
  have hleft := geometricIncidentPlaquettes_nodup
    zeroPreimageCubeFineSupportIds_mem_cutoffOneFaceSupports
    zeroPreimageCubeFenceLink
  have hright :
      (geometricIncidentPlaquettes zeroPreimageCubeFineSupport
        zeroPreimageCubeFenceLink).Nodup := by
    unfold geometricIncidentPlaquettes
    exact List.filter_sublist.nodup zeroPreimageCubeFineSupport_nodup
  exact (sameSupport_length_eq_of_nodup hsame hleft hright).trans
    zeroPreimageCubeFineSupport_fence_incidence_one

def zeroPreimageCubeFinePhysical :
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  componentLabel zeroPreimageCubeFineSupportIds

theorem zeroPreimageCubeFinePhysical_mem :
    zeroPreimageCubeFinePhysical ∈ explicitPhysicalLabellings 1 4 := by
  unfold zeroPreimageCubeFinePhysical
  apply componentLabel_mem_physical_of_subset
  intro edge hedge
  exact mem_of_mem_sublists (physicalFaceEdges 4)
    zeroPreimageCubeFineSupportIds
    zeroPreimageCubeFineSupportIds_mem_cutoffOneFaceSupports edge hedge

theorem zeroPreimageCubeFenceLink_mem_distinctBoxLinks :
    zeroPreimageCubeFenceLink ∈ distinctBoxLinks 4 := by
  unfold distinctBoxLinks
  apply List.mem_eraseDups.mpr
  apply boundary_mem_boxLinks
    (zeroPreimageCubeFineSupport_subset_box_four
      ((1, 1, 0, 0), .p01) (by
        simp [zeroPreimageCubeFineSupport]))
  simp [zeroPreimageCubeFenceLink, edgesOf, dirsOf, addE]

/-- The actual finite-box weight of the six represented fine plaquettes is
annihilated by the displayed odd-incidence link. -/
theorem zeroPreimageCubeFinePhysical_weight_eqv_zero :
    explicitSpinFoamWeight 1 4 zeroPreimageCubeFinePhysical ≈ 0 := by
  obtain ⟨index, hindexed⟩ :=
    exists_mem_enumerate zeroPreimageCubeFenceLink_mem_distinctBoxLinks
  apply explicitSpinFoamWeight_eqv_zero_of_odd_incidence
    zeroPreimageCubeFinePhysical_mem hindexed
  unfold zeroPreimageCubeFinePhysical
  rw [excitedIncidentPlaqIds_length_eq_geometric
    zeroPreimageCubeFineSupportIds_mem_cutoffOneFaceSupports]
  rw [zeroPreimageCubeFineSupportIds_fence_incidence_one]

/-! ## 3. Checked physicality obstruction -/

theorem oneFundamentalCubeRawWeight_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') <
      cubeCoupledRawWeight w 1 oneFundamentalCubeCompatibleSource
        (compatibleCubeTarget oneFundamentalCubeCompatibleSource) :=
  compatibleCubeRawWeight_pos hw 1 oneFundamentalCubeCompatibleSource

/-- No scalar normalization identity can identify the present cube term with
the literal fine source weight: the former is positive and the latter is
kernel-equal to zero. -/
theorem cubeRawWeight_ne_correspondingFineProductionWeight
    {w : Q'} (hw : (0 : Q') < w) :
    ¬ cubeCoupledRawWeight w 1 oneFundamentalCubeCompatibleSource
          (compatibleCubeTarget oneFundamentalCubeCompatibleSource) ≈
        explicitSpinFoamWeight 1 4 zeroPreimageCubeFinePhysical := by
  intro hequal
  have hzero :
      cubeCoupledRawWeight w 1 oneFundamentalCubeCompatibleSource
          (compatibleCubeTarget oneFundamentalCubeCompatibleSource) ≈ 0 :=
    Q'.eqv_trans _ _ _ hequal
      zeroPreimageCubeFinePhysical_weight_eqv_zero
  have hle :
      cubeCoupledRawWeight w 1 oneFundamentalCubeCompatibleSource
          (compatibleCubeTarget oneFundamentalCubeCompatibleSource) ≤ 0 :=
    Q'.le_of_eqv hzero
  have hbad : (0 : Q') < 0 :=
    YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
      (oneFundamentalCubeRawWeight_pos hw) hle
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' 0 hbad

/-! ## Dependency gates -/

#print axioms stretchedPairChannelRawWeight_eqv_coarseCoefficient
#print axioms oneFundamentalCubeRawWeight_eqv_coarseProductionSummand
#print axioms shiftedOneFaceFundamentalPacket_mem
#print axioms shiftedOneFaceFundamentalBoundedPacket
#print axioms oddFineCubeCompatibleSource
#print axioms oddFineCubeFaceRawProduct_eqv_pow_six
#print axioms oddFineCubeRawWeight_eqv_pow_six
#print axioms oddFineCube_packet_is_geometric
#print axioms oddFineCubeRawWeight_eqv_fineProductionSummand
#print axioms oddFineCubeFineProductionSummand_pos
#print axioms oddFineCubeFineSupport_closed
#print axioms oddFineCubeSource_ne_zeroSlotSource
#print axioms oddFineCubeTarget_eq_zeroSlotTarget
#print axioms cubeRawWeight_physical_nonphysical_sources_eqv
#print axioms cubeFace_zeroPreimages_eq_fineSupport
#print axioms zeroPreimageCubeFineSupportIds_fence_incidence_one
#print axioms zeroPreimageCubeFinePhysical_weight_eqv_zero
#print axioms oneFundamentalCubeRawWeight_pos
#print axioms cubeRawWeight_ne_correspondingFineProductionWeight

end YMGap.Continuum.Z4DyadicSlabCubePhysicalSummandBridge
