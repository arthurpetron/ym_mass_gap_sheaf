/-
# First Casimir moment on the original plaquette channels

The complete source is retained in its conditional spectator channels.
Their full first Casimir moment reduces exactly to the four physical face
links. The local cone bound therefore costs 24*C(w)^2 times the SAME
channel quadratic, independent of width, depth and late cutoff at fixed nome.
This is an uncentered moment estimate, not an interacting variance bound.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelRegularity
import YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelFirstMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (face_link_mem_base)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry (FullyActive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelRegularity
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels (plaquetteChannelSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyChannelLoss
open YMGap.Continuum.SU2QuaternionChannelAngularContraction
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairCasimir)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight terminalMessage

private theorem qsum_le (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ i, i ∈ ids → f i ≤ g i) →
    qListSum (ids.map f) ≤ qListSum (ids.map g)
  | [], _ => Q'.le_refl' _
  | i::ids, h => Q'.add_le_add (h i List.mem_cons_self)
      (qsum_le f g ids (fun j hj => h j (List.mem_cons_of_mem i hj)))

private theorem qsum_constant (a : Q') : ∀ ids : List Nat,
    qListSum (ids.map fun _ => a) ≈ Q'.ofNat ids.length * a
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv a)
  | _::ids => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (qsum_constant a ids))
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.add (.var 0) (.mul (.var 1) (.var 0)))
          (.mul (.add (.var 1) (.const 1)) (.var 0)) (by decide)
          (fun | 0 => a | _ => Q'.ofNat ids.length))
        (Q'.mul_eqv_congr_right _ _ a (Q'.eqv_symm (Q'.ofNat_add_eqv ids.length 1))))

/-- The actual carrier is nonempty whenever it contains the stated face. -/
theorem faceCarrier_positive (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) : 0 < N width := by
  have hl : (face.1, (dirsOf face.2).1) ∈ baseLinks width :=
    face_link_mem_base hf (by simp [edgesOf])
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)

/-- Four actual active face links, each with six angular planes, control the
full first moment of the SAME conditional channels. -/
theorem projectedEndpoint_plaquetteChannel_firstMoment_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointRelativeCutoff w ≤ K) (depth : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) (ha : FullyActive width face) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
      pairCasimir (N width-1)
        (plaquetteChannelSource w K width (terminalMessage w K width depth) face c)
        (plaquetteChannelSource w K width (terminalMessage w K width depth) face c)) ≤
      (24 * (endpointRelativeCap w * endpointRelativeCap w)) *
        familyChannelQuadratic (N width) w K (spectatorBlocks width face) q := by
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let passive := spectatorBlocks width face
  let active := observableBlocks width face
  let cs := productChannels (N width) w K passive
  let A := familyChannelQuadratic (N width) w K passive q
  let c := endpointRelativeCap w * endpointRelativeCap w
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  have hnd : passive.Nodup :=
    List.filter_sublist.nodup (CayleyParentInj.range_nodup (N width))
  have hreduce := pairCasimir_channel_eq_active (N width) (faceCarrier_positive width face hf)
    w K passive active (spectatorBlocks_lt width face)
    (spectator_observable_cover width face) q hq
  have hbound : qListSum (active.map fun i => channelSum cs
      (fun d => quaternionHaar (N width)
        (SU2QuaternionAngularReindex.blockAngularSquare i (channelSource passive q d)))) ≤
      qListSum (active.map fun _ => (6*c)*A) := by
    apply qsum_le
    intro i hi
    have hslot : i ∈ faceSlots width face := of_decide_eq_true (List.mem_filter.mp hi).2
    obtain ⟨l, hl, heq⟩ := List.mem_map.mp hslot
    have hlbase := face_link_mem_base hf hl
    have hnot : i ∉ passive := fun hs => spectator_not_observable width face i hs hi
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (channelSource_blockAngularSquare_eq (N width) w K passive i hnot q)) ?_
    have h := projectedEndpoint_familyChannelAngular_le hw0 hw1 K width hK depth
      l hlbase (ha l hl) passive hnd (spectatorBlocks_lt width face)
    simpa only [heq] using h
  have hcount : qListSum (active.map fun _ => (6*c)*A) ≈ (24*c)*A :=
    Q'.eqv_trans _ _ _ (qsum_constant _ active)
      (by
        rw [show active.length = 4 from observableBlocks_length width face hf]
        exact poly_identity_of_normal_eq
          (.mul (.const 4) (.mul (.mul (.const 6) (.var 0)) (.var 1)))
          (.mul (.mul (.const 24) (.var 0)) (.var 1)) (by decide)
          (fun | 0 => c | _ => A))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hreduce)
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hcount))

/-- Strict padding supplies the full activity premise from lattice geometry. -/
theorem padded_plaquetteChannel_firstMoment_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width)
    (hK : endpointRelativeCutoff w ≤ K) (depth : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
      pairCasimir (N width-1)
        (plaquetteChannelSource w K width (terminalMessage w K width depth) face c)
        (plaquetteChannelSource w K width (terminalMessage w K width depth) face c)) ≤
      (24 * (endpointRelativeCap w * endpointRelativeCap w)) *
        familyChannelQuadratic (N width) w K (spectatorBlocks width face) q :=
  projectedEndpoint_plaquetteChannel_firstMoment_le hw0 hw1 K width hK depth face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf) (plaquette_active_after_padding hwidth face hf)

#print axioms faceCarrier_positive
#print axioms projectedEndpoint_plaquetteChannel_firstMoment_le
#print axioms padded_plaquetteChannel_firstMoment_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelFirstMoment
