/-
# Constructive connected roots for the seven-cube outward cycle

Each literal boundary is reordered into a finite spanning order.  The generic
tail-bridge checker turns the closed Boolean certificate into witness-bearing
geometric connectivity, after which the four supports are encoded as genuine
canonical surface-polymer roots in volume six.
-/

import YMGap.Continuum.Z4FiniteGeometricConnectivityCertificate
import YMGap.Continuum.Z4OutwardSevenCubeCycleGeometry

namespace YMGap.Continuum.Z4OutwardSevenCubeCycleConnectedRoots

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4FiniteGeometricConnectivityCertificate
open YMGap.Continuum.Z4OutwardSevenCubeCycleGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion

/-! ## 1. Literal spanning orders -/

def sevenCube011To100ConnectivityOrder : List Z4Plaq :=
  [((2, 1, 1, 0), .p12), ((0, 3, 1, 0), .p02),
   ((1, 2, 1, 0), .p12), ((1, 1, 2, 0), .p01),
   ((0, 2, 2, 0), .p01), ((0, 2, 1, 0), .p12),
   ((1, 2, 1, 0), .p02), ((2, 1, 0, 0), .p12),
   ((2, 0, 1, 0), .p12), ((1, 0, 2, 0), .p01),
   ((0, 2, 1, 0), .p01), ((0, 1, 2, 0), .p01),
   ((0, 1, 1, 0), .p12), ((1, 1, 0, 0), .p01),
   ((1, 2, 0, 0), .p02), ((1, 0, 1, 0), .p02),
   ((2, 0, 0, 0), .p12), ((1, 0, 1, 0), .p12),
   ((1, 0, 0, 0), .p01), ((0, 1, 1, 0), .p01),
   ((0, 1, 1, 0), .p02), ((1, 1, 0, 0), .p12),
   ((1, 0, 0, 0), .p02), ((0, 0, 1, 0), .p01),
   ((0, 0, 0, 0), .p01), ((0, 1, 0, 0), .p02),
   ((0, 0, 0, 0), .p02), ((0, 0, 0, 0), .p12)]

def sevenCube100To000ConnectivityOrder : List Z4Plaq :=
  [((3, 1, 2, 0), .p12), ((2, 1, 3, 0), .p01),
   ((2, 2, 2, 0), .p02), ((3, 1, 1, 0), .p12),
   ((2, 1, 2, 0), .p02), ((2, 2, 1, 0), .p02),
   ((2, 1, 2, 0), .p12), ((3, 0, 1, 0), .p12),
   ((2, 1, 0, 0), .p02), ((3, 0, 0, 0), .p12),
   ((2, 1, 1, 0), .p01), ((2, 1, 0, 0), .p12),
   ((2, 0, 2, 0), .p01), ((2, 1, 1, 0), .p12),
   ((2, 0, 1, 0), .p02), ((2, 0, 0, 0), .p01),
   ((2, 0, 0, 0), .p02), ((1, 1, 1, 0), .p01),
   ((1, 1, 0, 0), .p01), ((1, 2, 0, 0), .p02),
   ((1, 0, 2, 0), .p01), ((1, 1, 1, 0), .p02),
   ((1, 0, 1, 0), .p02), ((1, 0, 0, 0), .p01),
   ((1, 0, 0, 0), .p02), ((1, 1, 0, 0), .p12),
   ((1, 0, 1, 0), .p12), ((1, 0, 0, 0), .p12)]

def sevenCube000To111ConnectivityOrder : List Z4Plaq :=
  [((2, 1, 2, 0), .p12), ((1, 1, 3, 0), .p01),
   ((1, 2, 2, 0), .p02), ((2, 1, 1, 0), .p12),
   ((1, 1, 2, 0), .p02), ((1, 2, 1, 0), .p02),
   ((1, 1, 2, 0), .p12), ((2, 0, 1, 0), .p12),
   ((1, 1, 0, 0), .p02), ((2, 0, 0, 0), .p12),
   ((1, 1, 1, 0), .p01), ((1, 1, 0, 0), .p12),
   ((1, 0, 2, 0), .p01), ((1, 1, 1, 0), .p12),
   ((1, 0, 1, 0), .p02), ((1, 0, 0, 0), .p01),
   ((1, 0, 0, 0), .p02), ((0, 1, 1, 0), .p01),
   ((0, 1, 0, 0), .p01), ((0, 2, 0, 0), .p02),
   ((0, 0, 2, 0), .p01), ((0, 1, 1, 0), .p02),
   ((0, 0, 1, 0), .p02), ((0, 0, 0, 0), .p01),
   ((0, 0, 0, 0), .p02), ((0, 1, 0, 0), .p12),
   ((0, 0, 1, 0), .p12), ((0, 0, 0, 0), .p12)]

def sevenCube111To011ConnectivityOrder : List Z4Plaq :=
  [((2, 1, 0, 0), .p12), ((2, 1, 0, 0), .p02),
   ((3, 0, 0, 0), .p12), ((2, 0, 0, 0), .p01),
   ((2, 0, 0, 0), .p02), ((2, 1, 1, 0), .p12),
   ((1, 1, 0, 0), .p01), ((1, 2, 0, 0), .p02),
   ((2, 0, 1, 0), .p01), ((1, 0, 0, 0), .p01),
   ((1, 0, 0, 0), .p02), ((1, 1, 1, 0), .p02),
   ((1, 1, 2, 0), .p01), ((1, 2, 1, 0), .p02),
   ((0, 1, 0, 0), .p01), ((0, 2, 0, 0), .p02),
   ((1, 0, 1, 0), .p01), ((0, 1, 0, 0), .p02),
   ((1, 0, 0, 0), .p12), ((1, 0, 1, 0), .p12),
   ((0, 1, 2, 0), .p01), ((0, 2, 1, 0), .p02),
   ((0, 1, 0, 0), .p12), ((0, 0, 2, 0), .p01),
   ((0, 0, 1, 0), .p01), ((0, 0, 1, 0), .p02),
   ((0, 1, 1, 0), .p12), ((0, 0, 1, 0), .p12)]

theorem sevenCubeCycle_connectivity_certificates :
    tailBridgeConnectedB sevenCube011To100ConnectivityOrder = true ∧
    tailBridgeConnectedB sevenCube100To000ConnectivityOrder = true ∧
    tailBridgeConnectedB sevenCube000To111ConnectivityOrder = true ∧
    tailBridgeConnectedB sevenCube111To011ConnectivityOrder = true := by
  decide

private theorem order_nodup_011To100 :
    sevenCube011To100ConnectivityOrder.Nodup := by
  unfold sevenCube011To100ConnectivityOrder
  simp

private theorem order_nodup_100To000 :
    sevenCube100To000ConnectivityOrder.Nodup := by
  unfold sevenCube100To000ConnectivityOrder
  simp

private theorem order_nodup_000To111 :
    sevenCube000To111ConnectivityOrder.Nodup := by
  unfold sevenCube000To111ConnectivityOrder
  simp

private theorem order_nodup_111To011 :
    sevenCube111To011ConnectivityOrder.Nodup := by
  unfold sevenCube111To011ConnectivityOrder
  simp

private theorem surface_perm_order_011To100 :
    sevenCube011To100Surface.Perm sevenCube011To100ConnectivityOrder := by
  apply perm_of_nodup_mem_iff
    sevenCube011To100Surface sevenCube011To100ConnectivityOrder
    sevenCubeCycleSurface_nodups.1 order_nodup_011To100
  intro plaquette
  constructor
  · intro hplaquette
    simp only [sevenCube011To100Surface, List.mem_cons,
      List.not_mem_nil, or_false] at hplaquette
    rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sevenCube011To100ConnectivityOrder]
  · intro hplaquette
    simp only [sevenCube011To100ConnectivityOrder, List.mem_cons,
      List.not_mem_nil, or_false] at hplaquette
    rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sevenCube011To100Surface]

private theorem surface_perm_order_100To000 :
    sevenCube100To000Surface.Perm sevenCube100To000ConnectivityOrder := by
  apply perm_of_nodup_mem_iff
    sevenCube100To000Surface sevenCube100To000ConnectivityOrder
    sevenCubeCycleSurface_nodups.2.1 order_nodup_100To000
  intro plaquette
  constructor
  · intro hplaquette
    simp only [sevenCube100To000Surface, List.mem_cons,
      List.not_mem_nil, or_false] at hplaquette
    rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sevenCube100To000ConnectivityOrder]
  · intro hplaquette
    simp only [sevenCube100To000ConnectivityOrder, List.mem_cons,
      List.not_mem_nil, or_false] at hplaquette
    rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sevenCube100To000Surface]

private theorem surface_perm_order_000To111 :
    sevenCube000To111Surface.Perm sevenCube000To111ConnectivityOrder := by
  apply perm_of_nodup_mem_iff
    sevenCube000To111Surface sevenCube000To111ConnectivityOrder
    sevenCubeCycleSurface_nodups.2.2.1 order_nodup_000To111
  intro plaquette
  constructor
  · intro hplaquette
    simp only [sevenCube000To111Surface, List.mem_cons,
      List.not_mem_nil, or_false] at hplaquette
    rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sevenCube000To111ConnectivityOrder]
  · intro hplaquette
    simp only [sevenCube000To111ConnectivityOrder, List.mem_cons,
      List.not_mem_nil, or_false] at hplaquette
    rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sevenCube000To111Surface]

private theorem surface_perm_order_111To011 :
    sevenCube111To011Surface.Perm sevenCube111To011ConnectivityOrder := by
  apply perm_of_nodup_mem_iff
    sevenCube111To011Surface sevenCube111To011ConnectivityOrder
    sevenCubeCycleSurface_nodups.2.2.2 order_nodup_111To011
  intro plaquette
  constructor
  · intro hplaquette
    simp only [sevenCube111To011Surface, List.mem_cons,
      List.not_mem_nil, or_false] at hplaquette
    rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sevenCube111To011ConnectivityOrder]
  · intro hplaquette
    simp only [sevenCube111To011ConnectivityOrder, List.mem_cons,
      List.not_mem_nil, or_false] at hplaquette
    rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sevenCube111To011Surface]

private def chainInMono_local {small large : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ small → plaquette ∈ large) :
    {first last : Z4Plaq} →
      ChainIn z4Chain.toLattice small first last →
      ChainIn z4Chain.toLattice large first last
  | _, _, .refl plaquette => .refl plaquette
  | _, _, .step adjacent hnext rest =>
      .step adjacent (hsubset _ hnext) (chainInMono_local hsubset rest)

private def connectedIn_of_perm_local {left right : List Z4Plaq}
    (hperm : left.Perm right)
    (hright : connectedIn (L := z4Chain.toLattice) right) :
    connectedIn (L := z4Chain.toLattice) left := by
  intro first last hfirst hlast
  exact chainInMono_local
    (fun plaquette hplaquette => (hperm.mem_iff).mpr hplaquette)
    (hright first last (hperm.mem_iff.mp hfirst)
      (hperm.mem_iff.mp hlast))

def sevenCube011To100Surface_connected :
    connectedIn (L := z4Chain.toLattice) sevenCube011To100Surface :=
  connectedIn_of_perm_local surface_perm_order_011To100
    (connectedIn_of_tailBridgeConnectedB _
      sevenCubeCycle_connectivity_certificates.1)

def sevenCube100To000Surface_connected :
    connectedIn (L := z4Chain.toLattice) sevenCube100To000Surface :=
  connectedIn_of_perm_local surface_perm_order_100To000
    (connectedIn_of_tailBridgeConnectedB _
      sevenCubeCycle_connectivity_certificates.2.1)

def sevenCube000To111Surface_connected :
    connectedIn (L := z4Chain.toLattice) sevenCube000To111Surface :=
  connectedIn_of_perm_local surface_perm_order_000To111
    (connectedIn_of_tailBridgeConnectedB _
      sevenCubeCycle_connectivity_certificates.2.2.1)

def sevenCube111To011Surface_connected :
    connectedIn (L := z4Chain.toLattice) sevenCube111To011Surface :=
  connectedIn_of_perm_local surface_perm_order_111To011
    (connectedIn_of_tailBridgeConnectedB _
      sevenCubeCycle_connectivity_certificates.2.2.2)

/-! ## 2. Canonical numerical roots -/

def sevenCube011To100Root : List Nat :=
  geometricSupportIds 6 sevenCube011To100Surface

def sevenCube100To000Root : List Nat :=
  geometricSupportIds 6 sevenCube100To000Surface

def sevenCube000To111Root : List Nat :=
  geometricSupportIds 6 sevenCube000To111Surface

def sevenCube111To011Root : List Nat :=
  geometricSupportIds 6 sevenCube111To011Surface

private theorem geometricRoot_mem_canonical_local
    {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hnonempty : Σ' plaquette : Z4Plaq, plaquette ∈ support)
    (hconnected : connectedIn (L := z4Chain.toLattice) support) :
    geometricSupportIds 6 support ∈ canonicalSurfacePolymers 6 := by
  apply connectedFaceSupport_mem_canonicalSurfacePolymers
  · exact geometricSupportIds_mem_cutoffOneFaceSupports 6 support
  · obtain ⟨plaquette, hplaquette⟩ := hnonempty
    have hdecoded : plaquette ∈
        geometricPolymer 6 (geometricSupportIds 6 support) :=
      (geometricSupportIds_sameSupport hbox).2 plaquette hplaquette
    obtain ⟨identifier, hidentifier, _⟩ :=
      decodeMapMember (boxPlaquetteAt 6)
        (geometricSupportIds 6 support) plaquette hdecoded
    exact ⟨identifier, hidentifier⟩
  · exact geometricSupportIds_connected hbox hconnected

theorem sevenCube011To100Root_mem_canonical :
    sevenCube011To100Root ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical_local
    sevenCube011To100Surface_subset_box_six
    ⟨((0, 0, 0, 0), .p12), by
      simp [sevenCube011To100Surface]⟩
    sevenCube011To100Surface_connected

theorem sevenCube100To000Root_mem_canonical :
    sevenCube100To000Root ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical_local
    sevenCube100To000Surface_subset_box_six
    ⟨((1, 0, 0, 0), .p12), by
      simp [sevenCube100To000Surface]⟩
    sevenCube100To000Surface_connected

theorem sevenCube000To111Root_mem_canonical :
    sevenCube000To111Root ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical_local
    sevenCube000To111Surface_subset_box_six
    ⟨((0, 0, 0, 0), .p12), by
      simp [sevenCube000To111Surface]⟩
    sevenCube000To111Surface_connected

theorem sevenCube111To011Root_mem_canonical :
    sevenCube111To011Root ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical_local
    sevenCube111To011Surface_subset_box_six
    ⟨((0, 0, 1, 0), .p12), by
      simp [sevenCube111To011Surface]⟩
    sevenCube111To011Surface_connected

theorem sevenCube011To100Root_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 sevenCube011To100Root)
      sevenCube011To100Surface :=
  geometricSupportIds_sameSupport
    sevenCube011To100Surface_subset_box_six

theorem sevenCube100To000Root_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 sevenCube100To000Root)
      sevenCube100To000Surface :=
  geometricSupportIds_sameSupport
    sevenCube100To000Surface_subset_box_six

theorem sevenCube000To111Root_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 sevenCube000To111Root)
      sevenCube000To111Surface :=
  geometricSupportIds_sameSupport
    sevenCube000To111Surface_subset_box_six

theorem sevenCube111To011Root_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 sevenCube111To011Root)
      sevenCube111To011Surface :=
  geometricSupportIds_sameSupport
    sevenCube111To011Surface_subset_box_six

private theorem encodedRoot_length_eq_surface_length
    {root : List Nat} {surface : List Z4Plaq}
    (hroot : root ∈ canonicalSurfacePolymers 6)
    (hsame : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 root) surface)
    (hsurfaceNodup : surface.Nodup) :
    root.length = surface.length := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports hroot
  have hlength := sameSupport_length_eq_of_nodup hsame
    (geometricPolymer_nodup hsupport) hsurfaceNodup
  rw [geometricPolymer_length_eq_support_length] at hlength
  exact hlength

theorem sevenCubeCycleRoot_lengths :
    sevenCube011To100Root.length = 28 ∧
    sevenCube100To000Root.length = 28 ∧
    sevenCube000To111Root.length = 28 ∧
    sevenCube111To011Root.length = 28 := by
  exact ⟨(encodedRoot_length_eq_surface_length
      sevenCube011To100Root_mem_canonical
      sevenCube011To100Root_sameSupport
      sevenCubeCycleSurface_nodups.1).trans
        sevenCubeCycleSurface_lengths.1,
    (encodedRoot_length_eq_surface_length
      sevenCube100To000Root_mem_canonical
      sevenCube100To000Root_sameSupport
      sevenCubeCycleSurface_nodups.2.1).trans
        sevenCubeCycleSurface_lengths.2.1,
    (encodedRoot_length_eq_surface_length
      sevenCube000To111Root_mem_canonical
      sevenCube000To111Root_sameSupport
      sevenCubeCycleSurface_nodups.2.2.1).trans
        sevenCubeCycleSurface_lengths.2.2.1,
    (encodedRoot_length_eq_surface_length
      sevenCube111To011Root_mem_canonical
      sevenCube111To011Root_sameSupport
      sevenCubeCycleSurface_nodups.2.2.2).trans
        sevenCubeCycleSurface_lengths.2.2.2⟩

#print axioms sevenCubeCycle_connectivity_certificates
#print axioms sevenCube011To100Surface_connected
#print axioms sevenCube100To000Surface_connected
#print axioms sevenCube000To111Surface_connected
#print axioms sevenCube111To011Surface_connected
#print axioms sevenCube011To100Root_mem_canonical
#print axioms sevenCube100To000Root_mem_canonical
#print axioms sevenCube000To111Root_mem_canonical
#print axioms sevenCube111To011Root_mem_canonical
#print axioms sevenCubeCycleRoot_lengths

end YMGap.Continuum.Z4OutwardSevenCubeCycleConnectedRoots
