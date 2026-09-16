/-
# Distance and insertion activity in the SAME original response

The three marked supports are two supplied connected probe carriers and
the actual inserted plaquette. No connecting corridor is added to those
carriers. Their maximum pairwise base-coordinate distance, minus the two
carrier sizes, is the minimum number of old faces required in a retained
response core. Exact insertion activity and detached partition factors are
retained in the resulting finite sum. Its signed cofactor has no proved
magnitude bound here; neither spatial decay nor a physical gap follows.
-/

import YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
import YMGap.Continuum.BF4ExactSlabThreeMarkGeometry
import YMGap.Continuum.BF4ExactSlabResponseInsertionActivity
import YMGap.Continuum.BF4ExactSlabRootedResponseResummation

namespace YMGap.Continuum.BF4ExactSlabResponseDistanceActivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabCoreDistanceFloor (rootedAnimal_linf_size_floor)
open YMGap.Continuum.SepLatticeZ4Linf (linfDist)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabThreeMarkGeometry
open YMGap.Continuum.BF4ExactSlabRootedResponseResummation
open YMGap.Continuum.BF4ExactSlabResponseInsertionActivity
open YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- Diameter of the actual three marked roots, with no added corridor. -/
def markedDiameter {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent id : Nat) : Nat :=
  max (linfDist P.animal.root Q.animal.root)
    (max (linfDist P.animal.root (slabPlaquetteAt extent id))
      (linfDist Q.animal.root (slabPlaquetteAt extent id)))

/-- The inserted face pays one place in the connected animal, not an old core face. -/
def minimumResponseSize {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent id : Nat) : Nat :=
  markedDiameter P Q extent id - (P.animal.support.length+Q.animal.support.length)

private theorem animal_pair_size (A : RootedConnectedAnimal z4Chain)
    (p q : Z4Plaq) (hp : p ∈ A.support) (hq : q ∈ A.support) :
    linfDist p q+1 ≤ A.support.length :=
  rootedAnimal_linf_size_floor
    (⟨p, A.support, hp, A.support_nodup, A.connected⟩ : RootedConnectedAnimal z4Chain) q hq

private theorem diameter_size {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent id n : Nat) (A : RootedConnectedAnimal z4Chain)
    (hp : P.animal.root ∈ A.support) (hq : Q.animal.root ∈ A.support)
    (hf : slabPlaquetteAt extent id ∈ A.support)
    (hsize : A.support.length ≤ P.animal.support.length+Q.animal.support.length+n+1) :
    minimumResponseSize P Q extent id ≤ n := by
  have hpq := animal_pair_size A _ _ hp hq
  have hpf := animal_pair_size A _ _ hp hf
  have hqf := animal_pair_size A _ _ hq hf
  unfold minimumResponseSize markedDiameter
  omega

/-- A fresh inserted face and two connected probe carriers give the
distance floor for EVERY retained original response anchor. -/
theorem response_anchor_size_floor {left right : List Z4Link}
    (P : ProbeCarrier left) (Q : ProbeCarrier right) (extent id : Nat)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ j, j ∈ ambient → j ∈ slabPhysicalFaceEdges extent)
    (hid : id ∈ slabPhysicalFaceEdges extent) (hfresh : id ∉ ambient)
    (anchor : List Nat) (ha : anchor ∈ responseAnchors extent id left right ambient) :
    minimumResponseSize P Q extent id ≤ anchor.length := by
  have hs := (List.mem_filter.mp (List.mem_filter.mp ha).1).1
  have hk := (List.mem_filter.mp ha).2
  have hf : core extent (markedLinks extent id left right) anchor = anchor :=
    of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp ha).1).2
  have han := (selected_sublist hs).nodup hn
  have hap : ∀ j, j ∈ anchor → j ∈ slabPhysicalFaceEdges extent :=
    fun j hj => hphys j (selected_mem hs j hj)
  have haf : id ∉ anchor := fun hi => hfresh (selected_mem hs id hi)
  let A := responseAnimal P Q extent anchor id han hap hid haf hk hf
  exact diameter_size P Q extent id anchor.length A
    (BF4ExactSlabTwoProbeAnimal.left_support_mem P Q extent (id::anchor) _ P.animal.root_mem)
    (BF4ExactSlabTwoProbeAnimal.right_support_mem P Q extent (id::anchor) _ Q.animal.root_mem)
    (responseAnimal_inserted_mem P Q extent anchor id han hap hid haf hk hf)
    (responseAnimal_size_le P Q extent anchor id han hap hid haf hk hf)

/-- Filtering out short cores changes no retained original response term. -/
theorem responseAnchors_size_filter {left right : List Z4Link}
    (P : ProbeCarrier left) (Q : ProbeCarrier right) (extent id : Nat)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ j, j ∈ ambient → j ∈ slabPhysicalFaceEdges extent)
    (hid : id ∈ slabPhysicalFaceEdges extent) (hfresh : id ∉ ambient) :
    (responseAnchors extent id left right ambient).filter
      (fun anchor => decide (minimumResponseSize P Q extent id ≤ anchor.length)) =
        responseAnchors extent id left right ambient :=
  List.filter_eq_self.mpr (fun anchor ha => decide_eq_true
    (response_anchor_size_floor P Q extent id ambient hn hphys hid hfresh anchor ha))

/-- Computed signed cofactor sum over cores satisfying the proved distance
floor. Each retains its own ORIGINAL detached partition fourth power. -/
def distanceActivity {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (w : Q') (K extent id : Nat) (p q : RatPoly) (ambient : List Nat) : Q' :=
  listQSum (fun anchor => insertionCoefficient w K extent id p q anchor *
    partitionFourth w K extent (detachedIds extent (markedLinks extent id left right) anchor ambient))
    ((responseAnchors extent id left right ambient).filter
      (fun anchor => decide (minimumResponseSize P Q extent id ≤ anchor.length)))

/-- The SAME original signed response has one explicit SU(2) insertion
activity factor and no too-short core. This holds at all rational w and K,
including zero, and assumes no estimate on the surviving cofactor. -/
theorem response_distance_activity {left right : List Z4Link}
    (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (w : Q') (K extent id : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ j, j ∈ ambient → j ∈ slabPhysicalFaceEdges extent)
    (hid : id ∈ slabPhysicalFaceEdges extent) (hfresh : id ∉ ambient) :
    response w K extent ambient id p q ≈
      (qpow w 3)*distanceActivity P Q w K extent id p q ambient := by
  unfold distanceActivity
  rw [responseAnchors_size_filter P Q extent id ambient hn hphys hid hfresh]
  refine Q'.eqv_trans _ _ _
    (response_resummed_filtered w K extent p q left right hp hq hl hr ambient hn id) ?_
  exact Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun anchor _ =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (responseCoefficient_activity w K extent id p q anchor)) (Q'.mul_assoc_eqv _ _ _)))
    (listQSum_mul_left _ _ _)

end YMGap.Continuum.BF4ExactSlabResponseDistanceActivity

#print axioms YMGap.Continuum.BF4ExactSlabResponseDistanceActivity.markedDiameter
#print axioms YMGap.Continuum.BF4ExactSlabResponseDistanceActivity.minimumResponseSize
#print axioms YMGap.Continuum.BF4ExactSlabResponseDistanceActivity.response_anchor_size_floor
#print axioms YMGap.Continuum.BF4ExactSlabResponseDistanceActivity.responseAnchors_size_filter
#print axioms YMGap.Continuum.BF4ExactSlabResponseDistanceActivity.distanceActivity
#print axioms YMGap.Continuum.BF4ExactSlabResponseDistanceActivity.response_distance_activity
