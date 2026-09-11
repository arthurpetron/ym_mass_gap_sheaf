/-
# Realizing mixed adjacent-even trajectory fields in one canonical Gram

The mixed endpoint normal form evaluates the fixed-face kernel on an incoming
predecessor field and an outgoing trajectory field.  The symbolic incidence
carrier now contains both fields.  This leaf proves that the kernel depends
only on literal fixed face/link incidences and therefore identifies every
mixed trajectory kernel with an entry of one canonical production Gram.

No trajectory terminal product is glued here.  The remaining theorem is the
rankwise shared-glue factorization of the sum over trajectories.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceChannelCarrier

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTrajectoryFieldRealization

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceChannelCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceBlock
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge

local infix:50 " ≈ " => Q'.eqv

private theorem list_getD_mem_of_lt_local
    {A : Type} (fallback : A) : ∀ (items : List A) (index : Nat),
    index < items.length → items.getD index fallback ∈ items
  | [], _, hindex => by simp at hindex
  | head :: tail, 0, _ => List.mem_cons_self
  | head :: tail, index + 1, hindex => by
      simp only [List.getD_cons_succ]
      exact List.mem_cons_of_mem head
        (list_getD_mem_of_lt_local fallback tail index (by
          simp at hindex
          omega))

private theorem eliminateLinks_congr_eq_local
    (left right : Nat → Q') : ∀ ids : List Nat,
    (∀ id, id ∈ ids → left id = right id) →
      eliminateLinks left ids = eliminateLinks right ids
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [eliminateLinks]
      rw [hagree head List.mem_cons_self]
      exact congrArg (fun value => right head * value)
        (eliminateLinks_congr_eq_local left right tail
          (fun id hid => hagree id
            (List.mem_cons_of_mem head hid)))

private theorem fourChannels_ext_local
    (left right : FourChannels)
    (hfirst : left.first = right.first)
    (hsecond : left.second = right.second)
    (hthird : left.third = right.third)
    (hfourth : left.fourth = right.fourth) : left = right := by
  cases left
  cases right
  simp_all

/-! ## 1. Incidence-locality of the dependent fixed-face kernel -/

/-- The four-channel reader sees only literal fixed-face/link incidences. -/
theorem fixedFaceFourChannels_congr_on_incidences
    (radius : Nat) (incoming outgoing : FixedFaceChannelField)
    {id : Nat} (hid : id ∈ adjacentEvenFixedFaceIds radius)
    (hagree : ∀ face link,
      (face, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
      incoming face link = outgoing face link) :
    fixedFaceFourChannels radius id (incoming id) =
      fixedFaceFourChannels radius id (outgoing id) := by
  let links := adjacentEvenFixedFaceLinks radius id
  have hlength : links.length = 4 :=
    adjacentEvenFixedFaceLinks_length radius id
  have hmem : ∀ index, index < 4 →
      links.getD index defaultZ4Link ∈ links := by
    intro index hindex
    apply list_getD_mem_of_lt_local defaultZ4Link
    rw [hlength]
    exact hindex
  apply fourChannels_ext_local
  · exact hagree id (links.getD 0 defaultZ4Link)
      (mem_adjacentEvenFixedFaceMajorIncidences.mpr
        ⟨hid, hmem 0 (by decide)⟩)
  · exact hagree id (links.getD 1 defaultZ4Link)
      (mem_adjacentEvenFixedFaceMajorIncidences.mpr
        ⟨hid, hmem 1 (by decide)⟩)
  · exact hagree id (links.getD 2 defaultZ4Link)
      (mem_adjacentEvenFixedFaceMajorIncidences.mpr
        ⟨hid, hmem 2 (by decide)⟩)
  · exact hagree id (links.getD 3 defaultZ4Link)
      (mem_adjacentEvenFixedFaceMajorIncidences.mpr
        ⟨hid, hmem 3 (by decide)⟩)

private theorem adjacentEvenDependentFixedFaceBlockProduct_congr
    (K radius : Nat)
    (incoming incoming' outgoing outgoing' : FixedFaceChannelField)
    (hincoming : ∀ id link,
      (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
      incoming id link = incoming' id link)
    (houtgoing : ∀ id link,
      (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
      outgoing id link = outgoing' id link) :
    adjacentEvenDependentFixedFaceBlockProduct
        K radius incoming outgoing =
      adjacentEvenDependentFixedFaceBlockProduct
        K radius incoming' outgoing' := by
  unfold adjacentEvenDependentFixedFaceBlockProduct
  apply eliminateLinks_congr_eq_local
  intro id hid
  rw [fixedFaceFourChannels_congr_on_incidences
      radius incoming incoming' hid hincoming]
  rw [fixedFaceFourChannels_congr_on_incidences
      radius outgoing outgoing' hid houtgoing]

/-- The global dependent fixed-face kernel is unchanged when both fields
agree on all literal fixed incidences. -/
theorem adjacentEvenGlobalDependentFixedFaceChannelKernel_congr_on_incidences
    (K radius : Nat)
    (incoming incoming' outgoing outgoing' : FixedFaceChannelField)
    (hincoming : ∀ id link,
      (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
      incoming id link = incoming' id link)
    (houtgoing : ∀ id link,
      (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
      outgoing id link = outgoing' id link) :
    adjacentEvenGlobalDependentFixedFaceChannelKernel
        K radius incoming outgoing ≈
      adjacentEvenGlobalDependentFixedFaceChannelKernel
        K radius incoming' outgoing' := by
  refine Q'.eqv_trans _ _ _
    (adjacentEvenGlobalDependentFixedFaceChannelKernel_eqv_blockProduct
      K radius incoming outgoing) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq
      (adjacentEvenDependentFixedFaceBlockProduct_congr
        K radius incoming incoming' outgoing outgoing'
        hincoming houtgoing)) ?_
  exact Q'.eqv_symm
    (adjacentEvenGlobalDependentFixedFaceChannelKernel_eqv_blockProduct
      K radius incoming' outgoing')

/-! ## 2. One canonical production Gram and mixed-entry realization -/

/-- The production fixed-face Gram on the complete symbolic incidence-field
carrier.  Its carrier is not evaluated. -/
def adjacentEvenCanonicalFixedIncidenceGramRep
    (K radius : Nat) :=
  adjacentEvenProductionDependentFixedFaceChannelGramRep
    K radius
    (adjacentEvenFixedIncidenceMiddleField K radius)
    (adjacentEvenFixedIncidenceMiddleField_le K radius)

/-- Every mixed fixed-face trajectory kernel is an entry of the single
canonical incidence-field Gram. -/
theorem adjacentEvenTrajectoryFixedFaceResummedKernel_realized
    {K radius : Nat} {source : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K)
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    ∃ incoming outgoing,
      incoming < adjacentEvenFixedIncidenceMiddleCount K radius ∧
      outgoing < adjacentEvenFixedIncidenceMiddleCount K radius ∧
      adjacentEvenTrajectoryFixedFaceResummedKernel
          K radius source trajectory ≈
        adjacentEvenGlobalDependentFixedFaceChannelMatrix
          K radius
          (adjacentEvenFixedIncidenceMiddleField K radius)
          incoming outgoing := by
  obtain ⟨incoming, hincomingBound, hincoming⟩ :=
    adjacentEvenTrajectoryIncomingMiddleField_realized
      hsource htrajectory
  obtain ⟨outgoing, houtgoingBound, houtgoing⟩ :=
    adjacentEvenTrajectoryOutgoingMiddleField_realized htrajectory
  refine ⟨incoming, outgoing, hincomingBound, houtgoingBound, ?_⟩
  unfold adjacentEvenTrajectoryFixedFaceResummedKernel
    adjacentEvenGlobalDependentFixedFaceChannelMatrix
  exact adjacentEvenGlobalDependentFixedFaceChannelKernel_congr_on_incidences
    K radius
    (adjacentEvenTrajectoryIncomingField radius source trajectory)
    (adjacentEvenFixedIncidenceMiddleField K radius incoming)
    (adjacentEvenTrajectoryOutgoingField trajectory)
    (adjacentEvenFixedIncidenceMiddleField K radius outgoing)
    (fun id link hincidence =>
      (hincoming id link hincidence).symm)
    (fun id link hincidence =>
      (houtgoing id link hincidence).symm)

#print axioms fixedFaceFourChannels_congr_on_incidences
#print axioms adjacentEvenGlobalDependentFixedFaceChannelKernel_congr_on_incidences
#print axioms adjacentEvenCanonicalFixedIncidenceGramRep
#print axioms adjacentEvenTrajectoryFixedFaceResummedKernel_realized

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTrajectoryFieldRealization
