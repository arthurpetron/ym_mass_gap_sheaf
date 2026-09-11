/-
# Terminal products as functions of canonical trajectory fields

The fixed-face part of every mixed trajectory has already been realized in
one canonical Gram.  This leaf proves that the terminal endpoint delta also
depends only on the same outgoing fixed-incidence field.  Thus a complete
decorated trajectory term can be represented by canonical incoming and
outgoing middle indices.

This does not yet reindex the whole trajectory sum or prove its shared-glue
sum-of-squares factorization.  It removes field preservation and terminal
preservation from that remaining combinatorial theorem.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTrajectoryFieldRealization

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTrajectoryTerminalField

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceChannelCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTrajectoryFieldRealization
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Wordwise channel congruence -/

theorem fixedIdIncomingChannel_congr_on
    (left right : Nat → Nat) : ∀ (start query : Nat) (ids : List Nat),
    (∀ id, id ∈ ids → left id = right id) →
      fixedIdIncomingChannel left start query ids =
        fixedIdIncomingChannel right start query ids
  | _, _, [], _ => rfl
  | start, query, head :: tail, hagree => by
      by_cases heq : query = head
      · subst query
        simp [fixedIdIncomingChannel]
      · change (if query = head then start else
          fixedIdIncomingChannel left (left head) query tail) =
          (if query = head then start else
            fixedIdIncomingChannel right (right head) query tail)
        rw [if_neg heq, if_neg heq, hagree head List.mem_cons_self]
        exact fixedIdIncomingChannel_congr_on left right
          (right head) query tail
          (fun id hid => hagree id
            (List.mem_cons_of_mem head hid))

theorem fixedIdFinalChannel_congr_on
    (left right : Nat → Nat) : ∀ (start : Nat) (ids : List Nat),
    (∀ id, id ∈ ids → left id = right id) →
      fixedIdFinalChannel left start ids =
        fixedIdFinalChannel right start ids
  | _, [], _ => rfl
  | _, head :: tail, hagree => by
      simp only [fixedIdFinalChannel]
      rw [hagree head List.mem_cons_self]
      exact fixedIdFinalChannel_congr_on left right
        (right head) tail
        (fun id hid => hagree id
          (List.mem_cons_of_mem head hid))

theorem fixedIdTerminalIndicator_congr_on
    (left right : Nat → Nat) (start finish : Nat) (ids : List Nat)
    (hagree : ∀ id, id ∈ ids → left id = right id) :
    fixedIdTerminalIndicator left start finish ids =
      fixedIdTerminalIndicator right start finish ids := by
  unfold fixedIdTerminalIndicator
  rw [fixedIdFinalChannel_congr_on left right start ids hagree]

/-! ## 2. Global terminal preservation -/

/-- Read a face-dependent field as the link-major trajectory carrying its
post-channel on every incidence. -/
def adjacentEvenTrajectoryOfField
    (field : FixedFaceChannelField) : FixedIncidenceTrajectoryState :=
  fun link id => field id link

/-- The complete terminal endpoint product depends only on the outgoing
channels at literal fixed incidences. -/
theorem adjacentEvenLinkTerminalProduct_congr_on_fixed_incidences
    (radius : Nat) (source target : Z4Link → Nat)
    (left right : FixedIncidenceTrajectoryState)
    (hagree : ∀ id link,
      (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
      left link id = right link id) :
    adjacentEvenLinkTerminalProduct radius source target left =
      adjacentEvenLinkTerminalProduct radius source target right := by
  unfold adjacentEvenLinkTerminalProduct
  apply listQProduct_congr
  intro link hlink
  apply congrArg Q'.ofNat
  apply fixedIdTerminalIndicator_congr_on
  intro id hid
  apply hagree id link
  apply adjacentEvenFixedIncidence_mem_iff.mpr
  exact mem_adjacentEvenFixedLinkMajorIncidences.mpr ⟨hlink, hid⟩

/-- The incoming predecessor field is also determined by the outgoing
trajectory channels on literal fixed incidences. -/
theorem adjacentEvenTrajectoryIncomingField_congr_on_fixed_incidences
    (radius : Nat) (source : Z4Link → Nat)
    (left right : FixedIncidenceTrajectoryState)
    (hagree : ∀ id link,
      (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
      left link id = right link id)
    {id : Nat} {link : Z4Link}
    (hincidence : (id, link) ∈
      adjacentEvenFixedFaceMajorIncidences radius) :
    adjacentEvenTrajectoryIncomingField radius source left id link =
      adjacentEvenTrajectoryIncomingField radius source right id link := by
  unfold adjacentEvenTrajectoryIncomingField
    adjacentEvenIncidenceIncomingChannel
  apply fixedIdIncomingChannel_congr_on
  intro face hface
  apply hagree face link
  apply adjacentEvenFixedIncidence_mem_iff.mpr
  have hlinkMajor : (id, link) ∈
      adjacentEvenFixedLinkMajorIncidences radius :=
    adjacentEvenFixedIncidence_mem_iff.mp hincidence
  have hparts :=
    mem_adjacentEvenFixedLinkMajorIncidences.mp hlinkMajor
  exact mem_adjacentEvenFixedLinkMajorIncidences.mpr
    ⟨hparts.1, hface⟩

/-- Terminal product computed directly from one canonical outgoing middle
field. -/
def adjacentEvenMiddleFieldTerminalProduct
    (K radius : Nat) (source target : Z4Link → Nat)
    (outgoing : Nat) : Q' :=
  adjacentEvenLinkTerminalProduct radius source target
    (adjacentEvenTrajectoryOfField
      (adjacentEvenFixedIncidenceMiddleField K radius outgoing))

/-! ## 3. Complete decorated-trajectory realization -/

/-- Every mixed trajectory term admits canonical incoming/outgoing indices
that simultaneously realize its fixed-face Gram entry and its terminal
endpoint factor.  The witnesses are intuitionistic existential data; no
global choice or function-space equality search is used. -/
theorem adjacentEvenDecoratedTrajectoryTerm_realized
    {K radius : Nat} {source target : Z4Link → Nat}
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
          incoming outgoing ∧
      adjacentEvenLinkTerminalProduct radius source target trajectory ≈
        adjacentEvenMiddleFieldTerminalProduct
          K radius source target outgoing := by
  obtain ⟨incoming, hincomingBound, hincoming⟩ :=
    adjacentEvenTrajectoryIncomingMiddleField_realized
      hsource htrajectory
  obtain ⟨outgoing, houtgoingBound, houtgoing⟩ :=
    adjacentEvenTrajectoryOutgoingMiddleField_realized htrajectory
  refine ⟨incoming, outgoing, hincomingBound, houtgoingBound, ?_, ?_⟩
  · unfold adjacentEvenTrajectoryFixedFaceResummedKernel
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
  · apply Q'.eqv_of_eq
    unfold adjacentEvenMiddleFieldTerminalProduct
    apply adjacentEvenLinkTerminalProduct_congr_on_fixed_incidences
    intro id link hincidence
    change trajectory link id =
      adjacentEvenFixedIncidenceMiddleField K radius outgoing id link
    exact (houtgoing id link hincidence).symm

/-- Strong form of canonical term realization.  Besides identifying the
product summand, it proves that the canonical incoming index is reconstructed
from the source endpoint and the canonical outgoing middle trajectory.  Thus
the entire summand is determined by `(source, incoming, outgoing)`; what
remains is the global multiplicity/reindexing and the per-rank shared SOS. -/
theorem adjacentEvenDecoratedTrajectorySummand_realized
    {K radius : Nat} {source target : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K)
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    ∃ incoming outgoing,
      incoming < adjacentEvenFixedIncidenceMiddleCount K radius ∧
      outgoing < adjacentEvenFixedIncidenceMiddleCount K radius ∧
      (adjacentEvenTrajectoryFixedFaceResummedKernel
            K radius source trajectory *
          adjacentEvenLinkTerminalProduct
            radius source target trajectory ≈
        adjacentEvenGlobalDependentFixedFaceChannelMatrix
            K radius
            (adjacentEvenFixedIncidenceMiddleField K radius)
            incoming outgoing *
          adjacentEvenMiddleFieldTerminalProduct
            K radius source target outgoing) ∧
      ∀ id link,
        (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
        adjacentEvenFixedIncidenceMiddleField
            K radius incoming id link =
          adjacentEvenTrajectoryIncomingField radius source
            (adjacentEvenTrajectoryOfField
              (adjacentEvenFixedIncidenceMiddleField
                K radius outgoing)) id link := by
  obtain ⟨incoming, hincomingBound, hincoming⟩ :=
    adjacentEvenTrajectoryIncomingMiddleField_realized
      hsource htrajectory
  obtain ⟨outgoing, houtgoingBound, houtgoing⟩ :=
    adjacentEvenTrajectoryOutgoingMiddleField_realized htrajectory
  have hface :
      adjacentEvenTrajectoryFixedFaceResummedKernel
          K radius source trajectory ≈
        adjacentEvenGlobalDependentFixedFaceChannelMatrix
          K radius
          (adjacentEvenFixedIncidenceMiddleField K radius)
          incoming outgoing := by
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
  have hterminal :
      adjacentEvenLinkTerminalProduct radius source target trajectory ≈
        adjacentEvenMiddleFieldTerminalProduct
          K radius source target outgoing := by
    apply Q'.eqv_of_eq
    unfold adjacentEvenMiddleFieldTerminalProduct
    apply adjacentEvenLinkTerminalProduct_congr_on_fixed_incidences
    intro id link hincidence
    change trajectory link id =
      adjacentEvenFixedIncidenceMiddleField K radius outgoing id link
    exact (houtgoing id link hincidence).symm
  refine ⟨incoming, outgoing, hincomingBound, houtgoingBound, ?_, ?_⟩
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hface)
      (Q'.mul_eqv_congr_left _ _ _ hterminal)
  · intro id link hincidence
    exact (hincoming id link hincidence).trans
      (adjacentEvenTrajectoryIncomingField_congr_on_fixed_incidences
        radius source trajectory
        (adjacentEvenTrajectoryOfField
          (adjacentEvenFixedIncidenceMiddleField K radius outgoing))
        (fun face edge hedge =>
          (houtgoing face edge hedge).symm)
        hincidence)

#print axioms fixedIdIncomingChannel_congr_on
#print axioms fixedIdFinalChannel_congr_on
#print axioms fixedIdTerminalIndicator_congr_on
#print axioms adjacentEvenLinkTerminalProduct_congr_on_fixed_incidences
#print axioms adjacentEvenTrajectoryIncomingField_congr_on_fixed_incidences
#print axioms adjacentEvenDecoratedTrajectoryTerm_realized
#print axioms adjacentEvenDecoratedTrajectorySummand_realized

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTrajectoryTerminalField
