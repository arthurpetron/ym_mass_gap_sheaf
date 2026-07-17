/-
# Pointwise regrouping of fixed incidence trajectories by face

For each fixed link, an internal trajectory consists of one fusion transition
per fixed incident face and a final endpoint delta.  This file makes that split
exact, defines the predecessor channel of every literal incidence, and uses the
face-major/link-major incidence permutation to regroup all transition factors
into the existing four-link `fourFusionIndicator` blocks.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedWordTrajectoryFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceBlock
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem qMulCongrLocal {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Transition product and terminal delta -/

def fixedIdTransitionProduct
    (physical channel : Nat → Nat) : Nat → List Nat → Nat
  | _, [] => 1
  | start, id :: rest =>
      boolMultiplicity (fusionOK start (physical id) (channel id)) *
        fixedIdTransitionProduct physical channel (channel id) rest

def fixedIdFinalChannel
    (channel : Nat → Nat) : Nat → List Nat → Nat
  | start, [] => start
  | _, id :: rest => fixedIdFinalChannel channel (channel id) rest

def fixedIdTerminalIndicator
    (channel : Nat → Nat) (start finish : Nat)
    (ids : List Nat) : Nat :=
  boolMultiplicity (decide
    (fixedIdFinalChannel channel start ids = finish))

theorem fixedIdTrajectoryMultiplicity_eq_transition_mul_terminal
    (physical channel : Nat → Nat) : ∀ start finish ids,
    fixedIdTrajectoryMultiplicity physical channel start finish ids =
      fixedIdTransitionProduct physical channel start ids *
        fixedIdTerminalIndicator channel start finish ids
  | start, finish, [] => by
      simp [fixedIdTrajectoryMultiplicity,
        fixedIdTransitionProduct, fixedIdTerminalIndicator,
        fixedIdFinalChannel]
      rfl
  | start, finish, id :: rest => by
      simp only [fixedIdTrajectoryMultiplicity,
        fixedIdTransitionProduct, fixedIdTerminalIndicator,
        fixedIdFinalChannel]
      rw [fixedIdTrajectoryMultiplicity_eq_transition_mul_terminal
        physical channel (channel id) finish rest]
      exact (Nat.mul_assoc _ _ _).symm

/-! ## 2. The predecessor channel of an incidence -/

def fixedIdIncomingChannel
    (channel : Nat → Nat) : Nat → Nat → List Nat → Nat
  | start, _, [] => start
  | start, query, id :: rest =>
      if query = id then start
      else fixedIdIncomingChannel channel (channel id) query rest

@[simp] theorem fixedIdIncomingChannel_head
    (channel : Nat → Nat) (start head : Nat) (rest : List Nat) :
    fixedIdIncomingChannel channel start head (head :: rest) = start := by
  simp [fixedIdIncomingChannel]

theorem fixedIdIncomingChannel_cons_of_mem_tail
    (channel : Nat → Nat) (start query head : Nat)
    {rest : List Nat} (hhead : head ∉ rest)
    (hquery : query ∈ rest) :
    fixedIdIncomingChannel channel start query (head :: rest) =
      fixedIdIncomingChannel channel (channel head) query rest := by
  have hne : query ≠ head := by
    intro heq
    exact hhead (heq ▸ hquery)
  change (if query = head then start else
      fixedIdIncomingChannel channel (channel head) query rest) = _
  rw [if_neg hne]

def fixedIdTransitionFactor
    (physical channel : Nat → Nat)
    (start : Nat) (ids : List Nat) (id : Nat) : Nat :=
  boolMultiplicity (fusionOK
    (fixedIdIncomingChannel channel start id ids)
    (physical id) (channel id))

theorem fixedIdTransitionProduct_eq_natListProduct
    (physical channel : Nat → Nat) :
    ∀ ids : List Nat, ids.Nodup → ∀ start,
      fixedIdTransitionProduct physical channel start ids =
        natListProduct
          (fixedIdTransitionFactor physical channel start ids) ids
  | [], _, _ => rfl
  | head :: rest, hnodup, start => by
      have hparts := List.nodup_cons.mp hnodup
      simp only [fixedIdTransitionProduct, natListProduct,
        fixedIdTransitionFactor, fixedIdIncomingChannel_head]
      apply congrArg
        (fun value =>
          boolMultiplicity
              (fusionOK start (physical head) (channel head)) * value)
      refine (fixedIdTransitionProduct_eq_natListProduct
        physical channel rest hparts.2 (channel head)).trans ?_
      apply natListProduct_congr
      intro id hid
      unfold fixedIdTransitionFactor
      rw [fixedIdIncomingChannel_cons_of_mem_tail
        channel start id head hparts.1 hid]

private theorem ofNat_natListProduct_eqv_listQProductLocal
    {A : Type} (value : A → Nat) : ∀ items : List A,
    Q'.ofNat (natListProduct value items) ≈
      listQProduct (fun item => Q'.ofNat (value item)) items
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      simp only [natListProduct, listQProduct]
      exact Q'.eqv_trans _ _ _
        (ofNat_mul_eqv (value head)
          (natListProduct value tail))
        (Q'.mul_eqv_congr_left _ _ _
          (ofNat_natListProduct_eqv_listQProductLocal value tail))

theorem ofNat_fixedIdTransitionProduct_eqv_listQProduct
    (physical channel : Nat → Nat)
    (start : Nat) (ids : List Nat) (hnodup : ids.Nodup) :
    Q'.ofNat (fixedIdTransitionProduct physical channel start ids) ≈
      listQProduct (fun id =>
        Q'.ofNat (fixedIdTransitionFactor
          physical channel start ids id)) ids := by
  rw [fixedIdTransitionProduct_eq_natListProduct
    physical channel ids hnodup start]
  exact ofNat_natListProduct_eqv_listQProductLocal
    (fixedIdTransitionFactor physical channel start ids) ids

/-! ## 3. A single rational factor on each literal incidence -/

def adjacentEvenIncidenceIncomingChannel
    (radius : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState)
    (incidence : FixedFaceLinkIncidence) : Nat :=
  fixedIdIncomingChannel (trajectory incidence.2)
    (source incidence.2) incidence.1
    (adjacentEvenIncidentFixedFaceIds radius incidence.2)

def adjacentEvenIncidenceTransitionFactor
    (radius : Nat) (physical : Nat → Nat)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState)
    (incidence : FixedFaceLinkIncidence) : Q' :=
  fusionInd
    (adjacentEvenIncidenceIncomingChannel
      radius source trajectory incidence)
    (physical incidence.1) (trajectory incidence.2 incidence.1)

private theorem ofNat_boolMultiplicity_fusionOK_eqv_fusionInd
    (source fixed target : Nat) :
    Q'.ofNat (boolMultiplicity (fusionOK source fixed target)) ≈
      fusionInd source fixed target := by
  unfold boolMultiplicity fusionInd
  cases fusionOK source fixed target <;> decide

theorem fixedLinkTransition_eqv_incidenceBlock
    (radius : Nat) (physical : Nat → Nat)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState)
    (link : Z4Link) :
    Q'.ofNat (fixedIdTransitionProduct physical (trajectory link)
        (source link)
        (adjacentEvenIncidentFixedFaceIds radius link)) ≈
      listQProduct (adjacentEvenIncidenceTransitionFactor
        radius physical source trajectory)
        ((adjacentEvenIncidentFixedFaceIds radius link).map
          (fun id => (id, link))) := by
  refine Q'.eqv_trans _ _ _
    (ofNat_fixedIdTransitionProduct_eqv_listQProduct
      physical (trajectory link) (source link)
      (adjacentEvenIncidentFixedFaceIds radius link)
      (adjacentEvenIncidentFixedFaceIds_nodup radius link)) ?_
  rw [listQProduct_map]
  apply listQProduct_congr_eqv
  intro id _
  unfold fixedIdTransitionFactor
    adjacentEvenIncidenceTransitionFactor
    adjacentEvenIncidenceIncomingChannel
  exact ofNat_boolMultiplicity_fusionOK_eqv_fusionInd _ _ _

/-! ## 4. Generic finite-product flattening -/

private theorem listQProduct_appendLocal
    {A : Type} (value : A → Q') : ∀ left right : List A,
    listQProduct value (left ++ right) ≈
      listQProduct value left * listQProduct value right
  | [], right => Q'.eqv_symm
      (Q'.one_mul_eqv (listQProduct value right))
  | head :: tail, right => by
      simp only [List.cons_append, listQProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (value head) _ _
          (listQProduct_appendLocal value tail right)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

private theorem listQProduct_flatMapLocal
    {A B : Type} (value : B → Q') (block : A → List B) :
    ∀ source : List A,
      listQProduct value (source.flatMap block) ≈
        listQProduct (fun item => listQProduct value (block item)) source
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      simp only [List.flatMap_cons, listQProduct]
      refine Q'.eqv_trans _ _ _
        (listQProduct_appendLocal value (block head)
          (tail.flatMap block)) ?_
      exact Q'.mul_eqv_congr_left
        (listQProduct value (block head)) _ _
        (listQProduct_flatMapLocal value block tail)

private theorem listQProduct_pointwise_mul
    {A : Type} (left right : A → Q') : ∀ items : List A,
    listQProduct (fun item => left item * right item) items ≈
      listQProduct left items * listQProduct right items
  | [] => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | head :: tail => by
      simp only [listQProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (left head * right head) _ _
          (listQProduct_pointwise_mul left right tail)) ?_
      exact YMGap.Continuum.RingNormaliser.q_mul4_swap
        (left head) (right head)
        (listQProduct left tail) (listQProduct right tail)

/-! ## 5. Link-major transition product -/

def adjacentEvenLinkTransitionProduct
    (radius : Nat) (physical : Nat → Nat)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  listQProduct (fun link =>
    Q'.ofNat (fixedIdTransitionProduct physical (trajectory link)
      (source link)
      (adjacentEvenIncidentFixedFaceIds radius link)))
    (adjacentEvenFixedLinks radius)

def adjacentEvenLinkTerminalProduct
    (radius : Nat) (source target : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  listQProduct (fun link =>
    Q'.ofNat (fixedIdTerminalIndicator (trajectory link)
      (source link) (target link)
      (adjacentEvenIncidentFixedFaceIds radius link)))
    (adjacentEvenFixedLinks radius)

theorem adjacentEvenLinkTransitionProduct_eqv_linkMajorIncidences
    (radius : Nat) (physical : Nat → Nat)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    adjacentEvenLinkTransitionProduct
        radius physical source trajectory ≈
      listQProduct (adjacentEvenIncidenceTransitionFactor
        radius physical source trajectory)
        (adjacentEvenFixedLinkMajorIncidences radius) := by
  unfold adjacentEvenLinkTransitionProduct
    adjacentEvenFixedLinkMajorIncidences
  refine Q'.eqv_trans _ _ _
    (listQProduct_congr_eqv _ _
      (adjacentEvenFixedLinks radius)
      (fun link _ => fixedLinkTransition_eqv_incidenceBlock
        radius physical source trajectory link)) ?_
  exact Q'.eqv_symm
    (listQProduct_flatMapLocal
      (adjacentEvenIncidenceTransitionFactor
        radius physical source trajectory)
      (fun link =>
        (adjacentEvenIncidentFixedFaceIds radius link).map
          (fun id => (id, link)))
      (adjacentEvenFixedLinks radius))

/-! ## 6. Face-major four-channel blocks -/

def adjacentEvenFaceIncomingFourChannels
    (radius id : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) : FourChannels :=
  fixedFaceFourChannels radius id (fun link =>
    adjacentEvenIncidenceIncomingChannel radius source trajectory
      (id, link))

def adjacentEvenFaceOutgoingFourChannels
    (radius id : Nat)
    (trajectory : FixedIncidenceTrajectoryState) : FourChannels :=
  fixedFaceFourChannels radius id (fun link => trajectory link id)

def adjacentEvenFaceTransitionProduct
    (radius : Nat) (physical : Nat → Nat)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  listQProduct (fun id =>
    fourFusionIndicator
      (adjacentEvenFaceIncomingFourChannels
        radius id source trajectory)
      (physical id)
      (adjacentEvenFaceOutgoingFourChannels radius id trajectory))
    (adjacentEvenFixedFaceIds radius)

private theorem listQProduct_length_four
    {A : Type} (fallback : A) (value : A → Q')
    (items : List A) (hlength : items.length = 4) :
    listQProduct value items ≈
      value (items.getD 0 fallback) *
        (value (items.getD 1 fallback) *
          (value (items.getD 2 fallback) *
            value (items.getD 3 fallback))) := by
  cases items with
  | nil => simp at hlength
  | cons first tail =>
      cases tail with
      | nil => simp at hlength
      | cons second tail =>
          cases tail with
          | nil => simp at hlength
          | cons third tail =>
              cases tail with
              | nil => simp at hlength
              | cons fourth tail =>
                  cases tail with
                  | nil =>
                      change value first *
                          (value second *
                            (value third * (value fourth * 1))) ≈
                        value first *
                          (value second *
                            (value third * value fourth))
                      exact Q'.mul_eqv_congr_left _ _ _
                        (Q'.mul_eqv_congr_left _ _ _
                          (Q'.mul_eqv_congr_left _ _ _
                            (Q'.mul_one_eqv _)))
                  | cons fifth tail => simp at hlength

private theorem fixedFaceIncidenceBlock_eqv_fourFusionIndicator
    (radius id : Nat) (physical : Nat → Nat)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    listQProduct (adjacentEvenIncidenceTransitionFactor
        radius physical source trajectory)
        ((adjacentEvenFixedFaceLinks radius id).map
          (fun link => (id, link))) ≈
      fourFusionIndicator
        (adjacentEvenFaceIncomingFourChannels
          radius id source trajectory)
        (physical id)
        (adjacentEvenFaceOutgoingFourChannels
          radius id trajectory) := by
  rw [listQProduct_map]
  unfold adjacentEvenFaceIncomingFourChannels
    adjacentEvenFaceOutgoingFourChannels
    fixedFaceFourChannels fourFusionIndicator
  exact listQProduct_length_four defaultZ4Link
    (fun link =>
      adjacentEvenIncidenceTransitionFactor
        radius physical source trajectory (id, link))
    (adjacentEvenFixedFaceLinks radius id)
    (adjacentEvenFixedFaceLinks_length radius id)

theorem adjacentEvenLinkTransitionProduct_eqv_faceTransitionProduct
    (radius : Nat) (physical : Nat → Nat)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    adjacentEvenLinkTransitionProduct
        radius physical source trajectory ≈
      adjacentEvenFaceTransitionProduct
        radius physical source trajectory := by
  let factor := adjacentEvenIncidenceTransitionFactor
    radius physical source trajectory
  refine Q'.eqv_trans _ _ _
    (adjacentEvenLinkTransitionProduct_eqv_linkMajorIncidences
      radius physical source trajectory) ?_
  refine Q'.eqv_trans _ _ _
    (listQProduct_perm factor
      (adjacentEvenFixedFaceLinkIncidences_perm radius).symm) ?_
  unfold adjacentEvenFixedFaceMajorIncidences
    adjacentEvenFaceTransitionProduct
  refine Q'.eqv_trans _ _ _
    (listQProduct_flatMapLocal factor
      (fun id => (adjacentEvenFixedFaceLinks radius id).map
        (fun link => (id, link)))
      (adjacentEvenFixedFaceIds radius)) ?_
  apply listQProduct_congr_eqv
  intro id _
  exact fixedFaceIncidenceBlock_eqv_fourFusionIndicator
    radius id physical source trajectory

/-! ## 7. Complete pointwise trajectory regrouping -/

def adjacentEvenTrajectoryLinkProduct
    (radius : Nat) (physical : Nat → Nat)
    (source target : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  listQProduct (fun link =>
    Q'.ofNat (fixedIdTrajectoryMultiplicity physical
      (trajectory link) (source link) (target link)
      (adjacentEvenIncidentFixedFaceIds radius link)))
    (adjacentEvenFixedLinks radius)

/-- Pointwise strict-incidence theorem.  Every compatible internal trajectory
equals one product of four-link face transitions times the terminal endpoint
deltas.  The face factors are exactly the existing `fourFusionIndicator`s. -/
theorem adjacentEvenTrajectoryLinkProduct_eqv_faceProduct_mul_terminal
    (radius : Nat) (physical : Nat → Nat)
    (source target : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    adjacentEvenTrajectoryLinkProduct
        radius physical source target trajectory ≈
      adjacentEvenFaceTransitionProduct
          radius physical source trajectory *
        listQProduct (fun link =>
          Q'.ofNat (fixedIdTerminalIndicator (trajectory link)
            (source link) (target link)
            (adjacentEvenIncidentFixedFaceIds radius link)))
          (adjacentEvenFixedLinks radius) := by
  unfold adjacentEvenTrajectoryLinkProduct
  let transition : Z4Link → Q' := fun link =>
    Q'.ofNat (fixedIdTransitionProduct physical (trajectory link)
      (source link)
      (adjacentEvenIncidentFixedFaceIds radius link))
  let terminal : Z4Link → Q' := fun link =>
    Q'.ofNat (fixedIdTerminalIndicator (trajectory link)
      (source link) (target link)
      (adjacentEvenIncidentFixedFaceIds radius link))
  refine Q'.eqv_trans _ _ _
    (listQProduct_congr_eqv _ _
      (adjacentEvenFixedLinks radius) (fun link _ => by
        rw [fixedIdTrajectoryMultiplicity_eq_transition_mul_terminal]
        exact ofNat_mul_eqv _ _)) ?_
  refine Q'.eqv_trans _ _ _
    (listQProduct_pointwise_mul transition terminal
      (adjacentEvenFixedLinks radius)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (adjacentEvenLinkTransitionProduct_eqv_faceTransitionProduct
      radius physical source trajectory)

#print axioms fixedIdTrajectoryMultiplicity_eq_transition_mul_terminal
#print axioms fixedIdTransitionProduct_eq_natListProduct
#print axioms adjacentEvenLinkTransitionProduct_eqv_faceTransitionProduct
#print axioms adjacentEvenTrajectoryLinkProduct_eqv_faceProduct_mul_terminal

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup
