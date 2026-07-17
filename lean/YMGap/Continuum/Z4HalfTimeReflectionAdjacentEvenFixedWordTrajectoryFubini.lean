/-
# Explicit fixed-word trajectory Fubini

The multi-fixed transition on one adjacent-even fixed link is a recursive
fusion walk.  Here it is rewritten as one literal finite sum over a bounded
channel assignment on the actual fixed incident-face identifiers.  This
exposes every intermediate channel needed for the subsequent face/link Fubini
interchange.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedWordTrajectoryFubini

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A channel assignment on the literal fixed face IDs -/

def fixedIdTrajectoryMultiplicity
    (physical channel : Nat → Nat) : Nat → Nat → List Nat → Nat
  | start, finish, [] => boolMultiplicity (decide (start = finish))
  | start, finish, id :: rest =>
      boolMultiplicity (fusionOK start (physical id) (channel id)) *
        fixedIdTrajectoryMultiplicity physical channel
          (channel id) finish rest

private theorem fixedIdTrajectoryMultiplicity_congr_on
    (physical left right : Nat → Nat) (start finish : Nat) :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → left id = right id) →
      fixedIdTrajectoryMultiplicity physical left start finish ids =
        fixedIdTrajectoryMultiplicity physical right start finish ids
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [fixedIdTrajectoryMultiplicity]
      have hhead := hagree head List.mem_cons_self
      rw [hhead]
      exact congrArg
        (fun value =>
          boolMultiplicity
              (fusionOK start (physical head) (right head)) * value)
        (fixedIdTrajectoryMultiplicity_congr_on
          physical left right (right head) finish tail
          (fun id hid => hagree id
            (List.mem_cons_of_mem head hid)))

private theorem fixedIdTrajectoryMultiplicity_set_head
    (physical label : Nat → Nat)
    {head : Nat} {rest : List Nat} (hhead : head ∉ rest)
    (next start finish : Nat) :
    fixedIdTrajectoryMultiplicity physical
        (setLabelOn label head next) start finish (head :: rest) =
      boolMultiplicity (fusionOK start (physical head) next) *
        fixedIdTrajectoryMultiplicity physical label next finish rest := by
  simp only [fixedIdTrajectoryMultiplicity]
  have hcurrent : setLabelOn label head next head = next := by
    simp [setLabelOn]
  rw [hcurrent]
  apply congrArg
    (fun value =>
      boolMultiplicity (fusionOK start (physical head) next) * value)
  apply fixedIdTrajectoryMultiplicity_congr_on
  intro id hid
  have hne : id ≠ head := by
    intro heq
    exact hhead (heq ▸ hid)
  simp [setLabelOn, hne]

/-! ## 2. Rational finite-sum transport -/

private theorem ofNat_natListSumMap_eqvLocal
    {A : Type} (value : A → Nat) : ∀ items : List A,
    Q'.ofNat (natListSum (items.map value)) ≈
      listQSum (fun item => Q'.ofNat (value item)) items
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      simp only [List.map_cons, natListSum, listQSum]
      exact Q'.eqv_trans _ _ _
        (Q'.ofNat_add_eqv (value head)
          (natListSum (tail.map value)))
        (Q'.add_eqv_congr_left _ _ _
          (ofNat_natListSumMap_eqvLocal value tail))

private theorem listQSum_zeroLocal {A : Type} :
    ∀ items : List A,
      listQSum (fun _ : A => (0 : Q')) items ≈ 0
  | [] => Q'.eqv_refl 0
  | _ :: tail => by
      simp only [listQSum]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl 0)
          (listQSum_zeroLocal tail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

/-! ## 3. A fusion walk is the explicit compatible trajectory sum -/

/-- Exact expansion of a fixed-word fusion walk into bounded channels attached
to the displayed noduplicated face IDs. -/
theorem ofNat_fusionWalk_map_eqv_fixedIdTrajectorySum
    (cutoff : Nat) (physical : Nat → Nat) :
    ∀ ids : List Nat, ids.Nodup → ∀ start finish,
      Q'.ofNat (fusionWalkMultiplicity cutoff start finish
          (ids.map physical)) ≈
        listQSum (fun channel =>
          Q'.ofNat (fixedIdTrajectoryMultiplicity
            physical channel start finish ids))
          (boundedLabellingsOn cutoff ids)
  | [], _, start, finish => by
      change Q'.ofNat (boolMultiplicity (decide (start = finish))) ≈
        Q'.ofNat (boolMultiplicity (decide (start = finish))) + 0
      exact Q'.eqv_symm
        (q_add_zero_eqv
          (Q'.ofNat (boolMultiplicity (decide (start = finish)))) )
  | head :: rest, hnodup, start, finish => by
      have hparts := List.nodup_cons.mp hnodup
      let leftTerm : Nat → Q' := fun next =>
        Q'.ofNat
          (if fusionOK start (physical head) next then
            fusionWalkMultiplicity cutoff next finish
              (rest.map physical)
          else 0)
      let rightTerm : Nat → Q' := fun next =>
        listQSum (fun channel =>
          Q'.ofNat (fixedIdTrajectoryMultiplicity physical
            (setLabelOn channel head next) start finish
            (head :: rest)))
          (boundedLabellingsOn cutoff rest)
      have hleft :
          Q'.ofNat (fusionWalkMultiplicity cutoff start finish
              ((head :: rest).map physical)) ≈
            fsum leftTerm (cutoff + 1) := by
        simp only [List.map_cons, fusionWalkMultiplicity]
        refine Q'.eqv_trans _ _ _
          (ofNat_natListSumMap_eqvLocal
            (fun next =>
              if fusionOK start (physical head) next then
                fusionWalkMultiplicity cutoff next finish
                  (rest.map physical)
              else 0)
            (List.range (cutoff + 1))) ?_
        exact listQSum_range_eq_fsum leftTerm (cutoff + 1)
      have hterm : ∀ next, leftTerm next ≈ rightTerm next := by
        intro next
        by_cases hfusion :
            fusionOK start (physical head) next = true
        · have hpoint : ∀ channel,
              Q'.ofNat (fixedIdTrajectoryMultiplicity physical
                  (setLabelOn channel head next) start finish
                  (head :: rest)) ≈
                Q'.ofNat (fixedIdTrajectoryMultiplicity physical
                  channel next finish rest) := by
            intro channel
            rw [fixedIdTrajectoryMultiplicity_set_head
              physical channel hparts.1 next start finish]
            simp [hfusion, boolMultiplicity]
            exact Q'.eqv_refl _
          have hsum : rightTerm next ≈
              listQSum (fun channel =>
                Q'.ofNat (fixedIdTrajectoryMultiplicity physical
                  channel next finish rest))
                (boundedLabellingsOn cutoff rest) := by
            unfold rightTerm
            exact listQSum_congr hpoint
              (boundedLabellingsOn cutoff rest)
          unfold leftTerm
          rw [hfusion]
          simp only [if_true]
          exact Q'.eqv_trans _ _ _
            (ofNat_fusionWalk_map_eqv_fixedIdTrajectorySum
              cutoff physical rest hparts.2 next finish)
            (Q'.eqv_symm hsum)
        · have hfalse :
              fusionOK start (physical head) next = false := by
            cases h : fusionOK start (physical head) next
            · rfl
            · exact False.elim (hfusion h)
          have hpoint : ∀ channel,
              Q'.ofNat (fixedIdTrajectoryMultiplicity physical
                  (setLabelOn channel head next) start finish
                  (head :: rest)) ≈ 0 := by
            intro channel
            rw [fixedIdTrajectoryMultiplicity_set_head
              physical channel hparts.1 next start finish]
            simp [hfalse, boolMultiplicity]
            exact Q'.ofNat_zero_eqv
          have hsum : rightTerm next ≈ 0 := by
            unfold rightTerm
            refine Q'.eqv_trans _ _ _
              (listQSum_congr hpoint
                (boundedLabellingsOn cutoff rest)) ?_
            exact listQSum_zeroLocal
              (boundedLabellingsOn cutoff rest)
          unfold leftTerm
          rw [hfalse]
          exact Q'.eqv_trans _ _ _ Q'.ofNat_zero_eqv
            (Q'.eqv_symm hsum)
      refine Q'.eqv_trans _ _ _ hleft ?_
      refine Q'.eqv_trans _ _ _
        (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
          leftTerm rightTerm hterm (cutoff + 1)) ?_
      exact Q'.eqv_symm
        (listQSum_boundedLabellingsOn_cons cutoff head rest
          (fun channel =>
            Q'.ofNat (fixedIdTrajectoryMultiplicity physical
              channel start finish (head :: rest))))

/-! ## 4. Literal fixed incident-face word -/

def adjacentEvenIncidentFixedFaceIds
    (radius : Nat) (link : Z4Link) : List Nat :=
  (adjacentEvenIncidentFaceIdParts radius link).2.1

theorem adjacentEvenIncidentFixedFaceIds_nodup
    (radius : Nat) (link : Z4Link) :
    (adjacentEvenIncidentFixedFaceIds radius link).Nodup := by
  have hfull := slabIncidentPlaqIds_nodup
    (adjacentEvenExtent radius) link
  have hall :
      ((adjacentEvenIncidentFaceIdParts radius link).1 ++
        (adjacentEvenIncidentFaceIdParts radius link).2.1 ++
        (adjacentEvenIncidentFaceIdParts radius link).2.2).Nodup :=
    (partitionBySide_perm
      (fun id => adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id))
      (slabIncidentPlaqIds (adjacentEvenExtent radius) link)).symm.nodup
        hfull
  have houter := List.nodup_append.mp hall
  have hlowerFixed := List.nodup_append.mp houter.1
  exact hlowerFixed.2.1

theorem ofNat_adjacentEvenFixedWordTransition_eqv_trajectorySum
    (K radius source target : Nat)
    (physical : Nat → Nat) (link : Z4Link) :
    Q'.ofNat (fusionWalkMultiplicity (linkAuxiliaryCutoff K)
        source target
        (adjacentEvenIncidentFixedSpins radius physical link)) ≈
      listQSum (fun channel =>
        Q'.ofNat (fixedIdTrajectoryMultiplicity physical channel
          source target
          (adjacentEvenIncidentFixedFaceIds radius link)))
        (boundedLabellingsOn (linkAuxiliaryCutoff K)
          (adjacentEvenIncidentFixedFaceIds radius link)) := by
  unfold adjacentEvenIncidentFixedSpins
    adjacentEvenIncidentFixedFaceIds
  exact ofNat_fusionWalk_map_eqv_fixedIdTrajectorySum
    (linkAuxiliaryCutoff K) physical
    (adjacentEvenIncidentFaceIdParts radius link).2.1
    (adjacentEvenIncidentFixedFaceIds_nodup radius link)
    source target

#print axioms ofNat_fusionWalk_map_eqv_fixedIdTrajectorySum
#print axioms adjacentEvenIncidentFixedFaceIds_nodup
#print axioms ofNat_adjacentEvenFixedWordTransition_eqv_trajectorySum

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedWordTrajectoryFubini
