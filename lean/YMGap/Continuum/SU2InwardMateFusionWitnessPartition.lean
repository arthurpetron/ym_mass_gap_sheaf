/-
# Partition an ordered SU(2) source witness at the inward mate

For a root-first source word `left :: right :: rest`, the first fusion
channel either survives the even inward mate or is the unique stretched
channel `left + right`.  The multiplicity proof previously used this only
after summing channel counts.  Here we begin the witness-level compiler by
constructively deleting the forced stretched first vertex.

`stretchedFusionWitnessDrop` is the inverse coordinate shift to
`stretchedFusionWitnessLift` through valence six.  An accepted source whose
first channel is stretched drops to an accepted witness for the collapsed
word `(left + right) :: rest`, and lifting that dropped witness recovers the
source exactly.  This is the injective debt branch needed for the eventual
source-to-`mate + debt` partition; no pointwise identification between
different external face orders is made.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport
import YMGap.Continuum.SU2StretchedFusionWitnessLift

namespace YMGap.Continuum.SU2InwardMateFusionWitnessPartition

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2StretchedFusionWitnessLift
open YMGap.Continuum.SU2StretchedTrivalentStrandContinuation
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Read and delete the first root-first channel -/

/-- The output of the first trivalent vertex in the canonical source chain.
For valence two it is the forced zero output; for valence three it is the
third physical leg; from valence four onward it is the first auxiliary edge.
The final branch is outside the geometrically used valence-six range. -/
def sourceFirstFusionChannel : List Nat → EdgeLabelling → Nat
  | [], _ => 0
  | [third], _ => third
  | _ :: _ :: [], source => source 5
  | _ :: _ :: _ :: [], source => source 6
  | _ :: _ :: _ :: _ :: [], source => source 7
  | _, _ => 0

/-- Delete a forced stretched first vertex and shift the remaining canonical
internal coordinates back to the collapsed chain. -/
def stretchedFusionWitnessDrop : List Nat → EdgeLabelling → EdgeLabelling
  | [], _ => zeroEdgeLabelling
  | [_], _ => zeroEdgeLabelling
  | _ :: _ :: [], _ => zeroEdgeLabelling
  | _ :: _ :: _ :: [], source =>
      setEdgeLabel zeroEdgeLabelling 5 (source 7)
  | _ :: _ :: _ :: _ :: [], source =>
      setEdgeLabel
        (setEdgeLabel zeroEdgeLabelling 6 (source 8))
        7 (source 9)
  | _, _ => zeroEdgeLabelling

/-- Membership in the source fiber exposes the actual first trivalent
fusion rule, uniformly over every geometrically possible remaining word. -/
theorem sourceFirstFusionChannel_fusionOK
    (cutoff left right : Nat) (rest : List Nat)
    (hlength : (left :: right :: rest).length ≤ 6)
    (source : EdgeLabelling)
    (hsource : source ∈ fusionWitnessesForSpins cutoff
      (left :: right :: rest)) :
    fusionOK left right (sourceFirstFusionChannel rest source) = true := by
  unfold fusionWitnessesForSpins at hsource
  obtain ⟨_, hallowed⟩ := List.mem_filter.mp hsource
  cases rest with
  | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd] at hallowed
      rw [canonicalAllowed_two] at hallowed
      have hparts := (Bool.and_eq_true _ _).mp hallowed
      have hzero : source 2 = 0 := of_decide_eq_true hparts.2
      simpa [sourceFirstFusionChannel, externalSpinsOfList, hzero] using
        hparts.1
  | cons third tail =>
      cases tail with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            Nat.reduceAdd] at hallowed
          rw [canonicalAllowed_three] at hallowed
          simpa [sourceFirstFusionChannel, externalSpinsOfList] using hallowed
      | cons fourth tail =>
          cases tail with
          | nil =>
              simp only [List.length_cons, List.length_nil, Nat.zero_add,
                Nat.reduceAdd] at hallowed
              rw [canonicalAllowed_four] at hallowed
              exact (Bool.and_eq_true _ _).mp hallowed |>.1
          | cons fifth tail =>
              cases tail with
              | nil =>
                  simp only [List.length_cons, List.length_nil, Nat.zero_add,
                    Nat.reduceAdd] at hallowed
                  rw [canonicalAllowed_five] at hallowed
                  exact (Bool.and_eq_true _ _).mp hallowed |>.1
              | cons sixth tail =>
                  cases tail with
                  | nil =>
                      simp only [List.length_cons, List.length_nil,
                        Nat.zero_add, Nat.reduceAdd] at hallowed
                      rw [canonicalAllowed_six] at hallowed
                      exact (Bool.and_eq_true _ _).mp hallowed |>.1
                  | cons seventh tail =>
                      simp only [List.length_cons] at hlength
                      have himpossible : False := by omega
                      exact False.elim himpossible

/-- If the actual first channel survives the even inward mate, the same
canonical auxiliary labelling is accepted over the mated ordered word.  The
statement keeps the external order fixed; it performs no face permutation. -/
theorem fusionWitnessForSpins_mem_evenInwardMate_of_first
    (cutoff left right : Nat) (rest : List Nat)
    (hlength : (left :: right :: rest).length ≤ 6)
    (source : EdgeLabelling)
    (hsource : source ∈ fusionWitnessesForSpins cutoff
      (left :: right :: rest))
    (htarget : fusionOK (evenInwardMateLabel left)
      (evenInwardMateLabel right)
      (sourceFirstFusionChannel rest source) = true) :
    source ∈ fusionWitnessesForSpins cutoff
      (evenInwardMateLabel left :: evenInwardMateLabel right :: rest) := by
  cases rest with
  | nil =>
      unfold fusionWitnessesForSpins at hsource ⊢
      simp only [List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd] at hsource ⊢
      obtain ⟨hbounded, hallowed⟩ := List.mem_filter.mp hsource
      rw [canonicalAllowed_two] at hallowed
      have hparts := (Bool.and_eq_true _ _).mp hallowed
      have hzero : source 2 = 0 := of_decide_eq_true hparts.2
      apply List.mem_filter.mpr
      refine ⟨hbounded, ?_⟩
      rw [canonicalAllowed_two]
      exact (Bool.and_eq_true _ _).mpr
        ⟨by simpa [sourceFirstFusionChannel, externalSpinsOfList, hzero]
            using htarget,
          decide_eq_true hzero⟩
  | cons third tail =>
      cases tail with
      | nil =>
          unfold fusionWitnessesForSpins at hsource ⊢
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            Nat.reduceAdd] at hsource ⊢
          apply List.mem_filter.mpr
          exact ⟨(List.mem_filter.mp hsource).1, by
            rw [canonicalAllowed_three]
            simpa [sourceFirstFusionChannel, externalSpinsOfList] using
              htarget⟩
      | cons fourth tail =>
          cases tail with
          | nil =>
              unfold fusionWitnessesForSpins at hsource ⊢
              simp only [List.length_cons, List.length_nil, Nat.zero_add,
                Nat.reduceAdd] at hsource ⊢
              obtain ⟨hbounded, hallowed⟩ := List.mem_filter.mp hsource
              rw [canonicalAllowed_four] at hallowed
              have hparts := (Bool.and_eq_true _ _).mp hallowed
              apply List.mem_filter.mpr
              refine ⟨hbounded, ?_⟩
              rw [canonicalAllowed_four]
              exact (Bool.and_eq_true _ _).mpr
                ⟨by simpa [sourceFirstFusionChannel,
                    externalSpinsOfList] using htarget,
                  hparts.2⟩
          | cons fifth tail =>
              cases tail with
              | nil =>
                  unfold fusionWitnessesForSpins at hsource ⊢
                  simp only [List.length_cons, List.length_nil,
                    Nat.zero_add, Nat.reduceAdd] at hsource ⊢
                  obtain ⟨hbounded, hallowed⟩ :=
                    List.mem_filter.mp hsource
                  rw [canonicalAllowed_five] at hallowed
                  have hparts := (Bool.and_eq_true _ _).mp hallowed
                  apply List.mem_filter.mpr
                  refine ⟨hbounded, ?_⟩
                  rw [canonicalAllowed_five]
                  exact (Bool.and_eq_true _ _).mpr
                    ⟨by simpa [sourceFirstFusionChannel,
                        externalSpinsOfList] using htarget,
                      hparts.2⟩
              | cons sixth tail =>
                  cases tail with
                  | nil =>
                      unfold fusionWitnessesForSpins at hsource ⊢
                      simp only [List.length_cons, List.length_nil,
                        Nat.zero_add, Nat.reduceAdd] at hsource ⊢
                      obtain ⟨hbounded, hallowed⟩ :=
                        List.mem_filter.mp hsource
                      rw [canonicalAllowed_six] at hallowed
                      have hparts := (Bool.and_eq_true _ _).mp hallowed
                      apply List.mem_filter.mpr
                      refine ⟨hbounded, ?_⟩
                      rw [canonicalAllowed_six]
                      exact (Bool.and_eq_true _ _).mpr
                        ⟨by simpa [sourceFirstFusionChannel,
                            externalSpinsOfList] using htarget,
                          hparts.2⟩
                  | cons seventh tail =>
                      simp only [List.length_cons] at hlength
                      have himpossible : False := by omega
                      exact False.elim himpossible

/-! ## 2. The drop remains an accepted collapsed witness -/

/-- An accepted root-first source witness with stretched first channel drops
to an accepted witness for the word with that first vertex contracted. -/
theorem stretchedFusionWitnessDrop_mem
    (cutoff left right : Nat) (rest : List Nat)
    (hlength : (left :: right :: rest).length ≤ 6)
    (source : EdgeLabelling)
    (hsource : source ∈ fusionWitnessesForSpins cutoff
      (left :: right :: rest))
    (hstretched : sourceFirstFusionChannel rest source = left + right) :
    stretchedFusionWitnessDrop rest source ∈
      fusionWitnessesForSpins cutoff ((left + right) :: rest) := by
  cases rest with
  | nil =>
      have hsum : left + right = 0 := by
        simpa [sourceFirstFusionChannel] using hstretched.symm
      have hleft : left = 0 := by omega
      have hright : right = 0 := by omega
      subst left
      subst right
      unfold fusionWitnessesForSpins
      simp only [List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd]
        at hsource ⊢
      apply List.mem_filter.mpr
      constructor
      · exact boundedEdgeLabellings_complete cutoff [1]
          zeroEdgeLabelling (by simp [zeroEdgeLabelling])
          (by simp [zeroEdgeLabelling])
      · rw [canonicalAllowed_one]
        simp [externalSpinsOfList, stretchedFusionWitnessDrop,
          zeroEdgeLabelling]
        decide
  | cons third tail =>
      cases tail with
      | nil =>
          have hthird : third = left + right := by
            simpa [sourceFirstFusionChannel] using hstretched
          subst third
          unfold fusionWitnessesForSpins
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            Nat.reduceAdd]
            at hsource ⊢
          apply List.mem_filter.mpr
          constructor
          · exact boundedEdgeLabellings_complete cutoff [2]
              zeroEdgeLabelling (by simp [zeroEdgeLabelling])
              (by simp [zeroEdgeLabelling])
          · rw [canonicalAllowed_two]
            simp [externalSpinsOfList, stretchedFusionWitnessDrop,
              zeroEdgeLabelling]
            exact
              (YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder
                (left + right) (left + right) 0).mpr
                ⟨left + right, by omega, by omega, by omega⟩
      | cons fourth tail =>
          cases tail with
          | nil =>
              unfold fusionWitnessesForSpins at hsource ⊢
              simp only [List.length_cons, List.length_nil, Nat.zero_add,
                Nat.reduceAdd]
                at hsource ⊢
              obtain ⟨_, hallowed⟩ := List.mem_filter.mp hsource
              rw [canonicalAllowed_four] at hallowed
              have hparts := (Bool.and_eq_true _ _).mp hallowed
              have hchannel : source 5 = left + right := by
                simpa [sourceFirstFusionChannel] using hstretched
              rw [hchannel] at hparts
              have htail : fusionOK (left + right) third fourth = true := by
                simpa [externalSpinsOfList] using hparts.2
              apply List.mem_filter.mpr
              constructor
              · exact boundedEdgeLabellings_complete cutoff []
                  zeroEdgeLabelling (by simp) (by simp [zeroEdgeLabelling])
              · rw [canonicalAllowed_three]
                simpa [externalSpinsOfList] using htail
          | cons fifth tail =>
              cases tail with
              | nil =>
                  unfold fusionWitnessesForSpins at hsource ⊢
                  simp only [List.length_cons, List.length_nil, Nat.zero_add,
                    Nat.reduceAdd]
                    at hsource ⊢
                  obtain ⟨hbounded, hallowed⟩ :=
                    List.mem_filter.mp hsource
                  rw [canonicalAllowed_five] at hallowed
                  have hparts := (Bool.and_eq_true _ _).mp hallowed
                  have hchannel : source 6 = left + right := by
                    simpa [sourceFirstFusionChannel] using hstretched
                  rw [hchannel] at hparts
                  have hsourceSeven : source 7 < cutoff + 1 :=
                    (boundedEdgeLabellings_sound cutoff [6, 7]
                      source hbounded).1 7 (by simp)
                  apply List.mem_filter.mpr
                  constructor
                  · apply boundedEdgeLabellings_complete
                    · intro edge hedge
                      change edge ∈ [5] at hedge
                      simp only [List.mem_singleton] at hedge
                      subst edge
                      simpa [stretchedFusionWitnessDrop, setEdgeLabel] using
                        hsourceSeven
                    · intro edge hedge
                      change edge ∉ [5] at hedge
                      have hne : edge ≠ 5 := by
                        intro heq
                        subst edge
                        exact hedge (by simp)
                      simp [stretchedFusionWitnessDrop, setEdgeLabel,
                        zeroEdgeLabelling, hne]
                  · rw [canonicalAllowed_four]
                    have htail :
                        fusionOK (left + right) third (source 7) = true ∧
                          fusionOK (source 7) fourth fifth = true := by
                      simpa [sourceFirstFusionChannel,
                        externalSpinsOfList] using hparts.2
                    simpa [externalSpinsOfList,
                      stretchedFusionWitnessDrop, setEdgeLabel,
                      htail.1, htail.2]
              | cons sixth tail =>
                  cases tail with
                  | nil =>
                      unfold fusionWitnessesForSpins at hsource ⊢
                      simp only [List.length_cons, List.length_nil,
                        Nat.zero_add, Nat.reduceAdd] at hsource ⊢
                      obtain ⟨hbounded, hallowed⟩ :=
                        List.mem_filter.mp hsource
                      rw [canonicalAllowed_six] at hallowed
                      have hparts := (Bool.and_eq_true _ _).mp hallowed
                      have hchannel : source 7 = left + right := by
                        simpa [sourceFirstFusionChannel] using hstretched
                      rw [hchannel] at hparts
                      have hsourceSound :=
                        (boundedEdgeLabellings_sound cutoff [7, 8, 9]
                          source hbounded).1
                      have hsourceEight := hsourceSound 8 (by simp)
                      have hsourceNine := hsourceSound 9 (by simp)
                      apply List.mem_filter.mpr
                      constructor
                      · apply boundedEdgeLabellings_complete
                        · intro edge hedge
                          change edge ∈ [6, 7] at hedge
                          simp only [List.mem_cons, List.not_mem_nil,
                            or_false] at hedge
                          rcases hedge with rfl | rfl
                          · simpa [stretchedFusionWitnessDrop,
                              setEdgeLabel] using hsourceEight
                          · simpa [stretchedFusionWitnessDrop,
                              setEdgeLabel] using hsourceNine
                        · intro edge hedge
                          change edge ∉ [6, 7] at hedge
                          have hneSix : edge ≠ 6 := by
                            intro heq
                            subst edge
                            exact hedge (by simp)
                          have hneSeven : edge ≠ 7 := by
                            intro heq
                            subst edge
                            exact hedge (by simp)
                          simp [stretchedFusionWitnessDrop, setEdgeLabel,
                            zeroEdgeLabelling, hneSix, hneSeven]
                      · rw [canonicalAllowed_five]
                        have htail :
                            fusionOK (left + right) third (source 8) = true ∧
                              fusionOK (source 8) fourth (source 9) = true ∧
                              fusionOK (source 9) fifth sixth = true := by
                          simpa [sourceFirstFusionChannel,
                            externalSpinsOfList] using hparts.2
                        simpa [externalSpinsOfList,
                          stretchedFusionWitnessDrop, setEdgeLabel,
                          htail.1, htail.2.1, htail.2.2]
                  | cons seventh tail =>
                      simp only [List.length_cons] at hlength
                      have himpossible : False := by omega
                      exact False.elim himpossible

/-! ## 3. Exact inverse on the stretched branch -/

/-- On an accepted source whose first channel is stretched, deleting and
reinserting the first vertex recovers the complete finitely supported
auxiliary labelling. -/
theorem stretchedFusionWitnessLift_drop
    (cutoff left right : Nat) (rest : List Nat)
    (hlength : (left :: right :: rest).length ≤ 6)
    (source : EdgeLabelling)
    (hsource : source ∈ fusionWitnessesForSpins cutoff
      (left :: right :: rest))
    (hstretched : sourceFirstFusionChannel rest source = left + right) :
    stretchedFusionWitnessLift left right rest
        (stretchedFusionWitnessDrop rest source) = source := by
  unfold fusionWitnessesForSpins at hsource
  obtain ⟨hbounded, hallowed⟩ := List.mem_filter.mp hsource
  have hsound := boundedEdgeLabellings_sound cutoff
    (canonicalUsedAuxiliaryCoordinates
      (left :: right :: rest).length) source hbounded
  funext edge
  cases rest with
  | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd]
        at hsound hallowed
      rw [canonicalAllowed_two] at hallowed
      have hsourceTwo : source 2 = 0 := by
        simp [externalSpinsOfList] at hallowed
        simpa using hallowed.2
      by_cases hedge : edge = 2
      · subst edge
        simpa [stretchedFusionWitnessLift, stretchedFusionWitnessDrop,
          zeroEdgeLabelling] using hsourceTwo.symm
      · have hzero := hsound.2 edge (by
          simpa [canonicalUsedAuxiliaryCoordinates,
            canonicalUsedCoordinates, hedge])
        simpa [stretchedFusionWitnessLift, stretchedFusionWitnessDrop,
          zeroEdgeLabelling] using hzero.symm
  | cons third tail =>
      cases tail with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            Nat.reduceAdd] at hsound
          have hzero := hsound.2 edge (by
            simp [canonicalUsedAuxiliaryCoordinates,
              canonicalUsedCoordinates])
          simpa [stretchedFusionWitnessLift, stretchedFusionWitnessDrop,
            zeroEdgeLabelling] using hzero.symm
      | cons fourth tail =>
          cases tail with
          | nil =>
              by_cases hedge : edge = 5
              · subst edge
                simpa [sourceFirstFusionChannel,
                  stretchedFusionWitnessLift, stretchedFusionWitnessDrop,
                  setEdgeLabel] using hstretched.symm
              · have hzero := hsound.2 edge (by
                  simpa [canonicalUsedAuxiliaryCoordinates,
                    canonicalUsedCoordinates, hedge])
                simpa [stretchedFusionWitnessLift,
                  stretchedFusionWitnessDrop, setEdgeLabel,
                  zeroEdgeLabelling, hedge] using hzero.symm
          | cons fifth tail =>
              cases tail with
              | nil =>
                  by_cases hsix : edge = 6
                  · subst edge
                    simpa [sourceFirstFusionChannel,
                      stretchedFusionWitnessLift,
                      stretchedFusionWitnessDrop, setEdgeLabel] using
                        hstretched.symm
                  · by_cases hseven : edge = 7
                    · subst edge
                      simp [stretchedFusionWitnessLift,
                        stretchedFusionWitnessDrop, setEdgeLabel, hsix]
                    · have hzero := hsound.2 edge (by
                        simpa [canonicalUsedAuxiliaryCoordinates,
                          canonicalUsedCoordinates, hsix, hseven])
                      simpa [stretchedFusionWitnessLift,
                        stretchedFusionWitnessDrop, setEdgeLabel,
                        zeroEdgeLabelling, hsix, hseven] using hzero.symm
              | cons sixth tail =>
                  cases tail with
                  | nil =>
                      by_cases hseven : edge = 7
                      · subst edge
                        simpa [sourceFirstFusionChannel,
                          stretchedFusionWitnessLift,
                          stretchedFusionWitnessDrop, setEdgeLabel] using
                            hstretched.symm
                      · by_cases height : edge = 8
                        · subst edge
                          simp [stretchedFusionWitnessLift,
                            stretchedFusionWitnessDrop, setEdgeLabel,
                            hseven]
                        · by_cases hnine : edge = 9
                          · subst edge
                            simp [stretchedFusionWitnessLift,
                              stretchedFusionWitnessDrop, setEdgeLabel,
                              hseven, height]
                          · have hzero := hsound.2 edge (by
                              simpa [canonicalUsedAuxiliaryCoordinates,
                                canonicalUsedCoordinates, hseven, height,
                                hnine])
                            simpa [stretchedFusionWitnessLift,
                              stretchedFusionWitnessDrop, setEdgeLabel,
                              zeroEdgeLabelling, hseven, height, hnine] using
                                hzero.symm
                  | cons seventh tail =>
                      simp only [List.length_cons] at hlength
                      have himpossible : False := by omega
                      exact False.elim himpossible

/-! ## 4. The injective `mate + stretched` witness partition -/

/-- Data retained on the stretched branch of the local partition.  Positivity
is kept with the collapsed accepted witness because it is precisely the gate
needed by the global active-debt strand root. -/
structure InwardMateStretchedFusionWitnessDebt
    (cutoff left right : Nat) (rest : List Nat) where
  left_pos : 0 < left
  right_pos : 0 < right
  collapsed : EdgeLabelling
  collapsed_mem : collapsed ∈ fusionWitnessesForSpins cutoff
    ((left + right) :: rest)

/-- Classify one accepted source witness by its actual first channel.  The
surviving branch retains the same auxiliary in the mated fiber; the unique
failing branch contracts the stretched first vertex and retains both
positivity witnesses. -/
def inwardMateFusionWitnessPartition
    (cutoff left right : Nat) (rest : List Nat)
    (hlength : (left :: right :: rest).length ≤ 6)
    (source : { auxiliary : EdgeLabelling //
      auxiliary ∈ fusionWitnessesForSpins cutoff
        (left :: right :: rest) }) :
    Sum
      { auxiliary : EdgeLabelling //
        auxiliary ∈ fusionWitnessesForSpins cutoff
          (evenInwardMateLabel left ::
            evenInwardMateLabel right :: rest) }
      (InwardMateStretchedFusionWitnessDebt
        cutoff left right rest) :=
  if htarget : fusionOK (evenInwardMateLabel left)
      (evenInwardMateLabel right)
      (sourceFirstFusionChannel rest source.1) = true then
    Sum.inl ⟨source.1,
      fusionWitnessForSpins_mem_evenInwardMate_of_first
        cutoff left right rest hlength source.1 source.2 htarget⟩
  else
    let hsourceFirst := sourceFirstFusionChannel_fusionOK
      cutoff left right rest hlength source.1 source.2
    let hdebt := fusionOK_evenInwardMate_or_positive_stretched
      left right (sourceFirstFusionChannel rest source.1) hsourceFirst
    let hpositive : 0 < left ∧ 0 < right ∧
        sourceFirstFusionChannel rest source.1 = left + right :=
      match hdebt with
      | Or.inl hsurvives => False.elim (htarget hsurvives)
      | Or.inr hstretched => hstretched
    Sum.inr
      { left_pos := hpositive.1
        right_pos := hpositive.2.1
        collapsed := stretchedFusionWitnessDrop rest source.1
        collapsed_mem := stretchedFusionWitnessDrop_mem
          cutoff left right rest hlength source.1 source.2 hpositive.2.2 }

/-- Decode either branch back into the source-coordinate space.  The target
branch already uses the same coordinates; the debt branch reinserts its
forced stretched first channel.  Only the branch carrier types depend on the
cutoff; the recovered auxiliary formula does not. -/
def recoverInwardMateFusionWitnessPartitionAt
    (cutoff left right : Nat) (rest : List Nat) :
    Sum
      { auxiliary : EdgeLabelling //
        auxiliary ∈ fusionWitnessesForSpins cutoff
          (evenInwardMateLabel left ::
            evenInwardMateLabel right :: rest) }
      (InwardMateStretchedFusionWitnessDebt cutoff left right rest) →
      EdgeLabelling
  | Sum.inl target => target.1
  | Sum.inr debt =>
      stretchedFusionWitnessLift left right rest debt.collapsed

theorem recoverInwardMateFusionWitnessPartitionAt_apply
    (cutoff left right : Nat) (rest : List Nat)
    (hlength : (left :: right :: rest).length ≤ 6)
    (source : { auxiliary : EdgeLabelling //
      auxiliary ∈ fusionWitnessesForSpins cutoff
        (left :: right :: rest) }) :
    recoverInwardMateFusionWitnessPartitionAt cutoff left right rest
        (inwardMateFusionWitnessPartition
          cutoff left right rest hlength source) =
      source.1 := by
  by_cases htarget : fusionOK (evenInwardMateLabel left)
      (evenInwardMateLabel right)
      (sourceFirstFusionChannel rest source.1) = true
  · simp [inwardMateFusionWitnessPartition, htarget,
      recoverInwardMateFusionWitnessPartitionAt]
  · have hsourceFirst := sourceFirstFusionChannel_fusionOK
      cutoff left right rest hlength source.1 source.2
    have hdebt := fusionOK_evenInwardMate_or_positive_stretched
      left right (sourceFirstFusionChannel rest source.1) hsourceFirst
    have hstretched :
        sourceFirstFusionChannel rest source.1 = left + right := by
      rcases hdebt with hsurvives | hdebt
      · exact False.elim (htarget hsurvives)
      · exact hdebt.2.2
    simpa [inwardMateFusionWitnessPartition, htarget,
      recoverInwardMateFusionWitnessPartitionAt] using
        (stretchedFusionWitnessLift_drop cutoff left right rest hlength
          source.1 source.2 hstretched)

/-- **Multiplicity-faithful local compiler.**  Two accepted ordered source
witnesses with the same classified output were equal already.  Thus the
partition loses no source multiplicity before the twelve-link product is
formed. -/
theorem inwardMateFusionWitnessPartition_injective
    (cutoff left right : Nat) (rest : List Nat)
    (hlength : (left :: right :: rest).length ≤ 6) :
    Function.Injective
      (inwardMateFusionWitnessPartition
        cutoff left right rest hlength) := by
  intro source₁ source₂ heq
  apply Subtype.ext
  calc
    source₁.1 =
        recoverInwardMateFusionWitnessPartitionAt cutoff left right rest
          (inwardMateFusionWitnessPartition
            cutoff left right rest hlength source₁) :=
      (recoverInwardMateFusionWitnessPartitionAt_apply
        cutoff left right rest hlength source₁).symm
    _ = recoverInwardMateFusionWitnessPartitionAt cutoff left right rest
          (inwardMateFusionWitnessPartition
            cutoff left right rest hlength source₂) :=
      congrArg
        (recoverInwardMateFusionWitnessPartitionAt
          cutoff left right rest) heq
    _ = source₂.1 :=
      recoverInwardMateFusionWitnessPartitionAt_apply
        cutoff left right rest hlength source₂

end YMGap.Continuum.SU2InwardMateFusionWitnessPartition

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.SU2InwardMateFusionWitnessPartition.sourceFirstFusionChannel
#print axioms
  YMGap.Continuum.SU2InwardMateFusionWitnessPartition.stretchedFusionWitnessDrop
#print axioms
  YMGap.Continuum.SU2InwardMateFusionWitnessPartition.stretchedFusionWitnessDrop_mem
#print axioms
  YMGap.Continuum.SU2InwardMateFusionWitnessPartition.stretchedFusionWitnessLift_drop
#print axioms
  YMGap.Continuum.SU2InwardMateFusionWitnessPartition.inwardMateFusionWitnessPartition
#print axioms
  YMGap.Continuum.SU2InwardMateFusionWitnessPartition.recoverInwardMateFusionWitnessPartitionAt_apply
#print axioms
  YMGap.Continuum.SU2InwardMateFusionWitnessPartition.inwardMateFusionWitnessPartition_injective
