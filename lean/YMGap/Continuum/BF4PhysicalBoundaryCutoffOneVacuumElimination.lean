/-
# Exact cutoff-one contraction of the BF4 vacuum boundary row

At central half-extent zero the fixed interface has 24 binary face labels.
This module gives a proof-carrying finite-CSP contraction of the genuine
production half amplitude with vacuum lower source.

The geometry certificate lists one lower link for every fixed face.  Lean
checks that the selected link is incident to that fixed face and otherwise
only to lower faces.  Hence a nonzero binary fixed label makes the selected
link's total incident spin odd, so the exact SU(2) fusion multiplicity is
zero.  The all-zero boundary has amplitude one.  The row is therefore the
Boolean vacuum delta, whose 24-coordinate variable-elimination trace has
constant width one and exact total mass one.

The displayed links may be proposed by an external exact-arithmetic search,
but all incidence, parity, fusion, and elimination equations are checked by
the Lean kernel.  This is a finite `K = 1`, half-extent-zero theorem only; it
does not provide a cutoff-uniform, volume-uniform, or continuum estimate.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryFactorGraph
import YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
import YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalBoundaryFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryVariableElimination
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteVariableEliminationCertificate
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The finite forcing cover -/

/-- One exact lower-link witness for each of the 24 fixed faces.  The order of
the pairs agrees with `centralFixedFaceIds 0`. -/
def cutoffOneVacuumForcingPairs : List (Nat × Z4Link) :=
  [(2,  ((0, 0, 0, 0), .x0)),
   (4,  ((0, 0, 0, 0), .x1)),
   (5,  ((0, 0, 0, 0), .x2)),
   (11, ((0, 0, 1, 0), .x0)),
   (13, ((0, 0, 1, 0), .x1)),
   (14, ((0, 0, 1, 0), .x2)),
   (20, ((0, 1, 0, 0), .x0)),
   (22, ((0, 1, 0, 0), .x1)),
   (23, ((0, 1, 0, 0), .x2)),
   (29, ((0, 1, 1, 0), .x0)),
   (31, ((0, 1, 1, 0), .x1)),
   (32, ((0, 1, 1, 0), .x2)),
   (38, ((1, 0, 0, 0), .x0)),
   (40, ((1, 0, 0, 0), .x1)),
   (41, ((1, 0, 0, 0), .x2)),
   (47, ((1, 0, 1, 0), .x0)),
   (49, ((1, 0, 1, 0), .x1)),
   (50, ((1, 0, 1, 0), .x2)),
   (56, ((1, 1, 0, 0), .x0)),
   (58, ((1, 1, 0, 0), .x1)),
   (59, ((1, 1, 0, 0), .x2)),
   (65, ((1, 1, 1, 0), .x0)),
   (67, ((1, 1, 1, 0), .x1)),
   (68, ((1, 1, 1, 0), .x2))]

/-- The proposed cover names every fixed face exactly in production order. -/
theorem cutoffOneVacuumForcingPairs_faces :
    cutoffOneVacuumForcingPairs.map Prod.fst =
      centralFixedFaceIds 0 := by
  decide

/-- Boolean-checkable validity of one forcing-cover entry. -/
def cutoffOneVacuumForcingPairValid (pair : Nat × Z4Link) : Bool :=
  decide (pair.2 ∈ centralLowerLinks 0) &&
    decide (pair.1 ∈ slabIncidentPlaqIds 1 pair.2) &&
      (slabIncidentPlaqIds 1 pair.2).all
        (fun other =>
          decide (other = pair.1 ∨ other ∈ centralLowerFaceIds 0))

/-- Kernel evaluation of the complete 24-entry geometric forcing cover. -/
theorem cutoffOneVacuumForcingPairs_checked :
    cutoffOneVacuumForcingPairs.all
      cutoffOneVacuumForcingPairValid = true := by
  decide

/-- Executable lookup of the link proposed for one fixed face. -/
def cutoffOneVacuumForcingLink (id : Nat) : Z4Link :=
  (((cutoffOneVacuumForcingPairs.find?
      (fun pair => decide (pair.1 = id))).map Prod.snd).getD
    ((0, 0, 0, 0), .x0))

/-- The lookup table satisfies the forcing condition on every production
fixed-face identifier. -/
theorem cutoffOneVacuumForcingLinks_checked :
    (centralFixedFaceIds 0).all
      (fun id =>
        decide (cutoffOneVacuumForcingLink id ∈ centralLowerLinks 0) &&
          decide (id ∈ slabIncidentPlaqIds 1
            (cutoffOneVacuumForcingLink id)) &&
            (slabIncidentPlaqIds 1
              (cutoffOneVacuumForcingLink id)).all
              (fun other =>
                decide
                  (other = id ∨ other ∈ centralLowerFaceIds 0))) = true := by
  decide

/-- Type-level witness extracted from the checked finite cover. -/
structure CutoffOneVacuumForcingWitness (id : Nat) : Type where
  link : Z4Link
  link_mem : link ∈ centralLowerLinks 0
  id_mem : id ∈ slabIncidentPlaqIds 1 link
  incident_support :
    ∀ other, other ∈ slabIncidentPlaqIds 1 link →
      other = id ∨ other ∈ centralLowerFaceIds 0

/-- Every fixed face constructively receives its checked forcing link. -/
def cutoffOneVacuumForcingWitness
    (id : Nat) (hid : id ∈ centralFixedFaceIds 0) :
    CutoffOneVacuumForcingWitness id := by
  have hvalid := List.all_eq_true.mp
    cutoffOneVacuumForcingLinks_checked id hid
  have hparts :
      (decide (cutoffOneVacuumForcingLink id ∈ centralLowerLinks 0) = true ∧
        decide (id ∈ slabIncidentPlaqIds 1
          (cutoffOneVacuumForcingLink id)) = true) ∧
        (slabIncidentPlaqIds 1
          (cutoffOneVacuumForcingLink id)).all
          (fun other =>
            decide (other = id ∨ other ∈ centralLowerFaceIds 0)) = true := by
    simpa only [Bool.and_eq_true] using hvalid
  refine
    { link := cutoffOneVacuumForcingLink id
      link_mem := of_decide_eq_true hparts.1.1
      id_mem := of_decide_eq_true hparts.1.2
      incident_support := ?_ }
  intro other hother
  exact of_decide_eq_true
    (List.all_eq_true.mp hparts.2 other hother)

/-! ## 2. Local odd-parity annihilation -/

theorem natListSum_map_zero_of
    (value : Nat → Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → value id = 0) →
      natListSum (ids.map value) = 0
  | [], _ => rfl
  | head :: tail, hvalue => by
      simp only [List.map_cons, natListSum,
        hvalue head List.mem_cons_self,
        natListSum_map_zero_of value tail
          (fun id hid => hvalue id (List.mem_cons_of_mem head hid)),
        Nat.zero_add]

theorem natListSum_map_unique_one
    (value : Nat → Nat) : ∀ (ids : List Nat) (selected : Nat),
    ids.Nodup → selected ∈ ids → value selected = 1 →
      (∀ id, id ∈ ids → id ≠ selected → value id = 0) →
        natListSum (ids.map value) = 1
  | [], selected, _, hmem, _, _ => absurd hmem List.not_mem_nil
  | head :: tail, selected, hnodup, hmem, hone, hzero => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [List.map_cons, natListSum, hone]
        have htailZero : natListSum (tail.map value) = 0 :=
          natListSum_map_zero_of value tail (fun id hid =>
            hzero id (List.mem_cons_of_mem selected hid)
              (fun heq => hparts.1 (heq ▸ hid)))
        rw [htailZero, Nat.add_zero]
      · have hheadNe : head ≠ selected := by
          intro heq
          subst head
          exact hparts.1 htail
        rw [List.map_cons, natListSum,
          hzero head List.mem_cons_self hheadNe,
          Nat.zero_add]
        exact natListSum_map_unique_one value tail selected hparts.2
          htail hone
          (fun id hid hne =>
            hzero id (List.mem_cons_of_mem head hid) hne)

theorem localExternalSpinSum_externalSpinsOfList
    (spins : List Nat) :
    localExternalSpinSum spins.length (externalSpinsOfList spins) =
      natListSum spins := by
  induction spins with
  | nil => rfl
  | cons head tail ih =>
      change
        natListSum
            ((List.range (tail.length + 1)).map
              (externalSpinsOfList (head :: tail))) =
          natListSum (head :: tail)
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, natListSum, List.map_map]
      change head +
          natListSum
            ((List.range tail.length).map
              (externalSpinsOfList tail)) =
        head + natListSum tail
      unfold localExternalSpinSum at ih
      rw [ih]

private theorem cutoffOneVacuum_forcingLinkMultiplicity_zero
    (boundary : EdgeLabelling)
    (id : Nat) (hid : id ∈ centralFixedFaceIds 0)
    (hidOne : boundary id = 1) :
    let witness := cutoffOneVacuumForcingWitness id hid
    slabExplicitLinkMultiplicity 1 1
      (assembleReflectedSlabLabelling 0
        zeroEdgeLabelling boundary zeroEdgeLabelling)
      witness.link = 0 := by
  dsimp only
  let witness := cutoffOneVacuumForcingWitness id hid
  let physical := assembleReflectedSlabLabelling 0
    zeroEdgeLabelling boundary zeroEdgeLabelling
  let spins := (slabIncidentPlaqIds 1 witness.link).map physical
  have hphysicalSelected : physical id = 1 := by
    unfold physical
    have hparts := mem_centralFixedFaceIds.mp hid
    rw [assembleReflectedSlabLabelling_fixed hparts.1 hparts.2]
    exact hidOne
  have hphysicalOther :
      ∀ other, other ∈ slabIncidentPlaqIds 1 witness.link →
        other ≠ id → physical other = 0 := by
    intro other hother hne
    have hsupport := witness.incident_support other hother
    rcases hsupport with heq | hlower
    · exact False.elim (hne heq)
    · unfold physical
      have hparts := mem_centralLowerFaceIds.mp hlower
      rw [assembleReflectedSlabLabelling_lower hparts.1 hparts.2]
      rfl
  have hsum : natListSum spins = 1 := by
    unfold spins
    exact natListSum_map_unique_one physical
      (slabIncidentPlaqIds 1 witness.link) id
      (slabIncidentPlaqIds_nodup 1 witness.link)
      witness.id_mem hphysicalSelected hphysicalOther
  unfold slabExplicitLinkMultiplicity
  change
    explicitValenceMultiplicity (linkAuxiliaryCutoff 1)
      spins.length (externalSpinsOfList spins) = 0
  apply explicitValenceMultiplicity_eq_zero_of_odd_sum
  · unfold spins
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 witness.link
  · rw [localExternalSpinSum_externalSpinsOfList spins, hsum]

theorem natListProduct_eq_zero_of_member {A : Type}
    (value : A → Nat) : ∀ (items : List A) {item : A},
    item ∈ items → value item = 0 →
      natListProduct value items = 0
  | [], _, hmem, _ => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem, hzero => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp [natListProduct, hzero]
      · rw [natListProduct,
          natListProduct_eq_zero_of_member value tail htail hzero,
          Nat.mul_zero]

theorem centralHalfAmplitude_cutoffOne_vacuum_eqv_zero_of_fixed_one
    (w : Q') (boundary : EdgeLabelling)
    (id : Nat) (hid : id ∈ centralFixedFaceIds 0)
    (hidOne : boundary id = 1) :
    centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary ≈ 0 := by
  let witness := cutoffOneVacuumForcingWitness id hid
  let physical := assembleReflectedSlabLabelling 0
    zeroEdgeLabelling boundary zeroEdgeLabelling
  have hlink :
      slabExplicitLinkMultiplicity 1 1 physical witness.link = 0 := by
    exact cutoffOneVacuum_forcingLinkMultiplicity_zero
      boundary id hid hidOne
  have hproduct :
      slabLinkMultiplicityProductOn 1 1 physical
        (centralLowerLinks 0) = 0 := by
    unfold slabLinkMultiplicityProductOn
    exact natListProduct_eq_zero_of_member
      (slabExplicitLinkMultiplicity 1 1 physical)
      (centralLowerLinks 0) witness.link_mem hlink
  unfold centralHalfAmplitude centralLowerFactor
  change
    slabFaceFactorOn w 1 physical (centralLowerFaceIds 0) *
      Q'.ofNat
        (slabLinkMultiplicityProductOn 1 1 physical
          (centralLowerLinks 0)) ≈ 0
  rw [hproduct]
  exact Q'.eqv_trans _
    (slabFaceFactorOn w 1 physical (centralLowerFaceIds 0) * 0) _
    (Q'.mul_eqv_congr_left _ _ _ Q'.ofNat_zero_eqv)
    (Q'.mul_zero_eqv _)

/-! ## 3. Vacuum value and Boolean word semantics -/

private theorem assembleReflectedSlabLabelling_zero :
    assembleReflectedSlabLabelling 0 zeroEdgeLabelling
        zeroEdgeLabelling zeroEdgeLabelling =
      zeroEdgeLabelling := by
  funext id
  by_cases hid : id ∈ slabPhysicalFaceEdges (centralExtent 0)
  · unfold assembleReflectedSlabLabelling
    rw [if_pos hid]
    generalize hside :
      plaquetteHalfSide 0 (slabPlaquetteAt (centralExtent 0) id) = side
    cases side <;> rfl
  · exact assembleReflectedSlabLabelling_zero_off_physical
      0 zeroEdgeLabelling zeroEdgeLabelling zeroEdgeLabelling hid

private theorem slabFaceFactorOn_zero_eqv_one
    (w : Q') (K : Nat) : ∀ ids : List Nat,
    slabFaceFactorOn w K zeroEdgeLabelling ids ≈ 1
  | [] => Q'.eqv_refl 1
  | _ :: tail => by
      change
        coeffAt (heatKernelPacket K w) 0 *
            slabFaceFactorOn w K zeroEdgeLabelling tail ≈ 1
      have hcoeff : coeffAt (heatKernelPacket K w) 0 ≈ 1 := by
        rw [coeffAt_heatKernelPacket (Nat.succ_pos K), coeffW_zero]
        exact Q'.eqv_refl 1
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hcoeff)
          (Q'.mul_eqv_congr_left _ _ _
            (slabFaceFactorOn_zero_eqv_one w K tail)))
        (Q'.one_mul_eqv 1)

private theorem slabLinkMultiplicityProductOn_zero_eq_one
    (K extent : Nat) : ∀ links : List Z4Link,
    slabLinkMultiplicityProductOn K extent zeroEdgeLabelling links = 1
  | [] => rfl
  | head :: tail => by
      change
        slabExplicitLinkMultiplicity K extent zeroEdgeLabelling head *
            slabLinkMultiplicityProductOn K extent zeroEdgeLabelling tail = 1
      rw [slabExplicitLinkMultiplicity_zero_eq_one,
        slabLinkMultiplicityProductOn_zero_eq_one K extent tail,
        Nat.one_mul]

theorem centralHalfAmplitude_cutoffOne_vacuum_vacuum_eqv_one
    (w : Q') :
    centralHalfAmplitude w 1 0 zeroEdgeLabelling zeroEdgeLabelling ≈ 1 := by
  unfold centralHalfAmplitude
  rw [assembleReflectedSlabLabelling_zero]
  unfold centralLowerFactor
  rw [slabLinkMultiplicityProductOn_zero_eq_one]
  exact Q'.eqv_trans _ (1 * Q'.ofNat 1) _
    (Q'.mul_eqv_congr_right _ _ _
      (slabFaceFactorOn_zero_eqv_one w 1 (centralLowerFaceIds 0)))
    (by decide)

/-- Boolean test for the unique all-vacuum word. -/
def binaryVacuumWordB : List Nat → Bool
  | [] => true
  | label :: labels =>
      decide (label = 0) && binaryVacuumWordB labels

/-- Rational delta supported on the all-vacuum word. -/
def binaryVacuumWordWeight (word : List Nat) : Q' :=
  if binaryVacuumWordB word then 1 else 0

theorem wordToEdgeLabelling_eq_zero_of_binaryVacuum :
    ∀ (edges word : List Nat), binaryVacuumWordB word = true →
      wordToEdgeLabelling edges word = zeroEdgeLabelling
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | edge :: rest, spin :: spins, hvacuum => by
      change
        (decide (spin = 0) && binaryVacuumWordB spins) = true at hvacuum
      have hparts :
          decide (spin = 0) = true ∧
            binaryVacuumWordB spins = true := by
        simpa only [Bool.and_eq_true] using hvacuum
      have hspin : spin = 0 := by
        exact of_decide_eq_true hparts.1
      have htail := wordToEdgeLabelling_eq_zero_of_binaryVacuum
        rest spins hparts.2
      rw [hspin, wordToEdgeLabelling, htail]
      funext id
      simp [setEdgeLabel, zeroEdgeLabelling]

theorem nonzeroDecodedOfNotBinaryVacuum
    (edges : List Nat) : ∀ word : List Nat,
      edges.length = word.length → edges.Nodup →
        binaryVacuumWordB word = false →
          ∃ id : Nat,
            id ∈ edges ∧ wordToEdgeLabelling edges word id ≠ 0 := by
  induction edges with
  | nil =>
    intro word hlength _hnodup hvacuum
    cases word with
    | nil => simp [binaryVacuumWordB] at hvacuum
    | cons _ tail =>
      change 0 = Nat.succ tail.length at hlength
      exact False.elim (Nat.noConfusion hlength)
  | cons edge rest ih =>
    intro word hlength hnodup hvacuum
    cases word with
    | nil =>
      change Nat.succ rest.length = 0 at hlength
      exact False.elim (Nat.noConfusion hlength)
    | cons spin spins =>
      have hrestLength : rest.length = spins.length := by
        simpa using Nat.succ.inj hlength
      have hnodupParts := List.nodup_cons.mp hnodup
      cases hspinDecision : decide (spin = 0) with
      | true =>
        have hspin : spin = 0 := of_decide_eq_true hspinDecision
        have htailVacuum : binaryVacuumWordB spins = false := by
          change (decide (spin = 0) &&
            binaryVacuumWordB spins) = false at hvacuum
          simp [hspin] at hvacuum
          exact hvacuum
        obtain ⟨id, hid, hvalue⟩ :=
          ih spins hrestLength hnodupParts.2 htailVacuum
        refine ⟨id, List.mem_cons_of_mem edge hid, ?_⟩
        have hne : id ≠ edge := by
          intro heq
          subst id
          exact hnodupParts.1 hid
        simpa [wordToEdgeLabelling, setEdgeLabel, hne] using hvalue
      | false =>
        have hspin : spin ≠ 0 := of_decide_eq_false hspinDecision
        refine ⟨edge, List.mem_cons_self, ?_⟩
        simpa [wordToEdgeLabelling, setEdgeLabel] using hspin

theorem mem_allSeqs_length
    (domainSize : Nat) : ∀ {variables : Nat} {word : List Nat},
    word ∈ allSeqs domainSize variables → word.length = variables
  | 0, word, hword => by
      change word ∈ [[]] at hword
      rw [List.mem_singleton.mp hword]
      rfl
  | variables + 1, word, hword => by
      change word ∈
        (List.range domainSize).flatMap
          (fun head =>
            (allSeqs domainSize variables).map
              (fun tail => head :: tail)) at hword
      obtain ⟨head, _hhead, hmapped⟩ := List.mem_flatMap.mp hword
      obtain ⟨tail, htail, heq⟩ := List.mem_map.mp hmapped
      rw [← heq, List.length_cons,
        mem_allSeqs_length domainSize htail]

theorem centralFixedFaceIds_zero_nodup :
    (centralFixedFaceIds 0).Nodup := by decide

theorem centralHalfAmplitude_cutoffOne_vacuum_word_eqv_delta
    (w : Q') (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    centralHalfAmplitude w 1 0 zeroEdgeLabelling
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      binaryVacuumWordWeight word := by
  cases hvacuum : binaryVacuumWordB word with
  | true =>
      rw [wordToEdgeLabelling_eq_zero_of_binaryVacuum
        (centralFixedFaceIds 0) word hvacuum]
      unfold binaryVacuumWordWeight
      rw [hvacuum]
      exact centralHalfAmplitude_cutoffOne_vacuum_vacuum_eqv_one w
  | false =>
      obtain ⟨id, hid, hnonzero⟩ :=
        nonzeroDecodedOfNotBinaryVacuum
          (centralFixedFaceIds 0) word
          (mem_allSeqs_length 2 hword).symm
          centralFixedFaceIds_zero_nodup hvacuum
      have hboundary :
          wordToEdgeLabelling (centralFixedFaceIds 0) word ∈
            centralBoundaryChannels 1 0 := by
        rw [centralBoundaryChannels_eq_map_allSeqs]
        exact List.mem_map.mpr ⟨word, hword, rfl⟩
      have hbound :=
        (boundedEdgeLabellings_sound 1 (centralFixedFaceIds 0)
          (wordToEdgeLabelling (centralFixedFaceIds 0) word)
          hboundary).1 id hid
      have hidOne :
          wordToEdgeLabelling (centralFixedFaceIds 0) word id = 1 := by
        omega
      unfold binaryVacuumWordWeight
      rw [hvacuum]
      exact centralHalfAmplitude_cutoffOne_vacuum_eqv_zero_of_fixed_one
        w (wordToEdgeLabelling (centralFixedFaceIds 0) word)
        id hid hidOne

/-! ## 4. Width-one exact elimination and physical row mass -/

theorem binaryVacuumWordWeight_eliminateHead
    (tail : List Nat) :
    eliminateHead 2 binaryVacuumWordWeight tail ≈
      binaryVacuumWordWeight tail := by
  unfold eliminateHead
  change
    binaryVacuumWordWeight (0 :: tail) +
        (binaryVacuumWordWeight (1 :: tail) + 0) ≈
      binaryVacuumWordWeight tail
  cases htail : binaryVacuumWordB tail <;>
    simp [binaryVacuumWordWeight, binaryVacuumWordB, htail] <;>
    decide

/-- A uniform exact trace for the Boolean vacuum delta.  Every stage table is
the same delta on the remaining tail, so eliminating a coordinate never
creates a scope larger than one. -/
def binaryVacuumEliminationCertificate (variables : Nat) :
    ExactVariableEliminationCertificate
      2 variables binaryVacuumWordWeight where
  table := fun _ word => binaryVacuumWordWeight word
  initial := fun _ _ => Q'.eqv_refl _
  step := fun _ _ tail _ =>
    binaryVacuumWordWeight_eliminateHead tail

/-- The physical cutoff-one vacuum row uses the generic width-one delta
trace, with its top-table semantics proved from the checked BF4 cover. -/
def cutoffOnePhysicalVacuumRowCertificate (w : Q') :
    ExactVariableEliminationCertificate
      2 (centralFixedFaceIds 0).length
      (fun word =>
        centralHalfAmplitude w 1 0 zeroEdgeLabelling
          (wordToEdgeLabelling (centralFixedFaceIds 0) word)) where
  table := (binaryVacuumEliminationCertificate
    (centralFixedFaceIds 0).length).table
  initial := fun assignment hassignment =>
    centralHalfAmplitude_cutoffOne_vacuum_word_eqv_delta
      w assignment hassignment
  step := (binaryVacuumEliminationCertificate
    (centralFixedFaceIds 0).length).step

/-- Exact mass one for the genuine one-sided physical BF4 half-amplitude row
at cutoff one, central half-extent zero, and vacuum lower source. -/
theorem centralHalfAmplitudeBoundaryRowMass_cutoffOne_vacuum_eqv_one
    (w : Q') :
    centralHalfAmplitudeBoundaryRowMass w 1 0 zeroEdgeLabelling ≈ 1 := by
  refine Q'.eqv_trans _
    ((cutoffOnePhysicalVacuumRowCertificate w).table 0 []) _
    (centralHalfAmplitudeBoundaryRowMass_eqv_certificateBottom
      (cutoffOnePhysicalVacuumRowCertificate w)) ?_
  change binaryVacuumWordWeight [] ≈ 1
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination.cutoffOneVacuumForcingPairs_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination.cutoffOneVacuumForcingWitness
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination.centralFixedFaceIds_zero_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination.centralHalfAmplitude_cutoffOne_vacuum_eqv_zero_of_fixed_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination.centralHalfAmplitude_cutoffOne_vacuum_vacuum_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination.centralHalfAmplitude_cutoffOne_vacuum_word_eqv_delta
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination.centralHalfAmplitudeBoundaryRowMass_cutoffOne_vacuum_eqv_one
