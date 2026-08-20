/-
# Exact ternary-delta vacuum boundary row at cutoff two

The cutoff-one vacuum-row proof used odd parity and therefore only handled the
nonzero doubled-spin label one.  At cutoff two the additional label two is
even.  The correct representation-theoretic statement is stronger: an
invariant tensor with exactly one non-vacuum external spin has multiplicity
zero.  We prove it constructively by deleting inserted vacuum spins from the
ordered fusion path and reducing to the exact one-valent multiplicity.

The checked 24-face forcing cover then shows that the genuine cutoff-two
vacuum half-amplitude is the ternary all-zero delta.  A width-one variable-
elimination certificate proves its complete boundary-row mass is one without
enumerating `3^24` words.

This is finite `K = 2`, half-extent-zero data at coupling `1/2`; it is not a
cutoff-uniform, volume-uniform, spectral-gap, or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior
import YMGap.Continuum.Z4FusionPathZeroInsertion

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumDeltaRow

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open scoped List
open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport
open YMGap.Continuum.BF4PhysicalBoundaryVariableElimination
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteVariableEliminationCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A single nonzero external spin cannot fuse to vacuum -/

private theorem nil_sublist (A : Type) : ∀ items : List A, [] <+ items
  | [] => List.Sublist.slnil
  | head :: tail => List.Sublist.cons head (nil_sublist A tail)

private theorem singleton_sublist_of_mem {A : Type} (item : A) :
    ∀ {items : List A}, item ∈ items → [item] <+ items
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst head
        exact List.Sublist.cons₂ item (nil_sublist A tail)
      · exact List.Sublist.cons head
          (singleton_sublist_of_mem item htail)

private theorem cutoffTwoVacuum_forcingLinkMultiplicity_zero
    (boundary : EdgeLabelling)
    (id : Nat) (hid : id ∈ centralFixedFaceIds 0)
    (hidNonzero : boundary id ≠ 0)
    (hidBound : boundary id ≤ 2) :
    let witness := cutoffOneVacuumForcingWitness id hid
    slabExplicitLinkMultiplicity 2 1
      (assembleReflectedSlabLabelling 0
        zeroEdgeLabelling boundary zeroEdgeLabelling)
      witness.link = 0 := by
  dsimp only
  let witness := cutoffOneVacuumForcingWitness id hid
  let physical := assembleReflectedSlabLabelling 0
    zeroEdgeLabelling boundary zeroEdgeLabelling
  let incidentIds := slabIncidentPlaqIds 1 witness.link
  let spins := incidentIds.map physical
  have hphysicalSelected : physical id = boundary id := by
    unfold physical
    have hparts := mem_centralFixedFaceIds.mp hid
    rw [assembleReflectedSlabLabelling_fixed hparts.1 hparts.2]
  have hphysicalOther :
      ∀ other, other ∈ incidentIds → other ≠ id →
        physical other = 0 := by
    intro other hother hne
    have hsupport := witness.incident_support other hother
    rcases hsupport with heq | hlower
    · exact False.elim (hne heq)
    · unfold physical
      have hparts := mem_centralLowerFaceIds.mp hlower
      rw [assembleReflectedSlabLabelling_lower hparts.1 hparts.2]
      rfl
  have hextension : ZeroExtension [boundary id] spins := by
    have hsub : [id] <+ incidentIds :=
      singleton_sublist_of_mem id witness.id_mem
    have hraw := ZeroExtension.map_of_sublist physical hsub
      (slabIncidentPlaqIds_nodup 1 witness.link)
      (fun other hother hnotSource =>
        hphysicalOther other hother (fun heq =>
          hnotSource (by subst other; simp)))
    simpa [spins, hphysicalSelected] using hraw
  have hincidentLength : spins.length ≤ 6 := by
    unfold spins incidentIds
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 witness.link
  have hsourceBounded :
      SpinsBounded (linkAuxiliaryCutoff 2) [boundary id] := by
    intro spin hspin
    have heq : spin = boundary id := List.mem_singleton.mp hspin
    rw [heq]
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  have hextensionMultiplicity :=
    explicitValenceMultiplicity_zeroExtension hextension
      (by simp : [boundary id].length ≤ 6)
      hincidentLength hsourceBounded
  have hsourceZero :
      explicitValenceMultiplicity (linkAuxiliaryCutoff 2)
          [boundary id].length
          (externalSpinsOfList [boundary id]) = 0 := by
    change oneValentMultiplicity (linkAuxiliaryCutoff 2) (boundary id) = 0
    rw [oneValentMultiplicity_eq_bool_zero]
    simp [boolMultiplicity, hidNonzero]
  unfold slabExplicitLinkMultiplicity
  change
    explicitValenceMultiplicity (linkAuxiliaryCutoff 2) spins.length
        (externalSpinsOfList spins) = 0
  exact Eq.trans hextensionMultiplicity.symm hsourceZero

/-- A nonzero cutoff-two fixed-interface label forces one lower-link
multiplicity, hence the complete vacuum-source half-amplitude, to zero. -/
theorem centralHalfAmplitude_cutoffTwo_vacuum_eqv_zero_of_fixed_nonzero
    (boundary : EdgeLabelling)
    (id : Nat) (hid : id ∈ centralFixedFaceIds 0)
    (hidNonzero : boundary id ≠ 0)
    (hidBound : boundary id ≤ 2) :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling boundary ≈ 0 := by
  let witness := cutoffOneVacuumForcingWitness id hid
  let physical := assembleReflectedSlabLabelling 0
    zeroEdgeLabelling boundary zeroEdgeLabelling
  have hlink :
      slabExplicitLinkMultiplicity 2 1 physical witness.link = 0 := by
    exact cutoffTwoVacuum_forcingLinkMultiplicity_zero
      boundary id hid hidNonzero hidBound
  have hproduct :
      slabLinkMultiplicityProductOn 2 1 physical
        (centralLowerLinks 0) = 0 := by
    unfold slabLinkMultiplicityProductOn
    exact natListProduct_eq_zero_of_member
      (slabExplicitLinkMultiplicity 2 1 physical)
      (centralLowerLinks 0) witness.link_mem hlink
  unfold centralHalfAmplitude centralLowerFactor
  change
    slabFaceFactorOn cutoffTwoHalfCoupling 2 physical
        (centralLowerFaceIds 0) *
      Q'.ofNat
        (slabLinkMultiplicityProductOn 2 1 physical
          (centralLowerLinks 0)) ≈ 0
  rw [hproduct]
  exact Q'.eqv_trans _
    (slabFaceFactorOn cutoffTwoHalfCoupling 2 physical
        (centralLowerFaceIds 0) * 0) _
    (Q'.mul_eqv_congr_left _ _ _ Q'.ofNat_zero_eqv)
    (Q'.mul_zero_eqv _)

/-! ## 2. Ternary all-zero word semantics -/

theorem centralHalfAmplitude_cutoffTwo_vacuum_word_eqv_delta
    (word : List Nat)
    (hword : word ∈ allSeqs 3 (centralFixedFaceIds 0).length) :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 zeroEdgeLabelling
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      binaryVacuumWordWeight word := by
  cases hvacuum : binaryVacuumWordB word with
  | true =>
      rw [wordToEdgeLabelling_eq_zero_of_binaryVacuum
        (centralFixedFaceIds 0) word hvacuum]
      unfold binaryVacuumWordWeight
      rw [hvacuum]
      exact centralHalfAmplitude_vacuum_eqv_one
        cutoffTwoHalfCoupling 2 0
  | false =>
      obtain ⟨id, hid, hnonzero⟩ :=
        nonzeroDecodedOfNotBinaryVacuum
          (centralFixedFaceIds 0) word
          (mem_allSeqs_length 3 hword).symm
          centralFixedFaceIds_zero_nodup hvacuum
      have hboundary :
          wordToEdgeLabelling (centralFixedFaceIds 0) word ∈
            centralBoundaryChannels 2 0 := by
        rw [centralBoundaryChannels_eq_map_allSeqs]
        exact List.mem_map.mpr ⟨word, hword, rfl⟩
      have hbound :=
        (boundedEdgeLabellings_sound 2 (centralFixedFaceIds 0)
          (wordToEdgeLabelling (centralFixedFaceIds 0) word)
          hboundary).1 id hid
      unfold binaryVacuumWordWeight
      rw [hvacuum]
      exact centralHalfAmplitude_cutoffTwo_vacuum_eqv_zero_of_fixed_nonzero
        (wordToEdgeLabelling (centralFixedFaceIds 0) word)
        id hid hnonzero (by omega)

/-! ## 3. Width-one ternary elimination certificate -/

private theorem ternaryVacuumWordWeight_eliminateHead
    (tail : List Nat) :
    eliminateHead 3 binaryVacuumWordWeight tail ≈
      binaryVacuumWordWeight tail := by
  unfold eliminateHead
  change
    binaryVacuumWordWeight (0 :: tail) +
      (binaryVacuumWordWeight (1 :: tail) +
        (binaryVacuumWordWeight (2 :: tail) + 0)) ≈
      binaryVacuumWordWeight tail
  cases htail : binaryVacuumWordB tail <;>
    simp [binaryVacuumWordWeight, binaryVacuumWordB, htail] <;>
    decide

/-- Proof-carrying ternary-delta contraction for the genuine cutoff-two
vacuum boundary row. -/
def cutoffTwoPhysicalVacuumRowCertificate :
    ExactVariableEliminationCertificate
      3 (centralFixedFaceIds 0).length
      (fun word =>
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          zeroEdgeLabelling
          (wordToEdgeLabelling (centralFixedFaceIds 0) word)) where
  table := fun _ word => binaryVacuumWordWeight word
  initial := fun assignment hassignment =>
    centralHalfAmplitude_cutoffTwo_vacuum_word_eqv_delta
      assignment hassignment
  step := fun _ _ tail _ =>
    ternaryVacuumWordWeight_eliminateHead tail

/-- The complete `3^24` physical vacuum half-amplitude boundary row has
exact mass one, certified by a width-one trace. -/
theorem centralHalfAmplitudeBoundaryRowMass_cutoffTwo_vacuum_eqv_one :
    centralHalfAmplitudeBoundaryRowMass cutoffTwoHalfCoupling
        2 0 zeroEdgeLabelling ≈ 1 := by
  refine Q'.eqv_trans _
    (cutoffTwoPhysicalVacuumRowCertificate.table 0 []) _
    (centralHalfAmplitudeBoundaryRowMass_eqv_certificateBottom
      cutoffTwoPhysicalVacuumRowCertificate) ?_
  change binaryVacuumWordWeight [] ≈ 1
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumDeltaRow

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumDeltaRow.centralHalfAmplitude_cutoffTwo_vacuum_eqv_zero_of_fixed_nonzero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumDeltaRow.centralHalfAmplitude_cutoffTwo_vacuum_word_eqv_delta
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumDeltaRow.centralHalfAmplitudeBoundaryRowMass_cutoffTwo_vacuum_eqv_one
