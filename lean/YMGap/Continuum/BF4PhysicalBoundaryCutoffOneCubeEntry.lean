/-
# Exact cutoff-one lower-cube boundary entry

The central six-face lower cube is the first explicit non-vacuum source in
the retained physical carrier.  This file evaluates its genuine one-sided
BF4 half amplitude at the vacuum boundary.  The answer is exactly the sixth
power of the fundamental heat-kernel coefficient.

This is one matrix entry, not yet a complete row contraction.  In
particular, no claim about other boundary coordinates, cutoff uniformity,
volume uniformity, or the continuum limit is made here.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CentralLowerCubeRowDomination
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumStatistics

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalBoundaryVariableElimination
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.FiniteVariableEliminationCertificate
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr_on
    (left right : Nat → Q') : ∀ ids : List Nat,
    (∀ id, id ∈ ids → left id ≈ right id) →
      eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _ => Q'.eqv_refl _
  | id :: rest, hagree =>
      qmul_congr
        (hagree id List.mem_cons_self)
        (eliminateLinks_congr_on left right rest
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem id hitem)))

private theorem eliminateLinks_indicator_pow
    (selected : List Nat) (coefficient : Q') : ∀ ids : List Nat,
    eliminateLinks
        (fun id => if id ∈ selected then coefficient else 1)
        ids ≈
      coefficient ^
        (ids.filter (fun id => decide (id ∈ selected))).length
  | [] => Q'.eqv_refl _
  | id :: rest => by
      by_cases hselected : id ∈ selected
      · simp only [eliminateLinks, hselected, if_pos,
          List.filter_cons, decide_true, List.length_cons, Q'.pow_succ]
        exact qmul_congr (Q'.eqv_refl _)
          (eliminateLinks_indicator_pow selected coefficient rest)
      · simp only [eliminateLinks, hselected,
          List.filter_cons, decide_false]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _
            (eliminateLinks_indicator_pow selected coefficient rest))
          (Q'.one_mul_eqv _)

/-! ## 1. Lower-face and lower-link evaluations -/

theorem centralLowerCube_lowerFaceFactor_eqv
    (w : Q') :
    slabFaceFactorOn w 1 centralLowerCubePhysical
        (centralLowerFaceIds 0) ≈
      (coeffW w 1) ^ 6 := by
  unfold slabFaceFactorOn
  have hcoefficient :
      eliminateLinks
          (fun id =>
            coeffAt (heatKernelPacket 1 w)
              (centralLowerCubePhysical id))
          (centralLowerFaceIds 0) ≈
        eliminateLinks
          (fun id =>
            if id ∈ centralLowerCubeFaceIds
            then coeffW w 1 else 1)
          (centralLowerFaceIds 0) := by
    apply eliminateLinks_congr_on
    intro id _
    rw [centralLowerCubePhysical_eq_componentLabel]
    by_cases hcube : id ∈ centralLowerCubeFaceIds
    · rw [componentLabel_eq_one_iff.mpr hcube,
        coeffAt_heatKernelPacket (by decide), if_pos hcube]
      exact Q'.eqv_refl _
    · rw [componentLabel_eq_zero_of_not_mem hcube,
        coeffAt_heatKernelPacket (by decide), coeffW_zero, if_neg hcube]
      exact Q'.eqv_refl _
  have hpower :=
    eliminateLinks_indicator_pow
      centralLowerCubeFaceIds (coeffW w 1)
      (centralLowerFaceIds 0)
  have hcount :
      ((centralLowerFaceIds 0).filter
        (fun id => decide (id ∈ centralLowerCubeFaceIds))).length = 6 := by
    decide
  rw [hcount] at hpower
  exact Q'.eqv_trans _ _ _ hcoefficient hpower

theorem centralLowerCube_lowerLinkMultiplicityProduct_one :
    slabLinkMultiplicityProductOn 1 (centralExtent 0) centralLowerCubePhysical
        (centralLowerLinks 0) = 1 := by
  rfl

/-! ## 2. The first exact non-vacuum half-amplitude entry -/

/-- The genuine cutoff-one lower-cube/vacuum boundary entry. -/
theorem centralHalfAmplitude_cutoffOne_cube_vacuum_eqv
    (w : Q') :
    centralHalfAmplitude w 1 0
        centralLowerCubeState zeroEdgeLabelling ≈
      (coeffW w 1) ^ 6 := by
  unfold centralHalfAmplitude
  change centralLowerFactor w 1 0 centralLowerCubePhysical ≈
    (coeffW w 1) ^ 6
  unfold centralLowerFactor
  rw [centralLowerCube_lowerLinkMultiplicityProduct_one]
  refine Q'.eqv_trans _ ((coeffW w 1) ^ 6 * Q'.ofNat 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (centralLowerCube_lowerFaceFactor_eqv w)
  · exact Q'.eqv_trans _ ((coeffW w 1) ^ 6 * 1) _
      (Q'.mul_eqv_congr_left _ _ _ (by decide))
      (Q'.mul_one_eqv _)

theorem centralHalfAmplitude_cutoffOne_cube_vacuum_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') <
      centralHalfAmplitude w 1 0
        centralLowerCubeState zeroEdgeLabelling := by
  exact Q'.pos_of_lt_of_le
    (YMGap.Continuum.HKPos.pow_pos (coeffW_pos hw 1) 6)
    (Q'.ge_of_eqv
      (centralHalfAmplitude_cutoffOne_cube_vacuum_eqv w))

/-! ## 3. The complete lower-cube row -/

private theorem natListSum_eq_of_perm
    {left right : List Nat} (hperm : left.Perm right) :
    natListSum left = natListSum right := by
  induction hperm with
  | nil => rfl
  | cons _ _ ih =>
      simp only [natListSum]
      rw [ih]
  | swap _ _ _ =>
      simp only [natListSum]
      omega
  | trans _ _ ihleft ihrigh =>
      exact ihleft.trans ihrigh

private theorem cutoffOneCube_forcingLinkMultiplicity_zero
    (boundary : EdgeLabelling)
    (id : Nat) (hid : id ∈ centralFixedFaceIds 0)
    (hidOne : boundary id = 1) :
    let witness := cutoffOneVacuumForcingWitness id hid
    slabExplicitLinkMultiplicity 1 1
      (assembleReflectedSlabLabelling 0
        centralLowerCubeState boundary zeroEdgeLabelling)
      witness.link = 0 := by
  dsimp only
  let witness := cutoffOneVacuumForcingWitness id hid
  let vacuumPhysical := centralVacuumSourcePhysical
    boundary zeroEdgeLabelling
  let cubePhysical := centralCubeSourcePhysical
    boundary zeroEdgeLabelling
  let rest :=
    (centralLowerCubeUnselectedIncidentIds witness.link).map
      vacuumPhysical
  let spins := (slabIncidentPlaqIds 1 witness.link).map cubePhysical
  have hidNotCube : id ∉ centralLowerCubeFaceIds := by
    intro hidCube
    have hlower := mem_centralLowerFaceIds.mp
      (centralLowerCubeFaceIds_subset_lower id hidCube)
    have hfixed := mem_centralFixedFaceIds.mp hid
    rw [hfixed.2] at hlower
    cases hlower.2
  have hidUnselected :
      id ∈ centralLowerCubeUnselectedIncidentIds witness.link := by
    simp [centralLowerCubeUnselectedIncidentIds,
      witness.id_mem, hidNotCube]
  have hselectedValue : vacuumPhysical id = 1 := by
    unfold vacuumPhysical centralVacuumSourcePhysical
    have hparts := mem_centralFixedFaceIds.mp hid
    rw [assembleReflectedSlabLabelling_fixed hparts.1 hparts.2]
    exact hidOne
  have hotherZero :
      ∀ other,
        other ∈ centralLowerCubeUnselectedIncidentIds witness.link →
          other ≠ id → vacuumPhysical other = 0 := by
    intro other hother hne
    have hincident := (List.mem_filter.mp hother).1
    have hsupport := witness.incident_support other hincident
    rcases hsupport with heq | hlower
    · exact False.elim (hne heq)
    · unfold vacuumPhysical centralVacuumSourcePhysical
      have hparts := mem_centralLowerFaceIds.mp hlower
      rw [assembleReflectedSlabLabelling_lower hparts.1 hparts.2]
      rfl
  have hrestSum : natListSum rest = 1 := by
    unfold rest
    exact natListSum_map_unique_one vacuumPhysical
      (centralLowerCubeUnselectedIncidentIds witness.link) id
      ((slabIncidentPlaqIds_nodup 1 witness.link).filter _)
      hidUnselected hselectedValue hotherZero
  have hlength :=
    centralLowerCube_selected_length_zero_or_two witness.link
      (mem_centralLowerLinks.mp witness.link_mem).1
  have hperm :
      spins.Perm
        (List.replicate
            (centralLowerCubeSelectedIncidentIds witness.link).length 1 ++
          rest) := by
    exact cube_incident_spins_perm_selected_remainder
      boundary zeroEdgeLabelling witness.link
  have hsum : natListSum spins % 2 = 1 := by
    have hsumPerm := natListSum_eq_of_perm hperm
    rw [hsumPerm, natListSum_append, hrestSum]
    rcases hlength with hzero | htwo
    · rw [hzero]
      decide
    · rw [htwo]
      decide
  unfold slabExplicitLinkMultiplicity
  change
    explicitValenceMultiplicity (linkAuxiliaryCutoff 1)
      spins.length (externalSpinsOfList spins) = 0
  apply explicitValenceMultiplicity_eq_zero_of_odd_sum
  · unfold spins
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 witness.link
  · rw [localExternalSpinSum_externalSpinsOfList spins]
    omega

theorem centralHalfAmplitude_cutoffOne_cube_eqv_zero_of_fixed_one
    (w : Q') (boundary : EdgeLabelling)
    (id : Nat) (hid : id ∈ centralFixedFaceIds 0)
    (hidOne : boundary id = 1) :
    centralHalfAmplitude w 1 0 centralLowerCubeState boundary ≈ 0 := by
  let witness := cutoffOneVacuumForcingWitness id hid
  let physical := assembleReflectedSlabLabelling 0
    centralLowerCubeState boundary zeroEdgeLabelling
  have hlink :
      slabExplicitLinkMultiplicity 1 1 physical witness.link = 0 := by
    exact cutoffOneCube_forcingLinkMultiplicity_zero
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

theorem centralHalfAmplitude_cutoffOne_cube_word_eqv_delta
    (w : Q') (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    centralHalfAmplitude w 1 0 centralLowerCubeState
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      binaryVacuumWordWeight word * (coeffW w 1) ^ 6 := by
  cases hvacuum : binaryVacuumWordB word with
  | true =>
      rw [wordToEdgeLabelling_eq_zero_of_binaryVacuum
        (centralFixedFaceIds 0) word hvacuum]
      unfold binaryVacuumWordWeight
      rw [hvacuum]
      exact Q'.eqv_trans _ _ _
        (centralHalfAmplitude_cutoffOne_cube_vacuum_eqv w)
        (Q'.eqv_symm (Q'.one_mul_eqv _))
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
      exact Q'.eqv_trans _ 0 _
        (centralHalfAmplitude_cutoffOne_cube_eqv_zero_of_fixed_one
          w (wordToEdgeLabelling (centralFixedFaceIds 0) word)
          id hid hidOne)
        (Q'.eqv_symm (Q'.zero_mul_eqv _))

private theorem eliminateHead_mul_right
    (domainSize : Nat) (value : List Nat → Q')
    (scale : Q') (tail : List Nat) :
    eliminateHead domainSize (fun word => value word * scale) tail ≈
      eliminateHead domainSize value tail * scale := by
  unfold eliminateHead
  exact listQSum_mul_right
    (fun label => value (label :: tail)) scale (List.range domainSize)

/-- Multiplying the Boolean delta by a fixed exact weight preserves its
width-one elimination trace. -/
def binaryVacuumScaledEliminationCertificate
    (variables : Nat) (scale : Q') :
    ExactVariableEliminationCertificate
      2 variables (fun word => binaryVacuumWordWeight word * scale) where
  table := fun _remaining word => binaryVacuumWordWeight word * scale
  initial := fun _assignment _hassignment => Q'.eqv_refl _
  step := by
    intro remaining _hremaining tail _htail
    exact Q'.eqv_trans _ _ _
      (eliminateHead_mul_right 2 binaryVacuumWordWeight scale tail)
      (Q'.mul_eqv_congr_right _ _ scale
        (binaryVacuumWordWeight_eliminateHead tail))

def cutoffOnePhysicalCubeRowCertificate (w : Q') :
    ExactVariableEliminationCertificate
      2 (centralFixedFaceIds 0).length
      (fun word =>
        centralHalfAmplitude w 1 0 centralLowerCubeState
          (wordToEdgeLabelling (centralFixedFaceIds 0) word)) where
  table := (binaryVacuumScaledEliminationCertificate
    (centralFixedFaceIds 0).length ((coeffW w 1) ^ 6)).table
  initial := fun assignment hassignment =>
    centralHalfAmplitude_cutoffOne_cube_word_eqv_delta
      w assignment hassignment
  step := (binaryVacuumScaledEliminationCertificate
    (centralFixedFaceIds 0).length ((coeffW w 1) ^ 6)).step

/-- Exact row mass of the first non-vacuum physical source. -/
theorem centralHalfAmplitudeBoundaryRowMass_cutoffOne_cube_eqv
    (w : Q') :
    centralHalfAmplitudeBoundaryRowMass w 1 0 centralLowerCubeState ≈
      (coeffW w 1) ^ 6 := by
  refine Q'.eqv_trans _
    ((cutoffOnePhysicalCubeRowCertificate w).table 0 []) _
    (centralHalfAmplitudeBoundaryRowMass_eqv_certificateBottom
      (cutoffOnePhysicalCubeRowCertificate w)) ?_
  change binaryVacuumWordWeight [] * (coeffW w 1) ^ 6 ≈
    (coeffW w 1) ^ 6
  exact Q'.one_mul_eqv _

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry.centralLowerCube_lowerFaceFactor_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry.centralLowerCube_lowerLinkMultiplicityProduct_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry.centralHalfAmplitude_cutoffOne_cube_vacuum_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry.centralHalfAmplitude_cutoffOne_cube_vacuum_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry.centralHalfAmplitude_cutoffOne_cube_eqv_zero_of_fixed_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry.centralHalfAmplitude_cutoffOne_cube_word_eqv_delta
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry.centralHalfAmplitudeBoundaryRowMass_cutoffOne_cube_eqv
