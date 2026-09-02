/-
# Complete high-spin profile of accepted paired canonical peeling

The arbitrary-coupling pointwise telescope and the cutoff-independent core
potential are combined here in one proof-carrying recursive output.  Besides
the accepted terminal state, it stores the literal complete trace and the
total exterior and residual-core multiplicities.  The output satisfies

  traceMass = exteriorMass + coreMass,

and the paired source weight is bounded by

  (anchor^exteriorMass * 2^coreMass) * terminalWeight.

On the complete physical face list, `coreMass` is bounded by
`2 * faceCount * threshold`, independently of the representation cutoff.
This is the exact profile needed for the subsequent inverse-trace summation.

Constructive contract: finite records, natural/rational arithmetic, and
well-founded accepted peeling only; no choice, `Classical`, `sorry`, or new
axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingFiniteCoreMass

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingFiniteCoreMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One-step exterior/core partition -/

private theorem listNatWeight_add
    {A : Type} (left right : A -> Nat) : forall items : List A,
    listNatWeight (fun item => left item + right item) items =
      listNatWeight left items + listNatWeight right items
  | [] => rfl
  | item :: items => by
      simp only [listNatWeight]
      rw [listNatWeight_add left right items]
      omega

/-- Exterior and residual words partition the complete physical component
drop with exact multiplicity. -/
theorem acceptedExpandedSourceExterior_add_coreResidual_eq_peelSize
    (D : SlabPhysicalData) (threshold faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId) :
    acceptedExpandedSourceExteriorPeelSizeAt
          D threshold faceId hface entry hpositive +
        acceptedExpandedSourceCoreResidualSizeAt
          D threshold faceId hface entry hpositive =
      acceptedExpandedSourcePeelSizeAt
        D faceId hface entry hpositive := by
  let seed := acceptedExpandedSourceRootSeed
    D faceId hface entry hpositive
  change
    (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
          seed threshold).length +
        (SlabFusionWitnessFaceStrandSeed.coreResidualFaces
          seed threshold).length =
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length
  unfold SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
    SlabFusionWitnessFaceStrandSeed.coreResidualFaces
    SlabFusionWitnessFaceStrandSeed.peelFaces
    highSpinExteriorDropFaces highSpinCoreResidualFaces
  rw [slabFaceDropList_length_eq_listNatWeight,
    slabFaceDropList_length_eq_listNatWeight,
    slabFaceDropList_length_eq_listNatWeight]
  rw [← listNatWeight_add]
  apply congrArg (fun weight : Nat -> Nat =>
    listNatWeight weight (slabPhysicalFaceEdges D.extent))
  funext selectedFaceId
  exact exteriorDropCount_add_coreResidualDropCount
    entry.1.1 threshold
      (slabFaceStrandSelectionCount seed.selected) selectedFaceId

/-- The selected paired-step counters partition its exact peel size. -/
theorem slabAcceptedPairedPeelChoice_exterior_add_core_eq_peelSize
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (threshold : Nat) (choice : SlabAcceptedPairedPeelChoice D state) :
    slabAcceptedPairedPeelChoiceExteriorPeelSizeAt threshold choice +
        slabAcceptedPairedPeelChoiceCoreResidualSizeAt threshold choice =
      choice.peelSize := by
  cases choice with
  | left faceId hface hpositive =>
      exact acceptedExpandedSourceExterior_add_coreResidual_eq_peelSize
        D threshold faceId hface state.1 hpositive
  | right faceId hface hleftZero hpositive =>
      exact acceptedExpandedSourceExterior_add_coreResidual_eq_peelSize
        D threshold faceId hface state.2 hpositive

/-! ## 2. Profiled accepted recursion -/

abbrev SlabAcceptedPairedHighSpinProfileOutput
    (D : SlabPhysicalData) :=
  SlabAcceptedTwoReplicaState D ×
    List SlabAcceptedPairedPeelRecord × Nat × Nat

/-- The deterministic accepted recursion with its exact complete high-spin
profile retained. -/
def slabAcceptedPairCanonicalHighSpinProfile
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent) :
    (state : SlabAcceptedTwoReplicaState D) ->
      SlabAcceptedPairedHighSpinProfileOutput D
  | state =>
      match slabAcceptedPairCanonicalChoice? D state faces hphysical with
      | none => (state, [], 0, 0)
      | some choice =>
          let tail := slabAcceptedPairCanonicalHighSpinProfile
            D threshold faces hphysical choice.lowerState
          (tail.1,
            slabAcceptedPairedPeelChoiceRecord choice :: tail.2.1,
              slabAcceptedPairedPeelChoiceExteriorPeelSizeAt
                threshold choice + tail.2.2.1,
              slabAcceptedPairedPeelChoiceCoreResidualSizeAt
                threshold choice + tail.2.2.2)
termination_by state => slabAcceptedTwoReplicaStateMass state
decreasing_by
  exact choice.lowerState_mass_lt

/-- Forgetting the two high-spin counters recovers the pre-existing canonical
accepted terminal and trace literally.  This lets the profile reuse the
complete-output injection and every trace-carrier theorem without a second
decoder proof. -/
theorem slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalHighSpinProfile
      D threshold faces hphysical state
    (result.1, result.2.1) =
      slabAcceptedPairCanonicalPeeling D faces hphysical state := by
  change
    ((slabAcceptedPairCanonicalHighSpinProfile
        D threshold faces hphysical state).1,
      (slabAcceptedPairCanonicalHighSpinProfile
        D threshold faces hphysical state).2.1) =
      slabAcceptedPairCanonicalPeeling D faces hphysical state
  rw [slabAcceptedPairCanonicalHighSpinProfile]
  split
  · rename_i hchoice
    rw [slabAcceptedPairCanonicalPeeling, hchoice]
  · rename_i choice hchoice
    rw [slabAcceptedPairCanonicalPeeling, hchoice]
    dsimp only
    have htail :=
      slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
        D threshold faces hphysical choice.lowerState
    have hterminal := congrArg Prod.fst htail
    have htrace := congrArg Prod.snd htail
    exact Prod.ext hterminal
      (congrArg (List.cons (slabAcceptedPairedPeelChoiceRecord choice))
        htrace)
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-! ## 3. Exact trace and potential identities -/

/-- The stored trace mass is exactly partitioned by the stored exterior and
core masses. -/
theorem slabAcceptedPairCanonicalHighSpinProfile_traceMass
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalHighSpinProfile
      D threshold faces hphysical state
    slabAcceptedPairedPeelTraceMass result.2.1 =
      result.2.2.1 + result.2.2.2 := by
  change slabAcceptedPairedPeelTraceMass
      (slabAcceptedPairCanonicalHighSpinProfile
        D threshold faces hphysical state).2.1 =
    (slabAcceptedPairCanonicalHighSpinProfile
        D threshold faces hphysical state).2.2.1 +
      (slabAcceptedPairCanonicalHighSpinProfile
        D threshold faces hphysical state).2.2.2
  rw [slabAcceptedPairCanonicalHighSpinProfile]
  split
  · rfl
  · rename_i choice hchoice
    have htail := slabAcceptedPairCanonicalHighSpinProfile_traceMass
      D threshold faces hphysical choice.lowerState
    have hsplit :=
      slabAcceptedPairedPeelChoice_exterior_add_core_eq_peelSize
        threshold choice
    unfold slabAcceptedPairedPeelTraceMass at htail ⊢
    simp only [listNatWeight,
      slabAcceptedPairedPeelChoiceRecord_peelSize]
    omega
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-- The stored core mass is exactly the loss of two-replica threshold
potential. -/
theorem slabAcceptedPairCanonicalHighSpinProfile_core_telescope
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalHighSpinProfile
      D threshold faces hphysical state
    slabAcceptedTwoReplicaThresholdCoreMass
          D threshold result.1 + result.2.2.2 =
      slabAcceptedTwoReplicaThresholdCoreMass D threshold state := by
  change slabAcceptedTwoReplicaThresholdCoreMass D threshold
        (slabAcceptedPairCanonicalHighSpinProfile
          D threshold faces hphysical state).1 +
      (slabAcceptedPairCanonicalHighSpinProfile
        D threshold faces hphysical state).2.2.2 =
    slabAcceptedTwoReplicaThresholdCoreMass D threshold state
  rw [slabAcceptedPairCanonicalHighSpinProfile]
  split
  · exact Nat.add_zero _
  · rename_i choice hchoice
    have hstep :=
      SlabAcceptedPairedPeelChoice.lowerState_thresholdCoreMass_add_residual
        D threshold choice
    have htail := slabAcceptedPairCanonicalHighSpinProfile_core_telescope
      D threshold faces hphysical choice.lowerState
    change slabAcceptedTwoReplicaThresholdCoreMass D threshold
          (slabAcceptedPairCanonicalHighSpinProfile
            D threshold faces hphysical choice.lowerState).1 +
        (slabAcceptedPairedPeelChoiceCoreResidualSizeAt threshold choice +
          (slabAcceptedPairCanonicalHighSpinProfile
            D threshold faces hphysical choice.lowerState).2.2.2) =
      slabAcceptedTwoReplicaThresholdCoreMass D threshold state
    omega
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-- For every scanned face list, the stored residual-core exponent is at most
the initial threshold-truncated pair mass. -/
theorem slabAcceptedPairCanonicalHighSpinProfile_core_le_initial
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalHighSpinProfile
      D threshold faces hphysical state
    result.2.2.2 <=
      slabAcceptedTwoReplicaThresholdCoreMass D threshold state := by
  have htelescope :=
    slabAcceptedPairCanonicalHighSpinProfile_core_telescope
      D threshold faces hphysical state
  omega

/-- On the complete physical face list, the stored residual-core exponent is
bounded independently of the representation cutoff. -/
theorem slabAcceptedPairCanonicalHighSpinProfile_core_le
    (D : SlabPhysicalData) (threshold : Nat)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalHighSpinProfile
      D threshold D.faceEdges
        (fun faceId hface => by
          simpa only [SlabPhysicalData.faceEdges] using hface)
        state
    result.2.2.2 <= 2 * D.faceEdges.length * threshold := by
  let hphysical : forall faceId, faceId ∈ D.faceEdges ->
      faceId ∈ slabPhysicalFaceEdges D.extent := fun faceId hface => by
    simpa only [SlabPhysicalData.faceEdges] using hface
  let result := slabAcceptedPairCanonicalHighSpinProfile
    D threshold D.faceEdges hphysical state
  have hcore :=
    slabAcceptedPairCanonicalHighSpinProfile_core_le_initial
      D threshold D.faceEdges hphysical state
  have hinitial := slabAcceptedTwoReplicaThresholdCoreMass_le
    D threshold state
  change result.2.2.2 <= 2 * D.faceEdges.length * threshold
  exact Nat.le_trans hcore hinitial

/-- Every stored production record remains valid for its adaptive carrier. -/
theorem slabAcceptedPairCanonicalHighSpinProfile_trace_valid
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    forall record,
      record ∈ (slabAcceptedPairCanonicalHighSpinProfile
        D threshold faces hphysical state).2.1 ->
      record.Valid D.extent := by
  rw [slabAcceptedPairCanonicalHighSpinProfile]
  split
  · intro record hrecord
    cases hrecord
  · rename_i choice hchoice
    intro record hrecord
    rcases List.mem_cons.mp hrecord with heq | htail
    · subst record
      exact slabAcceptedPairedPeelChoiceRecord_valid choice
    · exact slabAcceptedPairCanonicalHighSpinProfile_trace_valid
        D threshold faces hphysical choice.lowerState record htail
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-! ## 4. Arbitrary-coupling pointwise payment in profiled form -/

private theorem mul_four_regroup_local (A B C E : Q') :
    (A * B) * (C * E) ≈ (A * C) * (B * E) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * E)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * E)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv B C E)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ E (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B E

private theorem twoRatePower_mul
    (exteriorBase coreBase : Q')
    (headExterior headCore tailExterior tailCore : Nat)
    (target : Q') :
    (exteriorBase ^ headExterior * coreBase ^ headCore) *
        ((exteriorBase ^ tailExterior * coreBase ^ tailCore) * target) ≈
      (exteriorBase ^ (headExterior + tailExterior) *
          coreBase ^ (headCore + tailCore)) * target := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      (exteriorBase ^ headExterior * coreBase ^ headCore)
      (exteriorBase ^ tailExterior * coreBase ^ tailCore) target)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ target
      (mul_four_regroup_local
        (exteriorBase ^ headExterior) (coreBase ^ headCore)
        (exteriorBase ^ tailExterior) (coreBase ^ tailCore))) ?_
  apply Q'.mul_eqv_congr_right
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (Q'.pow_add_eqv exteriorBase headExterior tailExterior))) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm (Q'.pow_add_eqv coreBase headCore tailCore))

/-- Exact profiled weight telescope to the actual accepted terminal. -/
theorem slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalHighSpinProfile
      D (anchorPaidExteriorThreshold D.coupling) faces hphysical state
    slabAcceptedTwoReplicaStateWeight D state <=
      (anchorFaceCoefficient ^ result.2.2.1 *
          (Q'.ofNat 2) ^ result.2.2.2) *
        slabAcceptedTwoReplicaStateWeight D result.1 := by
  change slabAcceptedTwoReplicaStateWeight D state <=
    (anchorFaceCoefficient ^
          (slabAcceptedPairCanonicalHighSpinProfile D
            (anchorPaidExteriorThreshold D.coupling)
              faces hphysical state).2.2.1 *
        (Q'.ofNat 2) ^
          (slabAcceptedPairCanonicalHighSpinProfile D
            (anchorPaidExteriorThreshold D.coupling)
              faces hphysical state).2.2.2) *
      slabAcceptedTwoReplicaStateWeight D
        (slabAcceptedPairCanonicalHighSpinProfile D
          (anchorPaidExteriorThreshold D.coupling)
            faces hphysical state).1
  rw [slabAcceptedPairCanonicalHighSpinProfile]
  split
  · exact Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))
  · rename_i choice hchoice
    have hstep := SlabAcceptedPairedPeelChoice.sourceWeight_le
      D hw0 hw1 choice
    have htail := slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le
      D hw0 hw1 faces hphysical choice.lowerState
    have hrateNonnegative :=
      slabAcceptedPairedPeelChoiceHighSpinPaymentRate_nonnegative
        (anchorPaidExteriorThreshold D.coupling) choice
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
      htail hrateNonnegative
    refine Q'.le_trans' _ _ _ hstep
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_))
    unfold slabAcceptedPairedPeelChoiceHighSpinPaymentRate
    exact twoRatePower_mul
      anchorFaceCoefficient (Q'.ofNat 2)
      (slabAcceptedPairedPeelChoiceExteriorPeelSizeAt
        (anchorPaidExteriorThreshold D.coupling) choice)
      (slabAcceptedPairedPeelChoiceCoreResidualSizeAt
        (anchorPaidExteriorThreshold D.coupling) choice)
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical choice.lowerState).2.2.1
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical choice.lowerState).2.2.2
      (slabAcceptedTwoReplicaStateWeight D
        (slabAcceptedPairCanonicalHighSpinProfile D
          (anchorPaidExteriorThreshold D.coupling)
            faces hphysical choice.lowerState).1)
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

#print axioms acceptedExpandedSourceExterior_add_coreResidual_eq_peelSize
#print axioms slabAcceptedPairedPeelChoice_exterior_add_core_eq_peelSize
#print axioms slabAcceptedPairCanonicalHighSpinProfile
#print axioms slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
#print axioms slabAcceptedPairCanonicalHighSpinProfile_traceMass
#print axioms slabAcceptedPairCanonicalHighSpinProfile_core_telescope
#print axioms slabAcceptedPairCanonicalHighSpinProfile_core_le_initial
#print axioms slabAcceptedPairCanonicalHighSpinProfile_core_le
#print axioms slabAcceptedPairCanonicalHighSpinProfile_trace_valid
#print axioms slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
