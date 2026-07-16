/-
# Exact three-face leakage on the projected physical cube

The abstract three-block cumulant calculation becomes physical here on the
smallest already-normalized overlapping Z4 component.  We use the three faces
`bottomXY`, `frontXZ`, and `leftYZ` of one closed six-face cube.  Each pair is
joined by one of the literal production links, and the three links meet at the
same cube corner.

The cutoff-one fine-support projector has exactly two surviving assignments.
The exact character/fusion calculation identifies every compatible raw mass
with `(coeffW w 1)^6`; after normalization, both assignments therefore have
mass `1/2`.  The three selected face-time bits are simultaneously `000` or
`111`.  Consequently an exact independent coupling of two such physical rows
has incoming and outgoing cross-pattern leakage exactly `1/4`, while every
mixed pattern has zero physical mass.

This also gives a kernel-checked frontier fence.  The current one-cube
projector cannot supply the positive eight-fibre premise of the strict
three-block conditional kernel.  The next physical input must be a genuinely
multi-cube overlapping amplitude theorem (and its global fine/coarse marginal
bridge), not another repackaging of a leakage bound.
-/

import YMGap.Continuum.Z4ThreeBlockPatternLeakageDecision
import YMGap.Continuum.Z4DyadicSlabCubeKernelProductComposition

namespace YMGap.Continuum.Z4ThreeBlockPhysicalCubeLeakage

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicSlabCubeFineSupportProjectedKernel
open YMGap.Continuum.Z4DyadicSlabCubeKernelProductComposition
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4RetunedParityPhysicalMixtureKernel
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockPatternLeakageDecision
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  show p * Q'.recipPos q hq ≈ c
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _ (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

def physicalCubeHalf : Q' := Q'.mkPos 1 2 (by decide)

def physicalCubeQuarter : Q' := Q'.mkPos 1 4 (by decide)

private theorem physicalCubeHalf_mul_add_self (x : Q') :
    physicalCubeHalf * (x + x) ≈ x := by
  refine Q'.eqv_trans _ (physicalCubeHalf * x + physicalCubeHalf * x) _
    (Q'.mul_add_eqv physicalCubeHalf x x) ?_
  refine Q'.eqv_trans _ ((physicalCubeHalf + physicalCubeHalf) * x) _
    (Q'.eqv_symm (Q'.add_mul_eqv physicalCubeHalf physicalCubeHalf x)) ?_
  refine Q'.eqv_trans _ ((1 : Q') * x) _
    (Q'.mul_eqv_congr_right _ _ x (by
      unfold physicalCubeHalf
      decide)) ?_
  exact Q'.one_mul_eqv x

private theorem leakage_zero_cleanup (x : Q') :
    ((0 : Q') + (x + 0)) + (0 + 0) ≈ x := by
  refine Q'.eqv_trans _ ((x + 0) + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_of_eq (Q'.zero_add' (x + 0)))
      (Q'.eqv_of_eq (Q'.zero_add' 0))
  · exact Q'.eqv_trans _ (x + 0) _
      (Q'.eqv_of_eq (Q'.add_zero' (x + 0)))
      (Q'.eqv_of_eq (Q'.add_zero' x))

/-! ## 1. Three literal pairwise-overlap witnesses -/

def bottomFrontCornerIncidence : CubeProductionIncidence :=
  ⟨((0, 0, 0, 0), .x0), .bottomXY, .frontXZ⟩

def bottomLeftCornerIncidence : CubeProductionIncidence :=
  ⟨((0, 0, 0, 0), .x1), .bottomXY, .leftYZ⟩

def frontLeftCornerIncidence : CubeProductionIncidence :=
  ⟨((0, 0, 0, 0), .x2), .frontXZ, .leftYZ⟩

theorem bottomFrontCornerIncidence_mem :
    bottomFrontCornerIncidence ∈ cubeProductionIncidences := by
  simp [bottomFrontCornerIncidence, cubeProductionIncidences]

theorem bottomLeftCornerIncidence_mem :
    bottomLeftCornerIncidence ∈ cubeProductionIncidences := by
  simp [bottomLeftCornerIncidence, cubeProductionIncidences]

theorem frontLeftCornerIncidence_mem :
    frontLeftCornerIncidence ∈ cubeProductionIncidences := by
  simp [frontLeftCornerIncidence, cubeProductionIncidences]

/-- The three selected faces are genuinely pairwise coupled by literal Haar
production links of the normalized cube component. -/
theorem physicalCubeCornerFaces_pairwise_overlap :
    (((0, 0, 0, 0), .x0) ∈ edgesOf (cubeFace .bottomXY) ∧
      ((0, 0, 0, 0), .x0) ∈ edgesOf (cubeFace .frontXZ)) ∧
    (((0, 0, 0, 0), .x1) ∈ edgesOf (cubeFace .bottomXY) ∧
      ((0, 0, 0, 0), .x1) ∈ edgesOf (cubeFace .leftYZ)) ∧
    (((0, 0, 0, 0), .x2) ∈ edgesOf (cubeFace .frontXZ) ∧
      ((0, 0, 0, 0), .x2) ∈ edgesOf (cubeFace .leftYZ)) := by
  exact ⟨cubeProductionIncidence_on_recorded_faces
      bottomFrontCornerIncidence_mem,
    cubeProductionIncidence_on_recorded_faces
      bottomLeftCornerIncidence_mem,
    cubeProductionIncidence_on_recorded_faces
      frontLeftCornerIncidence_mem⟩

/-! ## 2. Exact normalization of the projected character row -/

theorem closedCubeFineSlotPartition_eqv_two_character_weights
    (w : Q') :
    closedCubeFineSlotPartition w ≈
      (coeffW w 1) ^ 6 + (coeffW w 1) ^ 6 := by
  unfold closedCubeFineSlotPartition
  rw [closedCubeFineSlotStateSpace_eq]
  change
    closedCubeFineSlotRawWeight w oddFineCubeSlotAssignment +
        (closedCubeFineSlotRawWeight w
          reflectedOddFineCubeSlotAssignment + 0) ≈
      (coeffW w 1) ^ 6 + (coeffW w 1) ^ 6
  refine Q'.add_eqv_congr'
    (closedCubeFineSlotRawWeight_eqv_pow_six w _)
    (Q'.eqv_trans _ ((coeffW w 1) ^ 6 + 0) _
      (Q'.add_eqv_congr'
        (closedCubeFineSlotRawWeight_eqv_pow_six w _)
        (Q'.eqv_refl 0))
      (Q'.eqv_of_eq (Q'.add_zero' ((coeffW w 1) ^ 6))))

/-- Every compatible projected slot assignment has exact normalized mass
`1/2`.  The proof uses only the derived six-character raw identity and the
two-state geometric classification. -/
theorem closedCubeFineSlotKernel_eqv_half
    (w : Q') (hw : (0 : Q') < w)
    (assignment : CubeFineSlotAssignment) :
    closedCubeFineSlotKernel w hw assignment ≈ physicalCubeHalf := by
  unfold closedCubeFineSlotKernel
  apply divPos_eqv_of_eqv_mul_local
    (closedCubeFineSlotPartition_pos hw)
  let characterWeight := (coeffW w 1) ^ 6
  have hnum : closedCubeFineSlotRawWeight w assignment ≈
      characterWeight :=
    closedCubeFineSlotRawWeight_eqv_pow_six w assignment
  have hpartition : closedCubeFineSlotPartition w ≈
      characterWeight + characterWeight :=
    closedCubeFineSlotPartition_eqv_two_character_weights w
  have hhalfPartition :
      physicalCubeHalf * closedCubeFineSlotPartition w ≈
        characterWeight := by
    refine Q'.eqv_trans _
      (physicalCubeHalf * (characterWeight + characterWeight)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left physicalCubeHalf _ _ hpartition
    · exact physicalCubeHalf_mul_add_self characterWeight
  exact Q'.eqv_trans _ characterWeight _ hnum
    (Q'.eqv_symm hhalfPartition)

/-! ## 3. The three-bit law on the incident corner faces -/

def bottomFaceTimeEvent (assignment : CubeFineSlotAssignment) : Bool :=
  fineFaceSlotTimeB (cubeFineSlotAt assignment .bottomXY)

def frontFaceTimeEvent (assignment : CubeFineSlotAssignment) : Bool :=
  fineFaceSlotTimeB (cubeFineSlotAt assignment .frontXZ)

def leftFaceTimeEvent (assignment : CubeFineSlotAssignment) : Bool :=
  fineFaceSlotTimeB (cubeFineSlotAt assignment .leftYZ)

private theorem closedCubeFaceTimeEventMass_eqv_half
    (w : Q') (hw : (0 : Q') < w)
    (event : CubeFineSlotAssignment → Bool)
    (hodd : event oddFineCubeSlotAssignment = false)
    (hreflected : event reflectedOddFineCubeSlotAssignment = true) :
    finiteEventMass (closedCubeFineSlotKernel w hw)
        closedCubeFineSlotStateSpace event ≈ physicalCubeHalf := by
  unfold finiteEventMass
  rw [closedCubeFineSlotStateSpace_eq]
  simp only [listQSum, hodd, hreflected, Bool.false_eq_true,
    if_false, if_true]
  refine Q'.eqv_trans _
    ((0 : Q') + (physicalCubeHalf + 0)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl 0)
      (Q'.add_eqv_congr'
        (closedCubeFineSlotKernel_eqv_half w hw _)
        (Q'.eqv_refl 0))
  · exact Q'.eqv_trans _ (physicalCubeHalf + 0) _
      (Q'.eqv_of_eq (Q'.zero_add' (physicalCubeHalf + 0)))
      (Q'.eqv_of_eq (Q'.add_zero' physicalCubeHalf))

def closedCubeCornerThreeBlockLaw
    (w : Q') (hw : (0 : Q') < w) :
    ThreeBlockOverlapFiniteLaw CubeFineSlotAssignment where
  mass := closedCubeFineSlotKernel w hw
  states := closedCubeFineSlotStateSpace
  leftParameter := physicalCubeHalf
  sharedParameter := physicalCubeHalf
  rightParameter := physicalCubeHalf
  leftEvent := bottomFaceTimeEvent
  sharedEvent := frontFaceTimeEvent
  rightEvent := leftFaceTimeEvent
  mass_nonnegative := closedCubeFineSlotKernel_nonnegative w hw
  left_nonnegative := by unfold physicalCubeHalf; decide
  left_le_one := by unfold physicalCubeHalf; decide
  shared_nonnegative := by unfold physicalCubeHalf; decide
  shared_le_one := by unfold physicalCubeHalf; decide
  right_nonnegative := by unfold physicalCubeHalf; decide
  right_le_one := by unfold physicalCubeHalf; decide
  left_mass := closedCubeFaceTimeEventMass_eqv_half w hw _ rfl rfl
  shared_mass := closedCubeFaceTimeEventMass_eqv_half w hw _ rfl rfl
  right_mass := closedCubeFaceTimeEventMass_eqv_half w hw _ rfl rfl
  normalized := closedCubeFineSlotKernel_row_normalized w hw

theorem closedCubeCornerThreeBlockPattern_odd
    (w : Q') (hw : (0 : Q') < w) :
    threeBlockPattern (closedCubeCornerThreeBlockLaw w hw)
        oddFineCubeSlotAssignment = (false, false, false) := by
  rfl

theorem closedCubeCornerThreeBlockPattern_reflected
    (w : Q') (hw : (0 : Q') < w) :
    threeBlockPattern (closedCubeCornerThreeBlockLaw w hw)
        reflectedOddFineCubeSlotAssignment = (true, true, true) := by
  rfl

/-- Fine-support closure collapses the nominal eight-cell pattern carrier to
the two diagonal cells `000` and `111`. -/
theorem closedCubeCornerThreeBlockPattern_diagonal
    (w : Q') (hw : (0 : Q') < w)
    {assignment : CubeFineSlotAssignment}
    (hassignment : assignment ∈ closedCubeFineSlotStateSpace) :
    threeBlockPattern (closedCubeCornerThreeBlockLaw w hw) assignment =
        (false, false, false) ∨
      threeBlockPattern (closedCubeCornerThreeBlockLaw w hw) assignment =
        (true, true, true) := by
  rw [closedCubeFineSlotStateSpace_eq] at hassignment
  rcases List.mem_cons.mp hassignment with hodd | hreflected
  · subst assignment
    exact Or.inl (closedCubeCornerThreeBlockPattern_odd w hw)
  · have heq := List.mem_singleton.mp hreflected
    subst assignment
    exact Or.inr (closedCubeCornerThreeBlockPattern_reflected w hw)

theorem closedCubeCornerPatternMass_false_eqv_half
    (w : Q') (hw : (0 : Q') < w) :
    threeBlockPatternMass (closedCubeCornerThreeBlockLaw w hw)
        (false, false, false) ≈ physicalCubeHalf := by
  unfold threeBlockPatternMass
  change listQSum
      (fun state => if threeBlockPattern
          (closedCubeCornerThreeBlockLaw w hw) state =
            (false, false, false)
        then closedCubeFineSlotKernel w hw state else 0)
      closedCubeFineSlotStateSpace ≈ physicalCubeHalf
  rw [closedCubeFineSlotStateSpace_eq]
  simp only [listQSum, closedCubeCornerThreeBlockPattern_odd,
    closedCubeCornerThreeBlockPattern_reflected, if_true]
  refine Q'.eqv_trans _
    (physicalCubeHalf + ((0 : Q') + 0)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (closedCubeFineSlotKernel_eqv_half w hw _)
      (Q'.eqv_refl _)
  · decide

theorem closedCubeCornerPatternMass_true_eqv_half
    (w : Q') (hw : (0 : Q') < w) :
    threeBlockPatternMass (closedCubeCornerThreeBlockLaw w hw)
        (true, true, true) ≈ physicalCubeHalf := by
  unfold threeBlockPatternMass
  change listQSum
      (fun state => if threeBlockPattern
          (closedCubeCornerThreeBlockLaw w hw) state =
            (true, true, true)
        then closedCubeFineSlotKernel w hw state else 0)
      closedCubeFineSlotStateSpace ≈ physicalCubeHalf
  rw [closedCubeFineSlotStateSpace_eq]
  simp only [listQSum, closedCubeCornerThreeBlockPattern_odd,
    closedCubeCornerThreeBlockPattern_reflected, if_true]
  refine Q'.eqv_trans _
    ((0 : Q') + (physicalCubeHalf + 0)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl 0)
      (Q'.add_eqv_congr'
        (closedCubeFineSlotKernel_eqv_half w hw _)
        (Q'.eqv_refl 0))
  · decide

theorem closedCubeCornerPatternMass_mixed_eqv_zero
    (w : Q') (hw : (0 : Q') < w) :
    threeBlockPatternMass (closedCubeCornerThreeBlockLaw w hw)
        (false, false, true) ≈ 0 := by
  unfold threeBlockPatternMass
  change listQSum
      (fun state => if threeBlockPattern
          (closedCubeCornerThreeBlockLaw w hw) state =
            (false, false, true)
        then closedCubeFineSlotKernel w hw state else 0)
      closedCubeFineSlotStateSpace ≈ 0
  rw [closedCubeFineSlotStateSpace_eq]
  simp only [listQSum, closedCubeCornerThreeBlockPattern_odd,
    closedCubeCornerThreeBlockPattern_reflected]
  simp
  ac_qeqv

/-! ## 4. Exact character-derived leakage of the independent coupling -/

def closedCubeIndependentJointMass
    (sourceW : Q') (hsourceW : (0 : Q') < sourceW)
    (targetW : Q') (htargetW : (0 : Q') < targetW)
    (source target : CubeFineSlotAssignment) : Q' :=
  closedCubeFineSlotKernel sourceW hsourceW source *
    closedCubeFineSlotKernel targetW htargetW target

theorem closedCubeIndependentJointMass_nonnegative
    (sourceW : Q') (hsourceW : (0 : Q') < sourceW)
    (targetW : Q') (htargetW : (0 : Q') < targetW)
    (source target : CubeFineSlotAssignment) :
    (0 : Q') ≤ closedCubeIndependentJointMass
      sourceW hsourceW targetW htargetW source target := by
  unfold closedCubeIndependentJointMass
  exact Q'.mul_nonneg _ _
    (closedCubeFineSlotKernel_nonnegative sourceW hsourceW source)
    (closedCubeFineSlotKernel_nonnegative targetW htargetW target)

def closedCubeIndependentPositiveCoupling
    (sourceW : Q') (hsourceW : (0 : Q') < sourceW)
    (targetW : Q') (htargetW : (0 : Q') < targetW) :
    PositiveFiniteConfigurationCoupling
      (closedCubeFineSlotKernel sourceW hsourceW)
      closedCubeFineSlotStateSpace
      (closedCubeFineSlotKernel targetW htargetW)
      closedCubeFineSlotStateSpace
      (closedCubeIndependentJointMass
        sourceW hsourceW targetW htargetW) where
  nonnegative := closedCubeIndependentJointMass_nonnegative
    sourceW hsourceW targetW htargetW
  source_marginal := by
    intro source
    unfold closedCubeIndependentJointMass
    refine Q'.eqv_trans _
      (closedCubeFineSlotKernel sourceW hsourceW source *
        listQSum (closedCubeFineSlotKernel targetW htargetW)
          closedCubeFineSlotStateSpace) _ ?_ ?_
    · exact listQSum_mul_left
        (closedCubeFineSlotKernel sourceW hsourceW source)
        (closedCubeFineSlotKernel targetW htargetW)
        closedCubeFineSlotStateSpace
    · refine Q'.eqv_trans _
        (closedCubeFineSlotKernel sourceW hsourceW source * 1) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (closedCubeFineSlotKernel_row_normalized targetW htargetW)
      · exact Q'.mul_one_eqv _
  target_marginal := by
    intro target
    unfold closedCubeIndependentJointMass
    refine Q'.eqv_trans _
      (listQSum (closedCubeFineSlotKernel sourceW hsourceW)
          closedCubeFineSlotStateSpace *
        closedCubeFineSlotKernel targetW htargetW target) _ ?_ ?_
    · exact listQSum_mul_right
        (closedCubeFineSlotKernel sourceW hsourceW)
        (closedCubeFineSlotKernel targetW htargetW target)
        closedCubeFineSlotStateSpace
    · refine Q'.eqv_trans _
        ((1 : Q') * closedCubeFineSlotKernel targetW htargetW target) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (closedCubeFineSlotKernel_row_normalized sourceW hsourceW)
      · exact Q'.one_mul_eqv _
  normalized := by
    refine Q'.eqv_trans _
      (listQSum (closedCubeFineSlotKernel sourceW hsourceW)
          closedCubeFineSlotStateSpace *
        listQSum (closedCubeFineSlotKernel targetW htargetW)
          closedCubeFineSlotStateSpace) _ ?_ ?_
    · exact listQSum_product
        (closedCubeFineSlotKernel sourceW hsourceW)
        (closedCubeFineSlotKernel targetW htargetW)
        closedCubeFineSlotStateSpace closedCubeFineSlotStateSpace
    · refine Q'.eqv_trans _ ((1 : Q') * 1) _
        (qmul_congr
          (closedCubeFineSlotKernel_row_normalized sourceW hsourceW)
          (closedCubeFineSlotKernel_row_normalized targetW htargetW)) ?_
      decide

/-- The unique cross-pattern summand is literally a product of the two
normalized six-face character/fusion amplitudes. -/
theorem closedCubeIndependent_cross_character_expression
    (sourceW : Q') (hsourceW : (0 : Q') < sourceW)
    (targetW : Q') (htargetW : (0 : Q') < targetW) :
    closedCubeIndependentJointMass sourceW hsourceW targetW htargetW
        oddFineCubeSlotAssignment reflectedOddFineCubeSlotAssignment =
      Q'.divPos
          (cubeCoupledRawWeight sourceW 1
            (cubeFineSlotSource oddFineCubeSlotAssignment)
            (compatibleCubeTarget
              (cubeFineSlotSource oddFineCubeSlotAssignment)))
          (closedCubeFineSlotPartition sourceW)
          (closedCubeFineSlotPartition_pos hsourceW) *
        Q'.divPos
          (cubeCoupledRawWeight targetW 1
            (cubeFineSlotSource reflectedOddFineCubeSlotAssignment)
            (compatibleCubeTarget
              (cubeFineSlotSource reflectedOddFineCubeSlotAssignment)))
          (closedCubeFineSlotPartition targetW)
          (closedCubeFineSlotPartition_pos htargetW) := by
  rfl

theorem closedCubeIndependent_cross_eqv_quarter
    (sourceW : Q') (hsourceW : (0 : Q') < sourceW)
    (targetW : Q') (htargetW : (0 : Q') < targetW) :
    closedCubeIndependentJointMass sourceW hsourceW targetW htargetW
        oddFineCubeSlotAssignment reflectedOddFineCubeSlotAssignment ≈
      physicalCubeQuarter := by
  unfold closedCubeIndependentJointMass
  refine Q'.eqv_trans _ (physicalCubeHalf * physicalCubeHalf) _
    (qmul_congr
      (closedCubeFineSlotKernel_eqv_half sourceW hsourceW _)
      (closedCubeFineSlotKernel_eqv_half targetW htargetW _)) ?_
  unfold physicalCubeHalf physicalCubeQuarter
  decide

theorem closedCubeIndependent_outgoing_false_eqv_quarter
    (sourceW : Q') (hsourceW : (0 : Q') < sourceW)
    (targetW : Q') (htargetW : (0 : Q') < targetW) :
    threeBlockPatternOutgoingLeakage
        (closedCubeCornerThreeBlockLaw sourceW hsourceW)
        (closedCubeCornerThreeBlockLaw targetW htargetW)
        (closedCubeIndependentJointMass
          sourceW hsourceW targetW htargetW)
        (false, false, false) ≈ physicalCubeQuarter := by
  unfold threeBlockPatternOutgoingLeakage
  change finiteEventOutgoingLeakage
      closedCubeFineSlotStateSpace closedCubeFineSlotStateSpace
      (threeBlockPatternEvent
        (closedCubeCornerThreeBlockLaw sourceW hsourceW)
        (false, false, false))
      (threeBlockPatternEvent
        (closedCubeCornerThreeBlockLaw targetW htargetW)
        (false, false, false))
      (closedCubeIndependentJointMass
        sourceW hsourceW targetW htargetW) ≈ physicalCubeQuarter
  unfold finiteEventOutgoingLeakage
  rw [closedCubeFineSlotStateSpace_eq]
  simp only [listQSum, threeBlockPatternEvent,
    closedCubeCornerThreeBlockPattern_odd,
    closedCubeCornerThreeBlockPattern_reflected]
  simp
  refine Q'.eqv_trans _
    (closedCubeIndependentJointMass sourceW hsourceW targetW htargetW
      oddFineCubeSlotAssignment reflectedOddFineCubeSlotAssignment) _ ?_ ?_
  · exact leakage_zero_cleanup _
  · exact closedCubeIndependent_cross_eqv_quarter
      sourceW hsourceW targetW htargetW

theorem closedCubeIndependent_incoming_true_eqv_quarter
    (sourceW : Q') (hsourceW : (0 : Q') < sourceW)
    (targetW : Q') (htargetW : (0 : Q') < targetW) :
    threeBlockPatternIncomingLeakage
        (closedCubeCornerThreeBlockLaw sourceW hsourceW)
        (closedCubeCornerThreeBlockLaw targetW htargetW)
        (closedCubeIndependentJointMass
          sourceW hsourceW targetW htargetW)
        (true, true, true) ≈ physicalCubeQuarter := by
  unfold threeBlockPatternIncomingLeakage
  change finiteEventIncomingLeakage
      closedCubeFineSlotStateSpace closedCubeFineSlotStateSpace
      (threeBlockPatternEvent
        (closedCubeCornerThreeBlockLaw sourceW hsourceW)
        (true, true, true))
      (threeBlockPatternEvent
        (closedCubeCornerThreeBlockLaw targetW htargetW)
        (true, true, true))
      (closedCubeIndependentJointMass
        sourceW hsourceW targetW htargetW) ≈ physicalCubeQuarter
  unfold finiteEventIncomingLeakage
  rw [closedCubeFineSlotStateSpace_eq]
  simp only [listQSum, threeBlockPatternEvent,
    closedCubeCornerThreeBlockPattern_odd,
    closedCubeCornerThreeBlockPattern_reflected]
  simp
  refine Q'.eqv_trans _
    (closedCubeIndependentJointMass sourceW hsourceW targetW htargetW
      oddFineCubeSlotAssignment reflectedOddFineCubeSlotAssignment) _ ?_ ?_
  · exact leakage_zero_cleanup _
  · exact closedCubeIndependent_cross_eqv_quarter
      sourceW hsourceW targetW htargetW

/-- A nontrivial rational bound (`1/4 < 1`) obtained from the exact physical
amplitudes, not from sampling or a free leakage premise. -/
theorem closedCubeIndependent_outgoing_false_le_quarter
    (sourceW : Q') (hsourceW : (0 : Q') < sourceW)
    (targetW : Q') (htargetW : (0 : Q') < targetW) :
    threeBlockPatternOutgoingLeakage
        (closedCubeCornerThreeBlockLaw sourceW hsourceW)
        (closedCubeCornerThreeBlockLaw targetW htargetW)
        (closedCubeIndependentJointMass
          sourceW hsourceW targetW htargetW)
        (false, false, false) ≤ physicalCubeQuarter :=
  Q'.le_of_eqv (closedCubeIndependent_outgoing_false_eqv_quarter
    sourceW hsourceW targetW htargetW)

theorem physicalCubeQuarter_lt_one : physicalCubeQuarter < (1 : Q') := by
  unfold physicalCubeQuarter
  decide

/-! ## 5. Machine fence -/

/-- The present one-cube projected law cannot meet the all-eight-fibres
positivity premise required by `ThreeBlockPatternMatch`. -/
theorem closedCubeCorner_no_patternMatch
    (sourceW : Q') (hsourceW : (0 : Q') < sourceW)
    (targetW : Q') (htargetW : (0 : Q') < targetW) :
    ¬ ThreeBlockPatternMatch
      (closedCubeCornerThreeBlockLaw sourceW hsourceW)
      (closedCubeCornerThreeBlockLaw targetW htargetW) := by
  intro hmatch
  have hpos := hmatch.target_pattern_mass_pos (false, false, true)
  have hzero := closedCubeCornerPatternMass_mixed_eqv_zero
    targetW htargetW
  have hle : threeBlockPatternMass
      (closedCubeCornerThreeBlockLaw targetW htargetW)
      (false, false, true) ≤ 0 := Q'.le_of_eqv hzero
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' 0
    (YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hpos hle)

theorem closedCubeCorner_not_mixedCellAmplitude
    (w : Q') (hw : (0 : Q') < w) :
    ¬ ((0 : Q') < threeBlockPatternMass
      (closedCubeCornerThreeBlockLaw w hw) (false, false, true)) := by
  intro hpos
  have hzero := closedCubeCornerPatternMass_mixed_eqv_zero w hw
  have hle : threeBlockPatternMass
      (closedCubeCornerThreeBlockLaw w hw)
      (false, false, true) ≤ 0 := Q'.le_of_eqv hzero
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' 0
    (YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hpos hle)

/-! ## 6. The actual fine/coarse three-root marginal bridge -/

/-- Three canonical cube roots in left/shared/right order. -/
abbrev PhysicalCubeRootTriple :=
  List Nat × (List Nat × List Nat)

def physicalRootTripleLeft (roots : PhysicalCubeRootTriple) : List Nat :=
  roots.1

def physicalRootTripleShared (roots : PhysicalCubeRootTriple) : List Nat :=
  roots.2.1

def physicalRootTripleRight (roots : PhysicalCubeRootTriple) : List Nat :=
  roots.2.2

def physicalRootOccurrenceEvent
    (volume : Nat) (root : List Nat) : EdgeLabelling → Bool :=
  cutoffOneLiftedFamilyEvent volume (familyContainsPolymerB root)

def physicalRootTripleLeftEvent
    (volume : Nat) (roots : PhysicalCubeRootTriple) :
    EdgeLabelling → Bool :=
  physicalRootOccurrenceEvent volume (physicalRootTripleLeft roots)

def physicalRootTripleSharedEvent
    (volume : Nat) (roots : PhysicalCubeRootTriple) :
    EdgeLabelling → Bool :=
  physicalRootOccurrenceEvent volume (physicalRootTripleShared roots)

def physicalRootTripleRightEvent
    (volume : Nat) (roots : PhysicalCubeRootTriple) :
    EdgeLabelling → Bool :=
  physicalRootOccurrenceEvent volume (physicalRootTripleRight roots)

/-- The complete normalized physical configuration law equipped with three
literal canonical-root occurrence coordinates. -/
def normalizedPhysicalThreeRootLaw
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (roots : PhysicalCubeRootTriple) :
    ThreeBlockOverlapFiniteLaw EdgeLabelling where
  mass := normalizedPhysicalMass coupling hcoupling cutoff volume
  states := activityMatchedConfigurationStateSpace cutoff volume
  leftParameter := finiteEventMass
    (normalizedPhysicalMass coupling hcoupling cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (physicalRootTripleLeftEvent volume roots)
  sharedParameter := finiteEventMass
    (normalizedPhysicalMass coupling hcoupling cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (physicalRootTripleSharedEvent volume roots)
  rightParameter := finiteEventMass
    (normalizedPhysicalMass coupling hcoupling cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (physicalRootTripleRightEvent volume roots)
  leftEvent := physicalRootTripleLeftEvent volume roots
  sharedEvent := physicalRootTripleSharedEvent volume roots
  rightEvent := physicalRootTripleRightEvent volume roots
  mass_nonnegative :=
    normalizedPhysicalMass_nonnegative coupling hcoupling cutoff volume
  left_nonnegative := finiteEventMass_nonnegative _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
  left_le_one := finiteEventMass_le_one _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
    (normalizedPhysicalMass_total coupling hcoupling cutoff volume)
  shared_nonnegative := finiteEventMass_nonnegative _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
  shared_le_one := finiteEventMass_le_one _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
    (normalizedPhysicalMass_total coupling hcoupling cutoff volume)
  right_nonnegative := finiteEventMass_nonnegative _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
  right_le_one := finiteEventMass_le_one _ _ _ (by
    intro state _
    exact normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
    (normalizedPhysicalMass_total coupling hcoupling cutoff volume)
  left_mass := Q'.eqv_refl _
  shared_mass := Q'.eqv_refl _
  right_mass := Q'.eqv_refl _
  normalized := normalizedPhysicalMass_total
    coupling hcoupling cutoff volume

def activityMatchedFineThreeRootLaw
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (fineRoots : PhysicalCubeRootTriple) :
    ThreeBlockOverlapFiniteLaw EdgeLabelling :=
  normalizedPhysicalThreeRootLaw
    fineCoupling hfine cutoff volume fineRoots

def activityMatchedCoarseThreeRootLaw
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (coarseRoots : PhysicalCubeRootTriple) :
    ThreeBlockOverlapFiniteLaw EdgeLabelling :=
  normalizedPhysicalThreeRootLaw
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine)
    cutoff volume coarseRoots

/-- Every complete three-bit cell of the actual normalized physical law is
an exact finite character/fusion numerator divided by the proved-positive
physical partition.  This discharges the global marginal bridge; no
compatibility premise is inserted. -/
theorem normalizedPhysicalThreeRootPatternMass_eqv_character_ratio
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (roots : PhysicalCubeRootTriple)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass
        (normalizedPhysicalThreeRootLaw
          coupling hcoupling cutoff volume roots) pattern ≈
      Q'.divPos
        (parametricKEventNumerator coupling cutoff volume
          (threeBlockPatternEvent
            (normalizedPhysicalThreeRootLaw
              coupling hcoupling cutoff volume roots) pattern))
        (parametricKPhysicalPartition coupling cutoff volume)
        (couplingKPhysicalPartition_pos
          hcoupling cutoff volume) := by
  refine Q'.eqv_trans _
    (finiteEventMass
      (normalizedPhysicalMass coupling hcoupling cutoff volume)
      (activityMatchedConfigurationStateSpace cutoff volume)
      (threeBlockPatternEvent
        (normalizedPhysicalThreeRootLaw
          coupling hcoupling cutoff volume roots) pattern)) _ ?_ ?_
  · exact Q'.eqv_symm
      (finiteEventMass_threeBlockPatternEvent
        (normalizedPhysicalThreeRootLaw
          coupling hcoupling cutoff volume roots) pattern)
  · unfold activityMatchedConfigurationStateSpace
    exact normalizedPhysicalEventMass_eqv_probability
      coupling hcoupling cutoff volume _

theorem activityMatchedFineThreeRootPatternMass_eqv_character_ratio
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (fineRoots : PhysicalCubeRootTriple)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass
        (activityMatchedFineThreeRootLaw
          fineCoupling hfine cutoff volume fineRoots) pattern ≈
      Q'.divPos
        (parametricKEventNumerator fineCoupling cutoff volume
          (threeBlockPatternEvent
            (activityMatchedFineThreeRootLaw
              fineCoupling hfine cutoff volume fineRoots) pattern))
        (parametricKPhysicalPartition fineCoupling cutoff volume)
        (couplingKPhysicalPartition_pos hfine cutoff volume) :=
  normalizedPhysicalThreeRootPatternMass_eqv_character_ratio
    fineCoupling hfine cutoff volume fineRoots pattern

theorem activityMatchedCoarseThreeRootPatternMass_eqv_character_ratio
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (coarseRoots : PhysicalCubeRootTriple)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass
        (activityMatchedCoarseThreeRootLaw
          fineCoupling hfine cutoff volume coarseRoots) pattern ≈
      Q'.divPos
        (parametricKEventNumerator
          (unitCubeBlockCoupling fineCoupling) cutoff volume
          (threeBlockPatternEvent
            (activityMatchedCoarseThreeRootLaw
              fineCoupling hfine cutoff volume coarseRoots) pattern))
        (parametricKPhysicalPartition
          (unitCubeBlockCoupling fineCoupling) cutoff volume)
        (couplingKPhysicalPartition_pos
          (unitCubeBlockCoupling_nonnegative hfine) cutoff volume) :=
  normalizedPhysicalThreeRootPatternMass_eqv_character_ratio
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine)
    cutoff volume coarseRoots pattern

/-! ## 7. Sharp remaining local-amplitude theorem -/

/-- Two canonical surface roots genuinely overlap when their geometric
supports share a literal production link. -/
def CanonicalRootsShareProductionLink
    (volume : Nat) (left right : List Nat) : Prop :=
  ∃ leftFace, leftFace ∈ geometricPolymer volume left ∧
    ∃ rightFace, rightFace ∈ geometricPolymer volume right ∧
      ∃ link, link ∈ edgesOf leftFace ∧ link ∈ edgesOf rightFace

/-- Exact geometric fine/coarse relation for one cube root. -/
def DyadicRootRefines
    (volume : Nat) (coarse fine : List Nat) : Prop :=
  sameSupport (L := z4Chain.toLattice)
    (geometricPolymer volume fine)
    (dyadicSupportCells (geometricPolymer volume coarse))

/-- The smallest genuine three-cube geometry needed after the one-cube
diagonal-pattern fence. -/
structure ThreeCubeBlockRootData (volume : Nat) where
  coarseRoots : PhysicalCubeRootTriple
  fineRoots : PhysicalCubeRootTriple
  coarseLeftCanonical :
    physicalRootTripleLeft coarseRoots ∈ canonicalSurfacePolymers volume
  coarseSharedCanonical :
    physicalRootTripleShared coarseRoots ∈ canonicalSurfacePolymers volume
  coarseRightCanonical :
    physicalRootTripleRight coarseRoots ∈ canonicalSurfacePolymers volume
  fineLeftCanonical :
    physicalRootTripleLeft fineRoots ∈ canonicalSurfacePolymers volume
  fineSharedCanonical :
    physicalRootTripleShared fineRoots ∈ canonicalSurfacePolymers volume
  fineRightCanonical :
    physicalRootTripleRight fineRoots ∈ canonicalSurfacePolymers volume
  leftRefines : DyadicRootRefines volume
    (physicalRootTripleLeft coarseRoots)
    (physicalRootTripleLeft fineRoots)
  sharedRefines : DyadicRootRefines volume
    (physicalRootTripleShared coarseRoots)
    (physicalRootTripleShared fineRoots)
  rightRefines : DyadicRootRefines volume
    (physicalRootTripleRight coarseRoots)
    (physicalRootTripleRight fineRoots)
  fineLeftSharedOverlap : CanonicalRootsShareProductionLink volume
    (physicalRootTripleLeft fineRoots)
    (physicalRootTripleShared fineRoots)
  fineLeftRightOverlap : CanonicalRootsShareProductionLink volume
    (physicalRootTripleLeft fineRoots)
    (physicalRootTripleRight fineRoots)
  fineSharedRightOverlap : CanonicalRootsShareProductionLink volume
    (physicalRootTripleShared fineRoots)
    (physicalRootTripleRight fineRoots)

/-- A positive mixed-pattern numerator reduces to one explicit physical
character/fusion summand.  This is the exact local theorem still absent from
the existing one-cube production modules. -/
structure MixedPatternPhysicalSummandCertificate
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat)
    (law : ThreeBlockOverlapFiniteLaw EdgeLabelling) where
  physical : EdgeLabelling
  physical_mem : physical ∈
    boundedEdgeLabellings cutoff (List.range (plaquetteEdgeCount volume))
  mixed_pattern : threeBlockPattern law physical = (false, false, true)
  raw_character_fusion_weight_pos :
    (0 : Q') < parametricKPhysicalTerm
      coupling cutoff volume physical

private theorem listQSum_member_le_physical {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs →
      value x ≤ listQSum value xs
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, x, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst x
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun y _ => hvalue y))
      · have ih := listQSum_member_le_physical value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih hmono

theorem mixedPatternEventNumerator_pos_of_physicalSummand
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat)
    (law : ThreeBlockOverlapFiniteLaw EdgeLabelling)
    (certificate : MixedPatternPhysicalSummandCertificate
      coupling hcoupling cutoff volume law) :
    (0 : Q') < parametricKEventNumerator coupling cutoff volume
      (threeBlockPatternEvent law (false, false, true)) := by
  let event := threeBlockPatternEvent law (false, false, true)
  have hevent : event certificate.physical = true := by
    unfold event threeBlockPatternEvent
    simp [certificate.mixed_pattern]
  have hterm : parametricKEventTerm coupling cutoff volume event
      certificate.physical =
        parametricKPhysicalTerm coupling cutoff volume
          certificate.physical := by
    unfold parametricKEventTerm
    rw [if_pos hevent]
  have hle : parametricKEventTerm coupling cutoff volume event
        certificate.physical ≤
      parametricKEventNumerator coupling cutoff volume event := by
    unfold parametricKEventNumerator
    exact listQSum_member_le_physical
      (parametricKEventTerm coupling cutoff volume event)
      (parametricKEventTerm_nonnegative
        hcoupling cutoff volume event)
      _ certificate.physical_mem
  rw [hterm] at hle
  exact Q'.pos_of_lt_of_le
    certificate.raw_character_fusion_weight_pos hle

/-- Terminal exact residual for this route: one positive mixed summand for
each of the actual fine and activity-matched coarse laws on the same genuine
three-cube block geometry.  The global normalized marginal identities are
already theorems above. -/
structure ThreeCubeFineCoarseMixedSummandInput
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (roots : ThreeCubeBlockRootData volume) where
  fine : MixedPatternPhysicalSummandCertificate
    fineCoupling hfine cutoff volume
    (activityMatchedFineThreeRootLaw
      fineCoupling hfine cutoff volume roots.fineRoots)
  coarse : MixedPatternPhysicalSummandCertificate
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine) cutoff volume
    (activityMatchedCoarseThreeRootLaw
      fineCoupling hfine cutoff volume roots.coarseRoots)

theorem threeCubeFineCoarseMixedPatternMass_pos
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (roots : ThreeCubeBlockRootData volume)
    (input : ThreeCubeFineCoarseMixedSummandInput
      fineCoupling hfine cutoff volume roots) :
    (0 : Q') < threeBlockPatternMass
        (activityMatchedFineThreeRootLaw
          fineCoupling hfine cutoff volume roots.fineRoots)
        (false, false, true) ∧
      (0 : Q') < threeBlockPatternMass
        (activityMatchedCoarseThreeRootLaw
          fineCoupling hfine cutoff volume roots.coarseRoots)
        (false, false, true) := by
  have hfineNumerator :=
    mixedPatternEventNumerator_pos_of_physicalSummand
      fineCoupling hfine cutoff volume _ input.fine
  have hcoarseNumerator :=
    mixedPatternEventNumerator_pos_of_physicalSummand
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine)
      cutoff volume _ input.coarse
  have hfineRatio :=
    activityMatchedFineThreeRootPatternMass_eqv_character_ratio
      fineCoupling hfine cutoff volume roots.fineRoots
      (false, false, true)
  have hcoarseRatio :=
    activityMatchedCoarseThreeRootPatternMass_eqv_character_ratio
      fineCoupling hfine cutoff volume roots.coarseRoots
      (false, false, true)
  constructor
  · have hratioPos := Q'.divPos_pos _ _
      (couplingKPhysicalPartition_pos hfine cutoff volume)
      hfineNumerator
    exact Q'.pos_of_lt_of_le hratioPos (Q'.ge_of_eqv hfineRatio)
  · have hratioPos := Q'.divPos_pos _ _
      (couplingKPhysicalPartition_pos
        (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
      hcoarseNumerator
    exact Q'.pos_of_lt_of_le hratioPos (Q'.ge_of_eqv hcoarseRatio)

#print axioms physicalCubeCornerFaces_pairwise_overlap
#print axioms closedCubeFineSlotPartition_eqv_two_character_weights
#print axioms closedCubeFineSlotKernel_eqv_half
#print axioms closedCubeCornerThreeBlockLaw
#print axioms closedCubeCornerThreeBlockPattern_diagonal
#print axioms closedCubeCornerPatternMass_mixed_eqv_zero
#print axioms closedCubeIndependentPositiveCoupling
#print axioms closedCubeIndependent_cross_character_expression
#print axioms closedCubeIndependent_outgoing_false_eqv_quarter
#print axioms closedCubeIndependent_incoming_true_eqv_quarter
#print axioms closedCubeIndependent_outgoing_false_le_quarter
#print axioms closedCubeCorner_no_patternMatch
#print axioms closedCubeCorner_not_mixedCellAmplitude
#print axioms normalizedPhysicalThreeRootLaw
#print axioms normalizedPhysicalThreeRootPatternMass_eqv_character_ratio
#print axioms activityMatchedFineThreeRootPatternMass_eqv_character_ratio
#print axioms activityMatchedCoarseThreeRootPatternMass_eqv_character_ratio
#print axioms mixedPatternEventNumerator_pos_of_physicalSummand
#print axioms threeCubeFineCoarseMixedPatternMass_pos

end YMGap.Continuum.Z4ThreeBlockPhysicalCubeLeakage
