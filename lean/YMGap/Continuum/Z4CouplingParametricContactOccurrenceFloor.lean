/-
# Coupling-parametric contact deletion and local occurrence floors

The anchor contact-deletion argument is geometric except for one input: the
activity of every face-pinned polymer layer is at most one half.  This module
proves that cutoff-one canonical polymer activities are monotone in every
nonnegative rational coupling.  Consequently the proved anchor half bound,
and hence the complete finite contact-deletion estimate, persists at every
coupling below the anchor.

The final specialization applies the resulting uniform estimate to the
six-face coarse unit cube at the exact activity-matched coupling
`2 * anchorCoupling^4`.  Its contact cover has cost at most `2^150`, uniformly
in the containing box.  This is a finite-volume occurrence floor, not an RG
defect estimate or a continuum-limit theorem.
-/

import YMGap.Continuum.FiniteCompatibilityRootInsertion
import YMGap.Continuum.Z4CanonicalContactLayerDeletion
import YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw

namespace YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityLayerDeletion
open YMGap.Continuum.FiniteCompatibilityMarkedBound
open YMGap.Continuum.FiniteCompatibilityRootInsertion
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalContactLayerDeletion
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Cutoff-one activity monotonicity -/

private theorem cutoffOneCoefficient_nonnegative_local
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (spin : Nat) :
    (0 : Q') ≤ coeffAt (heatKernelPacket 1 coupling) spin := by
  by_cases hspin : spin < 2
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg hcoupling spin
  · have hlarge : 1 < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket 1 coupling) hlarge]
    exact Q'.le_refl' 0

private theorem cutoffOneCoefficient_mono_local
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) (spin : Nat) :
    coeffAt (heatKernelPacket 1 lower) spin ≤
      coeffAt (heatKernelPacket 1 upper) spin := by
  by_cases hspin : spin < 2
  · rw [coeffAt_heatKernelPacket hspin,
      coeffAt_heatKernelPacket hspin]
    exact coeffW_mono_w hlower hle spin
  · have hlarge : 1 < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket 1 lower) hlarge,
      coeffAt_of_gt (heatKernelPacket 1 upper) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_nonnegative_local
    (value : Nat → Q') (hvalue : ∀ edge, (0 : Q') ≤ value edge) :
    ∀ edges : List Nat, (0 : Q') ≤ eliminateLinks value edges
  | [] => Q'.zero_le_one
  | edge :: rest => Q'.mul_nonneg _ _ (hvalue edge)
      (eliminateLinks_nonnegative_local value hvalue rest)

private theorem eliminateLinks_mono_local
    (lower upper : Nat → Q')
    (hlower0 : ∀ edge, (0 : Q') ≤ lower edge)
    (hupper0 : ∀ edge, (0 : Q') ≤ upper edge)
    (hle : ∀ edge, lower edge ≤ upper edge) :
    ∀ edges : List Nat,
      eliminateLinks lower edges ≤ eliminateLinks upper edges
  | [] => Q'.le_refl' 1
  | edge :: rest => by
      have htail := eliminateLinks_mono_local lower upper
        hlower0 hupper0 hle rest
      have hlowerTail0 := eliminateLinks_nonnegative_local
        lower hlower0 rest
      have hupperHead0 := hupper0 edge
      have hhead : lower edge * eliminateLinks lower rest ≤
          upper edge * eliminateLinks lower rest :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (hle edge) hlowerTail0
      have hrest : upper edge * eliminateLinks lower rest ≤
          upper edge * eliminateLinks upper rest :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ htail hupperHead0
      exact Q'.le_trans' _ _ _ hhead hrest

theorem canonicalSurfaceActivity_mono_coupling
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) {n : Nat} {support : List Nat}
    (_hsupport : support ∈ cutoffOneFaceSupports n) :
    canonicalSurfaceActivity lower n support ≤
      canonicalSurfaceActivity upper n support := by
  have hupper : (0 : Q') ≤ upper := Q'.le_trans' _ _ _ hlower hle
  have hface :
      parametricPhysicalFaceFactor lower n (componentLabel support) ≤
        parametricPhysicalFaceFactor upper n (componentLabel support) := by
    unfold parametricPhysicalFaceFactor
    apply eliminateLinks_mono_local
    · intro edge
      exact cutoffOneCoefficient_nonnegative_local hlower
        (componentLabel support edge)
    · intro edge
      exact cutoffOneCoefficient_nonnegative_local hupper
        (componentLabel support edge)
    · intro edge
      exact cutoffOneCoefficient_mono_local hlower hle
        (componentLabel support edge)
  have hlink0 : (0 : Q') ≤
      explicitLinkMultiplicityProduct 1 n (componentLabel support)
        ((enumerate (distinctBoxLinks n)).filter
          (linkTouchesExcitationB n (componentLabel support))) :=
    explicitLinkMultiplicityProduct_nonnegative 1 n
      (componentLabel support) _
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hface hlink0

theorem canonicalSurfacePolymer_activity_le_anchor_of_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    canonicalSurfaceActivity coupling n polymer ≤
      canonicalSurfaceActivity anchorCoupling n polymer :=
  canonicalSurfaceActivity_mono_coupling hcoupling hle
    (canonicalSurfacePolymer_mem_faceSupports hpolymer)

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ xs : List A,
    (∀ item, item ∈ xs → lower item ≤ upper item) →
      listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

/-! ## 2. The anchor pinned-layer estimate persists below the anchor -/

def couplingPinnedLayerActivity
    (coupling : Q') (n rootId : Nat) : Q' :=
  markedActivitySum (canonicalSurfaceActivity coupling n)
    (canonicalContainsFaceB rootId) (canonicalSurfacePolymers n)

theorem couplingPinnedLayerActivity_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (n rootId : Nat) :
    couplingPinnedLayerActivity coupling n rootId ≤
      canonicalPinnedLayerActivity n rootId := by
  unfold couplingPinnedLayerActivity canonicalPinnedLayerActivity
    markedActivitySum
  apply listQSum_mono_local
  intro polymer hpolymer
  have hambient := (List.mem_filter.mp hpolymer).1
  exact canonicalSurfacePolymer_activity_le_anchor_of_le
    hcoupling hle hambient

theorem couplingPinnedLayerActivity_le_half
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (n rootId : Nat) :
    couplingPinnedLayerActivity coupling n rootId ≤
      Q'.mkPos 1 2 (by decide) :=
  Q'.le_trans' _ _ _
    (couplingPinnedLayerActivity_le_anchor hcoupling hle n rootId)
    (canonicalPinnedLayerActivity_le_half n rootId)

/-! ## 3. Coupling-parametric contact-layer deletion -/

theorem canonicalPolymerPartition_le_contactDeleted_of_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (n : Nat) (root : List Nat) :
    canonicalPolymerPartition coupling n (canonicalSurfacePolymers n) ≤
      (Q'.ofNat 2) ^ (canonicalContactFaceCandidates n root).length *
        canonicalPolymerPartition coupling n
          (canonicalContactDeletedAmbient n root) := by
  unfold canonicalPolymerPartition canonicalContactDeletedAmbient
  apply partition_le_two_pow_mul_deleteMarkedLayers
    (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity coupling n)
    (canonicalSurfaceActivity_nonnegative hcoupling n)
    (fun face polymer => canonicalContainsFaceB face polymer)
    (canonicalContactFaceCandidates n root)
    (canonicalSurfacePolymers n)
  intro face _
  change couplingPinnedLayerActivity coupling n face ≤
    Q'.mkPos 1 2 (by decide)
  exact couplingPinnedLayerActivity_le_half hcoupling hle n face

/-! ## 4. Parametric root insertion and normalization -/

theorem couplingCanonicalPolymerPartition_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (n : Nat) (ambient : List (List Nat)) :
    (0 : Q') ≤ canonicalPolymerPartition coupling n ambient := by
  unfold canonicalPolymerPartition
  exact partition_nonnegative
    (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity coupling n)
    (canonicalSurfaceActivity_nonnegative hcoupling n) ambient

theorem couplingCanonicalPolymerPartition_one_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (n : Nat) (ambient : List (List Nat)) :
    (1 : Q') ≤ canonicalPolymerPartition coupling n ambient := by
  unfold canonicalPolymerPartition
  exact partition_ge_one
    (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity coupling n)
    (canonicalSurfaceActivity_nonnegative hcoupling n) ambient

theorem couplingCanonicalPolymerPartition_pos
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (n : Nat) (ambient : List (List Nat)) :
    (0 : Q') < canonicalPolymerPartition coupling n ambient :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (by decide)
    (couplingCanonicalPolymerPartition_one_le hcoupling n ambient)

theorem canonicalContactDeletedAmbient_nodup
    (n : Nat) (root : List Nat) :
    (canonicalContactDeletedAmbient n root).Nodup := by
  unfold canonicalContactDeletedAmbient
  exact deleteMarkedLayers_nodup
    (fun face polymer => canonicalContainsFaceB face polymer)
    (canonicalContactFaceCandidates n root)
    (canonicalSurfacePolymers_nodup n)

theorem canonicalRoot_not_mem_contactDeleted
    {n : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers n) :
    root ∉ canonicalContactDeletedAmbient n root := by
  intro hrootDeleted
  obtain ⟨face, hface⟩ :=
    canonicalSurfacePolymers_allNonempty n root hroot
  have hfalse : canonicalPolymerCompatibleB n root root = false :=
    canonicalPolymerCompatibleB_false_of_contact hface hface
      (Or.inl rfl)
  have htrue := canonicalContactDeletedAmbient_survivor_compatible
    hrootDeleted
  rw [hfalse] at htrue
  cases htrue

theorem couplingRoot_activity_mul_deletedPartition_le_numerator
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {n : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers n) :
    canonicalSurfaceActivity coupling n root *
        canonicalPolymerPartition coupling n
          (canonicalContactDeletedAmbient n root) ≤
      canonicalPolymerEventNumerator coupling n
        (canonicalSurfacePolymers n)
        (familyContainsPolymerB root) := by
  have hgeneric := root_weight_mul_partition_le_occurrenceNumerator
    (canonicalPolymerCompatibleB n)
    (canonicalPolymerCompatibleB_symm n)
    (canonicalSurfaceActivity coupling n)
    (canonicalSurfaceActivity_nonnegative hcoupling n)
    (canonicalSurfacePolymers n)
    (canonicalContactDeletedAmbient n root)
    root
    (canonicalSurfacePolymers_nodup n)
    (canonicalContactDeletedAmbient_nodup n root)
    hroot
    (canonicalRoot_not_mem_contactDeleted hroot)
    (fun atom hatom =>
      mem_deleteMarkedLayers_source
        (fun face candidate => canonicalContainsFaceB face candidate)
        (canonicalContactFaceCandidates n root)
        (canonicalSurfacePolymers n) atom hatom)
    (fun atom hatom =>
      canonicalContactDeletedAmbient_survivor_compatible hatom)
  have hevent :
      (fun family => memberB family root) =
        familyContainsPolymerB root := by
    funext family
    apply Bool.eq_iff_iff.mpr
    simp [memberB, familyContainsPolymerB]
  rw [hevent] at hgeneric
  simpa only [canonicalPolymerPartition,
    canonicalPolymerEventNumerator] using hgeneric

def couplingCanonicalPolymerOccurrenceProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (n : Nat) (root : List Nat) : Q' :=
  Q'.divPos
    (canonicalPolymerEventNumerator coupling n
      (canonicalSurfacePolymers n) (familyContainsPolymerB root))
    (canonicalPolymerPartition coupling n (canonicalSurfacePolymers n))
    (couplingCanonicalPolymerPartition_pos hcoupling n
      (canonicalSurfacePolymers n))

/-! ## 5. Identification with the physical cutoff-one cylinder law -/

private theorem listQSum_mask_eq_filter_local {A : Type}
    (weight : A → Q') (event : A → Bool) : ∀ xs : List A,
    listQSum (fun item => if event item then weight item else 0) xs ≈
      listQSum weight (xs.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head with
      | false =>
          simp only [hevent, Bool.false_eq_true, if_false,
            List.filter_cons, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum weight (tail.filter event)) _
            (Q'.add_eqv_congr' (Q'.eqv_refl 0)
              (listQSum_mask_eq_filter_local weight event tail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [hevent, if_true, List.filter_cons, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_mask_eq_filter_local weight event tail)

theorem cutoffOneAmbientMaskedEventNumerator_eqv_canonicalPolymer
    (coupling : Q') (n : Nat) (event : List (List Nat) → Bool) :
    cutoffOneAmbientMaskedEventNumerator coupling n event ≈
      canonicalPolymerEventNumerator coupling n
        (canonicalSurfacePolymers n) event := by
  let masked : List (List Nat) → Q' := fun family =>
    if event family
    then canonicalSurfaceFamilyActivity coupling n family else 0
  have hperm :
      listQSum masked (ambientOrderedExactGas n) ≈
        listQSum masked (canonicalCompatibleAmbientFamilies n) :=
    listQSum_perm masked (ambientOrderedExactGas_perm_compatibleFamilies n)
  have hfilter :
      listQSum masked (canonicalCompatibleAmbientFamilies n) ≈
        listQSum (canonicalSurfaceFamilyActivity coupling n)
          ((canonicalCompatibleAmbientFamilies n).filter event) := by
    dsimp only [masked]
    exact listQSum_mask_eq_filter_local
      (canonicalSurfaceFamilyActivity coupling n) event
      (canonicalCompatibleAmbientFamilies n)
  have hcanonical :
      canonicalPolymerEventNumerator coupling n
          (canonicalSurfacePolymers n) event ≈
        listQSum (canonicalSurfaceFamilyActivity coupling n)
          ((canonicalCompatibleAmbientFamilies n).filter event) := by
    unfold canonicalPolymerEventNumerator eventNumerator
    rw [genericCompatibleFamilies_eq_canonical]
    exact listQSum_congr
      (fun family => Q'.eqv_of_eq
        (genericFamilyWeight_eq_canonical coupling n family)) _
  unfold cutoffOneAmbientMaskedEventNumerator
  dsimp only [masked] at hperm
  exact Q'.eqv_trans _ _ _ hperm
    (Q'.eqv_trans _ _ _ hfilter (Q'.eqv_symm hcanonical))

theorem parametricKEventNumerator_one_eqv_canonicalPolymer
    (coupling : Q') (n : Nat) (event : List (List Nat) → Bool) :
    parametricKEventNumerator coupling 1 n
        (cutoffOneLiftedFamilyEvent n event) ≈
      canonicalPolymerEventNumerator coupling n
        (canonicalSurfacePolymers n) event :=
  Q'.eqv_trans _ _ _
    (parametricKEventNumerator_one_eqv_ambientMasked
      coupling n event)
    (cutoffOneAmbientMaskedEventNumerator_eqv_canonicalPolymer
      coupling n event)

theorem couplingKPhysicalPartition_one_eqv_canonicalPolymer
    (coupling : Q') (n : Nat) :
    parametricKPhysicalPartition coupling 1 n ≈
      canonicalPolymerPartition coupling n
        (canonicalSurfacePolymers n) :=
  Q'.eqv_trans _
    (parametricLocalizedSpinFoamPartition coupling n) _
    (parametricKPhysicalPartition_one_eqv_localized coupling n)
    (Q'.eqv_trans _
      (parametricCanonicalCompatibleAmbientPartition coupling n) _
      (parametricLocalizedSpinFoamPartition_eq_correctedPolymerPartition
        coupling n)
      (Q'.eqv_symm
        (canonicalPolymerPartition_eqv_parametric coupling n)))

theorem couplingKFamilyEventProbability_one_eqv_canonicalOccurrence
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (n : Nat) (root : List Nat) :
    couplingKFamilyEventProbability coupling hcoupling 1 n
        (familyContainsPolymerB root) ≈
      couplingCanonicalPolymerOccurrenceProbability
        coupling hcoupling n root := by
  unfold couplingKFamilyEventProbability
    couplingCanonicalPolymerOccurrenceProbability
  exact YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder.divPos_eqv_congr
    (couplingKPhysicalPartition_pos hcoupling 1 n)
    (couplingCanonicalPolymerPartition_pos hcoupling n
      (canonicalSurfacePolymers n))
    (parametricKEventNumerator_one_eqv_canonicalPolymer
      coupling n (familyContainsPolymerB root))
    (couplingKPhysicalPartition_one_eqv_canonicalPolymer coupling n)

/-! ## 6. A generic contact-cost occurrence floor -/

def canonicalRootContactCost (n : Nat) (root : List Nat) : Q' :=
  (Q'.ofNat 2) ^ (canonicalContactFaceCandidates n root).length

theorem canonicalRootContactCost_pos (n : Nat) (root : List Nat) :
    (0 : Q') < canonicalRootContactCost n root := by
  unfold canonicalRootContactCost
  exact YMGap.Continuum.HKPos.pow_pos (by decide) _

def couplingCanonicalRootContactFloor
    (coupling : Q') (n : Nat) (root : List Nat) : Q' :=
  Q'.divPos (canonicalSurfaceActivity coupling n root)
    (canonicalRootContactCost n root)
    (canonicalRootContactCost_pos n root)

theorem couplingCanonicalRootContactFloor_pos
    {coupling : Q'} {n : Nat} {root : List Nat}
    (hactivity : (0 : Q') <
      canonicalSurfaceActivity coupling n root) :
    (0 : Q') < couplingCanonicalRootContactFloor coupling n root := by
  unfold couplingCanonicalRootContactFloor
  exact Q'.divPos_pos _ _ (canonicalRootContactCost_pos n root)
    hactivity

theorem couplingCanonicalRootContactFloor_le_probability
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {n : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers n) :
    couplingCanonicalRootContactFloor coupling n root ≤
      couplingCanonicalPolymerOccurrenceProbability
        coupling hcoupling n root := by
  let deletedPartition := canonicalPolymerPartition coupling n
    (canonicalContactDeletedAmbient n root)
  let numerator := canonicalPolymerEventNumerator coupling n
    (canonicalSurfacePolymers n) (familyContainsPolymerB root)
  have hdeleted0 : (0 : Q') ≤ deletedPartition := by
    unfold deletedPartition
    exact couplingCanonicalPolymerPartition_nonnegative hcoupling n _
  have hpartition :
      canonicalPolymerPartition coupling n (canonicalSurfacePolymers n) ≤
        canonicalRootContactCost n root * deletedPartition := by
    unfold canonicalRootContactCost deletedPartition
    exact canonicalPolymerPartition_le_contactDeleted_of_le_anchor
      hcoupling hle n root
  have hinsertion :
      canonicalSurfaceActivity coupling n root * deletedPartition ≤
        numerator := by
    unfold deletedPartition numerator
    exact couplingRoot_activity_mul_deletedPartition_le_numerator
      hcoupling hroot
  have hfloor0 : (0 : Q') ≤
      couplingCanonicalRootContactFloor coupling n root := by
    unfold couplingCanonicalRootContactFloor Q'.divPos
    exact Q'.mul_nonneg _ _
      (canonicalSurfaceActivity_nonnegative hcoupling n root)
      (Q'.le_of_lt
        (Q'.recipPos_pos _ (canonicalRootContactCost_pos n root)))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    hpartition hfloor0
  have hcollapse :
      couplingCanonicalRootContactFloor coupling n root *
          (canonicalRootContactCost n root * deletedPartition) ≈
        canonicalSurfaceActivity coupling n root * deletedPartition := by
    refine Q'.eqv_trans _
      ((couplingCanonicalRootContactFloor coupling n root *
          canonicalRootContactCost n root) * deletedPartition) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    apply Q'.mul_eqv_congr_right
    unfold couplingCanonicalRootContactFloor
    exact Q'.divPos_mul_eqv _ _
      (canonicalRootContactCost_pos n root)
  have hmul :
      couplingCanonicalRootContactFloor coupling n root *
          canonicalPolymerPartition coupling n
            (canonicalSurfacePolymers n) ≤ numerator :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse) hinsertion)
  unfold couplingCanonicalPolymerOccurrenceProbability
  exact Q'.le_divPos_of_mul_le numerator
    (canonicalPolymerPartition coupling n (canonicalSurfacePolymers n))
    (couplingCanonicalPolymerPartition_pos hcoupling n
      (canonicalSurfacePolymers n)) hmul

/-! ## 7. The activity-matched coarse unit cube: a uniform `2^150` floor -/

def activityMatchedCoarseUnitCubeOccurrenceCost : Q' :=
  (Q'.ofNat 2) ^ 150

theorem activityMatchedCoarseUnitCubeOccurrenceCost_pos :
    (0 : Q') < activityMatchedCoarseUnitCubeOccurrenceCost := by
  unfold activityMatchedCoarseUnitCubeOccurrenceCost
  exact YMGap.Continuum.HKPos.pow_pos (by decide) 150

theorem coarseUnitCubeContactFaceCandidates_length_le_one_fifty
    {n : Nat} (hn : 2 ≤ n) :
    (canonicalContactFaceCandidates n
      (transportPolymer 2 n coarseUnitCubeSupportIds)).length ≤ 150 := by
  have hlength := canonicalContactFaceCandidates_length_le n
    (transportPolymer 2 n coarseUnitCubeSupportIds)
  have htransport := transportPolymer_length_eq hn
    coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports
  rw [htransport, coarseUnitCubeSupportIds_length] at hlength
  simpa using hlength

private theorem qpow_le_succ_of_one_le_local {base : Q'}
    (hbase : (1 : Q') ≤ base) (exponent : Nat) :
    base ^ exponent ≤ base ^ (exponent + 1) := by
  rw [Q'.pow_succ]
  have hpow0 : (0 : Q') ≤ base ^ exponent :=
    Q'.pow_nonneg base
      (Q'.le_trans' _ _ _ Q'.zero_le_one hbase) exponent
  have hscaled : (1 : Q') * base ^ exponent ≤
      base * base ^ exponent :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hpow0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (base ^ exponent))) hscaled

private theorem qpow_add_mono_of_one_le_local {base : Q'}
    (hbase : (1 : Q') ≤ base) (first : Nat) :
    ∀ offset : Nat, base ^ first ≤ base ^ (first + offset)
  | 0 => Q'.le_refl' _
  | offset + 1 => by
      have hindex : first + (offset + 1) =
          (first + offset) + 1 := by omega
      rw [hindex]
      exact Q'.le_trans' _ _ _
        (qpow_add_mono_of_one_le_local hbase first offset)
        (qpow_le_succ_of_one_le_local hbase (first + offset))

private theorem qpow_mono_exponent_of_one_le_local {base : Q'}
    (hbase : (1 : Q') ≤ base) {first second : Nat}
    (hle : first ≤ second) : base ^ first ≤ base ^ second := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact qpow_add_mono_of_one_le_local hbase first offset

theorem activityMatchedCoarsePartition_le_cost_mul_deleted
    {n : Nat} (hn : 2 ≤ n) :
    canonicalPolymerPartition
        (unitCubeBlockCoupling anchorCoupling) n
        (canonicalSurfacePolymers n) ≤
      activityMatchedCoarseUnitCubeOccurrenceCost *
        canonicalPolymerPartition
          (unitCubeBlockCoupling anchorCoupling) n
          (canonicalContactDeletedAmbient n
            (transportPolymer 2 n coarseUnitCubeSupportIds)) := by
  let coupling := unitCubeBlockCoupling anchorCoupling
  let root := transportPolymer 2 n coarseUnitCubeSupportIds
  let deleted := canonicalContactDeletedAmbient n root
  have hcoupling : (0 : Q') ≤ coupling := by
    unfold coupling
    exact unitCubeBlockCoupling_nonnegative (by decide)
  have hraw := canonicalPolymerPartition_le_contactDeleted_of_le_anchor
    hcoupling anchor_unitCubeBlockCoupling_le n root
  have hlength := coarseUnitCubeContactFaceCandidates_length_le_one_fifty hn
  have hpow :
      (Q'.ofNat 2) ^ (canonicalContactFaceCandidates n root).length ≤
        (Q'.ofNat 2) ^ 150 := by
    exact qpow_mono_exponent_of_one_le_local (by decide) hlength
  have hdeleted0 : (0 : Q') ≤
      canonicalPolymerPartition coupling n deleted :=
    couplingCanonicalPolymerPartition_nonnegative hcoupling n deleted
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hdeleted0
  unfold activityMatchedCoarseUnitCubeOccurrenceCost
  exact Q'.le_trans' _ _ _ hraw hscaled

/-- The numerator is deliberately written as the refined cube's anchor
activity.  The exact bare block theorem identifies it with the shifted coarse
root activity used in every target volume. -/
def activityMatchedCoarseUnitCubeUniformOccurrenceFloor : Q' :=
  Q'.divPos
    (canonicalSurfaceActivity anchorCoupling 4
      dyadicUnitCubeSupportIds)
    activityMatchedCoarseUnitCubeOccurrenceCost
    activityMatchedCoarseUnitCubeOccurrenceCost_pos

theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_pos :
    (0 : Q') < activityMatchedCoarseUnitCubeUniformOccurrenceFloor := by
  unfold activityMatchedCoarseUnitCubeUniformOccurrenceFloor
  exact Q'.divPos_pos _ _
    activityMatchedCoarseUnitCubeOccurrenceCost_pos
    dyadicUnitCube_anchorActivity_pos

theorem activityMatchedCoarseRootActivity_transport
    {n : Nat} (hn : 2 ≤ n) :
    canonicalSurfaceActivity anchorCoupling 4
        dyadicUnitCubeSupportIds ≈
      canonicalSurfaceActivity
        (unitCubeBlockCoupling anchorCoupling) n
        (transportPolymer 2 n coarseUnitCubeSupportIds) := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (coarse_shifted_activity_eqv_dyadic_activity anchorCoupling))
    (canonicalSurfaceActivity_transport
      (unitCubeBlockCoupling anchorCoupling) hn
      coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports)

/-- A single positive exact rational lower-bounds the shifted coarse-cube
occurrence probability in every containing canonical box. -/
theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_probability
    {n : Nat} (hn : 2 ≤ n) :
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      couplingCanonicalPolymerOccurrenceProbability
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) n
        (transportPolymer 2 n coarseUnitCubeSupportIds) := by
  let coupling := unitCubeBlockCoupling anchorCoupling
  let root := transportPolymer 2 n coarseUnitCubeSupportIds
  let deletedPartition := canonicalPolymerPartition coupling n
    (canonicalContactDeletedAmbient n root)
  let numerator := canonicalPolymerEventNumerator coupling n
    (canonicalSurfacePolymers n) (familyContainsPolymerB root)
  have hcoupling : (0 : Q') ≤ coupling := by
    unfold coupling
    exact unitCubeBlockCoupling_nonnegative (by decide)
  have hroot : root ∈ canonicalSurfacePolymers n := by
    unfold root
    exact transportPolymer_mem_canonicalSurfacePolymers hn
      coarseUnitCubeSupportIds_mem_canonicalSurfacePolymers
  have hdeleted0 : (0 : Q') ≤ deletedPartition := by
    unfold deletedPartition
    exact couplingCanonicalPolymerPartition_nonnegative hcoupling n _
  have hpartition :
      canonicalPolymerPartition coupling n (canonicalSurfacePolymers n) ≤
        activityMatchedCoarseUnitCubeOccurrenceCost * deletedPartition := by
    exact activityMatchedCoarsePartition_le_cost_mul_deleted hn
  have hinsertion :
      canonicalSurfaceActivity coupling n root * deletedPartition ≤
        numerator := by
    unfold deletedPartition numerator
    exact couplingRoot_activity_mul_deletedPartition_le_numerator
      hcoupling hroot
  have hfloor0 : (0 : Q') ≤
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor :=
    Q'.le_of_lt
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor_pos
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    hpartition hfloor0
  have hcollapse :
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor *
          (activityMatchedCoarseUnitCubeOccurrenceCost * deletedPartition) ≈
        canonicalSurfaceActivity anchorCoupling 4
          dyadicUnitCubeSupportIds * deletedPartition := by
    refine Q'.eqv_trans _
      ((activityMatchedCoarseUnitCubeUniformOccurrenceFloor *
          activityMatchedCoarseUnitCubeOccurrenceCost) *
        deletedPartition) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    apply Q'.mul_eqv_congr_right
    unfold activityMatchedCoarseUnitCubeUniformOccurrenceFloor
    exact Q'.divPos_mul_eqv _ _
      activityMatchedCoarseUnitCubeOccurrenceCost_pos
  have hactivityScaled :
      canonicalSurfaceActivity anchorCoupling 4 dyadicUnitCubeSupportIds *
          deletedPartition ≤
        canonicalSurfaceActivity coupling n root * deletedPartition := by
    apply Q'.mul_le_mul_of_nonneg_right
    · unfold coupling root
      exact Q'.le_of_eqv (activityMatchedCoarseRootActivity_transport hn)
    · exact hdeleted0
  have hmul :
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor *
          canonicalPolymerPartition coupling n
            (canonicalSurfacePolymers n) ≤ numerator :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse)
        (Q'.le_trans' _ _ _ hactivityScaled hinsertion))
  unfold couplingCanonicalPolymerOccurrenceProbability
  exact Q'.le_divPos_of_mul_le numerator
    (canonicalPolymerPartition coupling n (canonicalSurfacePolymers n))
    (couplingCanonicalPolymerPartition_pos hcoupling n
      (canonicalSurfacePolymers n)) hmul

/-- The same volume-uniform floor for the production cutoff-one law on
physical spin labellings, after the exact support-family reindexing. -/
theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_physicalProbability
    {n : Nat} (hn : 2 ≤ n) :
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      couplingKFamilyEventProbability
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative
          (fineCoupling := anchorCoupling) (by decide)) 1 n
        (familyContainsPolymerB
          (transportPolymer 2 n coarseUnitCubeSupportIds)) := by
  have hcanonical :=
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_probability hn
  have hphysical :=
    couplingKFamilyEventProbability_one_eqv_canonicalOccurrence
      (unitCubeBlockCoupling_nonnegative
        (fineCoupling := anchorCoupling) (by decide)) n
      (transportPolymer 2 n coarseUnitCubeSupportIds)
  exact Q'.le_trans' _ _ _ hcanonical (Q'.ge_of_eqv hphysical)

#print axioms canonicalSurfaceActivity_mono_coupling
#print axioms canonicalSurfacePolymer_activity_le_anchor_of_le
#print axioms couplingPinnedLayerActivity_le_half
#print axioms canonicalPolymerPartition_le_contactDeleted_of_le_anchor
#print axioms canonicalRoot_not_mem_contactDeleted
#print axioms couplingRoot_activity_mul_deletedPartition_le_numerator
#print axioms cutoffOneAmbientMaskedEventNumerator_eqv_canonicalPolymer
#print axioms couplingKPhysicalPartition_one_eqv_canonicalPolymer
#print axioms couplingKFamilyEventProbability_one_eqv_canonicalOccurrence
#print axioms couplingCanonicalRootContactFloor_le_probability
#print axioms coarseUnitCubeContactFaceCandidates_length_le_one_fifty
#print axioms activityMatchedCoarsePartition_le_cost_mul_deleted
#print axioms activityMatchedCoarseRootActivity_transport
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_probability
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_physicalProbability

end YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
