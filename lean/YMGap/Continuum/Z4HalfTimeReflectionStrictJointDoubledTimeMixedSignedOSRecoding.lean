/-
# Cofinal recoding from signed strict-joint values to OS schedules

The signed spatial descent and the strict reflected Gram construction use two
different centered exhaustions.  This file begins their comparison at the
finite geometric level.  A root first re-encoded in a signed centered box and
then zero-extended to the corresponding uniform-shift box is literally the
canonical uniform shift of the original root.  Applied to a fixed strict-joint
stage, this identifies the whole receding signed root list with a later
strict-joint root list after one explicit zero-extension.

No probability equality, covariance premise, or OS contraction is asserted
here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialDescent
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSRecoding

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCrossVolumeStability
open YMGap.Continuum.Z4CouplingParametricCutoffTail
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentVolumeComparison
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem reassoc_cancel_local (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem three_edge_abs_sub_le_local
    (a b c d epsilonAC epsilonCD epsilonDB : Q')
    (hAC : Q'.abs (a - c) ≤ epsilonAC)
    (hCD : Q'.abs (c - d) ≤ epsilonCD)
    (hDB : Q'.abs (d - b) ≤ epsilonDB) :
    Q'.abs (a - b) ≤ epsilonAC + (epsilonCD + epsilonDB) := by
  have hdecompose :
      a - b ≈ (a - c) + ((c - d) + (d - b)) := by
    change a + (-b) ≈
      (a + (-c)) + ((c + (-d)) + (d + (-b)))
    have hinner :
        (c + (-d)) + (d + (-b)) ≈ c + (-b) :=
      reassoc_cancel_local c d (-b)
    have hrhs :
        (a + (-c)) + ((c + (-d)) + (d + (-b))) ≈
          a + (-b) := by
      refine Q'.eqv_trans _ ((a + (-c)) + (c + (-b))) _ ?_
        (reassoc_cancel_local a c (-b))
      exact Q'.add_eqv_congr_left (a + (-c)) _ _ hinner
    exact Q'.eqv_symm hrhs
  have htriangleOuter :=
    Q'.abs_add_le' (a - c) ((c - d) + (d - b))
  have htriangleInner := Q'.abs_add_le' (c - d) (d - b)
  have hinner := Q'.add_le_add hCD hDB
  have houter := Q'.add_le_add hAC
    (Q'.le_trans' _ _ _ htriangleInner hinner)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.le_trans' _ _ _ htriangleOuter houter)

private theorem abs_sub_triangle_local (a b c : Q') :
    Q'.abs (a - b) ≤ Q'.abs (a - c) + Q'.abs (c - b) := by
  have hdecompose : a - b ≈ (a - c) + (c - b) := by
    exact Q'.eqv_symm (reassoc_cancel_local a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.abs_add_le' (a - c) (c - b))

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

/-! ## 1. One root across the two centered schedules -/

/-- Re-encoding a root in the radius-`radius` signed centered box and then
zero-extending it to the box used by a uniform shift of size `radius` gives
exactly that canonical uniform shift.  The positivity of `base` is the honest
arithmetic condition making the intermediate centered box no larger than the
uniform-shift box. -/
theorem transport_centeredOffsetCanonicalRoot_eq_uniformShift
    {base radius : Nat} (hbase : 0 < base) (hbaseRadius : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    transportPolymer (centeredBoxBase radius)
        (uniformPaddedBase radius base)
        (centeredOffsetCanonicalRoot radius base root) =
      uniformShiftCanonicalRoot radius base root := by
  have hsmall : centeredBoxBase radius ≤ uniformPaddedBase radius base := by
    unfold centeredBoxBase uniformPaddedBase
    omega
  have hcentered : centeredOffsetCanonicalRoot radius base root ∈
      canonicalSurfacePolymers (centeredBoxBase radius) :=
    centeredOffsetCanonicalRoot_canonical hbaseRadius hroot
  have hleft := transportPolymer_mem_canonicalSurfacePolymers
    hsmall hcentered
  have hright := uniformShiftCanonicalRoot_canonical
    (padding := radius) hroot
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport hleft hright
  have htransport := transportPolymer_sameSupport hsmall
    (canonicalSurfacePolymer_mem_faceSupports hcentered)
  have hcenteredSupport := centeredOffsetCanonicalRoot_sameSupport
    hbaseRadius hroot
  have huniformSupport := uniformShiftCanonicalRoot_sameSupport
    (padding := radius) hroot
  exact sameSupport_trans (sameSupport_symm htransport)
    (sameSupport_trans hcenteredSupport
      (sameSupport_symm huniformSupport))

/-! ## 2. Arithmetic alignment of a fixed strict stage -/

/-- The canonical base of the fixed strict-joint centered chart. -/
def strictJointSignedFixedBase (base fixedStage : Nat) : Nat :=
  centeredBoxBase (strictQueryBase base + fixedStage)

/-- The later strict-joint stage whose roots have the same natural-coordinate
support as signed receding stage `recedingStage`. -/
def strictJointSignedCofinalStage
    (base fixedStage recedingStage : Nat) : Nat :=
  fixedStage + strictJointSignedFixedBase base fixedStage + recedingStage

theorem strictJointSignedFixedBase_pos (base fixedStage : Nat) :
    0 < strictJointSignedFixedBase base fixedStage := by
  unfold strictJointSignedFixedBase centeredBoxBase
  omega

theorem strictJointSigned_recedingBase_le_cofinalBase
    (base fixedStage recedingStage : Nat) :
    centeredRecedingStageBase
        (strictJointSignedFixedBase base fixedStage) recedingStage ≤
      centeredBoxBase
        (strictQueryBase base +
          strictJointSignedCofinalStage base fixedStage recedingStage) := by
  unfold centeredRecedingStageBase centeredRecedingStageRadius
    strictJointSignedCofinalStage strictJointSignedFixedBase
    strictQueryBase uniformPaddedBase centeredBoxBase
  omega

theorem strictJointSigned_cofinalBase_eq_uniformPadded
    (base fixedStage recedingStage : Nat) :
    centeredBoxBase
        (strictQueryBase base +
          strictJointSignedCofinalStage base fixedStage recedingStage) =
      uniformPaddedBase
        (strictJointSignedFixedBase base fixedStage + recedingStage)
        (strictJointSignedFixedBase base fixedStage) := by
  unfold strictJointSignedCofinalStage strictJointSignedFixedBase
    strictQueryBase uniformPaddedBase centeredBoxBase
  omega

/-! ## 3. Whole strict-joint root-list recoding -/

/-- After zero-extension to the explicit cofinal strict box, the signed
receding roots based at a fixed strict stage are literally the roots of the
later strict stage. -/
theorem centeredRecedingStrictJointStageRoots_transport_eq_cofinal
    {base fixedStage recedingStage : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    let fixedBase := strictJointSignedFixedBase base fixedStage
    let smallBase := centeredRecedingStageBase fixedBase recedingStage
    let laterStage :=
      strictJointSignedCofinalStage base fixedStage recedingStage
    let largeBase := centeredBoxBase (strictQueryBase base + laterStage)
    transportedCylinderRoots smallBase largeBase
        (centeredRecedingStageRoots fixedBase recedingStage
          (centralStrictJointCenteredStageRoots
            base fixedStage roots)) =
      centralStrictJointCenteredStageRoots base laterStage roots := by
  dsimp only
  unfold centeredRecedingStageRoots centeredRecedingStageRadius
    centeredOffsetCylinderRoots transportedCylinderRoots
    centralStrictJointCenteredStageRoots
  simp only [List.map_map]
  apply List.map_congr_left
  intro source hsource
  simp only [Function.comp_apply]
  have hsourceCanonical :=
    centralStrictJointCenteredSourceRoots_canonical hroots source hsource
  have hfixedCanonical := uniformShiftCanonicalRoot_canonical
    (padding := fixedStage) hsourceCanonical
  rw [strictJointCenteredStageBase_eq] at hfixedCanonical
  have htransport := transport_centeredOffsetCanonicalRoot_eq_uniformShift
    (strictJointSignedFixedBase_pos base fixedStage)
    (Nat.le_add_right
      (strictJointSignedFixedBase base fixedStage) recedingStage)
    hfixedCanonical
  rw [← strictJointSigned_cofinalBase_eq_uniformPadded
    base fixedStage recedingStage] at htransport
  unfold centeredRecedingStageBase centeredRecedingStageRadius
  rw [htransport]
  have hadd := uniformShiftCanonicalRoot_add fixedStage
    (strictJointSignedFixedBase base fixedStage + recedingStage)
    hsourceCanonical
  rw [strictJointCenteredStageBase_eq] at hadd
  simpa only [strictJointSignedFixedBase,
    strictJointSignedCofinalStage, Nat.add_assoc] using hadd

/-! ## 4. Event-level consequence -/

theorem centeredRecedingStrictJointStageEvent_transport_eq_cofinal
    {base fixedStage recedingStage : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    let fixedBase := strictJointSignedFixedBase base fixedStage
    let smallBase := centeredRecedingStageBase fixedBase recedingStage
    let laterStage :=
      strictJointSignedCofinalStage base fixedStage recedingStage
    let largeBase := centeredBoxBase (strictQueryBase base + laterStage)
    targetCylinderEvent smallBase largeBase
        (centeredRecedingStageRoots fixedBase recedingStage
          (centralStrictJointCenteredStageRoots
            base fixedStage roots)) predicate =
      centralStrictJointCenteredCylinderEvent
        base laterStage roots predicate := by
  dsimp only
  unfold targetCylinderEvent
    centralStrictJointCenteredCylinderEvent sourceCylinderEvent
  rw [centeredRecedingStrictJointStageRoots_transport_eq_cofinal hroots]

/-! ## 5. Cutoff-uniform cross-volume comparison -/

/-- At one arbitrary representation cutoff, the cofinal strict event and the
signed receding event differ only by the standard boundary tail at distance
`recedingStage + 1`.  This is the quantitative consequence of the exact
zero-extension recoding above. -/
theorem couplingParametricK_strictJointCofinal_abs_sub_signedReceding_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base fixedStage recedingStage : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    let fixedBase := strictJointSignedFixedBase base fixedStage
    let smallBase := centeredRecedingStageBase fixedBase recedingStage
    let laterStage :=
      strictJointSignedCofinalStage base fixedStage recedingStage
    let largeBase := centeredBoxBase (strictQueryBase base + laterStage)
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff largeBase
            (centralStrictJointCenteredCylinderEvent
              base laterStage roots predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff smallBase
            (centeredRecedingCylinderEvent fixedBase recedingStage
              (centralStrictJointCenteredStageRoots
                base fixedStage roots) predicate)) ≤
      spinSummedCylinderBoundaryEpsilon
        (roots.length + roots.length) (recedingStage + 1) := by
  dsimp only
  let fixedRoots := centralStrictJointCenteredStageRoots
    base fixedStage roots
  let smallRoots := centeredRecedingStageRoots
    (strictJointSignedFixedBase base fixedStage) recedingStage fixedRoots
  have hfixedRoots : ∀ root, root ∈ fixedRoots →
      root ∈ canonicalSurfacePolymers
        (strictJointSignedFixedBase base fixedStage) := by
    dsimp only [fixedRoots, strictJointSignedFixedBase]
    exact centralStrictJointCenteredStageRoots_canonical hroots
  have hsmallRoots : ∀ root, root ∈ smallRoots →
      root ∈ canonicalSurfacePolymers
        (centeredRecedingStageBase
          (strictJointSignedFixedBase base fixedStage) recedingStage) := by
    dsimp only [smallRoots]
    exact centeredRecedingStageRoots_canonical hfixedRoots
  have hinside : ∀ root, root ∈ smallRoots →
      PolymerInsideBox
        (centeredFaceQueryInner
          (strictJointSignedFixedBase base fixedStage) recedingStage)
        (centeredRecedingStageBase
          (strictJointSignedFixedBase base fixedStage) recedingStage) root := by
    dsimp only [smallRoots]
    exact centeredRecedingStageRoots_inside_originBox hfixedRoots
  have hbox :
      centeredFaceQueryInner
            (strictJointSignedFixedBase base fixedStage) recedingStage +
          (recedingStage + 1) =
        centeredRecedingStageBase
          (strictJointSignedFixedBase base fixedStage) recedingStage :=
    centeredFaceQueryInner_add_distance
      (strictJointSignedFixedBase base fixedStage) recedingStage
  have hsmall := strictJointSigned_recedingBase_le_cofinalBase
    base fixedStage recedingStage
  have hraw :=
    couplingParametricKCompatibleCylinderProbability_cross_volume_abs_sub_le
      hcoupling hle cutoff hsmall smallRoots hsmallRoots predicate
      hinside hbox
  have hevent :
      markedCylinderEvent
          (transportedCanonicalCylinderAtoms hsmall smallRoots hsmallRoots)
          predicate =
        centralStrictJointCenteredCylinderEvent base
          (strictJointSignedCofinalStage
            base fixedStage recedingStage) roots predicate := by
    exact Eq.trans
      (markedTransportedCylinderEvent_eq_target
        hsmall smallRoots hsmallRoots predicate)
      (centeredRecedingStrictJointStageEvent_transport_eq_cofinal
        hroots predicate)
  rw [hevent] at hraw
  have hlength : smallRoots.length = roots.length + roots.length := by
    dsimp only [smallRoots, fixedRoots]
    rw [centeredRecedingStageRoots_length,
      centralStrictJointCenteredStageRoots_length]
  simpa only [smallRoots, fixedRoots, sourceCylinderEvent,
    centeredRecedingCylinderEvent, hlength] using hraw

/-! ## 6. Alignment of the two scheduled rational sequences -/

/-- After aligning both derived representation cutoffs through one common
cutoff, a later strict-joint approximant differs from the signed receding
approximant by the standard joint half-power modulus. -/
theorem couplingParametricStrictJointCenteredSequence_cofinal_abs_sub_signedReceding_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base fixedStage recedingStage : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots predicate
            (strictJointSignedCofinalStage
              base fixedStage recedingStage) -
          couplingParametricCenteredRecedingCylinderSequence
            coupling hcoupling
            (strictJointSignedFixedBase base fixedStage)
            (centralStrictJointCenteredStageRoots
              base fixedStage roots)
            predicate recedingStage) ≤
      spinSummedJointCylinderCoefficient
          (roots.length + roots.length) *
        HalfPow.half ^ recedingStage := by
  let fixedBase := strictJointSignedFixedBase base fixedStage
  let fixedRoots := centralStrictJointCenteredStageRoots
    base fixedStage roots
  let laterStage := strictJointSignedCofinalStage
    base fixedStage recedingStage
  let smallBase := centeredRecedingStageBase fixedBase recedingStage
  let largeBase := centeredBoxBase (strictQueryBase base + laterStage)
  let smallEvent := centeredRecedingCylinderEvent
    fixedBase recedingStage fixedRoots predicate
  let largeEvent := centralStrictJointCenteredCylinderEvent
    base laterStage roots predicate
  let smallCutoff := centeredRecedingStageCutoff fixedBase recedingStage
  let largeCutoff := centralStrictJointCenteredStageCutoff base laterStage
  let commonCutoff := smallCutoff + largeCutoff
  have hsmallCutoff : smallCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hlargeCutoff : largeCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  let a := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling largeCutoff largeBase largeEvent
  let b := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling smallCutoff smallBase smallEvent
  let c := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff largeBase largeEvent
  let d := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff smallBase smallEvent
  have hlater : recedingStage ≤ laterStage := by
    dsimp only [laterStage, strictJointSignedCofinalStage]
    omega
  have hACRaw :=
    couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
      hcoupling hle largeEvent hlargeCutoff
  have hACLater : Q'.abs (a - c) ≤ HalfPow.half ^ laterStage := by
    dsimp only [a, c, largeCutoff, largeBase]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm _ _))
      hACRaw
  have hhalfLater : HalfPow.half ^ laterStage ≤
      HalfPow.half ^ recedingStage := by
    obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hlater
    rw [hoffset]
    exact ExpNeg.pow_half_antitone recedingStage offset
  have hAC : Q'.abs (a - c) ≤ HalfPow.half ^ recedingStage :=
    Q'.le_trans' _ _ _ hACLater hhalfLater
  have hCDRaw :=
    couplingParametricK_strictJointCofinal_abs_sub_signedReceding_le
      hcoupling hle commonCutoff hroots predicate
      (fixedStage := fixedStage) (recedingStage := recedingStage)
  have hCDCoefficient :
      Q'.abs (c - d) ≤
        spinSummedCylinderBoundaryCoefficient
            (roots.length + roots.length) *
          HalfPow.half ^ (recedingStage + 1) := by
    exact Q'.le_trans' _ _ _
      (by simpa only [c, d, largeBase, smallBase,
          largeEvent, smallEvent, laterStage, fixedBase, fixedRoots]
        using hCDRaw)
      (spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
        (roots.length + roots.length) (recedingStage + 1))
  have hhalfSucc : HalfPow.half ^ (recedingStage + 1) ≤
      HalfPow.half ^ recedingStage :=
    ExpNeg.pow_half_antitone recedingStage 1
  have hCD : Q'.abs (c - d) ≤
      spinSummedCylinderBoundaryCoefficient
          (roots.length + roots.length) *
        HalfPow.half ^ recedingStage :=
    Q'.le_trans' _ _ _ hCDCoefficient
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hhalfSucc
        (spinSummedCylinderBoundaryCoefficient_nonnegative
          (roots.length + roots.length)))
  have hDBRaw :=
    couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
      hcoupling hle smallEvent hsmallCutoff
  have hDB : Q'.abs (d - b) ≤ HalfPow.half ^ recedingStage := by
    simpa only [d, b, smallCutoff, smallBase] using hDBRaw
  have hchain := three_edge_abs_sub_le_local a b c d
    (HalfPow.half ^ recedingStage)
    (spinSummedCylinderBoundaryCoefficient
      (roots.length + roots.length) * HalfPow.half ^ recedingStage)
    (HalfPow.half ^ recedingStage) hAC hCD hDB
  have hreorder :
      HalfPow.half ^ recedingStage +
          (spinSummedCylinderBoundaryCoefficient
                (roots.length + roots.length) *
              HalfPow.half ^ recedingStage +
            HalfPow.half ^ recedingStage) ≈
        spinSummedJointCylinderCoefficient
            (roots.length + roots.length) *
          HalfPow.half ^ recedingStage := by
    let h := HalfPow.half ^ recedingStage
    let coefficient := spinSummedCylinderBoundaryCoefficient
      (roots.length + roots.length)
    have hinner :
        (coefficient + (1 : Q')) * h ≈ coefficient * h + h :=
      Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv coefficient (1 : Q') h)
        (Q'.add_eqv_congr'
          (Q'.eqv_refl (coefficient * h)) (Q'.one_mul_eqv h))
    have hright :
        spinSummedJointCylinderCoefficient
            (roots.length + roots.length) * h ≈
          h + (coefficient * h + h) := by
      unfold spinSummedJointCylinderCoefficient
      exact Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv (1 : Q')
          (spinSummedCylinderBoundaryCoefficient
            (roots.length + roots.length) + (1 : Q')) h)
        (Q'.add_eqv_congr' (Q'.one_mul_eqv h) hinner)
    exact Q'.eqv_symm hright
  change Q'.abs (a - b) ≤
    spinSummedJointCylinderCoefficient
        (roots.length + roots.length) *
      HalfPow.half ^ recedingStage
  exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv hreorder)

/-! ## 7. Constructive-real cofinal descent -/

/-- The strict-joint centered limit equals the signed receding value based at
any fixed strict stage.  This is a cofinal-exhaustion theorem derived from the
explicit cross-volume and cutoff estimates above, not a covariance axiom. -/
theorem couplingParametricStrictJointCenteredLimit_equiv_signedRecedingStage
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base fixedStage : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (couplingParametricStrictJointCenteredLimit
        coupling hcoupling hle predicate hroots)
      (couplingParametricCenteredRecedingCylinderLimitAtAnchor
        coupling hcoupling hle predicate
        (centralStrictJointCenteredStageRoots_canonical
          (stage := fixedStage) hroots)) := by
  let entryCoefficient := spinSummedJointCylinderCoefficient
    (roots.length + roots.length)
  let coefficient := entryCoefficient + entryCoefficient
  have hentryCoefficient : (0 : Q') ≤ entryCoefficient :=
    spinSummedJointCylinderCoefficient_nonnegative
      (roots.length + roots.length)
  have hcoefficient : (0 : Q') ≤ coefficient :=
    Q'.zero_le_add _ _ hentryCoefficient hentryCoefficient
  intro epsilon hepsilon
  let scaledTolerance := epsilon * Q'.invSucc coefficient.num.toNat
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
  have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
    ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
      hcoefficient (Q'.le_of_lt hepsilon)
  refine ⟨scaledTolerance.den, fun stage hstage => ?_⟩
  let laterStage := strictJointSignedCofinalStage
    base fixedStage stage
  have hstageLater : stage ≤ laterStage := by
    dsimp only [laterStage, strictJointSignedCofinalStage]
    omega
  let strictNow := couplingParametricStrictJointCenteredSequence
    coupling hcoupling base roots predicate stage
  let strictLater := couplingParametricStrictJointCenteredSequence
    coupling hcoupling base roots predicate laterStage
  let signedNow := couplingParametricCenteredRecedingCylinderSequence
    coupling hcoupling (strictJointSignedFixedBase base fixedStage)
    (centralStrictJointCenteredStageRoots base fixedStage roots)
    predicate stage
  have hstrictRaw :=
    couplingParametricStrictJointCenteredSequence_pair_abs_le
      hcoupling hle hstageLater hroots predicate
  have hstrict : Q'.abs (strictNow - strictLater) ≤
      entryCoefficient * HalfPow.half ^ stage := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          strictNow strictLater))
      (by simpa only [strictNow, strictLater, laterStage,
          entryCoefficient] using hstrictRaw)
  have hcross : Q'.abs (strictLater - signedNow) ≤
      entryCoefficient * HalfPow.half ^ stage := by
    simpa only [strictLater, signedNow, laterStage,
      entryCoefficient] using
      (couplingParametricStrictJointCenteredSequence_cofinal_abs_sub_signedReceding_le
        hcoupling hle hroots predicate
        (fixedStage := fixedStage) (recedingStage := stage))
  have htriangle := abs_sub_triangle_local strictNow signedNow strictLater
  have hsum := Q'.add_le_add hstrict hcross
  have hpointRaw : Q'.abs (strictNow - signedNow) ≤
      entryCoefficient * HalfPow.half ^ stage +
        entryCoefficient * HalfPow.half ^ stage :=
    Q'.le_trans' _ _ _ htriangle hsum
  have hreorder :
      entryCoefficient * HalfPow.half ^ stage +
          entryCoefficient * HalfPow.half ^ stage ≈
        coefficient * HalfPow.half ^ stage := by
    dsimp only [coefficient]
    exact Q'.eqv_symm
      (Q'.add_mul_eqv entryCoefficient entryCoefficient
        (HalfPow.half ^ stage))
  have hpoint : Q'.abs (strictNow - signedNow) ≤
      coefficient * HalfPow.half ^ stage :=
    Q'.le_trans' _ _ _ hpointRaw (Q'.le_of_eqv hreorder)
  have hhalf : HalfPow.half ^ stage ≤
      HalfPow.half ^ scaledTolerance.den := by
    obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
    rw [hoffset]
    exact ExpNeg.pow_half_antitone scaledTolerance.den offset
  have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
      scaledTolerance :=
    HalfPow.pow_half_le scaledTolerance hscaledPositive
  have hscaled : coefficient * HalfPow.half ^ stage ≤
      coefficient * scaledTolerance :=
    Q'.mul_le_mul_of_nonneg_left _ _ coefficient
      (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
  have habs : Q'.abs (strictNow - signedNow) ≤ epsilon :=
    Q'.le_trans' _ _ _ hpoint
      (Q'.le_trans' _ _ _ hscaled hscaledFinal)
  simpa only [couplingParametricStrictJointCenteredLimit_approx,
    couplingParametricCenteredRecedingCylinderLimitAtAnchor_approx,
    strictNow, signedNow] using
    (two_sided_add_of_abs_sub_le_local habs)

/-! ## 8. The translated strict diagonal in the signed presentation -/

/-- Canonicality of the whole time-translated root list.  Naming this proof
keeps the translated limit statement independent of a large proof-valued
`let` expression. -/
theorem timeShiftCanonicalRoots_canonical
    {base shift : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ root,
      root ∈ roots.map (timeShiftCanonicalRoot shift base) →
        root ∈ canonicalSurfacePolymers (base + shift) := by
  intro root hroot
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hroot
  exact timeShiftCanonicalRoot_canonical (hroots source hsource)

theorem strictJointSignedFixedBase_add_shift_eq_target
    (base shift fixedStage : Nat) :
    strictJointSignedFixedBase (base + shift) fixedStage =
      centeredBoxBase ((strictQueryBase base + fixedStage) + shift) := by
  unfold strictJointSignedFixedBase strictQueryBase uniformPaddedBase
    centeredBoxBase
  omega

/-- The centered Gram-entry limit for the time-translated strict cylinder is
the target signed-presentation value used by signed spatial descent. -/
theorem couplingParametricTranslatedStrictJointCenteredLimit_equiv_signedTarget
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (couplingParametricStrictJointCenteredLimit
        coupling hcoupling hle predicate
        (timeShiftCanonicalRoots_canonical
          (base := base) (shift := shift) (roots := roots) hroots))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (timeTranslatedStrictJointSignedPresentation
          base shift fixedStage roots predicate hroots)) := by
  have hbridge :=
    couplingParametricStrictJointCenteredLimit_equiv_signedRecedingStage
      hcoupling hle
      (timeShiftCanonicalRoots_canonical
        (base := base) (shift := shift) (roots := roots) hroots)
      predicate
      (fixedStage := fixedStage)
  have htarget : CReal.Equiv
      (couplingParametricCenteredRecedingCylinderLimitAtAnchor
        coupling hcoupling hle predicate
        (centralStrictJointCenteredStageRoots_canonical
          (stage := fixedStage)
          (timeShiftCanonicalRoots_canonical
            (base := base) (shift := shift) (roots := roots) hroots)))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (timeTranslatedStrictJointSignedPresentation
          base shift fixedStage roots predicate hroots)) := by
    apply CReal.Equiv_of_lifted_approx_equal
    intro stage
    apply YMGap.Constructive.TrigAdd.equiv_ofQ'_of_eqv
    change couplingParametricCenteredRecedingCylinderSequence
        coupling hcoupling
        (strictJointSignedFixedBase (base + shift) fixedStage)
        (centralStrictJointCenteredStageRoots (base + shift) fixedStage
          (roots.map (timeShiftCanonicalRoot shift base)))
        predicate stage ≈
      couplingParametricCenteredRecedingCylinderSequence
        coupling hcoupling
        (centeredBoxBase ((strictQueryBase base + fixedStage) + shift))
        (centralStrictJointCenteredStageRoots (base + shift) fixedStage
          (roots.map (timeShiftCanonicalRoot shift base)))
        predicate stage
    rw [strictJointSignedFixedBase_add_shift_eq_target]
    exact Q'.eqv_refl _
  exact CReal.Equiv.trans hbridge htarget

#print axioms transport_centeredOffsetCanonicalRoot_eq_uniformShift
#print axioms strictJointSigned_recedingBase_le_cofinalBase
#print axioms strictJointSigned_cofinalBase_eq_uniformPadded
#print axioms centeredRecedingStrictJointStageRoots_transport_eq_cofinal
#print axioms centeredRecedingStrictJointStageEvent_transport_eq_cofinal
#print axioms couplingParametricK_strictJointCofinal_abs_sub_signedReceding_le
#print axioms couplingParametricStrictJointCenteredSequence_cofinal_abs_sub_signedReceding_le
#print axioms couplingParametricStrictJointCenteredLimit_equiv_signedRecedingStage
#print axioms timeShiftCanonicalRoots_canonical
#print axioms strictJointSignedFixedBase_add_shift_eq_target
#print axioms couplingParametricTranslatedStrictJointCenteredLimit_equiv_signedTarget

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSRecoding
