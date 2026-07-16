/-
# Constructive centered limit of the strict reflected joint chart

The strict lower/upper support pair has already been recoded as a fixed
finite root list in one odd centered box.  This module proves that its
uniformly translated odd-box laws form a constructive Cauchy sequence.  The
earlier centered stage supplies a protected core of width exactly `earlier`,
so the finite-volume modulus decays geometrically while the marked
cardinality remains exactly `k + k`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.FiniteJointKernelPushforward
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricCutoffTail
open YMGap.Continuum.Z4CouplingParametricCylinderCofinal
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierTail
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4UniformShiftTargetCylinderStability
open Dir4

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The uniform-shift semigroup on canonical roots -/

private theorem sameSupport_map_local
    {left right : List Z4Plaq} (reindex : Z4Plaq → Z4Plaq)
    (hsupport : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map reindex) (right.map reindex) := by
  constructor
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.1 source hsource, rfl⟩
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.2 source hsource, rfl⟩

private theorem sameSupport_right_eq_local
    {left right target : List Z4Plaq}
    (hsupport : sameSupport (L := z4Chain.toLattice) left right)
    (heq : right = target) :
    sameSupport (L := z4Chain.toLattice) left target := by
  cases heq
  exact hsupport

theorem uniformShiftCanonicalRoot_add
    {base : Nat} (first second : Nat) {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    uniformShiftCanonicalRoot second (uniformPaddedBase first base)
        (uniformShiftCanonicalRoot first base root) =
      uniformShiftCanonicalRoot (first + second) base root := by
  have hfirstCanonical := uniformShiftCanonicalRoot_canonical
    (padding := first) hroot
  have hleftCanonical := uniformShiftCanonicalRoot_canonical
    (padding := second) hfirstCanonical
  have hrightCanonical := uniformShiftCanonicalRoot_canonical
    (padding := first + second) hroot
  have hbaseEq :
      uniformPaddedBase second (uniformPaddedBase first base) =
        uniformPaddedBase (first + second) base := by
    unfold uniformPaddedBase
    omega
  rw [← hbaseEq] at hrightCanonical
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    hleftCanonical hrightCanonical
  have hsecondSupport := uniformShiftCanonicalRoot_sameSupport
    (padding := second) hfirstCanonical
  have hfirstSupport := uniformShiftCanonicalRoot_sameSupport
    (padding := first) hroot
  have hnested := sameSupport_trans hsecondSupport
    (sameSupport_map_local (uniformShiftPlaquette second) hfirstSupport)
  have hmapEq :
      ((geometricPolymer base root).map
          (uniformShiftPlaquette first)).map
          (uniformShiftPlaquette second) =
        (geometricPolymer base root).map
          (uniformShiftPlaquette (first + second)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro plaquette _
    simp only [Function.comp_apply]
    exact uniformShiftPlaquette_comp first second plaquette
  have hnestedCommon := sameSupport_right_eq_local hnested hmapEq
  have hdirect := uniformShiftCanonicalRoot_sameSupport
    (padding := first + second) hroot
  rw [← hbaseEq] at hdirect
  exact sameSupport_trans hnestedCommon (sameSupport_symm hdirect)

/-! ## 2. Exact stage-to-stage recoding -/

theorem strictJointCenteredStageBase_eq_uniformPadded_between
    {base earlier later : Nat} (hstage : earlier ≤ later) :
    centeredBoxBase (strictQueryBase base + later) =
      uniformPaddedBase (later - earlier)
        (centeredBoxBase (strictQueryBase base + earlier)) := by
  unfold centeredBoxBase uniformPaddedBase
  omega

theorem centralStrictJointCenteredStageRoots_eq_uniformShift_between
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    centralStrictJointCenteredStageRoots base later roots =
      (centralStrictJointCenteredStageRoots base earlier roots).map
        (uniformShiftCanonicalRoot (later - earlier)
          (centeredBoxBase (strictQueryBase base + earlier))) := by
  unfold centralStrictJointCenteredStageRoots
  rw [List.map_map]
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply]
  have hsource := centralStrictJointCenteredSourceRoots_canonical
    hroots root hroot
  symm
  calc
    uniformShiftCanonicalRoot (later - earlier)
        (centeredBoxBase (strictQueryBase base + earlier))
        (uniformShiftCanonicalRoot earlier
          (strictJointCenteredSourceBase base) root) =
      uniformShiftCanonicalRoot (later - earlier)
        (uniformPaddedBase earlier
          (strictJointCenteredSourceBase base))
        (uniformShiftCanonicalRoot earlier
          (strictJointCenteredSourceBase base) root) := by
        rw [strictJointCenteredStageBase_eq]
    _ = uniformShiftCanonicalRoot
          (earlier + (later - earlier))
          (strictJointCenteredSourceBase base) root :=
      uniformShiftCanonicalRoot_add earlier (later - earlier) hsource
    _ = uniformShiftCanonicalRoot later
          (strictJointCenteredSourceBase base) root := by
      congr 2
      omega

def centralStrictJointCenteredCylinderEvent
    (base stage : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) : List (List Nat) → Bool :=
  sourceCylinderEvent
    (centralStrictJointCenteredStageRoots base stage roots) predicate

theorem centralStrictJointCenteredCylinderEvent_eq_uniformShift_between
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    centralStrictJointCenteredCylinderEvent base later roots predicate =
      uniformShiftTargetCylinderEvent (later - earlier)
        (centeredBoxBase (strictQueryBase base + earlier))
        (centralStrictJointCenteredStageRoots base earlier roots)
        predicate := by
  unfold centralStrictJointCenteredCylinderEvent
    sourceCylinderEvent uniformShiftTargetCylinderEvent
    uniformShiftedCylinderRoots
  rw [centralStrictJointCenteredStageRoots_eq_uniformShift_between
    hstage hroots]

/-! ## 3. The fixed source box is the protected shifted core -/

theorem centralStrictJointCenteredStageRoot_face_inside_sourceCore
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    {target : List Nat}
    (htarget : target ∈
      centralStrictJointCenteredStageRoots base stage roots)
    {face : Nat} (hface : face ∈ target) :
    insideShiftedBoxB (uniformNatLower stage)
        (strictJointCenteredSourceBase base)
        (boxPlaquetteAt
          (centeredBoxBase (strictQueryBase base + stage)) face) = true := by
  obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp htarget
  rw [← htargetEq] at hface
  have hsourceCanonical :=
    centralStrictJointCenteredSourceRoots_canonical hroots source hsource
  have htargetSupport := uniformShiftCanonicalRoot_sameSupport
    (padding := stage) hsourceCanonical
  rw [strictJointCenteredStageBase_eq] at htargetSupport
  have htargetGeom :
      boxPlaquetteAt (centeredBoxBase
          (strictQueryBase base + stage)) face ∈
        geometricPolymer
          (centeredBoxBase (strictQueryBase base + stage))
          (uniformShiftCanonicalRoot stage
            (strictJointCenteredSourceBase base) source) :=
    List.mem_map.mpr ⟨face, hface, rfl⟩
  have hmapped := htargetSupport.1 _ htargetGeom
  obtain ⟨sourcePlaquette, hsourcePlaquette, hplaquetteEq⟩ :=
    List.mem_map.mp hmapped
  rw [← hplaquetteEq]
  apply (insideShiftedBoxB_true_iff _ _ _).2
  have hbox := geometricPolymer_subset_box
    (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical)
    sourcePlaquette hsourcePlaquette
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := sourcePlaquette
  have hcoordinates := (mem_boxPlaquettes
    (((a, b, c, d), plane) : Z4Plaq)
    (strictJointCenteredSourceBase base)).1 hbox
  change a < strictJointCenteredSourceBase base ∧
    b < strictJointCenteredSourceBase base ∧
    c < strictJointCenteredSourceBase base ∧
    d < strictJointCenteredSourceBase base at hcoordinates
  simp only [uniformNatLower, uniformShiftPlaquette,
    uniformShiftVertex, cPlaq, vComp]
  exact ⟨by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

theorem centralStrictJointCenteredUniformShiftAtoms_core
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    let sourceBase :=
      centeredBoxBase (strictQueryBase base + earlier)
    let padding := later - earlier
    let sourceRoots :=
      centralStrictJointCenteredStageRoots base earlier roots
    let hsourceRoots : ∀ root, root ∈ sourceRoots →
        root ∈ canonicalSurfacePolymers sourceBase :=
      centralStrictJointCenteredStageRoots_canonical
        (stage := earlier) hroots
    ∀ target,
      target ∈ uniformShiftCylinderCanonicalAtoms
        padding sourceBase sourceRoots hsourceRoots →
      insideShiftedBoxB
        (addUniform (uniformShiftCellLower padding) earlier)
        (strictJointCenteredSourceBase base)
        (boxPlaquetteAt (uniformPaddedBase padding sourceBase)
          (uniformShiftCanonicalAtomStart target)) = true := by
  intro sourceBase padding sourceRoots hsourceRoots target htarget
  have htargetValue : target.val ∈
      (uniformShiftCylinderCanonicalAtoms
        padding sourceBase sourceRoots hsourceRoots).map Subtype.val :=
    List.mem_map.mpr ⟨target, htarget, rfl⟩
  rw [uniformShiftCylinderCanonicalAtoms_values] at htargetValue
  have htargetLate : target.val ∈
      centralStrictJointCenteredStageRoots base later roots := by
    rw [centralStrictJointCenteredStageRoots_eq_uniformShift_between
      hstage hroots]
    exact htargetValue
  have hcore := centralStrictJointCenteredStageRoot_face_inside_sourceCore
    hroots htargetLate (uniformShiftCanonicalAtomStart_mem target)
  have hbaseEq : uniformPaddedBase padding sourceBase =
      centeredBoxBase (strictQueryBase base + later) := by
    dsimp only [padding, sourceBase]
    exact (strictJointCenteredStageBase_eq_uniformPadded_between
      hstage).symm
  have hlowerEq :
      addUniform (uniformShiftCellLower padding) earlier =
        uniformNatLower later := by
    dsimp only [padding]
    simp only [addUniform, uniformShiftCellLower, uniformNatLower]
    rw [Nat.sub_add_cancel hstage]
  have hplaquetteEq := congrArg
    (fun ambient => boxPlaquetteAt ambient
      (uniformShiftCanonicalAtomStart target)) hbaseEq
  change boxPlaquetteAt (uniformPaddedBase padding sourceBase)
      (uniformShiftCanonicalAtomStart target) =
    boxPlaquetteAt (centeredBoxBase
      (strictQueryBase base + later))
      (uniformShiftCanonicalAtomStart target) at hplaquetteEq
  rw [hlowerEq, hplaquetteEq]
  exact hcore

/-! ## 4. Fixed-cutoff stage-to-stage volume modulus -/

theorem centralStrictJointCenteredStageSide
    (base stage : Nat) :
    strictJointCenteredSourceBase base + stage + stage =
      centeredBoxBase (strictQueryBase base + stage) := by
  unfold strictJointCenteredSourceBase centeredBoxBase
  omega

theorem couplingParametricKCompatibleStrictJointCentered_pair_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase base + later))
            (centralStrictJointCenteredCylinderEvent
              base later roots predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase base + earlier))
            (centralStrictJointCenteredCylinderEvent
              base earlier roots predicate)) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon
        (roots.length + roots.length) earlier := by
  let sourceBase := centeredBoxBase (strictQueryBase base + earlier)
  let padding := later - earlier
  let sourceRoots :=
    centralStrictJointCenteredStageRoots base earlier roots
  have hsourceRoots : ∀ root, root ∈ sourceRoots →
      root ∈ canonicalSurfacePolymers sourceBase :=
    centralStrictJointCenteredStageRoots_canonical hroots
  have hside : strictJointCenteredSourceBase base + earlier + earlier =
      sourceBase := by
    dsimp only [sourceBase]
    exact centralStrictJointCenteredStageSide base earlier
  have hcore := centralStrictJointCenteredUniformShiftAtoms_core
    hstage hroots
  have hraw :=
    couplingParametricKUniformShiftFullTargetProbability_abs_sub_source_le_of_bound
      hcoupling
      (uniformShiftTargetCylinderStabilityBound_of_anchor hcoupling hle)
      cutoff padding sourceBase hsourceRoots predicate hside hcore
  have hbaseEq : uniformPaddedBase padding sourceBase =
      centeredBoxBase (strictQueryBase base + later) := by
    dsimp only [padding, sourceBase]
    exact (strictJointCenteredStageBase_eq_uniformPadded_between
      hstage).symm
  rw [hbaseEq] at hraw
  rw [← centralStrictJointCenteredCylinderEvent_eq_uniformShift_between
    hstage hroots predicate] at hraw
  have hlength : sourceRoots.length =
      roots.length + roots.length := by
    simpa only [sourceRoots] using
      (centralStrictJointCenteredStageRoots_length base earlier roots)
  simpa only [sourceBase, sourceRoots,
    centralStrictJointCenteredCylinderEvent, hlength] using hraw

theorem couplingParametricKCompatibleStrictJointCentered_pair_half_pow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase base + later))
            (centralStrictJointCenteredCylinderEvent
              base later roots predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase base + earlier))
            (centralStrictJointCenteredCylinderEvent
              base earlier roots predicate)) ≤
      spinSummedCylinderBoundaryCoefficient
          (roots.length + roots.length) *
        HalfPow.half ^ earlier := by
  exact Q'.le_trans' _ _ _
    (couplingParametricKCompatibleStrictJointCentered_pair_abs_sub_le
      hcoupling hle cutoff hstage hroots predicate)
    (uniformShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      (roots.length + roots.length) earlier)

/-! ## 5. Common-cutoff diagonal for the joint chart -/

def centralStrictJointCenteredStageCutoff
    (base stage : Nat) : Nat :=
  spinSummedJointCutoff stage
    (centeredBoxBase (strictQueryBase base + stage))

def couplingParametricStrictJointCenteredSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) : Q' :=
  couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff base stage)
    (centeredBoxBase (strictQueryBase base + stage))
    (centralStrictJointCenteredCylinderEvent
      base stage roots predicate)

theorem couplingParametricStrictJointCenteredSequence_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) :
    (0 : Q') ≤ couplingParametricStrictJointCenteredSequence
      coupling hcoupling base roots predicate stage :=
  couplingParametricKCompatibleSupportEventProbability_nonnegative
    hcoupling (centralStrictJointCenteredStageCutoff base stage)
    (centeredBoxBase (strictQueryBase base + stage))
    (centralStrictJointCenteredCylinderEvent
      base stage roots predicate)

theorem couplingParametricStrictJointCenteredSequence_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) :
    couplingParametricStrictJointCenteredSequence
        coupling hcoupling base roots predicate stage ≤ (1 : Q') :=
  couplingParametricKCompatibleSupportEventProbability_le_one
    hcoupling (centralStrictJointCenteredStageCutoff base stage)
    (centeredBoxBase (strictQueryBase base + stage))
    (centralStrictJointCenteredCylinderEvent
      base stage roots predicate)

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

private theorem four_point_abs_sub_le_local
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

theorem couplingParametricStrictJointCenteredSequence_pair_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots predicate later -
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots predicate earlier) ≤
      spinSummedJointCylinderCoefficient
          (roots.length + roots.length) *
        HalfPow.half ^ earlier := by
  let smallBase := centeredBoxBase (strictQueryBase base + earlier)
  let largeBase := centeredBoxBase (strictQueryBase base + later)
  let smallCutoff := centralStrictJointCenteredStageCutoff base earlier
  let largeCutoff := centralStrictJointCenteredStageCutoff base later
  let commonCutoff := smallCutoff + largeCutoff
  let smallEvent := centralStrictJointCenteredCylinderEvent
    base earlier roots predicate
  let largeEvent := centralStrictJointCenteredCylinderEvent
    base later roots predicate
  let a := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling largeCutoff largeBase largeEvent
  let b := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling smallCutoff smallBase smallEvent
  let c := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff largeBase largeEvent
  let d := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff smallBase smallEvent
  have hlargeCutoff : largeCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hsmallCutoff : smallCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hlargeRaw : Q'.abs (c - a) ≤ HalfPow.half ^ later := by
    dsimp only [a, c, largeCutoff, largeBase]
    exact
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle largeEvent hlargeCutoff
  have hlarge : Q'.abs (a - c) ≤ HalfPow.half ^ earlier := by
    have horiented : Q'.abs (a - c) ≤ HalfPow.half ^ later :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm a c))
        hlargeRaw
    obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
    have hhalf : HalfPow.half ^ later ≤
        HalfPow.half ^ earlier := by
      rw [hoffset]
      exact ExpNeg.pow_half_antitone earlier offset
    exact Q'.le_trans' _ _ _ horiented hhalf
  have hmiddle : Q'.abs (c - d) ≤
      spinSummedCylinderBoundaryCoefficient
          (roots.length + roots.length) *
        HalfPow.half ^ earlier := by
    dsimp only [c, d, largeBase, smallBase, largeEvent, smallEvent]
    exact couplingParametricKCompatibleStrictJointCentered_pair_half_pow
      hcoupling hle commonCutoff hstage hroots predicate
  have hsmall : Q'.abs (d - b) ≤ HalfPow.half ^ earlier := by
    dsimp only [b, d, smallCutoff, smallBase]
    exact
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle smallEvent hsmallCutoff
  have hthree := four_point_abs_sub_le_local a b c d
    (HalfPow.half ^ earlier)
    (spinSummedCylinderBoundaryCoefficient
      (roots.length + roots.length) * HalfPow.half ^ earlier)
    (HalfPow.half ^ earlier) hlarge hmiddle hsmall
  have hreorder :
      HalfPow.half ^ earlier +
          (spinSummedCylinderBoundaryCoefficient
              (roots.length + roots.length) *
                HalfPow.half ^ earlier +
            HalfPow.half ^ earlier) ≈
        spinSummedJointCylinderCoefficient
            (roots.length + roots.length) *
          HalfPow.half ^ earlier := by
    let h := HalfPow.half ^ earlier
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
      HalfPow.half ^ earlier
  exact Q'.le_trans' _ _ _ hthree (Q'.le_of_eqv hreorder)

/-! ## 6. Constructive real limit -/

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

def couplingParametricStrictJointCenteredLimit
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (predicate : List Bool → Bool)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) : CReal where
  approx := couplingParametricStrictJointCenteredSequence
    coupling hcoupling base roots predicate
  cauchy := by
    intro epsilon hepsilon
    let coefficient := spinSummedJointCylinderCoefficient
      (roots.length + roots.length)
    let scaledTolerance :=
      epsilon * Q'.invSucc coefficient.num.toNat
    have hcoefficient : (0 : Q') ≤ coefficient :=
      spinSummedJointCylinderCoefficient_nonnegative
        (roots.length + roots.length)
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
    have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
      ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
        hcoefficient (Q'.le_of_lt hepsilon)
    refine ⟨scaledTolerance.den, fun m n hm hn => ?_⟩
    rcases Nat.le_total m n with hmn | hnm
    · have hpair :=
        couplingParametricStrictJointCenteredSequence_pair_abs_le
          hcoupling hle hmn hroots predicate
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hm
      have hhalf : HalfPow.half ^ m ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ m) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricStrictJointCenteredSequence
              coupling hcoupling base roots predicate n -
            couplingParametricStrictJointCenteredSequence
              coupling hcoupling base roots predicate m) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      have htwo := two_sided_add_of_abs_sub_le_local habs
      exact ⟨htwo.2, htwo.1⟩
    · have hpair :=
        couplingParametricStrictJointCenteredSequence_pair_abs_le
          hcoupling hle hnm hroots predicate
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hn
      have hhalf : HalfPow.half ^ n ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ n) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricStrictJointCenteredSequence
              coupling hcoupling base roots predicate m -
            couplingParametricStrictJointCenteredSequence
              coupling hcoupling base roots predicate n) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      exact two_sided_add_of_abs_sub_le_local habs

@[simp] theorem couplingParametricStrictJointCenteredLimit_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (predicate : List Bool → Bool)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (couplingParametricStrictJointCenteredLimit
      coupling hcoupling hle predicate hroots).approx stage =
      couplingParametricStrictJointCenteredSequence
        coupling hcoupling base roots predicate stage := rfl

/-! ## 7. The conditional reflected law approaches the same centered chart -/

theorem couplingPhysicalGivenSlabStrictJoint_cross_centered_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    let atoms := centralStrictJointCanonicalAtoms
      (strictQueryBase base + stage) base roots
      (Nat.le_add_right (strictQueryBase base) stage) hroots
    let predicate := centralStrictJointPairPredicate
      roots.length left right
    Q'.abs
        (couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (centralExtent (strictQueryBase base + stage))
            (slabMarkedCylinderEvent atoms predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase base + stage))
            (centralStrictJointCenteredCylinderEvent
              base stage roots predicate)) ≤
      couplingSlabConditionalBoundaryEpsilon
          (roots.length + roots.length) (stage + 3) +
        spinSummedCylinderBoundaryEpsilon
          (roots.length + roots.length) stage := by
  dsimp only
  let atoms := centralStrictJointCanonicalAtoms
    (strictQueryBase base + stage) base roots
    (Nat.le_add_right (strictQueryBase base) stage) hroots
  let predicate := centralStrictJointPairPredicate
    roots.length left right
  let ambientEvent := slabMarkedCylinderEvent atoms predicate
  let centeredEvent := centralStrictJointCenteredCylinderEvent
    base stage roots predicate
  let conditional := couplingParametricKPhysicalGivenSlabProbability
    coupling hcoupling cutoff
    (centralExtent (strictQueryBase base + stage)) ambientEvent
  let ambient := couplingKFamilyEventProbability
    coupling hcoupling cutoff
    (centralAmbient (strictQueryBase base + stage)) ambientEvent
  let centeredPhysical := couplingKFamilyEventProbability
    coupling hcoupling cutoff
    (centeredBoxBase (strictQueryBase base + stage)) centeredEvent
  let centeredCompatible :=
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff
      (centeredBoxBase (strictQueryBase base + stage)) centeredEvent
  have hradius : 1 ≤ strictQueryBase base + stage := by
    unfold strictQueryBase uniformPaddedBase
    omega
  let defaultRoot : CanonicalAtom
      (centralAmbient (strictQueryBase base + stage)) :=
    centralLowerCanonicalAtom
      (strictQueryBase base + stage) hradius
  have hconditionalRaw :=
    couplingPhysicalStrictJoint_givenSlab_abs_sub_le
      hcoupling hle cutoff hroots left right defaultRoot
  have hconditional : Q'.abs (conditional - ambient) ≤
      couplingSlabConditionalBoundaryEpsilon
        (roots.length + roots.length) (stage + 3) := by
    have horiented : Q'.abs (conditional - ambient) ≤
        Q'.abs (ambient - conditional) :=
      Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          conditional ambient)
    exact Q'.le_trans' _ _ _ horiented
      (by simpa only [conditional, ambient, ambientEvent,
          atoms, predicate] using hconditionalRaw)
  have hadjacent : Q'.abs (ambient - centeredPhysical) ≤
      spinSummedCylinderBoundaryEpsilon
        (roots.length + roots.length) stage := by
    simpa only [ambient, centeredPhysical, ambientEvent, centeredEvent,
      atoms, predicate, centralStrictJointCenteredCylinderEvent] using
      (couplingPhysicalStrictJoint_cross_centered_abs_sub_le
        (stage := stage) hcoupling hle cutoff hroots predicate)
  have hdecompose :
      conditional - centeredPhysical ≈
        (conditional - ambient) + (ambient - centeredPhysical) := by
    exact Q'.eqv_symm
      (reassoc_cancel_local conditional ambient (-centeredPhysical))
  have htriangle := Q'.abs_add_le'
    (conditional - ambient) (ambient - centeredPhysical)
  have hsum := Q'.add_le_add hconditional hadjacent
  have hphysical : Q'.abs (conditional - centeredPhysical) ≤
      couplingSlabConditionalBoundaryEpsilon
          (roots.length + roots.length) (stage + 3) +
        spinSummedCylinderBoundaryEpsilon
          (roots.length + roots.length) stage :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
      (Q'.le_trans' _ _ _ htriangle hsum)
  have hbridge : centeredPhysical ≈ centeredCompatible :=
    couplingKFamilyEventProbability_eqv_compatible
      coupling hcoupling cutoff
      (centeredBoxBase (strictQueryBase base + stage)) centeredEvent
  have hdifference :
      conditional - centeredPhysical ≈
        conditional - centeredCompatible :=
    Q'.add_eqv_congr_left conditional
      (-centeredPhysical) (-centeredCompatible)
      (Q'.neg_eqv_congr centeredPhysical centeredCompatible hbridge)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr (Q'.eqv_symm hdifference)))
    (by simpa only [conditional, centeredCompatible, ambientEvent,
        centeredEvent, atoms, predicate] using hphysical)

theorem couplingPhysicalGivenSlabStrictJoint_to_centeredSequence_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    let cutoff := centralStrictJointCenteredStageCutoff base stage
    let atoms := centralStrictJointCanonicalAtoms
      (strictQueryBase base + stage) base roots
      (Nat.le_add_right (strictQueryBase base) stage) hroots
    let predicate := centralStrictJointPairPredicate
      roots.length left right
    Q'.abs
        (couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (centralExtent (strictQueryBase base + stage))
            (slabMarkedCylinderEvent atoms predicate) -
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots predicate stage) ≤
      couplingSlabConditionalBoundaryEpsilon
          (roots.length + roots.length) (stage + 3) +
        spinSummedCylinderBoundaryEpsilon
          (roots.length + roots.length) stage := by
  dsimp only
  simpa only [couplingParametricStrictJointCenteredSequence] using
    (couplingPhysicalGivenSlabStrictJoint_cross_centered_abs_sub_le
      hcoupling hle (centralStrictJointCenteredStageCutoff base stage)
      hroots left right)

/-! ## 8. One explicit modulus for the conditional-to-centered bridge -/

theorem couplingSlabConditionalBoundaryEpsilon_le_spinSummed_succ
    (rootCount stage : Nat) :
    couplingSlabConditionalBoundaryEpsilon rootCount (stage + 3) ≤
      spinSummedCylinderBoundaryEpsilon rootCount (stage + 1) := by
  unfold couplingSlabConditionalBoundaryEpsilon
    spinSummedCylinderBoundaryEpsilon
  rw [show stage + 1 + 2 = stage + 3 by omega]
  apply Q'.mul_le_mul_of_nonneg_left
  · exact Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedEffectiveRatio
          anchorDecoratedEffectiveRatio_nonnegative (stage + 3))
        (ExpNeg.ofNat_nonneg' 2))
  · exact ExpNeg.ofNat_nonneg' rootCount

theorem couplingSlabConditionalBoundaryEpsilon_le_coefficient_half_pow
    (rootCount stage : Nat) :
    couplingSlabConditionalBoundaryEpsilon rootCount (stage + 3) ≤
      spinSummedCylinderBoundaryCoefficient rootCount *
        HalfPow.half ^ stage := by
  have hsucc := couplingSlabConditionalBoundaryEpsilon_le_spinSummed_succ
    rootCount stage
  have hboundary :=
    spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      rootCount (stage + 1)
  have hpow :
      spinSummedCylinderBoundaryCoefficient rootCount *
          HalfPow.half ^ (stage + 1) ≤
        spinSummedCylinderBoundaryCoefficient rootCount *
          HalfPow.half ^ stage :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (ExpNeg.pow_half_antitone stage 1)
      (spinSummedCylinderBoundaryCoefficient_nonnegative rootCount)
  exact Q'.le_trans' _ _ _ hsucc
    (Q'.le_trans' _ _ _ hboundary hpow)

def strictJointConditionalCenteredCoefficient (rootCount : Nat) : Q' :=
  spinSummedCylinderBoundaryCoefficient rootCount +
    spinSummedCylinderBoundaryCoefficient rootCount

theorem strictJointConditionalCenteredCoefficient_nonnegative
    (rootCount : Nat) :
    (0 : Q') ≤ strictJointConditionalCenteredCoefficient rootCount := by
  unfold strictJointConditionalCenteredCoefficient
  exact Q'.zero_le_add _ _
    (spinSummedCylinderBoundaryCoefficient_nonnegative rootCount)
    (spinSummedCylinderBoundaryCoefficient_nonnegative rootCount)

theorem couplingPhysicalGivenSlabStrictJoint_to_centeredSequence_half_pow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    let cutoff := centralStrictJointCenteredStageCutoff base stage
    let atoms := centralStrictJointCanonicalAtoms
      (strictQueryBase base + stage) base roots
      (Nat.le_add_right (strictQueryBase base) stage) hroots
    let predicate := centralStrictJointPairPredicate
      roots.length left right
    Q'.abs
        (couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (centralExtent (strictQueryBase base + stage))
            (slabMarkedCylinderEvent atoms predicate) -
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots predicate stage) ≤
      strictJointConditionalCenteredCoefficient
          (roots.length + roots.length) *
        HalfPow.half ^ stage := by
  dsimp only
  have hraw :=
    couplingPhysicalGivenSlabStrictJoint_to_centeredSequence_abs_sub_le
      (stage := stage) hcoupling hle hroots left right
  have hconditional :=
    couplingSlabConditionalBoundaryEpsilon_le_coefficient_half_pow
      (roots.length + roots.length) stage
  have hadjacent :=
    spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      (roots.length + roots.length) stage
  have hsum := Q'.add_le_add hconditional hadjacent
  have hreorder :
      spinSummedCylinderBoundaryCoefficient
            (roots.length + roots.length) * HalfPow.half ^ stage +
          spinSummedCylinderBoundaryCoefficient
            (roots.length + roots.length) * HalfPow.half ^ stage ≈
        strictJointConditionalCenteredCoefficient
            (roots.length + roots.length) * HalfPow.half ^ stage := by
    exact Q'.eqv_symm
      (Q'.add_mul_eqv
        (spinSummedCylinderBoundaryCoefficient
          (roots.length + roots.length))
        (spinSummedCylinderBoundaryCoefficient
          (roots.length + roots.length))
        (HalfPow.half ^ stage))
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hreorder))

/-! ## 9. The actual corrected-slab diagonal and its Cauchy modulus -/

def couplingParametricStrictJointGivenSlabSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) (stage : Nat) : Q' :=
  couplingParametricKPhysicalGivenSlabProbability
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff base stage)
    (centralExtent (strictQueryBase base + stage))
    (slabMarkedCylinderEvent
      (centralStrictJointCanonicalAtoms
        (strictQueryBase base + stage) base roots
        (Nat.le_add_right (strictQueryBase base) stage) hroots)
      (centralStrictJointPairPredicate roots.length left right))

theorem couplingParametricStrictJointGivenSlabSequence_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) (stage : Nat) :
    (0 : Q') ≤ couplingParametricStrictJointGivenSlabSequence
      coupling hcoupling hroots left right stage := by
  unfold couplingParametricStrictJointGivenSlabSequence
    couplingParametricKPhysicalGivenSlabProbability Q'.divPos
  exact Q'.mul_nonneg _ _
    (parametricKEventNumerator_nonnegative hcoupling _ _ _)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

def strictJointGivenSlabCauchyCoefficient (rootCount : Nat) : Q' :=
  strictJointConditionalCenteredCoefficient rootCount +
    (spinSummedJointCylinderCoefficient rootCount +
      strictJointConditionalCenteredCoefficient rootCount)

theorem strictJointGivenSlabCauchyCoefficient_nonnegative
    (rootCount : Nat) :
    (0 : Q') ≤ strictJointGivenSlabCauchyCoefficient rootCount := by
  unfold strictJointGivenSlabCauchyCoefficient
  exact Q'.zero_le_add _ _
    (strictJointConditionalCenteredCoefficient_nonnegative rootCount)
    (Q'.zero_le_add _ _
      (spinSummedJointCylinderCoefficient_nonnegative rootCount)
      (strictJointConditionalCenteredCoefficient_nonnegative rootCount))

theorem couplingParametricStrictJointGivenSlabSequence_pair_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    Q'.abs
        (couplingParametricStrictJointGivenSlabSequence
            coupling hcoupling hroots left right later -
          couplingParametricStrictJointGivenSlabSequence
            coupling hcoupling hroots left right earlier) ≤
      strictJointGivenSlabCauchyCoefficient
          (roots.length + roots.length) *
        HalfPow.half ^ earlier := by
  let predicate := centralStrictJointPairPredicate roots.length left right
  let a := couplingParametricStrictJointGivenSlabSequence
    coupling hcoupling hroots left right later
  let b := couplingParametricStrictJointGivenSlabSequence
    coupling hcoupling hroots left right earlier
  let c := couplingParametricStrictJointCenteredSequence
    coupling hcoupling base roots predicate later
  let d := couplingParametricStrictJointCenteredSequence
    coupling hcoupling base roots predicate earlier
  let conditionalCoefficient := strictJointConditionalCenteredCoefficient
    (roots.length + roots.length)
  let centeredCoefficient := spinSummedJointCylinderCoefficient
    (roots.length + roots.length)
  have hlaterRaw : Q'.abs (a - c) ≤
      conditionalCoefficient * HalfPow.half ^ later := by
    simpa only [a, c, predicate, conditionalCoefficient,
      couplingParametricStrictJointGivenSlabSequence] using
      (couplingPhysicalGivenSlabStrictJoint_to_centeredSequence_half_pow
        (stage := later) hcoupling hle hroots left right)
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
  have hlaterPow : HalfPow.half ^ later ≤
      HalfPow.half ^ earlier := by
    rw [hoffset]
    exact ExpNeg.pow_half_antitone earlier offset
  have hlaterScaled :
      conditionalCoefficient * HalfPow.half ^ later ≤
        conditionalCoefficient * HalfPow.half ^ earlier :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hlaterPow
      (strictJointConditionalCenteredCoefficient_nonnegative
        (roots.length + roots.length))
  have hlater : Q'.abs (a - c) ≤
      conditionalCoefficient * HalfPow.half ^ earlier :=
    Q'.le_trans' _ _ _ hlaterRaw hlaterScaled
  have hcentered : Q'.abs (c - d) ≤
      centeredCoefficient * HalfPow.half ^ earlier := by
    simpa only [c, d, predicate, centeredCoefficient] using
      (couplingParametricStrictJointCenteredSequence_pair_abs_le
        hcoupling hle hstage hroots predicate)
  have hearlierRaw : Q'.abs (b - d) ≤
      conditionalCoefficient * HalfPow.half ^ earlier := by
    simpa only [b, d, predicate, conditionalCoefficient,
      couplingParametricStrictJointGivenSlabSequence] using
      (couplingPhysicalGivenSlabStrictJoint_to_centeredSequence_half_pow
        (stage := earlier) hcoupling hle hroots left right)
  have hearlier : Q'.abs (d - b) ≤
      conditionalCoefficient * HalfPow.half ^ earlier :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm d b))
      hearlierRaw
  have hthree := four_point_abs_sub_le_local a b c d
    (conditionalCoefficient * HalfPow.half ^ earlier)
    (centeredCoefficient * HalfPow.half ^ earlier)
    (conditionalCoefficient * HalfPow.half ^ earlier)
    hlater hcentered hearlier
  have hreorder :
      conditionalCoefficient * HalfPow.half ^ earlier +
          (centeredCoefficient * HalfPow.half ^ earlier +
            conditionalCoefficient * HalfPow.half ^ earlier) ≈
        strictJointGivenSlabCauchyCoefficient
            (roots.length + roots.length) *
          HalfPow.half ^ earlier := by
    let h := HalfPow.half ^ earlier
    have hinner :
        (centeredCoefficient + conditionalCoefficient) * h ≈
          centeredCoefficient * h + conditionalCoefficient * h :=
      Q'.add_mul_eqv centeredCoefficient conditionalCoefficient h
    have hright :
        strictJointGivenSlabCauchyCoefficient
            (roots.length + roots.length) * h ≈
          conditionalCoefficient * h +
            (centeredCoefficient * h + conditionalCoefficient * h) := by
      unfold strictJointGivenSlabCauchyCoefficient
      exact Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv conditionalCoefficient
          (centeredCoefficient + conditionalCoefficient) h)
        (Q'.add_eqv_congr'
          (Q'.eqv_refl (conditionalCoefficient * h)) hinner)
    exact Q'.eqv_symm hright
  change Q'.abs (a - b) ≤
    strictJointGivenSlabCauchyCoefficient
        (roots.length + roots.length) *
      HalfPow.half ^ earlier
  exact Q'.le_trans' _ _ _ hthree (Q'.le_of_eqv hreorder)

def couplingParametricStrictJointGivenSlabLimit
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) : CReal where
  approx := couplingParametricStrictJointGivenSlabSequence
    coupling hcoupling hroots left right
  cauchy := by
    intro epsilon hepsilon
    let coefficient := strictJointGivenSlabCauchyCoefficient
      (roots.length + roots.length)
    let scaledTolerance :=
      epsilon * Q'.invSucc coefficient.num.toNat
    have hcoefficient : (0 : Q') ≤ coefficient :=
      strictJointGivenSlabCauchyCoefficient_nonnegative
        (roots.length + roots.length)
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
    have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
      ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
        hcoefficient (Q'.le_of_lt hepsilon)
    refine ⟨scaledTolerance.den, fun m n hm hn => ?_⟩
    rcases Nat.le_total m n with hmn | hnm
    · have hpair :=
        couplingParametricStrictJointGivenSlabSequence_pair_abs_le
          hcoupling hle hmn hroots left right
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hm
      have hhalf : HalfPow.half ^ m ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ m) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricStrictJointGivenSlabSequence
              coupling hcoupling hroots left right n -
            couplingParametricStrictJointGivenSlabSequence
              coupling hcoupling hroots left right m) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      have htwo := two_sided_add_of_abs_sub_le_local habs
      exact ⟨htwo.2, htwo.1⟩
    · have hpair :=
        couplingParametricStrictJointGivenSlabSequence_pair_abs_le
          hcoupling hle hnm hroots left right
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hn
      have hhalf : HalfPow.half ^ n ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ n) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricStrictJointGivenSlabSequence
              coupling hcoupling hroots left right m -
            couplingParametricStrictJointGivenSlabSequence
              coupling hcoupling hroots left right n) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      exact two_sided_add_of_abs_sub_le_local habs

@[simp] theorem couplingParametricStrictJointGivenSlabLimit_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    (couplingParametricStrictJointGivenSlabLimit
      coupling hcoupling hle hroots left right).approx stage =
      couplingParametricStrictJointGivenSlabSequence
        coupling hcoupling hroots left right stage := rfl

theorem couplingParametricStrictJointGivenSlabLimit_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    CReal.ofQ' 0 ≤ couplingParametricStrictJointGivenSlabLimit
      coupling hcoupling hle hroots left right := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact couplingParametricStrictJointGivenSlabSequence_nonnegative
    hcoupling hroots left right stage

/-! ## 10. The corrected-slab and centered limits are the same CReal -/

theorem couplingParametricStrictJointGivenSlabLimit_equiv_centered
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    CReal.Equiv
      (couplingParametricStrictJointGivenSlabLimit
        coupling hcoupling hle hroots left right)
      (couplingParametricStrictJointCenteredLimit
        coupling hcoupling hle
        (centralStrictJointPairPredicate roots.length left right) hroots) := by
  intro epsilon hepsilon
  let coefficient := strictJointConditionalCenteredCoefficient
    (roots.length + roots.length)
  let scaledTolerance :=
    epsilon * Q'.invSucc coefficient.num.toNat
  have hcoefficient : (0 : Q') ≤ coefficient :=
    strictJointConditionalCenteredCoefficient_nonnegative
      (roots.length + roots.length)
  have hscaledPositive : (0 : Q') < scaledTolerance :=
    Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
  have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
    ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
      hcoefficient (Q'.le_of_lt hepsilon)
  refine ⟨scaledTolerance.den, fun stage hstage => ?_⟩
  have hhalf : HalfPow.half ^ stage ≤
      HalfPow.half ^ scaledTolerance.den := by
    obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
    rw [hoffset]
    exact ExpNeg.pow_half_antitone scaledTolerance.den offset
  have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
      scaledTolerance :=
    HalfPow.pow_half_le scaledTolerance hscaledPositive
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (HalfPow.half ^ stage) scaledTolerance coefficient
    (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
  have hpoint :=
    couplingPhysicalGivenSlabStrictJoint_to_centeredSequence_half_pow
      (stage := stage) hcoupling hle hroots left right
  have habs : Q'.abs
      (couplingParametricStrictJointGivenSlabSequence
          coupling hcoupling hroots left right stage -
        couplingParametricStrictJointCenteredSequence
          coupling hcoupling base roots
          (centralStrictJointPairPredicate roots.length left right)
          stage) ≤ epsilon :=
    Q'.le_trans' _ _ _
      (by simpa only [couplingParametricStrictJointGivenSlabSequence]
        using hpoint)
      (Q'.le_trans' _ _ _ hscaled hscaledFinal)
  exact two_sided_add_of_abs_sub_le_local habs

/-! ## 11. Literal local Gram representatives and positivity -/

def centralNormalizedStrictJointGramSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (left right : List Bool) (stage : Nat) : Q' :=
  centralNormalizedLocalSupportPairLaw
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff base stage)
    (strictQueryBase base + stage)
    (centralStrictLocalQueryCode
      (strictQueryBase base + stage) base roots)
    left right

theorem centralNormalizedStrictJointGramSequence_eqv_givenSlab
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) (stage : Nat) :
    centralNormalizedStrictJointGramSequence
        coupling hcoupling base roots left right stage ≈
      couplingParametricStrictJointGivenSlabSequence
        coupling hcoupling hroots left right stage := by
  simpa only [centralNormalizedStrictJointGramSequence,
    couplingParametricStrictJointGivenSlabSequence] using
    (centralNormalizedLocalSupportPairLaw_eq_strictMarkedCylinder
      coupling hcoupling
      (centralStrictJointCenteredStageCutoff base stage)
      (Nat.le_add_right (strictQueryBase base) stage)
      hroots left right)

theorem centralNormalizedStrictJointGramSequence_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) (stage : Nat) :
    (0 : Q') ≤ centralNormalizedStrictJointGramSequence
      coupling hcoupling base roots left right stage := by
  have hconditional :=
    couplingParametricStrictJointGivenSlabSequence_nonnegative
      hcoupling hroots left right stage
  exact Q'.le_trans' _ _ _ hconditional
    (Q'.ge_of_eqv
      (centralNormalizedStrictJointGramSequence_eqv_givenSlab
        hcoupling hroots left right stage))

theorem centralNormalizedStrictJointGramSequence_pair_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    Q'.abs
        (centralNormalizedStrictJointGramSequence
            coupling hcoupling base roots left right later -
          centralNormalizedStrictJointGramSequence
            coupling hcoupling base roots left right earlier) ≤
      strictJointGivenSlabCauchyCoefficient
          (roots.length + roots.length) *
        HalfPow.half ^ earlier := by
  have hlater := centralNormalizedStrictJointGramSequence_eqv_givenSlab
    hcoupling hroots left right later
  have hearlier := centralNormalizedStrictJointGramSequence_eqv_givenSlab
    hcoupling hroots left right earlier
  have hdifference :
      centralNormalizedStrictJointGramSequence
            coupling hcoupling base roots left right later -
          centralNormalizedStrictJointGramSequence
            coupling hcoupling base roots left right earlier ≈
        couplingParametricStrictJointGivenSlabSequence
            coupling hcoupling hroots left right later -
          couplingParametricStrictJointGivenSlabSequence
            coupling hcoupling hroots left right earlier :=
    Q'.add_eqv_congr' hlater
      (Q'.neg_eqv_congr _ _ hearlier)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (couplingParametricStrictJointGivenSlabSequence_pair_abs_le
      hcoupling hle hstage hroots left right)

def centralNormalizedStrictJointGramLimit
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) : CReal where
  approx := centralNormalizedStrictJointGramSequence
    coupling hcoupling base roots left right
  cauchy := by
    intro epsilon hepsilon
    obtain ⟨stage0, hstage0⟩ :=
      (couplingParametricStrictJointGivenSlabLimit
        coupling hcoupling hle hroots left right).cauchy epsilon hepsilon
    refine ⟨stage0, fun m n hm hn => ?_⟩
    have hmEqv := centralNormalizedStrictJointGramSequence_eqv_givenSlab
      hcoupling hroots left right m
    have hnEqv := centralNormalizedStrictJointGramSequence_eqv_givenSlab
      hcoupling hroots left right n
    have hconditional := hstage0 m n hm hn
    constructor
    · exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hmEqv)
        (Q'.le_trans' _ _ _ hconditional.1
          (Q'.add_le_add_right _ _ epsilon
            (Q'.ge_of_eqv hnEqv)))
    · exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hnEqv)
        (Q'.le_trans' _ _ _ hconditional.2
          (Q'.add_le_add_right _ _ epsilon
            (Q'.ge_of_eqv hmEqv)))

@[simp] theorem centralNormalizedStrictJointGramLimit_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    (centralNormalizedStrictJointGramLimit
      coupling hcoupling hle hroots left right).approx stage =
      centralNormalizedStrictJointGramSequence
        coupling hcoupling base roots left right stage := rfl

theorem centralNormalizedStrictJointGramLimit_equiv_givenSlab
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    CReal.Equiv
      (centralNormalizedStrictJointGramLimit
        coupling hcoupling hle hroots left right)
      (couplingParametricStrictJointGivenSlabLimit
        coupling hcoupling hle hroots left right) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have heqv := centralNormalizedStrictJointGramSequence_eqv_givenSlab
    hcoupling hroots left right stage
  have hepsilonNonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)
  · exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)

theorem centralNormalizedStrictJointGramLimit_equiv_centered
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    CReal.Equiv
      (centralNormalizedStrictJointGramLimit
        coupling hcoupling hle hroots left right)
      (couplingParametricStrictJointCenteredLimit
        coupling hcoupling hle
        (centralStrictJointPairPredicate roots.length left right) hroots) :=
  CReal.Equiv.trans
    (centralNormalizedStrictJointGramLimit_equiv_givenSlab
      hcoupling hle hroots left right)
    (couplingParametricStrictJointGivenSlabLimit_equiv_centered
      hcoupling hle hroots left right)

theorem centralNormalizedStrictJointGramLimit_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    CReal.ofQ' 0 ≤ centralNormalizedStrictJointGramLimit
      coupling hcoupling hle hroots left right := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact centralNormalizedStrictJointGramSequence_nonnegative
    hcoupling hroots left right stage

theorem centralNormalizedStrictJointGramLimit_geRat_zero
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    ExpPos.geRat
      (centralNormalizedStrictJointGramLimit
        coupling hcoupling hle hroots left right) 0 := by
  apply ExpPos.geRat_of_eventually
  exact ⟨0, fun stage _ =>
    centralNormalizedStrictJointGramSequence_nonnegative
      hcoupling hroots left right stage⟩

def centralNormalizedStrictJointLocalQuadraticSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (coefficient : List Bool → Q') (stage : Nat) : Q' :=
  finiteJointQuadratic
    (centralLocalSupportFingerprintSpace
      (strictQueryBase base + stage)
      (centralStrictLocalQueryCode
        (strictQueryBase base + stage) base roots))
    coefficient
    (centralNormalizedLocalSupportPairLaw
      coupling hcoupling
      (centralStrictJointCenteredStageCutoff base stage)
      (strictQueryBase base + stage)
      (centralStrictLocalQueryCode
        (strictQueryBase base + stage) base roots))

theorem centralNormalizedStrictJointLocalQuadraticSequence_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (coefficient : List Bool → Q') (stage : Nat) :
    (0 : Q') ≤ centralNormalizedStrictJointLocalQuadraticSequence
      coupling hcoupling base roots coefficient stage := by
  unfold centralNormalizedStrictJointLocalQuadraticSequence
  exact centralNormalizedLocalSupportQuadratic_nonnegative
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff base stage)
    (strictQueryBase base + stage)
    (centralStrictLocalQueryCode
      (strictQueryBase base + stage) base roots)
    coefficient

#print axioms uniformShiftCanonicalRoot_add
#print axioms centralStrictJointCenteredStageRoots_eq_uniformShift_between
#print axioms centralStrictJointCenteredStageRoot_face_inside_sourceCore
#print axioms centralStrictJointCenteredUniformShiftAtoms_core
#print axioms couplingParametricKCompatibleStrictJointCentered_pair_abs_sub_le
#print axioms couplingParametricKCompatibleStrictJointCentered_pair_half_pow
#print axioms couplingParametricStrictJointCenteredSequence_pair_abs_le
#print axioms couplingParametricStrictJointCenteredLimit
#print axioms couplingPhysicalGivenSlabStrictJoint_cross_centered_abs_sub_le
#print axioms couplingPhysicalGivenSlabStrictJoint_to_centeredSequence_abs_sub_le
#print axioms couplingSlabConditionalBoundaryEpsilon_le_coefficient_half_pow
#print axioms couplingPhysicalGivenSlabStrictJoint_to_centeredSequence_half_pow
#print axioms couplingParametricStrictJointGivenSlabSequence_pair_abs_le
#print axioms couplingParametricStrictJointGivenSlabLimit
#print axioms couplingParametricStrictJointGivenSlabLimit_nonnegative
#print axioms couplingParametricStrictJointGivenSlabLimit_equiv_centered
#print axioms centralNormalizedStrictJointGramSequence_eqv_givenSlab
#print axioms centralNormalizedStrictJointGramLimit
#print axioms centralNormalizedStrictJointGramLimit_equiv_centered
#print axioms centralNormalizedStrictJointGramLimit_geRat_zero
#print axioms centralNormalizedStrictJointLocalQuadraticSequence_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
