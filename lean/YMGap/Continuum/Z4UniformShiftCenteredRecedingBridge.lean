/-
# Uniform-shift finite bounds imply the centered receding volume modulus

This file is the exact interface between the uniformly shifted finite-cell
pipeline and `CenteredRecedingVolumeModulus`.  It proves all schedule,
canonical-root, protected-core, and shifted-cell exit identities for two
stages of the centered exhaustion.

The normalized finite target-versus-embedded-cell estimate is supplied by
`Z4UniformShiftTargetCylinderStability`.  The exact embedded-law identity and
the checked geometry turn that estimate into the full target-versus-source
bound; its derived geometric ratio is then converted to the existing
`HalfPow.half^earlier` interface and hence to an unconditional
`CenteredRecedingVolumeModulus` throughout the derived strong-coupling window.
-/

import YMGap.Continuum.Z4SignedCenteredRecedingPresentation
import YMGap.Continuum.Z4UniformShiftTargetCylinderStability

namespace YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredExhaustion
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCylinderSwitchSummation
open YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftEmbeddedRegion
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4UniformShiftTargetCylinderStability
open Dir4

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The uniformly shifted cell as an exact coordinate box -/

def uniformShiftCellLower (padding : Nat) : Z4Vertex :=
  (padding, padding, padding, padding)

theorem mem_uniformShiftedPlaquetteList_iff_coordinates
    (padding base : Nat) (plaquette : Z4Plaq) :
    plaquette ∈ uniformShiftedPlaquetteList padding base ↔
      padding ≤ cPlaq plaquette x0 ∧
      cPlaq plaquette x0 < padding + base ∧
      padding ≤ cPlaq plaquette x1 ∧
      cPlaq plaquette x1 < padding + base ∧
      padding ≤ cPlaq plaquette x2 ∧
      cPlaq plaquette x2 < padding + base ∧
      padding ≤ cPlaq plaquette x3 ∧
      cPlaq plaquette x3 < padding + base := by
  constructor
  · intro hmem
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
    rw [← heq]
    have hcoords := (mem_boxPlaquettes source base).1 hsource
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
    simp only [uniformShiftPlaquette, uniformShiftVertex, cPlaq, vComp]
    simp only at hcoords
    exact ⟨Nat.le_add_left padding a,
      by simpa only [Nat.add_comm] using
        Nat.add_lt_add_right hcoords.1 padding,
      Nat.le_add_left padding b,
      by simpa only [Nat.add_comm] using
        Nat.add_lt_add_right hcoords.2.1 padding,
      Nat.le_add_left padding c,
      by simpa only [Nat.add_comm] using
        Nat.add_lt_add_right hcoords.2.2.1 padding,
      Nat.le_add_left padding d,
      by simpa only [Nat.add_comm] using
        Nat.add_lt_add_right hcoords.2.2.2 padding⟩
  · intro hcoords
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
    simp only [cPlaq, vComp] at hcoords
    unfold uniformShiftedPlaquetteList
    apply List.mem_map.mpr
    let source : Z4Plaq :=
      ((a - padding, b - padding, c - padding, d - padding), plane)
    refine ⟨source, ?_, ?_⟩
    · apply (mem_boxPlaquettes source base).2
      dsimp only [source]
      exact ⟨by omega, by omega, by omega, by omega⟩
    · dsimp only [source]
      simp only [uniformShiftPlaquette, uniformShiftVertex, Prod.mk.injEq]
      rw [Nat.sub_add_cancel hcoords.1,
        Nat.sub_add_cancel hcoords.2.2.1,
        Nat.sub_add_cancel hcoords.2.2.2.2.1,
        Nat.sub_add_cancel hcoords.2.2.2.2.2.2.1]
      simp

theorem outside_uniformShiftCell_of_not_mem
    {padding base : Nat} {plaquette : Z4Plaq}
    (hnot : plaquette ∉ uniformShiftedPlaquetteList padding base) :
    outsideShiftedBoxB (uniformShiftCellLower padding) base plaquette = true := by
  apply (outsideShiftedBoxB_true_iff
    (uniformShiftCellLower padding) base plaquette).2
  have hcoordinates : ¬(
      padding ≤ cPlaq plaquette x0 ∧
      cPlaq plaquette x0 < padding + base ∧
      padding ≤ cPlaq plaquette x1 ∧
      cPlaq plaquette x1 < padding + base ∧
      padding ≤ cPlaq plaquette x2 ∧
      cPlaq plaquette x2 < padding + base ∧
      padding ≤ cPlaq plaquette x3 ∧
      cPlaq plaquette x3 < padding + base) := by
    intro hcoordinates
    exact hnot ((mem_uniformShiftedPlaquetteList_iff_coordinates
      padding base plaquette).2 hcoordinates)
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp only [cPlaq, vComp] at hcoordinates
  simp only [uniformShiftCellLower, cPlaq, vComp]
  by_cases halo : padding ≤ a
  · by_cases hahi : a < padding + base
    · by_cases hblo : padding ≤ b
      · by_cases hbhi : b < padding + base
        · by_cases hclo : padding ≤ c
          · by_cases hchi : c < padding + base
            · by_cases hdlo : padding ≤ d
              · by_cases hdhi : d < padding + base
                · exact False.elim
                    (hcoordinates ⟨halo, hahi, hblo, hbhi,
                      hclo, hchi, hdlo, hdhi⟩)
                · exact Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inr
                      (Nat.le_of_not_gt hdhi)))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl
                    (Nat.lt_of_not_ge hdlo)))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inl (Nat.le_of_not_gt hchi))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl (Nat.lt_of_not_ge hclo)))))
        · exact Or.inr (Or.inr (Or.inr
            (Or.inl (Nat.le_of_not_gt hbhi))))
      · exact Or.inr (Or.inr
          (Or.inl (Nat.lt_of_not_ge hblo)))
    · exact Or.inr (Or.inl (Nat.le_of_not_gt hahi))
  · exact Or.inl (Nat.lt_of_not_ge halo)

theorem outside_uniformShiftCell_of_not_mem_of_side_eq
    {padding base inner distance : Nat}
    (hside : inner + distance + distance = base)
    {plaquette : Z4Plaq}
    (hnot : plaquette ∉ uniformShiftedPlaquetteList padding base) :
    outsideShiftedBoxB (uniformShiftCellLower padding)
      (inner + distance + distance) plaquette = true := by
  rw [hside]
  exact outside_uniformShiftCell_of_not_mem hnot

/-! ## 2. Exact identities between two centered stages -/

theorem centeredRecedingStageBase_eq_uniformPadded_between
    {base earlier later : Nat} (hstage : earlier ≤ later) :
    centeredRecedingStageBase base later =
      uniformPaddedBase (later - earlier)
        (centeredRecedingStageBase base earlier) := by
  unfold centeredRecedingStageBase centeredRecedingStageRadius
    centeredBoxBase uniformPaddedBase
  omega

theorem centeredOffsetCanonicalRoot_eq_uniformShift_between
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centeredOffsetCanonicalRoot (base + later) base root =
      uniformShiftCanonicalRoot (later - earlier)
        (centeredBoxBase (base + earlier))
        (centeredOffsetCanonicalRoot (base + earlier) base root) := by
  have hsource : centeredOffsetCanonicalRoot (base + earlier) base root ∈
      canonicalSurfacePolymers (centeredBoxBase (base + earlier)) :=
    centeredOffsetCanonicalRoot_canonical
      (Nat.le_add_right base earlier) hroot
  have hleft : centeredOffsetCanonicalRoot (base + later) base root ∈
      canonicalSurfacePolymers (centeredBoxBase (base + later)) :=
    centeredOffsetCanonicalRoot_canonical
      (Nat.le_add_right base later) hroot
  have hright := uniformShiftCanonicalRoot_canonical
    (padding := later - earlier) hsource
  have hbaseEq : uniformPaddedBase (later - earlier)
      (centeredBoxBase (base + earlier)) =
        centeredBoxBase (base + later) := by
    unfold uniformPaddedBase centeredBoxBase
    omega
  rw [hbaseEq] at hright
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport hleft hright
  have hstageSupport := centeredOffsetCanonicalRoot_stage_transport
    (base := base) hstage hroot
  have hrightSupport := uniformShiftCanonicalRoot_sameSupport
    (padding := later - earlier) hsource
  rw [hbaseEq] at hrightSupport
  exact sameSupport_trans hstageSupport (sameSupport_symm hrightSupport)

theorem centeredRecedingStageRoots_eq_uniformShift_between
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    centeredRecedingStageRoots base later roots =
      (centeredRecedingStageRoots base earlier roots).map
        (uniformShiftCanonicalRoot (later - earlier)
          (centeredRecedingStageBase base earlier)) := by
  unfold centeredRecedingStageRoots centeredRecedingStageRadius
    centeredOffsetCylinderRoots centeredRecedingStageBase
  rw [List.map_map]
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply]
  exact centeredOffsetCanonicalRoot_eq_uniformShift_between hstage
    (hroots root hroot)

theorem centeredRecedingCylinderEvent_eq_uniformShift_between
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    centeredRecedingCylinderEvent base later roots predicate =
      uniformShiftTargetCylinderEvent (later - earlier)
        (centeredRecedingStageBase base earlier)
        (centeredRecedingStageRoots base earlier roots) predicate := by
  unfold centeredRecedingCylinderEvent uniformShiftTargetCylinderEvent
    uniformShiftedCylinderRoots
  rw [centeredRecedingStageRoots_eq_uniformShift_between hstage hroots]

theorem centeredRecedingCylinderEvent_eq_source_at
    (base stage : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) :
    centeredRecedingCylinderEvent base stage roots predicate =
      sourceCylinderEvent (centeredRecedingStageRoots base stage roots)
        predicate := rfl

/-! ## 3. Canonical marked atoms and the receding protected core -/

def uniformShiftCylinderCanonicalAtoms
    (padding base : Nat) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    List (CanonicalAtom (uniformPaddedBase padding base)) :=
  roots.attach.map (fun root =>
    ⟨uniformShiftCanonicalRoot padding base root.val,
      uniformShiftCanonicalRoot_canonical
        (hroots root.val root.property)⟩)

theorem uniformShiftCylinderCanonicalAtoms_length
    (padding base : Nat) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (uniformShiftCylinderCanonicalAtoms
      padding base roots hroots).length = roots.length := by
  unfold uniformShiftCylinderCanonicalAtoms
  rw [List.length_map, List.length_attach]

theorem uniformShiftCylinderCanonicalAtoms_values
    (padding base : Nat) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (uniformShiftCylinderCanonicalAtoms padding base roots hroots).map
        Subtype.val =
      uniformShiftedCylinderRoots padding base roots := by
  unfold uniformShiftCylinderCanonicalAtoms uniformShiftedCylinderRoots
  calc
    _ = roots.attach.map (fun root =>
          uniformShiftCanonicalRoot padding base root.val) := by
        rw [List.map_map]
        rfl
    _ = (roots.attach.map Subtype.val).map
          (uniformShiftCanonicalRoot padding base) := by
        rw [List.map_map]
        rfl
    _ = roots.map (uniformShiftCanonicalRoot padding base) := by
        rw [List.attach_map_subtype_val]

theorem uniformShiftMarkedCylinderEvent_canonicalAtoms
    (padding base : Nat) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    uniformShiftMarkedCylinderEvent
        (uniformShiftCylinderCanonicalAtoms padding base roots hroots)
        predicate =
      uniformShiftTargetCylinderEvent padding base roots predicate := by
  unfold uniformShiftMarkedCylinderEvent uniformShiftTargetCylinderEvent
  rw [uniformShiftCylinderCanonicalAtoms_values]

theorem uniformShiftCylinderCanonicalAtoms_inside
    (padding base : Nat) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target,
      target ∈ uniformShiftCylinderCanonicalAtoms
        padding base roots hroots →
        targetRootInsideUniformShiftB padding base target.val = true := by
  intro target htarget
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget
  subst target
  apply (targetRootInsideUniformShiftB_true_iff padding base _).2
  exact targetRootInside_uniformShiftCanonicalRoot
    (hroots source.val source.property)

def uniformShiftCanonicalAtomStart {n : Nat}
    (root : CanonicalAtom n) : Nat :=
  (canonicalSurfacePolymers_allNonempty
    n root.val root.property).1

theorem uniformShiftCanonicalAtomStart_mem {n : Nat}
    (root : CanonicalAtom n) :
    uniformShiftCanonicalAtomStart root ∈ root.val :=
  (canonicalSurfacePolymers_allNonempty
    n root.val root.property).2

theorem centeredRecedingUniformShiftCanonicalAtoms_core
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    let sourceBase := centeredRecedingStageBase base earlier
    let padding := later - earlier
    let sourceRoots := centeredRecedingStageRoots base earlier roots
    let hsourceRoots : ∀ root, root ∈ sourceRoots →
        root ∈ canonicalSurfacePolymers sourceBase :=
      centeredRecedingStageRoots_canonical hroots
    ∀ target,
      target ∈ uniformShiftCylinderCanonicalAtoms
        padding sourceBase sourceRoots hsourceRoots →
      insideShiftedBoxB
        (addUniform (uniformShiftCellLower padding) earlier)
        (centeredBoxBase base)
        (boxPlaquetteAt (uniformPaddedBase padding sourceBase)
          (uniformShiftCanonicalAtomStart target)) = true := by
  intro sourceBase padding sourceRoots hsourceRoots target htarget
  let start : Nat := uniformShiftCanonicalAtomStart target
  change insideShiftedBoxB
      (addUniform (uniformShiftCellLower padding) earlier)
      (centeredBoxBase base)
      (boxPlaquetteAt (uniformPaddedBase padding sourceBase) start) = true
  have htargetValue : target.val ∈
      (uniformShiftCylinderCanonicalAtoms
        padding sourceBase sourceRoots hsourceRoots).map Subtype.val :=
    List.mem_map.mpr ⟨target, htarget, rfl⟩
  rw [uniformShiftCylinderCanonicalAtoms_values] at htargetValue
  have htargetLate : target.val ∈
      centeredRecedingStageRoots base later roots := by
    rw [centeredRecedingStageRoots_eq_uniformShift_between
      hstage hroots]
    exact htargetValue
  unfold centeredRecedingStageRoots centeredOffsetCylinderRoots at htargetLate
  obtain ⟨sourceRoot, hsourceRoot, hrootEq⟩ :=
    List.mem_map.mp htargetLate
  have hstart : start ∈
      centeredOffsetCanonicalRoot
        (centeredRecedingStageRadius base later) base sourceRoot := by
    rw [hrootEq]
    exact uniformShiftCanonicalAtomStart_mem target
  have hcore := centeredOffsetCanonicalRoot_inside_receding_core
    hstage (hroots sourceRoot hsourceRoot) hstart
  have hbaseEq : uniformPaddedBase padding sourceBase =
      centeredBoxBase (base + later) := by
    dsimp only [padding, sourceBase]
    rw [← centeredRecedingStageBase_eq_uniformPadded_between hstage]
    rfl
  rw [hbaseEq]
  simpa only [uniformShiftCellLower, uniformNatLower,
    centeredRecedingStageRadius] using hcore

/-! ## 4. The derived finite boundary scale and its dyadic interface -/

theorem uniformShiftSpinSummedCylinderBoundaryEpsilon_le_standard
    (rootCount distance : Nat) :
    uniformShiftSpinSummedCylinderBoundaryEpsilon rootCount distance ≤
      spinSummedCylinderBoundaryEpsilon rootCount distance := by
  unfold uniformShiftSpinSummedCylinderBoundaryEpsilon
    spinSummedCylinderBoundaryEpsilon
  apply Q'.mul_le_mul_of_nonneg_left
  · exact Q'.add_le_self_of_nonneg
      (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2)
      (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2)
      (Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedEffectiveRatio
          anchorDecoratedEffectiveRatio_nonnegative (distance + 2))
        (by decide))
  · exact ExpNeg.ofNat_nonneg' rootCount

theorem uniformShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
    (rootCount distance : Nat) :
    uniformShiftSpinSummedCylinderBoundaryEpsilon rootCount distance ≤
      spinSummedCylinderBoundaryCoefficient rootCount *
        HalfPow.half ^ distance := by
  exact Q'.le_trans' _ _ _
    (uniformShiftSpinSummedCylinderBoundaryEpsilon_le_standard
      rootCount distance)
    (spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      rootCount distance)

/-! ## 5. Exact finite stability input and the full-target/source bridge -/

/-- The exact Boolean-cylinder finite estimate still owed by the uniform
connected-carrier pipeline.  This declaration merely names its full theorem
type; no inhabitant is constructed or assumed. -/
def UniformShiftTargetCylinderStabilityBound
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling) : Prop :=
  ∀ (cutoff padding base : Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool),
    (∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true) →
    ∀ (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat),
    (∀ root, root ∈ roots → rootStart root ∈ root.val) →
    ∀ (lower : Z4Vertex) (inner distance : Nat),
    (∀ root, root ∈ roots →
      insideShiftedBoxB (addUniform lower distance) inner
        (boxPlaquetteAt (uniformPaddedBase padding base)
          (rootStart root)) = true) →
    (∀ plaquette,
      plaquette ∉ uniformShiftedPlaquetteList padding base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) →
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (uniformPaddedBase padding base)
            (uniformShiftMarkedCylinderEvent roots predicate) -
          couplingParametricKUniformShiftEmbeddedTargetEventProbability
            coupling hcoupling cutoff padding base
            (uniformShiftMarkedCylinderEvent roots predicate)) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon
        roots.length distance

/-- The connected-carrier target stability theorem inhabits the exact bridge
interface throughout the constructively derived strong-coupling window. -/
theorem uniformShiftTargetCylinderStabilityBound_of_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    UniformShiftTargetCylinderStabilityBound coupling hcoupling := by
  intro cutoff padding base roots predicate hrootsInside
    rootStart hstartMem lower inner distance hrootCore houterExit
  exact
    Z4UniformShiftTargetCylinderStability.couplingParametricKUniformShiftTargetCylinderProbability_abs_sub_embedded_le
      hcoupling hle cutoff hrootsInside rootStart hstartMem
        hrootCore houterExit

theorem couplingParametricKUniformShiftFullTargetProbability_abs_sub_source_le_of_bound
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hbound : UniformShiftTargetCylinderStabilityBound coupling hcoupling)
    (cutoff padding base : Nat)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool)
    {inner distance : Nat}
    (hside : inner + distance + distance = base)
    (hcore : ∀ target,
      target ∈ uniformShiftCylinderCanonicalAtoms
        padding base roots hroots →
      insideShiftedBoxB
        (addUniform (uniformShiftCellLower padding) distance) inner
        (boxPlaquetteAt (uniformPaddedBase padding base)
          (uniformShiftCanonicalAtomStart target)) = true) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (uniformPaddedBase padding base)
            (uniformShiftTargetCylinderEvent
              padding base roots predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff base
            (sourceCylinderEvent roots predicate)) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon
        roots.length distance := by
  let targetRoots :=
    uniformShiftCylinderCanonicalAtoms padding base roots hroots
  have htargetInside : ∀ target, target ∈ targetRoots →
      targetRootInsideUniformShiftB padding base target.val = true :=
    uniformShiftCylinderCanonicalAtoms_inside padding base roots hroots
  have htargetBound := hbound cutoff padding base targetRoots predicate
    htargetInside uniformShiftCanonicalAtomStart
    (fun root _ => uniformShiftCanonicalAtomStart_mem root)
    (uniformShiftCellLower padding) inner distance
    (fun root hroot => hcore root hroot)
    (fun plaquette hplaquette =>
      outside_uniformShiftCell_of_not_mem_of_side_eq
        hside hplaquette)
  have hevent : uniformShiftMarkedCylinderEvent targetRoots predicate =
      uniformShiftTargetCylinderEvent padding base roots predicate :=
    uniformShiftMarkedCylinderEvent_canonicalAtoms
      padding base roots hroots predicate
  rw [hevent] at htargetBound
  have hsource :=
    couplingParametricKCompatibleCylinderProbability_eqv_embedded_uniformShift
      coupling hcoupling cutoff (padding := padding) (base := base)
      hroots predicate
  let fullProbability :=
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff (uniformPaddedBase padding base)
      (uniformShiftTargetCylinderEvent padding base roots predicate)
  let sourceProbability :=
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff base
      (sourceCylinderEvent roots predicate)
  let embeddedProbability :=
    couplingParametricKUniformShiftEmbeddedTargetEventProbability
      coupling hcoupling cutoff padding base
      (uniformShiftTargetCylinderEvent padding base roots predicate)
  have hdifference :
      (fullProbability - sourceProbability) ≈
        (fullProbability - embeddedProbability) :=
    Q'.add_eqv_congr_left fullProbability
      (-sourceProbability) (-embeddedProbability)
      (Q'.neg_eqv_congr sourceProbability embeddedProbability hsource)
  have habs : Q'.abs (fullProbability - sourceProbability) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon
        targetRoots.length distance :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) htargetBound
  simpa only [targetRoots,
    uniformShiftCylinderCanonicalAtoms_length] using habs

/-! ## 6. The centered receding modulus from the exact finite estimate -/

theorem centeredRecedingVolumeModulus_of_uniformShiftTargetBound
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hbound : UniformShiftTargetCylinderStabilityBound coupling hcoupling)
    {base : Nat} {roots : List (List Nat)}
    {predicate : List Bool → Bool}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    CenteredRecedingVolumeModulus
      coupling hcoupling base roots predicate := by
  refine ⟨hroots, ?_⟩
  intro cutoff earlier later hstage
  let sourceBase := centeredRecedingStageBase base earlier
  let padding := later - earlier
  let sourceRoots := centeredRecedingStageRoots base earlier roots
  have hsourceRoots : ∀ root, root ∈ sourceRoots →
      root ∈ canonicalSurfacePolymers sourceBase :=
    centeredRecedingStageRoots_canonical hroots
  have hside : centeredBoxBase base + earlier + earlier = sourceBase := by
    dsimp only [sourceBase, centeredRecedingStageBase,
      centeredRecedingStageRadius]
    exact centeredBoxBase_stage_side base earlier
  have hcore : ∀ target,
      target ∈ uniformShiftCylinderCanonicalAtoms
        padding sourceBase sourceRoots hsourceRoots →
      insideShiftedBoxB
        (addUniform (uniformShiftCellLower padding) earlier)
        (centeredBoxBase base)
        (boxPlaquetteAt (uniformPaddedBase padding sourceBase)
          (uniformShiftCanonicalAtomStart target)) = true := by
    dsimp only [padding, sourceBase, sourceRoots]
    exact centeredRecedingUniformShiftCanonicalAtoms_core
      hstage hroots
  have hraw :=
    couplingParametricKUniformShiftFullTargetProbability_abs_sub_source_le_of_bound
      hcoupling hbound cutoff padding sourceBase hsourceRoots predicate
      hside hcore
  have hconverted := Q'.le_trans' _ _ _ hraw
    (uniformShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      sourceRoots.length earlier)
  dsimp only [padding, sourceBase, sourceRoots] at hconverted
  rw [← centeredRecedingStageBase_eq_uniformPadded_between hstage]
    at hconverted
  rw [← centeredRecedingCylinderEvent_eq_uniformShift_between
    hstage hroots predicate] at hconverted
  simpa only [centeredRecedingCylinderEvent_eq_source_at,
    centeredRecedingStageRoots_length] using hconverted

/-! ## 7. Unconditional strong-coupling diagonal and presentation values -/

theorem centeredRecedingVolumeModulus_of_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    {predicate : List Bool → Bool}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    CenteredRecedingVolumeModulus
      coupling hcoupling base roots predicate :=
  centeredRecedingVolumeModulus_of_uniformShiftTargetBound hcoupling
    (uniformShiftTargetCylinderStabilityBound_of_anchor hcoupling hle)
    hroots

/-- The centered receding cylinder limit with the volume modulus discharged
by the uniform-shift stability theorem. -/
def couplingParametricCenteredRecedingCylinderLimitAtAnchor
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (predicate : List Bool → Bool)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) : CReal :=
  couplingParametricCenteredRecedingCylinderLimitOfVolumeModulus
    coupling hcoupling hle predicate
    (centeredRecedingVolumeModulus_of_anchor
      hcoupling hle hroots)

@[simp] theorem couplingParametricCenteredRecedingCylinderLimitAtAnchor_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (predicate : List Bool → Bool)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (couplingParametricCenteredRecedingCylinderLimitAtAnchor
      coupling hcoupling hle predicate hroots).approx stage =
      couplingParametricCenteredRecedingCylinderSequence
        coupling hcoupling base roots predicate stage := rfl

theorem couplingParametricCenteredRecedingCylinderLimitAtAnchor_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (predicate : List Bool → Bool)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    CReal.ofQ' 0 ≤
      couplingParametricCenteredRecedingCylinderLimitAtAnchor
        coupling hcoupling hle predicate hroots := by
  exact
    Z4SignedCenteredRecedingDiagonal.couplingParametricCenteredRecedingCylinderLimit_nonnegative
      hcoupling hle predicate
      (centeredRecedingVolumeModulus_of_anchor hcoupling hle hroots)

theorem couplingParametricCenteredRecedingCylinderLimitAtAnchor_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (predicate : List Bool → Bool)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    couplingParametricCenteredRecedingCylinderLimitAtAnchor
        coupling hcoupling hle predicate hroots ≤ CReal.ofQ' 1 := by
  exact
    Z4SignedCenteredRecedingDiagonal.couplingParametricCenteredRecedingCylinderLimit_le_one
      hcoupling hle predicate
      (centeredRecedingVolumeModulus_of_anchor hcoupling hle hroots)

theorem signedCenteredPresentationVolumeModulus_of_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : SignedCenteredCylinderPresentation) :
    SignedCenteredPresentationVolumeModulus
      coupling hcoupling presentation :=
  centeredRecedingVolumeModulus_of_anchor hcoupling hle
    (signedCenteredPresentation_rootsCanonical presentation)

/-- The signed `Int^4` presentation value with no remaining volume-modulus
argument. -/
def couplingParametricSignedCenteredPresentationValueAtAnchor
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : SignedCenteredCylinderPresentation) : CReal :=
  couplingParametricSignedCenteredPresentationValueOfVolumeModulus
    coupling hcoupling hle presentation
    (signedCenteredPresentationVolumeModulus_of_anchor
      hcoupling hle presentation)

@[simp] theorem couplingParametricSignedCenteredPresentationValueAtAnchor_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : SignedCenteredCylinderPresentation) (stage : Nat) :
    (couplingParametricSignedCenteredPresentationValueAtAnchor
      coupling hcoupling hle presentation).approx stage =
      couplingParametricSignedCenteredPresentationSequence
        coupling hcoupling presentation stage := rfl

theorem couplingParametricSignedCenteredPresentationValueAtAnchor_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : SignedCenteredCylinderPresentation) :
    CReal.ofQ' 0 ≤
      couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle presentation := by
  exact
    Z4SignedCenteredRecedingPresentation.couplingParametricSignedCenteredPresentationValue_nonnegative
      hcoupling hle presentation
      (signedCenteredPresentationVolumeModulus_of_anchor
        hcoupling hle presentation)

theorem couplingParametricSignedCenteredPresentationValueAtAnchor_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : SignedCenteredCylinderPresentation) :
    couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle presentation ≤ CReal.ofQ' 1 := by
  exact
    Z4SignedCenteredRecedingPresentation.couplingParametricSignedCenteredPresentationValue_le_one
      hcoupling hle presentation
      (signedCenteredPresentationVolumeModulus_of_anchor
        hcoupling hle presentation)

theorem couplingParametricSignedCenteredPresentationValueAtAnchor_translate
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (shift : SignedZ4Vector)
    (presentation : SignedCenteredCylinderPresentation) :
    CReal.Equiv
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle (presentation.translate shift))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle presentation) := by
  exact
    Z4SignedCenteredRecedingPresentation.couplingParametricSignedCenteredPresentationValue_translate
      hcoupling hle shift presentation
      (signedCenteredPresentationVolumeModulus_of_anchor
        hcoupling hle presentation)

#print axioms mem_uniformShiftedPlaquetteList_iff_coordinates
#print axioms outside_uniformShiftCell_of_not_mem
#print axioms centeredRecedingStageBase_eq_uniformPadded_between
#print axioms centeredOffsetCanonicalRoot_eq_uniformShift_between
#print axioms centeredRecedingStageRoots_eq_uniformShift_between
#print axioms centeredRecedingCylinderEvent_eq_uniformShift_between
#print axioms uniformShiftCylinderCanonicalAtoms_values
#print axioms uniformShiftCylinderCanonicalAtoms_inside
#print axioms centeredRecedingUniformShiftCanonicalAtoms_core
#print axioms uniformShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
#print axioms couplingParametricKUniformShiftFullTargetProbability_abs_sub_source_le_of_bound
#print axioms centeredRecedingVolumeModulus_of_uniformShiftTargetBound
#print axioms uniformShiftTargetCylinderStabilityBound_of_anchor
#print axioms centeredRecedingVolumeModulus_of_anchor
#print axioms couplingParametricCenteredRecedingCylinderLimitAtAnchor
#print axioms couplingParametricCenteredRecedingCylinderLimitAtAnchor_nonnegative
#print axioms couplingParametricCenteredRecedingCylinderLimitAtAnchor_le_one
#print axioms signedCenteredPresentationVolumeModulus_of_anchor
#print axioms couplingParametricSignedCenteredPresentationValueAtAnchor
#print axioms couplingParametricSignedCenteredPresentationValueAtAnchor_nonnegative
#print axioms couplingParametricSignedCenteredPresentationValueAtAnchor_le_one
#print axioms couplingParametricSignedCenteredPresentationValueAtAnchor_translate

end YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
