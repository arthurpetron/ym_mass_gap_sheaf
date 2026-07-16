/-
# Signed-centered recoding of the doubled-time mixed strict cylinder

At a source stage large enough to contain the doubled time translate, the
oriented mixed lower/upper chart can be re-encoded in the adjacent odd
centered box.  The translated target chart is then the canonical pure-spatial
re-encoding of this mixed centered chart in the box whose radius is larger by
`shift`.

In absolute signed coordinates (where the center of the radius-`r` corner
box is declared to be `(r,r,r,r)`), the target supports are translated by
the signed vector `(shift,shift,shift,0)`.  This is the exact geometric input
needed by signed translation covariance.  The final section records the
remaining representation-descent issue: the existing signed translation
theorem applies to a literal chart translation, while the strict target also
changes the chart radius and canonical numerical roots.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedEventRecoding
import YMGap.Continuum.Z4SignedCenteredFiniteColimitDescent

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderPresentationColimit
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedEventRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredExhaustion
open YMGap.Continuum.Z4SignedCenteredFiniteColimitDescent
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

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

/-! ## 1. Aligned radii -/

theorem strictJointDoubledTime_mixedRadius_eq
    {base shift stage : Nat} (hstage : shift + shift ≤ stage) :
    strictQueryBase (base + (shift + shift)) +
        (stage - (shift + shift)) =
      strictQueryBase base + stage := by
  unfold strictQueryBase uniformPaddedBase
  omega

theorem strictJointDoubledTime_targetRadius_eq
    (base shift stage : Nat) :
    strictQueryBase (base + shift) + stage =
      (strictQueryBase base + stage) + shift := by
  unfold strictQueryBase uniformPaddedBase
  omega

theorem uniformPaddedBase_centeredBoxBase
    (radius shift : Nat) :
    uniformPaddedBase shift (centeredBoxBase radius) =
      centeredBoxBase (radius + shift) := by
  unfold uniformPaddedBase centeredBoxBase
  omega

/-! ## 2. The oriented mixed chart in the odd centered box -/

def strictJointDoubledTimeMixedCenteredLowerRoot
    (base shift stage : Nat) (root : List Nat) : List Nat :=
  centralStrictLowerCenteredStageRoot base stage root

def strictJointDoubledTimeMixedCenteredUpperRoot
    (base shift stage : Nat) (root : List Nat) : List Nat :=
  centralStrictUpperCenteredStageRoot
    (base + (shift + shift)) (stage - (shift + shift))
    (timeShiftCanonicalRoot (shift + shift) base root)

def strictJointDoubledTimeMixedCenteredRoots
    (base shift stage : Nat) (roots : List (List Nat)) :
    List (List Nat) :=
  roots.map
      (strictJointDoubledTimeMixedCenteredLowerRoot base shift stage) ++
    roots.map
      (strictJointDoubledTimeMixedCenteredUpperRoot base shift stage)

@[simp] theorem strictJointDoubledTimeMixedCenteredRoots_length
    (base shift stage : Nat) (roots : List (List Nat)) :
    (strictJointDoubledTimeMixedCenteredRoots
      base shift stage roots).length = roots.length + roots.length := by
  simp [strictJointDoubledTimeMixedCenteredRoots]

theorem strictJointDoubledTimeMixedCenteredLowerRoot_canonical
    {base shift stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    strictJointDoubledTimeMixedCenteredLowerRoot
        base shift stage root ∈
      canonicalSurfacePolymers
        (centeredBoxBase (strictQueryBase base + stage)) := by
  have hsource := centralStrictLowerCenteredSourceRoot_canonical hroot
  have hshifted := uniformShiftCanonicalRoot_canonical
    (padding := stage) hsource
  rw [strictJointCenteredStageBase_eq] at hshifted
  exact hshifted

theorem strictJointDoubledTimeMixedCenteredUpperRoot_canonical
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    strictJointDoubledTimeMixedCenteredUpperRoot
        base shift stage root ∈
      canonicalSurfacePolymers
        (centeredBoxBase (strictQueryBase base + stage)) := by
  have htranslated := timeShiftCanonicalRoot_canonical
    (shift := shift + shift) hroot
  have hsource := centralStrictUpperCenteredSourceRoot_canonical
    htranslated
  have hshifted := uniformShiftCanonicalRoot_canonical
    (padding := stage - (shift + shift)) hsource
  rw [strictJointCenteredStageBase_eq] at hshifted
  rw [strictJointDoubledTime_mixedRadius_eq hstage] at hshifted
  exact hshifted

theorem strictJointDoubledTimeMixedCenteredRoots_canonical
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target,
      target ∈ strictJointDoubledTimeMixedCenteredRoots
          base shift stage roots →
        target ∈ canonicalSurfacePolymers
          (centeredBoxBase (strictQueryBase base + stage)) := by
  intro target htarget
  rcases List.mem_append.mp htarget with hlower | hupper
  · obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hlower
    exact strictJointDoubledTimeMixedCenteredLowerRoot_canonical
      (hroots root hroot)
  · obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hupper
    exact strictJointDoubledTimeMixedCenteredUpperRoot_canonical
      hstage (hroots root hroot)

theorem strictJointDoubledTimeMixedLowerRoot_eq_transport_centered
    {base shift stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    strictJointDoubledTimeMixedLowerRoot
        (strictQueryBase base + stage) base shift root =
      transportPolymer
        (centeredBoxBase (strictQueryBase base + stage))
        (centralAmbient (strictQueryBase base + stage))
        (strictJointDoubledTimeMixedCenteredLowerRoot
          base shift stage root) := by
  exact centralStrictLowerCanonicalRoot_eq_transport_centeredStage hroot

theorem strictJointDoubledTimeMixedUpperRoot_eq_transport_centered
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    strictJointDoubledTimeMixedUpperRoot
        (strictQueryBase base + stage) base shift root =
      transportPolymer
        (centeredBoxBase (strictQueryBase base + stage))
        (centralAmbient (strictQueryBase base + stage))
        (strictJointDoubledTimeMixedCenteredUpperRoot
          base shift stage root) := by
  have htranslated := timeShiftCanonicalRoot_canonical
    (shift := shift + shift) hroot
  have htransport :=
    centralStrictUpperCanonicalRoot_eq_transport_centeredStage
      (base := base + (shift + shift))
      (stage := stage - (shift + shift)) htranslated
  rw [strictJointDoubledTime_mixedRadius_eq hstage] at htransport
  exact htransport

/-! ## 3. Literal centered-root equality after the spatial shift -/

theorem timeTranslatedStrictJointLowerCenteredRoot_eq_spatialMixed
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictLowerCenteredStageRoot (base + shift) stage
        (timeShiftCanonicalRoot shift base root) =
      spatialShiftCanonicalRoot shift
        (centeredBoxBase (strictQueryBase base + stage))
        (strictJointDoubledTimeMixedCenteredLowerRoot
          base shift stage root) := by
  have htranslated := timeShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htargetCanonicalSource :=
    centralStrictLowerCenteredSourceRoot_canonical htranslated
  have htargetCanonical := uniformShiftCanonicalRoot_canonical
    (padding := stage) htargetCanonicalSource
  rw [strictJointCenteredStageBase_eq,
    strictJointDoubledTime_targetRadius_eq] at htargetCanonical
  have hmixedCanonical :=
    strictJointDoubledTimeMixedCenteredLowerRoot_canonical
      (shift := shift) (stage := stage) hroot
  have hspatialCanonical := spatialShiftCanonicalRoot_canonical
    (shift := shift) hmixedCanonical
  rw [uniformPaddedBase_centeredBoxBase] at hspatialCanonical
  have htargetLe := strictJointCenteredStageBase_le_centralAmbient
    (base + shift) stage
  rw [strictJointDoubledTime_targetRadius_eq] at htargetLe
  apply transportPolymer_injective_on_canonical htargetLe
    htargetCanonical hspatialCanonical
  have htargetTransport :=
    centralStrictLowerCanonicalRoot_eq_transport_centeredStage
      (base := base + shift) (stage := stage) htranslated
  rw [strictJointDoubledTime_targetRadius_eq] at htargetTransport
  have hspatialTransport := spatialShiftCanonicalRoot_transport
    (shift := shift)
    (strictJointCenteredStageBase_le_centralAmbient base stage)
    hmixedCanonical
  rw [uniformPaddedBase_centeredBoxBase,
    uniformPaddedBase_centralAmbient] at hspatialTransport
  rw [← strictJointDoubledTimeMixedLowerRoot_eq_transport_centered
    (shift := shift) (stage := stage) hroot] at hspatialTransport
  have hadmissible :
      strictQueryBase (base + (shift + shift)) ≤
        strictQueryBase base + stage := by
    unfold strictQueryBase uniformPaddedBase
    omega
  have hcentral := timeTranslatedStrictJointLowerRoot_eq_spatialMixed
    (shift := shift) hadmissible hroot
  exact Eq.trans htargetTransport.symm
    (Eq.trans hcentral hspatialTransport.symm)

theorem timeTranslatedStrictJointUpperCenteredRoot_eq_spatialMixed
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictUpperCenteredStageRoot (base + shift) stage
        (timeShiftCanonicalRoot shift base root) =
      spatialShiftCanonicalRoot shift
        (centeredBoxBase (strictQueryBase base + stage))
        (strictJointDoubledTimeMixedCenteredUpperRoot
          base shift stage root) := by
  have htranslated := timeShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htargetCanonicalSource :=
    centralStrictUpperCenteredSourceRoot_canonical htranslated
  have htargetCanonical := uniformShiftCanonicalRoot_canonical
    (padding := stage) htargetCanonicalSource
  rw [strictJointCenteredStageBase_eq,
    strictJointDoubledTime_targetRadius_eq] at htargetCanonical
  have hmixedCanonical :=
    strictJointDoubledTimeMixedCenteredUpperRoot_canonical
      hstage hroot
  have hspatialCanonical := spatialShiftCanonicalRoot_canonical
    (shift := shift) hmixedCanonical
  rw [uniformPaddedBase_centeredBoxBase] at hspatialCanonical
  have htargetLe := strictJointCenteredStageBase_le_centralAmbient
    (base + shift) stage
  rw [strictJointDoubledTime_targetRadius_eq] at htargetLe
  apply transportPolymer_injective_on_canonical htargetLe
    htargetCanonical hspatialCanonical
  have htargetTransport :=
    centralStrictUpperCanonicalRoot_eq_transport_centeredStage
      (base := base + shift) (stage := stage) htranslated
  rw [strictJointDoubledTime_targetRadius_eq] at htargetTransport
  have hadmissible :
      strictQueryBase (base + (shift + shift)) ≤
        strictQueryBase base + stage := by
    unfold strictQueryBase uniformPaddedBase
    omega
  have hspatialTransport := spatialShiftCanonicalRoot_transport
    (shift := shift)
    (strictJointCenteredStageBase_le_centralAmbient base stage)
    hmixedCanonical
  rw [uniformPaddedBase_centeredBoxBase,
    uniformPaddedBase_centralAmbient] at hspatialTransport
  rw [← strictJointDoubledTimeMixedUpperRoot_eq_transport_centered
    (shift := shift) hstage hroot] at hspatialTransport
  have hcentral := timeTranslatedStrictJointUpperRoot_eq_spatialMixed
    (shift := shift) hadmissible hroot
  exact Eq.trans htargetTransport.symm
    (Eq.trans hcentral hspatialTransport.symm)

theorem timeTranslatedStrictJointCenteredRoots_eq_spatialMixed
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    centralStrictJointCenteredStageRoots (base + shift) stage
        (roots.map (timeShiftCanonicalRoot shift base)) =
      (strictJointDoubledTimeMixedCenteredRoots
        base shift stage roots).map
          (spatialShiftCanonicalRoot shift
            (centeredBoxBase (strictQueryBase base + stage))) := by
  rw [centralStrictJointCenteredStageRoots_split]
  unfold strictJointDoubledTimeMixedCenteredRoots
  rw [List.map_append, List.map_map, List.map_map,
    List.map_map, List.map_map]
  have hlower :
      roots.map
          (centralStrictLowerCenteredStageRoot (base + shift) stage ∘
            timeShiftCanonicalRoot shift base) =
        roots.map
          (spatialShiftCanonicalRoot shift
              (centeredBoxBase (strictQueryBase base + stage)) ∘
            strictJointDoubledTimeMixedCenteredLowerRoot
              base shift stage) := by
    apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact timeTranslatedStrictJointLowerCenteredRoot_eq_spatialMixed
      hstage (hroots root hroot)
  have hupper :
      roots.map
          (centralStrictUpperCenteredStageRoot (base + shift) stage ∘
            timeShiftCanonicalRoot shift base) =
        roots.map
          (spatialShiftCanonicalRoot shift
              (centeredBoxBase (strictQueryBase base + stage)) ∘
            strictJointDoubledTimeMixedCenteredUpperRoot
              base shift stage) := by
    apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact timeTranslatedStrictJointUpperCenteredRoot_eq_spatialMixed
      hstage (hroots root hroot)
  rw [hlower, hupper]

/-! ## 4. Absolute signed supports and the zero-time translation -/

/-- Center which makes the signed coordinate of a natural corner-box cell
literally its nonnegative natural coordinate. -/
def signedNaturalCornerCenter (radius : Nat) : SignedZ4Vector :=
  (Int.ofNat radius, Int.ofNat radius,
    Int.ofNat radius, Int.ofNat radius)

/-- The physical translation left by the doubled-time reflection geometry:
three positive spatial coordinates and zero Euclidean-time coordinate. -/
def signedNatSpatialShift (shift : Nat) : SignedZ4Vector :=
  (Int.ofNat shift, Int.ofNat shift, Int.ofNat shift, 0)

theorem signedNaturalCornerCenter_centeredPlaquette
    (radius : Nat) (plaquette : Z4Plaq) :
    signedTranslatePlaquette (signedNaturalCornerCenter radius)
        (natPlaquetteToCenteredSigned radius plaquette) =
      natPlaquetteToSigned plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  apply Prod.ext
  · simp [signedNaturalCornerCenter, signedTranslatePlaquette,
      signedTranslateVertex, signedAdd, natPlaquetteToCenteredSigned,
      natVertexToCenteredSigned, natCoordinateToCenteredSigned,
      natPlaquetteToSigned, natVertexToSigned]
  · rfl

theorem natPlaquetteToSigned_spatialShift
    (shift : Nat) (plaquette : Z4Plaq) :
    natPlaquetteToSigned (spatialShiftPlaquette shift plaquette) =
      signedTranslatePlaquette (signedNatSpatialShift shift)
        (natPlaquetteToSigned plaquette) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  apply Prod.ext
  · simp [signedNatSpatialShift, signedTranslatePlaquette,
      signedTranslateVertex, signedAdd, natPlaquetteToSigned,
      natVertexToSigned, spatialShiftPlaquette, spatialShiftVertex]
  · rfl

/-- A spatially re-encoded canonical root has exactly the translated
absolute signed support.  The use of the natural-corner centers is what
keeps the fourth component of the signed translation equal to zero. -/
theorem spatialShiftCanonicalRoot_absoluteSignedSupport_iff
    {radius shift : Nat} {root : List Nat}
    (hroot : root ∈
      canonicalSurfacePolymers (centeredBoxBase radius))
    (plaquette : SignedZ4Plaq) :
    plaquette ∈
        (geometricPolymer (centeredBoxBase (radius + shift))
            (spatialShiftCanonicalRoot shift
              (centeredBoxBase radius) root)).map
          (fun target =>
            signedTranslatePlaquette
              (signedNaturalCornerCenter (radius + shift))
              (natPlaquetteToCenteredSigned
                (radius + shift) target)) ↔
      plaquette ∈
        ((geometricPolymer (centeredBoxBase radius) root).map
            (fun source =>
              signedTranslatePlaquette
                (signedNaturalCornerCenter radius)
                (natPlaquetteToCenteredSigned radius source))).map
          (signedTranslatePlaquette (signedNatSpatialShift shift)) := by
  have hsupport := spatialShiftCanonicalRoot_sameSupport
    (shift := shift) hroot
  rw [uniformPaddedBase_centeredBoxBase] at hsupport
  constructor
  · intro hplaquette
    obtain ⟨target, htarget, htargetEq⟩ := List.mem_map.mp hplaquette
    have hmapped := hsupport.1 target htarget
    obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hmapped
    apply List.mem_map.mpr
    refine ⟨signedTranslatePlaquette
        (signedNaturalCornerCenter radius)
        (natPlaquetteToCenteredSigned radius source), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨source, hsource, rfl⟩
    · rw [← htargetEq, ← hsourceEq,
        signedNaturalCornerCenter_centeredPlaquette,
        signedNaturalCornerCenter_centeredPlaquette,
        natPlaquetteToSigned_spatialShift]
  · intro hplaquette
    obtain ⟨sourceSigned, hsourceSigned, htranslatedEq⟩ :=
      List.mem_map.mp hplaquette
    obtain ⟨source, hsource, hsourceEq⟩ :=
      List.mem_map.mp hsourceSigned
    have hmapped : spatialShiftPlaquette shift source ∈
        (geometricPolymer (centeredBoxBase radius) root).map
          (spatialShiftPlaquette shift) :=
      List.mem_map.mpr ⟨source, hsource, rfl⟩
    have htarget := hsupport.2 _ hmapped
    apply List.mem_map.mpr
    refine ⟨spatialShiftPlaquette shift source, htarget, ?_⟩
    rw [← htranslatedEq, ← hsourceEq,
      signedNaturalCornerCenter_centeredPlaquette,
      signedNaturalCornerCenter_centeredPlaquette,
      natPlaquetteToSigned_spatialShift]

/-! ## 5. The two finite signed charts -/

def strictJointDoubledTimeMixedSignedChart
    (base shift stage : Nat) (roots : List (List Nat))
    (hstage : shift + shift ≤ stage)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    SignedCenteredCylinderChart where
  center := signedNaturalCornerCenter (strictQueryBase base + stage)
  radius := strictQueryBase base + stage
  roots := strictJointDoubledTimeMixedCenteredRoots
    base shift stage roots
  rootsCanonical :=
    strictJointDoubledTimeMixedCenteredRoots_canonical hstage hroots

def timeTranslatedStrictJointSignedChart
    (base shift stage : Nat) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    SignedCenteredCylinderChart where
  center := signedNaturalCornerCenter
    ((strictQueryBase base + stage) + shift)
  radius := (strictQueryBase base + stage) + shift
  roots := centralStrictJointCenteredStageRoots (base + shift) stage
    (roots.map (timeShiftCanonicalRoot shift base))
  rootsCanonical := by
    have htranslated : ∀ target,
        target ∈ roots.map (timeShiftCanonicalRoot shift base) →
          target ∈ canonicalSurfacePolymers (base + shift) := by
      intro target htarget
      obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp htarget
      exact timeShiftCanonicalRoot_canonical (hroots root hroot)
    have hcanonical := centralStrictJointCenteredStageRoots_canonical
      (stage := stage) htranslated
    rw [strictJointDoubledTime_targetRadius_eq] at hcanonical
    exact hcanonical

def strictJointDoubledTimeMixedSignedPresentation
    (base shift stage : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool)
    (hstage : shift + shift ≤ stage)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    SignedCenteredCylinderPresentation :=
  ⟨strictJointDoubledTimeMixedSignedChart
      base shift stage roots hstage hroots,
    predicate⟩

def timeTranslatedStrictJointSignedPresentation
    (base shift stage : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    SignedCenteredCylinderPresentation :=
  ⟨timeTranslatedStrictJointSignedChart
      base shift stage roots hroots,
    predicate⟩

/-- Exact root-list form of the signed geometric translation. -/
theorem timeTranslatedStrictJointSignedChart_roots_eq_spatialMixed
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (timeTranslatedStrictJointSignedChart
        base shift stage roots hroots).roots =
      (strictJointDoubledTimeMixedSignedChart
        base shift stage roots hstage hroots).roots.map
          (spatialShiftCanonicalRoot shift
            (centeredBoxBase (strictQueryBase base + stage))) := by
  exact timeTranslatedStrictJointCenteredRoots_eq_spatialMixed
    hstage hroots

/-- Quotient-free geometric relation between two signed charts: every
target coordinate is a specified recoding of a source coordinate and its
absolute signed support is translated by one common vector. -/
def SignedCenteredChartSupportTranslated
    (shift : SignedZ4Vector)
    (source target : SignedCenteredCylinderChart) : Prop :=
  ∃ recode : List Nat → List Nat,
    target.roots = source.roots.map recode ∧
    ∀ root, root ∈ source.roots →
      ∀ plaquette : SignedZ4Plaq,
        plaquette ∈ target.rootSupport (recode root) ↔
          plaquette ∈
            (source.rootSupport root).map
              (signedTranslatePlaquette shift)

/-- The strict translated chart and the oriented mixed chart satisfy the
support-translation relation with vector `(shift,shift,shift,0)`. -/
theorem timeTranslatedStrictJointSignedChart_supportTranslated
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    SignedCenteredChartSupportTranslated
      (signedNatSpatialShift shift)
      (strictJointDoubledTimeMixedSignedChart
        base shift stage roots hstage hroots)
      (timeTranslatedStrictJointSignedChart
        base shift stage roots hroots) := by
  let recode := spatialShiftCanonicalRoot shift
    (centeredBoxBase (strictQueryBase base + stage))
  refine ⟨recode,
    timeTranslatedStrictJointSignedChart_roots_eq_spatialMixed
      hstage hroots, ?_⟩
  intro root hroot plaquette
  have hcanonical :=
    (strictJointDoubledTimeMixedSignedChart
      base shift stage roots hstage hroots).rootsCanonical root hroot
  simpa only [SignedCenteredCylinderChart.rootSupport,
    strictJointDoubledTimeMixedSignedChart,
    timeTranslatedStrictJointSignedChart, recode] using
    (spatialShiftCanonicalRoot_absoluteSignedSupport_iff
      hcanonical plaquette)

/-- The existing signed translation theorem is stated for literal
`presentation.translate`, which preserves the chart radius.  A nonzero
strict time translation changes that radius, so the theorem cannot be
applied by definitional rewriting even though all corresponding absolute
supports are exact translates. -/
theorem timeTranslatedStrictJointSignedChart_ne_literalTranslate
    {base shift stage : Nat} (hshift : 0 < shift)
    {roots : List (List Nat)}
    (hstage : shift + shift ≤ stage)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    timeTranslatedStrictJointSignedChart
        base shift stage roots hroots ≠
      (strictJointDoubledTimeMixedSignedChart
        base shift stage roots hstage hroots).translate
          (signedNatSpatialShift shift) := by
  intro hequal
  have hradius := congrArg SignedCenteredCylinderChart.radius hequal
  simp only [timeTranslatedStrictJointSignedChart,
    strictJointDoubledTimeMixedSignedChart,
    SignedCenteredCylinderChart.translate] at hradius
  omega

/-- The exact additional descent principle needed to turn signed support
translation into equality of the already constructed values.  It is kept as
a route diagnostic and is not inhabited here. -/
def SignedCenteredSupportTranslationDescent : Prop :=
  ∀ (shift : SignedZ4Vector)
    (source target : SignedCenteredCylinderPresentation),
    source.predicate = target.predicate →
    SignedCenteredChartSupportTranslated
      shift source.chart target.chart →
    CylinderPresentationEquivalent
      (signedCenteredFinitePresentation target)
      (signedCenteredFinitePresentation (source.translate shift))

/-- Once the support-translation descent is supplied, the existing finite-
colimit descent and signed `Int^4` translation theorem close the event-level
identity.  Thus no further reflection geometry or cutoff input is hidden in
this implication. -/
theorem strictJointDoubledTime_signedValue_equiv_of_supportTranslationDescent
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (hdescent : SignedCenteredSupportTranslationDescent)
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (timeTranslatedStrictJointSignedPresentation
          base shift stage roots predicate hroots))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (strictJointDoubledTimeMixedSignedPresentation
          base shift stage roots predicate hstage hroots)) := by
  let source := strictJointDoubledTimeMixedSignedPresentation
    base shift stage roots predicate hstage hroots
  let target := timeTranslatedStrictJointSignedPresentation
    base shift stage roots predicate hroots
  have hsupport : SignedCenteredChartSupportTranslated
      (signedNatSpatialShift shift) source.chart target.chart := by
    dsimp only [source, target,
      strictJointDoubledTimeMixedSignedPresentation,
      timeTranslatedStrictJointSignedPresentation]
    exact timeTranslatedStrictJointSignedChart_supportTranslated
      hstage hroots
  have hfinite := hdescent (signedNatSpatialShift shift)
    source target (by rfl) hsupport
  have hrepresentation :=
    couplingParametricSignedCenteredPresentationValueAtAnchor_respects_finiteEquivalent
      hcoupling hle hfinite
  have htranslation :=
    couplingParametricSignedCenteredPresentationValueAtAnchor_translate
      hcoupling hle (signedNatSpatialShift shift) source
  exact CReal.Equiv.trans hrepresentation htranslation

#print axioms strictJointDoubledTimeMixedCenteredRoots_canonical
#print axioms strictJointDoubledTimeMixedUpperRoot_eq_transport_centered
#print axioms timeTranslatedStrictJointLowerCenteredRoot_eq_spatialMixed
#print axioms timeTranslatedStrictJointUpperCenteredRoot_eq_spatialMixed
#print axioms timeTranslatedStrictJointCenteredRoots_eq_spatialMixed
#print axioms spatialShiftCanonicalRoot_absoluteSignedSupport_iff
#print axioms timeTranslatedStrictJointSignedChart_roots_eq_spatialMixed
#print axioms timeTranslatedStrictJointSignedChart_supportTranslated
#print axioms timeTranslatedStrictJointSignedChart_ne_literalTranslate
#print axioms strictJointDoubledTime_signedValue_equiv_of_supportTranslationDescent

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
