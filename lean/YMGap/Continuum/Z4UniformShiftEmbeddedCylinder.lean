/-
# Exact embedded finite-cylinder law for a uniform affine padding

Every compatible source family is translated geometrically, re-ordered in
the target canonical polymer order, and proved to be a genuine compatible
target family.  Complete family activities and all finite Boolean cylinder
events are preserved.  Thus the source normalized law is exactly the law on
the translated embedded target cell.  The remaining thermodynamic step is
to compare this embedded cell with the full target gas using the shifted
connected-carrier tail.
-/

import YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
import YMGap.Continuum.Z4UniformShiftSupportActivity

namespace YMGap.Continuum.Z4UniformShiftEmbeddedCylinder

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4UniformShiftPhysicalWeights
open YMGap.Continuum.Z4UniformShiftSupportActivity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Member recovery and translated adjacency -/

def uniformShiftRootMemberSource
    {padding base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base)
    {targetFace : Nat}
    (htarget : targetFace ∈ uniformShiftCanonicalRoot padding base support) :
    Σ' sourceFace : Nat,
      (sourceFace ∈ support) ×'
        (uniformShiftPlaquette padding (boxPlaquetteAt base sourceFace) =
          boxPlaquetteAt (uniformPaddedBase padding base) targetFace) := by
  have htargetGeom : boxPlaquetteAt (uniformPaddedBase padding base) targetFace ∈
      geometricPolymer (uniformPaddedBase padding base)
        (uniformShiftCanonicalRoot padding base support) :=
    List.mem_map.mpr ⟨targetFace, htarget, rfl⟩
  have hmapped := (uniformShiftFaceSupport_sameSupport hsupport).1
    _ htargetGeom
  obtain ⟨sourcePlaquette, hsourcePlaquette, heq⟩ :=
    decodeMapMember (uniformShiftPlaquette padding)
      (geometricPolymer base support)
      (boxPlaquetteAt (uniformPaddedBase padding base) targetFace) hmapped
  obtain ⟨sourceFace, hsourceFace, hsourceEq⟩ :=
    decodeMapMember (boxPlaquetteAt base) support
      sourcePlaquette hsourcePlaquette
  subst sourcePlaquette
  exact ⟨sourceFace, hsourceFace, heq⟩

def uniformShiftRootMemberTarget
    {padding base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base)
    {sourceFace : Nat} (hsource : sourceFace ∈ support) :
    Σ' targetFace : Nat,
      (targetFace ∈ uniformShiftCanonicalRoot padding base support) ×'
        (uniformShiftPlaquette padding (boxPlaquetteAt base sourceFace) =
          boxPlaquetteAt (uniformPaddedBase padding base) targetFace) := by
  have hsourceGeom : boxPlaquetteAt base sourceFace ∈
      geometricPolymer base support :=
    List.mem_map.mpr ⟨sourceFace, hsource, rfl⟩
  have hmapped : uniformShiftPlaquette padding
      (boxPlaquetteAt base sourceFace) ∈
      (geometricPolymer base support).map
        (uniformShiftPlaquette padding) :=
    List.mem_map.mpr ⟨boxPlaquetteAt base sourceFace,
      hsourceGeom, rfl⟩
  have htargetGeom :=
    (uniformShiftFaceSupport_sameSupport hsupport).2 _ hmapped
  obtain ⟨targetFace, htargetFace, heq⟩ :=
    decodeMapMember (boxPlaquetteAt (uniformPaddedBase padding base))
      (uniformShiftCanonicalRoot padding base support)
      (uniformShiftPlaquette padding (boxPlaquetteAt base sourceFace))
      htargetGeom
  exact ⟨targetFace, htargetFace, heq.symm⟩

def unshiftActualAdjacent
    (padding : Nat) {left right : Z4Plaq}
    (hadj : z4Chain.toLattice.Adjacent
      (uniformShiftPlaquette padding left)
      (uniformShiftPlaquette padding right)) :
    z4Chain.toLattice.Adjacent left right := by
  have hleftEdge : hadj.link ∈
      edgesOf (uniformShiftPlaquette padding left) := by
    have hon := hadj.on_p
    change z4Boundary (uniformShiftPlaquette padding left) hadj.link = true at hon
    exact of_decide_eq_true hon
  have hrightEdge : hadj.link ∈
      edgesOf (uniformShiftPlaquette padding right) := by
    have hon := hadj.on_q
    change z4Boundary (uniformShiftPlaquette padding right) hadj.link = true at hon
    exact of_decide_eq_true hon
  rw [edgesOf_uniformShiftPlaquette] at hleftEdge hrightEdge
  obtain ⟨leftLink, hleftLink, hleftEq⟩ :=
    decodeMapMember (uniformShiftLink padding) (edgesOf left)
      hadj.link hleftEdge
  obtain ⟨rightLink, hrightLink, hrightEq⟩ :=
    decodeMapMember (uniformShiftLink padding) (edgesOf right)
      hadj.link hrightEdge
  have hlinkEq : leftLink = rightLink :=
    uniformShiftLink_injective padding (hleftEq.trans hrightEq.symm)
  subst rightLink
  refine {
    link := leftLink
    on_p := by
      change z4Boundary left leftLink = true
      exact decide_eq_true hleftLink
    on_q := by
      change z4Boundary right leftLink = true
      exact decide_eq_true hrightLink
  }

theorem supportsDisjoint_uniformShift
    {padding base : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports base)
    (hright : right ∈ cutoffOneFaceSupports base)
    (hdisjoint : SupportsDisjoint left right) :
    SupportsDisjoint
      (uniformShiftCanonicalRoot padding base left)
      (uniformShiftCanonicalRoot padding base right) := by
  intro targetFace htargetLeft htargetRight
  obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
    uniformShiftRootMemberSource hleft htargetLeft
  obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
    uniformShiftRootMemberSource hright htargetRight
  have hsourcePlaqEq : boxPlaquetteAt base sourceLeft =
      boxPlaquetteAt base sourceRight :=
    uniformShiftPlaquette_injective padding
      (hleftEq.trans hrightEq.symm)
  have hleftPhysical : sourceLeft ∈ physicalFaceEdges base :=
    mem_of_mem_sublists (physicalFaceEdges base) left hleft
      sourceLeft hsourceLeft
  have hrightPhysical : sourceRight ∈ physicalFaceEdges base :=
    mem_of_mem_sublists (physicalFaceEdges base) right hright
      sourceRight hsourceRight
  have hid := boxPlaquetteAt_injective_on_physical
    hleftPhysical hrightPhysical hsourcePlaqEq
  subst sourceRight
  exact hdisjoint sourceLeft hsourceLeft hsourceRight

theorem supportsSeparated_uniformShift
    {padding base : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports base)
    (hright : right ∈ cutoffOneFaceSupports base)
    (hseparated : SupportsSeparated (faceLinkAdjacentB base) left right) :
    SupportsSeparated (faceLinkAdjacentB (uniformPaddedBase padding base))
      (uniformShiftCanonicalRoot padding base left)
      (uniformShiftCanonicalRoot padding base right) := by
  intro targetLeft htargetLeft targetRight htargetRight
  cases hadjTarget : faceLinkAdjacentB (uniformPaddedBase padding base)
      targetLeft targetRight with
  | false => rfl
  | true =>
      obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
        uniformShiftRootMemberSource hleft htargetLeft
      obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
        uniformShiftRootMemberSource hright htargetRight
      have hleftPhysical : sourceLeft ∈ physicalFaceEdges base :=
        mem_of_mem_sublists (physicalFaceEdges base) left hleft
          sourceLeft hsourceLeft
      have hrightPhysical : sourceRight ∈ physicalFaceEdges base :=
        mem_of_mem_sublists (physicalFaceEdges base) right hright
          sourceRight hsourceRight
      have hadjTargetActual := actualAdjacentOfFaceLinkAdjacent hadjTarget
      have hadjShifted : z4Chain.toLattice.Adjacent
          (uniformShiftPlaquette padding (boxPlaquetteAt base sourceLeft))
          (uniformShiftPlaquette padding (boxPlaquetteAt base sourceRight)) := by
        simpa only [hleftEq, hrightEq] using hadjTargetActual
      have hadjSource := unshiftActualAdjacent padding hadjShifted
      have hadjSourceTrue :
          faceLinkAdjacentB base sourceLeft sourceRight = true :=
        faceLinkAdjacentB_true_of_actualAdjacent
          hleftPhysical hrightPhysical hadjSource
      have hadjSourceFalse :
          faceLinkAdjacentB base sourceLeft sourceRight = false :=
        hseparated sourceLeft hsourceLeft sourceRight hsourceRight
      have hbad : false = true := by
        simpa only [hadjSourceFalse] using hadjSourceTrue
      exact False.elim (Bool.false_ne_true hbad)

/-! ## 2. Compatible translated families -/

def uniformShiftFamily (padding base : Nat)
    (family : List (List Nat)) : List (List Nat) :=
  family.map (uniformShiftCanonicalRoot padding base)

def embeddedUniformShiftFamily (padding base : Nat)
    (family : List (List Nat)) : List (List Nat) :=
  ambientOrderedFamily (uniformPaddedBase padding base)
    (uniformShiftFamily padding base family)

theorem mem_embeddedUniformShiftFamily_iff
    {padding base : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base)
    (target : List Nat) :
    target ∈ embeddedUniformShiftFamily padding base family ↔
      ∃ source, source ∈ family ∧
        target = uniformShiftCanonicalRoot padding base source := by
  unfold embeddedUniformShiftFamily
  rw [mem_ambientOrderedFamily_iff]
  constructor
  · intro htarget
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget.2
    exact ⟨source, hsource, heq.symm⟩
  · rintro ⟨source, hsource, rfl⟩
    exact ⟨uniformShiftCanonicalRoot_canonical
        (compatibleAmbientFamily_member_ambient hfamily hsource),
      List.mem_map.mpr ⟨source, hsource, rfl⟩⟩

theorem embeddedUniformShiftFamily_invariants
    {padding base : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    DistinctDisjoint (embeddedUniformShiftFamily padding base family) ∧
      DistinctSeparated (faceLinkAdjacentB (uniformPaddedBase padding base))
        (embeddedUniformShiftFamily padding base family) := by
  have hsource := compatibleAmbientFamily_invariants hfamily
  constructor
  · intro targetLeft htargetLeft targetRight htargetRight hne
    obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
      (mem_embeddedUniformShiftFamily_iff hfamily targetLeft).1 htargetLeft
    obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
      (mem_embeddedUniformShiftFamily_iff hfamily targetRight).1 htargetRight
    have hsourceNe : sourceLeft ≠ sourceRight := by
      intro heq
      subst sourceRight
      exact hne (hleftEq.trans hrightEq.symm)
    rw [hleftEq, hrightEq]
    exact supportsDisjoint_uniformShift
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceLeft)
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceRight)
      (hsource.1 sourceLeft hsourceLeft sourceRight hsourceRight hsourceNe)
  · intro targetLeft htargetLeft targetRight htargetRight hne
    obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
      (mem_embeddedUniformShiftFamily_iff hfamily targetLeft).1 htargetLeft
    obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
      (mem_embeddedUniformShiftFamily_iff hfamily targetRight).1 htargetRight
    have hsourceNe : sourceLeft ≠ sourceRight := by
      intro heq
      subst sourceRight
      exact hne (hleftEq.trans hrightEq.symm)
    rw [hleftEq, hrightEq]
    exact supportsSeparated_uniformShift
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceLeft)
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceRight)
      (hsource.2 sourceLeft hsourceLeft sourceRight hsourceRight hsourceNe)

theorem embeddedUniformShiftFamily_mem_compatible
    {padding base : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    embeddedUniformShiftFamily padding base family ∈
      canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base) := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · unfold embeddedUniformShiftFamily ambientOrderedFamily
    exact filter_mem_sublists _ _
  · exact canonicalFamilyCompatibleB_true (uniformPaddedBase padding base)
      (embeddedUniformShiftFamily padding base family)
      (ambientOrderedFamily_nodup (uniformPaddedBase padding base)
        (uniformShiftFamily padding base family))
      (embeddedUniformShiftFamily_invariants hfamily).1
      (embeddedUniformShiftFamily_invariants hfamily).2

theorem uniformShiftFamily_nodup
    {padding base : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    (uniformShiftFamily padding base family).Nodup := by
  unfold uniformShiftFamily
  apply nodup_map_of_injOn (uniformShiftCanonicalRoot padding base) family
    (compatibleAmbientFamily_nodup hfamily)
  intro left hleft right hright heq
  exact uniformShiftCanonicalRoot_injective_on_canonical
    (compatibleAmbientFamily_member_ambient hfamily hleft)
    (compatibleAmbientFamily_member_ambient hfamily hright) heq

theorem uniformShiftFamily_perm_embedded
    {padding base : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    (uniformShiftFamily padding base family).Perm
      (embeddedUniformShiftFamily padding base family) := by
  apply perm_of_nodup_mem_iff
    (uniformShiftFamily padding base family)
    (embeddedUniformShiftFamily padding base family)
    (uniformShiftFamily_nodup hfamily)
    (ambientOrderedFamily_nodup (uniformPaddedBase padding base)
      (uniformShiftFamily padding base family))
  intro target
  unfold embeddedUniformShiftFamily
  rw [mem_ambientOrderedFamily_iff]
  constructor
  · intro htarget
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget
    rw [← heq]
    exact ⟨uniformShiftCanonicalRoot_canonical
      (compatibleAmbientFamily_member_ambient hfamily hsource),
      List.mem_map.mpr ⟨source, hsource, rfl⟩⟩
  · exact fun htarget => htarget.2

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem couplingParametricKSupportFamilyActivity_uniformShift
    (coupling : Q') (cutoff : Nat) {padding base : Nat} :
    ∀ family : List (List Nat),
      (∀ support, support ∈ family →
        support ∈ cutoffOneFaceSupports base) →
      couplingParametricKSupportFamilyActivity
          coupling cutoff base family ≈
        couplingParametricKSupportFamilyActivity coupling cutoff
          (uniformPaddedBase padding base) (uniformShiftFamily padding base family)
  | [], _ => Q'.eqv_refl 1
  | support :: rest, hmembers => by
      change
        couplingParametricKSupportActivity coupling cutoff base support *
            couplingParametricKSupportFamilyActivity
              coupling cutoff base rest ≈
          couplingParametricKSupportActivity coupling cutoff
              (uniformPaddedBase padding base)
              (uniformShiftCanonicalRoot padding base support) *
            couplingParametricKSupportFamilyActivity coupling cutoff
              (uniformPaddedBase padding base) (uniformShiftFamily padding base rest)
      exact qmul_congr_local
        (couplingParametricKSupportActivity_uniformShift coupling
          (hmembers support List.mem_cons_self))
        (couplingParametricKSupportFamilyActivity_uniformShift
          coupling cutoff rest
          (fun item hitem =>
            hmembers item (List.mem_cons_of_mem support hitem)))

theorem couplingParametricKCompatibleFamilyActivity_embedded_uniformShift
    (coupling : Q') (cutoff : Nat) {padding base : Nat}
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    couplingParametricKSupportFamilyActivity
        coupling cutoff base family ≈
      couplingParametricKSupportFamilyActivity coupling cutoff
        (uniformPaddedBase padding base) (embeddedUniformShiftFamily padding base family) := by
  refine Q'.eqv_trans _ _ _
    (couplingParametricKSupportFamilyActivity_uniformShift
      coupling cutoff (padding := padding) family
      (fun support hsupport =>
        compatibleAmbientFamily_member_faceSupport hfamily hsupport)) ?_
  exact couplingParametricKSupportFamilyActivity_perm
    coupling cutoff (uniformPaddedBase padding base)
    (uniformShiftFamily_perm_embedded hfamily)

/-! ## 3. The translated embedded target cell -/

def uniformShiftEmbeddedCompatibleFamilies (padding base : Nat) :
    List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies base).map
    (embeddedUniformShiftFamily padding base)

theorem uniformShiftEmbeddedCompatibleFamilies_member_target
    {padding base : Nat} {targetFamily : List (List Nat)}
    (htarget : targetFamily ∈
      uniformShiftEmbeddedCompatibleFamilies padding base) :
    targetFamily ∈ canonicalCompatibleAmbientFamilies
      (uniformPaddedBase padding base) := by
  obtain ⟨sourceFamily, hsource, heq⟩ := List.mem_map.mp htarget
  rw [← heq]
  exact embeddedUniformShiftFamily_mem_compatible hsource

theorem embeddedUniformShiftFamily_injective_on_compatible
    {padding base : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies base)
    (hright : right ∈ canonicalCompatibleAmbientFamilies base)
    (heq : embeddedUniformShiftFamily padding base left =
      embeddedUniformShiftFamily padding base right) :
    left = right := by
  apply sublists_eq_of_mem_iff (canonicalSurfacePolymers base) left right
    (canonicalSurfacePolymers_nodup base)
    (compatibleAmbientFamily_sublist hleft)
    (compatibleAmbientFamily_sublist hright)
  intro source
  constructor
  · intro hsource
    have htarget : uniformShiftCanonicalRoot padding base source ∈
        embeddedUniformShiftFamily padding base left :=
      (mem_embeddedUniformShiftFamily_iff hleft
        (uniformShiftCanonicalRoot padding base source)).2
        ⟨source, hsource, rfl⟩
    rw [heq] at htarget
    obtain ⟨other, hother, htransport⟩ :=
      (mem_embeddedUniformShiftFamily_iff hright
        (uniformShiftCanonicalRoot padding base source)).1 htarget
    have hsourceEq : source = other :=
      uniformShiftCanonicalRoot_injective_on_canonical
        (compatibleAmbientFamily_member_ambient hleft hsource)
        (compatibleAmbientFamily_member_ambient hright hother)
        htransport
    rw [hsourceEq]
    exact hother
  · intro hsource
    have htarget : uniformShiftCanonicalRoot padding base source ∈
        embeddedUniformShiftFamily padding base right :=
      (mem_embeddedUniformShiftFamily_iff hright
        (uniformShiftCanonicalRoot padding base source)).2
        ⟨source, hsource, rfl⟩
    rw [← heq] at htarget
    obtain ⟨other, hother, htransport⟩ :=
      (mem_embeddedUniformShiftFamily_iff hleft
        (uniformShiftCanonicalRoot padding base source)).1 htarget
    have hsourceEq : source = other :=
      uniformShiftCanonicalRoot_injective_on_canonical
        (compatibleAmbientFamily_member_ambient hright hsource)
        (compatibleAmbientFamily_member_ambient hleft hother)
        htransport
    rw [hsourceEq]
    exact hother

theorem uniformShiftEmbeddedCompatibleFamilies_nodup
    (padding base : Nat) :
    (uniformShiftEmbeddedCompatibleFamilies padding base).Nodup := by
  unfold uniformShiftEmbeddedCompatibleFamilies
  apply nodup_map_of_injOn (embeddedUniformShiftFamily padding base)
    (canonicalCompatibleAmbientFamilies base)
    (canonicalCompatibleAmbientFamilies_nodup base)
  intro left hleft right hright heq
  exact embeddedUniformShiftFamily_injective_on_compatible
    hleft hright heq

def uniformShiftEmbeddedTargetFamilies (padding base : Nat) :
    List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base)).filter
    (fun family => decide
      (family ∈ uniformShiftEmbeddedCompatibleFamilies padding base))

theorem uniformShiftEmbeddedCompatibleFamilies_perm_target
    (padding base : Nat) :
    (uniformShiftEmbeddedCompatibleFamilies padding base).Perm
      (uniformShiftEmbeddedTargetFamilies padding base) := by
  apply perm_of_nodup_mem_iff
    (uniformShiftEmbeddedCompatibleFamilies padding base)
    (uniformShiftEmbeddedTargetFamilies padding base)
    (uniformShiftEmbeddedCompatibleFamilies_nodup padding base)
  · unfold uniformShiftEmbeddedTargetFamilies
    exact List.filter_sublist.nodup
      (canonicalCompatibleAmbientFamilies_nodup (uniformPaddedBase padding base))
  · intro family
    unfold uniformShiftEmbeddedTargetFamilies
    rw [List.mem_filter]
    simp only [decide_eq_true_eq]
    constructor
    · intro hfamily
      exact ⟨uniformShiftEmbeddedCompatibleFamilies_member_target hfamily,
        hfamily⟩
    · exact fun hfamily => hfamily.2

/-! ## 4. Exact translated finite-cylinder law -/

def uniformShiftedCylinderRoots (padding base : Nat)
    (roots : List (List Nat)) : List (List Nat) :=
  roots.map (uniformShiftCanonicalRoot padding base)

theorem familyContainsPolymerB_embedded_uniformShift
    {padding base : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers base)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    familyContainsPolymerB polymer family =
      familyContainsPolymerB
        (uniformShiftCanonicalRoot padding base polymer)
        (embeddedUniformShiftFamily padding base family) := by
  unfold familyContainsPolymerB
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hsource
    have hmem : polymer ∈ family := of_decide_eq_true hsource
    apply decide_eq_true
    exact (mem_embeddedUniformShiftFamily_iff hfamily
      (uniformShiftCanonicalRoot padding base polymer)).2
      ⟨polymer, hmem, rfl⟩
  · intro htarget
    have hmem : uniformShiftCanonicalRoot padding base polymer ∈
        embeddedUniformShiftFamily padding base family :=
      of_decide_eq_true htarget
    obtain ⟨source, hsource, heq⟩ :=
      (mem_embeddedUniformShiftFamily_iff hfamily
        (uniformShiftCanonicalRoot padding base polymer)).1 hmem
    have hequal : polymer = source :=
      uniformShiftCanonicalRoot_injective_on_canonical
        hpolymer
        (compatibleAmbientFamily_member_ambient hfamily hsource)
        heq
    apply decide_eq_true
    rw [hequal]
    exact hsource

theorem familyOccurrenceFingerprint_embedded_uniformShift
    {padding base : Nat} :
    ∀ {roots : List (List Nat)},
      (∀ root, root ∈ roots →
        root ∈ canonicalSurfacePolymers base) →
      ∀ {family : List (List Nat)},
        family ∈ canonicalCompatibleAmbientFamilies base →
        familyOccurrenceFingerprint roots family =
          familyOccurrenceFingerprint
            (uniformShiftedCylinderRoots padding base roots)
            (embeddedUniformShiftFamily padding base family)
  | [], _, family, hfamily => by rfl
  | root :: roots, hroots, family, hfamily => by
      have hroot : root ∈ canonicalSurfacePolymers base :=
        hroots root List.mem_cons_self
      have htail : ∀ tailRoot, tailRoot ∈ roots →
          tailRoot ∈ canonicalSurfacePolymers base :=
        fun tailRoot htailRoot =>
          hroots tailRoot (List.mem_cons_of_mem root htailRoot)
      simp only [familyOccurrenceFingerprint, uniformShiftedCylinderRoots,
        List.map_cons]
      rw [familyContainsPolymerB_embedded_uniformShift hroot hfamily]
      exact congrArg
        (List.cons
          (familyContainsPolymerB
            (uniformShiftCanonicalRoot padding base root)
            (embeddedUniformShiftFamily padding base family)))
        (familyOccurrenceFingerprint_embedded_uniformShift
          htail hfamily)

def uniformShiftTargetCylinderEvent (padding base : Nat)
    (roots : List (List Nat)) (predicate : List Bool → Bool) :
    List (List Nat) → Bool :=
  cylinderEvent (uniformShiftedCylinderRoots padding base roots) predicate

theorem cylinderEvent_embedded_uniformShift
    {padding base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    sourceCylinderEvent roots predicate family =
      uniformShiftTargetCylinderEvent padding base roots predicate
        (embeddedUniformShiftFamily padding base family) := by
  unfold sourceCylinderEvent uniformShiftTargetCylinderEvent cylinderEvent
  rw [familyOccurrenceFingerprint_embedded_uniformShift hroots hfamily]

def uniformShiftEmbeddedSourceCylinderFamilies (padding base : Nat)
    (roots : List (List Nat)) (predicate : List Bool → Bool) :
    List (List (List Nat)) :=
  ((canonicalCompatibleAmbientFamilies base).filter
      (sourceCylinderEvent roots predicate)).map
    (embeddedUniformShiftFamily padding base)

theorem uniformShiftEmbeddedSourceCylinderFamilies_eq_filter
    {padding base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    uniformShiftEmbeddedSourceCylinderFamilies
        padding base roots predicate =
      (uniformShiftEmbeddedCompatibleFamilies padding base).filter
        (uniformShiftTargetCylinderEvent padding base roots predicate) := by
  unfold uniformShiftEmbeddedSourceCylinderFamilies
    uniformShiftEmbeddedCompatibleFamilies
  rw [List.filter_map]
  apply congrArg (List.map (embeddedUniformShiftFamily padding base))
  apply List.filter_congr
  intro family hfamily
  exact cylinderEvent_embedded_uniformShift hroots predicate hfamily

theorem uniformShiftEmbeddedSourceCylinderFamilies_perm_target
    {padding base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    (uniformShiftEmbeddedSourceCylinderFamilies
        padding base roots predicate).Perm
      ((uniformShiftEmbeddedTargetFamilies padding base).filter
        (uniformShiftTargetCylinderEvent padding base roots predicate)) := by
  rw [uniformShiftEmbeddedSourceCylinderFamilies_eq_filter
    hroots predicate]
  exact (uniformShiftEmbeddedCompatibleFamilies_perm_target
    padding base).filter _

def couplingParametricKUniformShiftEmbeddedTargetPartition
    (coupling : Q') (cutoff padding base : Nat) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base))
    (uniformShiftEmbeddedTargetFamilies padding base)

def couplingParametricKUniformShiftEmbeddedTargetEventNumerator
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base))
    ((uniformShiftEmbeddedTargetFamilies padding base).filter event)

theorem couplingParametricKCompatiblePartition_eqv_embedded_uniformShift
    (coupling : Q') (cutoff padding base : Nat) :
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff base ≈
      couplingParametricKUniformShiftEmbeddedTargetPartition
        coupling cutoff padding base := by
  have hmap :
      couplingParametricKCompatibleSupportGasPartition
          coupling cutoff base ≈
        listQSum
          (couplingParametricKSupportFamilyActivity coupling cutoff
            (uniformPaddedBase padding base))
          (uniformShiftEmbeddedCompatibleFamilies padding base) := by
    unfold couplingParametricKCompatibleSupportGasPartition
      uniformShiftEmbeddedCompatibleFamilies
    apply listQSum_map_eqv
    intro family hfamily
    exact couplingParametricKCompatibleFamilyActivity_embedded_uniformShift
      coupling cutoff hfamily
  refine Q'.eqv_trans _ _ _ hmap ?_
  unfold couplingParametricKUniformShiftEmbeddedTargetPartition
  exact listQSum_perm
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base))
    (uniformShiftEmbeddedCompatibleFamilies_perm_target padding base)

theorem couplingParametricKCompatibleCylinderNumerator_eqv_embedded_uniformShift
    (coupling : Q') (cutoff : Nat) {padding base : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff base
        (sourceCylinderEvent roots predicate) ≈
      couplingParametricKUniformShiftEmbeddedTargetEventNumerator
        coupling cutoff padding base
        (uniformShiftTargetCylinderEvent padding base roots predicate) := by
  have hmap :
      couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff base
          (sourceCylinderEvent roots predicate) ≈
        listQSum
          (couplingParametricKSupportFamilyActivity coupling cutoff
            (uniformPaddedBase padding base))
          (uniformShiftEmbeddedSourceCylinderFamilies
            padding base roots predicate) := by
    unfold couplingParametricKCompatibleSupportEventNumerator
      uniformShiftEmbeddedSourceCylinderFamilies
    apply listQSum_map_eqv
    intro family hfamily
    exact couplingParametricKCompatibleFamilyActivity_embedded_uniformShift
      coupling cutoff (List.mem_filter.mp hfamily).1
  refine Q'.eqv_trans _ _ _ hmap ?_
  unfold couplingParametricKUniformShiftEmbeddedTargetEventNumerator
  exact listQSum_perm
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base))
    (uniformShiftEmbeddedSourceCylinderFamilies_perm_target
      hroots predicate)

theorem couplingParametricKUniformShiftEmbeddedTargetPartition_pos
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff padding base : Nat) :
    (0 : Q') < couplingParametricKUniformShiftEmbeddedTargetPartition
      coupling cutoff padding base :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff base)
    (Q'.le_of_eqv
      (couplingParametricKCompatiblePartition_eqv_embedded_uniformShift
        coupling cutoff padding base))

def couplingParametricKUniformShiftEmbeddedTargetEventProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (couplingParametricKUniformShiftEmbeddedTargetEventNumerator
      coupling cutoff padding base event)
    (couplingParametricKUniformShiftEmbeddedTargetPartition
      coupling cutoff padding base)
    (couplingParametricKUniformShiftEmbeddedTargetPartition_pos
      hcoupling cutoff padding base)

theorem couplingParametricKCompatibleCylinderProbability_eqv_embedded_uniformShift
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {padding base : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff base
        (sourceCylinderEvent roots predicate) ≈
      couplingParametricKUniformShiftEmbeddedTargetEventProbability
        coupling hcoupling cutoff padding base
        (uniformShiftTargetCylinderEvent padding base roots predicate) := by
  unfold couplingParametricKCompatibleSupportEventProbability
    couplingParametricKUniformShiftEmbeddedTargetEventProbability
  exact divPos_eqv_congr
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff base)
    (couplingParametricKUniformShiftEmbeddedTargetPartition_pos
      hcoupling cutoff padding base)
    (couplingParametricKCompatibleCylinderNumerator_eqv_embedded_uniformShift
      coupling cutoff hroots predicate)
    (couplingParametricKCompatiblePartition_eqv_embedded_uniformShift
      coupling cutoff padding base)

#print axioms uniformShiftRootMemberSource
#print axioms unshiftActualAdjacent
#print axioms supportsDisjoint_uniformShift
#print axioms supportsSeparated_uniformShift
#print axioms embeddedUniformShiftFamily_mem_compatible
#print axioms uniformShiftFamily_perm_embedded
#print axioms couplingParametricKSupportFamilyActivity_uniformShift
#print axioms couplingParametricKCompatibleFamilyActivity_embedded_uniformShift
#print axioms embeddedUniformShiftFamily_injective_on_compatible
#print axioms uniformShiftEmbeddedCompatibleFamilies_perm_target
#print axioms familyOccurrenceFingerprint_embedded_uniformShift
#print axioms cylinderEvent_embedded_uniformShift
#print axioms couplingParametricKCompatiblePartition_eqv_embedded_uniformShift
#print axioms couplingParametricKCompatibleCylinderNumerator_eqv_embedded_uniformShift
#print axioms couplingParametricKCompatibleCylinderProbability_eqv_embedded_uniformShift

end YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
