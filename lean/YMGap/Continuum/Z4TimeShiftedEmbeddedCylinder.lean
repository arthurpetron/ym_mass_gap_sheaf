/-
# Exact embedded finite-cylinder law for an affine time shift

Every compatible source family is translated geometrically, re-ordered in
the target canonical polymer order, and proved to be a genuine compatible
target family.  Complete family activities and all finite Boolean cylinder
events are preserved.  Thus the source normalized law is exactly the law on
the translated embedded target cell.  The remaining thermodynamic step is
to compare this embedded cell with the full target gas using the shifted
connected-carrier tail.
-/

import YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
import YMGap.Continuum.Z4TimeShiftedSupportActivity

namespace YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder

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
open YMGap.Continuum.Z4TimeShiftedPhysicalWeights
open YMGap.Continuum.Z4TimeShiftedSupportActivity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Member recovery and translated adjacency -/

def timeShiftRootMemberSource
    {shift base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base)
    {targetFace : Nat}
    (htarget : targetFace ∈ timeShiftCanonicalRoot shift base support) :
    Σ' sourceFace : Nat,
      (sourceFace ∈ support) ×'
        (timeShiftPlaquette shift (boxPlaquetteAt base sourceFace) =
          boxPlaquetteAt (base + shift) targetFace) := by
  have htargetGeom : boxPlaquetteAt (base + shift) targetFace ∈
      geometricPolymer (base + shift)
        (timeShiftCanonicalRoot shift base support) :=
    List.mem_map.mpr ⟨targetFace, htarget, rfl⟩
  have hmapped := (timeShiftFaceSupport_sameSupport hsupport).1
    _ htargetGeom
  obtain ⟨sourcePlaquette, hsourcePlaquette, heq⟩ :=
    decodeMapMember (timeShiftPlaquette shift)
      (geometricPolymer base support)
      (boxPlaquetteAt (base + shift) targetFace) hmapped
  obtain ⟨sourceFace, hsourceFace, hsourceEq⟩ :=
    decodeMapMember (boxPlaquetteAt base) support
      sourcePlaquette hsourcePlaquette
  subst sourcePlaquette
  exact ⟨sourceFace, hsourceFace, heq⟩

def timeShiftRootMemberTarget
    {shift base : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports base)
    {sourceFace : Nat} (hsource : sourceFace ∈ support) :
    Σ' targetFace : Nat,
      (targetFace ∈ timeShiftCanonicalRoot shift base support) ×'
        (timeShiftPlaquette shift (boxPlaquetteAt base sourceFace) =
          boxPlaquetteAt (base + shift) targetFace) := by
  have hsourceGeom : boxPlaquetteAt base sourceFace ∈
      geometricPolymer base support :=
    List.mem_map.mpr ⟨sourceFace, hsource, rfl⟩
  have hmapped : timeShiftPlaquette shift
      (boxPlaquetteAt base sourceFace) ∈
      (geometricPolymer base support).map
        (timeShiftPlaquette shift) :=
    List.mem_map.mpr ⟨boxPlaquetteAt base sourceFace,
      hsourceGeom, rfl⟩
  have htargetGeom :=
    (timeShiftFaceSupport_sameSupport hsupport).2 _ hmapped
  obtain ⟨targetFace, htargetFace, heq⟩ :=
    decodeMapMember (boxPlaquetteAt (base + shift))
      (timeShiftCanonicalRoot shift base support)
      (timeShiftPlaquette shift (boxPlaquetteAt base sourceFace))
      htargetGeom
  exact ⟨targetFace, htargetFace, heq.symm⟩

def unshiftActualAdjacent
    (shift : Nat) {left right : Z4Plaq}
    (hadj : z4Chain.toLattice.Adjacent
      (timeShiftPlaquette shift left)
      (timeShiftPlaquette shift right)) :
    z4Chain.toLattice.Adjacent left right := by
  have hleftEdge : hadj.link ∈
      edgesOf (timeShiftPlaquette shift left) := by
    have hon := hadj.on_p
    change z4Boundary (timeShiftPlaquette shift left) hadj.link = true at hon
    exact of_decide_eq_true hon
  have hrightEdge : hadj.link ∈
      edgesOf (timeShiftPlaquette shift right) := by
    have hon := hadj.on_q
    change z4Boundary (timeShiftPlaquette shift right) hadj.link = true at hon
    exact of_decide_eq_true hon
  rw [edgesOf_timeShiftPlaquette] at hleftEdge hrightEdge
  obtain ⟨leftLink, hleftLink, hleftEq⟩ :=
    decodeMapMember (timeShiftLink shift) (edgesOf left)
      hadj.link hleftEdge
  obtain ⟨rightLink, hrightLink, hrightEq⟩ :=
    decodeMapMember (timeShiftLink shift) (edgesOf right)
      hadj.link hrightEdge
  have hlinkEq : leftLink = rightLink :=
    timeShiftLink_injective shift (hleftEq.trans hrightEq.symm)
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

theorem supportsDisjoint_timeShift
    {shift base : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports base)
    (hright : right ∈ cutoffOneFaceSupports base)
    (hdisjoint : SupportsDisjoint left right) :
    SupportsDisjoint
      (timeShiftCanonicalRoot shift base left)
      (timeShiftCanonicalRoot shift base right) := by
  intro targetFace htargetLeft htargetRight
  obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
    timeShiftRootMemberSource hleft htargetLeft
  obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
    timeShiftRootMemberSource hright htargetRight
  have hsourcePlaqEq : boxPlaquetteAt base sourceLeft =
      boxPlaquetteAt base sourceRight :=
    timeShiftPlaquette_injective shift
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

theorem supportsSeparated_timeShift
    {shift base : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports base)
    (hright : right ∈ cutoffOneFaceSupports base)
    (hseparated : SupportsSeparated (faceLinkAdjacentB base) left right) :
    SupportsSeparated (faceLinkAdjacentB (base + shift))
      (timeShiftCanonicalRoot shift base left)
      (timeShiftCanonicalRoot shift base right) := by
  intro targetLeft htargetLeft targetRight htargetRight
  cases hadjTarget : faceLinkAdjacentB (base + shift)
      targetLeft targetRight with
  | false => rfl
  | true =>
      obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
        timeShiftRootMemberSource hleft htargetLeft
      obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
        timeShiftRootMemberSource hright htargetRight
      have hleftPhysical : sourceLeft ∈ physicalFaceEdges base :=
        mem_of_mem_sublists (physicalFaceEdges base) left hleft
          sourceLeft hsourceLeft
      have hrightPhysical : sourceRight ∈ physicalFaceEdges base :=
        mem_of_mem_sublists (physicalFaceEdges base) right hright
          sourceRight hsourceRight
      have hadjTargetActual := actualAdjacentOfFaceLinkAdjacent hadjTarget
      have hadjShifted : z4Chain.toLattice.Adjacent
          (timeShiftPlaquette shift (boxPlaquetteAt base sourceLeft))
          (timeShiftPlaquette shift (boxPlaquetteAt base sourceRight)) := by
        simpa only [hleftEq, hrightEq] using hadjTargetActual
      have hadjSource := unshiftActualAdjacent shift hadjShifted
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

def timeShiftFamily (shift base : Nat)
    (family : List (List Nat)) : List (List Nat) :=
  family.map (timeShiftCanonicalRoot shift base)

def embeddedTimeShiftFamily (shift base : Nat)
    (family : List (List Nat)) : List (List Nat) :=
  ambientOrderedFamily (base + shift)
    (timeShiftFamily shift base family)

theorem mem_embeddedTimeShiftFamily_iff
    {shift base : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base)
    (target : List Nat) :
    target ∈ embeddedTimeShiftFamily shift base family ↔
      ∃ source, source ∈ family ∧
        target = timeShiftCanonicalRoot shift base source := by
  unfold embeddedTimeShiftFamily
  rw [mem_ambientOrderedFamily_iff]
  constructor
  · intro htarget
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget.2
    exact ⟨source, hsource, heq.symm⟩
  · rintro ⟨source, hsource, rfl⟩
    exact ⟨timeShiftCanonicalRoot_canonical
        (compatibleAmbientFamily_member_ambient hfamily hsource),
      List.mem_map.mpr ⟨source, hsource, rfl⟩⟩

theorem embeddedTimeShiftFamily_invariants
    {shift base : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    DistinctDisjoint (embeddedTimeShiftFamily shift base family) ∧
      DistinctSeparated (faceLinkAdjacentB (base + shift))
        (embeddedTimeShiftFamily shift base family) := by
  have hsource := compatibleAmbientFamily_invariants hfamily
  constructor
  · intro targetLeft htargetLeft targetRight htargetRight hne
    obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
      (mem_embeddedTimeShiftFamily_iff hfamily targetLeft).1 htargetLeft
    obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
      (mem_embeddedTimeShiftFamily_iff hfamily targetRight).1 htargetRight
    have hsourceNe : sourceLeft ≠ sourceRight := by
      intro heq
      subst sourceRight
      exact hne (hleftEq.trans hrightEq.symm)
    rw [hleftEq, hrightEq]
    exact supportsDisjoint_timeShift
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceLeft)
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceRight)
      (hsource.1 sourceLeft hsourceLeft sourceRight hsourceRight hsourceNe)
  · intro targetLeft htargetLeft targetRight htargetRight hne
    obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
      (mem_embeddedTimeShiftFamily_iff hfamily targetLeft).1 htargetLeft
    obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
      (mem_embeddedTimeShiftFamily_iff hfamily targetRight).1 htargetRight
    have hsourceNe : sourceLeft ≠ sourceRight := by
      intro heq
      subst sourceRight
      exact hne (hleftEq.trans hrightEq.symm)
    rw [hleftEq, hrightEq]
    exact supportsSeparated_timeShift
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceLeft)
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceRight)
      (hsource.2 sourceLeft hsourceLeft sourceRight hsourceRight hsourceNe)

theorem embeddedTimeShiftFamily_mem_compatible
    {shift base : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    embeddedTimeShiftFamily shift base family ∈
      canonicalCompatibleAmbientFamilies (base + shift) := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · unfold embeddedTimeShiftFamily ambientOrderedFamily
    exact filter_mem_sublists _ _
  · exact canonicalFamilyCompatibleB_true (base + shift)
      (embeddedTimeShiftFamily shift base family)
      (ambientOrderedFamily_nodup (base + shift)
        (timeShiftFamily shift base family))
      (embeddedTimeShiftFamily_invariants hfamily).1
      (embeddedTimeShiftFamily_invariants hfamily).2

theorem timeShiftFamily_nodup
    {shift base : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    (timeShiftFamily shift base family).Nodup := by
  unfold timeShiftFamily
  apply nodup_map_of_injOn (timeShiftCanonicalRoot shift base) family
    (compatibleAmbientFamily_nodup hfamily)
  intro left hleft right hright heq
  exact timeShiftCanonicalRoot_injective_on_canonical
    (compatibleAmbientFamily_member_ambient hfamily hleft)
    (compatibleAmbientFamily_member_ambient hfamily hright) heq

theorem timeShiftFamily_perm_embedded
    {shift base : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    (timeShiftFamily shift base family).Perm
      (embeddedTimeShiftFamily shift base family) := by
  apply perm_of_nodup_mem_iff
    (timeShiftFamily shift base family)
    (embeddedTimeShiftFamily shift base family)
    (timeShiftFamily_nodup hfamily)
    (ambientOrderedFamily_nodup (base + shift)
      (timeShiftFamily shift base family))
  intro target
  unfold embeddedTimeShiftFamily
  rw [mem_ambientOrderedFamily_iff]
  constructor
  · intro htarget
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget
    rw [← heq]
    exact ⟨timeShiftCanonicalRoot_canonical
      (compatibleAmbientFamily_member_ambient hfamily hsource),
      List.mem_map.mpr ⟨source, hsource, rfl⟩⟩
  · exact fun htarget => htarget.2

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem couplingParametricKSupportFamilyActivity_timeShift
    (coupling : Q') (cutoff : Nat) {shift base : Nat} :
    ∀ family : List (List Nat),
      (∀ support, support ∈ family →
        support ∈ cutoffOneFaceSupports base) →
      couplingParametricKSupportFamilyActivity
          coupling cutoff base family ≈
        couplingParametricKSupportFamilyActivity coupling cutoff
          (base + shift) (timeShiftFamily shift base family)
  | [], _ => Q'.eqv_refl 1
  | support :: rest, hmembers => by
      change
        couplingParametricKSupportActivity coupling cutoff base support *
            couplingParametricKSupportFamilyActivity
              coupling cutoff base rest ≈
          couplingParametricKSupportActivity coupling cutoff
              (base + shift)
              (timeShiftCanonicalRoot shift base support) *
            couplingParametricKSupportFamilyActivity coupling cutoff
              (base + shift) (timeShiftFamily shift base rest)
      exact qmul_congr_local
        (couplingParametricKSupportActivity_timeShift coupling
          (hmembers support List.mem_cons_self))
        (couplingParametricKSupportFamilyActivity_timeShift
          coupling cutoff rest
          (fun item hitem =>
            hmembers item (List.mem_cons_of_mem support hitem)))

theorem couplingParametricKCompatibleFamilyActivity_embedded_timeShift
    (coupling : Q') (cutoff : Nat) {shift base : Nat}
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    couplingParametricKSupportFamilyActivity
        coupling cutoff base family ≈
      couplingParametricKSupportFamilyActivity coupling cutoff
        (base + shift) (embeddedTimeShiftFamily shift base family) := by
  refine Q'.eqv_trans _ _ _
    (couplingParametricKSupportFamilyActivity_timeShift
      coupling cutoff (shift := shift) family
      (fun support hsupport =>
        compatibleAmbientFamily_member_faceSupport hfamily hsupport)) ?_
  exact couplingParametricKSupportFamilyActivity_perm
    coupling cutoff (base + shift)
    (timeShiftFamily_perm_embedded hfamily)

/-! ## 3. The translated embedded target cell -/

def timeShiftEmbeddedCompatibleFamilies (shift base : Nat) :
    List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies base).map
    (embeddedTimeShiftFamily shift base)

theorem timeShiftEmbeddedCompatibleFamilies_member_target
    {shift base : Nat} {targetFamily : List (List Nat)}
    (htarget : targetFamily ∈
      timeShiftEmbeddedCompatibleFamilies shift base) :
    targetFamily ∈ canonicalCompatibleAmbientFamilies
      (base + shift) := by
  obtain ⟨sourceFamily, hsource, heq⟩ := List.mem_map.mp htarget
  rw [← heq]
  exact embeddedTimeShiftFamily_mem_compatible hsource

theorem embeddedTimeShiftFamily_injective_on_compatible
    {shift base : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies base)
    (hright : right ∈ canonicalCompatibleAmbientFamilies base)
    (heq : embeddedTimeShiftFamily shift base left =
      embeddedTimeShiftFamily shift base right) :
    left = right := by
  apply sublists_eq_of_mem_iff (canonicalSurfacePolymers base) left right
    (canonicalSurfacePolymers_nodup base)
    (compatibleAmbientFamily_sublist hleft)
    (compatibleAmbientFamily_sublist hright)
  intro source
  constructor
  · intro hsource
    have htarget : timeShiftCanonicalRoot shift base source ∈
        embeddedTimeShiftFamily shift base left :=
      (mem_embeddedTimeShiftFamily_iff hleft
        (timeShiftCanonicalRoot shift base source)).2
        ⟨source, hsource, rfl⟩
    rw [heq] at htarget
    obtain ⟨other, hother, htransport⟩ :=
      (mem_embeddedTimeShiftFamily_iff hright
        (timeShiftCanonicalRoot shift base source)).1 htarget
    have hsourceEq : source = other :=
      timeShiftCanonicalRoot_injective_on_canonical
        (compatibleAmbientFamily_member_ambient hleft hsource)
        (compatibleAmbientFamily_member_ambient hright hother)
        htransport
    rw [hsourceEq]
    exact hother
  · intro hsource
    have htarget : timeShiftCanonicalRoot shift base source ∈
        embeddedTimeShiftFamily shift base right :=
      (mem_embeddedTimeShiftFamily_iff hright
        (timeShiftCanonicalRoot shift base source)).2
        ⟨source, hsource, rfl⟩
    rw [← heq] at htarget
    obtain ⟨other, hother, htransport⟩ :=
      (mem_embeddedTimeShiftFamily_iff hleft
        (timeShiftCanonicalRoot shift base source)).1 htarget
    have hsourceEq : source = other :=
      timeShiftCanonicalRoot_injective_on_canonical
        (compatibleAmbientFamily_member_ambient hright hsource)
        (compatibleAmbientFamily_member_ambient hleft hother)
        htransport
    rw [hsourceEq]
    exact hother

theorem timeShiftEmbeddedCompatibleFamilies_nodup
    (shift base : Nat) :
    (timeShiftEmbeddedCompatibleFamilies shift base).Nodup := by
  unfold timeShiftEmbeddedCompatibleFamilies
  apply nodup_map_of_injOn (embeddedTimeShiftFamily shift base)
    (canonicalCompatibleAmbientFamilies base)
    (canonicalCompatibleAmbientFamilies_nodup base)
  intro left hleft right hright heq
  exact embeddedTimeShiftFamily_injective_on_compatible
    hleft hright heq

def timeShiftEmbeddedTargetFamilies (shift base : Nat) :
    List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies (base + shift)).filter
    (fun family => decide
      (family ∈ timeShiftEmbeddedCompatibleFamilies shift base))

theorem timeShiftEmbeddedCompatibleFamilies_perm_target
    (shift base : Nat) :
    (timeShiftEmbeddedCompatibleFamilies shift base).Perm
      (timeShiftEmbeddedTargetFamilies shift base) := by
  apply perm_of_nodup_mem_iff
    (timeShiftEmbeddedCompatibleFamilies shift base)
    (timeShiftEmbeddedTargetFamilies shift base)
    (timeShiftEmbeddedCompatibleFamilies_nodup shift base)
  · unfold timeShiftEmbeddedTargetFamilies
    exact List.filter_sublist.nodup
      (canonicalCompatibleAmbientFamilies_nodup (base + shift))
  · intro family
    unfold timeShiftEmbeddedTargetFamilies
    rw [List.mem_filter]
    simp only [decide_eq_true_eq]
    constructor
    · intro hfamily
      exact ⟨timeShiftEmbeddedCompatibleFamilies_member_target hfamily,
        hfamily⟩
    · exact fun hfamily => hfamily.2

/-! ## 4. Exact translated finite-cylinder law -/

def timeShiftedCylinderRoots (shift base : Nat)
    (roots : List (List Nat)) : List (List Nat) :=
  roots.map (timeShiftCanonicalRoot shift base)

theorem familyContainsPolymerB_embedded_timeShift
    {shift base : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers base)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    familyContainsPolymerB polymer family =
      familyContainsPolymerB
        (timeShiftCanonicalRoot shift base polymer)
        (embeddedTimeShiftFamily shift base family) := by
  unfold familyContainsPolymerB
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hsource
    have hmem : polymer ∈ family := of_decide_eq_true hsource
    apply decide_eq_true
    exact (mem_embeddedTimeShiftFamily_iff hfamily
      (timeShiftCanonicalRoot shift base polymer)).2
      ⟨polymer, hmem, rfl⟩
  · intro htarget
    have hmem : timeShiftCanonicalRoot shift base polymer ∈
        embeddedTimeShiftFamily shift base family :=
      of_decide_eq_true htarget
    obtain ⟨source, hsource, heq⟩ :=
      (mem_embeddedTimeShiftFamily_iff hfamily
        (timeShiftCanonicalRoot shift base polymer)).1 hmem
    have hequal : polymer = source :=
      timeShiftCanonicalRoot_injective_on_canonical
        hpolymer
        (compatibleAmbientFamily_member_ambient hfamily hsource)
        heq
    apply decide_eq_true
    rw [hequal]
    exact hsource

theorem familyOccurrenceFingerprint_embedded_timeShift
    {shift base : Nat} :
    ∀ {roots : List (List Nat)},
      (∀ root, root ∈ roots →
        root ∈ canonicalSurfacePolymers base) →
      ∀ {family : List (List Nat)},
        family ∈ canonicalCompatibleAmbientFamilies base →
        familyOccurrenceFingerprint roots family =
          familyOccurrenceFingerprint
            (timeShiftedCylinderRoots shift base roots)
            (embeddedTimeShiftFamily shift base family)
  | [], _, family, hfamily => by rfl
  | root :: roots, hroots, family, hfamily => by
      have hroot : root ∈ canonicalSurfacePolymers base :=
        hroots root List.mem_cons_self
      have htail : ∀ tailRoot, tailRoot ∈ roots →
          tailRoot ∈ canonicalSurfacePolymers base :=
        fun tailRoot htailRoot =>
          hroots tailRoot (List.mem_cons_of_mem root htailRoot)
      simp only [familyOccurrenceFingerprint, timeShiftedCylinderRoots,
        List.map_cons]
      rw [familyContainsPolymerB_embedded_timeShift hroot hfamily]
      exact congrArg
        (List.cons
          (familyContainsPolymerB
            (timeShiftCanonicalRoot shift base root)
            (embeddedTimeShiftFamily shift base family)))
        (familyOccurrenceFingerprint_embedded_timeShift
          htail hfamily)

def timeShiftTargetCylinderEvent (shift base : Nat)
    (roots : List (List Nat)) (predicate : List Bool → Bool) :
    List (List Nat) → Bool :=
  cylinderEvent (timeShiftedCylinderRoots shift base roots) predicate

theorem cylinderEvent_embedded_timeShift
    {shift base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies base) :
    sourceCylinderEvent roots predicate family =
      timeShiftTargetCylinderEvent shift base roots predicate
        (embeddedTimeShiftFamily shift base family) := by
  unfold sourceCylinderEvent timeShiftTargetCylinderEvent cylinderEvent
  rw [familyOccurrenceFingerprint_embedded_timeShift hroots hfamily]

def timeShiftEmbeddedSourceCylinderFamilies (shift base : Nat)
    (roots : List (List Nat)) (predicate : List Bool → Bool) :
    List (List (List Nat)) :=
  ((canonicalCompatibleAmbientFamilies base).filter
      (sourceCylinderEvent roots predicate)).map
    (embeddedTimeShiftFamily shift base)

theorem timeShiftEmbeddedSourceCylinderFamilies_eq_filter
    {shift base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    timeShiftEmbeddedSourceCylinderFamilies
        shift base roots predicate =
      (timeShiftEmbeddedCompatibleFamilies shift base).filter
        (timeShiftTargetCylinderEvent shift base roots predicate) := by
  unfold timeShiftEmbeddedSourceCylinderFamilies
    timeShiftEmbeddedCompatibleFamilies
  rw [List.filter_map]
  apply congrArg (List.map (embeddedTimeShiftFamily shift base))
  apply List.filter_congr
  intro family hfamily
  exact cylinderEvent_embedded_timeShift hroots predicate hfamily

theorem timeShiftEmbeddedSourceCylinderFamilies_perm_target
    {shift base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    (timeShiftEmbeddedSourceCylinderFamilies
        shift base roots predicate).Perm
      ((timeShiftEmbeddedTargetFamilies shift base).filter
        (timeShiftTargetCylinderEvent shift base roots predicate)) := by
  rw [timeShiftEmbeddedSourceCylinderFamilies_eq_filter
    hroots predicate]
  exact (timeShiftEmbeddedCompatibleFamilies_perm_target
    shift base).filter _

def couplingParametricKTimeShiftEmbeddedTargetPartition
    (coupling : Q') (cutoff shift base : Nat) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift))
    (timeShiftEmbeddedTargetFamilies shift base)

def couplingParametricKTimeShiftEmbeddedTargetEventNumerator
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift))
    ((timeShiftEmbeddedTargetFamilies shift base).filter event)

theorem couplingParametricKCompatiblePartition_eqv_embedded_timeShift
    (coupling : Q') (cutoff shift base : Nat) :
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff base ≈
      couplingParametricKTimeShiftEmbeddedTargetPartition
        coupling cutoff shift base := by
  have hmap :
      couplingParametricKCompatibleSupportGasPartition
          coupling cutoff base ≈
        listQSum
          (couplingParametricKSupportFamilyActivity coupling cutoff
            (base + shift))
          (timeShiftEmbeddedCompatibleFamilies shift base) := by
    unfold couplingParametricKCompatibleSupportGasPartition
      timeShiftEmbeddedCompatibleFamilies
    apply listQSum_map_eqv
    intro family hfamily
    exact couplingParametricKCompatibleFamilyActivity_embedded_timeShift
      coupling cutoff hfamily
  refine Q'.eqv_trans _ _ _ hmap ?_
  unfold couplingParametricKTimeShiftEmbeddedTargetPartition
  exact listQSum_perm
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift))
    (timeShiftEmbeddedCompatibleFamilies_perm_target shift base)

theorem couplingParametricKCompatibleCylinderNumerator_eqv_embedded_timeShift
    (coupling : Q') (cutoff : Nat) {shift base : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff base
        (sourceCylinderEvent roots predicate) ≈
      couplingParametricKTimeShiftEmbeddedTargetEventNumerator
        coupling cutoff shift base
        (timeShiftTargetCylinderEvent shift base roots predicate) := by
  have hmap :
      couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff base
          (sourceCylinderEvent roots predicate) ≈
        listQSum
          (couplingParametricKSupportFamilyActivity coupling cutoff
            (base + shift))
          (timeShiftEmbeddedSourceCylinderFamilies
            shift base roots predicate) := by
    unfold couplingParametricKCompatibleSupportEventNumerator
      timeShiftEmbeddedSourceCylinderFamilies
    apply listQSum_map_eqv
    intro family hfamily
    exact couplingParametricKCompatibleFamilyActivity_embedded_timeShift
      coupling cutoff (List.mem_filter.mp hfamily).1
  refine Q'.eqv_trans _ _ _ hmap ?_
  unfold couplingParametricKTimeShiftEmbeddedTargetEventNumerator
  exact listQSum_perm
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift))
    (timeShiftEmbeddedSourceCylinderFamilies_perm_target
      hroots predicate)

theorem couplingParametricKTimeShiftEmbeddedTargetPartition_pos
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat) :
    (0 : Q') < couplingParametricKTimeShiftEmbeddedTargetPartition
      coupling cutoff shift base :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff base)
    (Q'.le_of_eqv
      (couplingParametricKCompatiblePartition_eqv_embedded_timeShift
        coupling cutoff shift base))

def couplingParametricKTimeShiftEmbeddedTargetEventProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (couplingParametricKTimeShiftEmbeddedTargetEventNumerator
      coupling cutoff shift base event)
    (couplingParametricKTimeShiftEmbeddedTargetPartition
      coupling cutoff shift base)
    (couplingParametricKTimeShiftEmbeddedTargetPartition_pos
      hcoupling cutoff shift base)

theorem couplingParametricKCompatibleCylinderProbability_eqv_embedded_timeShift
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {shift base : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff base
        (sourceCylinderEvent roots predicate) ≈
      couplingParametricKTimeShiftEmbeddedTargetEventProbability
        coupling hcoupling cutoff shift base
        (timeShiftTargetCylinderEvent shift base roots predicate) := by
  unfold couplingParametricKCompatibleSupportEventProbability
    couplingParametricKTimeShiftEmbeddedTargetEventProbability
  exact divPos_eqv_congr
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff base)
    (couplingParametricKTimeShiftEmbeddedTargetPartition_pos
      hcoupling cutoff shift base)
    (couplingParametricKCompatibleCylinderNumerator_eqv_embedded_timeShift
      coupling cutoff hroots predicate)
    (couplingParametricKCompatiblePartition_eqv_embedded_timeShift
      coupling cutoff shift base)

#print axioms timeShiftRootMemberSource
#print axioms unshiftActualAdjacent
#print axioms supportsDisjoint_timeShift
#print axioms supportsSeparated_timeShift
#print axioms embeddedTimeShiftFamily_mem_compatible
#print axioms timeShiftFamily_perm_embedded
#print axioms couplingParametricKSupportFamilyActivity_timeShift
#print axioms couplingParametricKCompatibleFamilyActivity_embedded_timeShift
#print axioms embeddedTimeShiftFamily_injective_on_compatible
#print axioms timeShiftEmbeddedCompatibleFamilies_perm_target
#print axioms familyOccurrenceFingerprint_embedded_timeShift
#print axioms cylinderEvent_embedded_timeShift
#print axioms couplingParametricKCompatiblePartition_eqv_embedded_timeShift
#print axioms couplingParametricKCompatibleCylinderNumerator_eqv_embedded_timeShift
#print axioms couplingParametricKCompatibleCylinderProbability_eqv_embedded_timeShift

end YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
