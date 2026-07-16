/-
# Nonnegative Euclidean-time translation of finite cylinder presentations

The corner-anchored finite boxes use natural coordinates, so they do not
carry a literal action of all of `Z^4`.  This module constructs the honest
semigroup that is available without subtraction: translate every plaquette
by a nonnegative amount in the fourth coordinate and re-encode the resulting
support in the enlarged box.

Canonical connected polymers remain canonical, re-encoding recovers exactly
the translated geometric support, and zero/composition hold exactly after
canonical re-encoding.  The construction is lifted coordinatewise to finite
cylinder charts and presentations.

This is the geometric/presentation action only.  It does not assert that the
common-refinement relation is translation invariant, nor that the colimit
state is translation invariant; those require separate finite-law boundary
control.
-/

import YMGap.Continuum.Z4FiniteCylinderPresentationColimit
import YMGap.Continuum.Z4HalfTimeReflectionGeometry

namespace YMGap.Continuum.Z4FiniteCylinderTimeTranslation

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteCylinderPresentationColimit
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4PhysicalSurfaceComponents

/-! ## 1. Translation geometry -/

theorem timeShiftVertex_injective (shift : Nat) :
    Function.Injective (timeShiftVertex shift) := by
  intro left right heq
  obtain ⟨a, b, c, d⟩ := left
  obtain ⟨a', b', c', d'⟩ := right
  simp only [timeShiftVertex, Prod.mk.injEq] at heq ⊢
  exact ⟨heq.1, heq.2.1, heq.2.2.1,
    Nat.add_right_cancel heq.2.2.2⟩

theorem timeShiftPlaquette_injective (shift : Nat) :
    Function.Injective (timeShiftPlaquette shift) := by
  intro left right heq
  apply Prod.ext
  · apply timeShiftVertex_injective shift
    simpa only [timeShiftPlaquette] using congrArg Prod.fst heq
  · simpa only [timeShiftPlaquette] using congrArg Prod.snd heq

theorem timeShiftPlaquette_add
    (first second : Nat) (plaquette : Z4Plaq) :
    timeShiftPlaquette second (timeShiftPlaquette first plaquette) =
      timeShiftPlaquette (first + second) plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp [timeShiftPlaquette, timeShiftVertex, Nat.add_assoc]

private theorem map_timeShiftPlaquette_zero_local :
    ∀ support : List Z4Plaq,
      support.map (timeShiftPlaquette 0) = support
  | [] => rfl
  | plaquette :: rest => by
      simp only [List.map_cons]
      rw [map_timeShiftPlaquette_zero_local rest]
      apply congrArg (fun head => head :: rest)
      obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
      simp [timeShiftPlaquette, timeShiftVertex]

theorem timeShiftPlaquette_mem_box_add
    {base shift : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    timeShiftPlaquette shift plaquette ∈ boxPlaquettes (base + shift) := by
  rw [mem_boxPlaquettes] at hplaquette ⊢
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp only [timeShiftPlaquette, timeShiftVertex] at *
  exact ⟨Nat.lt_of_lt_of_le hplaquette.1 (Nat.le_add_right base shift),
    Nat.lt_of_lt_of_le hplaquette.2.1 (Nat.le_add_right base shift),
    Nat.lt_of_lt_of_le hplaquette.2.2.1 (Nat.le_add_right base shift),
    Nat.add_lt_add_right hplaquette.2.2.2 shift⟩

private theorem sameSupport_map_local
    {X Y : List Z4Plaq} (mapP : Z4Plaq → Z4Plaq)
    (h : sameSupport (L := z4Chain.toLattice) X Y) :
    sameSupport (L := z4Chain.toLattice) (X.map mapP) (Y.map mapP) := by
  constructor
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr ⟨source, h.1 source hsource, rfl⟩
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr ⟨source, h.2 source hsource, rfl⟩

private theorem sameSupport_of_map_injective_local
    {X Y : List Z4Plaq} {mapP : Z4Plaq → Z4Plaq}
    (hinjective : Function.Injective mapP)
    (h : sameSupport (L := z4Chain.toLattice) (X.map mapP) (Y.map mapP)) :
    sameSupport (L := z4Chain.toLattice) X Y := by
  constructor
  · intro plaquette hplaquette
    have hmapped : mapP plaquette ∈ X.map mapP :=
      List.mem_map.mpr ⟨plaquette, hplaquette, rfl⟩
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp (h.1 _ hmapped)
    have hsourceEq : source = plaquette := hinjective heq
    simpa only [hsourceEq] using hsource
  · intro plaquette hplaquette
    have hmapped : mapP plaquette ∈ Y.map mapP :=
      List.mem_map.mpr ⟨plaquette, hplaquette, rfl⟩
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp (h.2 _ hmapped)
    have hsourceEq : source = plaquette := hinjective heq
    simpa only [hsourceEq] using hsource

private theorem sameSupport_right_congr_local
    {X Y Z : List Z4Plaq}
    (h : sameSupport (L := z4Chain.toLattice) X Y)
    (heq : Y = Z) :
    sameSupport (L := z4Chain.toLattice) X Z := by
  cases heq
  exact h

def timeShiftConnected (shift : Nat) {support : List Z4Plaq}
    (hconnected : connectedIn (L := z4Chain.toLattice) support) :
    connectedIn (L := z4Chain.toLattice)
      (support.map (timeShiftPlaquette shift)) := by
  intro first last hfirst hlast
  obtain ⟨sourceFirst, hsourceFirst, hfirstEq⟩ :=
    decodeMapMember (timeShiftPlaquette shift) support first hfirst
  obtain ⟨sourceLast, hsourceLast, hlastEq⟩ :=
    decodeMapMember (timeShiftPlaquette shift) support last hlast
  rw [← hfirstEq, ← hlastEq]
  exact timeShiftChain shift
    (hconnected sourceFirst sourceLast hsourceFirst hsourceLast)

/-! ## 2. Canonical re-encoding of a translated polymer -/

/-- Translate a canonical root by `shift` in Euclidean time and re-encode it
in the minimally enlarged corner-anchored box. -/
def timeShiftCanonicalRoot (shift base : Nat) (root : List Nat) : List Nat :=
  geometricSupportIds (base + shift)
    ((geometricPolymer base root).map (timeShiftPlaquette shift))

theorem timeShiftCanonicalRoot_sameSupport
    {shift base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (base + shift)
        (timeShiftCanonicalRoot shift base root))
      ((geometricPolymer base root).map (timeShiftPlaquette shift)) := by
  unfold timeShiftCanonicalRoot
  apply geometricSupportIds_sameSupport
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  exact timeShiftPlaquette_mem_box_add
    (geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource)

def timeShiftCanonicalRoot_nonempty
    {shift base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    Σ' face : Nat, face ∈ timeShiftCanonicalRoot shift base root := by
  obtain ⟨sourceFace, hsourceFace⟩ :=
    canonicalSurfacePolymers_allNonempty base root hroot
  have hsource : boxPlaquetteAt base sourceFace ∈
      geometricPolymer base root :=
    List.mem_map.mpr ⟨sourceFace, hsourceFace, rfl⟩
  have htranslated :
      timeShiftPlaquette shift (boxPlaquetteAt base sourceFace) ∈
        (geometricPolymer base root).map (timeShiftPlaquette shift) :=
    List.mem_map.mpr ⟨boxPlaquetteAt base sourceFace, hsource, rfl⟩
  have hencoded := (timeShiftCanonicalRoot_sameSupport hroot).2 _ htranslated
  obtain ⟨targetFace, htargetFace, _⟩ :=
    decodeMapMember (boxPlaquetteAt (base + shift))
      (timeShiftCanonicalRoot shift base root)
      (timeShiftPlaquette shift (boxPlaquetteAt base sourceFace)) hencoded
  exact ⟨targetFace, htargetFace⟩

def timeShiftCanonicalRoot_connected
    {shift base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    InternallyConnected (faceLinkAdjacentB (base + shift))
      (timeShiftCanonicalRoot shift base root) := by
  unfold timeShiftCanonicalRoot
  apply geometricSupportIds_connected
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact timeShiftPlaquette_mem_box_add
      (geometricPolymer_subset_box
        (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource)
  · exact timeShiftConnected shift
      (numericalConnectedToGeometric
        ((canonicalSurfacePolymers_allConnected base) root hroot))

theorem timeShiftCanonicalRoot_canonical
    {shift base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    timeShiftCanonicalRoot shift base root ∈
      canonicalSurfacePolymers (base + shift) :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (geometricSupportIds_mem_cutoffOneFaceSupports
      (base + shift)
      ((geometricPolymer base root).map (timeShiftPlaquette shift)))
    (timeShiftCanonicalRoot_nonempty hroot)
    (timeShiftCanonicalRoot_connected hroot)

theorem timeShiftCanonicalRoot_length
    {shift base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    (timeShiftCanonicalRoot shift base root).length = root.length := by
  have htargetNodup :
      (geometricPolymer (base + shift)
        (timeShiftCanonicalRoot shift base root)).Nodup :=
    geometricPolymer_nodup
      (canonicalSurfacePolymer_mem_faceSupports
        (timeShiftCanonicalRoot_canonical hroot))
  have hsourceNodup : (geometricPolymer base root).Nodup :=
    geometricPolymer_nodup
      (canonicalSurfacePolymer_mem_faceSupports hroot)
  have hshiftedNodup :
      ((geometricPolymer base root).map
        (timeShiftPlaquette shift)).Nodup :=
    nodup_map_of_injOn (timeShiftPlaquette shift)
      (geometricPolymer base root) hsourceNodup
      (fun _ _ _ _ heq => timeShiftPlaquette_injective shift heq)
  have hlength := sameSupport_length_eq_of_nodup
    (timeShiftCanonicalRoot_sameSupport hroot)
    htargetNodup hshiftedNodup
  rw [geometricPolymer_length_eq_support_length,
    List.length_map] at hlength
  exact hlength.trans
    (geometricPolymer_length_eq_support_length base root)

theorem timeShiftCanonicalRoot_injective_on_canonical
    {shift base : Nat} {left right : List Nat}
    (hleft : left ∈ canonicalSurfacePolymers base)
    (hright : right ∈ canonicalSurfacePolymers base)
    (heq : timeShiftCanonicalRoot shift base left =
      timeShiftCanonicalRoot shift base right) :
    left = right := by
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport hleft hright
  have hleftShift := timeShiftCanonicalRoot_sameSupport
    (shift := shift) hleft
  have hrightShift := timeShiftCanonicalRoot_sameSupport
    (shift := shift) hright
  rw [heq] at hleftShift
  have hmapped := sameSupport_trans (sameSupport_symm hleftShift) hrightShift
  exact sameSupport_of_map_injective_local
    (timeShiftPlaquette_injective shift) hmapped

theorem timeShiftCanonicalRoot_zero
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    timeShiftCanonicalRoot 0 base root = root := by
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    (by simpa using timeShiftCanonicalRoot_canonical (shift := 0) hroot)
    hroot
  have hsame := timeShiftCanonicalRoot_sameSupport (shift := 0) hroot
  have hzero :
      (geometricPolymer base root).map (timeShiftPlaquette 0) =
        geometricPolymer base root :=
    map_timeShiftPlaquette_zero_local _
  have hsame' : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer base (timeShiftCanonicalRoot 0 base root))
      ((geometricPolymer base root).map (timeShiftPlaquette 0)) := by
    simpa only [Nat.add_zero] using hsame
  exact sameSupport_right_congr_local hsame' hzero

theorem timeShiftCanonicalRoot_add
    {base : Nat} (first second : Nat) {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    timeShiftCanonicalRoot second (base + first)
        (timeShiftCanonicalRoot first base root) =
      timeShiftCanonicalRoot (first + second) base root := by
  have hfirstCanonical := timeShiftCanonicalRoot_canonical
    (shift := first) hroot
  have hleftCanonical := timeShiftCanonicalRoot_canonical
    (shift := second) hfirstCanonical
  have hrightCanonical :
      timeShiftCanonicalRoot (first + second) base root ∈
        canonicalSurfacePolymers ((base + first) + second) := by
    simpa only [Nat.add_assoc] using
      (timeShiftCanonicalRoot_canonical
        (shift := first + second) hroot)
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    hleftCanonical hrightCanonical
  have hsecondSupport := timeShiftCanonicalRoot_sameSupport
    (shift := second) hfirstCanonical
  have hfirstSupport := timeShiftCanonicalRoot_sameSupport
    (shift := first) hroot
  have hnested := sameSupport_trans hsecondSupport
    (sameSupport_map_local (timeShiftPlaquette second) hfirstSupport)
  have hnestedCombined : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer ((base + first) + second)
        (timeShiftCanonicalRoot second (base + first)
          (timeShiftCanonicalRoot first base root)))
      ((geometricPolymer base root).map
        (timeShiftPlaquette (first + second))) := by
    have hmap :
        ((geometricPolymer base root).map
          (timeShiftPlaquette first)).map (timeShiftPlaquette second) =
        (geometricPolymer base root).map
          (timeShiftPlaquette (first + second)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro plaquette _
      exact timeShiftPlaquette_add first second plaquette
    exact sameSupport_right_congr_local hnested hmap
  have hdirect := timeShiftCanonicalRoot_sameSupport
    (shift := first + second) hroot
  have hdirect' : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer ((base + first) + second)
        (timeShiftCanonicalRoot (first + second) base root))
      ((geometricPolymer base root).map
        (timeShiftPlaquette (first + second))) := by
    simpa only [Nat.add_assoc] using hdirect
  exact sameSupport_trans hnestedCombined (sameSupport_symm hdirect')

/-! ## 3. The semigroup on finite-cylinder presentations -/

def timeShiftFiniteCylinderChart
    (chart : FiniteCylinderChart) (shift : Nat) : FiniteCylinderChart where
  base := chart.base + shift
  roots := chart.roots.map (timeShiftCanonicalRoot shift chart.base)
  rootsCanonical := by
    intro root hroot
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hroot
    exact timeShiftCanonicalRoot_canonical
      (chart.rootsCanonical source hsource)

private theorem timeShiftCanonicalRoots_zero
    {base : Nat} (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    roots.map (timeShiftCanonicalRoot 0 base) = roots := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
      simp only [List.map_cons]
      rw [timeShiftCanonicalRoot_zero
        (hroots root List.mem_cons_self)]
      rw [ih (fun item hitem =>
        hroots item (List.mem_cons_of_mem root hitem))]

def timeShiftFiniteCylinderPresentation
    (presentation : FiniteCylinderPresentation) (shift : Nat) :
    FiniteCylinderPresentation :=
  (timeShiftFiniteCylinderChart presentation.chart shift).present
    presentation.predicate

private theorem finiteCylinderChart_ext_local
    {left right : FiniteCylinderChart}
    (hbase : left.base = right.base)
    (hroots : left.roots = right.roots) : left = right := by
  obtain ⟨leftBase, leftRoots, leftCanonical⟩ := left
  obtain ⟨rightBase, rightRoots, rightCanonical⟩ := right
  simp only at hbase hroots
  subst rightBase
  subst rightRoots
  rfl

private theorem finiteCylinderPresentation_ext_local
    {left right : FiniteCylinderPresentation}
    (hchart : left.chart = right.chart)
    (hpredicate : left.predicate = right.predicate) : left = right := by
  obtain ⟨leftChart, leftPredicate⟩ := left
  obtain ⟨rightChart, rightPredicate⟩ := right
  simp only at hchart hpredicate
  subst rightChart
  subst rightPredicate
  rfl

theorem timeShiftFiniteCylinderChart_zero
    (chart : FiniteCylinderChart) :
    timeShiftFiniteCylinderChart chart 0 = chart := by
  obtain ⟨base, roots, hrootsCanonical⟩ := chart
  have hroots :
      roots.map (timeShiftCanonicalRoot 0 base) = roots :=
    timeShiftCanonicalRoots_zero roots hrootsCanonical
  apply finiteCylinderChart_ext_local
  · simp [timeShiftFiniteCylinderChart]
  · exact hroots

theorem timeShiftFiniteCylinderChart_add
    (chart : FiniteCylinderChart) (first second : Nat) :
    timeShiftFiniteCylinderChart
        (timeShiftFiniteCylinderChart chart first) second =
      timeShiftFiniteCylinderChart chart (first + second) := by
  obtain ⟨base, roots, hrootsCanonical⟩ := chart
  have hroots :
      (roots.map (timeShiftCanonicalRoot first base)).map
          (timeShiftCanonicalRoot second (base + first)) =
        roots.map (timeShiftCanonicalRoot (first + second) base) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact timeShiftCanonicalRoot_add first second
      (hrootsCanonical root hroot)
  apply finiteCylinderChart_ext_local
  · simp [timeShiftFiniteCylinderChart, Nat.add_assoc]
  · exact hroots

theorem timeShiftFiniteCylinderPresentation_zero
    (presentation : FiniteCylinderPresentation) :
    timeShiftFiniteCylinderPresentation presentation 0 = presentation := by
  apply finiteCylinderPresentation_ext_local
  · exact timeShiftFiniteCylinderChart_zero presentation.chart
  · rfl

theorem timeShiftFiniteCylinderPresentation_add
    (presentation : FiniteCylinderPresentation) (first second : Nat) :
    timeShiftFiniteCylinderPresentation
        (timeShiftFiniteCylinderPresentation presentation first) second =
      timeShiftFiniteCylinderPresentation presentation (first + second) := by
  apply finiteCylinderPresentation_ext_local
  · exact timeShiftFiniteCylinderChart_add
      presentation.chart first second
  · rfl

/-! ## Axiom audit -/

#print axioms timeShiftCanonicalRoot_sameSupport
#print axioms timeShiftCanonicalRoot_canonical
#print axioms timeShiftCanonicalRoot_injective_on_canonical
#print axioms timeShiftCanonicalRoot_add
#print axioms timeShiftFiniteCylinderPresentation_zero
#print axioms timeShiftFiniteCylinderPresentation_add

end YMGap.Continuum.Z4FiniteCylinderTimeTranslation
