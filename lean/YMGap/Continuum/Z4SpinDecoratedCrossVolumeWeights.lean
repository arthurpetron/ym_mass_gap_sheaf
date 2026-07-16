/-
# Spin-decorated cross-volume weight transport

The geometric zero-extension constructed in
`Z4SpinDecoratedCrossVolumeLocality` preserves more than support.  This file
starts the exact weight-level transport by proving that the complete
heat-kernel face product is unchanged when a bounded box is enlarged: old
plaquette spins are recovered geometrically and every inserted plaquette has
the vacuum coefficient one.
-/

import YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality

namespace YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open scoped List
open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4NestedBoxEnumeration
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDependentIncidenceProductBound
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. A generic constructive finite product -/

def listQProduct {A : Type} (value : A → Q') : List A → Q'
  | [] => 1
  | head :: tail => value head * listQProduct value tail

theorem listQProduct_map {A B : Type} (value : B → Q')
    (f : A → B) : ∀ xs : List A,
    listQProduct value (xs.map f) =
      listQProduct (fun x => value (f x)) xs
  | [] => rfl
  | _ :: xs => by
      simp only [List.map_cons, listQProduct]
      rw [listQProduct_map value f xs]

theorem listQProduct_congr {A : Type} (left right : A → Q') :
    ∀ xs : List A, (∀ x, x ∈ xs → left x = right x) →
      listQProduct left xs = listQProduct right xs
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [listQProduct]
      rw [hagree head List.mem_cons_self,
        listQProduct_congr left right tail
          (fun x hx => hagree x (List.mem_cons_of_mem head hx))]

theorem listQProduct_congr_eqv {A : Type} (left right : A → Q') :
    ∀ xs : List A, (∀ x, x ∈ xs → left x ≈ right x) →
      listQProduct left xs ≈ listQProduct right xs
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hagree =>
      qmul_congr
        (hagree head List.mem_cons_self)
        (listQProduct_congr_eqv left right tail
          (fun x hx => hagree x (List.mem_cons_of_mem head hx)))

theorem listQProduct_perm {A : Type} (value : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      listQProduct value left ≈ listQProduct value right
  | _, _, List.Perm.nil => Q'.eqv_refl 1
  | _, _, List.Perm.cons _ h =>
      Q'.mul_eqv_congr_left _ _ _ (listQProduct_perm value h)
  | _, _, List.Perm.swap a b rest => by
      change value b * (value a * listQProduct value rest) ≈
        value a * (value b * listQProduct value rest)
      refine Q'.eqv_trans _
        ((value b * value a) * listQProduct value rest) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((value a * value b) * listQProduct value rest) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (listQProduct_perm value hleft)
        (listQProduct_perm value hright)

theorem eliminateLinks_eq_listQProduct (value : Nat → Q') :
    ∀ edges : List Nat,
      eliminateLinks value edges = listQProduct value edges
  | [] => rfl
  | edge :: rest => by
      simp only [eliminateLinks, listQProduct]
      rw [eliminateLinks_eq_listQProduct value rest]

/-- Inserting factors equivalent to one into a duplicate-free ordered list
does not change its rational product. -/
theorem listQProduct_sublist_vacuum {A : Type} (value : A → Q')
    {source target : List A} (hsub : source <+ target)
    (htarget : target.Nodup)
    (hvacuum : ∀ item, item ∈ target → item ∉ source →
      value item ≈ 1) :
    listQProduct value target ≈ listQProduct value source := by
  induction hsub with
  | slnil => exact Q'.eqv_refl 1
  | @cons source target item hsub ih =>
      have hparts := List.nodup_cons.mp htarget
      have hnotSource : item ∉ source := by
        intro hmem
        exact hparts.1 (List.Sublist.mem hmem hsub)
      have hhead := hvacuum item List.mem_cons_self hnotSource
      have htail := ih hparts.2
        (fun x hx hnot => hvacuum x
          (List.mem_cons_of_mem item hx) hnot)
      exact Q'.eqv_trans _ (1 * listQProduct value source) _
        (qmul_congr hhead htail) (Q'.one_mul_eqv _)
  | @cons₂ source target item hsub ih =>
      have hparts := List.nodup_cons.mp htarget
      have htailVacuum : ∀ x, x ∈ target → x ∉ source →
          value x ≈ 1 := by
        intro x hx hnot
        have hne : x ≠ item := by
          intro heq
          subst x
          exact hparts.1 hx
        apply hvacuum x (List.mem_cons_of_mem item hx)
        simp only [List.mem_cons, not_or]
        exact ⟨hne, hnot⟩
      exact qmul_congr (Q'.eqv_refl _) (ih hparts.2 htailVacuum)

/-! ## 2. Numerical and geometric presentations of the face product -/

def geometricFaceFactor (w : Q') (K : Nat)
    (spin : Z4Plaq → Nat) (plaquettes : List Z4Plaq) : Q' :=
  listQProduct
    (fun plaquette => coeffAt (heatKernelPacket K w) (spin plaquette))
    plaquettes

theorem parametricKPhysicalFaceFactor_eq_geometric
    (w : Q') (K n : Nat) (physical : EdgeLabelling) :
    parametricKPhysicalFaceFactor w K n physical =
      geometricFaceFactor w K
        (geometricSpinOfPhysical n physical) (boxPlaquettes n) := by
  unfold parametricKPhysicalFaceFactor geometricFaceFactor
  unfold plaquetteEdgeCount
  rw [← enumerate_map_fst_eq_range]
  rw [eliminateLinks_eq_listQProduct, listQProduct_map]
  have hagree :
      listQProduct
          (fun indexed : Nat × Z4Plaq =>
            coeffAt (heatKernelPacket K w) (physical indexed.1))
          (enumerate (boxPlaquettes n)) =
        listQProduct
          (fun indexed : Nat × Z4Plaq =>
            coeffAt (heatKernelPacket K w)
              (geometricSpinOfPhysical n physical indexed.2))
          (enumerate (boxPlaquettes n)) := by
    apply listQProduct_congr
    intro indexed hindexed
    rw [geometricSpinOfPhysical_eq_of_enumerate hindexed]
  rw [hagree]
  rw [← listQProduct_map
    (fun plaquette : Z4Plaq =>
      coeffAt (heatKernelPacket K w)
        (geometricSpinOfPhysical n physical plaquette)) Prod.snd]
  rw [enumerate_map_snd]

theorem geometricFaceFactor_transport_eq
    (w : Q') (K small large : Nat) (physical : EdgeLabelling) :
    geometricFaceFactor w K
        (geometricSpinOfPhysical large
          (transportPhysical small large physical))
        (boxPlaquettes large) =
      geometricFaceFactor w K
        (geometricSpinOfPhysical small physical)
        (boxPlaquettes large) := by
  unfold geometricFaceFactor
  apply listQProduct_congr
  intro plaquette hplaquette
  rw [geometricSpinOfTransport_eq_of_mem_box hplaquette]

/-! ## 3. Exact cross-volume face-factor locality -/

/-- The complete arbitrary-cutoff heat-kernel face product is invariant under
the geometric zero extension from a nested smaller box. -/
theorem parametricKPhysicalFaceFactor_cross_volume
    (w : Q') (K : Nat) {small large : Nat}
    (hsmall : small ≤ large) (physical : EdgeLabelling) :
    parametricKPhysicalFaceFactor w K small physical ≈
      parametricKPhysicalFaceFactor w K large
        (transportPhysical small large physical) := by
  rw [parametricKPhysicalFaceFactor_eq_geometric,
    parametricKPhysicalFaceFactor_eq_geometric,
    geometricFaceFactor_transport_eq]
  apply Q'.eqv_symm
  unfold geometricFaceFactor
  apply listQProduct_sublist_vacuum
    (fun plaquette => coeffAt (heatKernelPacket K w)
      (geometricSpinOfPhysical small physical plaquette))
    (boxPlaquettes_sublist hsmall)
    (boxPlaquettes_nodup large)
  intro plaquette _ hnot
  rw [geometricSpinOfPhysical_zero_of_not_mem
    small physical hnot]
  rw [coeffAt_heatKernelPacket (show 0 < K + 1 by omega),
    coeffW_zero]
  exact Q'.eqv_refl 1

/-! ## 4. A geometric normal form for the global link product -/

/-- A link factor with a fixed dummy enumeration index.  The private block
base attached to that index is immaterial: the actual factor only sees the
ordered incident-spin prefix. -/
def canonicalGeometricLinkFactor (K n : Nat)
    (physical : EdgeLabelling) (ell : Z4Link) : Q' :=
  explicitLinkMultiplicityFactor K n physical (0, ell)

theorem explicitLinkMultiplicityFactor_eq_canonical
    (K n : Nat) (physical : EdgeLabelling) (indexed : Nat × Z4Link) :
    explicitLinkMultiplicityFactor K n physical indexed =
      canonicalGeometricLinkFactor K n physical indexed.2 := by
  unfold explicitLinkMultiplicityFactor canonicalGeometricLinkFactor
  apply congrArg Q'.ofNat
  rw [actualExplicitMultiplicity_eq_incidentList,
    actualExplicitMultiplicity_eq_incidentList]

theorem canonicalGeometricLinkFactor_cross_volume
    {K small large : Nat} (hsmall : small ≤ large)
    {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount small))) (ell : Z4Link) :
    canonicalGeometricLinkFactor K small physical ell =
      canonicalGeometricLinkFactor K large
        (transportPhysical small large physical) ell := by
  unfold canonicalGeometricLinkFactor explicitLinkMultiplicityFactor
  apply congrArg Q'.ofNat
  exact explicitLinkMultiplicity_cross_volume hsmall hphysical ell
    (linkBlockBase small 0) (linkBlockBase large 0)

/-- A link absent from the smaller box is untouched by the transported
labelling and hence contributes exactly one in the larger box. -/
theorem canonicalGeometricLinkFactor_transport_eq_one_of_new
    (K small large : Nat) (physical : EdgeLabelling) {ell : Z4Link}
    (hnew : ell ∉ distinctBoxLinks small) :
    canonicalGeometricLinkFactor K large
        (transportPhysical small large physical) ell = 1 := by
  unfold canonicalGeometricLinkFactor
  apply explicitLinkMultiplicityFactor_eq_one_of_untouched
  unfold linkTouchesExcitationB
  apply (hasExcitedB_false_iff_zero_on
    (transportPhysical small large physical)
    (incidentPlaqIds large ell)).2
  intro targetId hincident
  obtain ⟨plaquette, hindexed, hedge⟩ :=
    mem_incidentPlaqIds.mp hincident
  rw [transportPhysical_eq_on_enumerate hindexed]
  apply geometricSpinOfPhysical_zero_of_not_mem
  intro hsmallPlaq
  apply hnew
  unfold distinctBoxLinks
  apply List.mem_eraseDups.mpr
  exact boundary_mem_boxLinks hsmallPlaq hedge

def canonicalGeometricLinkProduct (K n : Nat)
    (physical : EdgeLabelling) (links : List Z4Link) : Q' :=
  listQProduct (canonicalGeometricLinkFactor K n physical) links

theorem explicitLinkMultiplicityProduct_eq_canonical
    (K n : Nat) (physical : EdgeLabelling) :
    ∀ links : List (Nat × Z4Link),
    explicitLinkMultiplicityProduct K n physical links =
      canonicalGeometricLinkProduct K n physical
        (links.map Prod.snd)
  | [] => rfl
  | indexed :: rest => by
      change explicitLinkMultiplicityFactor K n physical indexed *
          explicitLinkMultiplicityProduct K n physical rest =
        canonicalGeometricLinkFactor K n physical indexed.2 *
          canonicalGeometricLinkProduct K n physical
            (rest.map Prod.snd)
      rw [explicitLinkMultiplicityFactor_eq_canonical,
        explicitLinkMultiplicityProduct_eq_canonical K n physical rest]

theorem explicitLinkMultiplicityProduct_full_eq_canonical
    (K n : Nat) (physical : EdgeLabelling) :
    explicitLinkMultiplicityProduct K n physical
        (enumerate (distinctBoxLinks n)) =
      canonicalGeometricLinkProduct K n physical
        (distinctBoxLinks n) := by
  rw [explicitLinkMultiplicityProduct_eq_canonical,
    enumerate_map_snd]

/-! ## 5. Nested distinct-link sets -/

theorem distinctBoxLinks_subset {small large : Nat}
    (hsmall : small ≤ large) {ell : Z4Link}
    (hell : ell ∈ distinctBoxLinks small) :
    ell ∈ distinctBoxLinks large := by
  unfold distinctBoxLinks at hell ⊢
  apply List.mem_eraseDups.mpr
  exact boxLinks_mono hsmall (List.mem_eraseDups.mp hell)

def inheritedBoxLinks (small large : Nat) : List Z4Link :=
  (distinctBoxLinks large).filter
    (fun ell => decide (ell ∈ distinctBoxLinks small))

theorem inheritedBoxLinks_sublist (small large : Nat) :
    inheritedBoxLinks small large <+ distinctBoxLinks large :=
  List.filter_sublist

theorem inheritedBoxLinks_nodup (small large : Nat) :
    (inheritedBoxLinks small large).Nodup :=
  List.filter_sublist.nodup (distinctBoxLinks_nodup large)

theorem inheritedBoxLinks_perm_source {small large : Nat}
    (hsmall : small ≤ large) :
    (distinctBoxLinks small).Perm (inheritedBoxLinks small large) := by
  apply Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
    (distinctBoxLinks small) (inheritedBoxLinks small large)
    (distinctBoxLinks_nodup small)
    (inheritedBoxLinks_nodup small large)
  intro ell
  unfold inheritedBoxLinks
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hell
    exact ⟨distinctBoxLinks_subset hsmall hell, hell⟩
  · exact fun hell => hell.2

/-! ## 5a. Exact round trip of ordered numerical supports -/

theorem faceSupport_eq_of_geometric_sameSupport
    {n : Nat} {left right : List Nat}
    (hleft : left ∈ cutoffOneFaceSupports n)
    (hright : right ∈ cutoffOneFaceSupports n)
    (hsupport : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n left) (geometricPolymer n right)) :
    left = right := by
  apply sublists_eq_of_mem_iff (physicalFaceEdges n) left right
    (physicalFaceEdges_nodup n) hleft hright
  intro face
  constructor
  · intro hface
    have hactual : boxPlaquetteAt n face ∈
        geometricPolymer n left :=
      List.mem_map.mpr ⟨face, hface, rfl⟩
    have hrightActual := hsupport.1 _ hactual
    obtain ⟨rightFace, hrightFace, heq⟩ :=
      List.mem_map.mp hrightActual
    have hid : rightFace = face :=
      boxPlaquetteAt_injective_on_physical
        (mem_of_mem_sublists (physicalFaceEdges n) right hright
          rightFace hrightFace)
        (mem_of_mem_sublists (physicalFaceEdges n) left hleft
          face hface)
        heq
    rw [← hid]
    exact hrightFace
  · intro hface
    have hactual : boxPlaquetteAt n face ∈
        geometricPolymer n right :=
      List.mem_map.mpr ⟨face, hface, rfl⟩
    have hleftActual := hsupport.2 _ hactual
    obtain ⟨leftFace, hleftFace, heq⟩ :=
      List.mem_map.mp hleftActual
    have hid : leftFace = face :=
      boxPlaquetteAt_injective_on_physical
        (mem_of_mem_sublists (physicalFaceEdges n) left hleft
          leftFace hleftFace)
        (mem_of_mem_sublists (physicalFaceEdges n) right hright
          face hface)
        heq
    rw [← hid]
    exact hleftFace

theorem transportPolymer_roundtrip
    {small large : Nat} (hsmall : small ≤ large)
    {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports small) :
    transportPolymer large small
        (transportPolymer small large support) = support := by
  let targetSupport := transportPolymer small large support
  have hforward : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer small support)
      (geometricPolymer large targetSupport) := by
    exact transportPolymer_sameSupport hsmall hsupport
  have htargetInSmall : ∀ plaquette,
      plaquette ∈ geometricPolymer large targetSupport →
        plaquette ∈ boxPlaquettes small := by
    intro plaquette hplaquette
    exact geometricPolymer_subset_box hsupport plaquette
      (hforward.2 plaquette hplaquette)
  have hback : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer small
        (geometricSupportIds small
          (geometricPolymer large targetSupport)))
      (geometricPolymer large targetSupport) :=
    geometricSupportIds_sameSupport htargetInSmall
  change geometricSupportIds small
      (geometricPolymer large targetSupport) = support
  apply faceSupport_eq_of_geometric_sameSupport
    (geometricSupportIds_mem_cutoffOneFaceSupports small
      (geometricPolymer large targetSupport)) hsupport
  exact sameSupport_trans hback (sameSupport_symm hforward)

/-! ## 5b. Restriction is inverse on an exact transported support -/

theorem transportPhysical_roundtrip_of_support
    {cutoff small large : Nat} (hsmall : small ≤ large)
    {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports small)
    {target : EdgeLabelling}
    (htarget : target ∈ physicalLabellingsWithSupport cutoff large
      (transportPolymer small large support)) :
    transportPhysical small large
        (transportPhysical large small target) = target := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp htarget
  have hforward := transportPolymer_sameSupport hsmall hsupport
  funext targetId
  by_cases htargetId : targetId ∈
      List.range (plaquetteEdgeCount large)
  · have hindexed :
        (targetId, boxPlaquetteAt large targetId) ∈
          enumerate (boxPlaquettes large) :=
      boxPlaquetteAt_mem_enumerate (physicalFaceId_lt htargetId)
    rw [transportPhysical_eq_on_enumerate hindexed,
      ← geometricSpinOfPhysical_eq_of_enumerate
        (physical := target) hindexed]
    by_cases hsmallPlaq : boxPlaquetteAt large targetId ∈
        boxPlaquettes small
    · exact geometricSpinOfTransport_eq_of_mem_box hsmallPlaq
    · rw [geometricSpinOfPhysical_zero_of_not_mem
          small (transportPhysical large small target) hsmallPlaq]
      have htargetZero : geometricSpinOfPhysical large target
          (boxPlaquetteAt large targetId) = 0 := by
        by_cases hzero : geometricSpinOfPhysical large target
            (boxPlaquetteAt large targetId) = 0
        · exact hzero
        · have hpositive : 1 ≤ geometricSpinOfPhysical large target
              (boxPlaquetteAt large targetId) := by omega
          have hgeometric :=
            (geometricSpin_positive_iff_mem_geometricSupport large target
              (boxPlaquetteAt large targetId)).1 hpositive
          rw [hparts.2] at hgeometric
          have hsourceGeometric := hforward.2 _ hgeometric
          exact False.elim (hsmallPlaq
            (geometricPolymer_subset_box hsupport _ hsourceGeometric))
      rw [htargetZero]
  · have hleftZero := transportPhysical_zero_outside small large
        (transportPhysical large small target) htargetId
    have hrightZero := (boundedEdgeLabellings_sound cutoff
      (List.range (plaquetteEdgeCount large)) target hparts.1).2
        targetId htargetId
    exact hleftZero.trans hrightZero.symm

theorem restrictPhysical_mem_sourceFiber
    {cutoff small large : Nat} (hsmall : small ≤ large)
    {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports small)
    {target : EdgeLabelling}
    (htarget : target ∈ physicalLabellingsWithSupport cutoff large
      (transportPolymer small large support)) :
    transportPhysical large small target ∈
      physicalLabellingsWithSupport cutoff small support := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp htarget
  apply mem_physicalLabellingsWithSupport_iff.mpr
  constructor
  · exact transportPhysical_mem_bounded hparts.1
  · rw [excitedPlaquetteIds_transportPhysical, hparts.2,
      transportPolymer_roundtrip hsmall hsupport]

theorem targetFiber_mem_transportedPhysicalFiber
    {cutoff small large : Nat} (hsmall : small ≤ large)
    {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports small)
    {target : EdgeLabelling}
    (htarget : target ∈ physicalLabellingsWithSupport cutoff large
      (transportPolymer small large support)) :
    target ∈ transportedPhysicalFiber cutoff small large support := by
  apply mem_transportedPhysicalFiber_iff.mpr
  exact ⟨transportPhysical large small target,
    restrictPhysical_mem_sourceFiber hsmall hsupport htarget,
    transportPhysical_roundtrip_of_support hsmall hsupport htarget⟩

theorem mem_transportedPhysicalFiber_iff_targetFiber
    {cutoff small large : Nat} (hsmall : small ≤ large)
    {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports small)
    (target : EdgeLabelling) :
    target ∈ transportedPhysicalFiber cutoff small large support ↔
      target ∈ physicalLabellingsWithSupport cutoff large
        (transportPolymer small large support) := by
  constructor
  · exact transportedPhysicalFiber_mem_target
  · exact targetFiber_mem_transportedPhysicalFiber hsmall hsupport

/-- Extensional equality of duplicate-free lists implies permutation without
any decidable equality on the element type.  This matters here because a
physical labelling is a function `Nat → Nat`. -/
theorem perm_of_nodup_mem_iff_constructive {A : Type} :
    ∀ (left right : List A), left.Nodup → right.Nodup →
      (∀ item, item ∈ left ↔ item ∈ right) → left.Perm right
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      have hfalse : head ∈ ([] : List A) :=
        (hmem head).2 List.mem_cons_self
      cases hfalse
  | head :: tail, right, hleft, hright, hmem => by
      have hleftParts := List.nodup_cons.mp hleft
      have hheadRight : head ∈ right :=
        (hmem head).1 List.mem_cons_self
      obtain ⟨before, after, hsplit⟩ := List.append_of_mem hheadRight
      subst right
      have hmiddle : (head :: (before ++ after)).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: (before ++ after)).Nodup :=
        hmiddle.symm.nodup hright
      have hmiddleParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ item,
          item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hleftParts.1 hitem
          have hy := (hmem item).1
            (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hy with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hy : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp ((hmem item).2 hy)).resolve_left hne
      have htailPerm := perm_of_nodup_mem_iff_constructive
        tail (before ++ after) hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

theorem transportedPhysicalFiber_perm_target
    {cutoff small large : Nat} (hsmall : small ≤ large)
    {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports small) :
    (transportedPhysicalFiber cutoff small large support).Perm
      (physicalLabellingsWithSupport cutoff large
        (transportPolymer small large support)) := by
  apply perm_of_nodup_mem_iff_constructive
    (transportedPhysicalFiber cutoff small large support)
    (physicalLabellingsWithSupport cutoff large
      (transportPolymer small large support))
    (transportedPhysicalFiber_nodup hsmall support)
    (physicalLabellingsWithSupport_nodup cutoff large
      (transportPolymer small large support))
  intro target
  exact mem_transportedPhysicalFiber_iff_targetFiber
    hsmall hsupport target

/-! ## 6. Exact global cross-volume link locality -/

/-- The product of every explicit local fusion cardinality is invariant under
geometric zero extension to a nested larger box. -/
theorem explicitLinkMultiplicityProduct_cross_volume
    {K small large : Nat} (hsmall : small ≤ large)
    {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount small))) :
    explicitLinkMultiplicityProduct K small physical
        (enumerate (distinctBoxLinks small)) ≈
      explicitLinkMultiplicityProduct K large
        (transportPhysical small large physical)
        (enumerate (distinctBoxLinks large)) := by
  rw [explicitLinkMultiplicityProduct_full_eq_canonical,
    explicitLinkMultiplicityProduct_full_eq_canonical]
  unfold canonicalGeometricLinkProduct
  let targetFactor := canonicalGeometricLinkFactor K large
    (transportPhysical small large physical)
  have hlocal :
      listQProduct (canonicalGeometricLinkFactor K small physical)
          (distinctBoxLinks small) ≈
        listQProduct targetFactor (distinctBoxLinks small) := by
    apply listQProduct_congr_eqv
    intro ell _
    exact Q'.eqv_of_eq
      (canonicalGeometricLinkFactor_cross_volume
        hsmall hphysical ell)
  have hperm :
      listQProduct targetFactor (distinctBoxLinks small) ≈
        listQProduct targetFactor (inheritedBoxLinks small large) :=
    listQProduct_perm targetFactor
      (inheritedBoxLinks_perm_source hsmall)
  have hvacuum :
      listQProduct targetFactor (distinctBoxLinks large) ≈
        listQProduct targetFactor (inheritedBoxLinks small large) := by
    apply listQProduct_sublist_vacuum targetFactor
      (inheritedBoxLinks_sublist small large)
      (distinctBoxLinks_nodup large)
    intro ell hell hnotInherited
    apply Q'.eqv_of_eq
    apply canonicalGeometricLinkFactor_transport_eq_one_of_new
    intro hsource
    apply hnotInherited
    unfold inheritedBoxLinks
    exact List.mem_filter.mpr
      ⟨hell, by simpa only [decide_eq_true_eq]⟩
  exact Q'.eqv_trans _ _ _ hlocal
    (Q'.eqv_trans _ _ _ hperm (Q'.eqv_symm hvacuum))

/-! ## 7. Full term and embedded-fibre transport -/

/-- Both exact factors of the arbitrary-cutoff physical spin-foam summand
are invariant under nested-box zero extension. -/
theorem parametricKPhysicalTerm_cross_volume
    (w : Q') {K small large : Nat} (hsmall : small ≤ large)
    {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount small))) :
    parametricKPhysicalTerm w K small physical ≈
      parametricKPhysicalTerm w K large
        (transportPhysical small large physical) := by
  unfold parametricKPhysicalTerm
  exact qmul_congr
    (parametricKPhysicalFaceFactor_cross_volume
      w K hsmall physical)
    (explicitLinkMultiplicityProduct_cross_volume hsmall hphysical)

theorem listQSum_map_eqv {A B : Type}
    (sourceWeight : A → Q') (targetWeight : B → Q')
    (reindex : A → B) : ∀ source : List A,
    (∀ x, x ∈ source →
      sourceWeight x ≈ targetWeight (reindex x)) →
    listQSum sourceWeight source ≈
      listQSum targetWeight (source.map reindex)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hterm =>
      Q'.add_eqv_congr'
        (hterm head List.mem_cons_self)
        (listQSum_map_eqv sourceWeight targetWeight reindex tail
          (fun x hx => hterm x (List.mem_cons_of_mem head hx)))

/-- The exact larger-box weight of the duplicate-free embedded support fibre.
This is deliberately distinguished from the full target fibre; proving that
no additional target configurations matter is the next measure-level step. -/
def transportedKSupportActivity (cutoff small large : Nat)
    (support : List Nat) : Q' :=
  listQSum
    (parametricKPhysicalTerm anchorCoupling cutoff large)
    (transportedPhysicalFiber cutoff small large support)

/-- Exact equality between a smaller support activity and its literal
embedded subensemble in every nested larger box. -/
theorem parametricKSupportActivity_eqv_transported
    {cutoff small large : Nat} (hsmall : small ≤ large)
    (support : List Nat) :
    parametricKSupportActivity cutoff small support ≈
      transportedKSupportActivity cutoff small large support := by
  unfold parametricKSupportActivity transportedKSupportActivity
    transportedPhysicalFiber
  apply listQSum_map_eqv
  intro physical hphysical
  exact parametricKPhysicalTerm_cross_volume
    anchorCoupling hsmall
    (mem_physicalLabellingsWithSupport_iff.mp hphysical).1

/-- **Exact arbitrary-spin support activity compatibility.**  For every valid
numerical support, every physical spin decoration in the larger transported
fibre is uniquely the zero extension of a smaller-box decoration, and the
complete summed activity is identical. -/
theorem parametricKSupportActivity_cross_volume
    {cutoff small large : Nat} (hsmall : small ≤ large)
    {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports small) :
    parametricKSupportActivity cutoff small support ≈
      parametricKSupportActivity cutoff large
        (transportPolymer small large support) := by
  refine Q'.eqv_trans _
    (transportedKSupportActivity cutoff small large support) _
    (parametricKSupportActivity_eqv_transported hsmall support) ?_
  unfold transportedKSupportActivity parametricKSupportActivity
  exact Z4CanonicalPolymerRange.listQSum_perm
    (parametricKPhysicalTerm anchorCoupling cutoff large)
    (transportedPhysicalFiber_perm_target hsmall hsupport)

#print axioms listQProduct_sublist_vacuum
#print axioms parametricKPhysicalFaceFactor_eq_geometric
#print axioms parametricKPhysicalFaceFactor_cross_volume
#print axioms explicitLinkMultiplicityFactor_eq_canonical
#print axioms canonicalGeometricLinkFactor_transport_eq_one_of_new
#print axioms explicitLinkMultiplicityProduct_cross_volume
#print axioms parametricKPhysicalTerm_cross_volume
#print axioms parametricKSupportActivity_eqv_transported
#print axioms transportPolymer_roundtrip
#print axioms transportPhysical_roundtrip_of_support
#print axioms transportedPhysicalFiber_perm_target
#print axioms parametricKSupportActivity_cross_volume

end YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
