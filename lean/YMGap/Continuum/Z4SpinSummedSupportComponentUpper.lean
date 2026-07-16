/-
# Componentwise upper factorization of spin-summed support activity

For a fixed support, every full physical labelling restricts to one bounded
labelling on each canonical connected component.  This module constructs the
finite Cartesian target explicitly and proves that restriction is injective
and weight-preserving.  Since function equality is not decidable
constructively, target elements are encoded by their complete finite spin
vectors together with their exact rational weight before applying the finite
weighted-injection lemma.
-/

import YMGap.Continuum.Z4SpinSummedSupportBoundaryTail
import YMGap.Continuum.Z4CanonicalDecoratedConnectedSurfaceGas

namespace YMGap.Continuum.Z4SpinSummedSupportComponentUpper

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4AllSpinSurfaceComponentLabels
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalDecoratedConnectedSurfaceGas
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedSupportPartition
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Cartesian enumeration aligned with a support family -/

inductive SupportMatched (cutoff n : Nat) :
    List (List Nat) → List EdgeLabelling → Prop
  | nil : SupportMatched cutoff n [] []
  | cons {support : List Nat} {supports : List (List Nat)}
      {label : EdgeLabelling} {labels : List EdgeLabelling} :
      label ∈ physicalLabellingsWithSupport cutoff n support →
      SupportMatched cutoff n supports labels →
      SupportMatched cutoff n (support :: supports) (label :: labels)

def supportFamilyLabellings (cutoff n : Nat) :
    List (List Nat) → List (List EdgeLabelling)
  | [] => [[]]
  | support :: supports =>
      (cartesian (physicalLabellingsWithSupport cutoff n support)
        (supportFamilyLabellings cutoff n supports)).map
          (fun pair => pair.1 :: pair.2)

theorem mem_supportFamilyLabellings_iff (cutoff n : Nat) :
    ∀ (supports : List (List Nat)) (labels : List EdgeLabelling),
      labels ∈ supportFamilyLabellings cutoff n supports ↔
        SupportMatched cutoff n supports labels
  | [], labels => by
      constructor
      · intro hlabels
        have heq : labels = [] := List.mem_singleton.mp hlabels
        subst labels
        exact SupportMatched.nil
      · intro hmatched
        cases hmatched
        exact List.mem_cons_self
  | support :: supports, labels => by
      constructor
      · intro hlabels
        unfold supportFamilyLabellings at hlabels
        obtain ⟨pair, hpair, heq⟩ := List.mem_map.mp hlabels
        rw [← heq]
        have hparts :=
          (mem_cartesian_iff
            (physicalLabellingsWithSupport cutoff n support)
            (supportFamilyLabellings cutoff n supports) pair).1 hpair
        exact SupportMatched.cons hparts.1
          ((mem_supportFamilyLabellings_iff cutoff n
            supports pair.2).1 hparts.2)
      · intro hmatched
        cases hmatched with
        | cons hlabel hlabels =>
            unfold supportFamilyLabellings
            apply List.mem_map.mpr
            refine ⟨(_, _), ?_, rfl⟩
            exact (mem_cartesian_iff
              (physicalLabellingsWithSupport cutoff n support)
              (supportFamilyLabellings cutoff n supports) _).2
                ⟨hlabel,
                  (mem_supportFamilyLabellings_iff cutoff n
                    supports _).2 hlabels⟩

theorem supportFamilyLabellings_nodup (cutoff n : Nat) :
    ∀ supports : List (List Nat),
      (supportFamilyLabellings cutoff n supports).Nodup
  | [] => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | support :: supports => by
      unfold supportFamilyLabellings
      apply nodup_map_of_injOn
      · exact cartesian_nodup _ _
          (physicalLabellingsWithSupport_nodup cutoff n support)
          (supportFamilyLabellings_nodup cutoff n supports)
      · intro left _ right _ heq
        rcases left with ⟨leftHead, leftTail⟩
        rcases right with ⟨rightHead, rightTail⟩
        injection heq with hhead htail
        exact Prod.ext hhead htail

theorem supportMatched_kPhysicalFamily
    {cutoff n : Nat} : ∀ {supports : List (List Nat)}
      {labels : List EdgeLabelling},
      SupportMatched cutoff n supports labels →
        KPhysicalFamily cutoff n labels
  | _, _, SupportMatched.nil => fun label hlabel =>
      absurd hlabel List.not_mem_nil
  | _, _, SupportMatched.cons hhead htail => by
      intro label hlabel
      rcases List.mem_cons.mp hlabel with heq | hrest
      · subst label
        exact (mem_physicalLabellingsWithSupport_iff.mp hhead).1
      · exact supportMatched_kPhysicalFamily htail label hrest

def parametricKSupportFamilyActivity (cutoff n : Nat) :
    List (List Nat) → Q'
  | [] => 1
  | support :: supports =>
      parametricKSupportActivity cutoff n support *
        parametricKSupportFamilyActivity cutoff n supports

private theorem parametricKPhysicalTermProduct_nonnegative
    (cutoff n : Nat) : ∀ labels : List EdgeLabelling,
    (0 : Q') ≤
      parametricKPhysicalTermProduct anchorCoupling cutoff n labels
  | [] => Q'.zero_le_one
  | label :: labels =>
      Q'.mul_nonneg _ _
        (parametricKPhysicalTerm_nonnegative (by decide)
          cutoff n label)
        (parametricKPhysicalTermProduct_nonnegative cutoff n labels)

theorem supportFamilyLabellings_weight_sum (cutoff n : Nat) :
    ∀ supports : List (List Nat),
      listQSum
          (parametricKPhysicalTermProduct anchorCoupling cutoff n)
          (supportFamilyLabellings cutoff n supports) ≈
        parametricKSupportFamilyActivity cutoff n supports
  | [] => by
      change (1 : Q') + 0 ≈ 1
      exact Q'.eqv_of_eq (Q'.add_zero' 1)
  | support :: supports => by
      unfold supportFamilyLabellings
      rw [listQSum_map]
      change listQSum
          (fun pair =>
            parametricKPhysicalTerm anchorCoupling cutoff n pair.1 *
              parametricKPhysicalTermProduct anchorCoupling cutoff n pair.2)
          (cartesian (physicalLabellingsWithSupport cutoff n support)
            (supportFamilyLabellings cutoff n supports)) ≈
        parametricKSupportFamilyActivity cutoff n
          (support :: supports)
      refine Q'.eqv_trans _ _ _
        (listQSum_cartesian_product
          (parametricKPhysicalTerm anchorCoupling cutoff n)
          (parametricKPhysicalTermProduct anchorCoupling cutoff n)
          (physicalLabellingsWithSupport cutoff n support)
          (supportFamilyLabellings cutoff n supports)) ?_
      unfold parametricKSupportFamilyActivity parametricKSupportActivity
      exact Q'.mul_eqv_congr_left _ _ _
        (supportFamilyLabellings_weight_sum cutoff n supports)

/-! ## 2. Component restriction lands in the aligned Cartesian list -/

theorem excitedDecoratedComponent_eq_canonicalFaceSupport
    {n : Nat} {physical : EdgeLabelling} {component : List Nat}
    (hcomponent : component ∈ surfaceComponents n physical) :
    excitedPlaquetteIds n
        (decoratedComponentLabel physical component) =
      canonicalFaceSupport n component := by
  apply sublists_eq_of_mem_iff (physicalFaceEdges n)
    (excitedPlaquetteIds n
      (decoratedComponentLabel physical component))
    (canonicalFaceSupport n component)
    (physicalFaceEdges_nodup n)
  · unfold excitedPlaquetteIds
    exact filter_mem_sublists _ _
  · exact canonicalFaceSupport_mem_cutoffOneFaceSupports n component
  · intro edge
    rw [mem_excitedPlaquetteIds_decoratedComponentLabel_iff
      hcomponent edge]
    exact (mem_canonicalFaceSupport_iff
      (surfaceComponent_subset_physicalFaceEdges hcomponent) edge).symm

private theorem mappedDecoratedComponents_matched
    {cutoff n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount n))) :
    ∀ components : List (List Nat),
      (∀ component, component ∈ components →
        component ∈ surfaceComponents n physical) →
      SupportMatched cutoff n
        (components.map (canonicalFaceSupport n))
        (components.map (decoratedComponentLabel physical))
  | [], _ => SupportMatched.nil
  | component :: components, hall => by
      apply SupportMatched.cons
      · apply mem_physicalLabellingsWithSupport_iff.mpr
        exact ⟨decoratedComponentLabel_mem_bounded hphysical
            (hall component List.mem_cons_self),
          excitedDecoratedComponent_eq_canonicalFaceSupport
            (hall component List.mem_cons_self)⟩
      · exact mappedDecoratedComponents_matched hphysical components
          (fun item hitem =>
            hall item (List.mem_cons_of_mem component hitem))

theorem decoratedSurfaceComponentLabels_matched
    {cutoff n : Nat} {support : List Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈
      physicalLabellingsWithSupport cutoff n support) :
    SupportMatched cutoff n (canonicalSurfaceFamily n support)
      (decoratedSurfaceComponentLabels n physical) := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp hphysical
  have hsupportMem : support ∈ cutoffOneFaceSupports n := by
    rw [← hparts.2]
    exact excitedPlaquetteIds_mem_cutoffOneFaceSupports n physical
  have hcomponents :
      surfaceComponents n physical =
        surfaceComponents n (componentLabel support) := by
    unfold surfaceComponents
    rw [hparts.2,
      excitedPlaquetteIds_componentLabel_eq_support hsupportMem]
  unfold canonicalSurfaceFamily decoratedSurfaceComponentLabels
  rw [← hcomponents]
  exact mappedDecoratedComponents_matched hparts.1
    (surfaceComponents n physical)
    (fun component hcomponent => hcomponent)

theorem decoratedSurfaceComponentLabels_mem_familyLabellings
    {cutoff n : Nat} {support : List Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈
      physicalLabellingsWithSupport cutoff n support) :
    decoratedSurfaceComponentLabels n physical ∈
      supportFamilyLabellings cutoff n
        (canonicalSurfaceFamily n support) :=
  (mem_supportFamilyLabellings_iff cutoff n _ _).2
    (decoratedSurfaceComponentLabels_matched hphysical)

/-! ## 3. Decidable finite codes for physical function labellings -/

def fullPhysicalSpinCode (n : Nat) (label : EdgeLabelling) : List Nat :=
  (physicalFaceEdges n).map label

def supportFamilySpinCode (n : Nat)
    (labels : List EdgeLabelling) : List (List Nat) :=
  labels.map (fullPhysicalSpinCode n)

private theorem map_values_eq_of_mem {A B : Type}
    (left right : A → B) : ∀ {xs : List A},
    xs.map left = xs.map right →
      ∀ {item}, item ∈ xs → left item = right item
  | [], _, _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, heq, item, hmem => by
      injection heq with hhead htail
      rcases List.mem_cons.mp hmem with hitem | hrest
      · subst item
        exact hhead
      · exact map_values_eq_of_mem left right htail hrest

theorem fullPhysicalSpinCode_injective_on_bounded
    {cutoff n : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount n)))
    (hright : right ∈ boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount n)))
    (hcode : fullPhysicalSpinCode n left =
      fullPhysicalSpinCode n right) :
    left = right := by
  have hleftSound := boundedEdgeLabellings_sound cutoff
    (List.range (plaquetteEdgeCount n)) left hleft
  have hrightSound := boundedEdgeLabellings_sound cutoff
    (List.range (plaquetteEdgeCount n)) right hright
  funext edge
  by_cases hedge : edge ∈ physicalFaceEdges n
  · exact map_values_eq_of_mem left right hcode hedge
  · exact (hleftSound.2 edge (by
        simpa [physicalFaceEdges] using hedge)).trans
      (hrightSound.2 edge (by
        simpa [physicalFaceEdges] using hedge)).symm

theorem supportFamilySpinCode_injective_on_kPhysical
    {cutoff n : Nat} : ∀ {left right : List EdgeLabelling},
    KPhysicalFamily cutoff n left →
      KPhysicalFamily cutoff n right →
      supportFamilySpinCode n left = supportFamilySpinCode n right →
      left = right
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hcode => by cases hcode
  | _ :: _, [], _, _, hcode => by cases hcode
  | leftHead :: leftTail, rightHead :: rightTail,
      hleft, hright, hcode => by
      unfold supportFamilySpinCode at hcode
      injection hcode with hheadCode htailCode
      have hhead : leftHead = rightHead :=
        fullPhysicalSpinCode_injective_on_bounded
          (hleft leftHead List.mem_cons_self)
          (hright rightHead List.mem_cons_self) hheadCode
      have htail : leftTail = rightTail :=
        supportFamilySpinCode_injective_on_kPhysical
          (fun label hlabel =>
            hleft label (List.mem_cons_of_mem leftHead hlabel))
          (fun label hlabel =>
            hright label (List.mem_cons_of_mem rightHead hlabel))
          htailCode
      rw [hhead, htail]

def codedSupportFamilyLabellings (cutoff n : Nat)
    (supports : List (List Nat)) :
    List (List (List Nat) × Q') :=
  (supportFamilyLabellings cutoff n supports).map
    (fun labels =>
      (supportFamilySpinCode n labels,
        parametricKPhysicalTermProduct anchorCoupling cutoff n labels))

theorem codedSupportFamilyLabellings_nodup
    (cutoff n : Nat) (supports : List (List Nat)) :
    (codedSupportFamilyLabellings cutoff n supports).Nodup := by
  unfold codedSupportFamilyLabellings
  apply nodup_map_of_injOn
  · exact supportFamilyLabellings_nodup cutoff n supports
  · intro left hleft right hright heq
    apply supportFamilySpinCode_injective_on_kPhysical
      (supportMatched_kPhysicalFamily
        ((mem_supportFamilyLabellings_iff cutoff n supports left).1 hleft))
      (supportMatched_kPhysicalFamily
        ((mem_supportFamilyLabellings_iff cutoff n supports right).1 hright))
    exact congrArg Prod.fst heq

/-! ## 4. Full-support activity injects into componentwise activity -/

theorem parametricKSupportActivity_le_componentFamilyActivity
    (cutoff n : Nat) (support : List Nat) :
    parametricKSupportActivity cutoff n support ≤
      parametricKSupportFamilyActivity cutoff n
        (canonicalSurfaceFamily n support) := by
  let source := physicalLabellingsWithSupport cutoff n support
  let families := supportFamilyLabellings cutoff n
    (canonicalSurfaceFamily n support)
  let target := codedSupportFamilyLabellings cutoff n
    (canonicalSurfaceFamily n support)
  let encodeFamily : EdgeLabelling → List EdgeLabelling :=
    fun physical => decoratedSurfaceComponentLabels n physical
  let encode : EdgeLabelling → List (List Nat) × Q' :=
    fun physical =>
      (supportFamilySpinCode n (encodeFamily physical),
        parametricKPhysicalTermProduct anchorCoupling cutoff n
          (encodeFamily physical))
  have hinjection :
      listQSum (parametricKPhysicalTerm anchorCoupling cutoff n) source ≤
        listQSum Prod.snd target := by
    apply listQSum_le_of_injective source target
      (parametricKPhysicalTerm anchorCoupling cutoff n)
      Prod.snd encode
    · exact physicalLabellingsWithSupport_nodup cutoff n support
    · intro physical hphysical
      unfold target codedSupportFamilyLabellings
      apply List.mem_map.mpr
      exact ⟨encodeFamily physical,
        decoratedSurfaceComponentLabels_mem_familyLabellings hphysical,
        rfl⟩
    · intro left hleft right hright heq
      have hleftParts :=
        mem_physicalLabellingsWithSupport_iff.mp hleft
      have hrightParts :=
        mem_physicalLabellingsWithSupport_iff.mp hright
      apply decoratedSurfaceComponentLabels_injective_on_bounded
        hleftParts.1 hrightParts.1
      apply supportFamilySpinCode_injective_on_kPhysical
        (decoratedSurfaceComponentLabels_kPhysicalFamily
          cutoff n left hleftParts.1)
        (decoratedSurfaceComponentLabels_kPhysicalFamily
          cutoff n right hrightParts.1)
      exact congrArg Prod.fst heq
    · intro physical hphysical
      have hparts := mem_physicalLabellingsWithSupport_iff.mp hphysical
      exact Q'.le_of_eqv
        (parametricKPhysicalTerm_surfaceComponent_factor hparts.1)
    · intro coded hcoded
      unfold target codedSupportFamilyLabellings at hcoded
      obtain ⟨family, _, heq⟩ := List.mem_map.mp hcoded
      rw [← heq]
      exact parametricKPhysicalTermProduct_nonnegative cutoff n family
  have htarget : listQSum Prod.snd target ≈
      listQSum
        (parametricKPhysicalTermProduct anchorCoupling cutoff n)
        families := by
    unfold target codedSupportFamilyLabellings families
    rw [listQSum_map]
    change listQSum
        (parametricKPhysicalTermProduct anchorCoupling cutoff n)
        (supportFamilyLabellings cutoff n
          (canonicalSurfaceFamily n support)) ≈
      listQSum
        (parametricKPhysicalTermProduct anchorCoupling cutoff n)
        (supportFamilyLabellings cutoff n
          (canonicalSurfaceFamily n support))
    exact Q'.eqv_refl _
  unfold parametricKSupportActivity
  exact Q'.le_trans' _ _ _ hinjection
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv htarget)
      (Q'.le_of_eqv
        (supportFamilyLabellings_weight_sum cutoff n
          (canonicalSurfaceFamily n support))))

end YMGap.Continuum.Z4SpinSummedSupportComponentUpper

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedSupportComponentUpper.supportFamilyLabellings_nodup
#print axioms YMGap.Continuum.Z4SpinSummedSupportComponentUpper.decoratedSurfaceComponentLabels_matched
#print axioms YMGap.Continuum.Z4SpinSummedSupportComponentUpper.codedSupportFamilyLabellings_nodup
#print axioms YMGap.Continuum.Z4SpinSummedSupportComponentUpper.parametricKSupportActivity_le_componentFamilyActivity
