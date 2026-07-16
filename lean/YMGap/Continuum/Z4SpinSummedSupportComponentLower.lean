/-
# Componentwise recombination of spin-summed support activity

The companion upper-factorization module restricts a full physical labelling
to its canonical connected support components.  Here we construct the inverse
map: an aligned family of independently spin-decorated, link-separated
components is recombined by pointwise addition.  Exact support matching makes
the recombination physical at the same cutoff, and disjointness makes it
injective.  A finite weighted injection then gives the reverse activity bound.
-/

import YMGap.Continuum.Z4SpinSummedSupportComponentUpper

namespace YMGap.Continuum.Z4SpinSummedSupportComponentLower

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact support semantics for aligned component families -/

theorem physicalLabel_one_le_iff_mem_support
    {cutoff n : Nat} {support : List Nat} {label : EdgeLabelling}
    (hlabel : label ∈ physicalLabellingsWithSupport cutoff n support)
    (edge : Nat) :
    1 ≤ label edge ↔ edge ∈ support := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp hlabel
  have hsound := boundedEdgeLabellings_sound cutoff
    (List.range (plaquetteEdgeCount n)) label hparts.1
  constructor
  · intro hpositive
    by_cases hphysical : edge ∈ physicalFaceEdges n
    · have hexcited : edge ∈ excitedPlaquetteIds n label := by
        unfold excitedPlaquetteIds
        apply List.mem_filter.mpr
        exact ⟨hphysical, by
          simpa only [decide_eq_true_eq] using hpositive⟩
      rw [hparts.2] at hexcited
      exact hexcited
    · have hzero : label edge = 0 :=
        hsound.2 edge (by
          simpa [physicalFaceEdges] using hphysical)
      rw [hzero] at hpositive
      omega
  · intro hmem
    have hexcited : edge ∈ excitedPlaquetteIds n label := by
      rw [hparts.2]
      exact hmem
    have htest := (List.mem_filter.mp hexcited).2
    simpa only [decide_eq_true_eq] using htest

theorem physicalLabel_eq_zero_of_not_mem_support
    {cutoff n : Nat} {support : List Nat} {label : EdgeLabelling}
    (hlabel : label ∈ physicalLabellingsWithSupport cutoff n support)
    {edge : Nat} (hnot : edge ∉ support) :
    label edge = 0 := by
  have hnotPositive : ¬ 1 ≤ label edge := fun hpositive =>
    hnot ((physicalLabel_one_le_iff_mem_support hlabel edge).mp hpositive)
  omega

theorem supportMatched_union_one_le_iff
    {cutoff n edge : Nat} :
    ∀ {supports : List (List Nat)} {labels : List EdgeLabelling},
      SupportMatched cutoff n supports labels →
      (1 ≤ binaryUnionLabels labels edge ↔
        ∃ support, support ∈ supports ∧ edge ∈ support)
  | _, _, SupportMatched.nil => by
      simp [binaryUnionLabels, zeroEdgeLabelling]
  | support :: supports, label :: labels,
      SupportMatched.cons hlabel htail => by
      constructor
      · intro hpositive
        by_cases hheadPositive : 1 ≤ label edge
        · exact ⟨support, List.mem_cons_self,
            (physicalLabel_one_le_iff_mem_support hlabel edge).mp
              hheadPositive⟩
        · have htailPositive : 1 ≤ binaryUnionLabels labels edge := by
            change 1 ≤ label edge + binaryUnionLabels labels edge at hpositive
            omega
          obtain ⟨found, hfound, hedge⟩ :=
            (supportMatched_union_one_le_iff htail).mp htailPositive
          exact ⟨found, List.mem_cons_of_mem support hfound, hedge⟩
      · rintro ⟨found, hfound, hedge⟩
        rcases List.mem_cons.mp hfound with heq | htailMem
        · subst found
          have hheadPositive : 1 ≤ label edge :=
            (physicalLabel_one_le_iff_mem_support hlabel edge).mpr hedge
          change 1 ≤ label edge + binaryUnionLabels labels edge
          omega
        · have htailPositive : 1 ≤ binaryUnionLabels labels edge :=
            (supportMatched_union_one_le_iff htail).mpr
              ⟨found, htailMem, hedge⟩
          change 1 ≤ label edge + binaryUnionLabels labels edge
          omega

theorem supportMatched_union_eq_zero_of_avoids
    {cutoff n edge : Nat} {supports : List (List Nat)}
    {labels : List EdgeLabelling}
    (hmatched : SupportMatched cutoff n supports labels)
    (havoids : ∀ support, support ∈ supports → edge ∉ support) :
    binaryUnionLabels labels edge = 0 := by
  have hnotPositive : ¬ 1 ≤ binaryUnionLabels labels edge := by
    intro hpositive
    obtain ⟨support, hsupport, hedge⟩ :=
      (supportMatched_union_one_le_iff hmatched).mp hpositive
    exact havoids support hsupport hedge
  omega

private theorem hasExcitedB_exists_local (label : EdgeLabelling) :
    ∀ edges, hasExcitedB label edges = true →
      ∃ edge, edge ∈ edges ∧ 1 ≤ label edge
  | [], h => by cases h
  | edge :: rest, h => by
      by_cases hexcited : 1 ≤ label edge
      · exact ⟨edge, List.mem_cons_self, hexcited⟩
      · have hrest : hasExcitedB label rest = true := by
          simpa [hasExcitedB, hexcited] using h
        obtain ⟨found, hmem, hfound⟩ :=
          hasExcitedB_exists_local label rest hrest
        exact ⟨found, List.mem_cons_of_mem edge hmem, hfound⟩

/-! ## 2. Geometry of an arbitrary aligned family -/

theorem supportMatched_linkSeparatedFamily
    {cutoff n : Nat} :
    ∀ {supports : List (List Nat)} {labels : List EdgeLabelling},
      SupportMatched cutoff n supports labels →
      supports.Nodup →
      DistinctDisjoint supports →
      DistinctSeparated (faceLinkAdjacentB n) supports →
      LinkSeparatedFamily n labels
  | [], [], SupportMatched.nil, _, _, _ => trivial
  | support :: supports, label :: labels,
      SupportMatched.cons hlabel htail,
      hnodup, hdisjoint, hseparated => by
      have hparts := List.nodup_cons.mp hnodup
      have hheadDisjoint : ∀ component, component ∈ supports →
          SupportsDisjoint support component := by
        intro component hcomponent
        have hne : support ≠ component := by
          intro heq
          subst component
          exact hparts.1 hcomponent
        exact hdisjoint support List.mem_cons_self component
          (List.mem_cons_of_mem support hcomponent) hne
      have hheadSeparated : ∀ component, component ∈ supports →
          SupportsSeparated (faceLinkAdjacentB n) support component := by
        intro component hcomponent
        have hne : support ≠ component := by
          intro heq
          subst component
          exact hparts.1 hcomponent
        exact hseparated support List.mem_cons_self component
          (List.mem_cons_of_mem support hcomponent) hne
      have htailDisjoint : DistinctDisjoint supports := by
        intro left hleft right hright hne
        exact hdisjoint left (List.mem_cons_of_mem support hleft)
          right (List.mem_cons_of_mem support hright) hne
      have htailSeparated :
          DistinctSeparated (faceLinkAdjacentB n) supports := by
        intro left hleft right hright hne
        exact hseparated left (List.mem_cons_of_mem support hleft)
          right (List.mem_cons_of_mem support hright) hne
      have hface : FaceDisjoint n label
          (binaryUnionLabels labels) := by
        intro edge _
        by_cases hedge : edge ∈ support
        · right
          exact supportMatched_union_eq_zero_of_avoids htail
            (fun component hcomponent =>
              hheadDisjoint component hcomponent edge hedge)
        · left
          exact physicalLabel_eq_zero_of_not_mem_support hlabel hedge
      have hlink : LinkSeparated n label
          (binaryUnionLabels labels) := by
        intro indexed hindexed hboth
        have hphysicalLink : indexed.2 ∈ distinctBoxLinks n :=
          enumerate_snd_mem hindexed
        obtain ⟨left, hleftIncident, hleftPositive⟩ :=
          hasExcitedB_exists_local _ _ hboth.1
        obtain ⟨right, hrightIncident, hrightPositive⟩ :=
          hasExcitedB_exists_local _ _ hboth.2
        have hleftSupport : left ∈ support :=
          (physicalLabel_one_le_iff_mem_support hlabel left).mp
            hleftPositive
        obtain ⟨component, hcomponent, hrightSupport⟩ :=
          (supportMatched_union_one_le_iff htail).mp hrightPositive
        have htrue := faceLinkAdjacentB_true_of_link hphysicalLink
          hleftIncident hrightIncident
        have hfalse := hheadSeparated component hcomponent
          left hleftSupport right hrightSupport
        rw [htrue] at hfalse
        cases hfalse
      change FaceDisjoint n label (binaryUnionLabels labels) ∧
        LinkSeparated n label (binaryUnionLabels labels) ∧
          LinkSeparatedFamily n labels
      exact ⟨hface, hlink,
        supportMatched_linkSeparatedFamily htail hparts.2
          htailDisjoint htailSeparated⟩

theorem supportMatched_union_excitedPlaquetteIds_eq
    {cutoff n : Nat} {support : List Nat}
    {supports : List (List Nat)} {labels : List EdgeLabelling}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hmatched : SupportMatched cutoff n supports labels)
    (hcover : Covers support supports) :
    excitedPlaquetteIds n (binaryUnionLabels labels) = support := by
  have hsupport' : support ∈ sublists (physicalFaceEdges n) := hsupport
  apply sublists_eq_of_mem_iff (physicalFaceEdges n)
    (excitedPlaquetteIds n (binaryUnionLabels labels)) support
    (physicalFaceEdges_nodup n)
  · unfold excitedPlaquetteIds
    exact filter_mem_sublists _ _
  · exact hsupport'
  · intro edge
    constructor
    · intro hexcited
      have hpositive : 1 ≤ binaryUnionLabels labels edge := by
        have htest := (List.mem_filter.mp hexcited).2
        simpa only [decide_eq_true_eq] using htest
      exact (hcover edge).mpr
        ((supportMatched_union_one_le_iff hmatched).mp hpositive)
    · intro hedge
      have hexists := (hcover edge).mp hedge
      have hpositive : 1 ≤ binaryUnionLabels labels edge :=
        (supportMatched_union_one_le_iff hmatched).mpr hexists
      unfold excitedPlaquetteIds
      apply List.mem_filter.mpr
      exact ⟨mem_of_mem_sublists (physicalFaceEdges n) support
          hsupport' edge hedge,
        by simpa only [decide_eq_true_eq] using hpositive⟩

theorem canonicalSupportFamily_union_mem
    {cutoff n : Nat} {support : List Nat}
    {labels : List EdgeLabelling}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hmatched : SupportMatched cutoff n
      (canonicalSurfaceFamily n support) labels) :
    binaryUnionLabels labels ∈
      physicalLabellingsWithSupport cutoff n support := by
  have hseparated := supportMatched_linkSeparatedFamily hmatched
    (canonicalSurfaceFamily_nodup n support)
    (canonicalSurfaceFamily_distinctDisjoint n support)
    (canonicalSurfaceFamily_distinctSeparated n support)
  apply mem_physicalLabellingsWithSupport_iff.mpr
  exact ⟨unionLabels_mem_bounded cutoff n labels
      (supportMatched_kPhysicalFamily hmatched) hseparated,
    supportMatched_union_excitedPlaquetteIds_eq hsupport hmatched
      (canonicalSurfaceFamily_covers hsupport)⟩

/-! ## 3. Injectivity of recombination -/

theorem supportMatched_union_injective
    {cutoff n : Nat} :
    ∀ {supports : List (List Nat)}
      {left right : List EdgeLabelling},
      SupportMatched cutoff n supports left →
      SupportMatched cutoff n supports right →
      supports.Nodup →
      DistinctDisjoint supports →
      binaryUnionLabels left = binaryUnionLabels right →
      left = right
  | [], [], [], SupportMatched.nil, SupportMatched.nil, _, _, _ => rfl
  | support :: supports, leftHead :: leftTail, rightHead :: rightTail,
      SupportMatched.cons hleftHead hleftTail,
      SupportMatched.cons hrightHead hrightTail,
      hnodup, hdisjoint, hunion => by
      have hparts := List.nodup_cons.mp hnodup
      have hheadDisjoint : ∀ component, component ∈ supports →
          SupportsDisjoint support component := by
        intro component hcomponent
        have hne : support ≠ component := by
          intro heq
          subst component
          exact hparts.1 hcomponent
        exact hdisjoint support List.mem_cons_self component
          (List.mem_cons_of_mem support hcomponent) hne
      have htailDisjoint : DistinctDisjoint supports := by
        intro left hleft right hright hne
        exact hdisjoint left (List.mem_cons_of_mem support hleft)
          right (List.mem_cons_of_mem support hright) hne
      have hhead : leftHead = rightHead := by
        funext edge
        by_cases hedge : edge ∈ support
        · have hleftZero : binaryUnionLabels leftTail edge = 0 :=
            supportMatched_union_eq_zero_of_avoids hleftTail
              (fun component hcomponent =>
                hheadDisjoint component hcomponent edge hedge)
          have hrightZero : binaryUnionLabels rightTail edge = 0 :=
            supportMatched_union_eq_zero_of_avoids hrightTail
              (fun component hcomponent =>
                hheadDisjoint component hcomponent edge hedge)
          have hpoint := congrFun hunion edge
          simpa [binaryUnionLabels, binaryUnionLabel,
            hleftZero, hrightZero] using hpoint
        · rw [physicalLabel_eq_zero_of_not_mem_support hleftHead hedge,
            physicalLabel_eq_zero_of_not_mem_support hrightHead hedge]
      have htailUnion :
          binaryUnionLabels leftTail = binaryUnionLabels rightTail := by
        funext edge
        have hpoint := congrFun hunion edge
        have hcancel :
            leftHead edge + binaryUnionLabels leftTail edge =
              leftHead edge + binaryUnionLabels rightTail edge := by
          simpa [binaryUnionLabels, binaryUnionLabel, hhead] using hpoint
        exact Nat.add_left_cancel hcancel
      have htail : leftTail = rightTail :=
        supportMatched_union_injective hleftTail hrightTail hparts.2
          htailDisjoint htailUnion
      rw [hhead, htail]

/-! ## 4. Reverse finite weighted injection and exact activity identity -/

def codedPhysicalSupportLabellings (cutoff n : Nat)
    (support : List Nat) : List (List Nat × Q') :=
  (physicalLabellingsWithSupport cutoff n support).map
    (fun physical =>
      (fullPhysicalSpinCode n physical,
        parametricKPhysicalTerm anchorCoupling cutoff n physical))

theorem componentFamilyActivity_le_parametricKSupportActivity
    (cutoff n : Nat) (support : List Nat)
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    parametricKSupportFamilyActivity cutoff n
        (canonicalSurfaceFamily n support) ≤
      parametricKSupportActivity cutoff n support := by
  let source := supportFamilyLabellings cutoff n
    (canonicalSurfaceFamily n support)
  let target := codedPhysicalSupportLabellings cutoff n support
  let recombine : List EdgeLabelling → EdgeLabelling :=
    fun family => binaryUnionLabels family
  let encode : List EdgeLabelling → List Nat × Q' :=
    fun family =>
      (fullPhysicalSpinCode n (recombine family),
        parametricKPhysicalTerm anchorCoupling cutoff n
          (recombine family))
  have hinjection :
      listQSum
          (parametricKPhysicalTermProduct anchorCoupling cutoff n)
          source ≤
        listQSum Prod.snd target := by
    apply listQSum_le_of_injective source target
      (parametricKPhysicalTermProduct anchorCoupling cutoff n)
      Prod.snd encode
    · exact supportFamilyLabellings_nodup cutoff n
        (canonicalSurfaceFamily n support)
    · intro family hfamily
      have hmatched :=
        (mem_supportFamilyLabellings_iff cutoff n
          (canonicalSurfaceFamily n support) family).mp hfamily
      have hphysical := canonicalSupportFamily_union_mem hsupport hmatched
      unfold target codedPhysicalSupportLabellings
      apply List.mem_map.mpr
      exact ⟨recombine family, hphysical, rfl⟩
    · intro left hleft right hright heq
      have hleftMatched :=
        (mem_supportFamilyLabellings_iff cutoff n
          (canonicalSurfaceFamily n support) left).mp hleft
      have hrightMatched :=
        (mem_supportFamilyLabellings_iff cutoff n
          (canonicalSurfaceFamily n support) right).mp hright
      have hleftPhysical :=
        canonicalSupportFamily_union_mem hsupport hleftMatched
      have hrightPhysical :=
        canonicalSupportFamily_union_mem hsupport hrightMatched
      have hunion : recombine left = recombine right :=
        fullPhysicalSpinCode_injective_on_bounded
          (mem_physicalLabellingsWithSupport_iff.mp hleftPhysical).1
          (mem_physicalLabellingsWithSupport_iff.mp hrightPhysical).1
          (congrArg Prod.fst heq)
      exact supportMatched_union_injective
        hleftMatched hrightMatched
        (canonicalSurfaceFamily_nodup n support)
        (canonicalSurfaceFamily_distinctDisjoint n support)
        hunion
    · intro family hfamily
      have hmatched :=
        (mem_supportFamilyLabellings_iff cutoff n
          (canonicalSurfaceFamily n support) family).mp hfamily
      have hseparated := supportMatched_linkSeparatedFamily hmatched
        (canonicalSurfaceFamily_nodup n support)
        (canonicalSurfaceFamily_distinctDisjoint n support)
        (canonicalSurfaceFamily_distinctSeparated n support)
      change parametricKPhysicalTermProduct anchorCoupling cutoff n family ≤
        parametricKPhysicalTerm anchorCoupling cutoff n
          (binaryUnionLabels family)
      exact Q'.ge_of_eqv
        (parametricKPhysicalTerm_unionLabels_factor
          anchorCoupling cutoff n family
          (supportMatched_kPhysicalFamily hmatched) hseparated)
    · intro coded hcoded
      unfold target codedPhysicalSupportLabellings at hcoded
      obtain ⟨physical, _, heq⟩ := List.mem_map.mp hcoded
      rw [← heq]
      exact parametricKPhysicalTerm_nonnegative (by decide)
        cutoff n physical
  have htarget : listQSum Prod.snd target ≈
      parametricKSupportActivity cutoff n support := by
    unfold target codedPhysicalSupportLabellings
    rw [listQSum_map]
    change listQSum
        (parametricKPhysicalTerm anchorCoupling cutoff n)
        (physicalLabellingsWithSupport cutoff n support) ≈
      parametricKSupportActivity cutoff n support
    unfold parametricKSupportActivity
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (supportFamilyLabellings_weight_sum cutoff n
        (canonicalSurfaceFamily n support)))
    (Q'.le_trans' _ _ _ hinjection (Q'.le_of_eqv htarget))

private theorem eqv_of_le_of_ge {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  unfold Q'.eqv
  change a.num * (b.den : Int) ≤ b.num * (a.den : Int) at hab
  change b.num * (a.den : Int) ≤ a.num * (b.den : Int) at hba
  exact Int.le_antisymm hab hba

theorem parametricKSupportActivity_eqv_componentFamilyActivity
    (cutoff n : Nat) (support : List Nat)
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    parametricKSupportActivity cutoff n support ≈
      parametricKSupportFamilyActivity cutoff n
        (canonicalSurfaceFamily n support) :=
  eqv_of_le_of_ge
    (parametricKSupportActivity_le_componentFamilyActivity
      cutoff n support)
    (componentFamilyActivity_le_parametricKSupportActivity
      cutoff n support hsupport)

end YMGap.Continuum.Z4SpinSummedSupportComponentLower

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedSupportComponentLower.physicalLabel_one_le_iff_mem_support
#print axioms YMGap.Continuum.Z4SpinSummedSupportComponentLower.supportMatched_linkSeparatedFamily
#print axioms YMGap.Continuum.Z4SpinSummedSupportComponentLower.canonicalSupportFamily_union_mem
#print axioms YMGap.Continuum.Z4SpinSummedSupportComponentLower.supportMatched_union_injective
#print axioms YMGap.Continuum.Z4SpinSummedSupportComponentLower.componentFamilyActivity_le_parametricKSupportActivity
#print axioms YMGap.Continuum.Z4SpinSummedSupportComponentLower.parametricKSupportActivity_eqv_componentFamilyActivity
