/-
# Cutoff-four link multiplicities are localized to parity excitations

For a target in the exact cutoff-one-to-cutoff-four lowering row, compare its
corrected-slab link product with the source's geometric parity ground state.
A link factor is unchanged unless one of its incident faces is excited.  The
changed links inject into the four-edge boundaries of the excited faces, so
there are at most four changed factors per excited face.  Each local factor
is bounded by the explicit cutoff-four cubic cardinality envelope.

This is the link half of the ground-relative Gibbs comparison.  It is an
exact finite-volume statement and does not sum targets or assert a posterior,
spectral, thermodynamic, continuum, or mass-gap estimate.

Constructive contract: finite lists, decidable incidence, natural arithmetic,
and the production SU(2) multiplicity bound only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceParityExcitationTiltBound
import YMGap.Continuum.Z4ExplicitSupportMultiplicityBound

namespace YMGap.Continuum.Z4DyadicBinarySourceParityExcitationLinkBound

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationSplit
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationTiltBound
open YMGap.Continuum.Z4DyadicBinarySourceParityGroundState
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4ExplicitSupportMultiplicityBound
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4UnitCubeEnumerationParity

/-! ## 1. Exact excitation support on the corrected slab -/

/-- A face differs from a supplied ground labelling. -/
def slabGroundExcitedFaceB
    (groundState targetState : EdgeLabelling) (faceId : Nat) : Bool :=
  decide (targetState faceId ≠ groundState faceId)

/-- Physical corrected-slab faces on which the target differs from ground. -/
def slabGroundExcitedFaces
    (extent : Nat) (groundState targetState : EdgeLabelling) : List Nat :=
  (slabPhysicalFaceEdges extent).filter
    (slabGroundExcitedFaceB groundState targetState)

/-- Four-edge boundary list of all excited physical faces.  Duplicates are
retained here because only an upper bound on its length is needed. -/
def slabGroundExcitedBoundaryLinks
    (extent : Nat) (groundState targetState : EdgeLabelling) : List Z4Link :=
  (slabGroundExcitedFaces extent groundState targetState).flatMap
    (fun faceId => edgesOf (slabPlaquetteAt extent faceId))

/-- Complete corrected-slab links incident to at least one excited face. -/
def slabGroundTouchedLinks
    (extent : Nat) (groundState targetState : EdgeLabelling) : List Z4Link :=
  (boundaryCompleteSlabLinks extent).filter fun link =>
    (slabIncidentPlaqIds extent link).any
      (slabGroundExcitedFaceB groundState targetState)

private theorem slabGroundTouchedLink_mem_excitedBoundary
    {extent : Nat} {groundState targetState : EdgeLabelling} {link : Z4Link}
    (htouched : link ∈
      slabGroundTouchedLinks extent groundState targetState) :
    link ∈ slabGroundExcitedBoundaryLinks extent groundState targetState := by
  have hany : (slabIncidentPlaqIds extent link).any
      (slabGroundExcitedFaceB groundState targetState) = true :=
    (List.mem_filter.mp htouched).2
  obtain ⟨faceId, hfaceIncident, hexcited⟩ := List.any_eq_true.mp hany
  obtain ⟨plaquette, hindexed, hedge⟩ :=
    mem_slabIncidentPlaqIds.mp hfaceIncident
  have hphysical := slabIncidentPlaqId_physical hfaceIncident
  have hlookup : slabPlaquetteAt extent faceId = plaquette := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem fallbackPlaquette hindexed
  unfold slabGroundExcitedBoundaryLinks
  rw [List.mem_flatMap]
  refine ⟨faceId, ?_, ?_⟩
  . exact List.mem_filter.mpr ⟨hphysical, hexcited⟩
  . simpa only [hlookup] using hedge

theorem slabGroundExcitedBoundaryLinks_length
    (extent : Nat) (groundState targetState : EdgeLabelling) :
    (slabGroundExcitedBoundaryLinks extent groundState targetState).length =
      (slabGroundExcitedFaces extent groundState targetState).length * 4 := by
  unfold slabGroundExcitedBoundaryLinks
  apply length_flatMap_fixed
  intro faceId
  rfl

theorem slabGroundTouchedLinks_nodup
    (extent : Nat) (groundState targetState : EdgeLabelling) :
    (slabGroundTouchedLinks extent groundState targetState).Nodup := by
  unfold slabGroundTouchedLinks
  exact List.filter_sublist.nodup
    (boundaryCompleteSlabLinks_nodup extent)

/-- At most four corrected-slab link factors can change per excited face. -/
theorem slabGroundTouchedLinks_length_le
    (extent : Nat) (groundState targetState : EdgeLabelling) :
    (slabGroundTouchedLinks extent groundState targetState).length ≤
      (slabGroundExcitedFaces extent groundState targetState).length * 4 := by
  have hsubset : ∀ link,
      link ∈ slabGroundTouchedLinks extent groundState targetState →
        link ∈ slabGroundExcitedBoundaryLinks extent groundState targetState := by
    intro link hlink
    exact slabGroundTouchedLink_mem_excitedBoundary hlink
  have hlength :=
    Z4UnitCubeEnumerationParity.nodup_subset_length_le
    (slabGroundTouchedLinks extent groundState targetState)
    (slabGroundExcitedBoundaryLinks extent groundState targetState)
    (slabGroundTouchedLinks_nodup extent groundState targetState)
    hsubset
  rw [slabGroundExcitedBoundaryLinks_length] at hlength
  exact hlength

/-! ## 2. Excited-face count is paid by additive excitation mass -/

private theorem filter_length_le_listNatWeight_of_selected_one_le
    {A : Type} (selected : A → Bool) (weight : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → selected item = true → 1 ≤ weight item) →
      (items.filter selected).length ≤ listNatWeight weight items
  | [], _ => by simp [listNatWeight]
  | head :: tail, hweight => by
      have htail := filter_length_le_listNatWeight_of_selected_one_le
        selected weight tail
        (fun item hitem => hweight item (List.mem_cons_of_mem head hitem))
      cases hselected : selected head
      . simp only [List.filter_cons, hselected, Bool.false_eq_true,
          if_false, listNatWeight]
        omega
      . have hhead := hweight head List.mem_cons_self hselected
        simp only [List.filter_cons, hselected, ↓reduceIte,
          List.length_cons, listNatWeight]
        omega

/-- Every face different from parity ground contributes at least one unit to
the additive two-spin excitation coordinate. -/
theorem slabGroundExcitedFaces_length_le_excitationMassOn
    (sourceState groundState targetState : EdgeLabelling) (faces : List Nat)
    (hground : ∀ faceId, faceId ∈ faces →
      groundState faceId = sourceState faceId % 2)
    (hsource : ∀ faceId, faceId ∈ faces → sourceState faceId ≤ 4)
    (htarget : ∀ faceId, faceId ∈ faces → targetState faceId ≤ 4)
    (hlowering : ∀ faceId, faceId ∈ faces →
      targetState faceId ≤ sourceState faceId /\
        targetState faceId % 2 = sourceState faceId % 2) :
    (faces.filter (slabGroundExcitedFaceB groundState targetState)).length ≤
      spinFourParityExcitationMassOn sourceState targetState faces := by
  unfold spinFourParityExcitationMassOn
  apply filter_length_le_listNatWeight_of_selected_one_le
  intro faceId hface hexcited
  have hne : targetState faceId ≠ groundState faceId :=
    of_decide_eq_true hexcited
  have hneParity : targetState faceId ≠ sourceState faceId % 2 := by
    intro heq
    apply hne
    rw [hground faceId hface]
    exact heq
  exact (spinFourParityExcitationLevel_pos_iff_ne_ground
    (hsource faceId hface) (htarget faceId hface)
    (hlowering faceId hface)).mpr hneParity

/-! ## 3. Local multiplicity comparison and product localization -/

/-- The corrected-slab local multiplicity obeys the production cubic
cardinality envelope because no lattice link has more than six incident
plaquettes. -/
theorem slabExplicitLinkMultiplicity_le_localMultiplicityNatBound
    (K extent : Nat) (physical : EdgeLabelling) (link : Z4Link) :
    slabExplicitLinkMultiplicity K extent physical link ≤
      localMultiplicityNatBound (linkAuxiliaryCutoff K) := by
  unfold slabExplicitLinkMultiplicity
  exact explicitValenceMultiplicity_le_cubic _
    (by simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six extent link)

/-- Away from an excited incident face, the target and ground local spin
lists, hence their exact production multiplicities, are identical. -/
theorem slabExplicitLinkMultiplicity_eq_ground_of_not_touched
    (K extent : Nat) (groundState targetState : EdgeLabelling)
    (link : Z4Link) (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (huntouched : link ∉
      slabGroundTouchedLinks extent groundState targetState) :
    slabExplicitLinkMultiplicity K extent targetState link =
      slabExplicitLinkMultiplicity K extent groundState link := by
  have htest : (slabIncidentPlaqIds extent link).any
      (slabGroundExcitedFaceB groundState targetState) = false := by
    cases hvalue : (slabIncidentPlaqIds extent link).any
        (slabGroundExcitedFaceB groundState targetState)
    . rfl
    . exact False.elim (huntouched
        (List.mem_filter.mpr ⟨hlink, hvalue⟩))
  have hspins :
      (slabIncidentPlaqIds extent link).map targetState =
        (slabIncidentPlaqIds extent link).map groundState := by
    apply List.map_congr_left
    intro faceId hface
    have hfaceFalse := List.any_eq_false.mp htest faceId hface
    by_cases heq : targetState faceId = groundState faceId
    . exact heq
    . have hfaceTrue :
          slabGroundExcitedFaceB groundState targetState faceId = true := by
        simp [slabGroundExcitedFaceB, heq]
      exact False.elim (hfaceFalse hfaceTrue)
  change
    explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        ((slabIncidentPlaqIds extent link).map targetState).length
        (externalSpinsOfList
          ((slabIncidentPlaqIds extent link).map targetState)) =
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        ((slabIncidentPlaqIds extent link).map groundState).length
        (externalSpinsOfList
          ((slabIncidentPlaqIds extent link).map groundState))
  exact congrArg
    (fun spins => explicitValenceMultiplicity
      (linkAuxiliaryCutoff K) spins.length (externalSpinsOfList spins))
    hspins

private theorem natListProduct_pos_iff_pointwise
    {A : Type} (value : A → Nat) : ∀ items : List A,
    0 < natListProduct value items ↔
      ∀ item, item ∈ items → 0 < value item
  | [] => by
      constructor
      . intro _ item hitem
        exact False.elim (List.not_mem_nil hitem)
      . intro _
        change 0 < 1
        omega
  | head :: tail => by
      constructor
      . intro hproduct item hitem
        rw [natListProduct] at hproduct
        rcases List.mem_cons.mp hitem with heq | htail
        . subst item
          exact Nat.pos_of_mul_pos_right hproduct
        . exact (natListProduct_pos_iff_pointwise value tail).mp
            (Nat.pos_of_mul_pos_left hproduct) item htail
      . intro hpointwise
        rw [natListProduct]
        exact Nat.mul_pos
          (hpointwise head List.mem_cons_self)
          ((natListProduct_pos_iff_pointwise value tail).mpr
            (fun item hitem =>
              hpointwise item (List.mem_cons_of_mem head hitem)))

private theorem natListProduct_le_selectedPow_mul
    {A : Type} (base : Nat) (selected : A → Bool)
    (left right : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → selected item = false →
      left item = right item) →
    (∀ item, item ∈ items → selected item = true →
      left item ≤ base * right item) →
    natListProduct left items ≤
      base ^ (items.filter selected).length * natListProduct right items
  | [], _, _ => by simp [natListProduct]
  | head :: tail, hoff, hon => by
      have htail := natListProduct_le_selectedPow_mul
        base selected left right tail
        (fun item hitem =>
          hoff item (List.mem_cons_of_mem head hitem))
        (fun item hitem =>
          hon item (List.mem_cons_of_mem head hitem))
      cases hselected : selected head
      . have hhead := hoff head List.mem_cons_self hselected
        simp only [List.filter_cons, hselected, Bool.false_eq_true,
          if_false, natListProduct]
        rw [hhead]
        calc
          right head * natListProduct left tail ≤
              right head *
                (base ^ (List.filter selected tail).length *
                  natListProduct right tail) :=
            Nat.mul_le_mul_left _ htail
          _ = base ^ (List.filter selected tail).length *
              (right head * natListProduct right tail) := by ac_rfl
      . have hhead := hon head List.mem_cons_self hselected
        simp only [List.filter_cons, hselected, natListProduct]
        calc
          left head * natListProduct left tail ≤
              (base * right head) *
                (base ^ (List.filter selected tail).length *
                  natListProduct right tail) :=
            Nat.mul_le_mul hhead htail
          _ = base ^ ((List.filter selected tail).length + 1) *
              (right head * natListProduct right tail) := by
            rw [Nat.pow_succ]
            ac_rfl

/-- A positive ground product absorbs every unchanged factor exactly and one
cubic envelope at each touched link. -/
theorem slabExplicitLinkMultiplicityProduct_le_touchedPow_mul_ground
    (K extent : Nat) (groundState targetState : EdgeLabelling)
    (hgroundPositive : 0 <
      slabExplicitLinkMultiplicityProduct K extent groundState) :
    slabExplicitLinkMultiplicityProduct K extent targetState ≤
      localMultiplicityNatBound (linkAuxiliaryCutoff K) ^
          (slabGroundTouchedLinks extent groundState targetState).length *
        slabExplicitLinkMultiplicityProduct K extent groundState := by
  unfold slabExplicitLinkMultiplicityProduct at hgroundPositive ⊢
  let selected : Z4Link → Bool := fun link =>
    (slabIncidentPlaqIds extent link).any
      (slabGroundExcitedFaceB groundState targetState)
  have hgroundPointwise :=
    (natListProduct_pos_iff_pointwise
      (slabExplicitLinkMultiplicity K extent groundState)
      (boundaryCompleteSlabLinks extent)).mp hgroundPositive
  have hbound := natListProduct_le_selectedPow_mul
    (localMultiplicityNatBound (linkAuxiliaryCutoff K)) selected
    (slabExplicitLinkMultiplicity K extent targetState)
    (slabExplicitLinkMultiplicity K extent groundState)
    (boundaryCompleteSlabLinks extent)
    (fun link hlink hselected =>
      slabExplicitLinkMultiplicity_eq_ground_of_not_touched
        K extent groundState targetState link hlink (by
          intro htouched
          have htrue := (List.mem_filter.mp htouched).2
          change selected link = true at htrue
          rw [hselected] at htrue
          contradiction))
    (fun link hlink _ =>
      Nat.le_trans
        (slabExplicitLinkMultiplicity_le_localMultiplicityNatBound
          K extent targetState link)
        (Nat.le_mul_of_pos_right _ (hgroundPointwise link hlink)))
  simpa only [selected, slabGroundTouchedLinks] using hbound

/-! ## 4. Actual cutoff-one source-row specialization -/

/-- At coarse cutoff four the six-valent auxiliary window is `24`, hence the
production cubic envelope is exactly `25^3 = 15625`. -/
def cutoffFourLocalMultiplicityNatBound : Nat := 15625

theorem localMultiplicityNatBound_linkAuxiliaryCutoff_four :
    localMultiplicityNatBound (linkAuxiliaryCutoff 4) =
      cutoffFourLocalMultiplicityNatBound := by
  decide

private theorem coarseTargetSpin_le_four_local
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    {targetState : EdgeLabelling}
    (htarget : targetState ∈ S.coarse.physicalLabellings)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    targetState faceId ≤ 4 := by
  have hsound := boundedEdgeLabellings_sound
    S.coarse.cutoff S.coarse.faceEdges targetState htarget
  have hbound := Nat.le_of_lt_succ (hsound.1 faceId hface)
  rw [S.coarse_cutoff, hfineCutoff] at hbound
  omega

/-- In every actual positive lowering row, the number of changed link
factors is at most four times the additive parity-excitation mass. -/
theorem positivePhysicalSourceTouchedLinks_length_le_four_mul_activity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) (targetState : EdgeLabelling)
    (htarget : targetState ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1)) :
    (slabGroundTouchedLinks S.coarse.extent
        (cutoffOneCoarseParityState S source.1) targetState).length ≤
      4 * positivePhysicalSourceParityExcitationActivity
        S source targetState := by
  have hparts := (mem_spinFourLoweringTargets_iff S _ _).mp htarget
  have hfaces :
      (slabGroundExcitedFaces S.coarse.extent
        (cutoffOneCoarseParityState S source.1) targetState).length ≤
      positivePhysicalSourceParityExcitationActivity
        S source targetState := by
    unfold slabGroundExcitedFaces
      positivePhysicalSourceParityExcitationActivity
    simpa only [SlabPhysicalData.faceEdges] using
      (slabGroundExcitedFaces_length_le_excitationMassOn
        (wholeSlabFinePacketTotalLabelling S source.1)
        (cutoffOneCoarseParityState S source.1) targetState
        S.coarse.faceEdges
        (fun faceId hface =>
          cutoffOneCoarseParityState_face_eq_total_mod_two
            S hfineCutoff source.2.1 hface)
        (fun faceId hface =>
          wholeSlabFinePacketTotalLabelling_le_four
            S hfineCutoff source.2.1 faceId hface)
        (fun faceId hface =>
          coarseTargetSpin_le_four_local
            S hfineCutoff hparts.1 faceId hface)
        hparts.2)
  have htouched := slabGroundTouchedLinks_length_le
    S.coarse.extent (cutoffOneCoarseParityState S source.1) targetState
  omega

/-- The complete target link multiplicity product is bounded by the parity
ground product times one explicit `15625^4` allowance per two-spin
excitation.  The exponent, not the ambient slab volume, controls the loss. -/
theorem positivePhysicalSourceLoweringLinkProduct_le_ground_mul_activityPow
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) (targetState : EdgeLabelling)
    (htarget : targetState ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1)) :
    slabExplicitLinkMultiplicityProduct
        S.coarse.cutoff S.coarse.extent targetState ≤
      cutoffFourLocalMultiplicityNatBound ^
          (4 * positivePhysicalSourceParityExcitationActivity
            S source targetState) *
        slabExplicitLinkMultiplicityProduct
          S.coarse.cutoff S.coarse.extent
          (cutoffOneCoarseParityState S source.1) := by
  have heven :=
    positiveCutoffOnePhysicalTerm_fineOddSupport_even
      hfineCutoff source.2.1 source.2.2
  have hgroundPositive :=
    cutoffOneCoarseParityState_linkProduct_pos
      hfineCutoff heven
  have hcomparison :=
    slabExplicitLinkMultiplicityProduct_le_touchedPow_mul_ground
      S.coarse.cutoff S.coarse.extent
      (cutoffOneCoarseParityState S source.1) targetState
      hgroundPositive
  have hbase :
      localMultiplicityNatBound (linkAuxiliaryCutoff S.coarse.cutoff) =
        cutoffFourLocalMultiplicityNatBound := by
    rw [S.coarse_cutoff, hfineCutoff]
    exact localMultiplicityNatBound_linkAuxiliaryCutoff_four
  rw [hbase] at hcomparison
  have hcount :=
    positivePhysicalSourceTouchedLinks_length_le_four_mul_activity
      S hfineCutoff source targetState htarget
  have hpower :
      cutoffFourLocalMultiplicityNatBound ^
          (slabGroundTouchedLinks S.coarse.extent
            (cutoffOneCoarseParityState S source.1) targetState).length ≤
        cutoffFourLocalMultiplicityNatBound ^
          (4 * positivePhysicalSourceParityExcitationActivity
            S source targetState) :=
    Nat.pow_le_pow_right (by decide) hcount
  have hscaled := Nat.mul_le_mul_right
    (slabExplicitLinkMultiplicityProduct
      S.coarse.cutoff S.coarse.extent
      (cutoffOneCoarseParityState S source.1)) hpower
  exact Nat.le_trans hcomparison hscaled

#print axioms slabGroundExcitedFaceB
#print axioms slabGroundExcitedFaces
#print axioms slabGroundExcitedBoundaryLinks
#print axioms slabGroundTouchedLinks
#print axioms slabGroundExcitedBoundaryLinks_length
#print axioms slabGroundTouchedLinks_nodup
#print axioms slabGroundTouchedLinks_length_le
#print axioms slabGroundExcitedFaces_length_le_excitationMassOn
#print axioms slabExplicitLinkMultiplicity_le_localMultiplicityNatBound
#print axioms slabExplicitLinkMultiplicity_eq_ground_of_not_touched
#print axioms slabExplicitLinkMultiplicityProduct_le_touchedPow_mul_ground
#print axioms cutoffFourLocalMultiplicityNatBound
#print axioms localMultiplicityNatBound_linkAuxiliaryCutoff_four
#print axioms positivePhysicalSourceTouchedLinks_length_le_four_mul_activity
#print axioms positivePhysicalSourceLoweringLinkProduct_le_ground_mul_activityPow

end YMGap.Continuum.Z4DyadicBinarySourceParityExcitationLinkBound
