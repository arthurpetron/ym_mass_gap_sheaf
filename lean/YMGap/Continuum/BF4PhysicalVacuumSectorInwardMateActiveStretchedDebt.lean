/-
# Remove the spurious zero-face terms from the inward-mate debt

The first product expansion used the raw stretched continuation at every
cube-boundary link.  The SU(2) ladder classification is sharper: that
continuation is needed only when both incident source face labels are
strictly positive.  If either label is zero, every source channel survives
the inward mate and the source multiplicity injects into the mate count with
no additive term.

This file carries that positivity gate through arbitrary incident order, the
twelve-link product, the Boolean expansion, and the concrete finite witness
carrier.  Thus any actual member of a stretched fiber is rooted at two
positive cube faces; fake debt supported at zero faces has been deleted
before the strand argument begins.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionReordering
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. The exact positivity-gated local debt -/

def activeStretchedContinuation
    (left right continuation : Nat) : Nat :=
  if decide (0 < left ∧ 0 < right) then continuation else 0

private theorem natListSum_map_mono {A : Type}
    (source target : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → source item ≤ target item) →
      natListSum (items.map source) ≤ natListSum (items.map target)
  | [], _ => Nat.le_refl 0
  | head :: tail, hle => by
      simp only [List.map_cons, natListSum]
      exact Nat.add_le_add
        (hle head List.mem_cons_self)
        (natListSum_map_mono source target tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

/-- If one of the changed labels is zero, every source fusion path survives
the even inward mate. -/
theorem fusionPathMultiplicity_evenInwardMate_le_of_not_both_positive
    (cutoff left right : Nat) (rest : List Nat)
    (hinactive : ¬ (0 < left ∧ 0 < right)) :
    fusionPathMultiplicity cutoff (left :: right :: rest) ≤
      fusionPathMultiplicity cutoff
        (evenInwardMateLabel left :: evenInwardMateLabel right :: rest) := by
  rw [fusionPathMultiplicity_cons_cons,
    fusionPathMultiplicity_cons_cons]
  apply natListSum_map_mono
  intro channel _
  cases hsource : fusionOK left right channel with
  | false => simp
  | true =>
      rcases fusionOK_evenInwardMate_or_positive_stretched
          left right channel hsource with htarget | hpositive
      · simp [htarget]
      · exact False.elim
          (hinactive ⟨hpositive.1, hpositive.2.1⟩)

/-- The additive continuation is present exactly on the load-bearing
positive-positive case and vanishes otherwise. -/
theorem fusionPathMultiplicity_evenInwardMate_le_add_activeStretched
    (cutoff left right : Nat) (rest : List Nat)
    (hstretchedCutoff : left + right ≤ cutoff) :
    fusionPathMultiplicity cutoff (left :: right :: rest) ≤
      fusionPathMultiplicity cutoff
          (evenInwardMateLabel left ::
            evenInwardMateLabel right :: rest) +
        activeStretchedContinuation left right
          (fusionPathMultiplicity cutoff ((left + right) :: rest)) := by
  by_cases hactive : 0 < left ∧ 0 < right
  · simpa [activeStretchedContinuation, hactive] using
      fusionPathMultiplicity_evenInwardMate_le_add_stretched
        cutoff left right rest hstretchedCutoff
  · simpa [activeStretchedContinuation, hactive] using
      fusionPathMultiplicity_evenInwardMate_le_of_not_both_positive
        cutoff left right rest hactive

/-! ## 2. Production multiplicities and arbitrary physical order -/

theorem explicitValenceMultiplicity_physical_inwardMate_le_add_activeStretched
    (K left right : Nat) (rest : List Nat)
    (hK : 1 ≤ K)
    (hlength : (left :: right :: rest).length ≤ 6)
    (hbounded : SpinsBounded K (left :: right :: rest)) :
    explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        (left :: right :: rest).length
        (externalSpinsOfList (left :: right :: rest)) ≤
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          (evenInwardMateLabel left ::
            evenInwardMateLabel right :: rest).length
          (externalSpinsOfList
            (evenInwardMateLabel left ::
              evenInwardMateLabel right :: rest)) +
        activeStretchedContinuation left right
          (explicitValenceMultiplicity (linkAuxiliaryCutoff K)
            ((left + right) :: rest).length
            (externalSpinsOfList ((left + right) :: rest))) := by
  have hleftK : left ≤ K := hbounded left (by simp)
  have hrightK : right ≤ K := hbounded right (by simp)
  have hrestK : SpinsBounded K rest := by
    intro spin hspin
    exact hbounded spin (by simp [hspin])
  have hKaux : K ≤ linkAuxiliaryCutoff K :=
    externalCutoff_le_linkAuxiliaryCutoff K
  have hsourceAux : SpinsBounded (linkAuxiliaryCutoff K)
      (left :: right :: rest) := by
    intro spin hspin
    exact Nat.le_trans (hbounded spin hspin) hKaux
  have hmateK : SpinsBounded K
      (evenInwardMateLabel left ::
        evenInwardMateLabel right :: rest) := by
    intro spin hspin
    rcases List.mem_cons.mp hspin with hspin | hspin
    · subst spin
      exact evenInwardMateLabel_le_cutoff hK hleftK
    · rcases List.mem_cons.mp hspin with hspin | hspin
      · subst spin
        exact evenInwardMateLabel_le_cutoff hK hrightK
      · exact hrestK spin hspin
  have hmateAux : SpinsBounded (linkAuxiliaryCutoff K)
      (evenInwardMateLabel left ::
        evenInwardMateLabel right :: rest) := by
    intro spin hspin
    exact Nat.le_trans (hmateK spin hspin) hKaux
  have hstretchedAux : left + right ≤ linkAuxiliaryCutoff K := by
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  have hdebtAux : SpinsBounded (linkAuxiliaryCutoff K)
      ((left + right) :: rest) := by
    intro spin hspin
    rcases List.mem_cons.mp hspin with hspin | hspin
    · subst spin
      exact hstretchedAux
    · exact Nat.le_trans (hrestK spin hspin) hKaux
  have hmateLength :
      (evenInwardMateLabel left ::
        evenInwardMateLabel right :: rest).length ≤ 6 := by
    simpa only [List.length_cons] using hlength
  have hdebtLength : ((left + right) :: rest).length ≤ 6 := by
    simp only [List.length_cons] at hlength ⊢
    omega
  rw [← fusionPathMultiplicity_eq_explicit_of_length_le_six
        (left :: right :: rest) hlength hsourceAux,
    ← fusionPathMultiplicity_eq_explicit_of_length_le_six
        (evenInwardMateLabel left ::
          evenInwardMateLabel right :: rest) hmateLength hmateAux,
    ← fusionPathMultiplicity_eq_explicit_of_length_le_six
        ((left + right) :: rest) hdebtLength hdebtAux]
  exact fusionPathMultiplicity_evenInwardMate_le_add_activeStretched
    (linkAuxiliaryCutoff K) left right rest hstretchedAux

theorem explicitValenceMultiplicity_physical_inwardMate_of_permutations_active
    (K left right : Nat) (rest source mate : List Nat)
    (hK : 1 ≤ K)
    (hlength : (left :: right :: rest).length ≤ 6)
    (hbounded : SpinsBounded K (left :: right :: rest))
    (hsource : source.Perm (left :: right :: rest))
    (hmate : mate.Perm
      (evenInwardMateLabel left ::
        evenInwardMateLabel right :: rest)) :
    explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        source.length (externalSpinsOfList source) ≤
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          mate.length (externalSpinsOfList mate) +
        activeStretchedContinuation left right
          (explicitValenceMultiplicity (linkAuxiliaryCutoff K)
            ((left + right) :: rest).length
            (externalSpinsOfList ((left + right) :: rest))) := by
  have hsourceLength : source.length ≤ 6 := by
    rw [hsource.length_eq]
    exact hlength
  have hsourceBounded : SpinsBounded K source :=
    spinsBounded_of_perm hsource.symm hbounded
  have hleftK : left ≤ K := hbounded left (by simp)
  have hrightK : right ≤ K := hbounded right (by simp)
  have hrestK : SpinsBounded K rest := by
    intro spin hspin
    exact hbounded spin (by simp [hspin])
  have hmateFrontBounded : SpinsBounded K
      (evenInwardMateLabel left ::
        evenInwardMateLabel right :: rest) := by
    intro spin hspin
    rcases List.mem_cons.mp hspin with hspin | hspin
    · subst spin
      exact evenInwardMateLabel_le_cutoff hK hleftK
    · rcases List.mem_cons.mp hspin with hspin | hspin
      · subst spin
        exact evenInwardMateLabel_le_cutoff hK hrightK
      · exact hrestK spin hspin
  have hmateLength : mate.length ≤ 6 := by
    rw [hmate.length_eq]
    simpa only [List.length_cons] using hlength
  have hmateBounded : SpinsBounded K mate :=
    spinsBounded_of_perm hmate.symm hmateFrontBounded
  have hsourceEq := explicitValenceMultiplicity_physical_perm
    hsource hsourceLength hsourceBounded
  have hmateEq := explicitValenceMultiplicity_physical_perm
    hmate hmateLength hmateBounded
  calc
    explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        source.length (externalSpinsOfList source) =
        explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          (left :: right :: rest).length
          (externalSpinsOfList (left :: right :: rest)) := hsourceEq
    _ ≤ explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          (evenInwardMateLabel left ::
            evenInwardMateLabel right :: rest).length
          (externalSpinsOfList
            (evenInwardMateLabel left ::
              evenInwardMateLabel right :: rest)) +
        activeStretchedContinuation left right
          (explicitValenceMultiplicity (linkAuxiliaryCutoff K)
            ((left + right) :: rest).length
            (externalSpinsOfList ((left + right) :: rest))) :=
      explicitValenceMultiplicity_physical_inwardMate_le_add_activeStretched
        K left right rest hK hlength hbounded
    _ = explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          mate.length (externalSpinsOfList mate) +
        activeStretchedContinuation left right
          (explicitValenceMultiplicity (linkAuxiliaryCutoff K)
            ((left + right) :: rest).length
            (externalSpinsOfList ((left + right) :: rest))) := by
      rw [← hmateEq]

/-! ## 3. The sharpened twelve-link product and remainder -/

def cubeInwardMateActiveStretchedDebt
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) : Nat :=
  activeStretchedContinuation
    (physical (centralLowerCubeFaceId linked.1.left))
    (physical (centralLowerCubeFaceId linked.1.right))
    (cubeInwardMateStretchedDebt K physical hK hbounded linked)

theorem cubeInwardMateSourceLinkMultiplicity_le_target_add_activeDebt
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    cubeInwardMateSourceLinkMultiplicity K physical linked ≤
      cubeInwardMateTargetLinkMultiplicity K physical linked +
        cubeInwardMateActiveStretchedDebt
          K physical hK hbounded linked := by
  have hsource :
      ((slabIncidentPlaqIds 1 linked.1.link).map physical).Perm
        (physical (centralLowerCubeFaceId linked.1.left) ::
          physical (centralLowerCubeFaceId linked.1.right) ::
            cubeInwardMateLinkRest K physical hK hbounded linked) :=
    (cubeInwardMateLinkCertificate K physical hK hbounded linked).2.1
  have hmate :
      ((slabIncidentPlaqIds 1 linked.1.link).map
        (centralLowerCubeEvenInwardMatePhysical physical)).Perm
        (evenInwardMateLabel
            (physical (centralLowerCubeFaceId linked.1.left)) ::
          evenInwardMateLabel
              (physical (centralLowerCubeFaceId linked.1.right)) ::
            cubeInwardMateLinkRest K physical hK hbounded linked) :=
    (cubeInwardMateLinkCertificate K physical hK hbounded linked).2.2.1
  have hlength :
      (physical (centralLowerCubeFaceId linked.1.left) ::
        physical (centralLowerCubeFaceId linked.1.right) ::
          cubeInwardMateLinkRest K physical hK hbounded linked).length ≤ 6 := by
    rw [← hsource.length_eq]
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 linked.1.link
  have hsourceBounded : SpinsBounded K
      ((slabIncidentPlaqIds 1 linked.1.link).map physical) :=
    slabIncidentSpins_bounded hbounded linked.1.link
  have hfrontBounded : SpinsBounded K
      (physical (centralLowerCubeFaceId linked.1.left) ::
        physical (centralLowerCubeFaceId linked.1.right) ::
          cubeInwardMateLinkRest K physical hK hbounded linked) :=
    spinsBounded_of_perm hsource hsourceBounded
  unfold cubeInwardMateSourceLinkMultiplicity
    cubeInwardMateTargetLinkMultiplicity
    cubeInwardMateActiveStretchedDebt cubeInwardMateStretchedDebt
    cubeInwardMateLinkRest
  unfold slabExplicitLinkMultiplicity
  exact explicitValenceMultiplicity_physical_inwardMate_of_permutations_active
    K
    (physical (centralLowerCubeFaceId linked.1.left))
    (physical (centralLowerCubeFaceId linked.1.right))
    (cubeInwardMateLinkRest K physical hK hbounded linked)
    ((slabIncidentPlaqIds 1 linked.1.link).map physical)
    ((slabIncidentPlaqIds 1 linked.1.link).map
      (centralLowerCubeEvenInwardMatePhysical physical))
    hK hlength hfrontBounded hsource hmate

def cubeInwardMateTargetPlusActiveDebtBoundaryProduct
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) : Nat :=
  natListProduct
    (fun linked =>
      cubeInwardMateTargetLinkMultiplicity K physical linked +
        cubeInwardMateActiveStretchedDebt K physical hK hbounded linked)
    cubeProductionIncidences.attach

private theorem natListProduct_mono_on
    {A : Type} (left right : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      natListProduct left items ≤ natListProduct right items
  | [], _ => Nat.le_refl 1
  | head :: tail, hle => by
      simp only [natListProduct]
      exact Nat.mul_le_mul
        (hle head List.mem_cons_self)
        (natListProduct_mono_on left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

theorem cubeInwardMateSourceBoundaryProduct_le_targetPlusActiveDebt
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    cubeInwardMateSourceBoundaryProduct K physical ≤
      cubeInwardMateTargetPlusActiveDebtBoundaryProduct
        K physical hK hbounded := by
  apply natListProduct_mono_on
  intro linked _
  exact cubeInwardMateSourceLinkMultiplicity_le_target_add_activeDebt
    K physical hK hbounded linked

def cubeInwardMateNonemptyActiveStretchedRemainder
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) : Nat :=
  nonemptyDebtExpansion
    (cubeInwardMateTargetLinkMultiplicity K physical)
    (cubeInwardMateActiveStretchedDebt K physical hK hbounded)
    cubeProductionIncidences.attach

theorem cubeInwardMateTargetPlusActiveDebtBoundaryProduct_eq_target_add_remainder
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    cubeInwardMateTargetPlusActiveDebtBoundaryProduct
        K physical hK hbounded =
      cubeInwardMateTargetBoundaryProduct K physical +
        cubeInwardMateNonemptyActiveStretchedRemainder
          K physical hK hbounded :=
  product_target_add_debt_eq_target_add_nonemptyExpansion
    (cubeInwardMateTargetLinkMultiplicity K physical)
    (cubeInwardMateActiveStretchedDebt K physical hK hbounded)
    cubeProductionIncidences.attach

theorem cubeInwardMateSourceBoundaryProduct_le_target_add_activeRemainder
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    cubeInwardMateSourceBoundaryProduct K physical ≤
      cubeInwardMateTargetBoundaryProduct K physical +
        cubeInwardMateNonemptyActiveStretchedRemainder
          K physical hK hbounded := by
  rw [← cubeInwardMateTargetPlusActiveDebtBoundaryProduct_eq_target_add_remainder]
  exact cubeInwardMateSourceBoundaryProduct_le_targetPlusActiveDebt
    K physical hK hbounded

/-! ## 4. Delete the inactive witness fibers before rerouting -/

def cubeInwardMateActiveStretchedFusionWitnesses
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) : List EdgeLabelling :=
  if decide
      (0 < physical (centralLowerCubeFaceId linked.1.left) ∧
        0 < physical (centralLowerCubeFaceId linked.1.right)) then
    cubeInwardMateStretchedFusionWitnesses K physical hK hbounded linked
  else []

theorem cubeInwardMateActiveStretchedFusionWitnesses_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    (cubeInwardMateActiveStretchedFusionWitnesses
      K physical hK hbounded linked).length =
      cubeInwardMateActiveStretchedDebt K physical hK hbounded linked := by
  unfold cubeInwardMateActiveStretchedFusionWitnesses
    cubeInwardMateActiveStretchedDebt activeStretchedContinuation
  by_cases hactive :
      0 < physical (centralLowerCubeFaceId linked.1.left) ∧
        0 < physical (centralLowerCubeFaceId linked.1.right)
  · simp only [decide_eq_true hactive, if_true]
    exact cubeInwardMateStretchedFusionWitnesses_length
      K physical hK hbounded linked
  · simp [hactive]

def cubeActiveDebtWordFusionAssignments
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (word : List Bool) : List CubeDebtFusionAssignment :=
  choiceFiberAssignments
    (fun linked => slabLinkFusionWitnesses K 1
      (centralLowerCubeEvenInwardMatePhysical physical) linked.1.link)
    (cubeInwardMateActiveStretchedFusionWitnesses
      K physical hK hbounded)
    cubeProductionIncidences.attach word

theorem cubeActiveDebtWordFusionAssignments_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (word : List Bool) :
    (cubeActiveDebtWordFusionAssignments
      K physical hK hbounded word).length =
      debtChoiceProduct
        (cubeInwardMateTargetLinkMultiplicity K physical)
        (cubeInwardMateActiveStretchedDebt K physical hK hbounded)
        cubeProductionIncidences.attach word := by
  unfold cubeActiveDebtWordFusionAssignments
  rw [choiceFiberAssignments_length]
  have htarget :
      (fun linked : CubeProductionIncidenceMember =>
        (slabLinkFusionWitnesses K 1
          (centralLowerCubeEvenInwardMatePhysical physical)
          linked.1.link).length) =
        cubeInwardMateTargetLinkMultiplicity K physical := by
    funext linked
    exact slabLinkFusionWitnesses_length K 1
      (centralLowerCubeEvenInwardMatePhysical physical) linked.1.link
  have hdebt :
      (fun linked : CubeProductionIncidenceMember =>
        (cubeInwardMateActiveStretchedFusionWitnesses
          K physical hK hbounded linked).length) =
        cubeInwardMateActiveStretchedDebt K physical hK hbounded := by
    funext linked
    exact cubeInwardMateActiveStretchedFusionWitnesses_length
      K physical hK hbounded linked
  rw [htarget, hdebt]

abbrev CubeNonemptyActiveDebtFusionCarrier :=
  CubeNonemptyDebtWord × CubeDebtFusionAssignment

def cubeInwardMateNonemptyActiveDebtFusionCarriers
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List CubeNonemptyActiveDebtFusionCarrier :=
  (nonemptyDebtChoiceWords cubeProductionIncidences.attach).attach.flatMap
    fun word =>
      (cubeActiveDebtWordFusionAssignments
        K physical hK hbounded word.1).map fun assignment =>
          (word, assignment)

private theorem length_flatMap_fiber_maps {A B : Type}
    (fiber : A → List B) : ∀ items : List A,
    (items.flatMap fun item =>
      (fiber item).map fun value => (item, value)).length =
      natListSum (items.map fun item => (fiber item).length)
  | [] => rfl
  | head :: tail => by
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.map_cons, natListSum]
      rw [length_flatMap_fiber_maps fiber tail]

theorem cubeInwardMateNonemptyActiveDebtFusionCarriers_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateNonemptyActiveDebtFusionCarriers
      K physical hK hbounded).length =
      cubeInwardMateNonemptyActiveStretchedRemainder
        K physical hK hbounded := by
  unfold cubeInwardMateNonemptyActiveDebtFusionCarriers
    cubeInwardMateNonemptyActiveStretchedRemainder nonemptyDebtExpansion
  rw [length_flatMap_fiber_maps]
  apply congrArg natListSum
  calc
    (nonemptyDebtChoiceWords cubeProductionIncidences.attach).attach.map
        (fun word =>
          (cubeActiveDebtWordFusionAssignments
            K physical hK hbounded word.1).length) =
        (nonemptyDebtChoiceWords cubeProductionIncidences.attach).attach.map
          (fun word => debtChoiceProduct
            (cubeInwardMateTargetLinkMultiplicity K physical)
            (cubeInwardMateActiveStretchedDebt K physical hK hbounded)
            cubeProductionIncidences.attach word.1) := by
              apply List.map_congr_left
              intro word _
              exact cubeActiveDebtWordFusionAssignments_length
                K physical hK hbounded word.1
    _ = ((nonemptyDebtChoiceWords
          cubeProductionIncidences.attach).attach.map Subtype.val).map
        (debtChoiceProduct
          (cubeInwardMateTargetLinkMultiplicity K physical)
          (cubeInwardMateActiveStretchedDebt K physical hK hbounded)
          cubeProductionIncidences.attach) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro word _
            rfl
    _ = (nonemptyDebtChoiceWords cubeProductionIncidences.attach).map
        (debtChoiceProduct
          (cubeInwardMateTargetLinkMultiplicity K physical)
          (cubeInwardMateActiveStretchedDebt K physical hK hbounded)
          cubeProductionIncidences.attach) := by
            rw [List.attach_map_subtype_val]

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.fusionPathMultiplicity_evenInwardMate_le_add_activeStretched
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.explicitValenceMultiplicity_physical_inwardMate_of_permutations_active
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.cubeInwardMateSourceBoundaryProduct_le_target_add_activeRemainder
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.cubeInwardMateActiveStretchedFusionWitnesses_length
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.cubeInwardMateNonemptyActiveDebtFusionCarriers_length
