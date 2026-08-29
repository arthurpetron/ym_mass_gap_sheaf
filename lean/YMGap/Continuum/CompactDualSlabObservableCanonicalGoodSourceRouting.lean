/-
# Canonical finite routing on every recoupling-good connected source

The connected strand-choice carrier is already filtered twice: every entry
is a successful disconnection channel and has strictly positive exact SU(2)
row weight.  Hence the canonical good-source predicate is simply nonemptiness
of that finite list.

On the attached good subcarrier, constructive head selection gives one
positive channel in every row.  The repository's capped finite positive
minimum supplies the common row floor, while the full good-source list length
supplies a literal (non-uniform) target-fiber congestion bound.  Thus at every
fixed finite datum the routing half of the good-source contraction is
canonical.  The only remaining quantitative finite input is good physical
mass density; a positive-channel witness also constructs its exact
datum-dependent ratio, proving that this compiler is non-vacuous.

The list minimum and list-length congestion are deliberately not called
uniform in cutoff, volume, coupling, or spacing.  Constructive contract:
finite search, attached carriers, exact positive minima, and explicit ratios
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
import YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabRetainedContraction

namespace YMGap.Continuum.CompactDualSlabObservableCanonicalGoodSourceRouting

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
open YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction.SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabRetainedContraction

local infix:50 " ≈ " => Q'.eqv

local instance canonicalGoodPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

/-! ## 1. Executable nonempty-row good predicate -/

/-- A connected source is canonically good exactly when its already-positive
successful strand-choice list is nonempty. -/
def slabObservablePairedConnectedCanonicalGoodB
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) : Bool :=
  !(slabObservablePairedConnectedStrandChoices
    D rootFaceId targetFaceId source).isEmpty

private def listFirstOfNonempty
    {A : Type} (items : List A) (hnonempty : items ≠ []) : A :=
  match items with
  | [] => False.elim (hnonempty rfl)
  | first :: _ => first

private theorem listFirstOfNonempty_mem
    {A : Type} (items : List A) (hnonempty : items ≠ []) :
    listFirstOfNonempty items hnonempty ∈ items := by
  cases items with
  | nil => exact False.elim (hnonempty rfl)
  | cons first rest => exact List.mem_cons_self

theorem canonicalGoodSource_choices_nonempty
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId
        (slabObservablePairedConnectedCanonicalGoodB
          D rootFaceId targetFaceId)) :
    slabObservablePairedConnectedStrandChoices
        D rootFaceId targetFaceId source.toChoiceSource ≠ [] := by
  change slabObservablePairedConnectedStrandChoices
    D rootFaceId targetFaceId source.1 ≠ []
  have hgood := (List.mem_filter.mp source.2).2
  intro hempty
  unfold slabObservablePairedConnectedCanonicalGoodB at hgood
  rw [hempty] at hgood
  exact (by decide : (false : Bool) ≠ true) hgood

/-- Constructively select the first already-positive successful channel. -/
def canonicalGoodSourceChoice
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId
        (slabObservablePairedConnectedCanonicalGoodB
          D rootFaceId targetFaceId)) :
    SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source.toChoiceSource :=
  listFirstOfNonempty
    (slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId source.toChoiceSource)
    (canonicalGoodSource_choices_nonempty source)

theorem canonicalGoodSourceChoice_mem
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId
        (slabObservablePairedConnectedCanonicalGoodB
          D rootFaceId targetFaceId)) :
    canonicalGoodSourceChoice source ∈
      slabObservablePairedConnectedStrandChoices
        D rootFaceId targetFaceId source.toChoiceSource :=
  listFirstOfNonempty_mem _ (canonicalGoodSource_choices_nonempty source)

/-! ## 2. Canonical finite minimum and congestion -/

/-- Capped finite minimum of the selected positive weights on the good
subcarrier. -/
def slabObservablePairedConnectedCanonicalGoodEta
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  listPositiveMinOne
    (fun source : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId
        (slabObservablePairedConnectedCanonicalGoodB
          D rootFaceId targetFaceId) =>
      slabObservablePairedConnectedStrandWeight
        D rootFaceId targetFaceId source.toChoiceSource
          (canonicalGoodSourceChoice source))
    (slabObservablePairedConnectedGoodSourceList
      D rootFaceId targetFaceId
        (slabObservablePairedConnectedCanonicalGoodB
          D rootFaceId targetFaceId))

private theorem listPositiveMinOne_le_one_local
    {A : Type} (value : A → Q') : ∀ items : List A,
    listPositiveMinOne value items ≤ (1 : Q')
  | [] => Q'.le_refl' 1
  | _ :: rest =>
      Q'.le_trans' _ _ _ (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one_local value rest)

theorem slabObservablePairedConnectedCanonicalGoodEta_pos
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    (0 : Q') < slabObservablePairedConnectedCanonicalGoodEta
      D rootFaceId targetFaceId := by
  unfold slabObservablePairedConnectedCanonicalGoodEta
  apply listPositiveMinOne_pos
  intro source _
  exact slabObservablePairedConnectedStrandWeight_pos_of_mem
    D rootFaceId targetFaceId source.toChoiceSource
      (canonicalGoodSourceChoice source)
      (canonicalGoodSourceChoice_mem source)

theorem slabObservablePairedConnectedCanonicalGoodEta_le_one
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    slabObservablePairedConnectedCanonicalGoodEta
        D rootFaceId targetFaceId ≤ (1 : Q') := by
  unfold slabObservablePairedConnectedCanonicalGoodEta
  exact listPositiveMinOne_le_one_local _ _

/-- At a fixed finite datum, the complete good-source list length is a
literal, though generally non-uniform, fiber-congestion bound. -/
def slabObservablePairedConnectedCanonicalGoodCongestion
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Nat :=
  (slabObservablePairedConnectedGoodSourceList
    D rootFaceId targetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        D rootFaceId targetFaceId)).length

/-- The entire routing witness is constructed at every finite datum. -/
def slabObservablePairedConnectedCanonicalGoodRouting
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget
      (slabObservablePairedConnectedCanonicalGoodB
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedCanonicalGoodEta
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedCanonicalGoodCongestion
        D rootFaceId targetFaceId) where
  eta_pos := slabObservablePairedConnectedCanonicalGoodEta_pos
    D rootFaceId targetFaceId
  eta_le_one := slabObservablePairedConnectedCanonicalGoodEta_le_one
    D rootFaceId targetFaceId
  choice := canonicalGoodSourceChoice
  choice_mem := canonicalGoodSourceChoice_mem
  choice_weight_floor := by
    intro source
    unfold slabObservablePairedConnectedCanonicalGoodEta
    exact listPositiveMinOne_le_of_mem _ _ source
      (List.mem_attach _ source)
  fiber_count_le := by
    intro target
    unfold selectedTargetFiber
      slabObservablePairedConnectedCanonicalGoodCongestion
    exact Nat.le_trans (List.length_filter_le _ _)
      (Nat.le_succ _)

/-! ## 3. A positive channel constructs the exact fixed-datum density -/

theorem slabObservablePairedConnectedCanonicalGoodB_true_of_positiveChannel
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) :
    slabObservablePairedConnectedCanonicalGoodB
      D rootFaceId targetFaceId witness.source = true := by
  unfold slabObservablePairedConnectedCanonicalGoodB
  cases hchoices : slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId witness.source with
  | nil =>
      have hfalse : witness.choice ∈ ([] : List
          (SlabObservablePairedConnectedStrandChoice
            D rootFaceId targetFaceId witness.source)) := by
        rw [← hchoices]
        exact witness.choice_mem
      exact False.elim (List.not_mem_nil hfalse)
  | cons first rest => rfl

def canonicalGoodSourceOfPositiveChannel
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) :
    SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId
        (slabObservablePairedConnectedCanonicalGoodB
          D rootFaceId targetFaceId) :=
  ⟨witness.source, List.mem_filter.mpr
    ⟨List.mem_attach _ witness.source,
      slabObservablePairedConnectedCanonicalGoodB_true_of_positiveChannel
        witness⟩⟩

theorem slabObservablePairedConnectedCanonicalGoodMass_pos
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) :
    (0 : Q') < slabObservablePairedConnectedGoodSourceMass
      D rootFaceId targetFaceId
        (slabObservablePairedConnectedCanonicalGoodB
          D rootFaceId targetFaceId) := by
  unfold slabObservablePairedConnectedGoodSourceMass
  exact listQSum_pos_of_mem
    (fun source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId =>
        slabObservableTwoReplicaPairWeight D source.1)
    (fun source => slabObservableTwoReplicaPairWeight_nonnegative
      D rootFaceId source.1)
    (slabObservablePairedConnectedGoodSources
      D rootFaceId targetFaceId
        (slabObservablePairedConnectedCanonicalGoodB
          D rootFaceId targetFaceId))
    (canonicalGoodSourceOfPositiveChannel witness).2
    (slabObservablePairedConnectedStrandSourceWeight_pos_of_coupling_pos
      D hcoupling rootFaceId targetFaceId witness.source)

theorem slabObservablePairedConnectedCanonicalGoodMass_le_sourceMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    slabObservablePairedConnectedGoodSourceMass
        D rootFaceId targetFaceId
          (slabObservablePairedConnectedCanonicalGoodB
            D rootFaceId targetFaceId) ≤
      slabObservablePairedConnectedSourceMass
        D rootFaceId targetFaceId :=
  slabObservablePairedConnectedGoodSourceMass_le_sourceMass
    D rootFaceId targetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        D rootFaceId targetFaceId)

/-- Exact datum-dependent good-mass fraction. -/
def slabObservablePairedConnectedCanonicalGoodDensityFraction
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) : Q' :=
  Q'.divPos
    (slabObservablePairedConnectedGoodSourceMass
      D rootFaceId targetFaceId
        (slabObservablePairedConnectedCanonicalGoodB
          D rootFaceId targetFaceId))
    (slabObservablePairedConnectedSourceMass
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedSourceMass_pos
      D hcoupling rootFaceId targetFaceId witness)

/-- A positive finite channel proves that the canonical good subcarrier has
an exact positive datum-dependent physical density. -/
def slabObservablePairedConnectedCanonicalGoodDensity
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) :
    SlabObservablePairedConnectedGoodSourceDensity
      D rootFaceId targetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedCanonicalGoodDensityFraction
        D hcoupling rootFaceId targetFaceId witness) := by
  let goodMass := slabObservablePairedConnectedGoodSourceMass
    D rootFaceId targetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        D rootFaceId targetFaceId)
  let sourceMass := slabObservablePairedConnectedSourceMass
    D rootFaceId targetFaceId
  have hsource : (0 : Q') < sourceMass :=
    slabObservablePairedConnectedSourceMass_pos
      D hcoupling rootFaceId targetFaceId witness
  have hgood : (0 : Q') < goodMass :=
    slabObservablePairedConnectedCanonicalGoodMass_pos
      D hcoupling rootFaceId targetFaceId witness
  have hle : goodMass ≤ sourceMass :=
    slabObservablePairedConnectedCanonicalGoodMass_le_sourceMass
      D rootFaceId targetFaceId
  exact
    { rho_pos := Q'.divPos_pos goodMass sourceMass hsource hgood
      rho_le_one := Q'.divPos_le_of_le_mul goodMass sourceMass hsource
        (Q'.le_trans' _ sourceMass _ hle
          (Q'.ge_of_eqv (Q'.one_mul_eqv sourceMass)))
      good_mass_floor := Q'.le_of_eqv
        (Q'.divPos_mul_eqv goodMass sourceMass hsource) }

/-! ## 4. Non-vacuous fixed-datum composition -/

def slabObservablePairedConnectedCanonicalGoodRetainedContraction
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) :
    SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId :=
  (slabObservablePairedConnectedCanonicalGoodRouting
    D rootFaceId targetFaceId htarget).toRetainedContraction
      (slabObservablePairedConnectedCanonicalGoodDensity
        D hcoupling rootFaceId targetFaceId witness)

/-- The reflected bent witness inhabits both canonical finite inputs. -/
def reflectedBentCanonicalGoodRetainedContraction :
    SlabObservablePairedSplitRetainedContraction
      reflectedBentPhysicalData reflectedBentRootFaceId
        reflectedBentTargetFaceId :=
  slabObservablePairedConnectedCanonicalGoodRetainedContraction
    reflectedBentPhysicalData reflectedBentPhysicalData_coupling_pos
    reflectedBentRootFaceId reflectedBentTargetFaceId
    reflectedBentTargetFaceId_physical reflectedBentPositiveChannelWitness

#print axioms canonicalGoodSourceChoice
#print axioms slabObservablePairedConnectedCanonicalGoodEta_pos
#print axioms slabObservablePairedConnectedCanonicalGoodRouting
#print axioms slabObservablePairedConnectedCanonicalGoodB_true_of_positiveChannel
#print axioms slabObservablePairedConnectedCanonicalGoodMass_pos
#print axioms slabObservablePairedConnectedCanonicalGoodDensity
#print axioms slabObservablePairedConnectedCanonicalGoodRetainedContraction
#print axioms reflectedBentCanonicalGoodRetainedContraction

end YMGap.Continuum.CompactDualSlabObservableCanonicalGoodSourceRouting
