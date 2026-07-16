/-
# An exact source-dependent finite configuration kernel for the unit-cube law

The observable-level resampler can match the refined Bernoulli coordinate,
but its rows forget the source.  Here the carrier is instead the complete
finite physical face-labelling space.  We put the exact normalized
spin-foam mass at the activity-matched coarse coupling on the source and the
exact normalized spin-foam mass at the fine coupling on the target.

The kernel is a finite rational Farlie--Gumbel--Morgenstern coupling.  Its
correlation coordinate is the centered coarse unit-cube occurrence on the
source times the centered refined unit-cube occurrence on the target:

  q(y) * (1 + (1_A(x)-P(A)) * (1_B(y)-P(B))).

Because both centered coordinates have exact mean zero, every row sums to
one and the physical source law pushes forward pointwise to the complete
physical target law.  The refined cylinder marginal is consequently the
previously defined exact physical ratio.  All entries are derived `Q'`
rationals.  The construction is genuinely source-dependent, but it is still
global: it uses the complete finite target law and is not claimed to be a
spatially local phase-cell RG kernel.
-/

import YMGap.Continuum.Z4RetunedParityPhysicalMixtureKernel
import YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
import YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor

namespace YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
open YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeBlockCylinderIntertwining
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricCanonicalRootOccurrence
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4RetunedParityPhysicalMixtureKernel
open YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

/-- Cancellation-free rational-semantic rebracketing. -/
local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ xs : List A,
      (∀ x, x ∈ xs → lower x ≤ upper x) →
      listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, h =>
      Q'.add_le_add (h head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun x hx => h x (List.mem_cons_of_mem head hx)))

private theorem one_sub_le_one_local {a : Q'}
    (ha : (0 : Q') ≤ a) : (1 : Q') + -a ≤ (1 : Q') := by
  have hneg : -a ≤ (0 : Q') := Q'.nonpos_neg_of_nonneg ha
  have hadd := Q'.add_le_add_left (1 : Q') (-a) 0 hneg
  rwa [Q'.add_zero'] at hadd

/-! ## 1. A finite centered-event copula -/

/-- Exact mass of a Boolean event under a finite rational mass. -/
def finiteEventMass {A : Type} (mass : A → Q') (states : List A)
    (event : A → Bool) : Q' :=
  listQSum (fun state => if event state then mass state else 0) states

theorem finiteEventMass_nonnegative {A : Type}
    (mass : A → Q') (states : List A) (event : A → Bool)
    (hmass : ∀ state, state ∈ states → (0 : Q') ≤ mass state) :
    (0 : Q') ≤ finiteEventMass mass states event := by
  unfold finiteEventMass
  apply listQSum_nonnegative_on
  intro state hstate
  cases hevent : event state
  · simp only [hevent, Bool.false_eq_true, if_false]
    exact Q'.le_refl' 0
  · simp only [hevent, if_true]
    exact hmass state hstate

theorem finiteEventMass_le_one {A : Type}
    (mass : A → Q') (states : List A) (event : A → Bool)
    (hmass : ∀ state, state ∈ states → (0 : Q') ≤ mass state)
    (htotal : listQSum mass states ≈ 1) :
    finiteEventMass mass states event ≤ (1 : Q') := by
  have hle : finiteEventMass mass states event ≤ listQSum mass states := by
    unfold finiteEventMass
    apply listQSum_mono_local
    intro state hstate
    cases hevent : event state
    · simp only [hevent, Bool.false_eq_true, if_false]
      exact hmass state hstate
    · simp only [hevent, if_true]
      exact Q'.le_refl' _
  exact Q'.le_trans' _ _ _ hle (Q'.le_of_eqv htotal)

/-- The centered indicator `1_event - parameter`, written without a cast
from `Bool`. -/
def centeredEventCoordinate {A : Type}
    (parameter : Q') (event : A → Bool) (state : A) : Q' :=
  if event state then (1 : Q') + -parameter else -parameter

theorem centeredWeight_pointwise {A : Type}
    (mass : A → Q') (parameter : Q') (event : A → Bool)
    (state : A) :
    mass state * centeredEventCoordinate parameter event state ≈
      (if event state then mass state else 0) +
        -(parameter * mass state) := by
  cases hevent : event state
  · simp only [centeredEventCoordinate, hevent, Bool.false_eq_true,
      if_false]
    refine Q'.eqv_trans _ (-(mass state * parameter)) _
      (Q'.mul_neg_eqv (mass state) parameter) ?_
    refine Q'.eqv_trans _ (-(parameter * mass state)) _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_comm_eqv (mass state) parameter)) ?_
    exact Q'.eqv_symm
      (Q'.eqv_of_eq (Q'.zero_add' (-(parameter * mass state))))
  · simp only [centeredEventCoordinate, hevent, if_true]
    ac_qeqv

private theorem listQSum_neg_local {A : Type} (value : A → Q') :
    ∀ states : List A,
      listQSum (fun state => -(value state)) states ≈
        -(listQSum value states)
  | [] => by
      have h := Q'.neg_add_self_eqv (0 : Q')
      rw [Q'.add_zero'] at h
      exact Q'.eqv_symm h
  | head :: tail => by
      change -(value head) + listQSum (fun state => -(value state)) tail ≈
        -(value head + listQSum value tail)
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_neg_local value tail)) ?_
      exact Q'.eqv_symm
        (Q'.neg_add_eqv (value head) (listQSum value tail))

/-- The exact finite expectation of a centered event coordinate is zero. -/
theorem centeredEventCoordinate_mean_zero {A : Type}
    (mass : A → Q') (states : List A) (event : A → Bool)
    (parameter : Q')
    (heventMass : finiteEventMass mass states event ≈ parameter)
    (htotal : listQSum mass states ≈ 1) :
    listQSum
        (fun state =>
          mass state * centeredEventCoordinate parameter event state)
        states ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        (if event state then mass state else 0) +
          -(parameter * mass state)) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    exact centeredWeight_pointwise mass parameter event state
  refine Q'.eqv_trans _
    (finiteEventMass mass states event +
      listQSum (fun state => -(parameter * mass state)) states) _
    (listQSum_add _ _ states) ?_
  have hnegSum :
      listQSum (fun state => -(parameter * mass state)) states ≈
        -(parameter * listQSum mass states) := by
    refine Q'.eqv_trans _
      (-(listQSum (fun state => parameter * mass state) states)) _ ?_ ?_
    · exact listQSum_neg_local
        (fun state => parameter * mass state) states
    · exact Q'.neg_eqv_congr _ _
        (listQSum_mul_left parameter mass states)
  refine Q'.eqv_trans _
    (parameter + -(parameter * 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr' heventMass
      (Q'.eqv_trans _ _ _ hnegSum
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left parameter _ _ htotal)))
  exact Q'.eqv_trans _
    (parameter + -parameter) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv parameter)))
    (Q'.add_neg_self_eqv parameter)

/-- Correlated row on the full target carrier.  It is not a Bernoulli
resampler: `targetMass` is the complete target configuration law. -/
def centeredConfigurationKernel {Source Target : Type}
    (targetMass : Target → Q')
    (sourceParameter targetParameter : Q')
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (source : Source) (target : Target) : Q' :=
  targetMass target *
    ((1 : Q') +
      centeredEventCoordinate sourceParameter sourceEvent source *
        centeredEventCoordinate targetParameter targetEvent target)

theorem centeredEventFactor_nonnegative {Source Target : Type}
    {sourceParameter targetParameter : Q'}
    (hsource0 : (0 : Q') ≤ sourceParameter)
    (hsource1 : sourceParameter ≤ (1 : Q'))
    (htarget0 : (0 : Q') ≤ targetParameter)
    (htarget1 : targetParameter ≤ (1 : Q'))
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (source : Source) (target : Target) :
    (0 : Q') ≤
      (1 : Q') +
        centeredEventCoordinate sourceParameter sourceEvent source *
          centeredEventCoordinate targetParameter targetEvent target := by
  cases hs : sourceEvent source <;> cases ht : targetEvent target
  · simp only [centeredEventCoordinate, hs, ht, Bool.false_eq_true,
      if_false]
    have hprod : (0 : Q') ≤ sourceParameter * targetParameter :=
      Q'.mul_nonneg _ _ hsource0 htarget0
    have hsum : (0 : Q') ≤
        (1 : Q') + sourceParameter * targetParameter :=
      Q'.zero_le_add _ _ (by decide) hprod
    have heq :
        (1 : Q') + -sourceParameter * -targetParameter ≈
          (1 : Q') + sourceParameter * targetParameter := by
      ac_qeqv
    exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv heq)
  · simp only [centeredEventCoordinate, hs, ht, Bool.false_eq_true,
      if_false, if_true]
    have honeSub : (0 : Q') ≤ (1 : Q') + -targetParameter :=
      Q'.sub_nonneg_of_le htarget1
    have hprod0 : (0 : Q') ≤
        sourceParameter * ((1 : Q') + -targetParameter) :=
      Q'.mul_nonneg _ _ hsource0 honeSub
    have hprod1 :
        sourceParameter * ((1 : Q') + -targetParameter) ≤ (1 : Q') := by
      have hmul := Q'.mul_le_mul_of_nonneg hsource1
        (one_sub_le_one_local htarget0)
        (by decide : (0 : Q') ≤ 1) honeSub
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_of_eqv (Q'.one_mul_eqv 1))
    have hinter : (0 : Q') ≤
        (1 : Q') +
          -(sourceParameter * ((1 : Q') + -targetParameter)) :=
      Q'.sub_nonneg_of_le hprod1
    have heq :
        (1 : Q') + -sourceParameter * ((1 : Q') + -targetParameter) ≈
          (1 : Q') +
            -(sourceParameter * ((1 : Q') + -targetParameter)) := by
      ac_qeqv
    exact Q'.le_trans' _ _ _ hinter (Q'.ge_of_eqv heq)
  · simp only [centeredEventCoordinate, hs, ht, Bool.false_eq_true,
      if_false, if_true]
    have honeSub : (0 : Q') ≤ (1 : Q') + -sourceParameter :=
      Q'.sub_nonneg_of_le hsource1
    have hprod0 : (0 : Q') ≤
        ((1 : Q') + -sourceParameter) * targetParameter :=
      Q'.mul_nonneg _ _ honeSub htarget0
    have hprod1 :
        ((1 : Q') + -sourceParameter) * targetParameter ≤ (1 : Q') := by
      have hmul := Q'.mul_le_mul_of_nonneg
        (one_sub_le_one_local hsource0) htarget1
        (by decide : (0 : Q') ≤ 1) htarget0
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_of_eqv (Q'.one_mul_eqv 1))
    have hinter : (0 : Q') ≤
        (1 : Q') +
          -(((1 : Q') + -sourceParameter) * targetParameter) :=
      Q'.sub_nonneg_of_le hprod1
    have heq :
        (1 : Q') + ((1 : Q') + -sourceParameter) * -targetParameter ≈
          (1 : Q') +
            -(((1 : Q') + -sourceParameter) * targetParameter) := by
      ac_qeqv
    exact Q'.le_trans' _ _ _ hinter (Q'.ge_of_eqv heq)
  · simp only [centeredEventCoordinate, hs, ht, if_true]
    exact Q'.zero_le_add _ _ (by decide)
      (Q'.mul_nonneg _ _
        (Q'.sub_nonneg_of_le hsource1)
        (Q'.sub_nonneg_of_le htarget1))

theorem centeredConfigurationKernel_nonnegative {Source Target : Type}
    (targetMass : Target → Q')
    (sourceParameter targetParameter : Q')
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (hsource0 : (0 : Q') ≤ sourceParameter)
    (hsource1 : sourceParameter ≤ (1 : Q'))
    (htarget0 : (0 : Q') ≤ targetParameter)
    (htarget1 : targetParameter ≤ (1 : Q'))
    (htargetMass : ∀ target, (0 : Q') ≤ targetMass target)
    (source : Source) (target : Target) :
    (0 : Q') ≤ centeredConfigurationKernel targetMass
      sourceParameter targetParameter sourceEvent targetEvent source target := by
  unfold centeredConfigurationKernel
  exact Q'.mul_nonneg _ _ (htargetMass target)
    (centeredEventFactor_nonnegative hsource0 hsource1 htarget0 htarget1
      sourceEvent targetEvent source target)

theorem centeredConfigurationKernel_row_normalized {Source Target : Type}
    (targetMass : Target → Q') (targetStates : List Target)
    (sourceParameter targetParameter : Q')
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (htargetEvent :
      finiteEventMass targetMass targetStates targetEvent ≈ targetParameter)
    (htargetTotal : listQSum targetMass targetStates ≈ 1)
    (source : Source) :
    listQSum
      (centeredConfigurationKernel targetMass sourceParameter targetParameter
        sourceEvent targetEvent source) targetStates ≈ 1 := by
  let sourceCoordinate :=
    centeredEventCoordinate sourceParameter sourceEvent source
  have hcenter := centeredEventCoordinate_mean_zero targetMass targetStates
    targetEvent targetParameter htargetEvent htargetTotal
  refine Q'.eqv_trans _
    (listQSum
      (fun target => targetMass target +
        sourceCoordinate *
          (targetMass target *
            centeredEventCoordinate targetParameter targetEvent target))
      targetStates) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    unfold centeredConfigurationKernel sourceCoordinate
    ac_qeqv
  refine Q'.eqv_trans _
    (listQSum targetMass targetStates +
      listQSum
        (fun target => sourceCoordinate *
          (targetMass target *
            centeredEventCoordinate targetParameter targetEvent target))
        targetStates) _
    (listQSum_add _ _ targetStates) ?_
  refine Q'.eqv_trans _
    (listQSum targetMass targetStates +
      sourceCoordinate *
        listQSum
          (fun target => targetMass target *
            centeredEventCoordinate targetParameter targetEvent target)
          targetStates) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_mul_left sourceCoordinate _ targetStates)
  refine Q'.eqv_trans _ ((1 : Q') + sourceCoordinate * 0) _
    (Q'.add_eqv_congr' htargetTotal
      (Q'.mul_eqv_congr_left sourceCoordinate _ _ hcenter)) ?_
  exact Q'.eqv_trans _ ((1 : Q') + 0) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_zero_eqv sourceCoordinate))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

/-- Exact pushforward through the finite configuration kernel. -/
def configurationPushforward {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (kernel : Source → Target → Q') (target : Target) : Q' :=
  listQSum (fun source => sourceMass source * kernel source target)
    sourceStates

/-- A finite exact joint coupling certificate.  The two marginal equalities
are pointwise on the listed carriers, while positivity is ambient. -/
structure PositiveFiniteConfigurationCoupling {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (targetMass : Target → Q') (targetStates : List Target)
    (jointMass : Source → Target → Q') : Prop where
  nonnegative : ∀ source target, (0 : Q') ≤ jointMass source target
  source_marginal : ∀ source,
    listQSum (jointMass source) targetStates ≈ sourceMass source
  target_marginal : ∀ target,
    listQSum (fun source => jointMass source target) sourceStates ≈
      targetMass target
  normalized :
    listQSum
      (fun source => listQSum (jointMass source) targetStates)
      sourceStates ≈ 1

theorem centeredConfigurationKernel_pushforward {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (targetMass : Target → Q')
    (sourceParameter targetParameter : Q')
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (hsourceEvent :
      finiteEventMass sourceMass sourceStates sourceEvent ≈ sourceParameter)
    (hsourceTotal : listQSum sourceMass sourceStates ≈ 1)
    (target : Target) :
    configurationPushforward sourceMass sourceStates
        (centeredConfigurationKernel targetMass sourceParameter
          targetParameter sourceEvent targetEvent) target ≈
      targetMass target := by
  let targetCoordinate :=
    centeredEventCoordinate targetParameter targetEvent target
  have hcenter := centeredEventCoordinate_mean_zero sourceMass sourceStates
    sourceEvent sourceParameter hsourceEvent hsourceTotal
  unfold configurationPushforward
  refine Q'.eqv_trans _
    (listQSum
      (fun source => targetMass target *
        (sourceMass source +
          targetCoordinate *
            (sourceMass source *
              centeredEventCoordinate sourceParameter sourceEvent source)))
      sourceStates) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    unfold centeredConfigurationKernel targetCoordinate
    ac_qeqv
  refine Q'.eqv_trans _
    (targetMass target *
      listQSum
        (fun source => sourceMass source +
          targetCoordinate *
            (sourceMass source *
              centeredEventCoordinate sourceParameter sourceEvent source))
        sourceStates) _
    (listQSum_mul_left (targetMass target) _ sourceStates) ?_
  refine Q'.eqv_trans _
    (targetMass target *
      (listQSum sourceMass sourceStates +
        listQSum
          (fun source => targetCoordinate *
            (sourceMass source *
              centeredEventCoordinate sourceParameter sourceEvent source))
          sourceStates)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (targetMass target) _ _
      (listQSum_add _ _ sourceStates)
  refine Q'.eqv_trans _
    (targetMass target *
      (listQSum sourceMass sourceStates +
        targetCoordinate *
          listQSum
            (fun source => sourceMass source *
              centeredEventCoordinate sourceParameter sourceEvent source)
            sourceStates)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (targetMass target) _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (listQSum_mul_left targetCoordinate _ sourceStates))
  refine Q'.eqv_trans _ (targetMass target * ((1 : Q') + targetCoordinate * 0)) _
    (Q'.mul_eqv_congr_left (targetMass target) _ _
      (Q'.add_eqv_congr' hsourceTotal
        (Q'.mul_eqv_congr_left targetCoordinate _ _ hcenter))) ?_
  refine Q'.eqv_trans _ (targetMass target * 1) _
    (Q'.mul_eqv_congr_left (targetMass target) _ _
      (Q'.eqv_trans _ ((1 : Q') + 0) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_zero_eqv targetCoordinate))
        (Q'.eqv_of_eq (Q'.add_zero' 1)))) ?_
  exact Q'.mul_one_eqv (targetMass target)

/-! ## 2. The actual activity-matched physical configuration laws -/

def activityMatchedCoarseConfigurationEvent (volume : Nat) :
    EdgeLabelling → Bool :=
  cutoffOneLiftedFamilyEvent volume
    (targetCylinderEvent 4 volume unitCubeBlockCylinderRoots
      unitCubeBlockCoarseOccurrencePredicate)

def activityMatchedRefinedConfigurationEvent (volume : Nat) :
    EdgeLabelling → Bool :=
  cutoffOneLiftedFamilyEvent volume
    (targetCylinderEvent 4 volume unitCubeBlockCylinderRoots
      unitCubeBlockRefinedOccurrencePredicate)

def activityMatchedConfigurationStateSpace (cutoff volume : Nat) :
    List EdgeLabelling :=
  explicitPhysicalLabellings cutoff volume

/-- The physical vacuum is an actual member of every finite configuration
carrier, not merely an ambient test labelling. -/
theorem zeroEdgeLabelling_mem_activityMatchedConfigurationStateSpace
    (cutoff volume : Nat) :
    zeroEdgeLabelling ∈
      activityMatchedConfigurationStateSpace cutoff volume := by
  unfold activityMatchedConfigurationStateSpace explicitPhysicalLabellings
    physicalFaceEdges
  exact zeroEdgeLabelling_mem_bounded cutoff volume

/-- At cutoff at least one, the canonical coarse unit-cube component is an
actual physical carrier state. -/
theorem coarseRoot_mem_activityMatchedConfigurationStateSpace
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    componentLabel (coarseUnitCubeBlockRootAt volume) ∈
      activityMatchedConfigurationStateSpace cutoff volume := by
  unfold activityMatchedConfigurationStateSpace explicitPhysicalLabellings
    physicalFaceEdges
  exact componentLabel_mem_bounded_of_one_le hcutoff
    (canonicalSurfacePolymer_mem_faceSupports
      (coarseUnitCubeBlockRootAt_mem_canonicalSurfacePolymers hvolume))

/-- At cutoff at least one, the refined dyadic unit-cube component is also
an actual physical carrier state. -/
theorem refinedRoot_mem_activityMatchedConfigurationStateSpace
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    componentLabel (dyadicUnitCubeSupportIdsAt volume) ∈
      activityMatchedConfigurationStateSpace cutoff volume := by
  unfold activityMatchedConfigurationStateSpace explicitPhysicalLabellings
    physicalFaceEdges
  exact componentLabel_mem_bounded_of_one_le hcutoff
    (canonicalSurfacePolymer_mem_faceSupports
      (dyadicUnitCubeSupportIdsAt_mem_canonicalSurfacePolymers hvolume))

def activityMatchedCoarseConfigurationMass
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) : EdgeLabelling → Q' :=
  normalizedPhysicalMass (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine) cutoff volume

def activityMatchedRefinedConfigurationMass
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) : EdgeLabelling → Q' :=
  normalizedPhysicalMass fineCoupling hfine cutoff volume

theorem normalizedPhysicalEventMass_eqv_probability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (event : EdgeLabelling → Bool) :
    finiteEventMass
        (normalizedPhysicalMass coupling hcoupling cutoff volume)
        (explicitPhysicalLabellings cutoff volume) event ≈
      Q'.divPos (parametricKEventNumerator coupling cutoff volume event)
        (parametricKPhysicalPartition coupling cutoff volume)
        (couplingKPhysicalPartition_pos hcoupling cutoff volume) := by
  unfold finiteEventMass normalizedPhysicalMass Q'.divPos
  unfold parametricKEventNumerator
  change
    listQSum
      (fun physical =>
        if event physical then
          parametricKPhysicalTerm coupling cutoff volume physical *
            Q'.recipPos
              (parametricKPhysicalPartition coupling cutoff volume)
              (couplingKPhysicalPartition_pos hcoupling cutoff volume)
        else 0)
      (explicitPhysicalLabellings cutoff volume) ≈
    listQSum (parametricKEventTerm coupling cutoff volume event)
        (boundedEdgeLabellings cutoff
          (List.range (plaquetteEdgeCount volume))) *
      Q'.recipPos
        (parametricKPhysicalPartition coupling cutoff volume)
        (couplingKPhysicalPartition_pos hcoupling cutoff volume)
  unfold explicitPhysicalLabellings physicalFaceEdges
  let states := boundedEdgeLabellings cutoff
    (List.range (plaquetteEdgeCount volume))
  let reciprocal := Q'.recipPos
    (parametricKPhysicalPartition coupling cutoff volume)
    (couplingKPhysicalPartition_pos hcoupling cutoff volume)
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        (if event physical
          then parametricKPhysicalTerm coupling cutoff volume physical
          else 0) * reciprocal) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro physical _
    cases hevent : event physical
    · simp only [hevent, Bool.false_eq_true, if_false]
      exact Q'.eqv_symm (Q'.zero_mul_eqv reciprocal)
    · simp only [hevent, if_true]
      exact Q'.eqv_refl _
  exact
    YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization.listQSum_mul_const
      (parametricKEventTerm coupling cutoff volume event) reciprocal states

theorem activityMatchedCoarseConfigurationEventMass_eqv
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    finiteEventMass
        (activityMatchedCoarseConfigurationMass
          fineCoupling hfine cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (activityMatchedCoarseConfigurationEvent volume) ≈
      couplingKUnitCubeBlockCoarseProbability
        (unitCubeBlockCoupling fineCoupling)
        (unitCubeBlockCoupling_nonnegative hfine) cutoff volume := by
  unfold activityMatchedCoarseConfigurationMass
    activityMatchedConfigurationStateSpace
    activityMatchedCoarseConfigurationEvent
    couplingKUnitCubeBlockCoarseProbability
    couplingKFamilyEventProbability
  exact normalizedPhysicalEventMass_eqv_probability _ _ _ _ _

theorem activityMatchedRefinedConfigurationEventMass_eqv
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    finiteEventMass
        (activityMatchedRefinedConfigurationMass
          fineCoupling hfine cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (activityMatchedRefinedConfigurationEvent volume) ≈
      couplingKUnitCubeBlockRefinedProbability
        fineCoupling hfine cutoff volume := by
  unfold activityMatchedRefinedConfigurationMass
    activityMatchedConfigurationStateSpace
    activityMatchedRefinedConfigurationEvent
    couplingKUnitCubeBlockRefinedProbability
    couplingKFamilyEventProbability
  exact normalizedPhysicalEventMass_eqv_probability _ _ _ _ _

/-! ## 3. Coarse-to-fine refinement coupling -/

/-- The full configuration-level coarse-to-fine refinement coupling.  This
is the inverse direction from a physical block transformation. -/
def activityMatchedFiniteConfigurationKernel
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) : Q' :=
  centeredConfigurationKernel
    (activityMatchedRefinedConfigurationMass
      fineCoupling hfine cutoff volume)
    (couplingKUnitCubeBlockCoarseProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (couplingKUnitCubeBlockRefinedProbability
      fineCoupling hfine cutoff volume)
    (activityMatchedCoarseConfigurationEvent volume)
    (activityMatchedRefinedConfigurationEvent volume)
    source target

theorem activityMatchedFiniteConfigurationKernel_nonnegative
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) :
    (0 : Q') ≤ activityMatchedFiniteConfigurationKernel
      fineCoupling hfine cutoff volume source target := by
  unfold activityMatchedFiniteConfigurationKernel
  apply centeredConfigurationKernel_nonnegative
  · exact couplingKUnitCubeBlockCoarseProbability_nonnegative _ _ _ _
  · exact couplingKUnitCubeBlockCoarseProbability_le_one _ _ _ _
  · exact couplingKUnitCubeBlockRefinedProbability_nonnegative _ _ _ _
  · exact couplingKUnitCubeBlockRefinedProbability_le_one _ _ _ _
  · intro physical
    exact normalizedPhysicalMass_nonnegative
      fineCoupling hfine cutoff volume physical

theorem activityMatchedFiniteConfigurationKernel_row_normalized
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source : EdgeLabelling) :
    listQSum
        (activityMatchedFiniteConfigurationKernel
          fineCoupling hfine cutoff volume source)
        (activityMatchedConfigurationStateSpace cutoff volume) ≈ 1 := by
  unfold activityMatchedFiniteConfigurationKernel
  apply centeredConfigurationKernel_row_normalized
  · exact activityMatchedRefinedConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume
  · exact normalizedPhysicalMass_total fineCoupling hfine cutoff volume

/-- Pointwise equality with the complete target spin-foam law, not merely
with its Boolean unit-cube marginal. -/
theorem activityMatchedFiniteConfigurationKernel_pushforward
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (target : EdgeLabelling) :
    configurationPushforward
        (activityMatchedCoarseConfigurationMass
          fineCoupling hfine cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (activityMatchedFiniteConfigurationKernel
          fineCoupling hfine cutoff volume) target ≈
      activityMatchedRefinedConfigurationMass
        fineCoupling hfine cutoff volume target := by
  unfold activityMatchedFiniteConfigurationKernel
  apply centeredConfigurationKernel_pushforward
  · exact activityMatchedCoarseConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume
  · exact normalizedPhysicalMass_total
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume

/-- The pushed refined cylinder event is exactly the established normalized
physical event numerator over the physical finite partition. -/
theorem activityMatchedFiniteConfigurationKernel_refinedCylinder
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    finiteEventMass
        (configurationPushforward
          (activityMatchedCoarseConfigurationMass
            fineCoupling hfine cutoff volume)
          (activityMatchedConfigurationStateSpace cutoff volume)
          (activityMatchedFiniteConfigurationKernel
            fineCoupling hfine cutoff volume))
        (activityMatchedConfigurationStateSpace cutoff volume)
        (activityMatchedRefinedConfigurationEvent volume) ≈
      couplingKUnitCubeBlockRefinedProbability
        fineCoupling hfine cutoff volume := by
  refine Q'.eqv_trans _
    (finiteEventMass
      (activityMatchedRefinedConfigurationMass
        fineCoupling hfine cutoff volume)
      (activityMatchedConfigurationStateSpace cutoff volume)
      (activityMatchedRefinedConfigurationEvent volume)) _ ?_ ?_
  · unfold finiteEventMass
    apply listQSum_congr_on
    intro target _
    cases hevent : activityMatchedRefinedConfigurationEvent volume target
    · simp only [hevent, Bool.false_eq_true, if_false]
      exact Q'.eqv_refl 0
    · simp only [hevent, if_true]
      exact activityMatchedFiniteConfigurationKernel_pushforward
        fineCoupling hfine cutoff volume target
  · exact activityMatchedRefinedConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume

/-! ## 4. Fine-to-coarse law-level blocking coupling -/

/-- A fine-source/coarse-target finite configuration kernel.  It is an exact
coupling of the two complete physical laws in the blocking direction.  It is
global (the target base row is the complete coarse law), so this theorem does
not assert spatial locality or identify the kernel with a phase-cell RG map. -/
def activityMatchedBlockingConfigurationKernel
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) : Q' :=
  centeredConfigurationKernel
    (activityMatchedCoarseConfigurationMass
      fineCoupling hfine cutoff volume)
    (couplingKUnitCubeBlockRefinedProbability
      fineCoupling hfine cutoff volume)
    (couplingKUnitCubeBlockCoarseProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (activityMatchedRefinedConfigurationEvent volume)
    (activityMatchedCoarseConfigurationEvent volume)
    source target

theorem activityMatchedBlockingConfigurationKernel_nonnegative
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) :
    (0 : Q') ≤ activityMatchedBlockingConfigurationKernel
      fineCoupling hfine cutoff volume source target := by
  unfold activityMatchedBlockingConfigurationKernel
  apply centeredConfigurationKernel_nonnegative
  · exact couplingKUnitCubeBlockRefinedProbability_nonnegative _ _ _ _
  · exact couplingKUnitCubeBlockRefinedProbability_le_one _ _ _ _
  · exact couplingKUnitCubeBlockCoarseProbability_nonnegative _ _ _ _
  · exact couplingKUnitCubeBlockCoarseProbability_le_one _ _ _ _
  · intro physical
    exact normalizedPhysicalMass_nonnegative
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume physical

theorem activityMatchedBlockingConfigurationKernel_row_normalized
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source : EdgeLabelling) :
    listQSum
        (activityMatchedBlockingConfigurationKernel
          fineCoupling hfine cutoff volume source)
        (activityMatchedConfigurationStateSpace cutoff volume) ≈ 1 := by
  unfold activityMatchedBlockingConfigurationKernel
  apply centeredConfigurationKernel_row_normalized
  · exact activityMatchedCoarseConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume
  · exact normalizedPhysicalMass_total
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume

/-- Pointwise, the complete fine physical law pushes through the blocking
coupling to the complete activity-matched coarse physical law. -/
theorem activityMatchedBlockingConfigurationKernel_pushforward
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (target : EdgeLabelling) :
    configurationPushforward
        (activityMatchedRefinedConfigurationMass
          fineCoupling hfine cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (activityMatchedBlockingConfigurationKernel
          fineCoupling hfine cutoff volume) target ≈
      activityMatchedCoarseConfigurationMass
        fineCoupling hfine cutoff volume target := by
  unfold activityMatchedBlockingConfigurationKernel
  apply centeredConfigurationKernel_pushforward
  · exact activityMatchedRefinedConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume
  · exact normalizedPhysicalMass_total
      fineCoupling hfine cutoff volume

/-- The coarse cylinder marginal of the blocking pushforward is exactly its
derived normalized physical probability. -/
theorem activityMatchedBlockingConfigurationKernel_coarseCylinder
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    finiteEventMass
        (configurationPushforward
          (activityMatchedRefinedConfigurationMass
            fineCoupling hfine cutoff volume)
          (activityMatchedConfigurationStateSpace cutoff volume)
          (activityMatchedBlockingConfigurationKernel
            fineCoupling hfine cutoff volume))
        (activityMatchedConfigurationStateSpace cutoff volume)
        (activityMatchedCoarseConfigurationEvent volume) ≈
      couplingKUnitCubeBlockCoarseProbability
        (unitCubeBlockCoupling fineCoupling)
        (unitCubeBlockCoupling_nonnegative hfine) cutoff volume := by
  refine Q'.eqv_trans _
    (finiteEventMass
      (activityMatchedCoarseConfigurationMass
        fineCoupling hfine cutoff volume)
      (activityMatchedConfigurationStateSpace cutoff volume)
      (activityMatchedCoarseConfigurationEvent volume)) _ ?_ ?_
  · unfold finiteEventMass
    apply listQSum_congr_on
    intro target _
    cases hevent : activityMatchedCoarseConfigurationEvent volume target
    · simp only [hevent, Bool.false_eq_true, if_false]
      exact Q'.eqv_refl 0
    · simp only [hevent, if_true]
      exact activityMatchedBlockingConfigurationKernel_pushforward
        fineCoupling hfine cutoff volume target
  · exact activityMatchedCoarseConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume

/-! ### The induced exact full-configuration joint law -/

def activityMatchedBlockingJointMass
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) : Q' :=
  activityMatchedRefinedConfigurationMass
      fineCoupling hfine cutoff volume source *
    activityMatchedBlockingConfigurationKernel
      fineCoupling hfine cutoff volume source target

theorem activityMatchedBlockingJointMass_nonnegative
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) :
    (0 : Q') ≤ activityMatchedBlockingJointMass
      fineCoupling hfine cutoff volume source target := by
  unfold activityMatchedBlockingJointMass
  exact Q'.mul_nonneg _ _
    (normalizedPhysicalMass_nonnegative
      fineCoupling hfine cutoff volume source)
    (activityMatchedBlockingConfigurationKernel_nonnegative
      fineCoupling hfine cutoff volume source target)

theorem activityMatchedBlockingJointMass_source_marginal
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source : EdgeLabelling) :
    listQSum
        (activityMatchedBlockingJointMass
          fineCoupling hfine cutoff volume source)
        (activityMatchedConfigurationStateSpace cutoff volume) ≈
      activityMatchedRefinedConfigurationMass
        fineCoupling hfine cutoff volume source := by
  unfold activityMatchedBlockingJointMass
  refine Q'.eqv_trans _
    (activityMatchedRefinedConfigurationMass
        fineCoupling hfine cutoff volume source *
      listQSum
        (activityMatchedBlockingConfigurationKernel
          fineCoupling hfine cutoff volume source)
        (activityMatchedConfigurationStateSpace cutoff volume)) _ ?_ ?_
  · exact listQSum_mul_left
      (activityMatchedRefinedConfigurationMass
        fineCoupling hfine cutoff volume source)
      (activityMatchedBlockingConfigurationKernel
        fineCoupling hfine cutoff volume source)
      (activityMatchedConfigurationStateSpace cutoff volume)
  · refine Q'.eqv_trans _
      (activityMatchedRefinedConfigurationMass
        fineCoupling hfine cutoff volume source * 1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (activityMatchedBlockingConfigurationKernel_row_normalized
          fineCoupling hfine cutoff volume source)
    · exact Q'.mul_one_eqv _

theorem activityMatchedBlockingJointMass_target_marginal
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (target : EdgeLabelling) :
    listQSum
        (fun source => activityMatchedBlockingJointMass
          fineCoupling hfine cutoff volume source target)
        (activityMatchedConfigurationStateSpace cutoff volume) ≈
      activityMatchedCoarseConfigurationMass
        fineCoupling hfine cutoff volume target := by
  change configurationPushforward
      (activityMatchedRefinedConfigurationMass
        fineCoupling hfine cutoff volume)
      (activityMatchedConfigurationStateSpace cutoff volume)
      (activityMatchedBlockingConfigurationKernel
        fineCoupling hfine cutoff volume) target ≈ _
  exact activityMatchedBlockingConfigurationKernel_pushforward
    fineCoupling hfine cutoff volume target

theorem activityMatchedBlockingJointMass_normalized
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    listQSum
        (fun source => listQSum
          (activityMatchedBlockingJointMass
            fineCoupling hfine cutoff volume source)
          (activityMatchedConfigurationStateSpace cutoff volume))
        (activityMatchedConfigurationStateSpace cutoff volume) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (activityMatchedRefinedConfigurationMass
        fineCoupling hfine cutoff volume)
      (activityMatchedConfigurationStateSpace cutoff volume)) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    exact activityMatchedBlockingJointMass_source_marginal
      fineCoupling hfine cutoff volume source
  · exact normalizedPhysicalMass_total
      fineCoupling hfine cutoff volume

def activityMatchedPositiveBlockingConfigurationCoupling
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) :
    PositiveFiniteConfigurationCoupling
      (activityMatchedRefinedConfigurationMass
        fineCoupling hfine cutoff volume)
      (activityMatchedConfigurationStateSpace cutoff volume)
      (activityMatchedCoarseConfigurationMass
        fineCoupling hfine cutoff volume)
      (activityMatchedConfigurationStateSpace cutoff volume)
      (activityMatchedBlockingJointMass
        fineCoupling hfine cutoff volume) where
  nonnegative := activityMatchedBlockingJointMass_nonnegative
    fineCoupling hfine cutoff volume
  source_marginal := activityMatchedBlockingJointMass_source_marginal
    fineCoupling hfine cutoff volume
  target_marginal := activityMatchedBlockingJointMass_target_marginal
    fineCoupling hfine cutoff volume
  normalized := activityMatchedBlockingJointMass_normalized
    fineCoupling hfine cutoff volume

/-! ## 5. The weakest unit-cube support-locality interface -/

/-- Minimal event-level block locality on finite carriers: a kernel may put
nonzero mass only on pairs whose chosen source and target block-cylinder
observables agree.  This is strictly weaker than spatial factorization or
neighborhood-local dependence, but is already necessary for a kernel that
intertwines the two block observables pointwise. -/
def CylinderSupportLocalOn {Source Target : Type}
    (sourceStates : List Source) (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (kernel : Source → Target → Q') : Prop :=
  ∀ source, source ∈ sourceStates →
    ∀ target, target ∈ targetStates →
      sourceEvent source ≠ targetEvent target →
        kernel source target ≈ 0

/-! ## 6. Concrete physical-carrier source-dependence fences -/

private theorem excitedPlaquetteIds_zero (volume : Nat) :
    excitedPlaquetteIds volume zeroEdgeLabelling = [] := by
  unfold excitedPlaquetteIds physicalFaceEdges
  have general : ∀ edges : List Nat,
      edges.filter (fun edge => decide (1 ≤ zeroEdgeLabelling edge)) = [] := by
    intro edges
    induction edges with
    | nil => rfl
    | cons head tail ih =>
        rw [List.filter_cons]
        have hfalse : decide (1 ≤ zeroEdgeLabelling head) = false := by rfl
        rw [hfalse]
        exact ih
  exact general _

private theorem physicalCanonicalAmbientFamily_zero (volume : Nat) :
    physicalCanonicalAmbientFamily volume zeroEdgeLabelling = [] := by
  unfold physicalCanonicalAmbientFamily canonicalSurfaceFamily
  rw [excitedPlaquetteIds_zero]
  have hlabel : componentLabel [] = zeroEdgeLabelling := by
    funext edge
    rfl
  rw [hlabel]
  unfold surfaceComponents
  rw [excitedPlaquetteIds_zero]
  change ambientOrderedFamily volume [] = []
  unfold ambientOrderedFamily
  generalize canonicalSurfacePolymers volume = polymers
  induction polymers with
  | nil => rfl
  | cons head tail ih =>
      rw [List.filter_cons]
      have hfalse : decide (head ∈ ([] : List (List Nat))) = false := by rfl
      rw [hfalse]
      exact ih

theorem activityMatchedCoarseConfigurationEvent_zero
    (volume : Nat) :
    activityMatchedCoarseConfigurationEvent volume zeroEdgeLabelling =
      false := by
  unfold activityMatchedCoarseConfigurationEvent cutoffOneLiftedFamilyEvent
  rw [physicalCanonicalAmbientFamily_zero]
  rw [unitCubeBlock_targetCoarse_eq_occurrence]
  rfl

theorem activityMatchedRefinedConfigurationEvent_zero
    (volume : Nat) :
    activityMatchedRefinedConfigurationEvent volume zeroEdgeLabelling =
      false := by
  unfold activityMatchedRefinedConfigurationEvent cutoffOneLiftedFamilyEvent
  rw [physicalCanonicalAmbientFamily_zero]
  rw [unitCubeBlock_targetRefined_eq_occurrence]
  rfl

theorem activityMatchedCoarseConfigurationEvent_root
    {volume : Nat} (hvolume : 4 ≤ volume) :
    activityMatchedCoarseConfigurationEvent volume
        (componentLabel (coarseUnitCubeBlockRootAt volume)) = true := by
  unfold activityMatchedCoarseConfigurationEvent
  rw [unitCubeBlock_targetCoarse_eq_occurrence]
  exact componentLabel_liftedOccurrenceEvent_true
    (coarseUnitCubeBlockRootAt_mem_canonicalSurfacePolymers hvolume)

theorem activityMatchedRefinedConfigurationEvent_root
    {volume : Nat} (hvolume : 4 ≤ volume) :
    activityMatchedRefinedConfigurationEvent volume
        (componentLabel (dyadicUnitCubeSupportIdsAt volume)) = true := by
  unfold activityMatchedRefinedConfigurationEvent
  rw [unitCubeBlock_targetRefined_eq_occurrence]
  exact componentLabel_liftedOccurrenceEvent_true
    (dyadicUnitCubeSupportIdsAt_mem_canonicalSurfacePolymers hvolume)

private theorem correlated_row_difference
    (mass left right targetCoordinate : Q') :
    mass * ((1 : Q') + left * targetCoordinate) +
        -(mass * ((1 : Q') + right * targetCoordinate)) ≈
      mass * ((left + -right) * targetCoordinate) := by
  have hnegMul :
      -(mass * ((1 : Q') + right * targetCoordinate)) ≈
        mass * (-((1 : Q') + right * targetCoordinate)) :=
    Q'.eqv_symm
      (Q'.mul_neg_eqv mass ((1 : Q') + right * targetCoordinate))
  refine Q'.eqv_trans _
    (mass * ((1 : Q') + left * targetCoordinate) +
      mass * (-((1 : Q') + right * targetCoordinate))) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) hnegMul) ?_
  refine Q'.eqv_trans _
    (mass *
      (((1 : Q') + left * targetCoordinate) +
        -((1 : Q') + right * targetCoordinate))) _
    (Q'.eqv_symm
      (Q'.mul_add_eqv mass
        ((1 : Q') + left * targetCoordinate)
        (-((1 : Q') + right * targetCoordinate)))) ?_
  apply Q'.mul_eqv_congr_left
  have hnegAdd := Q'.neg_add_eqv (1 : Q')
    (right * targetCoordinate)
  refine Q'.eqv_trans _
    (((1 : Q') + left * targetCoordinate) +
      (-1 + -(right * targetCoordinate))) _
    (Q'.add_eqv_congr_left ((1 : Q') + left * targetCoordinate) _ _
      hnegAdd) ?_
  refine Q'.eqv_trans _
    (((1 : Q') + -1) +
      (left * targetCoordinate + -(right * targetCoordinate))) _
    (Q'.add_swap_inner (1 : Q') (left * targetCoordinate)
      (-1) (-(right * targetCoordinate))) ?_
  refine Q'.eqv_trans _
    ((0 : Q') +
      (left * targetCoordinate + -(right * targetCoordinate))) _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv 1)) ?_
  rw [Q'.zero_add']
  refine Q'.eqv_trans _
    (left * targetCoordinate + (-right) * targetCoordinate) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_symm (Q'.neg_mul_eqv right targetCoordinate))) ?_
  exact Q'.eqv_symm
    (Q'.add_mul_eqv left (-right) targetCoordinate)

private theorem centered_true_false_row_difference
    (mass sourceParameter targetParameter : Q') :
    mass *
          ((1 : Q') +
            ((1 : Q') + -sourceParameter) * -targetParameter) +
        -(mass *
          ((1 : Q') + -sourceParameter * -targetParameter)) ≈
      -(mass * targetParameter) := by
  refine Q'.eqv_trans _
    (mass *
      ((((1 : Q') + -sourceParameter) + -(-sourceParameter)) *
        -targetParameter)) _
    (correlated_row_difference mass
      ((1 : Q') + -sourceParameter) (-sourceParameter)
      (-targetParameter)) ?_
  have hcoordinate :
      ((1 : Q') + -sourceParameter) + -(-sourceParameter) ≈ 1 := by
    refine Q'.eqv_trans _
      (((1 : Q') + -sourceParameter) + sourceParameter) _
      (Q'.add_eqv_congr_left ((1 : Q') + -sourceParameter) _ _
        (Q'.neg_neg_eqv sourceParameter)) ?_
    refine Q'.eqv_trans _
      ((1 : Q') + (-sourceParameter + sourceParameter)) _
      (Q'.add_assoc_eqv 1 (-sourceParameter) sourceParameter) ?_
    refine Q'.eqv_trans _ ((1 : Q') + 0) _
      (Q'.add_eqv_congr_left 1 _ _
        (Q'.neg_add_self_eqv sourceParameter)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' 1)
  refine Q'.eqv_trans _ (mass * ((1 : Q') * -targetParameter)) _
    (Q'.mul_eqv_congr_left mass _ _
      (Q'.mul_eqv_congr_right _ _ (-targetParameter) hcoordinate)) ?_
  refine Q'.eqv_trans _ (mass * -targetParameter) _
    (Q'.mul_eqv_congr_left mass _ _
      (Q'.one_mul_eqv (-targetParameter))) ?_
  exact Q'.mul_neg_eqv mass targetParameter

private theorem normalizedPhysicalMass_zero_pos
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    (0 : Q') < normalizedPhysicalMass coupling hcoupling cutoff volume
      zeroEdgeLabelling := by
  unfold normalizedPhysicalMass Q'.divPos
  have hone : parametricKPhysicalTerm coupling cutoff volume
      zeroEdgeLabelling ≈ 1 :=
    parametricKPhysicalTerm_zero_eqv_one coupling cutoff volume
  have hterm : (0 : Q') <
      parametricKPhysicalTerm coupling cutoff volume zeroEdgeLabelling :=
    YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
      (by decide) (Q'.le_of_eqv (Q'.eqv_symm hone))
  exact Q'.mul_pos hterm
    (Q'.recipPos_pos _
      (couplingKPhysicalPartition_pos hcoupling cutoff volume))

/-- The zero source and the canonical coarse-root source have provably
different rows at the physical vacuum target.  Thus the exact full-law
pushforward above is not the source-independent Boolean resampler in disguise. -/
theorem activityMatchedFiniteConfigurationKernel_source_dependent
    {fineCoupling : Q'} (hfine0 : (0 : Q') ≤ fineCoupling)
    (hfine : (0 : Q') < fineCoupling)
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    activityMatchedFiniteConfigurationKernel
        fineCoupling hfine0 cutoff volume
        (componentLabel (coarseUnitCubeBlockRootAt volume))
        zeroEdgeLabelling ≠
      activityMatchedFiniteConfigurationKernel
        fineCoupling hfine0 cutoff volume
        zeroEdgeLabelling zeroEdgeLabelling := by
  let coarseProbability := couplingKUnitCubeBlockCoarseProbability
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine0) cutoff volume
  let refinedProbability := couplingKUnitCubeBlockRefinedProbability
    fineCoupling hfine0 cutoff volume
  let vacuumMass := activityMatchedRefinedConfigurationMass
    fineCoupling hfine0 cutoff volume zeroEdgeLabelling
  have hrefinedPos : (0 : Q') < refinedProbability := by
    exact activityMatchedUnitCubeBlockRefinedProbability_pos
      hfine0 hfine hcutoff hvolume
  have hvacuumPos : (0 : Q') < vacuumMass := by
    exact normalizedPhysicalMass_zero_pos
      fineCoupling hfine0 cutoff volume
  intro hequal
  have hdiff :
      activityMatchedFiniteConfigurationKernel
          fineCoupling hfine0 cutoff volume
          (componentLabel (coarseUnitCubeBlockRootAt volume))
          zeroEdgeLabelling +
        -activityMatchedFiniteConfigurationKernel
          fineCoupling hfine0 cutoff volume
          zeroEdgeLabelling zeroEdgeLabelling ≈
        -(vacuumMass * refinedProbability) := by
    unfold activityMatchedFiniteConfigurationKernel
      centeredConfigurationKernel centeredEventCoordinate
    rw [activityMatchedCoarseConfigurationEvent_root hvolume,
      activityMatchedCoarseConfigurationEvent_zero,
      activityMatchedRefinedConfigurationEvent_zero]
    simp only [if_true, if_false, Bool.false_eq_true]
    change
      vacuumMass *
          ((1 : Q') + ((1 : Q') + -coarseProbability) * -refinedProbability) +
        -(vacuumMass *
          ((1 : Q') + -coarseProbability * -refinedProbability)) ≈
        -(vacuumMass * refinedProbability)
    exact centered_true_false_row_difference
      vacuumMass coarseProbability refinedProbability
  have hzero :
      activityMatchedFiniteConfigurationKernel
          fineCoupling hfine0 cutoff volume
          (componentLabel (coarseUnitCubeBlockRootAt volume))
          zeroEdgeLabelling +
        -activityMatchedFiniteConfigurationKernel
          fineCoupling hfine0 cutoff volume
          zeroEdgeLabelling zeroEdgeLabelling ≈ 0 := by
    rw [hequal]
    exact Q'.add_neg_self_eqv _
  have hprodPos : (0 : Q') < vacuumMass * refinedProbability :=
    Q'.mul_pos hvacuumPos hrefinedPos
  have hnegZero : -(vacuumMass * refinedProbability) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hdiff) hzero
  have hprodZero : vacuumMass * refinedProbability ≈ 0 := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_neg_eqv _))
      (Q'.neg_eqv_congr _ _ hnegZero)
  have hbad : vacuumMass * refinedProbability ≤ 0 :=
    Q'.le_of_eqv hprodZero
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' 0
    (YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hprodPos hbad)

/-- The two sources witnessing row dependence both lie in the physical
finite carrier (and the target vacuum used to distinguish them does too). -/
theorem activityMatchedFiniteConfigurationKernel_source_dependent_on_physical_carrier
    {fineCoupling : Q'} (hfine0 : (0 : Q') ≤ fineCoupling)
    (hfine : (0 : Q') < fineCoupling)
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    componentLabel (coarseUnitCubeBlockRootAt volume) ∈
        activityMatchedConfigurationStateSpace cutoff volume ∧
      zeroEdgeLabelling ∈
        activityMatchedConfigurationStateSpace cutoff volume ∧
      activityMatchedFiniteConfigurationKernel
          fineCoupling hfine0 cutoff volume
          (componentLabel (coarseUnitCubeBlockRootAt volume))
          zeroEdgeLabelling ≠
        activityMatchedFiniteConfigurationKernel
          fineCoupling hfine0 cutoff volume
          zeroEdgeLabelling zeroEdgeLabelling := by
  exact ⟨coarseRoot_mem_activityMatchedConfigurationStateSpace
      hcutoff hvolume,
    zeroEdgeLabelling_mem_activityMatchedConfigurationStateSpace
      cutoff volume,
    activityMatchedFiniteConfigurationKernel_source_dependent
      hfine0 hfine hcutoff hvolume⟩

/-- In the physically oriented fine-to-coarse coupling, the vacuum and the
canonical refined-root source have different rows at the coarse vacuum
target. -/
theorem activityMatchedBlockingConfigurationKernel_source_dependent
    {fineCoupling : Q'} (hfine0 : (0 : Q') ≤ fineCoupling)
    (hfine : (0 : Q') < fineCoupling)
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    activityMatchedBlockingConfigurationKernel
        fineCoupling hfine0 cutoff volume
        (componentLabel (dyadicUnitCubeSupportIdsAt volume))
        zeroEdgeLabelling ≠
      activityMatchedBlockingConfigurationKernel
        fineCoupling hfine0 cutoff volume
        zeroEdgeLabelling zeroEdgeLabelling := by
  let refinedProbability := couplingKUnitCubeBlockRefinedProbability
    fineCoupling hfine0 cutoff volume
  let coarseProbability := couplingKUnitCubeBlockCoarseProbability
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine0) cutoff volume
  let vacuumMass := activityMatchedCoarseConfigurationMass
    fineCoupling hfine0 cutoff volume zeroEdgeLabelling
  have hcoarsePos : (0 : Q') < coarseProbability := by
    exact activityMatchedUnitCubeBlockCoarseProbability_pos
      hfine0 hfine hcutoff hvolume
  have hvacuumPos : (0 : Q') < vacuumMass := by
    exact normalizedPhysicalMass_zero_pos
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine0) cutoff volume
  intro hequal
  have hdiff :
      activityMatchedBlockingConfigurationKernel
          fineCoupling hfine0 cutoff volume
          (componentLabel (dyadicUnitCubeSupportIdsAt volume))
          zeroEdgeLabelling +
        -activityMatchedBlockingConfigurationKernel
          fineCoupling hfine0 cutoff volume
          zeroEdgeLabelling zeroEdgeLabelling ≈
        -(vacuumMass * coarseProbability) := by
    unfold activityMatchedBlockingConfigurationKernel
      centeredConfigurationKernel centeredEventCoordinate
    rw [activityMatchedRefinedConfigurationEvent_root hvolume,
      activityMatchedRefinedConfigurationEvent_zero,
      activityMatchedCoarseConfigurationEvent_zero]
    simp only [if_true, if_false, Bool.false_eq_true]
    change
      vacuumMass *
          ((1 : Q') + ((1 : Q') + -refinedProbability) * -coarseProbability) +
        -(vacuumMass *
          ((1 : Q') + -refinedProbability * -coarseProbability)) ≈
        -(vacuumMass * coarseProbability)
    exact centered_true_false_row_difference
      vacuumMass refinedProbability coarseProbability
  have hzero :
      activityMatchedBlockingConfigurationKernel
          fineCoupling hfine0 cutoff volume
          (componentLabel (dyadicUnitCubeSupportIdsAt volume))
          zeroEdgeLabelling +
        -activityMatchedBlockingConfigurationKernel
          fineCoupling hfine0 cutoff volume
          zeroEdgeLabelling zeroEdgeLabelling ≈ 0 := by
    rw [hequal]
    exact Q'.add_neg_self_eqv _
  have hprodPos : (0 : Q') < vacuumMass * coarseProbability :=
    Q'.mul_pos hvacuumPos hcoarsePos
  have hnegZero : -(vacuumMass * coarseProbability) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hdiff) hzero
  have hprodZero : vacuumMass * coarseProbability ≈ 0 := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_neg_eqv _))
      (Q'.neg_eqv_congr _ _ hnegZero)
  have hbad : vacuumMass * coarseProbability ≤ 0 :=
    Q'.le_of_eqv hprodZero
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' 0
    (YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hprodPos hbad)

/-- Both sources in the fine-to-coarse row-dependence witness lie in the
finite physical carrier. -/
theorem activityMatchedBlockingConfigurationKernel_source_dependent_on_physical_carrier
    {fineCoupling : Q'} (hfine0 : (0 : Q') ≤ fineCoupling)
    (hfine : (0 : Q') < fineCoupling)
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    componentLabel (dyadicUnitCubeSupportIdsAt volume) ∈
        activityMatchedConfigurationStateSpace cutoff volume ∧
      zeroEdgeLabelling ∈
        activityMatchedConfigurationStateSpace cutoff volume ∧
      activityMatchedBlockingConfigurationKernel
          fineCoupling hfine0 cutoff volume
          (componentLabel (dyadicUnitCubeSupportIdsAt volume))
          zeroEdgeLabelling ≠
        activityMatchedBlockingConfigurationKernel
          fineCoupling hfine0 cutoff volume
          zeroEdgeLabelling zeroEdgeLabelling := by
  exact ⟨refinedRoot_mem_activityMatchedConfigurationStateSpace
      hcutoff hvolume,
    zeroEdgeLabelling_mem_activityMatchedConfigurationStateSpace
      cutoff volume,
    activityMatchedBlockingConfigurationKernel_source_dependent
      hfine0 hfine hcutoff hvolume⟩

private theorem true_false_centered_factor_pos
    {sourceParameter targetParameter : Q'}
    (hsourcePos : (0 : Q') < sourceParameter)
    (hsourceLeOne : sourceParameter ≤ (1 : Q'))
    (htargetLeOne : targetParameter ≤ (1 : Q')) :
    (0 : Q') <
      (1 : Q') +
        ((1 : Q') + -sourceParameter) * -targetParameter := by
  have hsourceComplement : (0 : Q') ≤
      (1 : Q') + -sourceParameter :=
    Q'.sub_nonneg_of_le hsourceLeOne
  have htargetComplement : (0 : Q') ≤
      (1 : Q') + -targetParameter :=
    Q'.sub_nonneg_of_le htargetLeOne
  have hproduct : (0 : Q') ≤
      ((1 : Q') + -sourceParameter) *
        ((1 : Q') + -targetParameter) :=
    Q'.mul_nonneg _ _ hsourceComplement htargetComplement
  have hrhs : (0 : Q') <
      sourceParameter +
        ((1 : Q') + -sourceParameter) *
          ((1 : Q') + -targetParameter) :=
    Q'.pos_add_nonneg hsourcePos hproduct
  have heq :
      (1 : Q') +
          ((1 : Q') + -sourceParameter) * -targetParameter ≈
        sourceParameter +
          ((1 : Q') + -sourceParameter) *
            ((1 : Q') + -targetParameter) := by
    have hsourceSum :
        sourceParameter + ((1 : Q') + -sourceParameter) ≈ 1 :=
      Q'.eqv_symm (Q'.add_sub_cancel_eqv 1 sourceParameter)
    have hright :
        sourceParameter +
            ((1 : Q') + -sourceParameter) *
              ((1 : Q') + -targetParameter) ≈
          (1 : Q') +
            ((1 : Q') + -sourceParameter) * -targetParameter := by
      refine Q'.eqv_trans _
        (sourceParameter +
          (((1 : Q') + -sourceParameter) * 1 +
            ((1 : Q') + -sourceParameter) * -targetParameter)) _ ?_ ?_
      · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_add_eqv
            ((1 : Q') + -sourceParameter) 1 (-targetParameter))
      refine Q'.eqv_trans _
        (sourceParameter +
          (((1 : Q') + -sourceParameter) +
            ((1 : Q') + -sourceParameter) * -targetParameter)) _ ?_ ?_
      · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.add_eqv_congr'
            (Q'.mul_one_eqv ((1 : Q') + -sourceParameter))
            (Q'.eqv_refl _))
      refine Q'.eqv_trans _
        ((sourceParameter + ((1 : Q') + -sourceParameter)) +
          ((1 : Q') + -sourceParameter) * -targetParameter) _ ?_ ?_
      · exact Q'.eqv_symm
          (Q'.add_assoc_eqv sourceParameter
            ((1 : Q') + -sourceParameter)
            (((1 : Q') + -sourceParameter) * -targetParameter))
      exact Q'.add_eqv_congr_right _ _ _ hsourceSum
    exact Q'.eqv_symm hright
  exact Q'.pos_of_lt_of_le hrhs (Q'.ge_of_eqv heq)

/-- A physical mismatched block-observable transition has strictly positive
weight in the global law-level blocking coupling. -/
theorem activityMatchedBlockingConfigurationKernel_refinedRoot_zero_pos
    {fineCoupling : Q'} (hfine0 : (0 : Q') ≤ fineCoupling)
    (hfine : (0 : Q') < fineCoupling)
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    (0 : Q') < activityMatchedBlockingConfigurationKernel
      fineCoupling hfine0 cutoff volume
      (componentLabel (dyadicUnitCubeSupportIdsAt volume))
      zeroEdgeLabelling := by
  let refinedProbability := couplingKUnitCubeBlockRefinedProbability
    fineCoupling hfine0 cutoff volume
  let coarseProbability := couplingKUnitCubeBlockCoarseProbability
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine0) cutoff volume
  let vacuumMass := activityMatchedCoarseConfigurationMass
    fineCoupling hfine0 cutoff volume zeroEdgeLabelling
  have hrefinedPos : (0 : Q') < refinedProbability :=
    activityMatchedUnitCubeBlockRefinedProbability_pos
      hfine0 hfine hcutoff hvolume
  have hrefinedLeOne : refinedProbability ≤ (1 : Q') :=
    couplingKUnitCubeBlockRefinedProbability_le_one _ _ _ _
  have hcoarseLeOne : coarseProbability ≤ (1 : Q') :=
    couplingKUnitCubeBlockCoarseProbability_le_one _ _ _ _
  have hvacuumPos : (0 : Q') < vacuumMass :=
    normalizedPhysicalMass_zero_pos
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine0) cutoff volume
  unfold activityMatchedBlockingConfigurationKernel
    centeredConfigurationKernel centeredEventCoordinate
  rw [activityMatchedRefinedConfigurationEvent_root hvolume,
    activityMatchedCoarseConfigurationEvent_zero]
  simp only [if_true, if_false, Bool.false_eq_true]
  change (0 : Q') < vacuumMass *
    ((1 : Q') +
      ((1 : Q') + -refinedProbability) * -coarseProbability)
  exact Q'.mul_pos hvacuumPos
    (true_false_centered_factor_pos hrefinedPos hrefinedLeOne hcoarseLeOne)

/-- Therefore the exact fine-to-coarse full-law coupling is not even local
in the weakest pointwise unit-cube support-intertwining sense.  Both the
mismatched source and target are genuine physical carrier states. -/
theorem activityMatchedBlockingConfigurationKernel_not_cylinderSupportLocal
    {fineCoupling : Q'} (hfine0 : (0 : Q') ≤ fineCoupling)
    (hfine : (0 : Q') < fineCoupling)
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    ¬ CylinderSupportLocalOn
      (activityMatchedConfigurationStateSpace cutoff volume)
      (activityMatchedConfigurationStateSpace cutoff volume)
      (activityMatchedRefinedConfigurationEvent volume)
      (activityMatchedCoarseConfigurationEvent volume)
      (activityMatchedBlockingConfigurationKernel
        fineCoupling hfine0 cutoff volume) := by
  intro hlocal
  let source := componentLabel (dyadicUnitCubeSupportIdsAt volume)
  let target := zeroEdgeLabelling
  have hsource : source ∈
      activityMatchedConfigurationStateSpace cutoff volume :=
    refinedRoot_mem_activityMatchedConfigurationStateSpace
      hcutoff hvolume
  have htarget : target ∈
      activityMatchedConfigurationStateSpace cutoff volume :=
    zeroEdgeLabelling_mem_activityMatchedConfigurationStateSpace
      cutoff volume
  have hmismatch :
      activityMatchedRefinedConfigurationEvent volume source ≠
        activityMatchedCoarseConfigurationEvent volume target := by
    unfold source target
    rw [activityMatchedRefinedConfigurationEvent_root hvolume,
      activityMatchedCoarseConfigurationEvent_zero]
    decide
  have hzero := hlocal source hsource target htarget hmismatch
  have hpositive : (0 : Q') <
      activityMatchedBlockingConfigurationKernel
        fineCoupling hfine0 cutoff volume source target := by
    unfold source target
    exact activityMatchedBlockingConfigurationKernel_refinedRoot_zero_pos
      hfine0 hfine hcutoff hvolume
  have hnonpositive :
      activityMatchedBlockingConfigurationKernel
        fineCoupling hfine0 cutoff volume source target ≤ 0 :=
    Q'.le_of_eqv hzero
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' 0
    (YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
      hpositive hnonpositive)

#print axioms finiteEventMass_nonnegative
#print axioms finiteEventMass_le_one
#print axioms centeredEventCoordinate_mean_zero
#print axioms centeredConfigurationKernel_nonnegative
#print axioms centeredEventFactor_nonnegative
#print axioms centeredConfigurationKernel_row_normalized
#print axioms centeredConfigurationKernel_pushforward
#print axioms activityMatchedCoarseConfigurationEventMass_eqv
#print axioms activityMatchedRefinedConfigurationEventMass_eqv
#print axioms normalizedPhysicalEventMass_eqv_probability
#print axioms activityMatchedFiniteConfigurationKernel_nonnegative
#print axioms activityMatchedFiniteConfigurationKernel_row_normalized
#print axioms activityMatchedFiniteConfigurationKernel_pushforward
#print axioms activityMatchedFiniteConfigurationKernel_refinedCylinder
#print axioms activityMatchedBlockingConfigurationKernel_nonnegative
#print axioms activityMatchedBlockingConfigurationKernel_row_normalized
#print axioms activityMatchedBlockingConfigurationKernel_pushforward
#print axioms activityMatchedBlockingConfigurationKernel_coarseCylinder
#print axioms activityMatchedBlockingJointMass_nonnegative
#print axioms activityMatchedBlockingJointMass_source_marginal
#print axioms activityMatchedBlockingJointMass_target_marginal
#print axioms activityMatchedBlockingJointMass_normalized
#print axioms activityMatchedPositiveBlockingConfigurationCoupling
#print axioms activityMatchedCoarseConfigurationEvent_zero
#print axioms physicalCanonicalAmbientFamily_zero
#print axioms excitedPlaquetteIds_zero
#print axioms activityMatchedRefinedConfigurationEvent_zero
#print axioms activityMatchedCoarseConfigurationEvent_root
#print axioms activityMatchedRefinedConfigurationEvent_root
#print axioms normalizedPhysicalMass_zero_pos
#print axioms YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence.activityMatchedUnitCubeBlockRefinedProbability_pos
#print axioms activityMatchedFiniteConfigurationKernel_source_dependent
#print axioms zeroEdgeLabelling_mem_activityMatchedConfigurationStateSpace
#print axioms coarseRoot_mem_activityMatchedConfigurationStateSpace
#print axioms refinedRoot_mem_activityMatchedConfigurationStateSpace
#print axioms activityMatchedFiniteConfigurationKernel_source_dependent_on_physical_carrier
#print axioms activityMatchedBlockingConfigurationKernel_source_dependent
#print axioms activityMatchedBlockingConfigurationKernel_source_dependent_on_physical_carrier
#print axioms activityMatchedBlockingConfigurationKernel_refinedRoot_zero_pos
#print axioms activityMatchedBlockingConfigurationKernel_not_cylinderSupportLocal

end YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
