/-
# Fixed-volume cutoff limits below the strong-coupling anchor

The finite-box event numerator and partition are monotone in the nonnegative
heat-kernel coupling before normalization.  This module applies that fact to
the literal new-label cutoff sectors.  For every `0 <= w <= anchorCoupling`,
both the partition increment and every masked event increment are dominated
by the corresponding anchor increment, and hence inherit its exact dyadic
cutoff tail.

The inherited tail gives a constructive normalized cutoff limit for every
fixed finite box and every Boolean physical-labelling event.  Specializing to
the activity-matched shifted coarse unit cube carries the cutoff-uniform
positive occurrence floor into this fixed-volume cutoff limit.

No comparison between two different box volumes is proved here.  The
coupling-parametric thermodynamic compatibility needed for a shifted-coupling
infinite-volume state remains a separate locality theorem.
-/

import YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
import YMGap.Continuum.Z4SpinSummedCutoffEventBridge

namespace YMGap.Continuum.Z4CouplingParametricCutoffEventCofinal

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
open YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
open YMGap.Continuum.Z4CouplingParametricMonotonicity
open YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity
open YMGap.Continuum.Z4SpinSummedCutoffEventBridge
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

private theorem two_mul_eqv_local (x : Q') :
    Q'.ofNat 2 * x ≈ x + x := by
  refine Q'.eqv_trans _ ((Q'.ofNat 1 + Q'.ofNat 1) * x) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv 1 1)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 1 * x + Q'.ofNat 1 * x) _
    (Q'.add_mul_eqv (Q'.ofNat 1) (Q'.ofNat 1) x) ?_
  exact Q'.add_eqv_congr' (Q'.one_mul_eqv x) (Q'.one_mul_eqv x)

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ source : List A,
      (∀ item, item ∈ source → lower item ≤ upper item) →
        listQSum lower source ≤ listQSum upper source
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem => hle item
            (List.mem_cons_of_mem head hitem)))

/-! ## 1. New-label increments are monotone in the coupling -/

theorem parametricKCutoffIncrement_mono_coupling
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) (K L volume : Nat) :
    parametricKCutoffIncrement lower K L volume ≤
      parametricKCutoffIncrement upper K L volume := by
  unfold parametricKCutoffIncrement
  apply listQSum_mono_local
  intro physical hphysical
  exact parametricKPhysicalTerm_mono_coupling hlower hle
    (List.mem_filter.mp hphysical).1

theorem parametricKEventCutoffIncrement_mono_coupling
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) (K L volume : Nat)
    (event : EdgeLabelling → Bool) :
    parametricKEventCutoffIncrement lower K L volume event ≤
      parametricKEventCutoffIncrement upper K L volume event := by
  unfold parametricKEventCutoffIncrement
  apply listQSum_mono_local
  intro physical hphysical
  exact parametricKEventTerm_mono_coupling hlower hle
    (List.mem_filter.mp hphysical).1

/-! ## 2. Every sub-anchor coupling inherits the anchor dyadic tail -/

theorem couplingParametricCutoffIncrement_le_two_halfPow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (stage depth volume : Nat) :
    parametricKCutoffIncrement coupling
        (interactingAdjacentCutoff stage volume)
        (interactingAdjacentCutoff stage volume + depth) volume ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  exact Q'.le_trans' _ _ _
    (parametricKCutoffIncrement_mono_coupling
      hcoupling hle _ _ volume)
    (anchorParametricCutoffIncrement_le_two_halfPow
      stage depth volume)

theorem couplingParametricAdjacentIncrement_le_halfPow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (stage volume : Nat) :
    parametricKCutoffIncrement coupling
        (interactingAdjacentCutoff stage volume)
        (interactingAdjacentCutoff stage volume + 1) volume ≤
      HalfPow.half ^ stage := by
  exact Q'.le_trans' _ _ _
    (parametricKCutoffIncrement_mono_coupling
      hcoupling hle _ _ volume)
    (anchorParametricAdjacentIncrement_le_halfPow stage volume)

theorem couplingParametricEventCutoffIncrement_le_two_halfPow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (stage depth volume : Nat) (event : EdgeLabelling → Bool) :
    parametricKEventCutoffIncrement coupling
        (interactingAdjacentCutoff stage volume)
        (interactingAdjacentCutoff stage volume + depth)
        volume event ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  exact Q'.le_trans' _ _ _
    (parametricKEventCutoffIncrement_mono_coupling
      hcoupling hle _ _ volume event)
    (anchorParametricEventCutoffIncrement_le_two_halfPow
      stage depth volume event)

theorem couplingParametricEventAdjacentIncrement_le_halfPow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (stage volume : Nat) (event : EdgeLabelling → Bool) :
    parametricKEventCutoffIncrement coupling
        (interactingAdjacentCutoff stage volume)
        (interactingAdjacentCutoff stage volume + 1)
        volume event ≤
      HalfPow.half ^ stage := by
  exact Q'.le_trans' _ _ _
    (parametricKEventCutoffIncrement_mono_coupling
      hcoupling hle _ _ volume event)
    (anchorParametricEventAdjacentIncrement_le_halfPow
      stage volume event)

/-! ## 3. The normalized fixed-volume cutoff sequence -/

def couplingParametricCutoffEventProbabilitySequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (volume : Nat) (event : EdgeLabelling → Bool)
    (stage : Nat) : Q' :=
  Q'.divPos
    (parametricKEventNumerator coupling
      (interactingAdjacentCutoff stage volume) volume event)
    (parametricKPhysicalPartition coupling
      (interactingAdjacentCutoff stage volume) volume)
    (couplingKPhysicalPartition_pos hcoupling
      (interactingAdjacentCutoff stage volume) volume)

theorem couplingParametricCutoffEventProbabilitySequence_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (volume : Nat) (event : EdgeLabelling → Bool)
    (stage : Nat) :
    (0 : Q') ≤ couplingParametricCutoffEventProbabilitySequence
      coupling hcoupling volume event stage := by
  unfold couplingParametricCutoffEventProbabilitySequence Q'.divPos
  exact Q'.mul_nonneg _ _
    (parametricKEventNumerator_nonnegative
      hcoupling _ volume event)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (couplingKPhysicalPartition_pos
          hcoupling _ volume)))

theorem couplingParametricCutoffEventProbabilitySequence_le_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (volume : Nat) (event : EdgeLabelling → Bool)
    (stage : Nat) :
    couplingParametricCutoffEventProbabilitySequence
        coupling hcoupling volume event stage ≤ (1 : Q') := by
  unfold couplingParametricCutoffEventProbabilitySequence
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (parametricKEventNumerator_le_partition
      hcoupling _ volume event)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (parametricKPhysicalPartition coupling
          (interactingAdjacentCutoff stage volume) volume)))

theorem couplingParametricCutoffPartitionSequence_le_anchorUniformBound
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (volume stage : Nat) :
    parametricKPhysicalPartition coupling
        (interactingAdjacentCutoff stage volume) volume ≤
      anchorParametricCutoffPartitionUniformBound volume := by
  exact Q'.le_trans' _ _ _
    (parametricKPhysicalPartition_mono_coupling
      hcoupling hle (interactingAdjacentCutoff stage volume) volume)
    (anchorParametricCutoffPartitionSequence_le_uniformBound
      volume stage)

theorem couplingParametricCutoffEventProbabilitySequence_step_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (volume : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    Q'.abs
        (couplingParametricCutoffEventProbabilitySequence
            coupling hcoupling volume event stage +
          -couplingParametricCutoffEventProbabilitySequence
            coupling hcoupling volume event (stage + 1)) ≤
      geoIncr (anchorParametricCutoffProbabilityStepConstant volume)
        stage := by
  let K := interactingAdjacentCutoff stage volume
  let L := K + 1
  let a := parametricKEventNumerator coupling K volume event
  let A := parametricKEventNumerator coupling L volume event
  let d := parametricKPhysicalPartition coupling K volume
  let D := parametricKPhysicalPartition coupling L volume
  let e := HalfPow.half ^ stage
  let B := anchorParametricCutoffPartitionUniformBound volume
  have hcutoffSucc : interactingAdjacentCutoff (stage + 1) volume = L := by
    dsimp only [L, K]
    unfold interactingAdjacentCutoff
    omega
  have hKone : 1 ≤ K := by
    dsimp only [K]
    exact interactingAdjacentCutoff_ge_one stage volume
  have hLone : 1 ≤ L := by omega
  have ha0 : (0 : Q') ≤ a := by
    dsimp only [a]
    exact parametricKEventNumerator_nonnegative
      hcoupling K volume event
  have hA0 : (0 : Q') ≤ A := by
    dsimp only [A]
    exact parametricKEventNumerator_nonnegative
      hcoupling L volume event
  have hd1 : (1 : Q') ≤ d := by
    dsimp only [d]
    exact couplingKPhysicalPartition_one_le hcoupling K volume
  have hD1 : (1 : Q') ≤ D := by
    dsimp only [D]
    exact couplingKPhysicalPartition_one_le hcoupling L volume
  have hKL : K ≤ L := by omega
  have haA : a ≤ A := by
    dsimp only [a, A]
    exact parametricKEventNumerator_mono hcoupling hKL
  have hdD : d ≤ D := by
    dsimp only [d, D]
    exact parametricKPhysicalPartition_mono hcoupling hKL
  have he0 : (0 : Q') ≤ e := by
    dsimp only [e]
    exact Q'.pow_nonneg _ HalfPow.half_nonneg stage
  have hAdef : A - a ≤ e := by
    change A + -a ≤ e
    have heq := parametricKEventNumerator_difference_eq_increment
      (w := coupling) (K := K) (L := L) (n := volume)
      (event := event) hKL
    have hinc : parametricKEventCutoffIncrement coupling
        K L volume event ≤ e := by
      dsimp only [L, K, e]
      exact couplingParametricEventAdjacentIncrement_le_halfPow
        hcoupling hle stage volume event
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hinc
  have hDdef : D - d ≤ e := by
    change D + -d ≤ e
    have heq := parametricKPhysicalPartition_difference_eq_increment
      (w := coupling) (K := K) (L := L) (n := volume) hKL
    have hinc : parametricKCutoffIncrement coupling K L volume ≤ e := by
      dsimp only [L, K, e]
      exact couplingParametricAdjacentIncrement_le_halfPow
        hcoupling hle stage volume
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hinc
  have hratio := ratio_endpoint_continuity
    ha0 hA0 hd1 hD1 haA hdD he0 he0 hAdef hDdef
  have hratioAbs :
      Q'.abs
          (Q'.divPos a d (FusedRatioCorridor.pos_of_one_le hd1) +
            -Q'.divPos A D
              (FusedRatioCorridor.pos_of_one_le hD1)) ≤
        e * D + A * e := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (YMGap.Continuum.ContinuumYMStack.absQ_eqv_abs
          (Q'.divPos a d
              (FusedRatioCorridor.pos_of_one_le hd1) +
            -Q'.divPos A D
              (FusedRatioCorridor.pos_of_one_le hD1))))
      hratio
  have hD_B : D ≤ B := by
    dsimp only [D, B]
    rw [← hcutoffSucc]
    exact couplingParametricCutoffPartitionSequence_le_anchorUniformBound
      hcoupling hle volume (stage + 1)
  have hA_D : A ≤ D := by
    dsimp only [A, D]
    exact parametricKEventNumerator_le_partition
      hcoupling L volume event
  have hA_B : A ≤ B := Q'.le_trans' _ _ _ hA_D hD_B
  have hleft : e * D ≤ e * B :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hD_B he0
  have hright : A * e ≤ B * e :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hA_B he0
  have hbudget : e * D + A * e ≤
      (Q'.ofNat 2 * B) * e := by
    refine Q'.le_trans' _ _ _ (Q'.add_le_add hleft hright)
      (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ (B * e + B * e) _
      (Q'.add_eqv_congr'
        (Q'.mul_comm_eqv e B) (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ ((B + B) * e) _
      (Q'.eqv_symm (Q'.add_mul_eqv B B e)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (two_mul_eqv_local B))
  have hratioSequence :
      Q'.abs
          (couplingParametricCutoffEventProbabilitySequence
              coupling hcoupling volume event stage +
            -couplingParametricCutoffEventProbabilitySequence
              coupling hcoupling volume event (stage + 1)) ≤
        e * D + A * e := by
    dsimp only [a, A, d, D] at hratioAbs
    simpa only [couplingParametricCutoffEventProbabilitySequence,
      hcutoffSucc, K, L, A, D] using hratioAbs
  refine Q'.le_trans' _ _ _ hratioSequence
    (Q'.le_trans' _ _ _ hbudget ?_)
  unfold geoIncr anchorParametricCutoffProbabilityStepConstant
  dsimp only [B, e]
  exact Q'.le_refl' _

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

theorem couplingParametricCutoffEventProbabilitySequence_step_upper
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (volume : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    couplingParametricCutoffEventProbabilitySequence
        coupling hcoupling volume event (stage + 1) ≤
      couplingParametricCutoffEventProbabilitySequence
          coupling hcoupling volume event stage +
        geoIncr (anchorParametricCutoffProbabilityStepConstant volume)
          stage := by
  exact (two_sided_add_of_abs_sub_le_local
    (couplingParametricCutoffEventProbabilitySequence_step_abs_le
      hcoupling hle volume event stage)).2

theorem couplingParametricCutoffEventProbabilitySequence_step_lower
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (volume : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    couplingParametricCutoffEventProbabilitySequence
        coupling hcoupling volume event stage ≤
      couplingParametricCutoffEventProbabilitySequence
          coupling hcoupling volume event (stage + 1) +
        geoIncr (anchorParametricCutoffProbabilityStepConstant volume)
          stage := by
  exact (two_sided_add_of_abs_sub_le_local
    (couplingParametricCutoffEventProbabilitySequence_step_abs_le
      hcoupling hle volume event stage)).1

/-! ## 4. The normalized constructive cutoff limit -/

def couplingParametricCutoffEventProbabilityLimit
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (volume : Nat) (event : EdgeLabelling → Bool) : CReal :=
  crealOfGeoIncrement
    (couplingParametricCutoffEventProbabilitySequence
      coupling hcoupling volume event)
    (anchorParametricCutoffProbabilityStepConstant volume)
    (anchorParametricCutoffProbabilityStepConstant_nonnegative volume)
    (couplingParametricCutoffEventProbabilitySequence_step_upper
      hcoupling hle volume event)
    (couplingParametricCutoffEventProbabilitySequence_step_lower
      hcoupling hle volume event)
    (fun epsilon hepsilon => by
      let coefficient := Q'.ofNat 2 *
        anchorParametricCutoffProbabilityStepConstant volume
      have hcoefficient : (0 : Q') ≤ coefficient := by
        dsimp only [coefficient]
        exact Q'.mul_nonneg _ _ (by decide)
          (anchorParametricCutoffProbabilityStepConstant_nonnegative
            volume)
      let delta := epsilon * Q'.invSucc coefficient.num.toNat
      have hdelta : (0 : Q') < delta := by
        dsimp only [delta]
        exact Q'.mul_pos hepsilon
          (Q'.invSucc_pos coefficient.num.toNat)
      refine ⟨delta, hdelta, ?_⟩
      exact ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
        hcoefficient (Q'.le_of_lt hepsilon))

@[simp] theorem couplingParametricCutoffEventProbabilityLimit_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (volume : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    (couplingParametricCutoffEventProbabilityLimit
      coupling hcoupling hle volume event).approx stage =
        couplingParametricCutoffEventProbabilitySequence
          coupling hcoupling volume event stage := rfl

theorem couplingParametricCutoffEventProbabilityLimit_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (volume : Nat) (event : EdgeLabelling → Bool) :
    CReal.ofQ' 0 ≤ couplingParametricCutoffEventProbabilityLimit
      coupling hcoupling hle volume event := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  rw [couplingParametricCutoffEventProbabilityLimit_approx]
  exact couplingParametricCutoffEventProbabilitySequence_nonnegative
    coupling hcoupling volume event stage

theorem couplingParametricCutoffEventProbabilityLimit_le_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (volume : Nat) (event : EdgeLabelling → Bool) :
    couplingParametricCutoffEventProbabilityLimit
        coupling hcoupling hle volume event ≤ CReal.ofQ' 1 := by
  apply CReal.le_ofQ'_of_approx_le
  intro stage
  rw [couplingParametricCutoffEventProbabilityLimit_approx]
  exact couplingParametricCutoffEventProbabilitySequence_le_one
    coupling hcoupling volume event stage

/-! ## 5. Canonical-family wrapper and the shifted coarse cube -/

def couplingParametricCutoffFamilyEventProbabilityLimit
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (volume : Nat) (event : List (List Nat) → Bool) : CReal :=
  couplingParametricCutoffEventProbabilityLimit
    coupling hcoupling hle volume
      (cutoffOneLiftedFamilyEvent volume event)

@[simp] theorem couplingParametricCutoffFamilyEventProbabilityLimit_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (volume : Nat) (event : List (List Nat) → Bool)
    (stage : Nat) :
    (couplingParametricCutoffFamilyEventProbabilityLimit
        coupling hcoupling hle volume event).approx stage =
      couplingKFamilyEventProbability coupling hcoupling
        (interactingAdjacentCutoff stage volume) volume event := rfl

def shiftedCoarseUnitCubeFixedVolumeCutoffLimit
    (volume : Nat) : CReal :=
  couplingParametricCutoffFamilyEventProbabilityLimit
    (unitCubeBlockCoupling anchorCoupling)
    (unitCubeBlockCoupling_nonnegative (by decide))
    anchor_unitCubeBlockCoupling_le volume
    (familyContainsPolymerB (coarseUnitCubeBlockRootAt volume))

@[simp] theorem shiftedCoarseUnitCubeFixedVolumeCutoffLimit_approx
    (volume stage : Nat) :
    (shiftedCoarseUnitCubeFixedVolumeCutoffLimit volume).approx stage =
      couplingKFamilyEventProbability
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide))
        (interactingAdjacentCutoff stage volume) volume
        (familyContainsPolymerB
          (coarseUnitCubeBlockRootAt volume)) := rfl

theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_fixedVolumeCutoffLimit
    {volume : Nat} (hvolume : 4 ≤ volume) :
    CReal.ofQ' activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      shiftedCoarseUnitCubeFixedVolumeCutoffLimit volume := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  rw [shiftedCoarseUnitCubeFixedVolumeCutoffLimit_approx]
  exact
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_allCutoffPhysicalProbability
      (interactingAdjacentCutoff_ge_one stage volume) hvolume

theorem shiftedCoarseUnitCubeFixedVolumeCutoffLimit_pos
    {volume : Nat} (hvolume : 4 ≤ volume) :
    CReal.IsPositive
      (shiftedCoarseUnitCubeFixedVolumeCutoffLimit volume) :=
  ⟨activityMatchedCoarseUnitCubeUniformOccurrenceFloor,
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_pos,
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_fixedVolumeCutoffLimit
      hvolume⟩

#print axioms parametricKCutoffIncrement_mono_coupling
#print axioms parametricKEventCutoffIncrement_mono_coupling
#print axioms couplingParametricCutoffIncrement_le_two_halfPow
#print axioms couplingParametricEventCutoffIncrement_le_two_halfPow
#print axioms couplingParametricCutoffEventProbabilitySequence_step_abs_le
#print axioms couplingParametricCutoffEventProbabilityLimit
#print axioms couplingParametricCutoffEventProbabilityLimit_nonnegative
#print axioms couplingParametricCutoffEventProbabilityLimit_le_one
#print axioms couplingParametricCutoffFamilyEventProbabilityLimit_approx
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_fixedVolumeCutoffLimit
#print axioms shiftedCoarseUnitCubeFixedVolumeCutoffLimit_pos

end YMGap.Continuum.Z4CouplingParametricCutoffEventCofinal
