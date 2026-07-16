/-
# Cutoff-cofinal finite-box events at the strong-coupling anchor

An event in this module is an arbitrary decidable predicate on physical face
labellings.  Masking the exact coupling-parametric spin-foam summand preserves
cutoff stability and the exact old/new-sector decomposition.  At the derived
anchor `w = 1/400`, every event increment is bounded by the corresponding full
partition increment.  Thus every fixed finite-box event numerator has the
same explicit dyadic representation-cutoff modulus and a constructive-real
limit.

The second half normalizes by the actual positive partition and constructs the
corresponding cutoff-cofinal probability.  This is a fixed-box cutoff theorem;
simultaneous volume compatibility remains a separate step.
-/

import YMGap.Continuum.EndpointCutoffTwoParameter
import YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity

namespace YMGap.Continuum.Z4ParametricCutoffEventCofinal

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitSupportMultiplicityBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumFloor
open YMGap.Continuum.Z4FinitePartitionRelativeNormalization
open YMGap.Continuum.Z4InteractingCutoffCofinal
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem two_mul_eqv_local (x : Q') :
    Q'.ofNat 2 * x ≈ x + x := by
  refine Q'.eqv_trans _ ((Q'.ofNat 1 + Q'.ofNat 1) * x) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv 1 1)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 1 * x + Q'.ofNat 1 * x) _
    (Q'.add_mul_eqv (Q'.ofNat 1) (Q'.ofNat 1) x) ?_
  exact Q'.add_eqv_congr' (Q'.one_mul_eqv x) (Q'.one_mul_eqv x)

/-! ## 1. Masked finite-cutoff event weights -/

def parametricKEventTerm (w : Q') (K n : Nat)
    (event : EdgeLabelling → Bool) (physical : EdgeLabelling) : Q' :=
  if event physical then parametricKPhysicalTerm w K n physical else 0

def parametricKEventNumerator (w : Q') (K n : Nat)
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum (parametricKEventTerm w K n event)
    (boundedEdgeLabellings K (List.range (plaquetteEdgeCount n)))

def parametricKEventCutoffIncrement (w : Q') (K L n : Nat)
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum (parametricKEventTerm w L n event)
    ((boundedEdgeLabellings L (List.range (plaquetteEdgeCount n))).filter
      (fun physical =>
        !(labelWithinB K (List.range (plaquetteEdgeCount n)) physical)))

theorem parametricKEventTerm_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K n : Nat)
    (event : EdgeLabelling → Bool) (physical : EdgeLabelling) :
    (0 : Q') ≤ parametricKEventTerm w K n event physical := by
  unfold parametricKEventTerm
  by_cases hevent : event physical = true
  · rw [if_pos hevent]
    exact parametricKPhysicalTerm_nonnegative hw K n physical
  · rw [if_neg hevent]
    exact Q'.le_refl' 0

private theorem listQSum_nonnegative_local {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ xs : List A, (0 : Q') ≤ listQSum value xs
  | [] => Q'.le_refl' 0
  | head :: tail => Q'.zero_le_add _ _ (hvalue head)
      (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ xs : List A,
      (∀ x, x ∈ xs → left x ≤ right x) →
      listQSum left xs ≤ listQSum right xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun x hx => hle x (List.mem_cons_of_mem head hx)))

theorem parametricKEventNumerator_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K n : Nat)
    (event : EdgeLabelling → Bool) :
    (0 : Q') ≤ parametricKEventNumerator w K n event := by
  unfold parametricKEventNumerator
  exact listQSum_nonnegative_local _
    (parametricKEventTerm_nonnegative hw K n event) _

theorem parametricKEventCutoffIncrement_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K L n : Nat)
    (event : EdgeLabelling → Bool) :
    (0 : Q') ≤ parametricKEventCutoffIncrement w K L n event := by
  unfold parametricKEventCutoffIncrement
  exact listQSum_nonnegative_local _
    (parametricKEventTerm_nonnegative hw L n event) _

theorem parametricKEventTerm_le_physicalTerm
    {w : Q'} (hw : (0 : Q') ≤ w) (K n : Nat)
    (event : EdgeLabelling → Bool) (physical : EdgeLabelling) :
    parametricKEventTerm w K n event physical ≤
      parametricKPhysicalTerm w K n physical := by
  unfold parametricKEventTerm
  by_cases hevent : event physical = true
  · rw [if_pos hevent]
    exact Q'.le_refl' _
  · rw [if_neg hevent]
    exact parametricKPhysicalTerm_nonnegative hw K n physical

theorem parametricKEventNumerator_le_partition
    {w : Q'} (hw : (0 : Q') ≤ w) (K n : Nat)
    (event : EdgeLabelling → Bool) :
    parametricKEventNumerator w K n event ≤
      parametricKPhysicalPartition w K n := by
  unfold parametricKEventNumerator parametricKPhysicalPartition
  apply listQSum_le_termwise_local
  intro physical _
  exact parametricKEventTerm_le_physicalTerm hw K n event physical

theorem parametricKEventCutoffIncrement_le_partitionIncrement
    {w : Q'} (hw : (0 : Q') ≤ w) (K L n : Nat)
    (event : EdgeLabelling → Bool) :
    parametricKEventCutoffIncrement w K L n event ≤
      parametricKCutoffIncrement w K L n := by
  unfold parametricKEventCutoffIncrement parametricKCutoffIncrement
  apply listQSum_le_termwise_local
  intro physical _
  exact parametricKEventTerm_le_physicalTerm hw L n event physical

/-! ## 2. Exact cutoff stability and sector decomposition -/

theorem parametricKEventTerm_cutoff_stable
    {w : Q'} {K L n : Nat} {event : EdgeLabelling → Bool}
    {physical : EdgeLabelling} (hKL : K ≤ L)
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    parametricKEventTerm w L n event physical =
      parametricKEventTerm w K n event physical := by
  unfold parametricKEventTerm
  by_cases hevent : event physical = true
  · rw [if_pos hevent, if_pos hevent,
      parametricKPhysicalTerm_cutoff_stable hKL hphysical]
  · rw [if_neg hevent, if_neg hevent]

private theorem range_nodup_local (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyN : y = N := List.mem_singleton.mp hy
      rw [hxy, hyN] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl N)

theorem parametricKEventNumerator_eq_base_add_increment
    {w : Q'} {K L n : Nat} {event : EdgeLabelling → Bool}
    (hKL : K ≤ L) :
    parametricKEventNumerator w L n event ≈
      parametricKEventNumerator w K n event +
        parametricKEventCutoffIncrement w K L n event := by
  let edges := List.range (plaquetteEdgeCount n)
  let oldTest := labelWithinB K edges
  let largeSupport := boundedEdgeLabellings L edges
  let smallSupport := boundedEdgeLabellings K edges
  have hfilter : largeSupport.filter oldTest = smallSupport := by
    dsimp only [largeSupport, smallSupport, oldTest, edges]
    exact boundedEdgeLabellings_filter_cutoff hKL _ (range_nodup_local _)
  have hcommon :
      listQSum (parametricKEventTerm w L n event)
          (largeSupport.filter oldTest) ≈
        listQSum (parametricKEventTerm w K n event) smallSupport := by
    rw [hfilter]
    apply listQSum_congr_on
    intro physical hphysical
    exact Q'.eqv_of_eq
      (parametricKEventTerm_cutoff_stable hKL hphysical)
  have hsplit :
      listQSum (parametricKEventTerm w L n event) largeSupport ≈
        listQSum (parametricKEventTerm w L n event)
            (largeSupport.filter oldTest) +
          parametricKEventCutoffIncrement w K L n event := by
    have h := listQSum_filter_partition
      (parametricKEventTerm w L n event) oldTest largeSupport
    simpa [parametricKEventCutoffIncrement, largeSupport, oldTest, edges]
      using h
  unfold parametricKEventNumerator
  dsimp only [largeSupport, smallSupport, edges] at hcommon hsplit ⊢
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr' hcommon (Q'.eqv_refl _))

theorem parametricKEventNumerator_mono
    {w : Q'} (hw : (0 : Q') ≤ w) {K L n : Nat}
    {event : EdgeLabelling → Bool} (hKL : K ≤ L) :
    parametricKEventNumerator w K n event ≤
      parametricKEventNumerator w L n event := by
  have hinc := parametricKEventCutoffIncrement_nonnegative
    hw K L n event
  have hadd : parametricKEventNumerator w K n event ≤
      parametricKEventNumerator w K n event +
        parametricKEventCutoffIncrement w K L n event :=
    Q'.add_le_self_of_nonneg _ _ hinc
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv (parametricKEventNumerator_eq_base_add_increment hKL))

theorem parametricKEventNumerator_difference_eq_increment
    {w : Q'} {K L n : Nat} {event : EdgeLabelling → Bool}
    (hKL : K ≤ L) :
    parametricKEventNumerator w L n event +
        -parametricKEventNumerator w K n event ≈
      parametricKEventCutoffIncrement w K L n event := by
  let NK := parametricKEventNumerator w K n event
  let NL := parametricKEventNumerator w L n event
  let increment := parametricKEventCutoffIncrement w K L n event
  have hdecomp : NL ≈ NK + increment :=
    parametricKEventNumerator_eq_base_add_increment hKL
  refine Q'.eqv_trans _ ((NK + increment) + -NK) _
    (Q'.add_eqv_congr' hdecomp (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _ (NK + (increment + -NK)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (NK + (-NK + increment)) _
    (Q'.add_eqv_congr_left NK _ _
      (Q'.add_comm_eqv increment (-NK))) ?_
  refine Q'.eqv_trans _ ((NK + -NK) + increment) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + increment) _
    (Q'.add_eqv_congr_right _ _ increment
      (Q'.add_neg_self_eqv NK)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' increment)

/-! ## 3. Anchor event tail and constructive-real numerator -/

theorem anchorParametricEventCutoffIncrement_le_two_halfPow
    (stage depth n : Nat) (event : EdgeLabelling → Bool) :
    parametricKEventCutoffIncrement anchorCoupling
        (interactingAdjacentCutoff stage n)
        (interactingAdjacentCutoff stage n + depth) n event ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  exact Q'.le_trans' _ _ _
    (parametricKEventCutoffIncrement_le_partitionIncrement
      (by decide) _ _ _ event)
    (anchorParametricCutoffIncrement_le_two_halfPow stage depth n)

theorem anchorParametricEventAdjacentIncrement_le_halfPow
    (stage n : Nat) (event : EdgeLabelling → Bool) :
    parametricKEventCutoffIncrement anchorCoupling
        (interactingAdjacentCutoff stage n)
        (interactingAdjacentCutoff stage n + 1) n event ≤
      HalfPow.half ^ stage := by
  exact Q'.le_trans' _ _ _
    (parametricKEventCutoffIncrement_le_partitionIncrement
      (by decide) _ _ _ event)
    (anchorParametricAdjacentIncrement_le_halfPow stage n)

def anchorParametricCutoffEventNumeratorSequence
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) : Q' :=
  parametricKEventNumerator anchorCoupling
    (interactingAdjacentCutoff stage n) n event

theorem anchorParametricCutoffEventNumeratorSequence_step_eqv
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    anchorParametricCutoffEventNumeratorSequence n event (stage + 1) ≈
      anchorParametricCutoffEventNumeratorSequence n event stage +
        parametricKEventCutoffIncrement anchorCoupling
          (interactingAdjacentCutoff stage n)
          (interactingAdjacentCutoff stage n + 1) n event := by
  have hcutoff : interactingAdjacentCutoff (stage + 1) n =
      interactingAdjacentCutoff stage n + 1 := by
    unfold interactingAdjacentCutoff
    omega
  unfold anchorParametricCutoffEventNumeratorSequence
  rw [hcutoff]
  exact parametricKEventNumerator_eq_base_add_increment (by omega)

theorem anchorParametricCutoffEventNumeratorSequence_step_upper
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    anchorParametricCutoffEventNumeratorSequence n event (stage + 1) ≤
      anchorParametricCutoffEventNumeratorSequence n event stage +
        geoIncr 1 stage := by
  have heq := anchorParametricCutoffEventNumeratorSequence_step_eqv
    n event stage
  have hinc := anchorParametricEventAdjacentIncrement_le_halfPow
    stage n event
  have hgeo : HalfPow.half ^ stage ≤ geoIncr 1 stage :=
    Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ hinc hgeo))

theorem anchorParametricCutoffEventNumeratorSequence_step_lower
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    anchorParametricCutoffEventNumeratorSequence n event stage ≤
      anchorParametricCutoffEventNumeratorSequence n event (stage + 1) +
        geoIncr 1 stage := by
  have hcutoff : interactingAdjacentCutoff stage n ≤
      interactingAdjacentCutoff (stage + 1) n := by
    unfold interactingAdjacentCutoff
    omega
  have hmono : anchorParametricCutoffEventNumeratorSequence n event stage ≤
      anchorParametricCutoffEventNumeratorSequence n event (stage + 1) := by
    unfold anchorParametricCutoffEventNumeratorSequence
    exact parametricKEventNumerator_mono (by decide) hcutoff
  exact Q'.le_trans' _ _ _ hmono
    (Q'.add_le_self_of_nonneg _ _
      (geoIncr_nonneg 1 Q'.zero_le_one stage))

def anchorParametricCutoffEventNumeratorLimit
    (n : Nat) (event : EdgeLabelling → Bool) : CReal :=
  crealOfGeoIncrement
    (anchorParametricCutoffEventNumeratorSequence n event)
    1 Q'.zero_le_one
    (anchorParametricCutoffEventNumeratorSequence_step_upper n event)
    (anchorParametricCutoffEventNumeratorSequence_step_lower n event)
    (fun ε hε => by
      refine ⟨HalfPow.half * ε, ExpNeg.half_mul_pos ε hε, ?_⟩
      show (Q'.ofNat 2 * 1) * (HalfPow.half * ε) ≤ ε
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ (Q'.ofNat 2 * (HalfPow.half * ε)) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_one_eqv (Q'.ofNat 2))) ?_
      refine Q'.eqv_trans _ ((Q'.ofNat 2 * HalfPow.half) * ε) _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv (Q'.ofNat 2) HalfPow.half ε)) ?_
      refine Q'.eqv_trans _ ((1 : Q') * ε) _
        (Q'.mul_eqv_congr_right _ _ _ (by decide)) ?_
      exact Q'.one_mul_eqv ε)

@[simp] theorem anchorParametricCutoffEventNumeratorLimit_approx
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    (anchorParametricCutoffEventNumeratorLimit n event).approx stage =
      anchorParametricCutoffEventNumeratorSequence n event stage := rfl

/-! ## 4. Normalized cutoff-cofinal event probabilities -/

private theorem interactingAdjacentCutoff_ge_one_local
    (stage n : Nat) : 1 ≤ interactingAdjacentCutoff stage n := by
  unfold interactingAdjacentCutoff
  omega

def anchorParametricCutoffEventProbabilitySequence
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) : Q' :=
  Q'.divPos
    (parametricKEventNumerator anchorCoupling
      (interactingAdjacentCutoff stage n) n event)
    (parametricKPhysicalPartition anchorCoupling
      (interactingAdjacentCutoff stage n) n)
    (anchorParametricPartition_pos
      (interactingAdjacentCutoff_ge_one_local stage n) n)

theorem anchorParametricCutoffEventProbabilitySequence_nonnegative
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    (0 : Q') ≤
      anchorParametricCutoffEventProbabilitySequence n event stage := by
  unfold anchorParametricCutoffEventProbabilitySequence Q'.divPos
  exact Q'.mul_nonneg _ _
    (parametricKEventNumerator_nonnegative (by decide) _ _ event)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (anchorParametricPartition_pos
          (interactingAdjacentCutoff_ge_one_local stage n) n)))

theorem anchorParametricCutoffEventProbabilitySequence_le_one
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    anchorParametricCutoffEventProbabilitySequence n event stage ≤
      (1 : Q') := by
  unfold anchorParametricCutoffEventProbabilitySequence
  apply Q'.divPos_le_of_le_mul
  have hnum := parametricKEventNumerator_le_partition
    (w := anchorCoupling) (by decide)
    (interactingAdjacentCutoff stage n) n event
  exact Q'.le_trans' _ _ _ hnum
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (parametricKPhysicalPartition anchorCoupling
          (interactingAdjacentCutoff stage n) n)))

/-- A cutoff-independent upper bound for the scheduled partitions in one
fixed box.  It is deliberately coarse but finite and fully derived. -/
def anchorParametricCutoffPartitionUniformBound (n : Nat) : Q' :=
  anchorParametricCutoffPartitionSequence n 0 + Q'.ofNat 2

theorem anchorParametricCutoffPartitionUniformBound_nonnegative (n : Nat) :
    (0 : Q') ≤ anchorParametricCutoffPartitionUniformBound n := by
  unfold anchorParametricCutoffPartitionUniformBound
  have hZ : (0 : Q') ≤ anchorParametricCutoffPartitionSequence n 0 := by
    exact Q'.le_trans' _ _ _ (by decide)
      (anchorParametricPartition_one_le
        (interactingAdjacentCutoff_ge_one_local 0 n) n)
  exact Q'.zero_le_add _ _ hZ (by decide)

theorem anchorParametricCutoffPartitionSequence_le_uniformBound
    (n stage : Nat) :
    anchorParametricCutoffPartitionSequence n stage ≤
      anchorParametricCutoffPartitionUniformBound n := by
  have hschedule : interactingAdjacentCutoff stage n =
      interactingAdjacentCutoff 0 n + stage := by
    unfold interactingAdjacentCutoff
    omega
  unfold anchorParametricCutoffPartitionSequence
    anchorParametricCutoffPartitionUniformBound
  rw [hschedule]
  have hdecomp := parametricKPhysicalPartition_eq_base_add_increment
    (w := anchorCoupling)
    (K := interactingAdjacentCutoff 0 n)
    (L := interactingAdjacentCutoff 0 n + stage)
    (n := n) (by omega)
  have hinc := anchorParametricCutoffIncrement_le_two_halfPow 0 stage n
  have hincTwo :
      parametricKCutoffIncrement anchorCoupling
          (interactingAdjacentCutoff 0 n)
          (interactingAdjacentCutoff 0 n + stage) n ≤
        Q'.ofNat 2 := by
    exact Q'.le_trans' _ _ _ hinc
      (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.ofNat 2)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdecomp)
    (Q'.add_le_add_left _ _ _ hincTwo)

def anchorParametricCutoffProbabilityStepConstant (n : Nat) : Q' :=
  Q'.ofNat 2 * anchorParametricCutoffPartitionUniformBound n

theorem anchorParametricCutoffProbabilityStepConstant_nonnegative
    (n : Nat) :
    (0 : Q') ≤ anchorParametricCutoffProbabilityStepConstant n := by
  unfold anchorParametricCutoffProbabilityStepConstant
  exact Q'.mul_nonneg _ _ (by decide)
    (anchorParametricCutoffPartitionUniformBound_nonnegative n)

theorem anchorParametricCutoffEventProbabilitySequence_step_abs_le
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    Q'.abs
        (anchorParametricCutoffEventProbabilitySequence n event stage +
          -anchorParametricCutoffEventProbabilitySequence n event
            (stage + 1)) ≤
      geoIncr (anchorParametricCutoffProbabilityStepConstant n) stage := by
  let K := interactingAdjacentCutoff stage n
  let L := K + 1
  let a := parametricKEventNumerator anchorCoupling K n event
  let A := parametricKEventNumerator anchorCoupling L n event
  let d := parametricKPhysicalPartition anchorCoupling K n
  let D := parametricKPhysicalPartition anchorCoupling L n
  let e := HalfPow.half ^ stage
  let B := anchorParametricCutoffPartitionUniformBound n
  have hcutoffSucc : interactingAdjacentCutoff (stage + 1) n = L := by
    dsimp only [L, K]
    unfold interactingAdjacentCutoff
    omega
  have hKone : 1 ≤ K := by
    dsimp only [K]
    exact interactingAdjacentCutoff_ge_one_local stage n
  have hLone : 1 ≤ L := by omega
  have ha0 : (0 : Q') ≤ a := by
    dsimp only [a]
    exact parametricKEventNumerator_nonnegative (by decide) K n event
  have hA0 : (0 : Q') ≤ A := by
    dsimp only [A]
    exact parametricKEventNumerator_nonnegative (by decide) L n event
  have hd1 : (1 : Q') ≤ d := by
    dsimp only [d]
    exact anchorParametricPartition_one_le hKone n
  have hD1 : (1 : Q') ≤ D := by
    dsimp only [D]
    exact anchorParametricPartition_one_le hLone n
  have hKL : K ≤ L := by omega
  have haA : a ≤ A := by
    dsimp only [a, A]
    exact parametricKEventNumerator_mono (by decide) hKL
  have hdD : d ≤ D := by
    dsimp only [d, D]
    exact parametricKPhysicalPartition_mono (by decide) hKL
  have he0 : (0 : Q') ≤ e := by
    dsimp only [e]
    exact Q'.pow_nonneg _ HalfPow.half_nonneg stage
  have hAdef : A - a ≤ e := by
    change A + -a ≤ e
    have heq := parametricKEventNumerator_difference_eq_increment
      (w := anchorCoupling) (K := K) (L := L) (n := n)
      (event := event) hKL
    have hinc : parametricKEventCutoffIncrement anchorCoupling
        K L n event ≤ e := by
      dsimp only [L, K, e]
      exact anchorParametricEventAdjacentIncrement_le_halfPow stage n event
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hinc
  have hDdef : D - d ≤ e := by
    change D + -d ≤ e
    have heq := parametricKPhysicalPartition_difference_eq_increment
      (w := anchorCoupling) (K := K) (L := L) (n := n) hKL
    have hinc : parametricKCutoffIncrement anchorCoupling K L n ≤ e := by
      dsimp only [L, K, e]
      exact anchorParametricAdjacentIncrement_le_halfPow stage n
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
    exact anchorParametricCutoffPartitionSequence_le_uniformBound
      n (stage + 1)
  have hA_D : A ≤ D := by
    dsimp only [A, D]
    exact parametricKEventNumerator_le_partition
      (w := anchorCoupling) (by decide) L n event
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
      (Q'.add_eqv_congr' (Q'.mul_comm_eqv e B) (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ ((B + B) * e) _
      (Q'.eqv_symm (Q'.add_mul_eqv B B e)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (two_mul_eqv_local B))
  have hratioSequence :
      Q'.abs
          (anchorParametricCutoffEventProbabilitySequence n event stage +
            -anchorParametricCutoffEventProbabilitySequence n event
              (stage + 1)) ≤
        e * D + A * e := by
    dsimp only [a, A, d, D] at hratioAbs
    simpa only [anchorParametricCutoffEventProbabilitySequence,
      hcutoffSucc, K, L, A, D] using hratioAbs
  refine Q'.le_trans' _ _ _ hratioSequence
    (Q'.le_trans' _ _ _ hbudget ?_)
  unfold geoIncr anchorParametricCutoffProbabilityStepConstant
  dsimp only [B, e]
  exact Q'.le_refl' _

private theorem two_sided_add_of_abs_sub_le_local {a b epsilon : Q'}
    (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

theorem anchorParametricCutoffEventProbabilitySequence_step_upper
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    anchorParametricCutoffEventProbabilitySequence n event (stage + 1) ≤
      anchorParametricCutoffEventProbabilitySequence n event stage +
        geoIncr (anchorParametricCutoffProbabilityStepConstant n) stage := by
  exact (two_sided_add_of_abs_sub_le_local
    (anchorParametricCutoffEventProbabilitySequence_step_abs_le
      n event stage)).2

theorem anchorParametricCutoffEventProbabilitySequence_step_lower
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    anchorParametricCutoffEventProbabilitySequence n event stage ≤
      anchorParametricCutoffEventProbabilitySequence n event (stage + 1) +
        geoIncr (anchorParametricCutoffProbabilityStepConstant n) stage := by
  exact (two_sided_add_of_abs_sub_le_local
    (anchorParametricCutoffEventProbabilitySequence_step_abs_le
      n event stage)).1

def anchorParametricCutoffEventProbabilityLimit
    (n : Nat) (event : EdgeLabelling → Bool) : CReal :=
  crealOfGeoIncrement
    (anchorParametricCutoffEventProbabilitySequence n event)
    (anchorParametricCutoffProbabilityStepConstant n)
    (anchorParametricCutoffProbabilityStepConstant_nonnegative n)
    (anchorParametricCutoffEventProbabilitySequence_step_upper n event)
    (anchorParametricCutoffEventProbabilitySequence_step_lower n event)
    (fun ε hε => by
      let coefficient := Q'.ofNat 2 *
        anchorParametricCutoffProbabilityStepConstant n
      have hcoefficient : (0 : Q') ≤ coefficient := by
        dsimp only [coefficient]
        exact Q'.mul_nonneg _ _ (by decide)
          (anchorParametricCutoffProbabilityStepConstant_nonnegative n)
      let δ := ε * Q'.invSucc coefficient.num.toNat
      have hδ : (0 : Q') < δ := by
        dsimp only [δ]
        exact Q'.mul_pos hε (Q'.invSucc_pos coefficient.num.toNat)
      refine ⟨δ, hδ, ?_⟩
      exact ExpNeg.mul_le_of_mul_invSucc_toNat coefficient ε
        hcoefficient (Q'.le_of_lt hε))

@[simp] theorem anchorParametricCutoffEventProbabilityLimit_approx
    (n : Nat) (event : EdgeLabelling → Bool) (stage : Nat) :
    (anchorParametricCutoffEventProbabilityLimit n event).approx stage =
      anchorParametricCutoffEventProbabilitySequence n event stage := rfl

end YMGap.Continuum.Z4ParametricCutoffEventCofinal

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ParametricCutoffEventCofinal.parametricKEventNumerator_eq_base_add_increment
#print axioms YMGap.Continuum.Z4ParametricCutoffEventCofinal.parametricKEventNumerator_le_partition
#print axioms YMGap.Continuum.Z4ParametricCutoffEventCofinal.anchorParametricEventAdjacentIncrement_le_halfPow
#print axioms YMGap.Continuum.Z4ParametricCutoffEventCofinal.anchorParametricCutoffEventNumeratorLimit
#print axioms YMGap.Continuum.Z4ParametricCutoffEventCofinal.anchorParametricCutoffEventProbabilitySequence_step_abs_le
#print axioms YMGap.Continuum.Z4ParametricCutoffEventCofinal.anchorParametricCutoffEventProbabilityLimit
