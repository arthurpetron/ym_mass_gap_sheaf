/-
# Entropy-times-decay factorization of the BF4 off-ray length-shell bound

The literal off-ray resistance shell estimate can be separated into two
physical inputs.  First, count the genuine source states whose canonical
simple root path uses a fixed directed edge and has a fixed length.  Second,
bound the stationary-weight times path-resistance load of every state in that
same literal shell.  Multiplying the two bounds gives the geometric shell
estimate required by the existing cofinal congestion compiler.

This module proves that multiplication and the ensuing compiler.  It does not
inhabit either input: the entropy and pointwise-decay estimates remain the
active BF4 analytic obligations.  In particular, the arbitrary canonical
simple path length has not yet been related to a monotone spin-mass peeling
statistic.  No continuum or Clay conclusion is asserted.  No `Classical`,
choice, `native_decide`, `sorry`, new axiom, or noncomputable declaration is
used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShell

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShellFactorization

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShell
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive finite-sum and power algebra -/

private theorem listQSum_le_length_mul_local {Item : Type}
    (value : Item → Q') {bound : Q'}
    (hbound0 : (0 : Q') ≤ bound) :
    ∀ items : List Item,
      (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _ =>
      Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := listQSum_le_length_mul_local value hbound0 tail
        (fun item hitem =>
          hbound item (List.mem_cons_of_mem head hitem))
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add hhead htail) ?_
      refine Q'.le_of_eqv (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv (Q'.ofNat tail.length * bound) bound)

private theorem mul_pow_eqv_local (left right : Q') :
    ∀ exponent : Nat,
      (left * right) ^ exponent ≈
        left ^ exponent * right ^ exponent
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | exponent + 1 => by
      have hinductive := mul_pow_eqv_local left right exponent
      show
        (left * right) * (left * right) ^ exponent ≈
          (left * left ^ exponent) *
            (right * right ^ exponent)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (left * right) _ _ hinductive) ?_
      calc
        (left * right) *
              (left ^ exponent * right ^ exponent) ≈
            left *
              (right *
                (left ^ exponent * right ^ exponent)) :=
          Q'.mul_assoc_eqv _ _ _
        _ ≈ left *
              ((right * left ^ exponent) *
                right ^ exponent) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                right (left ^ exponent)
                (right ^ exponent)))
        _ ≈ left *
              ((left ^ exponent * right) *
                right ^ exponent) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_right _ _
              (right ^ exponent)
              (Q'.mul_comm_eqv
                right (left ^ exponent)))
        _ ≈ left *
              (left ^ exponent *
                (right * right ^ exponent)) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_assoc_eqv
              (left ^ exponent) right
              (right ^ exponent))
        _ ≈ (left * left ^ exponent) *
              (right * right ^ exponent) :=
          Q'.eqv_symm
            (Q'.mul_assoc_eqv _ _ _)

/-! ## 2. The factorized physical input -/

/-- Separate physical bounds on the size and the pointwise load of every
literal edge-user path-length shell.  The combined ratio is the product of
the entropy base and the pointwise load ratio. -/
structure FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellFactorizedBound
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  entropyAmplitude : Q'
  entropyBase : Q'
  loadAmplitude : Q'
  loadRatio : Q'
  budget : Q'
  entropyAmplitude_nonnegative : (0 : Q') ≤ entropyAmplitude
  entropyBase_nonnegative : (0 : Q') ≤ entropyBase
  loadAmplitude_nonnegative : (0 : Q') ≤ loadAmplitude
  loadRatio_nonnegative : (0 : Q') ≤ loadRatio
  combinedRatio_lt_one : entropyBase * loadRatio < (1 : Q')
  budget_nonnegative : (0 : Q') ≤ budget
  geometric_step :
    entropyAmplitude * loadAmplitude +
        (entropyBase * loadRatio) * budget ≤ budget
  shellCardinality_le : ∀ K, start ≤ K → ∀ source target (shell : Nat),
    shell < centralLowerExcitedSpinCubeOffRayRootLengthShellCount
      w (Q'.le_of_lt hw) K →
    Q'.ofNat
        (centralLowerExcitedSpinCubeOffRayRootEdgeLengthShellStates
          w (Q'.le_of_lt hw) K source target shell).length ≤
      entropyAmplitude * entropyBase ^ shell
  stateLoad_le : ∀ K, start ≤ K → ∀ source target (shell state : Nat),
    shell < centralLowerExcitedSpinCubeOffRayRootLengthShellCount
      w (Q'.le_of_lt hw) K →
    state ∈ centralLowerExcitedSpinCubeOffRayRootEdgeLengthShellStates
      w (Q'.le_of_lt hw) K source target shell →
    centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
        w (Q'.le_of_lt hw) K state ≤
      loadAmplitude * loadRatio ^ shell

namespace FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellFactorizedBound

theorem shellLoad_le_combined
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellFactorizedBound
        hw)
    (K : Nat) (hK : family.start ≤ K) (source target shell : Nat)
    (hshell : shell <
      centralLowerExcitedSpinCubeOffRayRootLengthShellCount
        w (Q'.le_of_lt hw) K) :
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgeLengthShellLoad
        w (Q'.le_of_lt hw) K source target shell ≤
      (family.entropyAmplitude * family.loadAmplitude) *
        (family.entropyBase * family.loadRatio) ^ shell := by
  let states :=
    centralLowerExcitedSpinCubeOffRayRootEdgeLengthShellStates
      w (Q'.le_of_lt hw) K source target shell
  let value :=
    centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
      w (Q'.le_of_lt hw) K
  let pointBound := family.loadAmplitude * family.loadRatio ^ shell
  have hpointBound0 : (0 : Q') ≤ pointBound := by
    exact Q'.mul_nonneg _ _ family.loadAmplitude_nonnegative
      (Q'.pow_nonneg family.loadRatio family.loadRatio_nonnegative shell)
  have hsum : listQSum value states ≤
      Q'.ofNat states.length * pointBound := by
    apply listQSum_le_length_mul_local value hpointBound0 states
    intro state hstate
    exact family.stateLoad_le K hK source target shell state hshell hstate
  have hcardinality : Q'.ofNat states.length ≤
      family.entropyAmplitude * family.entropyBase ^ shell := by
    exact family.shellCardinality_le K hK source target shell hshell
  have hscaled : Q'.ofNat states.length * pointBound ≤
      (family.entropyAmplitude * family.entropyBase ^ shell) *
        pointBound :=
    Q'.mul_le_mul_of_nonneg_right _ _ pointBound
      hcardinality hpointBound0
  have hfactor :
      (family.entropyAmplitude * family.entropyBase ^ shell) *
          pointBound ≈
        (family.entropyAmplitude * family.loadAmplitude) *
          (family.entropyBase * family.loadRatio) ^ shell := by
    unfold pointBound
    calc
      (family.entropyAmplitude * family.entropyBase ^ shell) *
            (family.loadAmplitude * family.loadRatio ^ shell) ≈
          family.entropyAmplitude *
            (family.entropyBase ^ shell *
              (family.loadAmplitude * family.loadRatio ^ shell)) :=
        Q'.mul_assoc_eqv _ _ _
      _ ≈ family.entropyAmplitude *
            ((family.entropyBase ^ shell * family.loadAmplitude) *
              family.loadRatio ^ shell) :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      _ ≈ family.entropyAmplitude *
            ((family.loadAmplitude * family.entropyBase ^ shell) *
              family.loadRatio ^ shell) :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_comm_eqv _ _))
      _ ≈ family.entropyAmplitude *
            (family.loadAmplitude *
              (family.entropyBase ^ shell * family.loadRatio ^ shell)) :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_assoc_eqv _ _ _)
      _ ≈ (family.entropyAmplitude * family.loadAmplitude) *
            (family.entropyBase ^ shell * family.loadRatio ^ shell) :=
        Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      _ ≈ (family.entropyAmplitude * family.loadAmplitude) *
            (family.entropyBase * family.loadRatio) ^ shell :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm
            (mul_pow_eqv_local family.entropyBase family.loadRatio shell))
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceEdgeLengthShellLoad
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hfactor))

def toLengthShellBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellFactorizedBound
        hw) :
    FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellBound hw where
  start := family.start
  amplitude := family.entropyAmplitude * family.loadAmplitude
  ratio := family.entropyBase * family.loadRatio
  budget := family.budget
  amplitude_nonnegative := Q'.mul_nonneg _ _
    family.entropyAmplitude_nonnegative family.loadAmplitude_nonnegative
  ratio_nonnegative := Q'.mul_nonneg _ _
    family.entropyBase_nonnegative family.loadRatio_nonnegative
  ratio_lt_one := family.combinedRatio_lt_one
  budget_nonnegative := family.budget_nonnegative
  geometric_step := family.geometric_step
  shellLoad_le := family.shellLoad_le_combined

def toResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellFactorizedBound
        hw) :
    FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw :=
  family.toLengthShellBound.toResistanceCongestionBound

/-- The separate physical entropy and pointwise-decay inputs, together with
any cofinal ray capacity, construct the exact full-sector simple-routing
certificate. -/
def toSimpleRootResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellFactorizedBound
        hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) :
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
      hw :=
  family.toLengthShellBound.toSimpleRootResistanceCongestionBound ray

end FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellFactorizedBound

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShellFactorization

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShellFactorization.FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellFactorizedBound.shellLoad_le_combined
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShellFactorization.FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellFactorizedBound.toLengthShellBound
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShellFactorization.FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellFactorizedBound.toResistanceCongestionBound
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShellFactorization.FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellFactorizedBound.toSimpleRootResistanceCongestionBound
