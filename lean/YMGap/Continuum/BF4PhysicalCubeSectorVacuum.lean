/-
# Construct the stationary cube-sector vector from the physical measure

The canonical finite component indicators have a uniform unit envelope and
agree with the cutoff-independent sector event on each retained core. The
existing corrected-slab tail gives an explicit squared-norm Cauchy modulus.
Their limit belongs to the EXISTING marginal-sector cylinder completion and
its global image is exactly the bounded physical event observable.

The same core-tail estimate passes the event's exact finite stationarity to
the original completed conditional operator. Injectivity and the already
proved intertwining identify stationary vectors in the marginal and reflected
sector completions. No strict gap or geometric-time assertion is involved.
-/

import YMGap.Continuum.BF4PhysicalCubeSectorPrefix
import YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell

namespace YMGap.Continuum.BF4PhysicalCubeSectorVacuum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeSectorIndicator
open YMGap.Continuum.BF4PhysicalCubeSectorPrefix
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCoreTailCauchy
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffTargetShellTail
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "G" => centralPhysicalCutoffLinearSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "M" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "P" => centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "TM" => centralPhysicalVacuumSectorCylinderCompletedTransfer
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "I" => centralPhysicalVacuumSectorCylinderCompletionToGlobal
  (hw0 := (by decide : (0 : Q') < anchorCoupling))
  (hw1 := (by decide : anchorCoupling < (1 : Q'))) (half := 0)

def sectorLinearObservable : CentralPhysicalLinearObservable := .atom cubeSectorObservable

/-- The original physical tail schedule, not a presumed spectral rate. -/
def sectorTailRate (epsilon : Q') : Nat :=
  max 1 (centralPhysicalTargetShellCutoff anchorCoupling 0 epsilon)

private theorem unit_square_bound (left right : CentralPhysicalUnitObservable) (state : EdgeLabelling) :
    (left.value state + -right.value state) * (left.value state + -right.value state) ≤ (1 : Q') := by
  have ha := Q'.le_trans' _ _ _ (left.le_one state)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' 1)))
      (Q'.add_le_add_right _ _ 1 (right.nonnegative state)))
  have hb := Q'.le_trans' _ _ _ (right.le_one state)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' 1)))
      (Q'.add_le_add_right _ _ 1 (left.nonnegative state)))
  have habs := CReal.abs_sub_le_of_bounds ha hb
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
      (Q'.mul_le_mul_of_nonneg habs habs Q'.zero_le_one (Q'.abs_nonneg _))))
    (Q'.le_of_eqv (Q'.one_mul_eqv 1))

private theorem represented_unit_square_bound
    (left right : CentralPhysicalLinearObservable) (u v : CentralPhysicalUnitObservable)
    (hl : ∀ state, left.value state ≈ u.value state)
    (hr : ∀ state, right.value state ≈ v.value state) (state : EdgeLabelling) :
    (left.value state + -right.value state) * (left.value state + -right.value state) ≤ (1 : Q') := by
  have heq := Q'.add_eqv_congr' (hl state) (Q'.neg_eqv_congr _ _ (hr state))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ heq) (Q'.mul_eqv_congr_left _ _ _ heq)))
    (unit_square_bound u v state)

/-- Uniform original-index distance bound from exact core agreement and a
unit squared envelope. Both hypotheses are proved below for the actual data. -/
theorem coreApproximation (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (base : Nat) (hbase : sectorTailRate epsilon ≤ base)
    (left right : CentralPhysicalLinearObservable)
    (hcore : ∀ state, state ∈ centralPositiveHalfStates anchorCoupling (by decide) base 0 →
      left.value state ≈ right.value state)
    (henvelope : ∀ state,
      (left.value state + -right.value state) * (left.value state + -right.value state) ≤ (1 : Q')) :
    CReal.leEv ((G).distSq left right) (CReal.ofQ' epsilon) := by
  intro slack hslack
  refine ⟨base, fun later hlater => ?_⟩
  have hfinite := centralPhysicalFiniteDistSq_le_core_add_scaled_shell
    (w := anchorCoupling) (by decide) later 0 base left.value right.value 0 1 (Q'.le_refl' 0)
    (fun state hsupp hwithin hrow => by
      have hs : state ∈ centralPositiveHalfStates anchorCoupling (by decide) base 0 :=
        mem_centralPositiveHalfStates_iff.mpr ⟨boundedEdgeLabellings_complete base _ state
          ((labelWithinB_true_iff base _ state).mp hwithin) hsupp, hrow⟩
      have hz := Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (hcore state hs))
        (Q'.add_neg_self_eqv _)
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hz)
        (Q'.zero_mul_eqv _))) henvelope
  have hscheduled : centralPhysicalTargetShellCutoff anchorCoupling 0 epsilon ≤ base :=
    Nat.le_trans (Nat.le_max_right _ _) hbase
  have hshell := centralPhysicalRowMarginalOutsideBase_le_increment
    (half := 0) (w := anchorCoupling) (by decide) hlater
  have hmono := slabParametricKCutoffIncrement_antitone_base (extent := 1)
    (w := anchorCoupling) (by decide) hscheduled hlater
  have htail := slabPhysicalNomeCutoffIncrement_le_tolerance
    (w := anchorCoupling) (by decide) (by decide) 1 hepsilon (Nat.le_trans hscheduled hlater)
  have hbound := Q'.le_trans' _ _ _ hshell (Q'.le_trans' _ _ _ hmono htail)
  have hstage := physicalLinearDistSq_approx_eqv_stage (w := anchorCoupling)
    (by decide) (by decide) 0 later left right
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hstage) (Q'.le_trans' _ _ _ hfinite
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (Q'.zero_add' _)) (Q'.mul_one_eqv _)))
      (Q'.le_trans' _ _ _ hbound (Q'.add_le_self_of_nonneg _ slack (Q'.le_of_lt hslack)))))

private theorem half_mono {K L : Nat} (h : K ≤ L) (state : EdgeLabelling)
    (hs : state ∈ centralHalfStates K 0) : state ∈ centralHalfStates L 0 := by
  have hb := boundedEdgeLabellings_sound K (centralLowerFaceIds 0) state hs
  exact boundedEdgeLabellings_complete L _ state (fun face hf => by have := hb.1 face hf; omega) hb.2

def sectorVacuumCauchy : (M).Cauchy where
  seq := sectorPrefix
  modulus := sectorTailRate
  isCauchy := by
    intro epsilon hepsilon m n hm hn
    apply coreApproximation epsilon hepsilon (min m n) (Nat.le_min.mpr ⟨hm, hn⟩)
    · intro state hs
      have hhalf := (mem_centralPositiveHalfStates_iff.mp hs).1
      have hm1 : 1 ≤ m := Nat.le_trans (Nat.le_max_left _ _) hm
      have hn1 : 1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
      exact Q'.eqv_trans _ _ _
        (sectorPrefix_value_on_core m hm1 state (half_mono (Nat.min_le_left _ _) state hhalf))
        (Q'.eqv_symm (sectorPrefix_value_on_core n hn1 state
          (half_mono (Nat.min_le_right _ _) state hhalf)))
    · exact represented_unit_square_bound _ _ (prefixObservable m) (prefixObservable n)
        (sectorPrefix_value m) (sectorPrefix_value n)

def sectorVacuum : (M).Completion := Quotient.mk (M).completionSetoid sectorVacuumCauchy

def sectorVacuumGlobalClose : (G).Close
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal sectorVacuumCauchy)
    ((G).constant sectorLinearObservable) where
  modulus := sectorTailRate
  close := by
    intro epsilon hepsilon n hn
    apply coreApproximation epsilon hepsilon n hn
    · intro state hs
      exact sectorPrefix_value_on_core n (Nat.le_trans (Nat.le_max_left _ _) hn) state
        (mem_centralPositiveHalfStates_iff.mp hs).1
    · exact represented_unit_square_bound _ _ (prefixObservable n) cubeSectorObservable
        (sectorPrefix_value n) (fun _ => Q'.eqv_refl _)

theorem sectorVacuum_global : I sectorVacuum = (G).embedRep sectorLinearObservable :=
  Quotient.sound ⟨sectorVacuumGlobalClose⟩

def sectorActionClose : (G).Close
    (centralPhysicalLinearMarkovCutoffCauchy
      ((centralPhysicalDenseMarkovCauchyData (w := anchorCoupling) (by decide) (by decide) 0).modulus
        sectorLinearObservable)) ((G).constant sectorLinearObservable) where
  modulus := sectorTailRate
  close := by
    intro epsilon hepsilon n hn
    apply coreApproximation epsilon hepsilon n hn
    · intro state hs
      exact Q'.eqv_trans _ _ _ (centralPhysicalLinearMarkovCutoffAction_value_of_mem
        (w := anchorCoupling) (by decide) n 0 sectorLinearObservable state hs)
        (cubeSectorIndicator_markov_fixed anchorCoupling (by decide) n state hs)
    · exact unit_square_bound
        (centralPhysicalMarkovCutoffUnitObservable (w := anchorCoupling) (by decide) n 0 cubeSectorObservable)
        cubeSectorObservable

theorem globalSectorVacuum_fixed : P ((G).embedRep sectorLinearObservable) =
    (G).embedRep sectorLinearObservable := by
  exact Eq.trans (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_embed
    (w := anchorCoupling) (by decide) (by decide) 0 sectorLinearObservable)
    (Quotient.sound ⟨sectorActionClose⟩)

theorem sectorVacuum_fixed : TM sectorVacuum = sectorVacuum := by
  apply centralPhysicalVacuumSectorCylinderCompletionToGlobal_injective
  have h := (centralPhysicalVacuumSectorCylinderTransferLiftData
    (w := anchorCoupling) (by decide) (by decide) 0).intertwines sectorVacuum
  rw [sectorVacuum_global, globalSectorVacuum_fixed] at h
  exact Eq.trans h sectorVacuum_global.symm

def reflectedSectorVacuum : CubeReflectedCompletion := sectorToReflected sectorVacuum

theorem reflectedSectorVacuum_fixed : cubeTransfer reflectedSectorVacuum = reflectedSectorVacuum := by
  unfold reflectedSectorVacuum
  rw [cubeTransfer_sector]
  unfold mappedTransfer
  rw [sectorVacuum_fixed]

end YMGap.Continuum.BF4PhysicalCubeSectorVacuum

#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.sectorLinearObservable
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.sectorTailRate
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.coreApproximation
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.sectorVacuumCauchy
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.sectorVacuum
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.sectorVacuumGlobalClose
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.sectorVacuum_global
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.sectorActionClose
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.globalSectorVacuum_fixed
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.sectorVacuum_fixed
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.reflectedSectorVacuum
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorVacuum.reflectedSectorVacuum_fixed
