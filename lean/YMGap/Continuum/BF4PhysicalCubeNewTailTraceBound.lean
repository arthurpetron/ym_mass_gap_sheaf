/-
# The actual new-block centered tail has an explicit uniform small bound

Every genuinely new sector index beyond base cutoff B represents a state
of radius > B. The original indexed self-return equals the existing physical
conditional diagonal. A constructive weighted injection puts the complete
new-block trace below the proved high-label trace.

For epsilon>0, base=1400+epsilon.den therefore bounds the actual centered
new-tail form by epsilon times its own stationary diagonal norm at EVERY
later cutoff. The old head estimate remains open: this does not supply an
all-vector rate below one, geometric time, or continuum Yang--Mills.
-/

import YMGap.Continuum.BF4PhysicalCubeHighLabelTrace
import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredHeadTailTraceGap

namespace YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeBalancedDescent
open YMGap.Continuum.BF4PhysicalCubeGaussianReturn
open YMGap.Continuum.BF4PhysicalCubeHighLabelTrace
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredHeadTailTraceGap
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment
open YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap
open YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- A genuinely new state cannot fit the old cutoff: the exact cube-sector
classification would otherwise put its index in the embedded old image. -/
theorem newBlock_radius_gt {w : Q'} (hw : (0 : Q') < w) (base later : Nat)
    (hbase : 1 ≤ base) (hcutoff : base ≤ later) {index : Nat}
    (hi : index ∈ centralPhysicalFiniteVacuumSectorNewBlockIndices w (Q'.le_of_lt hw) base later 0) :
    base < radius (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) later 0 index) := by
  have hm := mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hi
  let state := centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) later 0 index
  have hs : state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) later 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index _ _ _ _ hm.1 rfl
  have hp := vacuumSector_cubeSupportedCommonParity w (Q'.le_of_lt hw) later hs
  by_cases hsmall : radius state ≤ base
  · have hold := cubeSupportedCommonParity_mem_sector hw base hbase state
      (fun face hf => Nat.le_trans (label_le_radius state face hf) hsmall) hp
    obtain ⟨old, ho, he⟩ := List.mem_map.mp hold
    have holt := centralPhysicalFiniteVacuumSectorIndex_lt w (Q'.le_of_lt hw) base 0 ho
    have hmap : centralPhysicalFiniteCutoffIndexMap w (Q'.le_of_lt hw) base later 0 old = index :=
      centralPhysicalFiniteStateAt_injective_of_lt
        (centralPhysicalFiniteCutoffIndexMap_lt hcutoff holt)
        (centralPhysicalFiniteVacuumSectorIndex_lt w (Q'.le_of_lt hw) later 0 hm.1)
        ((centralPhysicalFiniteStateAt_cutoffIndexMap_eq hcutoff holt).trans he)
    exact False.elim (hm.2 (List.mem_map.mpr ⟨old, ho, hmap⟩))
  · change base < radius state
    omega

/-- Exact identification, including the original normalized joint and its
own marginal; no change of dynamics or normalization. -/
theorem selfReturnProbability_eq_conditional (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {index : Nat} (hi : index ∈ centralPhysicalFiniteVacuumSectorIndices w hw K half) :
    centralPhysicalFiniteVacuumSectorSelfReturnProbability w hw K half index =
      centralPhysicalConditionalKernel w hw K half
        (centralPhysicalFiniteStateAt w hw K half index)
        (centralPhysicalFiniteStateAt w hw K half index) := by
  unfold centralPhysicalFiniteVacuumSectorSelfReturnProbability
  rw [dif_pos hi, centralPhysicalConditionalKernel_eq_divPos
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hi)]
  rfl

/-- The complete existing new-block trace is bounded by the literal
high-label trace on the same later-cutoff sector. -/
theorem newTailSelfReturnTrace_le_highLabel {w : Q'} (hw : (0 : Q') < w) (base later : Nat)
    (hbase : 1 ≤ base) (hcutoff : base ≤ later) :
    centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace w (Q'.le_of_lt hw) base later 0 ≤
      highLabelTrace w (Q'.le_of_lt hw) later (base + 1) := by
  apply listQSum_le_of_injective_nodup
    (centralPhysicalFiniteVacuumSectorNewBlockIndices w (Q'.le_of_lt hw) base later 0)
    (centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) later 0)
    (centralPhysicalFiniteVacuumSectorSelfReturnProbability w (Q'.le_of_lt hw) later 0)
    (fun state => if base + 1 ≤ radius state then
      centralPhysicalConditionalKernel w (Q'.le_of_lt hw) later 0 state state else 0)
    (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) later 0)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices_nodup _ _ _ _ _)
    (vacuumSectorStates_nodup _ _ _ _)
  · intro index hi
    exact centralPhysicalFiniteVacuumSectorState_mem_of_index _ _ _ _
      (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hi).1 rfl
  · intro left hl right hr he
    exact centralPhysicalFiniteStateAt_injective_of_lt
      (centralPhysicalFiniteVacuumSectorIndex_lt _ _ _ _
        (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hl).1)
      (centralPhysicalFiniteVacuumSectorIndex_lt _ _ _ _
        (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hr).1) he
  · intro index hi
    have hbound : base + 1 ≤ radius (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) later 0 index) := by
      have h := newBlock_radius_gt hw base later hbase hcutoff hi
      omega
    rw [if_pos hbound]
    exact Q'.le_of_eqv (Q'.eqv_of_eq (selfReturnProbability_eq_conditional _ _ _ _
      (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hi).1))
  · intro state _
    split
    · exact centralPhysicalConditionalKernel_nonnegative (Q'.le_of_lt hw) later 0 state state
    · exact Q'.le_refl' 0

/-- The OLD named centered trace input now has a proved cutoff-uniform
Gaussian majorant, for every base>=1399 and every later admitting cutoff. -/
theorem newTailTraceRate_le_gaussian {w : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ HalfPow.half)
    (base later : Nat) (hbase : 1399 ≤ base) (hcutoff : base ≤ later) :
    centralPhysicalFiniteVacuumSectorExactNewTailTraceRate w (Q'.le_of_lt hw0) base later 0 ≤
      Q'.ofNat 2 * radialEnvelope w (base + 1) :=
  Q'.le_trans' _ _ _ (centralPhysicalFiniteVacuumSectorExactNewTailTraceRate_le_selfReturnTrace _ _ _ _ _)
    (Q'.le_trans' _ _ _ (newTailSelfReturnTrace_le_highLabel hw0 base later (by omega) hcutoff)
      (highLabelTrace_le_radial hw0 hw later (base + 1) (by omega)))

/-- Computed old cutoff for the existing old/new decomposition. -/
def newTailBase (epsilon : Q') : Nat := 1400 + epsilon.den

theorem newTailTraceRate_small {w : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ HalfPow.half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (later : Nat) (hlater : newTailBase epsilon ≤ later) :
    centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
      w (Q'.le_of_lt hw0) (newTailBase epsilon) later 0 ≤ epsilon := by
  refine Q'.le_trans' _ _ _ (centralPhysicalFiniteVacuumSectorExactNewTailTraceRate_le_selfReturnTrace _ _ _ _ _) ?_
  refine Q'.le_trans' _ _ _ (newTailSelfReturnTrace_le_highLabel hw0 (newTailBase epsilon) later
    (by unfold newTailBase; omega) hlater) ?_
  have hi : newTailBase epsilon + 1 = radialTailCutoff epsilon := by unfold newTailBase radialTailCutoff; omega
  rw [hi]
  exact highLabelTrace_small hw0 hw epsilon he later

/-- Unconditional full-form control on EVERY literal new-tail coefficient,
using its own later-cutoff stationary diagonal norm. The trace input has
been proved rather than supplied as a new hypothesis. -/
theorem centered_newTail_le {w : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ HalfPow.half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (later : Nat) (hlater : newTailBase epsilon ≤ later)
    (coefficient : Nat → Q') :
    let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData w (Q'.le_of_lt hw0) later 0
    let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
      w (Q'.le_of_lt hw0) (newTailBase epsilon) later 0 coefficient
    D.B tail tail ≤ epsilon * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
      w (Q'.le_of_lt hw0) later 0 tail :=
  centralPhysicalFiniteVacuumSectorCenteredNewTailCoefficient_le_of_traceBound _ _ _ _ _ _ _
    (newTailTraceRate_small hw0 hw epsilon he later hlater)

/-- The existing physical head--tail compiler with its trace obligation
discharged. The sufficient centered HEAD estimate is still an explicit
open input; no q+epsilon<1 is asserted without proving that head bound. -/
theorem matrix_le_of_head {w : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ HalfPow.half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (later : Nat) (hlater : newTailBase epsilon ≤ later)
    (coefficient : Nat → Q') (q : Q') (hq : (0 : Q') ≤ q)
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean w (Q'.le_of_lt hw0) later 0 coefficient ≈ 0)
    (hhead :
      let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData w (Q'.le_of_lt hw0) later 0
      let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
        w (Q'.le_of_lt hw0) (newTailBase epsilon) later 0 coefficient
      D.B head head ≤ q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0 head) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic w (Q'.le_of_lt hw0) later 0 coefficient ≤
      (q + epsilon) * centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0 coefficient :=
  centralPhysicalFiniteVacuumSectorMatrix_le_of_centeredHead_trace _ _ _ _ _ _ _ _
    hq (Q'.le_of_lt he) hcenter hhead (newTailTraceRate_small hw0 hw epsilon he later hlater)

end YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound

#print axioms YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound.newBlock_radius_gt
#print axioms YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound.selfReturnProbability_eq_conditional
#print axioms YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound.newTailSelfReturnTrace_le_highLabel
#print axioms YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound.newTailTraceRate_le_gaussian
#print axioms YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound.newTailBase
#print axioms YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound.newTailTraceRate_small
#print axioms YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound.centered_newTail_le
#print axioms YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound.matrix_le_of_head
