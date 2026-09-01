/-
# Positive-carrier replication automatically supplies a finite row floor

The weighted replication compiler requires a common positive number `lambda`
such that every encoded replica raw row dominates `lambda` times its excited
spin-cube source row.  At a fixed finite cutoff this comparison need not be
added as independent data.  If the encoded states lie in the literal positive
carrier, all source and target raw rows are strictly positive rationals.

This file computes a common floor constructively.  For every source/replica
pair it clips the exact target/source raw-row ratio at one, and multiplies all
of those finitely many positive factors.  The product is positive, at most
each selected factor, and therefore supplies the weighted row comparison.

The result reduces the finite certificate to geometry: positive-carrier
membership and injectivity.  It does not control how rapidly the product floor
shrinks with cutoff, so divergent effective multiplicity remains a genuinely
open matched asymptotic obligation.  No finite gap, continuum theory, or Clay
conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The geometric positive-replication datum -/

/-- Distinct literal positive-carrier replicas for every excited spin-cube
source.  No quantitative row comparison is requested from the constructor. -/
structure CentralLowerExcitedSpinCubePositiveRawReplication
    (w : Q') (hw0 : (0 : Q') < w) (K : Nat) : Type where
  replicaCount : Nat
  replicaCount_pos : 0 < replicaCount
  encode : Nat × Nat → EdgeLabelling
  encode_mem : ∀ offset replica,
    offset < K → replica < replicaCount →
      encode (offset, replica) ∈
        centralPositiveHalfStates w (Q'.le_of_lt hw0) K 0
  encode_injective : ∀ left right,
    left.1 < K → left.2 < replicaCount →
    right.1 < K → right.2 < replicaCount →
    encode left = encode right → left = right

namespace CentralLowerExcitedSpinCubePositiveRawReplication

private theorem sourceRawRow_pos
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (_replication :
      CentralLowerExcitedSpinCubePositiveRawReplication w hw0 K)
    (offset : Nat) (hoffset : offset < K) :
    (0 : Q') <
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw0) K 0
        (centralLowerSpinCubeState (offset + 1)) := by
  exact centralPhysicalPositiveRawRowMass_pos
    (centralLowerSpinCubeState_mem_centralPositiveHalfStates
      hw0 (by omega))

/-- The target/source raw-row ratio, clipped at one.  Outside the finite
Cartesian carrier it is set to one; that branch is never selected below. -/
def clippedRawRowRatio
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubePositiveRawReplication w hw0 K)
    (pair : Nat × Nat) : Q' :=
  if hpair : pair.1 < K ∧ pair.2 < replication.replicaCount then
    Q'.min' 1
      (Q'.divPos
        (centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K 0 (replication.encode pair))
        (centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw0) K 0
          (centralLowerSpinCubeState (pair.1 + 1)))
        (replication.sourceRawRow_pos pair.1 hpair.1))
  else 1

private theorem clippedRawRowRatio_pos
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubePositiveRawReplication w hw0 K)
    (pair : Nat × Nat) :
    (0 : Q') < replication.clippedRawRowRatio pair := by
  unfold clippedRawRowRatio
  split
  next hpair =>
    exact CReal.min_pos (by decide)
      (Q'.divPos_pos _ _
        (replication.sourceRawRow_pos pair.1 hpair.1)
        (centralPhysicalPositiveRawRowMass_pos
          (replication.encode_mem pair.1 pair.2 hpair.1 hpair.2)))
  next _ => decide

private theorem clippedRawRowRatio_le_one
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubePositiveRawReplication w hw0 K)
    (pair : Nat × Nat) :
    replication.clippedRawRowRatio pair ≤ 1 := by
  unfold clippedRawRowRatio
  split
  next _ => exact Q'.min_le_left
  next _ => exact Q'.le_refl' 1

private theorem listQProduct_pos_local {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') < value item) :
    ∀ items : List A, (0 : Q') < listQProduct value items
  | [] => by
      change (0 : Q') < 1
      decide
  | head :: tail =>
      Q'.mul_pos (hvalue head)
        (listQProduct_pos_local value hvalue tail)

private theorem listQProduct_nonnegative_local {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQProduct value items
  | [] => by
      change (0 : Q') ≤ 1
      decide
  | head :: tail =>
      Q'.mul_nonneg _ _ (hvalue head)
        (listQProduct_nonnegative_local value hvalue tail)

private theorem listQProduct_le_one_local {A : Type}
    (value : A → Q')
    (hvalue0 : ∀ item, (0 : Q') ≤ value item)
    (hvalue1 : ∀ item, value item ≤ (1 : Q')) :
    ∀ items : List A, listQProduct value items ≤ (1 : Q')
  | [] => Q'.le_refl' 1
  | head :: tail => by
      have htail0 : (0 : Q') ≤ listQProduct value tail :=
        listQProduct_nonnegative_local value hvalue0 tail
      have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
        (listQProduct value tail) (hvalue1 head) htail0
      exact Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.one_mul_eqv (listQProduct value tail)))
          (listQProduct_le_one_local value hvalue0 hvalue1 tail))

private theorem listQProduct_le_selected_local {A : Type}
    (value : A → Q')
    (hvalue0 : ∀ item, (0 : Q') ≤ value item)
    (hvalue1 : ∀ item, value item ≤ (1 : Q'))
    (selected : A) :
    ∀ items : List A, selected ∈ items →
      listQProduct value items ≤ value selected
  | [], hmem => by cases hmem
  | head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        have hrest := listQProduct_le_one_local
          value hvalue0 hvalue1 tail
        have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
          (value selected) hrest (hvalue0 selected)
        exact Q'.le_trans' _ _ _ hscaled
          (Q'.le_of_eqv (Q'.mul_one_eqv (value selected)))
      · have hselected := listQProduct_le_selected_local
          value hvalue0 hvalue1 selected tail htail
        have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
          (value head) hselected (hvalue0 head)
        have hcap := Q'.mul_le_mul_of_nonneg_right _ _
          (value selected) (hvalue1 head) (hvalue0 selected)
        exact Q'.le_trans' _ _ _ hscaled
          (Q'.le_trans' _ _ _ hcap
            (Q'.le_of_eqv (Q'.one_mul_eqv (value selected))))

/-! ## 2. Explicit common finite floor -/

/-- Product of all clipped positive row ratios in the finite replica family. -/
def rawRowRatioFloor
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubePositiveRawReplication w hw0 K) : Q' :=
  listQProduct replication.clippedRawRowRatio
    (cartesian (List.range K) (List.range replication.replicaCount))

theorem rawRowRatioFloor_pos
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubePositiveRawReplication w hw0 K) :
    (0 : Q') < replication.rawRowRatioFloor := by
  unfold rawRowRatioFloor
  exact listQProduct_pos_local _ replication.clippedRawRowRatio_pos _

theorem rawRowRatioFloor_le_clippedRawRowRatio
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubePositiveRawReplication w hw0 K)
    (offset replica : Nat) (hoffset : offset < K)
    (hreplica : replica < replication.replicaCount) :
    replication.rawRowRatioFloor ≤
      replication.clippedRawRowRatio (offset, replica) := by
  unfold rawRowRatioFloor
  apply listQProduct_le_selected_local
    replication.clippedRawRowRatio
    (fun pair => Q'.le_of_lt (replication.clippedRawRowRatio_pos pair))
    replication.clippedRawRowRatio_le_one
    (offset, replica)
  exact (mem_cartesian_iff _ _ _).mpr
    ⟨List.mem_range.mpr hoffset, List.mem_range.mpr hreplica⟩

/-! ## 3. Compilation to the weighted certificate -/

/-- Finite positivity computes all quantitative fields needed by the weighted
replication compiler. -/
def toWeighted
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubePositiveRawReplication w hw0 K) :
    CentralLowerExcitedSpinCubeWeightedRawReplication w hw0 K where
  replicaCount := replication.replicaCount
  replicaCount_pos := replication.replicaCount_pos
  replicaFloor := replication.rawRowRatioFloor
  replicaFloor_pos := replication.rawRowRatioFloor_pos
  encode := replication.encode
  encode_mem := by
    intro offset replica hoffset hreplica
    exact (mem_centralPositiveHalfStates_iff.mp
      (replication.encode_mem offset replica hoffset hreplica)).1
  encode_injective := replication.encode_injective
  scaledRawRow_le := by
    intro offset replica hoffset hreplica
    let sourceRow := centralPhysicalPositiveRawRowMass
      w (Q'.le_of_lt hw0) K 0
      (centralLowerSpinCubeState (offset + 1))
    let targetRow := centralPhysicalPositiveRawRowMass
      w (Q'.le_of_lt hw0) K 0
      (replication.encode (offset, replica))
    let hsource : (0 : Q') < sourceRow :=
      replication.sourceRawRow_pos offset hoffset
    let ratio := Q'.divPos targetRow sourceRow hsource
    have hfloorClip := replication.rawRowRatioFloor_le_clippedRawRowRatio
      offset replica hoffset hreplica
    have hclipRatio :
        replication.clippedRawRowRatio (offset, replica) ≤ ratio := by
      unfold clippedRawRowRatio
      simp only [hoffset, hreplica, and_self, dite_true]
      exact Q'.min_le_right
    have hfloorRatio : replication.rawRowRatioFloor ≤ ratio :=
      Q'.le_trans' _ _ _ hfloorClip hclipRatio
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ sourceRow
      hfloorRatio (Q'.le_of_lt hsource)
    have hcollapse : sourceRow * ratio ≈ targetRow := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv sourceRow ratio)
        (Q'.divPos_mul_eqv targetRow sourceRow hsource)
    exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse)

/-- The automatically computed positive floor immediately yields the finite
ray-mass reciprocal bound. -/
theorem rayMass_le_reciprocalComputedEffectiveMultiplicity
    {w : Q'} {hw0 : (0 : Q') < w} {K : Nat}
    (replication :
      CentralLowerExcitedSpinCubePositiveRawReplication w hw0 K) :
    centralLowerExcitedSpinCubeRayMass w (Q'.le_of_lt hw0) K ≤
      Q'.divPos 1 replication.toWeighted.effectiveMultiplicity
        replication.toWeighted.effectiveMultiplicity_pos :=
  replication.toWeighted.rayMass_le_reciprocalEffectiveMultiplicity

/-! ## 4. Finite non-vacuity -/

/-- One literal positive replica per excited source is always available: the
spin-cube source itself.  This proves finite non-vacuity but supplies no
growing replica count, so it does not discharge the matched asymptotic input. -/
def identityPositiveRawReplication
    (w : Q') (hw0 : (0 : Q') < w) (K : Nat) :
    CentralLowerExcitedSpinCubePositiveRawReplication w hw0 K where
  replicaCount := 1
  replicaCount_pos := by omega
  encode := fun pair => centralLowerSpinCubeState (pair.1 + 1)
  encode_mem := by
    intro offset _replica hoffset _hreplica
    exact centralLowerSpinCubeState_mem_centralPositiveHalfStates
      hw0 (by omega)
  encode_injective := by
    intro left right _hleftOffset hleftReplica
      _hrightOffset hrightReplica heq
    have hfirst : left.1 = right.1 := by
      have hspin := centralLowerSpinCubeState_injective heq
      omega
    have hsecond : left.2 = right.2 := by omega
    exact Prod.ext hfirst hsecond

end CentralLowerExcitedSpinCubePositiveRawReplication

/-! ## 5. Matched positive-replication family -/

/-- A matched family of finite positive-carrier injections, together with the
single analytic assertion that the reciprocal of their *computed* effective
multiplicity has a located zero tail. -/
structure MatchedDyadicExcitedSpinCubePositiveRawReplicationFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (_bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  replication : ∀ scale,
    CentralLowerExcitedSpinCubePositiveRawReplication
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
  rate : Q' → Nat
  reciprocalComputedEffectiveMultiplicity_le :
    ∀ epsilon, (0 : Q') < epsilon →
      ∀ scale, rate epsilon ≤ scale →
        Q'.divPos 1
            (replication scale).toWeighted.effectiveMultiplicity
            (replication scale).toWeighted.effectiveMultiplicity_pos ≤
          epsilon

/-- Positive-carrier geometry plus the computed-product asymptotic inhabits
the earlier weighted-replication interface without adding row comparisons. -/
def MatchedDyadicExcitedSpinCubePositiveRawReplicationFamily.toWeightedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (replicas :
      MatchedDyadicExcitedSpinCubePositiveRawReplicationFamily bridge) :
    MatchedDyadicExcitedSpinCubeWeightedRawReplicationFamily bridge where
  replication := fun scale => (replicas.replication scale).toWeighted
  rate := replicas.rate
  reciprocalEffectiveMultiplicity_le :=
    replicas.reciprocalComputedEffectiveMultiplicity_le

def MatchedDyadicExcitedSpinCubePositiveRawReplicationFamily.toRayMassTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (replicas :
      MatchedDyadicExcitedSpinCubePositiveRawReplicationFamily bridge) :
    MatchedDyadicExcitedSpinCubeRayMassTailZero bridge :=
  replicas.toWeightedFamily.toRayMassTailZero

/-- A matched positive-replica family with divergent computed effective
multiplicity excludes the cutoff-uniform assigned-ratio route. -/
theorem positiveReplicationFamily_excludes_cofinalAssignedRatio
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (replicas :
      MatchedDyadicExcitedSpinCubePositiveRawReplicationFamily bridge) :
    ¬ Nonempty
      (MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio
        bridge) :=
  tailZero_excludes_cofinalAssignedRatio replicas.toRayMassTailZero

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate.CentralLowerExcitedSpinCubePositiveRawReplication.rawRowRatioFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate.CentralLowerExcitedSpinCubePositiveRawReplication.rawRowRatioFloor_le_clippedRawRowRatio
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate.CentralLowerExcitedSpinCubePositiveRawReplication.toWeighted
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate.CentralLowerExcitedSpinCubePositiveRawReplication.rayMass_le_reciprocalComputedEffectiveMultiplicity
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate.CentralLowerExcitedSpinCubePositiveRawReplication.identityPositiveRawReplication
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate.MatchedDyadicExcitedSpinCubePositiveRawReplicationFamily.toWeightedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate.MatchedDyadicExcitedSpinCubePositiveRawReplicationFamily.toRayMassTailZero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate.positiveReplicationFamily_excludes_cofinalAssignedRatio
