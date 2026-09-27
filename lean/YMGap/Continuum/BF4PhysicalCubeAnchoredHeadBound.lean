/-
# A constructed cutoff-uniform energy bound on the fixed root-anchored head

For the fixed head B=1404, reuse the existing constructed persistent floor
on its positive physical edges and the loop-erased carrier-square path bound.
Pulling an ARBITRARY later coefficient back to the head restricts the original
directed energy to old-old pairs; this sub-sum is no larger than its full
energy. It is not replaced by the energy of a zero extension.

Every head value relative to the vacuum root is thus bounded by the same
energy. Summing with ORIGINAL later stationary weights costs at most one,
not the head cardinality. This produces the explicit constant S/F, where S
is the fixed carrier-square path scale and F is the constructed persistent
positive edge floor. Both depend on w and the FIXED head, never on later K.

The declared onset is the existing explicit row-tail anchor. Combining this
actual head producer with fixed-tail absorption gives full centered coercivity.
Scope: extent one, 0<w<=1/2. No coupling-uniform lower gap, geometric time,
completed operator identification, continuum/QFT or Clay claim is inferred.
-/

import YMGap.Continuum.BF4PhysicalCubeTailAbsorption
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathScale

namespace YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeTailAbsorption
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathScale
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-- Restriction along the canonical embedding selects an old-old sub-sum
of the SAME later energy, for arbitrary later coefficients. -/
theorem pulled_energy_le_full {w : Q'} {hw : (0 : Q') ≤ w}
    (base later half : Nat) (hlater : base ≤ later) (f : Nat → Q') :
    finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w hw base half)
      (fun i => f (centralPhysicalFiniteCutoffIndexMap w hw base later half i))
      (centralPhysicalFinitePulledKernel w hw base later half) ≤
    finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w hw later half)
      f (centralPhysicalFiniteKernel w hw later half) := by
  let source := centralPhysicalFiniteVacuumSectorIndices w hw base half
  let target := centralPhysicalFiniteVacuumSectorIndices w hw later half
  let code := centralPhysicalFiniteCutoffIndexMap w hw base later half
  let term := fun i j => centralPhysicalFiniteKernel w hw later half i j *
    ((f i + -f j) * (f i + -f j))
  have hs : source.Nodup := centralPhysicalFiniteVacuumSectorIndices_nodup w hw base half
  have ht : target.Nodup := centralPhysicalFiniteVacuumSectorIndices_nodup w hw later half
  have hm (i : Nat) (hi : i ∈ source) : code i ∈ target :=
    centralPhysicalFiniteVacuumSectorIndexMap_mem hlater hi
  have hinj (i : Nat) (hi : i ∈ source) (j : Nat) (hj : j ∈ source) (he : code i = code j) : i = j :=
    centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector hlater hi hj he
  have hterm (i j : Nat) : (0 : Q') ≤ term i j :=
    Q'.mul_nonneg _ _ (centralNormalizedPhysicalReflectedKernel_nonnegative hw later half _ _)
      (SumOfSquares.q_mul_self_nonneg _)
  change listQSum (fun i => listQSum (fun j => term (code i) (code j)) source) source ≤
    listQSum (fun i => listQSum (term i) target) target
  exact listQSum_le_of_injective_nodup source target _ _ code hs ht hm hinj
    (fun i _ => listQSum_le_of_injective_nodup source target _ _ code hs ht hm hinj
      (fun _ _ => Q'.le_refl' _) (fun j _ => hterm (code i) j))
    (fun i _ => listQSum_nonnegative_on (term i) target (fun j _ => hterm i j))

/-- The fixed-head path bound controls each ROOTED later coefficient by
the full original later energy, using a persistent floor only on base edges. -/
theorem floor_mul_rooted_coordinate_le_energy {w : Q'} {hw : (0 : Q') ≤ w}
    {base : Nat} (certificate : FixedBasePulledPositiveEdgeFloor w hw base 0)
    (later : Nat) (hlater : certificate.start ≤ later) (f : Nat → Q')
    (i : Nat) (hi : i ∈ centralPhysicalFiniteVacuumSectorIndices w hw base 0) :
    certificate.floor *
      ((rootShift f (centralPhysicalFiniteCutoffIndexMap w hw base later 0 i)) *
        (rootShift f (centralPhysicalFiniteCutoffIndexMap w hw base later 0 i))) ≤
      centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale w hw base 0 *
        finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w hw later 0)
          f (centralPhysicalFiniteKernel w hw later 0) := by
  let code := centralPhysicalFiniteCutoffIndexMap w hw base later 0
  have hpath := BF4PhysicalCutoffVacuumSectorPulledSimplePathScale.FixedBasePulledPositiveEdgeFloor.floor_mul_endpoint_sq_le_simpleCarrierSquareScale_mul_pulledDirichlet
    certificate later hlater (fun j => f (code j)) i 0 hi (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw base 0)
  have hzero : code 0 = 0 := centralPhysicalFiniteCutoffIndexMap_zero w hw base later 0
  dsimp only at hpath
  rw [hzero] at hpath
  exact Q'.le_trans' _ _ _ hpath
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (pulled_energy_le_full base later 0 (Nat.le_trans certificate.start_ge_base hlater) f)
      (Q'.le_of_lt (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos w hw base 0)))

/-- Summing with the original stationary law costs at most its mass, which
is <=1. No head cardinality or unit-sector-mass assumption is inserted. -/
theorem floor_mul_anchored_head_norm_le_energy {w : Q'} {hw : (0 : Q') ≤ w}
    {base : Nat} (certificate : FixedBasePulledPositiveEdgeFloor w hw base 0)
    (later : Nat) (hlater : certificate.start ≤ later) (f : Nat → Q') :
    certificate.floor * centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw later 0
      (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient w hw base later 0 (rootShift f)) ≤
      centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale w hw base 0 *
        finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w hw later 0)
          f (centralPhysicalFiniteKernel w hw later 0) := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw later 0
  let weight := centralPhysicalFiniteWeight w hw later 0
  let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient w hw base later 0 (rootShift f)
  let A := centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale w hw base 0 *
    finiteJointDirichletEnergy states f (centralPhysicalFiniteKernel w hw later 0)
  have hA : (0 : Q') ≤ A := Q'.mul_nonneg _ _
    (Q'.le_of_lt (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos w hw base 0))
    (finiteJointDirichletEnergy_nonnegative states f _
      (fun _ _ => centralNormalizedPhysicalReflectedKernel_nonnegative hw later 0 _ _))
  have hpoint (i : Nat) : certificate.floor * (head i * head i) ≤ A := by
    by_cases hold : i ∈ centralPhysicalFiniteEmbeddedVacuumSectorIndices w hw base later 0
    · obtain ⟨j, hj, he⟩ := List.mem_map.mp hold
      have h := floor_mul_rooted_coordinate_le_energy certificate later hlater f j hj
      rw [he] at h
      simpa only [head, centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient,
        centralPhysicalFiniteEmbeddedVacuumSectorB, decide_eq_true hold, if_true] using h
    · have hh : head i = 0 := by
        simp only [head, centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient,
          centralPhysicalFiniteEmbeddedVacuumSectorB, decide_eq_false hold, Bool.false_eq_true, if_false]
      rw [hh]
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv 0)) (Q'.mul_zero_eqv _))) hA
  have hsum : listQSum (fun i => certificate.floor * ((head i * head i) * weight i)) states ≤
      listQSum (fun i => A * weight i) states := by
    apply listQSum_mono
    intro i _
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (hpoint i)
        (centralPhysicalRowMarginal_nonnegative hw later 0 _))
  have hmass : listQSum weight states ≤ 1 := centralPhysicalFiniteVacuumSectorMass_le_one w hw later 0
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (listQSum_mul_left certificate.floor _ states))
    (Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv (listQSum_mul_left A weight states))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ A hmass hA)
        (Q'.le_of_eqv (Q'.mul_one_eqv A)))))

/-- Explicit onset; the base is fixed while the nome dependence is retained. -/
def headBoundStart (w : Q') : Nat := fixedBasePulledEdgeFloorAnchor w 1404 0

theorem headBoundStart_ge_base (w : Q') : 1404 ≤ headBoundStart w :=
  fixedBasePulledEdgeFloorAnchor_ge_base w 1404 0

/-- A computable finite quotient S/F, not an opaque existential constant. -/
def headEnergyConstant (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  Q'.divPos (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale w hw 1404 0)
    (fixedBasePulledPositiveEdgeFloorValue w hw 1404 0)
    (fixedBasePulledPositiveEdgeFloorValue_pos w hw 1404 0)

theorem headEnergyConstant_pos (w : Q') (hw : (0 : Q') ≤ w) : (0 : Q') < headEnergyConstant w hw :=
  Q'.divPos_pos _ _ _ (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos w hw 1404 0)

/-! The quotient definition is kept behind these two small projection lemmas.
Downstream calibration files should use them instead of unfolding the
dependent carrier expression, which otherwise causes expensive elaboration. -/

theorem headEnergyConstant_eq_divPos (w : Q') (hw : (0 : Q') ≤ w) :
    headEnergyConstant w hw =
      Q'.divPos
        (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
          w hw 1404 0)
        (fixedBasePulledPositiveEdgeFloorValue w hw 1404 0)
        (fixedBasePulledPositiveEdgeFloorValue_pos w hw 1404 0) := rfl

theorem fixedBasePulledPositiveEdgeFloorValue_mul_headEnergyConstant_eqv_scale
    (w : Q') (hw : (0 : Q') ≤ w) :
    fixedBasePulledPositiveEdgeFloorValue w hw 1404 0 *
        headEnergyConstant w hw ≈
      centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
        w hw 1404 0 := by
  rw [headEnergyConstant_eq_divPos]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv _ _)
    (Q'.divPos_mul_eqv _ _ _)

/-- The formerly open fixed-head estimate, with its concrete constant and
onset. Uniform in later K; NOT uniform in the nome w. -/
theorem anchored_head_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (later : Nat) (hlater : headBoundStart w ≤ later) (f : Nat → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0
      (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient w (Q'.le_of_lt hw0) 1404 later 0 (rootShift f)) ≤
      headEnergyConstant w (Q'.le_of_lt hw0) *
        finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw0) later 0)
          f (centralPhysicalFiniteKernel w (Q'.le_of_lt hw0) later 0) := by
  let hw := Q'.le_of_lt hw0
  let cert := explicitFixedBasePulledPositiveEdgeFloor hw0 hw1 1404 0
  have hstart : cert.start = headBoundStart w := explicitFixedBasePulledPositiveEdgeFloor_start_eq_anchor hw0 hw1 1404 0
  have h := floor_mul_anchored_head_norm_le_energy cert later (by rw [hstart]; exact hlater) f
  have hf : cert.floor ≈ fixedBasePulledPositiveEdgeFloorValue w hw 1404 0 :=
    explicitFixedBasePulledPositiveEdgeFloor_floor_eqv_value hw0 hw1 1404 0
  let E := finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w hw later 0)
    f (centralPhysicalFiniteKernel w hw later 0)
  let F := fixedBasePulledPositiveEdgeFloorValue w hw 1404 0
  let S := centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale w hw 1404 0
  have hcancel : F * (headEnergyConstant w hw * E) ≈ S * E := by
    refine Q'.eqv_trans _ ((F * headEnergyConstant w hw) * E) _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    apply Q'.mul_eqv_congr_right
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv S F _)
  apply Q'.le_of_mul_le_mul_left (c := F) _ (fixedBasePulledPositiveEdgeFloorValue_pos w hw 1404 0)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ _ hf))
    (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv hcancel))

/-- Full cofinal coercivity constant in the DIRECTED energy convention. -/
def coercivityConstant (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  1 + 3 * headEnergyConstant w hw

theorem coercivityConstant_pos (w : Q') (hw : (0 : Q') ≤ w) :
    (0 : Q') < coercivityConstant w hw :=
  Q'.add_pos (by decide) (Q'.mul_pos (by decide) (headEnergyConstant_pos w hw))

private theorem energy_regroup (C E : Q') : E + 3 * (C * E) ≈ (1 + 3 * C) * E :=
  Q'.eqv_trans _ (1 * E + (3 * C) * E) _
    (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.one_mul_eqv E)) (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
    (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))

/-- Constructed, coefficient-independent full centered Poincare estimate.
Its constant and onset depend explicitly on w, NOT on the outer cutoff. -/
theorem centered_norm_le_coercivity_mul_energy {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ HalfPow.half) (later : Nat) (hlater : headBoundStart w ≤ later) (f : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean w (Q'.le_of_lt hw0) later 0 f ≈ 0) :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0 f ≤
      coercivityConstant w (Q'.le_of_lt hw0) *
        finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw0) later 0)
          f (centralPhysicalFiniteKernel w (Q'.le_of_lt hw0) later 0) := by
  have hw1 : w < (1 : Q') := Q'.lt_of_le_of_lt hw (by decide)
  have habsorb := centered_norm_le_energy_add_anchored_head hw0 hw later
    (Nat.le_trans (headBoundStart_ge_base w) hlater) f hcenter
  have hhead := anchored_head_bound hw0 hw1 later hlater f
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ 3 hhead (by decide)
  exact Q'.le_trans' _ _ _ habsorb
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hscaled)
      (Q'.le_of_eqv (energy_regroup _ _)))

end YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound

#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.pulled_energy_le_full
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.floor_mul_rooted_coordinate_le_energy
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.floor_mul_anchored_head_norm_le_energy
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.headBoundStart
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.headBoundStart_ge_base
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.headEnergyConstant
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.headEnergyConstant_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.headEnergyConstant_eq_divPos
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.fixedBasePulledPositiveEdgeFloorValue_mul_headEnergyConstant_eqv_scale
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.anchored_head_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.coercivityConstant
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.coercivityConstant_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound.centered_norm_le_coercivity_mul_energy
